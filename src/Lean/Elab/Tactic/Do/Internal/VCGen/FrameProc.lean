/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.WPApp
public import Lean.Meta.Sym.Apply
import Std.Internal.Do.Order.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.Sym.InferType

/-!
The metadata a frame inference procedure operates on: the `wp` application metadata `WPApp` and the
`FrameProc` bundling an inference procedure with its frame operator.
`@[frameproc]` registration lives in `FrameProcAttr`.
-/

open Lean Meta Sym

namespace Lean.Elab.Tactic.Do.Internal

/-- How the goal precondition frames through the frame operator: `vcgen` applies the frame rule with
frame `F := frame` and footprint `P := footprint?`. The footprint appears verbatim in
the split VC `pre ⊑ (op frame footprint) s⃗` and its residual VC `footprint ⊑ wp …` becomes a
subgoal. When `footprint?` is omitted, `vcgen` will close `footprint ⊑ wp …` and emit the split
VC `pre ⊑ (op frame (wp …)) s⃗` which for any `op` other than the lattice meet will bring VC
generation to a halt.

`proof?` discharges the split VC `pre ⊑ (op frame footprint) s⃗`; holes in the proof, or an omitted
proof, become VCs. -/
public structure VCGen.FrameSplit where
  /-- The framed resource `F : R`. -/
  frame : Expr
  /-- The footprint `P : Pred`. -/
  footprint? : Option Expr := none
  /-- A proof of the split VC `pre ⊑ (op frame footprint) s⃗`. -/
  proof? : Option Expr := none

/-- The point footprint `fun u⃗ => ⌜u⃗ = t⃗⌝ ⊓ P u⃗`: the predicate `P` strengthened to hold exactly
at the states `t⃗`. -/
public def VCGen.mkPointFootprint (states : Array Expr) (P : Expr) : SymM Expr := do
  let n := states.size
  let mut domTys := #[]
  let mut carriers := #[]
  let mut ty ← Sym.inferType P
  for _ in [0:n] do
    domTys := domTys.push ty.bindingDomain!
    ty := ty.bindingBody!
    carriers := carriers.push ty
  -- Innermost body: `P u⃗`, with `uⱼ` the j-th binder from the outside.
  let mut body := P.beta (Array.ofFn (n := n) fun j => Expr.bvar (n - 1 - j))
  for i' in [0:n] do
    let i := n - 1 - i'
    let C := carriers[i]!
    -- `CompleteLattice` is `Sort`-polymorphic in the carrier; `ofProp` and `meet` take a `Type`.
    let w ← Meta.getLevel C
    let some v := w.dec
      | throwError "mkPointFootprint: carrier is not a `Type`{indentExpr C}"
    let inst ← Meta.synthInstance (mkApp (mkConst ``Lean.Order.CompleteLattice [w]) C)
    let eq := mkApp3 (mkConst ``Eq [← Meta.getLevel domTys[i]!]) domTys[i]! (.bvar 0) states[i]!
    let ofp := mkApp3 (mkConst ``Lean.Order.CompleteLattice.ofProp [v]) C inst eq
    body := .lam `u domTys[i]! (mkApp4 (mkConst ``Lean.Order.meet [v]) C inst ofp body) .default
  shareCommon body

/-- A frame backward rule together with the positions of its assignable subgoals in the applied
rule's goal list: the schematic frame `F` and footprint `P`, the split VC `pre ⊑ (op F P) s⃗`, and
the residual VC `P ⊑ wp x (fun a => upperAdjoint (op F) (Q a)) E`. The positions are fixed at rule
construction, so applying a `FrameSplit` assigns by index. -/
public structure VCGen.FrameBackwardRule where
  /-- The backward rule concluding `pre ⊑ wp x Q E s⃗`. -/
  rule : Lean.Meta.Sym.BackwardRule
  /-- Position of the split VC `pre ⊑ (op F P) s⃗`. -/
  splitVCIdx : Nat
  /-- Position of the schematic frame `F : R`. -/
  frameIdx : Nat
  /-- Position of the schematic footprint `P : Pred`. -/
  footprintIdx : Nat
  /-- Position of the residual VC `P ⊑ wp x (fun a => upperAdjoint (op F) (Q a)) E`. -/
  residualVCIdx : Nat

/-- A frame inference procedure: given the resource type `R` of the applicable frame operator
`op : R → Pred → Pred`, the goal's precondition, the `wp` metadata of a spec-ready program, the
spec's precondition instantiated at the call site (the RHS of the spec's precondition VC `pre ⊑ ·`),
and the frame of a matching `frames` clause (if any), optionally produce a `FrameSplit`. `none`
leaves the spec to apply directly.

The caller instantiates and hash-conses the split before the speculative spec application's
metavariable context is reset, so it may mention metavariables assigned during that application. -/
public abbrev VCGen.FrameInferenceProc :=
  Expr → Expr → VCGen.WPApp → Expr → Option Expr → SymM (Option VCGen.FrameSplit)

/-- How to decompose a lattice operator `head … s⃗` on the RHS of an entailment: the distribution and
unfolding `rewrites` that saturate it, and the terminal `⊑`-introduction `terminals` that close the
reduced form. `head` keys the split in the `latticeOps` table. -/
public structure VCGen.LatticeOp where
  /-- Head constant of the operator this split decomposes. Keys the `latticeOps` table. -/
  head : Name
  /-- The number of leading arguments held constant during rule construction: the operator's carrier
  type and its typeclass instances. The operands and excess state arguments after them become the
  rule's schematic parameters. `2` for a connective over a `CompleteLattice` carrier; `0` for a
  monomorphic operator. -/
  numConst : Nat := 2
  /-- Distribution and unfolding equalities that saturate the operator applied to state arguments. -/
  rewrites : Array Name := #[]
  /-- The operator's terminal `⊑`-introduction rule, or `none` when it saturates to another operator's
  terminal. -/
  terminal? : Option Name := none

/-- A frame inference procedure registered with `@[frameproc]`, together with its frame operator. The
`vcgen` frontend selects the one whose `prog` matches the goal program's monad. -/
public structure VCGen.FrameProc where
  /-- Head constant of the program type (the monad) whose `wp` this procedure frames. Keys the
  procedure in the `byProg` index; `vcgen` consults it for a program with that head. -/
  prog : Name
  /-- Builds the frame operator (head constant `opHead`) applied to the goal's assertion type. -/
  mkOpAppM : VCGen.WPApp → MetaM Expr
  /-- The resource type `R` of the operator `op : R → Pred → Pred`, i.e. the domain of `mkOpAppM`'s
  result. Provided directly so `vcgen` reads it without building the operator, which it does only when
  a frame actually applies. -/
  resourceTy : VCGen.WPApp → MetaM Expr
  /-- Head constant of the frame operator, locating the split VC in the frame rule. -/
  opHead : Name
  /-- The frame inference metaprogram. -/
  proc : VCGen.FrameInferenceProc

/-- The registered frame inference procedures, indexed by the program monad's head constant
(selected per node in `solve`). -/
public structure VCGen.FrameProcs where
  byProg : Std.HashMap Name VCGen.FrameProc := {}

public instance : Inhabited VCGen.FrameProcs := ⟨{}⟩

public def VCGen.FrameProcs.insert (s : FrameProcs) (fp : FrameProc) : FrameProcs :=
  { byProg := s.byProg.insert fp.prog fp }

/-- Default meet frame procedure: frame the resource pinned by a `frames` clause. -/
public def VCGen.meetFrameInferenceProc : FrameInferenceProc :=
  fun _resourceTy _pre _info _specPre frame? => do
    let some frame := frame? | return none
    return some { frame }

/-- The default frame operator: lattice meet `pre ⊓ F`, the Hoare frame every complete lattice carries.
Framed only through an explicit `frames` clause; used for a monad with no registered `@[frameproc]`. -/
public def VCGen.meetFrameProc : VCGen.FrameProc where
  prog := ``Lean.Order.meet
  mkOpAppM info := Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]
  resourceTy info := pure info.Pred
  opHead := ``Lean.Order.meet
  proc := meetFrameInferenceProc

end Lean.Elab.Tactic.Do.Internal
