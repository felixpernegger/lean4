/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import Std.Internal
import Std.Tactic.Do

set_option mvcgen.warning false
set_option grind.warning false

/-!
# A minimal separation logic for `vcgen` frame inference, with in-place list reverse

A heap `Heap := Nat → Option Nat` with separating conjunction `∗` (disjoint union), magic wand `-∗`,
and points-to `↦`. Unlike the lattice meet, `∗` is not cartesian: `l ↦ v ∗ l ↦ v = ⊥`. The frame
operator is `∗` itself; its upper adjoint is the wand. `HeapM.wp` is the `frameClosure` of the base
`StateM Heap` wp over `∗`, so every program frames every heap assertion by construction. The
registered `@[frameproc]` cancels the framed resource out of the precondition (proof by `ac_rfl`),
so `vcgen … with finish` closes the `iFrame` examples.

The showcase is an in-place reverse of a null-terminated doubly-linked list. A node at address `p`
stores next at `p`, prev at `p + 1`, and the payload at `p + 2`. The abstract contents are the
`List Nat` of payloads, related to the heap by `IsList`; the program takes only a `head` pointer,
so the list is ghost state in the specification. Framing an unrelated cell across the whole
reverse is the `iFrame` moment at program scale.
-/

open Lean Order Meta Elab Tactic Sym Std Internal.Do Std.Internal.Do.CompleteLattice

/-! ## Heaps and the separation algebra -/

/-- A heap maps locations to optionally-present values. -/
abbrev Heap := Nat → Option Nat

/-- Two heaps are disjoint when no location is present in both. -/
def Heap.disjoint (h₁ h₂ : Heap) : Prop := ∀ n, h₁ n = none ∨ h₂ n = none

/-- Union of heaps, preferring the left value on overlap (agreeing with disjointness). -/
def Heap.union (h₁ h₂ : Heap) : Heap := fun n => (h₁ n).or (h₂ n)

/-- The singleton heap holding `v` at `l`. -/
def Heap.single (l v : Nat) : Heap := fun n => if n = l then some v else none

/-- Overwrite location `l` with `w`. -/
def Heap.update (h : Heap) (l w : Nat) : Heap := fun n => if n = l then some w else h n

@[simp] theorem Heap.union_none_iff (h₁ h₂ : Heap) (n : Nat) :
    h₁.union h₂ n = none ↔ h₁ n = none ∧ h₂ n = none := by
  simp only [Heap.union]; cases h₁ n <;> simp

theorem Heap.disjoint_comm {h₁ h₂ : Heap} (h : h₁.disjoint h₂) : h₂.disjoint h₁ :=
  fun n => (h n).symm

theorem Heap.union_comm {h₁ h₂ : Heap} (h : h₁.disjoint h₂) : h₁.union h₂ = h₂.union h₁ := by
  funext n; simp only [Heap.union]; rcases h n with hn | hn <;> simp [hn]

theorem Heap.union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  funext n; simp only [Heap.union]; cases h₁ n <;> rfl

theorem Heap.none_union (h : Heap) : Heap.union (fun _ => none) h = h := by
  funext n; simp [Heap.union]

theorem Heap.union_none (h : Heap) : Heap.union h (fun _ => none) = h := by
  funext n; simp only [Heap.union]; cases h n <;> rfl

theorem Heap.disjoint_union_left {h₁ h₂ h₃ : Heap} :
    (h₁.union h₂).disjoint h₃ ↔ h₁.disjoint h₃ ∧ h₂.disjoint h₃ := by
  simp only [Heap.disjoint, Heap.union_none_iff]
  constructor
  · intro h; exact ⟨fun n => (h n).imp_left (·.1), fun n => (h n).imp_left (·.2)⟩
  · rintro ⟨ha, hb⟩ n; have := ha n; have := hb n; grind

theorem Heap.disjoint_union_right {h₁ h₂ h₃ : Heap} :
    h₁.disjoint (h₂.union h₃) ↔ h₁.disjoint h₂ ∧ h₁.disjoint h₃ := by
  simp only [Heap.disjoint, Heap.union_none_iff]
  constructor
  · intro h; exact ⟨fun n => (h n).imp_right (·.1), fun n => (h n).imp_right (·.2)⟩
  · rintro ⟨ha, hb⟩ n; have := ha n; have := hb n; grind

/-! ## Heap assertions

`HProp` is an opaque `def`, not `Heap → Prop`, so `vcgen` treats the heap as a resource dimension
rather than a state to introduce pointwise (which would destroy `∗`). The lattice is the pointwise
order transported from `Heap → Prop`. -/
def HProp : Type := Heap → Prop

instance : CompleteLattice HProp := inferInstanceAs (CompleteLattice (Heap → Prop))

/-! ## The separation-logic connectives -/

/-- The empty heap assertion. -/
def emp : HProp := fun h => ∀ n, h n = none

/-- The singleton heap assertion: the heap is exactly `l ↦ v`. -/
def pointsTo (l v : Nat) : HProp := fun h => h = Heap.single l v

/-- Separating conjunction: the heap splits into disjoint parts satisfying each side. -/
def sepConj (P Q : HProp) : HProp :=
  fun h => ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P h₁ ∧ Q h₂

/-- Magic wand: extending by any disjoint `P` heap yields a `Q` heap. -/
def wand (P Q : HProp) : HProp :=
  fun h => ∀ h', h.disjoint h' → P h' → Q (h.union h')

@[inherit_doc pointsTo] local notation:70 l:max " ↦ " v:max => pointsTo l v
@[inherit_doc sepConj] local infixr:65 " ∗ " => sepConj
@[inherit_doc wand] local infixr:60 " -∗ " => wand

/-! ## The separation algebra laws -/

theorem emp_sepConj (a : HProp) : (emp ∗ a) = a := by
  funext h
  apply propext
  constructor
  · rintro ⟨h₁, h₂, _, rfl, he, ha⟩
    have : h₁.union h₂ = h₂ := by funext n; simp only [Heap.union, he n, Option.none_or]
    rwa [this]
  · intro ha
    exact ⟨fun _ => none, h, fun _ => Or.inl rfl,
      by funext n; simp only [Heap.union, Option.none_or], fun _ => rfl, ha⟩

@[grind _=_]
theorem sepConj_assoc (a b c : HProp) : ((a ∗ b) ∗ c) = (a ∗ (b ∗ c)) := by
  funext h
  apply propext
  constructor
  · rintro ⟨_, h₃, hd, rfl, ⟨h₁, h₂, hd12, rfl, ha, hb⟩, hc⟩
    obtain ⟨hd13, hd23⟩ := Heap.disjoint_union_left.mp hd
    exact ⟨h₁, h₂.union h₃, Heap.disjoint_union_right.mpr ⟨hd12, hd13⟩,
      Heap.union_assoc h₁ h₂ h₃, ha, h₂, h₃, hd23, rfl, hb, hc⟩
  · rintro ⟨h₁, _, hd, rfl, ha, ⟨h₂, h₃, hd23, rfl, hb, hc⟩⟩
    obtain ⟨hd12, hd13⟩ := Heap.disjoint_union_right.mp hd
    exact ⟨h₁.union h₂, h₃, Heap.disjoint_union_left.mpr ⟨hd13, hd23⟩,
      (Heap.union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, hd12, rfl, ha, hb⟩, hc⟩

@[grind =]
theorem sepConj_comm (a b : HProp) : (a ∗ b) = (b ∗ a) := by
  funext h; apply propext
  constructor <;>
    · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
      exact ⟨h₂, h₁, Heap.disjoint_comm hd, Heap.union_comm hd, hq, hp⟩

theorem sepConj_emp (a : HProp) : (a ∗ emp) = a := by
  rw [sepConj_comm, emp_sepConj]

instance : Std.Associative (α := HProp) sepConj := ⟨sepConj_assoc⟩
instance : Std.Commutative (α := HProp) sepConj := ⟨sepConj_comm⟩
instance : Std.LawfulIdentity (α := HProp) sepConj emp where
  left_id := emp_sepConj
  right_id := sepConj_emp

attribute [local grind ←] PartialOrder.rel_of_eq
attribute [local grind ←] le_ofProp

/-! ## Pure facts and existentials via the lattice

`⌜φ⌝` (`ofProp`) is `⊤`/`⊥` and does not claim an empty heap. Separating pure (Iris `⌜φ⌝`) is
`⌜φ⌝ ⊓ emp`. Existentials are the lattice `iSup` (`⨆`). -/

noncomputable abbrev sepPure (φ : Prop) : HProp := ⌜φ⌝ ⊓ emp

theorem sepPure_apply (φ : Prop) (h : Heap) : sepPure φ h ↔ φ ∧ emp h := by
  constructor
  · intro hp
    refine ⟨?_, (meet_le_right (⌜φ⌝ : HProp) emp) h hp⟩
    have hφ : (⌜φ⌝ : HProp) h := (meet_le_left (⌜φ⌝ : HProp) emp) h hp
    simp only [CompleteLattice.ofProp] at hφ
    split at hφ
    · assumption
    · exact False.elim <| (bot_le (x := (fun _ => False : HProp))) h hφ
  · intro ⟨hφ, he⟩
    exact (le_meet (emp : HProp) ⌜φ⌝ emp (le_ofProp emp φ hφ) PartialOrder.rel_refl) h he

theorem sepPure_sepConj_iff (P : Prop) (Q : HProp) (h : Heap) :
    (sepPure P ∗ Q) h ↔ P ∧ Q h := by
  constructor
  · rintro ⟨h₁, h₂, _, rfl, hp, hQ⟩
    obtain ⟨hP, he⟩ := (sepPure_apply P h₁).mp hp
    have : h₁.union h₂ = h₂ := by funext n; simp only [Heap.union, he n, Option.none_or]
    exact ⟨hP, this.symm ▸ hQ⟩
  · intro ⟨hP, hQ⟩
    refine ⟨fun _ => none, h, fun _ => Or.inl rfl, (Heap.none_union h).symm, ?_, hQ⟩
    exact (sepPure_apply P _).mpr ⟨hP, fun _ => rfl⟩

@[grind =] theorem sepPure_true_eq_emp : sepPure True = emp := by
  funext h; apply propext
  simp [sepPure_apply]

@[grind .] theorem sepPure_sepConj_le (P : Prop) (Q : HProp) : (sepPure P ∗ Q) ⊑ Q := by
  intro h hh
  exact (sepPure_sepConj_iff P Q h |>.mp hh).2

@[grind ←] theorem sepPure_sepConj_le_of (φ : Prop) (Q R : HProp) (h : φ → Q ⊑ R) :
    sepPure φ ∗ Q ⊑ R := by
  intro heap hh
  have ⟨hφ, hQ⟩ := (sepPure_sepConj_iff φ Q heap).mp hh
  exact h hφ heap hQ

/-- Pointwise characterization of the sup on `HProp`. -/
theorem hprop_sup_apply (s : HProp → Prop) (h : Heap) :
    CompleteLattice.sup s h = ∃ f, s f ∧ f h := by
  apply propext
  constructor
  · exact fun hh => sup_le s (x := fun h => ∃ f, s f ∧ f h)
      (fun f hf h' hfh' => ⟨f, hf, hfh'⟩) h hh
  · rintro ⟨f, hf, hfh⟩; exact le_sup (c := s) hf h hfh

theorem iSup_hprop_apply {α : Type} (P : α → HProp) (h : Heap) :
    (iSup P : HProp) h ↔ ∃ a, P a h := by
  simp only [iSup, hprop_sup_apply]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, ha⟩; exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩; exact ⟨P a, ⟨a, rfl⟩, ha⟩

instance (F : HProp) : PreservesSup (sepConj F) where
  map_sup s := by
    funext h
    apply propext
    simp only [sepConj, hprop_sup_apply]
    constructor
    · rintro ⟨h₁, h₂, hd, rfl, hF, x, hx, hxh₂⟩
      exact ⟨sepConj F x, ⟨x, hx, rfl⟩, h₁, h₂, hd, rfl, hF, hxh₂⟩
    · rintro ⟨f, ⟨x, hx, rfl⟩, h₁, h₂, hd, rfl, hF, hxh₂⟩
      exact ⟨h₁, h₂, hd, rfl, hF, x, hx, hxh₂⟩

/-- The counit of the adjunction `F ∗ · ⊣ F -∗ ·`. -/
theorem sepConj_wand_le (F b : HProp) : (F ∗ (F -∗ b)) ⊑ b := by
  rintro h ⟨h₁, h₂, hd, rfl, hF, hw⟩
  have := hw h₁ (Heap.disjoint_comm hd) hF
  rwa [Heap.union_comm (Heap.disjoint_comm hd)] at this

/-- The upper adjoint of `F ∗ ·` is the magic wand `F -∗ ·`. -/
theorem sepConj_upperAdjoint (F b : HProp) :
    PreservesSup.upperAdjoint (sepConj F) b = (F -∗ b) := by
  apply PartialOrder.rel_antisymm
  · unfold PreservesSup.upperAdjoint
    apply sup_le
    intro x hx h hxh h' hdisj hF
    apply hx (h.union h')
    exact ⟨h', h, Heap.disjoint_comm hdisj, Heap.union_comm hdisj, hF, hxh⟩
  · exact PreservesSup.le_upperAdjoint (sepConj F) (sepConj_wand_le F b)

/-! ## The heap monad and its frame-internalizing weakest precondition -/

/-- The heap state monad. A `def` so it carries its own frame-internalizing `WP`. -/
def HeapM (α : Type) : Type := StateM Heap α

instance : Monad HeapM := inferInstanceAs (Monad (StateM Heap))
instance : LawfulMonad HeapM := inferInstanceAs (LawfulMonad (StateM Heap))

/-- A `HeapM` program as its underlying `StateM Heap` program, carrying the base wp. -/
def HeapM.run {α : Type} (x : HeapM α) : StateM Heap α := x

/-- A `StateM Heap` program as a `HeapM` program, carrying the frame-internalizing wp. -/
def HeapM.mk {α : Type} (x : StateM Heap α) : HeapM α := x

@[simp, grind =] theorem HeapM.run_mk {α : Type} (x : StateM Heap α) : (HeapM.mk x).run = x := rfl
@[simp, grind =] theorem HeapM.mk_run {α : Type} (x : HeapM α) : HeapM.mk x.run = x := rfl

/-- The frame-internalizing weakest precondition: the `frameClosure` of the base `StateM Heap` wp
over separating conjunction. -/
noncomputable instance HeapM.instWPMonad : WPMonad HeapM HProp EPost.Nil :=
  WPMonad.of_frameClosure (m := StateM Heap) sepConj sepConj_assoc emp_sepConj StateT.instWPMonad

/-- Every `HeapM` program frames every heap assertion `F`. -/
@[grind .]
theorem frames_sepConj {α : Type} (x : HeapM α) (F : HProp) : WP.Frames sepConj x F :=
  WP.Frames.of_frameClosure sepConj sepConj sepConj_assoc
    ⟨fun y E Q' => WP.wp y.run Q' E, fun _ _ _ => rfl⟩

/-- Triple introduction from the base `StateM Heap` interpretation: prove the base triple with an
arbitrary frame `F` held on both sides. -/
theorem HeapM.triple_of_base {α : Type} {x : HeapM α} {pre : HProp} {Q : α → HProp}
    (h : ∀ F : HProp, ⦃ F ∗ pre ⦄ x.run ⦃ fun a => F ∗ Q a ⦄) :
    ⦃ pre ⦄ x ⦃ Q ⦄ :=
  ⟨WP.le_wp_of_frameClosure_eq rfl fun F => (h F).1⟩

/-! ## Heap operations and their specs -/

/-- The null address. -/
def null : Nat := 0

/-- Load the value at `l` (0 when absent). -/
def load (l : Nat) : HeapM Nat :=
  HeapM.mk <| modifyGet fun h => ((h l).getD 0, h)

/-- Store `w` at location `l`. -/
def store (l w : Nat) : HeapM Unit :=
  HeapM.mk <| modifyGet fun h => ((), h.update l w)

open Lean.Elab.Tactic.Do.Internal Lean.Elab.Tactic.Do.Internal.VCGen

/-- Storing overwrites the cell, framing every disjoint heap by construction. -/
@[spec] theorem store_spec (l v w : Nat) :
    ⦃ l ↦ v ⦄ (store l w) ⦃ fun _ => l ↦ w ⦄ := by
  refine HeapM.triple_of_base fun F => ⟨?_⟩
  simp only [store, HeapM.run_mk]
  refine PartialOrder.rel_trans ?_
    (WPMonad.le_wp_modifyGet_StateT_apply (m := Id) (fun h : Heap => ((), h.update l w)) _ _)
  rintro h ⟨hF, _, hd, rfl, hFh, rfl⟩
  refine ⟨hF, Heap.single l w, ?_, ?_, hFh, rfl⟩
  · intro n; rcases hd n with h' | h'
    · exact Or.inl h'
    · right; simp only [Heap.single] at h' ⊢; grind
  · funext n
    simp only [Heap.update, Heap.union, Heap.single]
    by_cases hn : n = l
    · subst hn; have := hd n; simp only [Heap.single] at this; grind
    · simp [hn]

/-- Loading returns the stored value and leaves the cell in place. -/
@[spec] theorem load_spec (l v : Nat) :
    ⦃ l ↦ v ⦄ (load l) ⦃ fun r => sepPure (r = v) ∗ l ↦ v ⦄ := by
  refine HeapM.triple_of_base fun F => ⟨?_⟩
  simp only [load, HeapM.run_mk]
  refine PartialOrder.rel_trans ?_
    (WPMonad.le_wp_modifyGet_StateT_apply (m := Id) (fun h : Heap => ((h l).getD 0, h)) _ _)
  rintro h ⟨hF, _, hd, rfl, hFh, rfl⟩
  refine ⟨hF, Heap.single l v, ?_, rfl, hFh, ?_⟩
  · intro n; rcases hd n with h' | h'
    · exact Or.inl h'
    · right; simp only [Heap.single] at h' ⊢; grind
  · refine (sepPure_sepConj_iff _ _ _).mpr ⟨?_, rfl⟩
    change ((hF.union (Heap.single l v) l).getD 0 = v)
    simp only [Heap.union, Heap.single, Option.getD]
    have := hd l
    simp only [Heap.single] at this
    grind

/-- Flatten a separating conjunction after mvars are instantiated. -/
partial def sepAtoms.go (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOf ``sepConj then go e.appFn!.appArg! ++ go e.appArg!
  else #[e]

/-- Flatten a separating conjunction; instantiate mvars once at the root. -/
def sepAtoms (e : Expr) : MetaM (Array Expr) :=
  return sepAtoms.go (← instantiateMVars e)

def sepConjOfAtoms (atoms : Array Expr) : Expr :=
  if atoms.isEmpty then mkConst ``emp
  else atoms[1:].foldl (fun acc a => mkApp2 (mkConst ``sepConj) acc a) atoms[0]!

/-- Match and remove `cancel` atoms from `pre`. Returns `(remaining, matched)` or `none`. -/
def matchSepAtoms (pre cancel : Expr) : MetaM (Option (Array Expr × Array Expr)) := do
  let mut rest ← sepAtoms pre
  let mut matched : Array Expr := #[]
  for atom in (← sepAtoms cancel) do
    -- `withoutModifyingMCtx`: a failed near-miss must not pin schematic mvars.
    let some i ← rest.findIdxM? fun cand => withoutModifyingMCtx (isDefEq atom cand)
      | return none
    matched := matched.push rest[i]!
    rest := rest.eraseIdxIfInBounds i
  return some (rest, matched)

def proveSepConjLe (pre rhs : Expr) : MetaM (Option Expr) := do
  if ← isDefEq pre rhs then
    return some (← mkAppM ``PartialOrder.rel_of_eq #[← mkEqRefl pre])
  let eqTy ← mkEq pre rhs
  let eqMVar ← mkFreshExprSyntheticOpaqueMVar eqTy
  try
    Lean.Meta.AC.rewriteUnnormalizedRefl eqMVar.mvarId!
    let eq ← instantiateMVars eqMVar
    return some (← mkAppM ``PartialOrder.rel_of_eq #[eq])
  catch _ =>
    return none

/-- A `FrameSplit` cancelling `frame` off the precondition, with the split VC proved by
AC-rearrangement of `∗`. -/
def mkSepFrameSplit (pre frame footprint : Expr) : MetaM FrameSplit := do
  let proof? ← proveSepConjLe pre (mkApp2 (mkConst ``sepConj) frame footprint)
  return { frame, footprint? := some footprint, proof? }

/-- Automatic frame inference by domain difference: the spec's precondition's atoms (its footprint)
are cancelled from the goal precondition's; the leftover atoms are the frame. A pinned `frames`
resource cancels its own atoms instead, leaving the split VC open when they are missing. -/
def sepConjFrameProc : FrameInferenceProc := fun _R pre _info specPre frame? => do
  match frame? with
  | some frame =>
    match ← matchSepAtoms pre frame with
    | none => return some { frame, footprint? := some pre }
    | some (rest, _) => return some (← mkSepFrameSplit pre frame (sepConjOfAtoms rest))
  | none =>
    let some (rest, matched) ← matchSepAtoms pre specPre | return none
    if rest.isEmpty then return none
    return some (← mkSepFrameSplit pre (sepConjOfAtoms rest) (sepConjOfAtoms matched))

@[frameproc] def heapFP : FrameProc where
  prog := ``HeapM
  mkOpAppM := fun _ => pure (mkConst ``sepConj)
  resourceTy := fun _ => pure (mkConst ``HProp)
  opHead := ``sepConj
  proc := sepConjFrameProc

example (l1 l2 a b x : Nat) :
    ⦃ l1 ↦ a ∗ l2 ↦ b ⦄ (store l1 x) ⦃ fun _ => l1 ↦ x ∗ l2 ↦ b ⦄ := by
  vcgen [store_spec] with finish

example (l1 l2 a b x : Nat) :
    ⦃ l1 ↦ a ∗ l2 ↦ b ⦄ (store l1 x) ⦃ fun _ => l1 ↦ x ∗ l2 ↦ b ⦄ := by
  vcgen [store_spec] frames | store l1 x => (l2 ↦ b) with finish

example (l1 l2 a b : Nat) :
    ⦃ l1 ↦ a ∗ l2 ↦ b ⦄ (load l1) ⦃ fun r => l2 ↦ b ∗ sepPure (r = a) ∗ l1 ↦ a ⦄ := by
  vcgen [load_spec] with finish

/-! ## Doubly-linked lists and in-place reverse

`IsList xs back p` asserts that `p` roots a null-terminated doubly-linked list whose **payloads** are
`xs`, and that the head cell's prev field equals `back`. A cons node at `p` stores next at `p`,
prev at `p + 1`, and the head payload at `p + 2` (C field order; and `p ≠ null`). The program
`reverse` takes only a head pointer; `xs` is ghost in the specification. -/

/-- Pointwise characterization of an embedded-guard assertion. -/
theorem ofProp_meet_apply (φ : Prop) (P : HProp) (h : Heap) : (⌜φ⌝ ⊓ P) h ↔ φ ∧ P h := by
  constructor
  · intro hp
    refine ⟨?_, (meet_le_right (⌜φ⌝ : HProp) P) h hp⟩
    have hφ : (⌜φ⌝ : HProp) h := (meet_le_left (⌜φ⌝ : HProp) P) h hp
    simp only [CompleteLattice.ofProp] at hφ
    split at hφ
    · assumption
    · exact False.elim <| (bot_le (x := (fun _ => False : HProp))) h hφ
  · intro ⟨hφ, hP⟩
    exact (le_meet P ⌜φ⌝ P (le_ofProp P φ hφ) PartialOrder.rel_refl) h hP

/-- Doubly-linked list segment: payloads `xs`, head at `p`, head-prev `back`.
Node layout: `p ↦ next ∗ (p+1) ↦ prev ∗ (p+2) ↦ payload`. -/
noncomputable def IsList : List Nat → Nat → Nat → HProp
  | [], _back, p => sepPure (p = null)
  | v :: vs, back, p =>
      ⌜p ≠ null⌝ ⊓ ⨆ n, p ↦ n ∗ (p + 1) ↦ back ∗ (p + 2) ↦ v ∗ IsList vs p n

@[grind =] theorem IsList_nil_eq (back p : Nat) : IsList [] back p = sepPure (p = null) := rfl

@[grind =] theorem IsList_cons_eq (v : Nat) (vs : List Nat) (back p : Nat) :
    IsList (v :: vs) back p =
      ⌜p ≠ null⌝ ⊓ ⨆ n, p ↦ n ∗ (p + 1) ↦ back ∗ (p + 2) ↦ v ∗ IsList vs p n := rfl

@[grind =] theorem IsList_nil_null (back : Nat) : IsList [] back null = emp := by
  funext h; apply propext
  simp [IsList_nil_eq, sepPure_apply]

theorem IsList_cons_elim {v : Nat} {vs : List Nat} {back p : Nat} {h : Heap}
    (hl : IsList (v :: vs) back p h) :
    p ≠ null ∧ ∃ n, (p ↦ n ∗ (p + 1) ↦ back ∗ (p + 2) ↦ v ∗ IsList vs p n) h := by
  rw [IsList_cons_eq] at hl
  exact ((ofProp_meet_apply _ _ _).mp hl).imp_right fun hh => (iSup_hprop_apply _ _).mp hh

@[grind ←]
theorem IsList_cons_intro (v n back : Nat) (vs : List Nat) (p : Nat) (hp : p ≠ null) :
    (p ↦ n ∗ (p + 1) ↦ back ∗ (p + 2) ↦ v ∗ IsList vs p n) ⊑ IsList (v :: vs) back p := by
  intro h hh
  exact (ofProp_meet_apply _ _ _).mpr ⟨hp, (iSup_hprop_apply _ _).mpr ⟨n, hh⟩⟩

/-- Load the next-pointer of a cons cell; the loaded value is the `IsList` witness.
Higher priority than `load_spec` so `vcgen` prefers the `IsList`-shaped precondition. -/
@[spec high] theorem load_next_IsList (v : Nat) (vs : List Nat) (back curr : Nat) :
    ⦃ IsList (v :: vs) back curr ⦄
      load curr
    ⦃ fun next =>
        ⌜curr ≠ null⌝ ⊓
          (curr ↦ next ∗ (curr + 1) ↦ back ∗ (curr + 2) ↦ v ∗ IsList vs curr next) ⦄ := by
  simp only [IsList_cons_eq]
  vcgen [load_spec] with finish

/-- After rewriting next and prev, rebuild the cons cell onto the accumulator; the `curr ≠ null`
guard reaches the context through precondition normalization, and `grind`'s AC theory for `∗`
matches the statement against the association the framed `store`s leave in the VC. -/
@[grind .]
theorem reverse_store_handoff_le (v : Nat) (vs ys : List Nat) (curr next prev : Nat)
    (hpne : curr ≠ null) :
    IsList ys curr prev ∗ (curr + 2) ↦ v ∗ IsList vs curr next ∗ curr ↦ prev ∗ (curr + 1) ↦ next
      ⊑ IsList vs curr next ∗ IsList (v :: ys) next curr := by
  intro h hh
  have heq :
      (IsList ys curr prev ∗ (curr + 2) ↦ v ∗ IsList vs curr next ∗ curr ↦ prev ∗
          (curr + 1) ↦ next) =
        ((curr ↦ prev ∗ (curr + 1) ↦ next ∗ (curr + 2) ↦ v ∗ IsList ys curr prev) ∗
          IsList vs curr next) := by
    grind
  rw [heq] at hh
  obtain ⟨h₁, h₂, hd, rfl, hnode, hvs⟩ := hh
  exact ⟨h₂, h₁, Heap.disjoint_comm hd, Heap.union_comm hd, hvs,
    IsList_cons_intro v prev next ys curr hpne h₁ hnode⟩

/-- When the remaining segment is empty, `curr = null` and the accumulator is the whole result. -/
@[grind .] theorem IsList_nil_acc_le (ys : List Nat) (curr prev : Nat) :
    (sepPure (curr = null) ∗ IsList ys curr prev) ⊑ IsList ys null prev := by
  intro h hh
  have ⟨rfl, hys⟩ := (sepPure_sepConj_iff (curr = null) (IsList ys curr prev) h).mp hh
  exact hys

@[grind =] theorem IsList_append_nil (xs : List Nat) (back r : Nat) :
    IsList (xs ++ ([] : List Nat)) back r = IsList xs back r := by
  simp

/-- Fuel-bounded reverse accumulator: only pointers in the program. At each cons cell, swap the
next/prev links (`next := prev`, `prev := old next`). `fuel` bounds the remaining spine length. -/
def reverse.go (fuel : Nat) (curr prev : Nat) : HeapM Nat :=
  match fuel with
  | 0 => pure prev
  | fuel + 1 => do
    if curr = null then
      pure prev
    else
      let next ← load curr
      store curr prev
      store (curr + 1) next
      reverse.go fuel next curr

/-- In-place reverse with fuel `xs.length` in the specification. -/
def reverse (fuel : Nat) (head : Nat) : HeapM Nat :=
  reverse.go fuel head null

/-- Accumulator specification — both induction cases are `vcgen` scripts.
Pre: remaining segment `xs` at `curr` with back-pointer `prev`, plus reversed segment `ys` at `prev`
with back-pointer `curr`. -/
@[spec] theorem reverse.go_spec (fuel : Nat) (xs ys : List Nat) (curr prev : Nat)
    (hle : xs.length ≤ fuel) :
    ⦃ IsList xs prev curr ∗ IsList ys curr prev ⦄
      reverse.go fuel curr prev
    ⦃ fun r => IsList (xs.reverse ++ ys) null r ⦄ := by
  induction xs generalizing fuel curr prev ys with
  | nil =>
    cases fuel with
    | zero =>
      simp only [reverse.go, IsList_nil_eq, List.reverse_nil, List.nil_append]
      vcgen with (try finish; try (exact IsList_nil_acc_le _ _ _))
    | succ fuel =>
      simp only [reverse.go, IsList_nil_eq, List.reverse_nil, List.nil_append]
      -- `go` still branches on `curr = null`; the `≠` arm is absurd under `IsList []`.
      split
      · vcgen with (try finish; try (exact IsList_nil_acc_le _ _ _))
      · rename_i hne
        constructor
        intro h hh
        have ⟨hc, _⟩ :=
          (sepPure_sepConj_iff (curr = null) (IsList ys curr prev) h).mp hh
        exact (hne hc).elim
  | cons v vs ih =>
    match fuel, hle with
    | 0, hle =>
      simp at hle
    | fuel + 1, hle =>
      simp only [reverse.go, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons] at hle ⊢
      -- `go` branches on `curr = null`; the `=` arm is absurd under `IsList (v :: vs)`.
      split
      · rename_i hc
        constructor
        intro h hh
        obtain ⟨h₁, _, _, _, hl, _⟩ := hh
        exact ((IsList_cons_elim hl).1 hc).elim
      · -- Prefer `load_next_IsList`; IH after `generalizing` is `fuel ys curr prev`.
        vcgen [-load_spec, load_next_IsList, store_spec,
          fun next => ih fuel (v :: ys) next curr (Nat.le_of_succ_le_succ hle)] with
          (try finish; try (exact reverse_store_handoff_le _ _ _ _ _ _))

@[spec] theorem reverse_spec (xs : List Nat) (head : Nat) :
    ⦃ IsList xs null head ⦄ reverse xs.length head ⦃ fun r => IsList xs.reverse null r ⦄ := by
  simp only [reverse]
  -- Pin `ys`/`prev` via an explicit accumulator instance of the schematic `@[spec]`.
  vcgen [-reverse.go_spec, reverse.go_spec xs.length xs [] head null (Nat.le_refl _)] with
    (try finish; try (simp [IsList_nil_null, sepConj_emp, IsList_append_nil]; finish))

example (xs : List Nat) (head l v : Nat) :
    ⦃ l ↦ v ∗ IsList xs null head ⦄ (reverse xs.length head)
      ⦃ fun r => l ↦ v ∗ IsList xs.reverse null r ⦄ := by
  vcgen [reverse_spec] with finish
