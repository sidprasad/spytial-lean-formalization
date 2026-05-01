/-
# Input.lean — A type system for spytial inputs

The constraint *rules* of a `Spec` stay constant; the *atoms* and *selectors*
of an `Input` evolve.  This file casts that asymmetry as a type system —
*purely* the type story, with no denotational interpretation.  All
denotational lifting lives in `Interpretation.lean`, which is gated on the
typing judgment so that ill-typed inputs cannot be interpreted at all.

## Typing rules

`WellTyped S I` is a structure with four typing premises:

* **(SCOPE)**     every rule's selector ⊆ `I.atoms`
* **(ARITY₁)**    binary shapes have empty `resolve₁` (operationally arity-correct)
* **(ARITY₂)**    unary shapes have empty `resolve₂`
* **(HIDE-GEOM)** when `S` requires hiding atoms (`always`-mode `.hideatom`),
                  no other `always`-mode geometric rule may reference any
                  hidden atom.

## Operational steps

`Step I I'` has four constructors corresponding to user-level operations:
`addAtom`, `removeAtom`, `setSel₁`, `setSel₂`.  Arity-correctness for
`setSel₁/₂` is enforced *operationally* — they only apply at unary/binary
shapes, respectively, so writing a unary selector to a binary slot is not
constructible.

### Note on selector semantics

In this model, selectors are *fixed* finite atom sets — `resolve₁/₂` returns
a literal `Finset Atom`, not a query against the atom set.  Consequently,
`addAtom` is genuinely atomic: it does not change any selector's value.

In real spytial usage, selectors are often queries (e.g. "all atoms of type
Int"), in which case adding an atom *can* change a selector's resolution.
Modelling that would require either (a) selectors as functions of the atom
set, or (b) a compound `addAtom + reselect` step.  Either is a follow-up.

## Gating

`TypedInput S` carries a proof of `WellTyped S input`.  The interpretation
in `Interpretation.lean` only takes `TypedInput`, never a bare `Input`.
-/

import Main

namespace Spytial

--------------------------------------------------------------------------------
-- ConstraintShape: a Constraint minus its selector
--------------------------------------------------------------------------------

inductive ConstraintShape where
| orientation : Direction → ConstraintShape
| align       : AlignDir  → ConstraintShape
| cyclic      : Rotation  → ConstraintShape
| group₁      : ConstraintShape
| group₂      : (addEdge : Bool) → ConstraintShape
| size        : (w h : ℚ) → ConstraintShape
| hideatom    : ConstraintShape
deriving DecidableEq, Repr

inductive Arity | unary | binary
deriving DecidableEq, Repr

def shapeArity : ConstraintShape → Arity
| .orientation _ | .align _ | .cyclic _ | .group₂ _ => .binary
| .group₁ | .size _ _ | .hideatom                   => .unary

/-- A shape is *geometric* iff it requires its atoms to have boxes (i.e.
    be visible).  Every shape except `.hideatom` is geometric. -/
def isGeometric : ConstraintShape → Bool
| .hideatom => false
| _         => true

--------------------------------------------------------------------------------
-- SpecRule and Spec (the constant part)
--------------------------------------------------------------------------------

structure SpecRule where
  shape : ConstraintShape
  holds : HoldsMode := .always
deriving DecidableEq, Repr

abbrev Spec := Finset SpecRule

--------------------------------------------------------------------------------
-- Input (the varying part)
--------------------------------------------------------------------------------

structure Input where
  atoms    : Finset Atom
  resolve₁ : ConstraintShape → Selector₁
  resolve₂ : ConstraintShape → Selector₂

/-- The atoms a rule "talks about" given the input's selector resolution.

    Defined conservatively as the union of *both* resolvers' atoms at
    `r.shape`.  In a `WellTyped` input, the ARITY rules guarantee that
    only the resolver appropriate to the shape's arity is non-empty, so
    this union has only one nonempty term in practice — but stating it
    as a union makes proof reasoning uniform. -/
def selectedAtoms (I : Input) (r : SpecRule) : Finset Atom :=
  I.resolve₁ r.shape ∪
  (I.resolve₂ r.shape).image Prod.fst ∪
  (I.resolve₂ r.shape).image Prod.snd

--------------------------------------------------------------------------------
-- The typing judgment
--------------------------------------------------------------------------------

/-- `WellTyped S I` — input `I` is structurally compatible with spec `S`. -/
structure WellTyped (S : Spec) (I : Input) : Prop where
  /-- (SCOPE) Every rule's selector references only in-scope atoms. -/
  scope :
    ∀ r ∈ S, selectedAtoms I r ⊆ I.atoms
  /-- (ARITY₁) Binary shapes have empty `resolve₁`. -/
  arity₁ :
    ∀ sh, shapeArity sh = Arity.binary → I.resolve₁ sh = ∅
  /-- (ARITY₂) Unary shapes have empty `resolve₂`. -/
  arity₂ :
    ∀ sh, shapeArity sh = Arity.unary → I.resolve₂ sh = ∅
  /-- (HIDE-GEOM) When `S` requires hiding atoms, no other `always`-mode
      geometric rule may reference any hidden atom. -/
  hide_geom :
    ⟨ConstraintShape.hideatom, HoldsMode.always⟩ ∈ S →
    ∀ rG ∈ S, rG.holds = HoldsMode.always → isGeometric rG.shape = true →
    Disjoint (I.resolve₁ ConstraintShape.hideatom) (selectedAtoms I rG)

--------------------------------------------------------------------------------
-- Operational steps
--------------------------------------------------------------------------------

def Input.addAtom (I : Input) (a : Atom) : Input :=
  { I with atoms := insert a I.atoms }

def Input.removeAtom (I : Input) (a : Atom) : Input :=
  { I with atoms := I.atoms.erase a }

def Input.setSel₁ (I : Input) (sh : ConstraintShape) (v : Selector₁) : Input :=
  { I with resolve₁ := Function.update I.resolve₁ sh v }

def Input.setSel₂ (I : Input) (sh : ConstraintShape) (v : Selector₂) : Input :=
  { I with resolve₂ := Function.update I.resolve₂ sh v }

/-- The four atomic operations on inputs.  `setSel₁/₂` carry an arity
    precondition so that writing a unary selector to a binary slot
    (or vice-versa) is not constructible. -/
inductive Step : Input → Input → Prop where
| addAtom    (I : Input) (a : Atom) :
    Step I (I.addAtom a)
| removeAtom (I : Input) (a : Atom) :
    Step I (I.removeAtom a)
| setSel₁    (I : Input) (sh : ConstraintShape) (v : Selector₁)
             (h : shapeArity sh = Arity.unary) :
    Step I (I.setSel₁ sh v)
| setSel₂    (I : Input) (sh : ConstraintShape) (v : Selector₂)
             (h : shapeArity sh = Arity.binary) :
    Step I (I.setSel₂ sh v)

--------------------------------------------------------------------------------
-- Helper @[simp] lemmas: how the structure projects through each step
--------------------------------------------------------------------------------

@[simp] lemma resolve₁_addAtom (I : Input) (a : Atom) :
    (I.addAtom a).resolve₁ = I.resolve₁ := rfl

@[simp] lemma resolve₂_addAtom (I : Input) (a : Atom) :
    (I.addAtom a).resolve₂ = I.resolve₂ := rfl

@[simp] lemma atoms_addAtom (I : Input) (a : Atom) :
    (I.addAtom a).atoms = insert a I.atoms := rfl

@[simp] lemma resolve₁_removeAtom (I : Input) (a : Atom) :
    (I.removeAtom a).resolve₁ = I.resolve₁ := rfl

@[simp] lemma resolve₂_removeAtom (I : Input) (a : Atom) :
    (I.removeAtom a).resolve₂ = I.resolve₂ := rfl

@[simp] lemma atoms_removeAtom (I : Input) (a : Atom) :
    (I.removeAtom a).atoms = I.atoms.erase a := rfl

@[simp] lemma atoms_setSel₁ (I : Input) (sh : ConstraintShape) (v : Selector₁) :
    (I.setSel₁ sh v).atoms = I.atoms := rfl

@[simp] lemma atoms_setSel₂ (I : Input) (sh : ConstraintShape) (v : Selector₂) :
    (I.setSel₂ sh v).atoms = I.atoms := rfl

@[simp] lemma resolve₁_setSel₁ (I : Input) (sh : ConstraintShape) (v : Selector₁) :
    (I.setSel₁ sh v).resolve₁ = Function.update I.resolve₁ sh v := rfl

@[simp] lemma resolve₂_setSel₁ (I : Input) (sh : ConstraintShape) (v : Selector₁) :
    (I.setSel₁ sh v).resolve₂ = I.resolve₂ := rfl

@[simp] lemma resolve₁_setSel₂ (I : Input) (sh : ConstraintShape) (v : Selector₂) :
    (I.setSel₂ sh v).resolve₁ = I.resolve₁ := rfl

@[simp] lemma resolve₂_setSel₂ (I : Input) (sh : ConstraintShape) (v : Selector₂) :
    (I.setSel₂ sh v).resolve₂ = Function.update I.resolve₂ sh v := rfl

@[simp] lemma selectedAtoms_addAtom (I : Input) (a : Atom) (r : SpecRule) :
    selectedAtoms (I.addAtom a) r = selectedAtoms I r := rfl

@[simp] lemma selectedAtoms_removeAtom (I : Input) (a : Atom) (r : SpecRule) :
    selectedAtoms (I.removeAtom a) r = selectedAtoms I r := rfl

--------------------------------------------------------------------------------
-- Preservation (subject reduction)
--------------------------------------------------------------------------------

/-- **addAtom always preserves typing.** Atoms grow; selectors are unchanged,
    so ARITY and HIDE-GEOM trivially carry over, and SCOPE only loosens. -/
theorem WellTyped.preserve_addAtom {S : Spec} {I : Input}
    (hWT : WellTyped S I) (a : Atom) :
    WellTyped S (I.addAtom a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [selectedAtoms_addAtom]
    exact (hWT.scope r hr).trans (Finset.subset_insert _ _)
  · exact hWT.arity₁
  · exact hWT.arity₂
  · intro hHide rG hr hh hg
    exact hWT.hide_geom hHide rG hr hh hg

/-- **removeAtom preserves typing iff the removed atom is unreferenced.**
    Resolvers are unchanged, so ARITY and HIDE-GEOM are automatic; only
    SCOPE needs the unreferenced obligation. -/
theorem WellTyped.preserve_removeAtom {S : Spec} {I : Input}
    (hWT : WellTyped S I) (a : Atom)
    (hUnref : ∀ r ∈ S, a ∉ selectedAtoms I r) :
    WellTyped S (I.removeAtom a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr x hx
    rw [selectedAtoms_removeAtom] at hx
    show x ∈ I.atoms.erase a
    rw [Finset.mem_erase]
    refine ⟨?_, hWT.scope r hr hx⟩
    rintro rfl; exact hUnref r hr hx
  · exact hWT.arity₁
  · exact hWT.arity₂
  · intro hHide rG hr hh hg
    exact hWT.hide_geom hHide rG hr hh hg

/-- **setSel₁ preservation** at a unary shape `sh`.

    Three structural obligations beyond `hWT`:
    * `hScope`   — the new selector `v` is in scope of `I.atoms`,
    * `hHide_a`  — if `sh = .hideatom`, the new hidden set `v` is disjoint
                  from every positive geometric rule's selected atoms,
    * `hHide_b`  — if `sh ≠ .hideatom` (so `sh` is geometric unary), and
                  there is an `always`-mode rule with shape `sh`, the
                  current hidden set is disjoint from `v`.

    ARITY₁/ARITY₂ preservation is automatic from `hArity`. -/
theorem WellTyped.preserve_setSel₁ {S : Spec} {I : Input}
    (hWT : WellTyped S I) (sh : ConstraintShape) (v : Selector₁)
    (hArity : shapeArity sh = Arity.unary)
    (hScope : v ⊆ I.atoms)
    (hHide_a :
      sh = ConstraintShape.hideatom →
      ⟨ConstraintShape.hideatom, HoldsMode.always⟩ ∈ S →
      ∀ rG ∈ S, rG.holds = HoldsMode.always → isGeometric rG.shape = true →
      Disjoint v (selectedAtoms I rG))
    (hHide_b :
      sh ≠ ConstraintShape.hideatom →
      ⟨ConstraintShape.hideatom, HoldsMode.always⟩ ∈ S →
      ∀ rG ∈ S, rG.shape = sh → rG.holds = HoldsMode.always →
      Disjoint (I.resolve₁ ConstraintShape.hideatom) v) :
    WellTyped S (I.setSel₁ sh v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- SCOPE
    intro r hr x hx
    show x ∈ I.atoms
    simp only [selectedAtoms, resolve₁_setSel₁, resolve₂_setSel₁] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hupd | hf
      · by_cases hsh : r.shape = sh
        · rw [hsh, Function.update_self] at hupd
          exact hScope hupd
        · rw [Function.update_of_ne hsh] at hupd
          exact hWT.scope r hr (Finset.mem_union_left _ (Finset.mem_union_left _ hupd))
      · exact hWT.scope r hr (Finset.mem_union_left _ (Finset.mem_union_right _ hf))
    · exact hWT.scope r hr (Finset.mem_union_right _ hx)
  · -- ARITY₁: sh is unary, so binary slots are unchanged.
    intro sh' hsh'
    have hne : sh' ≠ sh := by
      intro heq; rw [heq] at hsh'; rw [hsh'] at hArity; cases hArity
    show Function.update I.resolve₁ sh v sh' = ∅
    rw [Function.update_of_ne hne]
    exact hWT.arity₁ sh' hsh'
  · -- ARITY₂: resolve₂ unchanged.
    exact hWT.arity₂
  · -- HIDE-GEOM
    intro hHide rG hr hh hg
    show Disjoint ((I.setSel₁ sh v).resolve₁ ConstraintShape.hideatom)
                  (selectedAtoms (I.setSel₁ sh v) rG)
    by_cases hsh : sh = ConstraintShape.hideatom
    · -- sh = .hideatom: hidden becomes v.
      have hresolve : (I.setSel₁ sh v).resolve₁ ConstraintShape.hideatom = v := by
        simp only [resolve₁_setSel₁]; rw [hsh]; exact Function.update_self _ _ _
      rw [hresolve]
      have hrG_ne_sh : rG.shape ≠ sh := by
        intro heq; rw [heq, hsh] at hg; simp [isGeometric] at hg
      have hsel : selectedAtoms (I.setSel₁ sh v) rG = selectedAtoms I rG := by
        simp only [selectedAtoms, resolve₁_setSel₁, resolve₂_setSel₁]
        rw [Function.update_of_ne hrG_ne_sh]
      rw [hsel]
      exact hHide_a hsh hHide rG hr hh hg
    · -- sh ≠ .hideatom: hidden unchanged.
      have hresolve : (I.setSel₁ sh v).resolve₁ ConstraintShape.hideatom
                       = I.resolve₁ ConstraintShape.hideatom := by
        simp only [resolve₁_setSel₁]
        exact Function.update_of_ne (Ne.symm hsh) _ _
      rw [hresolve]
      by_cases hrGsh : rG.shape = sh
      · -- rG.shape = sh: selectedAtoms = v (using arity₂ to drop resolve₂).
        have hres2 : I.resolve₂ sh = ∅ := hWT.arity₂ sh hArity
        have hsel : selectedAtoms (I.setSel₁ sh v) rG = v := by
          simp only [selectedAtoms, resolve₁_setSel₁, resolve₂_setSel₁]
          rw [hrGsh, Function.update_self, hres2]; simp
        rw [hsel]
        exact hHide_b hsh hHide rG hr hrGsh hh
      · -- rG.shape ≠ sh: selectedAtoms unchanged.
        have hsel : selectedAtoms (I.setSel₁ sh v) rG = selectedAtoms I rG := by
          simp only [selectedAtoms, resolve₁_setSel₁, resolve₂_setSel₁]
          rw [Function.update_of_ne hrGsh]
        rw [hsel]
        exact hWT.hide_geom hHide rG hr hh hg

/-- **setSel₂ preservation** at a binary shape `sh`.

    Obligations: scope on both projections of `v`, plus a HIDE-GEOM
    obligation for any `always`-mode rule with shape `sh`. -/
theorem WellTyped.preserve_setSel₂ {S : Spec} {I : Input}
    (hWT : WellTyped S I) (sh : ConstraintShape) (v : Selector₂)
    (hArity : shapeArity sh = Arity.binary)
    (hScopeFst : v.image Prod.fst ⊆ I.atoms)
    (hScopeSnd : v.image Prod.snd ⊆ I.atoms)
    (hHide :
      ⟨ConstraintShape.hideatom, HoldsMode.always⟩ ∈ S →
      ∀ rG ∈ S, rG.shape = sh → rG.holds = HoldsMode.always →
      Disjoint (I.resolve₁ ConstraintShape.hideatom)
               (v.image Prod.fst ∪ v.image Prod.snd)) :
    WellTyped S (I.setSel₂ sh v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- SCOPE
    intro r hr x hx
    show x ∈ I.atoms
    simp only [selectedAtoms, resolve₁_setSel₂, resolve₂_setSel₂] at hx
    rcases Finset.mem_union.mp hx with hx | hsnd
    · rcases Finset.mem_union.mp hx with hr1 | hfst
      · exact hWT.scope r hr (Finset.mem_union_left _ (Finset.mem_union_left _ hr1))
      · by_cases hsh : r.shape = sh
        · rw [hsh, Function.update_self] at hfst
          exact hScopeFst hfst
        · rw [Function.update_of_ne hsh] at hfst
          exact hWT.scope r hr (Finset.mem_union_left _ (Finset.mem_union_right _ hfst))
    · by_cases hsh : r.shape = sh
      · rw [hsh, Function.update_self] at hsnd
        exact hScopeSnd hsnd
      · rw [Function.update_of_ne hsh] at hsnd
        exact hWT.scope r hr (Finset.mem_union_right _ hsnd)
  · -- ARITY₁: resolve₁ unchanged.
    exact hWT.arity₁
  · -- ARITY₂: sh is binary, so unary slots are unchanged.
    intro sh' hsh'
    have hne : sh' ≠ sh := by
      intro heq; rw [heq] at hsh'; rw [hsh'] at hArity; cases hArity
    show Function.update I.resolve₂ sh v sh' = ∅
    rw [Function.update_of_ne hne]
    exact hWT.arity₂ sh' hsh'
  · -- HIDE-GEOM
    intro hHideMem rG hr hh hg
    show Disjoint (I.resolve₁ ConstraintShape.hideatom)
                  (selectedAtoms (I.setSel₂ sh v) rG)
    by_cases hrGsh : rG.shape = sh
    · -- rG.shape = sh: selectedAtoms = v.image fst ∪ v.image snd.
      have hres1 : I.resolve₁ sh = ∅ := hWT.arity₁ sh hArity
      have hsel : selectedAtoms (I.setSel₂ sh v) rG
                   = v.image Prod.fst ∪ v.image Prod.snd := by
        simp only [selectedAtoms, resolve₁_setSel₂, resolve₂_setSel₂]
        rw [hrGsh, Function.update_self, hres1]; simp
      rw [hsel]
      exact hHide hHideMem rG hr hrGsh hh
    · -- rG.shape ≠ sh: selectedAtoms unchanged.
      have hsel : selectedAtoms (I.setSel₂ sh v) rG = selectedAtoms I rG := by
        simp only [selectedAtoms, resolve₁_setSel₂, resolve₂_setSel₂]
        rw [Function.update_of_ne hrGsh]
      rw [hsel]
      exact hWT.hide_geom hHideMem rG hr hh hg

--------------------------------------------------------------------------------
-- TypedInput: the gate
--
-- This is the only way to interpret an input.  It bundles an `Input` with
-- a proof that it is well-typed under a specific `Spec`.  Code that wants
-- to interpret a spec at an input must take a `TypedInput`, not a bare
-- `Input` — see `Interpretation.lean`.
--------------------------------------------------------------------------------

structure TypedInput (S : Spec) where
  input : Input
  wellTyped : WellTyped S input

/-- Antimonotonicity of typing in the spec context: `WellTyped` is preserved
    by removing rules.  HIDE-GEOM and SCOPE become weaker (fewer rules to
    constrain), and ARITY does not depend on `S`. -/
theorem WellTyped.antimono {S₁ S₂ : Spec} (hSub : S₁ ⊆ S₂) {I : Input}
    (hWT : WellTyped S₂ I) :
    WellTyped S₁ I := by
  refine ⟨?_, hWT.arity₁, hWT.arity₂, ?_⟩
  · intro r hr; exact hWT.scope r (hSub hr)
  · intro hHide rG hr hh hg
    exact hWT.hide_geom (hSub hHide) rG (hSub hr) hh hg

/-- A `TypedInput (S₁ ∪ S₂)` projects to `TypedInput S₁` and `TypedInput S₂`
    via antimonotonicity. -/
def TypedInput.restrictLeft {S₁ S₂ : Spec} (TI : TypedInput (S₁ ∪ S₂)) :
    TypedInput S₁ :=
  ⟨TI.input, TI.wellTyped.antimono Finset.subset_union_left⟩

def TypedInput.restrictRight {S₁ S₂ : Spec} (TI : TypedInput (S₁ ∪ S₂)) :
    TypedInput S₂ :=
  ⟨TI.input, TI.wellTyped.antimono Finset.subset_union_right⟩

--------------------------------------------------------------------------------
-- Public API
--------------------------------------------------------------------------------

#check @WellTyped
#check @Step
#check @WellTyped.preserve_addAtom
#check @WellTyped.preserve_removeAtom
#check @WellTyped.preserve_setSel₁
#check @WellTyped.preserve_setSel₂
#check @WellTyped.antimono
#check @TypedInput
#check @TypedInput.restrictLeft
#check @TypedInput.restrictRight

end Spytial
