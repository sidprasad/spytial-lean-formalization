/-
# Input.lean — A type system for spytial inputs

The constraint *rules* of a `Spec` stay constant; the *atoms* and *selectors*
of an `Input` evolve.  This file casts that asymmetry as a type system:

* a `Spec` is a typing context,
* an `Input` is a term,
* `WellTyped S I` is the typing judgment,
* `Step` is the operational step relation, with four constructors —
  `addAtom`, `removeAtom`, `setSel₁`, `setSel₂` — exactly the user-level
  operations of (1) atom added, (2) atom removed, (3) selector changed
  (split by arity).

The single typing rule is **SCOPE**: every rule's selector references only
atoms in `I.atoms`. The preservation (subject-reduction) theorems below
say exactly which steps keep `S ⊢ I`.

The denotational lifting (`Spec.atInput`, `spec_compose_at`, …) is kept
alongside as a separate algebra: semantics and typing live side by side
and do not interfere.

A natural extension is a second typing rule **HIDE-GEOM** — that hidden
atoms cannot participate in any positive geometric rule. Sketched at the
end as `HideGeomDisj`; its preservation theorems are left as future work.
-/

import Main

open Spytial

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

/-- A shape is *geometric* iff it requires its atoms to have boxes.
    Used by the (planned) HIDE-GEOM typing rule below. -/
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
--
-- Resolvers are keyed on `ConstraintShape` (not `SpecRule`) so that rules
-- with the same shape but different `HoldsMode` resolve to the *same*
-- selector — essential for `always_never_unsat_at`.
--------------------------------------------------------------------------------

structure Input where
  atoms    : Finset Atom
  resolve₁ : ConstraintShape → Selector₁
  resolve₂ : ConstraintShape → Selector₂

/-- The atoms a rule "talks about" given the input's selector resolution.

    Conservatively defined as the union of *both* resolvers' atoms at
    `r.shape`, regardless of the rule's arity. This is a slightly stronger
    typing invariant than strictly necessary (a binary rule's `resolve₁`
    is irrelevant to its semantics), but in exchange the type system has
    very clean preservation proofs. Users supply `∅` for unused resolvers. -/
def selectedAtoms (I : Input) (r : SpecRule) : Finset Atom :=
  I.resolve₁ r.shape ∪
  (I.resolve₂ r.shape).image Prod.fst ∪
  (I.resolve₂ r.shape).image Prod.snd

--------------------------------------------------------------------------------
-- Typing judgment
--
-- One typing rule:
--   (SCOPE)  ∀ r ∈ S, selectedAtoms I r ⊆ I.atoms.
--------------------------------------------------------------------------------

/-- `WellTyped S I` — input `I` is structurally compatible with spec `S`:
    every rule's selector references only atoms in scope. -/
def WellTyped (S : Spec) (I : Input) : Prop :=
  ∀ r ∈ S, selectedAtoms I r ⊆ I.atoms

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

/-- The four atomic operations on inputs. -/
inductive Step : Input → Input → Prop where
| addAtom    (I : Input) (a : Atom)                              : Step I (I.addAtom a)
| removeAtom (I : Input) (a : Atom)                              : Step I (I.removeAtom a)
| setSel₁    (I : Input) (sh : ConstraintShape) (v : Selector₁)  : Step I (I.setSel₁ sh v)
| setSel₂    (I : Input) (sh : ConstraintShape) (v : Selector₂)  : Step I (I.setSel₂ sh v)

--------------------------------------------------------------------------------
-- selectedAtoms behaviour under each step (helper lemmas)
--------------------------------------------------------------------------------

@[simp] lemma selectedAtoms_addAtom (I : Input) (a : Atom) (r : SpecRule) :
    selectedAtoms (I.addAtom a) r = selectedAtoms I r := rfl

@[simp] lemma selectedAtoms_removeAtom (I : Input) (a : Atom) (r : SpecRule) :
    selectedAtoms (I.removeAtom a) r = selectedAtoms I r := rfl

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

--------------------------------------------------------------------------------
-- Preservation (subject reduction)
--------------------------------------------------------------------------------

/- TODO: I think it is actually much more complicated. Add atom could also affect selectors right?

Like a selector grabs all Ints, then you add an Int, and now the selector references an atom that is in scope
but wasn't before. So you need to either model this as "compound" step[s?]

-/


/-- **addAtom always preserves typing.** Atoms grow, selectors are unchanged. -/
theorem WellTyped.preserve_addAtom {S : Spec} {I : Input}
    (hWT : WellTyped S I) (a : Atom) :
    WellTyped S (I.addAtom a) := by
  intro r hr
  rw [selectedAtoms_addAtom]
  exact (hWT r hr).trans (Finset.subset_insert _ _)

/-- **removeAtom preserves typing iff the removed atom is unreferenced.** -/
theorem WellTyped.preserve_removeAtom {S : Spec} {I : Input}
    (hWT : WellTyped S I) (a : Atom)
    (hUnref : ∀ r ∈ S, a ∉ selectedAtoms I r) :
    WellTyped S (I.removeAtom a) := by
  intro r hr x hx
  rw [selectedAtoms_removeAtom] at hx
  show x ∈ I.atoms.erase a
  rw [Finset.mem_erase]
  refine ⟨?_, hWT r hr hx⟩
  rintro rfl; exact hUnref r hr hx

/-- **setSel₁ preserves typing iff the new selector is in scope.** Only the
    `resolve₁` slot at `sh` changes; `resolve₂` and `atoms` are untouched. -/
theorem WellTyped.preserve_setSel₁ {S : Spec} {I : Input}
    (hWT : WellTyped S I) (sh : ConstraintShape) (v : Selector₁)
    (hScope : v ⊆ I.atoms) :
    WellTyped S (I.setSel₁ sh v) := by
  intro r hr x hx
  show x ∈ I.atoms
  simp only [selectedAtoms, resolve₁_setSel₁, resolve₂_setSel₁] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hupd | hf
    · -- x ∈ Function.update I.resolve₁ sh v r.shape
      by_cases hsh : r.shape = sh
      · rw [hsh, Function.update_self] at hupd
        exact hScope hupd
      · rw [Function.update_of_ne hsh] at hupd
        exact hWT r hr (Finset.mem_union_left _ (Finset.mem_union_left _ hupd))
    · -- x ∈ (I.resolve₂ r.shape).image Prod.fst — resolve₂ unchanged
      exact hWT r hr (Finset.mem_union_left _ (Finset.mem_union_right _ hf))
  · -- x ∈ (I.resolve₂ r.shape).image Prod.snd — resolve₂ unchanged
    exact hWT r hr (Finset.mem_union_right _ hx)

/-- **setSel₂ preserves typing iff the new binary selector's atoms are in scope.** -/
theorem WellTyped.preserve_setSel₂ {S : Spec} {I : Input}
    (hWT : WellTyped S I) (sh : ConstraintShape) (v : Selector₂)
    (hScopeFst : v.image Prod.fst ⊆ I.atoms)
    (hScopeSnd : v.image Prod.snd ⊆ I.atoms) :
    WellTyped S (I.setSel₂ sh v) := by
  intro r hr x hx
  show x ∈ I.atoms
  simp only [selectedAtoms, resolve₁_setSel₂, resolve₂_setSel₂] at hx
  rcases Finset.mem_union.mp hx with hx | hsnd
  · rcases Finset.mem_union.mp hx with hr1 | hfst
    · -- x ∈ I.resolve₁ r.shape — resolve₁ unchanged
      exact hWT r hr (Finset.mem_union_left _ (Finset.mem_union_left _ hr1))
    · -- x ∈ ((Function.update _).r.shape).image Prod.fst
      by_cases hsh : r.shape = sh
      · rw [hsh, Function.update_self] at hfst
        exact hScopeFst hfst
      · rw [Function.update_of_ne hsh] at hfst
        exact hWT r hr (Finset.mem_union_left _ (Finset.mem_union_right _ hfst))
  · -- x ∈ ((Function.update _).r.shape).image Prod.snd
    by_cases hsh : r.shape = sh
    · rw [hsh, Function.update_self] at hsnd
      exact hScopeSnd hsnd
    · rw [Function.update_of_ne hsh] at hsnd
      exact hWT r hr (Finset.mem_union_right _ hsnd)

--------------------------------------------------------------------------------
-- Subject reduction (combined into a single theorem on the Step relation)
--
-- The four step kinds have different preservation conditions; this packages
-- them as a uniform statement: well-typedness is preserved by a step
-- exactly when its step-kind-specific obligations hold.
--------------------------------------------------------------------------------

/-- **Subject reduction** in inductive form: a `Step I I'` preserves typing
    when its associated obligation holds. -/
theorem WellTyped.preserve_step {S : Spec} {I I' : Input}
    (hWT : WellTyped S I) (hStep : Step I I')
    (hRem  : ∀ a, I' = I.removeAtom a → ∀ r ∈ S, a ∉ selectedAtoms I r)
    (hSel₁ : ∀ sh v, I' = I.setSel₁ sh v → v ⊆ I.atoms)
    (hSel₂ : ∀ sh v, I' = I.setSel₂ sh v →
              v.image Prod.fst ⊆ I.atoms ∧ v.image Prod.snd ⊆ I.atoms) :
    WellTyped S I' := by
  cases hStep with
  | addAtom a    => exact hWT.preserve_addAtom a
  | removeAtom a => exact hWT.preserve_removeAtom a (hRem a rfl)
  | setSel₁ sh v => exact hWT.preserve_setSel₁ sh v (hSel₁ sh v rfl)
  | setSel₂ sh v =>
    obtain ⟨hf, hs⟩ := hSel₂ sh v rfl
    exact hWT.preserve_setSel₂ sh v hf hs

--------------------------------------------------------------------------------
-- Denotational lifting (orthogonal to typing)
--------------------------------------------------------------------------------

def constraintOf (I : Input) : ConstraintShape → Constraint
| .orientation d => .orientation (I.resolve₂ (.orientation d)) d
| .align d       => .align       (I.resolve₂ (.align d))       d
| .cyclic d      => .cyclic      (I.resolve₂ (.cyclic d))      d
| .group₂ ae     => .group₂      (I.resolve₂ (.group₂ ae))     ae
| .group₁        => .group₁      (I.resolve₁ .group₁)
| .size w h      => .size  w h   (I.resolve₁ (.size w h))
| .hideatom      => .hideatom    (I.resolve₁ .hideatom)

def instantiateRule (I : Input) (r : SpecRule) : QualifiedConstraint :=
  ⟨constraintOf I r.shape, r.holds⟩

@[simp] lemma instantiateRule_def (I : Input) (sh : ConstraintShape) (h : HoldsMode) :
    instantiateRule I ⟨sh, h⟩ = ⟨constraintOf I sh, h⟩ := rfl

def Spec.atInput (S : Spec) (I : Input) : Program :=
  S.image (instantiateRule I)

theorem spec_compose_at (S₁ S₂ : Spec) (I : Input) :
    denotes ((S₁ ∪ S₂).atInput I) = denotes (S₁.atInput I) ∩ denotes (S₂.atInput I) := by
  unfold Spec.atInput
  rw [Finset.image_union]
  exact compose_eq_inter _ _

theorem spec_antimono {S₁ S₂ : Spec} (h : S₁ ⊆ S₂) (I : Input) :
    denotes (S₂.atInput I) ⊆ denotes (S₁.atInput I) :=
  antimonotonicity (Finset.image_subset_image h)

/-- Static contradiction: a spec with both `⟨sh, .always⟩` and `⟨sh, .never⟩`
    has empty denotation at every input. -/
theorem always_never_unsat_at (S : Spec) (I : Input) (sh : ConstraintShape)
    (hA : ⟨sh, .always⟩ ∈ S) (hN : ⟨sh, .never⟩ ∈ S) :
    denotes (S.atInput I) = ∅ := by
  apply always_never_unsat (S.atInput I) (constraintOf I sh)
  · exact Finset.mem_image_of_mem _ hA
  · exact Finset.mem_image_of_mem _ hN

--------------------------------------------------------------------------------
-- Future work: a richer typing rule (HIDE-GEOM)
--
-- If `⟨.hideatom, .always⟩ ∈ S`, then for every other `always`-mode geometric
-- rule `rG ∈ S`, the hidden set must be disjoint from `rG`'s selected atoms.
-- Adding this to `WellTyped` requires more nuanced preservation conditions
-- on `setSel₁`/`setSel₂` (tracking which selectors interact with `.hideatom`).
--------------------------------------------------------------------------------

/-- Sketch of the HIDE-GEOM typing rule. Not used in `WellTyped` yet. -/
def HideGeomDisj (S : Spec) (I : Input) : Prop :=
  ⟨ConstraintShape.hideatom, HoldsMode.always⟩ ∈ S →
  ∀ rG ∈ S, rG.holds = HoldsMode.always → isGeometric rG.shape = true →
  Disjoint (I.resolve₁ ConstraintShape.hideatom) (selectedAtoms I rG)

--------------------------------------------------------------------------------
-- Public API
--------------------------------------------------------------------------------

#check @WellTyped
#check @Step
#check @WellTyped.preserve_addAtom
#check @WellTyped.preserve_removeAtom
#check @WellTyped.preserve_setSel₁
#check @WellTyped.preserve_setSel₂
#check @WellTyped.preserve_step
#check @Spec.atInput
#check @spec_compose_at
#check @spec_antimono
#check @always_never_unsat_at
#check @HideGeomDisj

end Spytial
