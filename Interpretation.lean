/-
# Interpretation.lean — Gated denotational interpretation of typed inputs

This module connects the type system in `Input.lean` to the denotational
semantics in `Main.lean`.  The single point of contact is `TypedInput.atInput`:
it converts a `TypedInput S` (an input with a `WellTyped` proof) into a
concrete `Program`, and from there into a denotation `⟦…⟧ ⊆ WF`.

Crucially, there is no `Spec.atInput` on bare `Input` — interpretation is
gated by the typing judgment.  Ill-typed inputs are *not constructible*
as `TypedInput`, so they cannot be interpreted at all.
-/

import Main
import Input

namespace Spytial

--------------------------------------------------------------------------------
-- Instantiation: shape + input → concrete `Constraint`
--------------------------------------------------------------------------------

/-- Concrete constraint produced by a shape under a given input's resolvers. -/
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

--------------------------------------------------------------------------------
-- The gated interpretation.
--
-- Note: there is *no* `Spec.atInput : Spec → Input → Program`. The only
-- entry point is `TypedInput.atInput`. To interpret, a caller must supply
-- a `TypedInput`, which carries a `WellTyped` proof.
--------------------------------------------------------------------------------

/-- The program produced by interpreting a typed input. -/
def TypedInput.atInput {S : Spec} (TI : TypedInput S) : Program :=
  S.image (instantiateRule TI.input)

/-- Convenience: the denotation of a typed input. -/
def TypedInput.denote {S : Spec} (TI : TypedInput S) : Set Realization :=
  denotes TI.atInput

--------------------------------------------------------------------------------
-- Lifting: composition over the gated interpretation
--------------------------------------------------------------------------------

/-- **Composition.** Given a `TypedInput (S₁ ∪ S₂)`, the denotation of the
    combined interpretation equals the intersection of the projections'
    denotations.  All three `TypedInput`s share the same underlying `Input`
    (via `restrictLeft/restrictRight`). -/
theorem typed_compose_at {S₁ S₂ : Spec} (TI : TypedInput (S₁ ∪ S₂)) :
    denotes TI.atInput
      = denotes (TI.restrictLeft : TypedInput S₁).atInput
      ∩ denotes (TI.restrictRight : TypedInput S₂).atInput := by
  unfold TypedInput.atInput TypedInput.restrictLeft TypedInput.restrictRight
  show denotes ((S₁ ∪ S₂).image (instantiateRule TI.input))
       = denotes (S₁.image (instantiateRule TI.input))
       ∩ denotes (S₂.image (instantiateRule TI.input))
  rw [Finset.image_union]
  exact compose_eq_inter _ _

/-- **Antimonotonicity** of the gated interpretation.  Lifting through the
    `restrictLeft` projection yields the corresponding subset relation. -/
theorem typed_antimono_left {S₁ S₂ : Spec} (TI : TypedInput (S₁ ∪ S₂)) :
    denotes TI.atInput ⊆ denotes (TI.restrictLeft : TypedInput S₁).atInput := by
  rw [typed_compose_at]
  exact Set.inter_subset_left

theorem typed_antimono_right {S₁ S₂ : Spec} (TI : TypedInput (S₁ ∪ S₂)) :
    denotes TI.atInput ⊆ denotes (TI.restrictRight : TypedInput S₂).atInput := by
  rw [typed_compose_at]
  exact Set.inter_subset_right

--------------------------------------------------------------------------------
-- Static contradiction (independent of typing): a spec containing both
-- ⟨sh, .always⟩ and ⟨sh, .never⟩ has empty denotation at *every* typed input.
-- This is the typed companion to `always_never_unsat` from `Main.lean`.
--------------------------------------------------------------------------------

theorem typed_always_never_unsat {S : Spec} (TI : TypedInput S) (sh : ConstraintShape)
    (hA : ⟨sh, .always⟩ ∈ S) (hN : ⟨sh, .never⟩ ∈ S) :
    denotes TI.atInput = ∅ := by
  apply always_never_unsat TI.atInput (constraintOf TI.input sh)
  · exact Finset.mem_image_of_mem _ hA
  · exact Finset.mem_image_of_mem _ hN

--------------------------------------------------------------------------------
-- Public API
--------------------------------------------------------------------------------

#check @TypedInput.atInput
#check @TypedInput.denote
#check @typed_compose_at
#check @typed_antimono_left
#check @typed_antimono_right
#check @typed_always_never_unsat

end Spytial
