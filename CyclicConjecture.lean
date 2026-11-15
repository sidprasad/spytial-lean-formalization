/-
# CyclicConjecture.lean — open proof obligation (NOT part of the default build)

This file holds the one statement in the mechanization that does not have
a complete proof: a clockwise and a counterclockwise `cyclic` constraint
on the same selector are jointly unsatisfiable.

It is kept apart from `Main.lean` so that the default build targets
(`Main`, `Counterfactuals`) contain no `sorry`. No other theorem depends
on this file. Build it explicitly with `lake build CyclicConjecture`.

The supporting lemmas (`angle_pair_not_both_eq`, `leftOf_asymm`,
`above_asymm`) are fully proven and live in `Main.lean`.
-/

import Main

namespace Spytial

/-- **Cyclic CW+CCW contradiction.** A program requiring both clockwise
    and counterclockwise cyclic layout on the same selector is unsatisfiable,
    provided the selector induces at least one maximal path of length > 2.

    **Proof sketch**: For any list L of length n ≥ 3, `allPairs_ok R L k` (CW)
    and `allPairs_ok R L.reverse k'` (CCW) impose contradictory spatial
    constraints. The pair `(0, n-1)` in L corresponds to the pair `(0, n-1)` in
    L.reverse but with atoms **swapped** (L.reverse[0] = L[n-1], L.reverse[n-1] = L[0]).
    This produces `hrel`/`vrel` constraints on the same two boxes with swapped arguments.

    The contradiction follows by case analysis on the cos/sin comparisons:
    - If CW and CCW cos comparisons go the **same way** (both < or both >):
      the swapped atom order forces `leftOf A B ∧ leftOf B A` → `leftOf_asymm`.
    - If both cos comparisons give **aligned_v**: check `vrel` (sin). If both
      sin go the same way → `above_asymm`. If both give **aligned_h**: then
      `angle_pair_not_both_eq` shows the angles can't match for n ≥ 3.
    - If cos comparisons go **opposite ways**: hrel is consistent, but then
      one must examine additional pairs (e.g., (0,1) and (1,2)) to find
      a contradictory triple. This requires a multi-pair chirality argument
      using the fact that CW and CCW assign angles in opposite circular order.

    The single-pair cases are discharged by `leftOf_asymm`, `above_asymm`,
    and `angle_pair_not_both_eq` (all proven). The multi-pair chirality
    argument is the remaining sorry. -/
theorem cyclic_cw_ccw_unsat (P : Program) (X : Selector₂)
    (hCW : ⟨.cyclic X .clockwise, .always⟩ ∈ P)
    (hCCW : ⟨.cyclic X .counterclockwise, .always⟩ ∈ P)
    (hNontriv : ∃ L ∈ maximalSimplePaths X, 2 < L.length) :
    denotes P = ∅ := by
  apply unsat_empty
  intro R hWF hSat
  obtain ⟨L, hLmem, hLlen⟩ := hNontriv
  have hCWsat := hSat ⟨.cyclic X .clockwise, .always⟩ hCW
  have hCCWsat := hSat ⟨.cyclic X .counterclockwise, .always⟩ hCCW
  simp only [modelsQC, modelsC] at hCWsat hCCWsat
  have hCW_L := hCWsat L hLmem hLlen
  have hCCW_L := hCCWsat L hLmem (by rwa [List.length_reverse])
  -- hCW_L : ∃ k, k < L.length ∧ allPairs_ok R L k
  -- hCCW_L : ∃ k, k < L.reverse.length ∧ allPairs_ok R L.reverse k
  -- Supporting lemmas proven:
  --   angle_pair_not_both_eq : distinct circle positions for n ≥ 3
  --   leftOf_asymm / above_asymm : spatial relation asymmetry
  -- Remaining: multi-pair chirality argument for opposite-direction cases
  sorry

end Spytial
