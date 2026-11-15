# Spytial Lean Mechanization

Lean 4 mechanization of the Spytial spatial constraint type system.

## Build

```sh
lake exe cache get   # fetch Mathlib oleans
lake build           # build everything
```

Or use `./check.sh` which does both.

## Structure

- **Main.lean** — core mechanization: definitions and theorems (no `sorry`)
- **Counterfactuals.lean** — pairwise diagram-element relations for orientation, alignment, and cyclic constraints; feasible subsets of these relations in a counterfactual diagram (no `sorry`)
- **CyclicConjecture.lean** — the one open proof (`cyclic_cw_ccw_unsat`, has a `sorry`). Not a default build target and nothing depends on it; build with `lake build CyclicConjecture`
- **lakefile.lean** — Lake build config (depends on mathlib4, batteries)
- **lean-toolchain** — pinned Lean version (v4.24.0)

## Key theorems

All proofs are kernel-checked by `lake build`. The default targets contain no `sorry`:

**Algebraic structure:**
- `antimonotonicity` — P ⊆ Q → ⟦Q⟧ ⊆ ⟦P⟧ (contravariant denotation)
- `compose_eq_inter` — ⟦P ∪ Q⟧ = ⟦P⟧ ∩ ⟦Q⟧
- `denotes_empty` — ⟦∅⟧ = WF
- `compose_comm/assoc/idem` — (Program/≡, compose) is a commutative idempotent monoid
- `full_abstraction` — observational ≡ denotational equivalence (fully abstract)

**Unsatisfiability:**
- `unsat_iff_empty` — unsatisfiability iff empty denotation
- `always_never_unsat` — `always` and `never` for one constraint → ⟦P⟧ = ∅, if the two modes exclude each other (true for a non-empty selector: `orientation_exclusive`, `align_exclusive`)

**Negation:**
- `modelsNegC` — at the constraint level, `never` requires the positive constraint to fail on every selected pair or eligible cyclic path. For example, two visible boxes with different top edges satisfy `never` horizontal alignment. At the diagram element level, `spytial-core` requires one box to be above the other.
- `PureNeg c` — `never` is the logical negation for `c` (true for a one-pair selector, `size`, `hideatom`, groups)
- `pure_neg_exhaustive/exclusive` — for `PureNeg c`, the two modes partition the realizations

**Entailment:**
- `entails_iff_subset` — semantic entailment = denotation inclusion
- `constraint_redundant` — entailed constraints are no-ops

**Closure:**
- `denoteDiff_decompose` — ⟦P⟧ \ ⟦Q⟧ = ⋃ q ∈ Q, ⟦P ∪ {flip q}⟧, for `Q` with `PureNeg` constraints

**Constraint contradictions:**
- `opposite_orientation_unsat` — left + right = ∅
- `opposite_vertical_unsat` — above + below = ∅

**Counterfactual diagrams (`Counterfactuals.lean`):**
- `translate_always_iff`, `translate_never_sound` — for orientation, alignment, and cyclic constraints, the diagram-element relations imply the source constraint. For `always`, the converse also holds.
- `greedy_feasible` — the kept relations have a well-formed realization
- `greedy_dichotomy` — each disjunction has a kept branch, or every branch conflicts with the kept relations. The statement applies to the order supplied; it does not specify the solver's choice of order.
- `kept_constraint_satisfied` — if all disjunctions of a source constraint have a kept branch, the constraint holds
- `greedy_conjuncts_isMFS` — for a conjunction of individual relations, the kept set is a maximal feasible subset
- `dropped_in_some_iis`, `uncontested_kept`, `feasible_hits_every_iis` — relation between kept relations and IISes
- `directlyRight_partial_keep` — when the order conflicts, a counterfactual diagram can still satisfy the horizontal alignment required by `directlyRight`
- `commit_not_maximal` — two disjunctions can be jointly feasible even if choosing the first branch of one rules out the other

**Open (outside the default build, in `CyclicConjecture.lean`):**
- `cyclic_cw_ccw_unsat` — CW + CCW = ∅ (sorry: geometric core)

## CI

GitHub Actions runs on every push to `main` and on PRs. It fetches the Mathlib cache, builds the project, and confirms all theorems type-check.
