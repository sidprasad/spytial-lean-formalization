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
- **Counterfactuals.lean** — diagram-element relations and maximum-cardinality counterfactuals on the branch used for the reported IIS (no `sorry`)
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
- `modelsNegC` — at the constraint level, `never` requires the positive constraint to fail on every selected pair or eligible cyclic path. For example, two visible boxes with different top edges satisfy `never` horizontal alignment. The positional translation supplies two sufficient alternatives, one box above the other in either order.
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

**Counterfactual diagrams (`Counterfactuals.lean`)**

- `translate_always_iff`, `translate_never_sound` relate diagram-element constraints to their source orientation, alignment, and cyclic rules.
- `IsCounterfactual` defines a drawing that realizes a maximum-cardinality feasible subset of the selected branch.
- `first_repair_isMaximum`, `exists_first_repair` establish optimality and existence for conflict-directed search by deletion budget.
- `retained_iff_holds` identifies the branch requirements that hold in a drawing of a maximum subset.
- `counterfactual_violates_each_iis` shows that the drawing violates at least one requirement from each IIS on its branch.
- `kept_constraint_satisfied` shows that retaining a complete alternative for each disjunction of a translated rule satisfies the source rule.
- `directlyRight_partial_keep` shows that a maximum repair can keep horizontal alignment when the order conflicts.
- `row_middle_violates_exact_group` shows why an equal-height row with a middle outsider violates exact grouping of the two endpoints.

**Open (outside the default build, in `CyclicConjecture.lean`):**
- `cyclic_cw_ccw_unsat` — CW + CCW = ∅ (sorry: geometric core)

## CI

GitHub Actions runs on every push to `main` and on PRs. It fetches the Mathlib cache, builds the project, and confirms all theorems type-check.
