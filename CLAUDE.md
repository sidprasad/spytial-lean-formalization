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
- **Counterfactuals.lean** — the diagram for an UNSAT program: units, alternatives and relations for each construct, the greedy construction of `spytial-core`, and a general MFS / IIS theory (no `sorry`)
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
- `always_never_unsat` — contradictory modes → ⟦P⟧ = ∅

**Negation:**
- `pure_neg_exhaustive/exclusive` — modelsC partitions realizations

**Entailment:**
- `entails_iff_subset` — semantic entailment = denotation inclusion
- `constraint_redundant` — entailed constraints are no-ops

**Closure:**
- `denoteDiff_decompose` — ⟦P⟧ \ ⟦Q⟧ = ⋃ q ∈ Q, ⟦P ∪ {flip q}⟧

**Constraint contradictions:**
- `opposite_orientation_unsat` — left + right = ∅
- `opposite_vertical_unsat` — above + below = ∅

**UNSAT diagrams (`Counterfactuals.lean`):**
- `units_correct` — each construct holds iff all its units hold
- `greedy_feasible` — the kept relations have a realization
- `greedy_dichotomy` — each unit is kept, or all its alternatives conflict with the kept relations
- `kept_constraint_satisfied` — a constraint with all units kept is satisfied
- `greedy_must_isMFS` — with one alternative for each unit, the kept set is an MFS of the relations
- `dropped_in_some_iis`, `uncontested_kept`, `feasible_hits_every_iis` — relation between kept relations and IISes
- `partial_keep` — a part of a constraint is kept and a part is dropped
- `commit_not_maximal` — the commitment to one alternative can drop a compatible unit

**Open (outside the default build, in `CyclicConjecture.lean`):**
- `cyclic_cw_ccw_unsat` — CW + CCW = ∅ (sorry: geometric core)

## CI

GitHub Actions runs on every push to `main` and on PRs. It fetches the Mathlib cache, builds the project, and confirms all theorems type-check.
