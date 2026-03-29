# Spytial Lean Mechanization

Lean 4 mechanization of the Spytial spatial constraint type system.

## Build

```sh
lake exe cache get   # fetch Mathlib oleans
lake build           # build everything
```

Or use `./check.sh` which does both.

## Structure

- **Main.lean** — single-file mechanization containing all definitions and theorems
- **lakefile.lean** — Lake build config (depends on mathlib4, batteries)
- **lean-toolchain** — pinned Lean version (v4.24.0)

## Key theorems

All proofs are kernel-checked by `lake build` (except `cyclic_cw_ccw_unsat` which has a `sorry` for the geometric core):

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
- `cyclic_cw_ccw_unsat` — CW + CCW = ∅ (sorry: geometric core)

## CI

GitHub Actions runs on every push to `main` and on PRs. It fetches the Mathlib cache, builds the project, and confirms all theorems type-check.
