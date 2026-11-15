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
- **Counterfactuals.lean** — MFS / IIS and UNSAT-diagram semantics (no `sorry`)
- **DiagramMFS.lean** — the MFS at the diagram-element level, as `spytial-core` constructs it: pairwise relations are kept or dropped, so a part of one source constraint can stay (no `sorry`)
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

**Diagram-level MFS (`DiagramMFS.lean`):**
- `denotes_atomize` — ⟦atomize P⟧ = ⟦P⟧ (splitting into pairwise relations keeps the semantics)
- `diagramMFS_refines` — each constraint-level MFS is contained in a diagram-level MFS
- `greedy_isMFS` / `greedy_isDiagramMFS` — the greedy pass gives an MFS
- `uncontested_atom_kept` — a relation in no IIS is in every diagram-level MFS
- `partial_keep_witness` — a program where a part of a constraint is kept and a part is dropped

**Open (outside the default build, in `CyclicConjecture.lean`):**
- `cyclic_cw_ccw_unsat` — CW + CCW = ∅ (sorry: geometric core)

## CI

GitHub Actions runs on every push to `main` and on PRs. It fetches the Mathlib cache, builds the project, and confirms all theorems type-check.
