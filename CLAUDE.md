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

All proofs are kernel-checked by `lake build`:
- `refinement` — adding a constraint refines the denotation
- `monotonicity` — program subset reverses denotation inclusion
- `unsat_iff_empty` — unsatisfiability iff empty denotation

## CI

GitHub Actions runs on every push to `main` and on PRs. It fetches the Mathlib cache, builds the project, and confirms all theorems type-check.
