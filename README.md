# Spytial Semantics Mechanization (Lean 4)

This artifact contains a mechanized formalization of the Spytial spatial layout semantics.

## Quick Start

**Prerequisites:**
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (tested with version 4.x)
- [elan](https://github.com/leanprover/elan) (Lean version manager, recommended)

**Installation:**
```bash
# Clone or extract the artifact
cd lean-mech

# Install dependencies (Mathlib)
lake exe cache get
lake build
```

**Verify the mechanization:**
```bash
# Check all proofs
lake build

# Interactive exploration (VS Code with Lean 4 extension recommended)
code Main.lean
```

## What's Mechanized

This Lean file (`Main.lean`) formalizes:

1. **Core definitions**:
   - Atoms, Boxes, Realizations
   - Well-formedness conditions
   - Selectors (unary and binary)

2. **Constraint semantics**:
   - Orientation constraints (8 directions)
   - Alignment constraints (horizontal/vertical)
   - Cyclic constraints (clockwise/counterclockwise on maximal paths)
   - Grouping constraints (unary `group₁`, binary `group₂`)
   - Size and hiding constraints

3. **Denotational semantics** :
   - Program composition (set union)
   - Satisfaction relation `modelsP`
   - Denotation `⟦P⟧` as the set of well-formed realizations satisfying a program

4. **Meta-theorems** :
   - **Refinement**: Adding constraints shrinks denotation (`⟦P ∪ {C}⟧ ⊆ ⟦P⟧`)
   - **Monotonicity**: Larger programs have smaller denotations (`P ⊆ Q ⟹ ⟦Q⟧ ⊆ ⟦P⟧`)
   - **Unsatisfiability**: A program is unsat iff its denotation is empty

`IsCounterfactual` defines which drawings qualify as counterfactuals. On the branch
used for the reported IIS, the drawing must realize a **maximum-cardinality feasible
subset of the diagram-element requirements**. Several subsets can tie for the maximum.
Every counterfactual drawing violates at least one requirement from every IIS on the
branch (`counterfactual_violates_each_iis`).

The counting unit is a diagram-element requirement. For example, `directlyRight`
requires both an order and horizontal alignment. If the order conflicts, a
maximum feasible subset can still retain the alignment. A selected cyclic
rotation contributes its individual pairwise relations. A group side and a
never-group inclusion witness each count once, even when they require several
relations to hold together.

`BranchFeasible` means that a single well-formed
realization satisfies every relation in the retained requirements.
`first_repair_isMaximum` proves optimality for search by increasing deletion
budget, assuming downward-closed feasibility and a valid conflict extractor.
`exists_first_repair` proves that a successful budget exists when the empty
set is feasible. [Counterfactuals.lean](Counterfactuals.lean)

In the three-box example, the rectangle must contain exactly 0 and 2. If the
counterfactual keeps the equal-height row 0, 1, 2, every rectangle containing
both endpoints also contains 1. `row_middle_violates_exact_group` proves that
this violates the source-level group requirement.

## Theorems You Can Check

Open `Main.lean` in VS Code (with Lean 4 extension) and:
- Hover over `theorem refinement` to see its type
- Click "Go to Definition" on `denotes` to inspect the denotation
- Use `#check` commands (add at end of file):
  ```lean
  #check refinement
  #check monotonicity
  #check unsat_iff_empty
  ```

## Dependencies

- **Mathlib**: for real numbers (`ℝ`), rationals (`ℚ`), finsets, basic tactics
- **Std**: for HashMap (used in cyclic path enumeration)

All dependencies are managed via `lakefile.lean` and fetched by `lake exe cache get`.

## Troubleshooting

**Build fails with "unknown package 'Mathlib'":**
```bash
lake exe cache get
lake build
```

**VS Code doesn't show Lean goals:**
- Install the official Lean 4 extension
- Ensure `elan` is in your PATH
- Restart VS Code

