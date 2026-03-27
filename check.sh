#!/usr/bin/env bash
set -euo pipefail

echo "=== Spytial Lean Mechanization Verification ==="
echo ""
echo "Step 1: Fetching Mathlib cache..."
lake exe cache get

echo ""
echo "Step 2: Building the mechanization..."
lake build

echo ""
echo "Step 3: Verification complete!"
echo "Key theorems proven:"
echo "  - refinement: Adding constraints refines denotation"
echo "  - monotonicity: Program subset relation reverses denotation inclusion"
echo "  - unsat_iff_empty: Unsatisfiability characterized by empty denotation"
echo ""
echo "To explore interactively, open Main.lean in VS Code with Lean 4 extension."
