#!/usr/bin/env bash
set -euo pipefail

# Run verification
./check.sh

echo ""
echo "Starting file server on port 8080..."
echo "  View Main.lean at: http://localhost:8080/Main.lean"
echo ""

cd /lean-mech
python3 -m http.server 8080 --bind 0.0.0.0
