#!/bin/bash
# harbor-canary GUID {{canary}}
# Reference solution: the machine-checked derivation from the corpus
# (corpus/lean/KMiniPy/{{solution_rel}}; every theorem rests on Lean's core
# axioms plus the two documented String-hook declarations only).
set -euo pipefail
cp /solution/{{stub_file}} /app/KMiniPy/Verification/{{stub_file}}
