#!/usr/bin/env bash
# Text check for constructs that must not appear in the library. See AGENTS.md.
set -uo pipefail
cd "$(dirname "$0")/.."
pattern='^[[:space:]]*(private |protected |noncomputable |unsafe )*(axiom|opaque)[[:space:]]|native_decide|implemented_by|@\[extern|^[[:space:]]*unsafe[[:space:]]|set_option[[:space:]]+debug\.|skipKernelTC|sorryAx'
if grep -rnE --include='*.lean' "$pattern" RiemannMasullo Main.lean; then
  echo "lint: forbidden construct found (see AGENTS.md)" >&2
  exit 1
fi
echo "lint: ok"
