#!/usr/bin/env bash
# Print the signature of every declaration in the library (see scripts/Signatures.lean).
#
#   scripts/signatures.sh > new.txt
#   scripts/signatures.sh --compare old.txt new.txt     # lists declarations whose statement changed
#
# The comparison ignores declarations that exist in only one file: adding a lemma or finishing
# a proof is fine, changing or removing what others build on is not. Exit status 1 if anything
# changed.
set -euo pipefail
cd "$(dirname "$0")/.."
if [ "${1:-}" = --compare ]; then
  old=${2:?old signatures}; new=${3:?new signatures}
  changed=$(awk 'NR==FNR { sig[$2]=$0; next } ($2 in sig) && sig[$2] != $0 { print $2 }' "$old" "$new")
  removed=$(awk 'NR==FNR { seen[$2]=1; next } !($2 in seen) { print $2 }' "$new" "$old")
  [ -z "$changed" ] || { echo "statement or definition changed:"; echo "$changed" | sed 's/^/  /'; }
  [ -z "$removed" ] || { echo "removed:"; echo "$removed" | sed 's/^/  /'; }
  [ -z "$changed$removed" ]
  exit
fi
lake build RiemannMasullo >/dev/null
modules=$(find RiemannMasullo -name '*.lean' | sort | sed 's#/#.#g; s#\.lean$##')
lake env lean --run scripts/Signatures.lean $modules
