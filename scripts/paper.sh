#!/usr/bin/env bash
# Read the paper. Printed page numbers equal PDF page numbers.
#   scripts/paper.sh 59 62       text of pages 59 to 62
#   scripts/paper.sh --png 63    render page 63 (or a range) to .agent/pages/ and print the paths
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
pdf="$root/paper/the-music-of-the-primes.pdf"
if [ "${1:-}" = "--png" ]; then
  first=${2:?first page}; last=${3:-$first}
  mkdir -p "$root/.agent/pages"
  pdftoppm -png -r 130 -f "$first" -l "$last" "$pdf" "$root/.agent/pages/p"
  ls "$root"/.agent/pages/p-*.png | awk -F'p-|[.]png' -v a="$first" -v b="$last" '$(NF-1)+0>=a && $(NF-1)+0<=b'
else
  first=${1:?usage: paper.sh [--png] FIRST [LAST]}; last=${2:-$first}
  pdftotext -layout -f "$first" -l "$last" "$pdf" -
fi
