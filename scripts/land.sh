#!/usr/bin/env bash
# Integrator's tool: merge the proof pull requests that need no judgment, and list the rest.
#
#   scripts/land.sh            show what would be merged and what needs review
#   scripts/land.sh --apply    merge, then update and rebuild main
#   scripts/land.sh --apply --no-pull    merge on GitHub only (for use by scripts/pool.sh)
#
# A pull request is merged without being read only if all of these hold:
#   - it comes from a `prover/<issue>` branch opened by a project member with the launcher,
#     whose hand-in recorded that no existing declaration changed ("Statement check: none of");
#   - it touches only Lean files under RiemannMasullo/ outside External/;
#   - it adds no `sorry` (so it is a finished proof, not a split).
# Lean has checked the proof and the launcher has checked that no statement moved, so there is
# nothing left for a reader to decide. Everything else is listed for review: statement pull
# requests, splits, and anything from outside the project.
set -euo pipefail
cd "$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")"
apply=0; pull=1
for arg in "$@"; do
  case $arg in --apply) apply=1 ;; --no-pull) pull=0 ;; esac   # --no-pull: merge on GitHub only
done
merged=0
while read -r pr branch assoc; do
  reason=""
  body=$(gh pr view "$pr" --json body --jq .body)
  diff=$(gh pr diff "$pr")
  files=$(gh pr view "$pr" --json files --jq '.files[].path')
  [[ "$branch" == prover/* ]] || reason="not a prover branch"
  [[ "$assoc" =~ ^(OWNER|MEMBER|COLLABORATOR)$ ]] || reason="${reason:-from outside the project}"
  grep -q "Statement check: none of" <<<"$body" || reason="${reason:-no statement check recorded}"
  if grep -qvE '^RiemannMasullo/.*\.lean$' <<<"$files" || grep -q '^RiemannMasullo/External/' <<<"$files"; then
    reason="${reason:-touches files outside the library}"
  fi
  if grep -E '^\+[^+]' <<<"$diff" | grep -qw sorry; then reason="${reason:-adds a sorry (a split)}"; fi
  title=$(gh pr view "$pr" --json title --jq .title)
  if [ -n "$reason" ]; then
    echo "review  #$pr  $branch  ($reason)  $title"
  else
    echo "merge   #$pr  $branch  $title"
    if [ $apply = 1 ]; then gh pr merge "$pr" --squash --delete-branch >/dev/null && merged=$((merged+1)); fi
  fi
done < <(gh api --paginate "repos/{owner}/{repo}/pulls?state=open&per_page=100" \
           --jq 'sort_by(.number) | .[] | "\(.number) \(.head.ref) \(.author_association)"')
if [ $apply = 1 ] && [ $pull = 1 ] && [ $merged -gt 0 ]; then
  git pull -q origin main
  lake build 2>&1 | tail -n 1
fi
