#!/usr/bin/env bash
# Launch one agent on one issue in its own worktree, then hand in its work.
#
#   scripts/agent.sh <prover|digester|scout> <issue number|next> [options]
#
#   --cli codex|claude   which agent to run (default: codex; claude for scouts)
#   --model NAME         model to pass to the CLI
#   --dry-run            set up the worktree and print the prompt, but run nothing
#   --force              take an issue even if it is labelled `claimed`
#
# The agent edits files in the worktree and writes .agent/PR.md and/or .agent/REPORT.md. It needs
# no network and no git access: this script builds, commits, pushes, opens the pull request and
# posts the report. Relaunching on an issue whose branch already exists resumes that branch and
# shows the agent the review comments on its pull request.
set -euo pipefail

role=${1:?usage: agent.sh <prover|digester|scout> <issue|next> [--cli codex|claude] [--model M] [--dry-run] [--force]}
target=${2:?issue number or 'next'}
shift 2
cli=""; model=""; dry=0; force=0
while [ $# -gt 0 ]; do
  case $1 in
    --cli) cli=$2; shift 2 ;;
    --model) model=$2; shift 2 ;;
    --dry-run) dry=1; shift ;;
    --force) force=1; shift ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
done
case $role in
  prover) label=proof ;;
  digester) label=section ;;
  scout) label="" ;;
  *) echo "unknown role $role" >&2; exit 2 ;;
esac
[ -n "$cli" ] || { [ "$role" = scout ] && cli=claude || cli=codex; }

main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
cd "$main"

if [ "$target" = next ]; then
  [ -n "$label" ] || { echo "'next' needs a prover or digester role" >&2; exit 2; }
  target=$(gh issue list --label "$label" --state open --limit 1000 --json number,labels --jq \
    '[.[] | select([.labels[].name] | (index("claimed") or index("blocked")) | not)] | sort_by(.number) | .[0].number // empty')
  [ -n "$target" ] || { echo "no unclaimed $label issue" >&2; exit 1; }
fi
n=$target
issue=$(gh issue view "$n" --json number,title,body,labels,comments)
labels=$(jq -r '[.labels[].name] | join(" ")' <<<"$issue")
if [ "$role" != scout ] && [[ " $labels " == *" claimed "* ]] && [ $force = 0 ]; then
  echo "issue #$n is already claimed (use --force to take it anyway)" >&2; exit 1
fi

branch="$role/$n"
wt="$main/../$(basename "$main")-wt/$role-$n"
git fetch -q origin
base=origin/main; resumed=0
if git rev-parse -q --verify "origin/$branch" >/dev/null; then base="origin/$branch"; resumed=1; fi
[ -d "$wt" ] && git worktree remove --force "$wt"
git worktree add -q -B "$branch" "$wt" "$base"
mkdir -p "$wt/.lake" "$wt/.agent"
ln -sfn "$main/.lake/packages" "$wt/.lake/packages"   # share the built Mathlib

prompt="$(cat "prompts/$role.md")

---

## Your issue: #$n

$(jq -r '"**\(.title)**\n\n\(.body)\n" + ([.comments[] | "\n### Comment by \(.author.login)\n\n\(.body)\n"] | join(""))' <<<"$issue")"
if [ $resumed = 1 ]; then
  review=$(gh pr view "$branch" --json comments,reviews --jq \
    '[.reviews[].body, .comments[].body] | map(select(. != "")) | join("\n\n")' 2>/dev/null || true)
  prompt="$prompt

---

## You are resuming earlier work

This worktree already contains a previous attempt at this issue. Review comments on its pull
request:

${review:-(none)}"
fi

if [ $dry = 1 ]; then echo "worktree: $wt"; echo; echo "$prompt"; exit 0; fi

if [ "$role" != scout ] && [ $resumed = 0 ]; then
  gh issue edit "$n" --add-label claimed >/dev/null
  gh issue comment "$n" --body "Claimed by a $role agent ($cli${model:+, $model}) on branch \`$branch\`." >/dev/null
fi

echo "running $cli as $role on #$n in $wt"
cd "$wt"
set +e
case $cli in
  codex)
    args=(exec --sandbox workspace-write -C "$wt" -o "$wt/.agent/last-message.md")
    [ -n "$model" ] && args+=(-m "$model")
    [ "$role" = scout ] && args+=(-c sandbox_workspace_write.network_access=true)
    codex "${args[@]}" "$prompt" >"$wt/.agent/log.txt" 2>&1 ;;
  claude)
    args=(-p "$prompt" --permission-mode auto)
    [ -n "$model" ] && args+=(--model "$model")
    claude "${args[@]}" --allowedTools Bash Read Edit Write Grep Glob WebSearch WebFetch >"$wt/.agent/log.txt" 2>&1 ;;
  *) echo "unknown cli $cli" >&2; exit 2 ;;
esac
echo "agent exited with status $?"
set -e

# ---- hand in ----
git add -A
changed=0; git diff --cached --quiet || changed=1
[ "$role" = scout ] && changed=0
note() { gh issue comment "$n" --body "$1" >/dev/null; }

if [ $changed = 1 ]; then
  if ! { scripts/lint.sh && lake build; } >"$wt/.agent/build.txt" 2>&1; then
    note "A $role agent ($cli) stopped with changes that do not pass \`scripts/lint.sh\` and \`lake build\`. Nothing was pushed.

\`\`\`
$(tail -n 25 "$wt/.agent/build.txt")
\`\`\`"
    [ $resumed = 1 ] || gh issue edit "$n" --remove-label claimed >/dev/null
    echo "build failed; worktree kept at $wt" >&2; exit 1
  fi
  title="$role: #$n"; body=""
  if [ -s .agent/PR.md ]; then title=$(head -n 1 .agent/PR.md | sed 's/^#* *//'); body=$(tail -n +2 .agent/PR.md); fi
  [ "$role" = prover ] && link="Closes #$n" || link="Part of #$n"
  body="$body

$link

Written by a $role agent ($cli${model:+, $model}); pushed after \`lake build\` and \`scripts/lint.sh\` passed locally."
  git commit -q -m "$title" -m "$link"
  git push -q --force -u origin "$branch"
  if [ $resumed = 1 ] && gh pr view "$branch" >/dev/null 2>&1; then
    echo "updated $(gh pr view "$branch" --json url --jq .url)"
  else
    gh pr create --base main --head "$branch" --title "$title" --body "$body"
  fi
fi

if [ -s .agent/REPORT.md ]; then
  gh issue comment "$n" --body-file .agent/REPORT.md >/dev/null
  echo "posted report on #$n"
elif [ $changed = 0 ]; then
  note "A $role agent ($cli) finished without changes or a report."
fi
if [ $changed = 0 ] && [ "$role" != scout ] && [ $resumed = 0 ]; then
  gh issue edit "$n" --remove-label claimed >/dev/null
fi

cd "$main"
git worktree remove --force "$wt"
echo "done: #$n"
