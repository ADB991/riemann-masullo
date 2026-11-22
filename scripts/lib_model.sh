# Sourced by agent.sh, review.sh and sweep.sh. Decides which CLI and model an agent runs on.
#
#   resolve_model <main checkout>      reads and sets the variables `model` and `cli`
#
# 1. A local, uncommitted file <main>/.agent/model-map redirects a model that this machine no
#    longer uses, whoever asks for it. One pair per line: the name asked for, the name to run.
#        gpt-6.2-sol    claude-opus-5-5
#        gpt-6.2-astra  claude-fable-5-2
# 2. If --cli was not given, it follows from the model's name; with no model either, Claude
#    Code is used when it is installed, and Codex otherwise.
resolve_model() {
  local map="$1/.agent/model-map" to
  if [ -n "${model:-}" ] && [ -f "$map" ]; then
    to=$(awk -v m="$model" '$1 == m { print $2; exit }' "$map")
    if [ -n "$to" ]; then
      # A CLI that was chosen for the old model does not fit the new one.
      case "$model:$to" in gpt-*:claude-*|claude-*:gpt-*) cli="" ;; esac
      model=$to
    fi
  fi
  if [ -z "${cli:-}" ]; then
    case "${model:-}" in
      gpt-*) cli=codex ;;
      claude-*|opus|sonnet|haiku|fable) cli=claude ;;
      *) command -v claude >/dev/null && cli=claude || cli=codex ;;
    esac
  fi
}
