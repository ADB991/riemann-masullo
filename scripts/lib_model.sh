# Sourced by agent.sh, review.sh and sweep.sh. Decides which CLI and model an agent runs on.
#
#   resolve_model <main checkout>      reads and sets the variables `model` and `cli`
#
# 1. A local, uncommitted file <main>/.agent/model-map redirects a model that this machine has
#    stopped using by default, for command lines that do not name a CLI. One pair per line: the
#    name asked for, the name to run.
#        gpt-6.2-sol    claude-opus-5-5
#        gpt-6.2-astra  claude-fable-5-2
#    Naming the CLI (--cli codex --model gpt-6.2-astra) is a deliberate choice and is not
#    redirected.
# 2. If --cli was not given, it follows from the model's name; with no model either, Claude
#    Code is used when it is installed, and Codex otherwise.
resolve_model() {
  local map="$1/.agent/model-map" to
  if [ -z "${cli:-}" ] && [ -n "${model:-}" ] && [ -f "$map" ]; then
    to=$(awk -v m="$model" '$1 == m { print $2; exit }' "$map")
    [ -z "$to" ] || model=$to
  fi
  if [ -z "${cli:-}" ]; then
    case "${model:-}" in
      gpt-*) cli=codex ;;
      claude-*|opus|sonnet|haiku|fable) cli=claude ;;
      *) command -v claude >/dev/null && cli=claude || cli=codex ;;
    esac
  fi
}
