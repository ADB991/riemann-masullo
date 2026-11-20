#!/usr/bin/env bash
# Keep a fixed number of provers working, and merge their finished proofs.
#
#   scripts/pool.sh <count> [options passed to agent.sh, e.g. --model M --effort high]
#
# Until the file .agent/pool.stop exists, it starts `scripts/agent.sh prover next` whenever fewer
# than <count> prover launchers are running, and every couple of minutes merges the proof pull
# requests that `scripts/land.sh` accepts. It never touches the main checkout's working tree:
# the integrator pulls, rebuilds and syncs issues. An issue an agent could not finish is labelled
# `stuck` by the launcher and is not tried again until that label is removed.
#
# Stop it with: touch .agent/pool.stop   (running agents finish and hand in on their own)
set -uo pipefail
count=${1:?usage: pool.sh <count> [agent.sh options]}; shift
cd "$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")"
mkdir -p .agent/logs; rm -f .agent/pool.stop
tick=0
while [ ! -e .agent/pool.stop ]; do
  running=$(pgrep -fc "scripts/agent.sh prover" || true)
  if [ "$running" -lt "$count" ]; then
    (scripts/agent.sh prover next "$@" >>.agent/logs/pool-agents.out 2>&1 &)
    sleep 25      # let the new launcher claim its issue before the next one chooses
  else
    sleep 30
  fi
  tick=$((tick+1))
  if [ $((tick % 5)) = 0 ]; then
    scripts/land.sh --apply --no-pull 2>/dev/null | grep -E "^(merge|review)" >>.agent/logs/pool-land.out || true
  fi
done
echo "pool stopped; $(pgrep -fc 'scripts/agent.sh prover' || true) launchers still finishing"
