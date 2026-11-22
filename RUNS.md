# Masullo formalization runs (ADB991)

Cloud runs prove open `proof` issues of mccorvie/riemann-masullo, one library file per run (a sweep).

## setup notes

(2026-11-22, 8e13) A cold `lake build` of Ch07 Sec1a (all its deps, no project cache) took about 21 min; its direct importers Sec1a_Printed + Sec1b took another 5 min. Mathlib modules not in a file's import closure (e.g. `Mathlib.Topology.MetricSpace.ProperSpace.Lemmas`) can be added with a plain `import`.

(2026-11-22, db2b) `scripts/signatures.sh` starts a full `lake build RiemannMasullo` (over an hour from a cold cache here). For before/after on one file: `lake env lean --run scripts/Signatures.lean RiemannMasullo.<Mod>` > file, then `scripts/signatures.sh --compare`. Build importers of the file instead of the whole library (Ch11 Sec1a importers took ~18 min cold). elan install: `curl elan-init.sh | sh -s -- -y --default-toolchain none`, then link the release zip.

(2026-11-22) Environment v3r1t4s; the sibling RH-port runs found: 4 vCPU, 15 GB RAM, ~60 GB disk.
elan's own toolchain download fails; install Lean v4.36.0 from the GitHub release zip
(`lean-4.36.0-linux.zip`, `unzip`) and `elan toolchain link`. `zstd` is not installed.
mathlib4.lean-cache.cloud, releases.lean-lang.org and alpo.ge are on the allowlist.
GitHub GraphQL is refused from the sandbox: use `gh api` REST (search/issues needs `is:issue`).

## open

- RiemannMasullo/Ch06_LocalGlobal/Sec1.lean: #4266 #4274 #4276 #4278 #4281 #4282 #4283 #4284 #4288; session ADB991-claude-20261122-f988; branch claude/sweep-ch06-sec1-f988 (not pushed yet); PR none; last touched 2026-11-22T13:09Z


- RiemannMasullo/Ch06_LocalGlobal/Sec2.lean: #4311 #4306 #4308 #4316; session ADB991-claude-20261122-7c3e; branch claude/sweep-ch06-sec2-7c3e (not pushed yet); PR none; last touched 2026-11-22T13:50Z

- RiemannMasullo/Ch02_AdelicTheta/Sec2b.lean: #3523 #3524; session ADB991-claude-20261122-d618; branch claude/sweep-ch02-sec2b-d618 (not pushed yet); PR none; last touched 2026-11-22T14:22Z


- RiemannMasullo/Ch04_PeriodicSchauderBases/Sec5.lean: #2654 #2667 #2688 #2691 #2693 #2694 #2696 #2708 #2711; session ADB991-claude-20261122-9335; branch claude/sweep-ch04-sec5-9335 (not pushed yet); PR none; last touched 2026-11-22T15:25Z

## runs

- 2026-11-22 ADB991-claude-20261122-db2b: Ch11_ShellStructure/Sec1a.lean, proved #4699 #4702 (file now sorry-free), PR https://github.com/mccorvie/riemann-masullo/pull/5234 (branch claude/sweep-ch11-sec1a-db2b). Ch06 Sec1 claim of f988 left alone (live).

- 2026-11-22 ADB991-claude-20261122-8e13: Ch07_SchauderBasesZeta/Sec1a.lean, proved #4036 (Laurent expansion of the zeta germ); released #4037 #4038 with notes (need explicit local Tate factor forms, private in Ch03 Sec3b). PR from branch claude/sweep-ch07-sec1a-8e13 https://github.com/mccorvie/riemann-masullo/pull/5313.

## for Andrea

