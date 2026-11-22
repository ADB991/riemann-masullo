# Masullo formalization runs (ADB991)

Cloud runs prove open `proof` issues of mccorvie/riemann-masullo, one library file per run (a sweep).

## setup notes

(2026-11-22) Environment v3r1t4s; the sibling RH-port runs found: 4 vCPU, 15 GB RAM, ~60 GB disk.
elan's own toolchain download fails; install Lean v4.36.0 from the GitHub release zip
(`lean-4.36.0-linux.zip`, `unzip`) and `elan toolchain link`. `zstd` is not installed.
mathlib4.lean-cache.cloud, releases.lean-lang.org and alpo.ge are on the allowlist.
GitHub GraphQL is refused from the sandbox: use `gh api` REST (search/issues needs `is:issue`).

## open

- RiemannMasullo/Ch06_LocalGlobal/Sec1.lean: #4266 #4274 #4276 #4278 #4281 #4282 #4283 #4284 #4288; session ADB991-claude-20261122-f988; branch claude/sweep-ch06-sec1-f988 (not pushed yet); PR none; last touched 2026-11-22T13:09Z

- RiemannMasullo/Ch11_ShellStructure/Sec1a.lean: #4699 #4702; session ADB991-claude-20261122-db2b; branch claude/sweep-ch11-sec1a-db2b (not pushed yet); PR none; last touched 2026-11-22T13:32Z

- RiemannMasullo/Ch06_LocalGlobal/Sec2.lean: #4311 #4306 #4308 #4316; session ADB991-claude-20261122-7c3e; branch claude/sweep-ch06-sec2-7c3e (not pushed yet); PR none; last touched 2026-11-22T13:50Z

## runs

## for Andrea

