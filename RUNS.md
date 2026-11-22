# Masullo formalization runs (ADB991)

Cloud runs prove open `proof` issues of mccorvie/riemann-masullo, one library file per run (a sweep).

## setup notes

(2026-11-22, 9335) `obtain ⟨..⟩ := lemma` on an existential inside a proof whose goal mentions the decay space E hung Lean for 20+ min in Ch04 Sec5; `have h := ...; Classical.choose h` was instant. Cold `lake build RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5` took 27 min; the full `lake build` afterwards about 30 min more. Sec1c private lemmas are reachable with `import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c`.

(2026-11-22, 8e13) A cold `lake build` of Ch07 Sec1a (all its deps, no project cache) took about 21 min; its direct importers Sec1a_Printed + Sec1b took another 5 min. Mathlib modules not in a file's import closure (e.g. `Mathlib.Topology.MetricSpace.ProperSpace.Lemmas`) can be added with a plain `import`.

(2026-11-22, db2b) `scripts/signatures.sh` starts a full `lake build RiemannMasullo` (over an hour from a cold cache here). For before/after on one file: `lake env lean --run scripts/Signatures.lean RiemannMasullo.<Mod>` > file, then `scripts/signatures.sh --compare`. Build importers of the file instead of the whole library (Ch11 Sec1a importers took ~18 min cold). elan install: `curl elan-init.sh | sh -s -- -y --default-toolchain none`, then link the release zip.

(2026-11-22) Environment v3r1t4s; the sibling RH-port runs found: 4 vCPU, 15 GB RAM, ~60 GB disk.
elan's own toolchain download fails; install Lean v4.36.0 from the GitHub release zip
(`lean-4.36.0-linux.zip`, `unzip`) and `elan toolchain link`. `zstd` is not installed.
mathlib4.lean-cache.cloud, releases.lean-lang.org and alpo.ge are on the allowlist.
GitHub GraphQL is refused from the sandbox: use `gh api` REST (search/issues needs `is:issue`).
(2026-11-22, d618) `scripts/signatures.sh` runs a full `lake build` first (~25 min on 4 cores from a
fresh cache), which outruns a 30-min background job if started with other work; run it with a 2 h
timeout, or for a one-file change compare just that module:
`lake env lean --run scripts/Signatures.lean RiemannMasullo.<Ch>.<File>` before/after, then `--compare`.
Never wrap it in `git stash ... stash pop` in one job: a killed job leaves the work in the stash.
Full `lake build` after the cache: 1431 s. Elan is at ~/.elan/bin (add to PATH).
Lean tip: if applying a lemma from another file times out at `isDefEq`/`whnf` on a hypothesis,
apply it in steps with `have` (`have h₀ := lem (F := F) B; have h₁ := h₀ hB N; obtain … := h₁`);
a one-shot application, or one inside `obtain`, unifies before instance args are synthesized.

(2026-11-22, 7c3e) elan installs fine from elan-init.sh with `--default-toolchain none`, then link the
release zip. A cold `lake build` of one Ch06 module takes about 40 min and a full `lake build` about 25 min
after that: run builds with `run_in_background` and the 2 h timeout (the default 30 min kills them). Test proofs
on a trimmed scratch copy (file header + the needed declarations; `lake lean .agent/X.lean` takes ~10 s). In
this library `obtain ⟨..⟩ :=` on an existential over ℬ-subtypes can make elaboration run away; `.elim fun .. ↦ ?_`
or an abstract private lemma avoids it.

(2026-11-22, f988) Fresh container: project oleans are NOT cached; building Ch06 deps (161 modules) took ~1.5 h on 4 cores. Background bash commands default to a 10 min limit: pass a long timeout. `lake lean` of a scratch copy with `#exit` inserted is a fast way to bisect (~15 s per run for Ch06/Sec1).
(2026-11-22, f988) Lean pitfalls around `SchwartzBruhat` (ℬ) types: `obtain ⟨A, hA⟩` on an ∃ over a linear map out of ℬ can hang forever (use `choose`); `rw` leaving a goal about ℬ values can hang (use `rewrite`/explicit Eq.trans); `have` of class instances (T2Space, PolynormableSpace) in context made `Add ℬ` synthesis time out; to use `finitePlaceSchwartz_finestTopology` pass `FinestLocallyConvex (schwartzBruhatSubmodule _)`, not `FinestLocallyConvex ℬ`, via `(congrArg (fun t ↦ @P _ t ..) h).mpr`.

## open

- RiemannMasullo/Ch09_HardySobolev/Sec3_Printed.lean: #5328 #5329 #5332; session ADB991-claude-20261122-b7e4; branch claude/sweep-ch09-sec3-printed-b7e4 (not pushed yet); PR none; last touched 2026-11-22T17:15Z

- RiemannMasullo/AppC_LCTVS/Sec3a_part2.lean: #783; session ADB991-claude-20261122-8532; branch claude/sweep-appc-sec3a-part2-8532 (not pushed yet); PR none; last touched 2026-11-22T16:39Z

- RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean: #3443; session ADB991-claude-20261122-18ea; branch claude/sweep-appd-sec1a-18ea (not pushed yet); PR none; last touched 2026-11-22T16:40Z

- RiemannMasullo/Ch10_TraceSpectral/Sec1.lean: #4871 #4872 #4873 #4876 #4877 #4879 #4880 #4881 #4883 #4884 #4885 #4887 #4889 #4890 #4891 #4892 #4893 #4894 #4895 #4896 #4897 #4898 #4900 #4901 #4902 #4903 #4904; session ADB991-claude-20261122-a7c2; branch claude/sweep-ch10-sec1-a7c2 (not pushed yet); PR none; last touched 2026-11-22T16:40Z



- RiemannMasullo/Ch04_PeriodicSchauderBases/Sec5.lean: #2654 (in PR); session ADB991-claude-20261122-9335; branch claude/sweep-ch04-sec5-9335; PR https://github.com/mccorvie/riemann-masullo/pull/5372; last touched 2026-11-22T17:02Z

## runs

- 2026-11-22 ADB991-claude-20261122-9335: Ch04_PeriodicSchauderBases/Sec5.lean, proved #2654 (modulatedPeriodization_surjective, the keystone of §4.5: cutoff route with private Bruhat-smoothness helpers: product rule, pullback along closed quotient, profiles of log|.|), PR https://github.com/mccorvie/riemann-masullo/pull/5372. Released #2667 #2688 #2691 #2693 #2694 #2696 #2708 #2711 with notes (missing: Schwartz estimates for one-sided orbit sums; topological identifications of supported stages).

- 2026-11-22 ADB991-claude-20261122-f988: Ch06_LocalGlobal/Sec1.lean. Proved #4266, #4278 (PR #5357, branch claude/sweep-ch06-sec1-f988). Released #4274 #4276 #4281 #4282 #4283 #4284 #4288 with notes; full Lean draft of the averaging/Laurent proofs in drafts/Ch06-Sec1-sweep-f988-draft.lean (elaboration problems, see setup notes).

- 2026-11-22 session ADB991-claude-20261122-7c3e: Ch06_LocalGlobal/Sec2.lean. Proved #4311 (PR #5351). Released #4306 #4308 #4316 (archimedean integrals over N∞: need decay bounds that exist only as private lemmas in Ch02 Sec2a/Sec2b and a concrete form of sNormOneIdeleTamagawaMeasure). Claim closed.

- 2026-11-22 d618: Ch02_AdelicTheta/Sec2b.lean, proved #3523 #3524 (Theorem 2.2.5.4(5)-(6), last two sorries of the file); PR #5346. No releases.

- 2026-11-22 ADB991-claude-20261122-db2b: Ch11_ShellStructure/Sec1a.lean, proved #4699 #4702 (file now sorry-free), PR https://github.com/mccorvie/riemann-masullo/pull/5234 (branch claude/sweep-ch11-sec1a-db2b). Ch06 Sec1 claim of f988 left alone (live).

- 2026-11-22 ADB991-claude-20261122-8e13: Ch07_SchauderBasesZeta/Sec1a.lean, proved #4036 (Laurent expansion of the zeta germ); released #4037 #4038 with notes (need explicit local Tate factor forms, private in Ch03 Sec3b). PR from branch claude/sweep-ch07-sec1a-8e13 https://github.com/mccorvie/riemann-masullo/pull/5313.

## for Andrea

