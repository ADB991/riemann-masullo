# Masullo formalization runs (ADB991)

Cloud runs prove open `proof` issues of mccorvie/riemann-masullo, one library file per run (a sweep).

## setup notes

(2026-11-23, 76e0) Fresh container: `lake exe cache get` brought project oleans; first `lake build` of AppC Sec5a_Printed 4 min, full `lake build` 27 min. Don't add `.{u}` to a statement to fix universes (changes the hash): let unification pick the level (e.g. `ULift ℂ`). `ContDiff.pow` needs `import Mathlib.Analysis.Calculus.ContDiff.Operations` in low AppC files; `EuclideanSpace.single_*` lemmas are gone, use `WithLp.toLp 2 (fun _ ↦ t)` and `EuclideanSpace.norm_eq`.

(2026-11-22, b7e4) Cold build of a _Printed leaf that imports Ch12 Sec1a (171 modules) took 37 min after `lake exe cache get`; full `lake build` afterwards 31 min. Once deps are built, `lake build` of the leaf file is ~10 s, so iterate there. On ℝ≥0ˣ: `positiveRealHaar` (= map exp volume) gives `{t | log t ∈ K}` measure `volume K` by `Measure.map_apply`; `borelSpace_units_of_continuousInv₀` lives in `RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic` (add the import); `Measure.map_dirac'` (with measurability) not `map_dirac`. Inside a theorem, `rcases h with rfl` on `c = Λ` can eliminate the outer variable Λ: use `rw`.

(2026-11-22, 18ea) This container: `lake exe cache get` also brought project oleans; building AppD Sec1a took 2.5 min, full `lake build` 70 min. Single-module signature compare: write `origin/main` version of the file, rebuild module, run Signatures.lean, `git checkout` the file back (work committed first).

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

(2026-11-22, 8532) Fresh container: `lake exe cache get` also brought the project's AppC oleans, so `lake build` of AppC Sec3a_part2 took 3 min. A full `lake build` afterwards took 44 min (Ch05/Ch06/Ch07 modules are slow). Iterating directly on the module with `lake build <module>` took about 30 s per round. `xxd` is missing (use `od`). Before/after signatures: commit, `git checkout origin/main -- <file>`, build, run Signatures.lean, then `git checkout HEAD -- <file>`.

(2026-11-22, ffe6) Fresh container: `lake exe cache get` (1 min) did not bring Ch04 oleans; cold `lake build` of Ch04 Sec2 took ~19 min total. Background Bash jobs are killed at 10 min unless `timeout` is passed explicitly. `lake env lean --run scripts/Signatures.lean <Mod>` takes 15 s once the module is built.

(2026-11-22, a7c2) Cold `lake build` of Ch10 Sec1 (all deps) took 31 min; the module itself ~75 s; full `lake build` after that 16 min. Scratch files that copy a module's `local instance`s collide with the instance names exported by the imported module: rename them. In Ch10 Sec1, unification through ℬ-subtypes / weighted-Lp subspaces is very slow (`obtain` on `mem_adelePolarSubspace`, `rw [map_smul]` on a LinearIsometryEquiv of Lp subspaces): abstract private lemmas over generic groups/spaces fix it. Test those on a tiny scratch that imports only the lower module (e.g. Ch02 Sec2b), ~8 s.

(2026-11-22, 0825) `maxHeartbeats` (200000) is per declaration, not per tactic: a long proof made of individually cheap steps fails with `(deterministic) timeout at whnf` reported at the `by` or the declaration start. Split into several private lemmas, each its own budget. Also: `set` and `obtain ⟨..⟩ :=` under a goal mentioning linear maps out of `SchwartzBruhat` hang; use `.choose`/`.choose_spec` and state helper facts for a generic `h : SchwartzBruhat G`. A scratch `.agent/X.lean` with `import all RiemannMasullo.<Mod>` plus the file's notations (rename copied `local instance`s, they clash by name) checks in ~10 s, but only while the imported module itself is unmodified and built: `lake lean` rebuilds a modified import first. Cold deps of AppB Sec4b (cache had Mathlib only): ~50 min.

(2026-11-23, e67a) Fresh container: `lake exe cache get` (1 min) brought the project oleans too; `lake build` of the AppC Sec2a_part2 _Printed leaf took 74 s, then ~10 s per round. In a `module` file, `lp` needs an explicit `import Mathlib.Analysis.Normed.Lp.lpSpace`. Passing an explicit non-instance topology (e.g. `completionCompactDualTopology E`) through `Continuous.comp`/`@Continuous` fails with "synthesized instance not defeq"; use `let : TopologicalSpace T := ...` first, as the library does. `IsEmbedding.injective` on a type whose topology is only a `letI` fails to synthesize: use `obtain ⟨-, hinj⟩ := hemb`. A long proof hit maxHeartbeats at the declaration: moving generic steps (DirectedSystem of completed stages, completion functoriality) into private lemmas over abstract spaces fixed it. `DirectedSystem.map_self` has no `h` argument and `map_map ⦃k j i⦄` takes `hij hjk` in that order.

(2026-11-23, 2e73) Fresh container: cold `lake build` of Ch09 Sec2_Printed (9007 jobs, cache had Mathlib only) took 18.6 min; full `lake build` afterwards 14.6 min. `SchwartzBergman I` is a `def` synonym (WithGeneratingSeminorms) of a submodule subtype: build elements as `(⟨f, hf⟩ : SchwartzBergman I)` (works) but a `fun m ↦ (⟨..⟩ : AS)` still gets the subtype as codomain, so state such lemmas as `Tendsto (β := AS) ...` and use `refine ….mpr` instead of `rw` (rw/simp fail with "not type-correct under implicit transparency" on terms containing `↑v`, v : AS); close such steps with term proofs (`congrArg`, `.trans`). A `Tendsto f l (𝓝 x)` applied to a set gives membership in `map f l`: use `Filter.mem_map.mp` before `nonempty_of_mem`. With a non-instance topology, call `@Continuous.tendsto X Y topX _ _ hcont x`.

(2026-11-23, c34d) Fresh container: `lake exe cache get` (1 min) brought project oleans; building the AppA Sec3 leaf took 4.6 min and a full `lake build` 24 min. In a `_Printed` file whose local `MeasurableSpace ℚ_[p] := borel _` has no BorelSpace, add `have : BorelSpace ℚ_[3] := ⟨rfl⟩` inside the proof for `measurableSet_closedBall`/`measure_preimage_add`. Instantiating a printed ∀ yields casts `((3:ℕ):ℚ_[3])`: state intermediate `have`s with that exact cast so `rw` matches.

## open

- RiemannMasullo/AppD_SchwartzBruhat/Sec1c_Printed.lean: #5756 (claimed); session ADB991-claude-20261123-f923; branch claude/sweep-appd-sec1c-printed-f923; PR none yet; last touched 2026-11-23T02:20Z
- RiemannMasullo/Ch04_PeriodicSchauderBases/Sec5_Printed.lean: #5335 (claimed); session ADB991-claude-20261123-5e1d; branch claude/sweep-ch04-sec5-printed-5e1d; PR none yet; last touched 2026-11-23T01:59Z
- RiemannMasullo/AppC_LCTVS/Sec5a_Printed.lean: #5749 (proved, in PR); session ADB991-claude-20261123-76e0; branch claude/sweep-appc-sec5a-printed-76e0; PR https://github.com/mccorvie/riemann-masullo/pull/5908; last touched 2026-11-23T01:50Z

## runs

- 2026-11-23 ADB991-claude-20261123-e67a: AppC_LCTVS/Sec2a_part2_F225_F227_Printed.lean, proved refutations #5745 (Remark C.2.3.2: non-complete span of ℓ² basis) and #5746 (Prop. C.2.3.13(2): tail projections on finitely supported ℓ², limit zero but completed-stage limit nonzero). PR https://github.com/mccorvie/riemann-masullo/pull/5926 (branch claude/sweep-appc-sec2a-part2-printed-e67a). #5748 (bornological, stationary sets in ω₁) not claimed. Full lake build 26 min; lint ok; signatures unchanged. Claim closed.

- 2026-11-23 ADB991-claude-20261123-c34d: AppA_AlgebraicNT/Sec3_TranslatedFourier_Printed.lean, proved refutation #5770 (p=3, n=0, a=1/3, x=0: mass of translated ball 1 vs conjugate of padicTamagawaFourier_scaledIntegers at -1/3 = 0; file now sorry-free). PR https://github.com/mccorvie/riemann-masullo/pull/5914 (branch claude/sweep-appa-sec3-translatedfourier-printed-c34d). Full lake build 24 min; lint ok; signatures unchanged. No releases. Claim closed.
- 2026-11-23 ADB991-claude-20261123-2e73: Ch09_HardySobolev/Sec2_Printed.lean, proved refutations #5815 #5816 (tilted Gaussians exp(m(z−1)+z²): line norms exp(m(σ−1))·const, value at 1 constant). PR https://github.com/mccorvie/riemann-masullo/pull/5913 (branch claude/sweep-ch09-sec2-printed-2e73). File now sorry-free. No releases. Full lake build 14.6 min; lint ok; signatures unchanged.

- 2026-11-23 ADB991-claude-20261123-76e0: AppC_LCTVS/Sec5a_Printed.lean, proved refutation #5749 (Printed.weaklyContDiffOn_lipschitz_false: f(x)=x², increments 2t+1 unbounded; uses ULift ℂ since E has a free universe). PR https://github.com/mccorvie/riemann-masullo/pull/5908. Full lake build 27 min; lint ok; signatures unchanged. No releases. Also cleared the finished 2026-11-22 claims (all PRs merged).

- 2026-11-22 ADB991-claude-20261122-0825: AppB_AnalyticNT/Sec4b.lean, proved #3895 (exists_finiteConnesPrincipalValue) and #3892 (finiteLogFourier_unique, uses #3891 by name). PR https://github.com/mccorvie/riemann-masullo/pull/5581 (branch claude/sweep-appb-sec4b-0825). Released #3891 with a note (needs explicit p-adic Gauss-sum computation). Full lake build 1711 s; lint ok; signatures unchanged.

- 2026-11-22 ADB991-claude-20261122-ffe6: Ch04_PeriodicSchauderBases/Sec2.lean, proved #1948 (cyclicPeriodizationCLM_apply, one line from cyclicPeriodization_hasSum; file now sorry-free). PR https://github.com/mccorvie/riemann-masullo/pull/5485 (branch claude/sweep-ch04-sec2-ffe6). Full lake build 35 min. No releases. Claim closed.

- 2026-11-22 ADB991-claude-20261122-a7c2: Ch10_TraceSpectral/Sec1.lean, proved #4877 #4879 #4883 #4884 #4885 #4897 #4898 #4902 (PR #5451, branch claude/sweep-ch10-sec1-a7c2). Released the other 19 with notes (#4880 needs an S-local analogue of ideleClassTamagawaMeasure_eq_smul_canonical; #4900 sketched).

- 2026-11-22 ADB991-claude-20261122-b7e4: Ch09_HardySobolev/Sec3_Printed.lean, proved refutations #5328 #5329 #5332 (concrete counterexamples on ℝ>0 with dt/t), PR https://github.com/mccorvie/riemann-masullo/pull/5438. #5330 #5331 not claimed (heavier: isotype bands, Mellin jets of Gaussians). No releases.

- 2026-11-22 ADB991-claude-20261122-18ea: AppD_SchwartzBruhat/Sec1a.lean, proved #3443 (elementarySchwartz_barrelled, one line from the private elementarySchwartz_frechet_montel); PR https://github.com/mccorvie/riemann-masullo/pull/5425 (branch claude/sweep-appd-sec1a-18ea). #3436 (tensor embedding, needs nuclearity/π=ε) not taken. Claim closed.

- 2026-11-22 ADB991-claude-20261122-8532: AppC_LCTVS/Sec3a_part2.lean, proved #783 (Proposition C.3.6.4(3): the injective completion of E'⊗F is isometric to the compact operators on Hilbert spaces; the file is now sorry-free). PR https://github.com/mccorvie/riemann-masullo/pull/5391 (branch claude/sweep-appc-sec3a-part2-8532). No releases. Also dropped the finished d618 claim (PR #5346 merged).

- 2026-11-22 ADB991-claude-20261122-9335: Ch04_PeriodicSchauderBases/Sec5.lean, proved #2654 (modulatedPeriodization_surjective, the keystone of §4.5: cutoff route with private Bruhat-smoothness helpers: product rule, pullback along closed quotient, profiles of log|.|), PR https://github.com/mccorvie/riemann-masullo/pull/5372. Released #2667 #2688 #2691 #2693 #2694 #2696 #2708 #2711 with notes (missing: Schwartz estimates for one-sided orbit sums; topological identifications of supported stages).

- 2026-11-22 ADB991-claude-20261122-f988: Ch06_LocalGlobal/Sec1.lean. Proved #4266, #4278 (PR #5357, branch claude/sweep-ch06-sec1-f988). Released #4274 #4276 #4281 #4282 #4283 #4284 #4288 with notes; full Lean draft of the averaging/Laurent proofs in drafts/Ch06-Sec1-sweep-f988-draft.lean (elaboration problems, see setup notes).

- 2026-11-22 session ADB991-claude-20261122-7c3e: Ch06_LocalGlobal/Sec2.lean. Proved #4311 (PR #5351). Released #4306 #4308 #4316 (archimedean integrals over N∞: need decay bounds that exist only as private lemmas in Ch02 Sec2a/Sec2b and a concrete form of sNormOneIdeleTamagawaMeasure). Claim closed.

- 2026-11-22 d618: Ch02_AdelicTheta/Sec2b.lean, proved #3523 #3524 (Theorem 2.2.5.4(5)-(6), last two sorries of the file); PR #5346. No releases.

- 2026-11-22 ADB991-claude-20261122-db2b: Ch11_ShellStructure/Sec1a.lean, proved #4699 #4702 (file now sorry-free), PR https://github.com/mccorvie/riemann-masullo/pull/5234 (branch claude/sweep-ch11-sec1a-db2b). Ch06 Sec1 claim of f988 left alone (live).

- 2026-11-22 ADB991-claude-20261122-8e13: Ch07_SchauderBasesZeta/Sec1a.lean, proved #4036 (Laurent expansion of the zeta germ); released #4037 #4038 with notes (need explicit local Tate factor forms, private in Ch03 Sec3b). PR from branch claude/sweep-ch07-sec1a-8e13 https://github.com/mccorvie/riemann-masullo/pull/5313.

## for Andrea

