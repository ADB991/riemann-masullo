# RiemannMasullo

An attempt to autoformalize, in Lean 4 + Mathlib, the manuscript

> Alessandro Maria Masullo, *The Music of the Primes* (940 pp.)

The paper is in [`paper/`](paper/) (PDF plus a `pdftotext -layout` extraction for search/grep).

## Status

**On hold (20 November 2026).** The paper's main theorem, the trace formula of Theorem 12.5.1.1,
is in dispute. In the Lean Zulip thread
[Formalising Masullo's proof of GRH](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Formalising.20Masullo.27s.20proof.20of.20GRH/with/642314625)
it was reported that an LLM-assisted reading found a counterexample to it, and that correcting
one of the errors reduces the theorem to a classical formula. The details have not been posted,
and others in the thread consider a formalization premature. The draft is also incomplete:
Chapter 13, which should deduce GRH, has no statement of its main theorem.

Until people who know the area have settled this, the section issues stay open but nobody
should spend much effort on them. The infrastructure here (the Comparator setup, the issue
workflow, the agent launcher) is reusable for another target.

## Layout

The library mirrors the paper's table of contents. Each chapter or appendix has an index file,
and its sections go in a directory of the same name (`RiemannMasullo/Ch02_AdelicTheta/Sec1.lean`):

| File | Paper |
|---|---|
| `RiemannMasullo/Ch02_AdelicTheta.lean` | Ch. 2 Adelic θ-functions |
| `RiemannMasullo/Ch03_IdelicZeta.lean` | Ch. 3 Idelic Zeta Functions |
| `RiemannMasullo/Ch04_PeriodicSchauderBases.lean` | Ch. 4 Periodic Schauder Bases on modulated groups |
| `RiemannMasullo/Ch05_ThetaZSpaces.lean` | Ch. 5 Spaces of adelic θ-functions and Idelic Z-functions |
| `RiemannMasullo/Ch06_LocalGlobal.lean` | Ch. 6 Local-Global structures |
| `RiemannMasullo/Ch07_SchauderBasesZeta.lean` | Ch. 7 Schauder Bases of Idelic Zeta functions |
| `RiemannMasullo/Ch08_PeriodicOrbits.lean` | Ch. 8 Periodic Orbits and Fixed Points |
| `RiemannMasullo/Ch09_HardySobolev.lean` | Ch. 9 Hardy-Sobolev topologies |
| `RiemannMasullo/Ch10_TraceSpectral.lean` | Ch. 10 Trace formula: Spectral Side |
| `RiemannMasullo/Ch11_ShellStructure.lean` | Ch. 11 The Shell Structure |
| `RiemannMasullo/Ch12_TraceGeometric.lean` | Ch. 12 Trace formula: Geometric Side |
| `RiemannMasullo/Ch13_ZerosHecke.lean` | Ch. 13 Zeros of Hecke L-functions |
| `RiemannMasullo/Ch14_Complements.lean` | Ch. 14 Complements |
| `RiemannMasullo/AppA_AlgebraicNT.lean` | App. A Algebraic Number Theory |
| `RiemannMasullo/AppB_AnalyticNT.lean` | App. B Analytic Number Theory |
| `RiemannMasullo/AppC_LCTVS.lean` | App. C Locally convex TVS |
| `RiemannMasullo/AppD_SchwartzBruhat.lean` | App. D Schwartz-Bruhat functions |
| `RiemannMasullo/AppE_TopologicalStacks.lean` | App. E Topological stacks |

(Chapter 1 is the informal introduction and has no file.)

Third-party formalizations we build on are vendored under
[`RiemannMasullo/External/`](RiemannMasullo/External/README.md); nothing is vendored yet.

## Roadmap

On hold; see Status above. The order follows the paper's own cross-references. Two streams run in parallel and meet at the
trace formula:

| Wave | Paper | Status |
|---|---|---|
| 1 | Appendices A.1–A.3, A.5, C, D; then Chapters 2–3 (adelic θ-functions, idelic zeta functions) and, independently, Chapters 4 and 9 (periodic Schauder bases, Hardy–Sobolev spaces) | [section issues open](https://github.com/mccorvie/riemann-masullo/issues?q=is%3Aissue+is%3Aopen+label%3Asection) |
| 2 | Chapters 5–7, with Appendix B.1–B.3 and B.6 | not yet seeded |
| 3 | Chapters 10–12: the trace formula, with Appendix B.4 | not yet seeded |
| later | Chapters 8 and 14, Appendix E, A.4, B.5, B.7 | only when something needs them |

An issue labelled `blocked` is waiting for the sections it builds on. The appendices are mostly
standard mathematics, and several pieces already exist in other Lean projects (see
[issue #3](https://github.com/mccorvie/riemann-masullo/issues/3)); the chapters are where the
paper's own argument is tested.

## Contributing

Work is organized with issues and pull requests: scouts find existing Lean, digesters turn paper
sections into statements, provers close one `sorry` at a time, and an integrator reviews and
merges. The workflow and rules are in [`AGENTS.md`](AGENTS.md), the role prompts in
[`prompts/`](prompts/README.md).

## Building

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

Pinned to Lean `v4.36.0` / Mathlib `v4.36.0`.

## Comparator

The target statements are checked with [Comparator](https://github.com/leanprover/comparator)
(`lake comparator`, built into Lean from 4.35), following the setup for Alpoge's formalization at
<https://github.com/Deicyde/riemann-hypothesis>.

| File | What it is |
|---|---|
| [`Statements.lean`](Statements.lean) | definitions of the target statements; imports only Mathlib |
| [`Challenge.lean`](Challenge.lean) | the theorems, with `sorry` |
| [`Main.lean`](Main.lean) | the same theorems, to be proved from `RiemannMasullo` |
| [`comparator.json`](comparator.json) | the Comparator config |

| Theorem | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive` | RH and GRH for Dirichlet L-functions, identical to the Alpoge challenge |
| `dedekindZeta_zeros_re` | GRH for the Dedekind zeta function of every number field |
| `heckeLFunction_zeros_re` | GRH for `L(s, χ)`, every number field, every unitary Hecke character |

```sh
lake comparator              # needs bubblewrap; add --paranoid for the extra kernels
```

It currently rejects with `Illegal axiom detected: 'sorryAx'`, as it should until `Main.lean` has
no `sorry`.

The paper's own main theorem (Theorem 13.3.1.2) is a placeholder in the current draft, so the last
two statements were reconstructed from the introduction and have not been reviewed.

## License

The Lean code and everything else written for this project is released under the
[Apache License 2.0](LICENSE), the license of Mathlib. The manuscript in [`paper/`](paper/README.md)
belongs to its author and is not covered by it. Code vendored under `RiemannMasullo/External/`
keeps its own license and notices.
