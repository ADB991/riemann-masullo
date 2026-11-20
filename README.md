# RiemannMasullo

An attempt to autoformalize, in Lean 4 + Mathlib, the manuscript

> Alessandro Maria Masullo, *The Music of the Primes* (940 pp.)

The paper is in [`paper/`](paper/) (PDF plus a `pdftotext -layout` extraction for search/grep).

## Layout

The library mirrors the paper's table of contents, one file per chapter/appendix:

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

## Building

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

Pinned to Lean `v4.36.0` / Mathlib `v4.36.0`.
