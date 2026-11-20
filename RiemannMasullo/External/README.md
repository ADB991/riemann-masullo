# External

Third-party Lean developments vendored into this project. **Nothing is vendored yet**; the
directories below are reserved for the sources we expect to draw on.

| Directory | Upstream | License | Status |
|---|---|---|---|
| [`PrimeNumberTheoremAnd/`](PrimeNumberTheoremAnd/) | <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd> | Apache-2.0 | planned |
| [`TauCeti/`](TauCeti/) | <https://github.com/TauCetiProject/TauCeti> | Apache-2.0 | planned (selected modules) |
| [`Stacks/`](Stacks/) | <https://github.com/AxiomMath/Stacks> | Apache-2.0 | under consideration |

## Convention

Vendored code is copied, not added as a Lake dependency, so that each piece is pinned, auditable
and can be adapted to this project's Lean/Mathlib version. Every vendored source `X` lives in
`RiemannMasullo/External/X/` (modules `RiemannMasullo.External.X.…`) and carries:

- `README.md` — upstream URL, the exact pinned commit, authors, and which files were taken.
- `LICENSE` — the upstream license, unmodified. Check that it permits redistribution before
  vendoring; original copyright headers stay in every file.
- `MODIFICATIONS.md` — every change made to the upstream source (toolchain ports, renames,
  removed declarations), as the Apache-2.0 license requires.
- `SOURCE_MAP.json` — for each vendored file, its upstream path and sha256 at the pinned commit.

Rules:

- Take only what is needed, and keep upstream declaration names where possible.
- Vendored files must contain no `sorry` and no new axioms. Upstream `sorry`s are not vendored.
- Mathematics developed for this project goes in the chapter files, not here. If a vendored
  result needs strengthening, do it in a chapter file that imports it.
- One vendoring per pull request, with the build passing.
