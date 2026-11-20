# Agent and contributor guide

This repository formalizes A. M. Masullo, *The Music of the Primes*, in Lean 4 with Mathlib. The
paper claims GRH for the Hecke L-functions of every number field. It is an unrefereed 940-page
draft that its own author calls unfinished, so part of the job is finding where it does not hold
up. A precise report that a statement in the paper is false, vague or missing is as useful as a
proof.

Work is organized with GitHub issues and pull requests. There is no blueprint.

## How work flows

1. Each paper section has a **section issue** (label `section`).
2. A **scout** comments on it with what already exists in Mathlib and other Lean projects.
3. A **digester** writes the section's definitions and statements in Lean, with `sorry` for every
   proof, and opens a pull request.
4. When that merges, the integrator runs `scripts/issues.py`, which opens one **proof issue**
   (label `proof`) per `sorry`.
5. A **prover** takes one proof issue and either proves the declaration or splits it into smaller
   `sorry`s, which become new proof issues.
6. The **integrator** reviews and merges. The project is finished when `lake comparator` accepts
   `Main.lean`.

Role instructions are in [`prompts/`](prompts/README.md).

## Layout

| Path | Contents | Who edits |
|---|---|---|
| `RiemannMasullo/<Chapter>/Sec<N>.lean` | paper section N of that chapter | digesters, provers |
| `RiemannMasullo/<Chapter>.lean` | chapter index (docstring only) | nobody |
| `RiemannMasullo/ForMathlib/` | general lemmas missing from Mathlib, at the path Mathlib would use | provers |
| `RiemannMasullo/External/` | vendored third-party Lean, see its README | integrator |
| `Statements.lean`, `Challenge.lean`, `Main.lean`, `comparator.json` | the target theorems | integrator |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.github/`, `scripts/`, `prompts/` | infrastructure | integrator |
| `paper/` | the PDF and a text extraction | nobody |

Every module under `RiemannMasullo/` is built automatically, so a new file needs no entry in an
import list. Declarations live in `namespace RiemannMasullo`.

## Rules for Lean code

These exist because many agents work in parallel and nobody rereads everything.

- **A proof pull request never changes a statement.** Other work is already building on it. If a
  statement is wrong or unprovable, say so on the issue and stop; the integrator decides.
- **`sorry` only in proofs.** A definition whose data is `sorry` makes everything downstream
  meaningless while still compiling.
- **No `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque` or `debug.*`
  options.** A finished proof must show only `propext`, `Classical.choice` and `Quot.sound` under
  `#print axioms`. `scripts/lint.sh` checks the text; CI runs it.
- **Use Mathlib's definitions where they exist.** Every new definition is something a human must
  later check by hand against the paper.
- **Every declaration taken from the paper has a docstring** starting `Paper: <item>, p. <page>.`
  (for example `Paper: Proposition 2.1.3.4, p. 63.`), followed by what the Lean says in plain
  words. Mark any difference from the paper with `Deviation:`.
- **Do not run `lake update`** or change the toolchain or dependency pins. If `lake build` starts
  compiling Mathlib itself, stop: something is wrong with the setup, not with your proof.
- Keep diffs small. Do not reformat or reorganize code you were not asked to touch.

## Reading the paper

Printed page numbers equal PDF page numbers.

```sh
scripts/paper.sh 59 62         # text of pages 59 to 62
scripts/paper.sh --png 63      # renders page 63 to .agent/pages/ and prints the path
```

The text extraction drops subscripts, hats, primes and the layout of displayed formulas. Before
you formalize a formula, look at the page image.

## Building and checking

```sh
lake build RiemannMasullo.Ch02_AdelicTheta.Sec1   # one module
lake build                                        # everything; must pass before you hand in
scripts/lint.sh
```

To check axioms, put `#print axioms RiemannMasullo.your_theorem` in a scratch file under `.agent/`
(which git ignores) and run `lake env lean .agent/Check.lean`.

## Handing in work

**If you were launched by `scripts/agent.sh`** you are in a private worktree with no network. Do
not run `git` or `gh`. Leave your changes in the working tree and write:

- `.agent/PR.md` if you changed files: the first line is the pull request title, the rest is the
  description.
- `.agent/REPORT.md` if you have something to tell the issue (a blocker, a gap in the paper,
  scouting results). It is posted as a comment.

The launcher builds, commits, pushes and opens the pull request for you.

**If you are working by hand**, branch from `main`, open a pull request against `main`, and write
`Closes #<issue>` in the description.
