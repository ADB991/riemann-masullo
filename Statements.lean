import Mathlib

/-!
# Target statements

The statements this project aims to prove, written with Mathlib definitions only.
`Challenge.lean` states them with `sorry`; `Main.lean` is where the proofs go.

The first four definitions are copied verbatim from the Comparator setup for Alpoge's
formalization (<https://github.com/Deicyde/riemann-hypothesis>, `src/Statements.lean`), so the
two projects can be judged against identical statements.

The last two are the generality claimed by Masullo: all number fields, all unitary Hecke
characters. Mathlib defines `dedekindZeta` and `HeckeCharacter.LSeries` only as Dirichlet series
(convergent for `Re s > 1`), so they are phrased for *any* meromorphic continuation `f`, and a
zero is a point where `f` has positive order. This avoids junk values at poles.
-/

open NumberField

def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- GRH for Dedekind zeta functions: every zero in the critical strip of any meromorphic
continuation of `ζ_K` lies on `Re s = 1/2`. -/
def DedekindZetaZerosOnLine : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (f : ℂ → ℂ),
    MeromorphicOn f Set.univ → (∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s) →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < meromorphicOrderAt f s → s.re = 1 / 2

/-- GRH for Hecke L-functions: for every number field `K` and every unitary Hecke character `χ`
of `K`, every zero in the critical strip of any meromorphic continuation of `L(s, χ)` lies on
`Re s = 1/2`. -/
def HeckeLZerosOnLine : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (χ : HeckeCharacter (𝓞 K) K), (∀ x, ‖χ x‖ = 1) →
    ∀ f : ℂ → ℂ, MeromorphicOn f Set.univ → (∀ s : ℂ, 1 < s.re → f s = χ.LSeries s) →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < meromorphicOrderAt f s → s.re = 1 / 2
