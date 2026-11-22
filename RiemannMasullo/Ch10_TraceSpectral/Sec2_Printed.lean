module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # §10.2 assertions that are false as printed -/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

attribute [local instance] instIdeleClassMeasurableSpaceSec1

set_option quotPrecheck false

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "order(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat
local notation "weight(" F ", " α ", " s ")" =>
  ((ideleClassTamagawaMeasure F).withDensity fun g : C𝔽(F) ↦ ENNReal.ofReal
    (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹)

/-- Paper: Theorem 10.2.1.1 and (10.2.1.6), p. 440. The printed floor cutoff
makes each selected jet belong to the negative Sobolev space on the line. -/
def Printed.spectralLineJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
    k < min (order(χ ω, shift(a, t))) (Nat.floor ((s - 1) / 2 + 1)) →
    MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s))

/-- Paper: Theorem 10.2.1.1 and (10.2.1.6), p. 440. Take the splitting
field of X³−2, the trivial character, s = 3, and a+it a nontrivial zero of the
two-dimensional Artin factor. That factor occurs squared in the Dedekind
zeta function. The cutoff includes k = 1, whose squared norm has a 1/|x|
tail in the log norm coordinate x. -/
theorem Printed.spectralLineJet_memLp_false : ¬ Printed.spectralLineJet_memLp := by sorry

/-- Paper: Proposition 10.2.1.3, p. 443. The printed annulus statement uses
all derivative orders below the full zero multiplicity. -/
def Printed.spectralLineJet_annulus : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < order(χ ω, shift(a, t)) →
      let η := spectralZeroJet (χ ω) 0 t k
      ∃ h : MemLp η 2 (weight(F, 0, s)), C⁻¹ ≤ ‖h.toLp η‖ ∧ ‖h.toLp η‖ ≤ C

/-- Paper: Proposition 10.2.1.3, p. 443. In the splitting field of X³−2
use the trivial character and a nontrivial zero of its squared two-dimensional
Artin factor. For s = 3 the printed full multiplicity includes k = 1 and the
squared norm diverges logarithmically. -/
theorem Printed.spectralLineJet_annulus_false : ¬ Printed.spectralLineJet_annulus := by sorry

/-- Paper: Proposition 10.2.1.3, p. 443. As printed, the a-line family
fails to be contained in an open ball of some positive radius. -/
def Printed.spectralLineJet_not_subset_ball : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ¬ (∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < order(χ ω, shift(a, t)) →
      ∃ h : MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s)),
        ‖h.toLp (spectralZeroJet (χ ω) 0 t k)‖ < C⁻¹)

/-- Paper: Proposition 10.2.1.3, p. 443. Take F = ℚ, a = 2 and s = 2.
All the completed Hecke L-functions are zero-free on this line by the
absolutely convergent Euler products and the nonvanishing gamma factors.
The resulting empty family is contained in every open ball. -/
theorem Printed.spectralLineJet_not_subset_ball_false :
    ¬ Printed.spectralLineJet_not_subset_ball := by sorry

/-- Paper: Terminology 10.2.1.2(2), p. 444. The printed implication says
that the functionals paired with a regular Markushevich family are bounded. -/
def Printed.spectralRegular_dual_bounded : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (x : ℕ → E) (Λ : ℕ → StrongDual ℂ E),
    IsSpectralMarkushevichBasis x Λ → IsRegularSpectralFamily x →
    ∃ C : ℝ, ∀ n, ‖Λ n‖ ≤ C

/-- Paper: Terminology 10.2.1.2(2), p. 444. In complex ℓ² take
x₂ₙ = e₂ₙ and x₂ₙ₊₁ = e₂ₙ + (n+1)⁻¹ e₂ₙ₊₁. If eⱼ* is coordinate evaluation,
the dual pair is e₂ₙ* − (n+1)e₂ₙ₊₁* and (n+1)e₂ₙ₊₁*. Both spans contain
the finite-support families, every x has norm at least one, and the dual
norms are unbounded. -/
theorem Printed.spectralRegular_dual_bounded_false :
    ¬ Printed.spectralRegular_dual_bounded := by sorry

/-- Paper: Theorem 10.2.2.1 and (10.2.2.5)–(10.2.2.6), p. 446.
The printed floor cutoff on the boundary and the full cutoff in the interior
are asserted to produce elements of the reciprocal strip space. -/
def Printed.spectralStripJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ), 0 ≤ α → 0 ≤ s → ∀ (ω : PontryaginDual C₁(F)) (b t : ℝ) (k : ℕ),
    let N := order(χ ω, shift(a + b, t))
    ((b = -α ∨ b = α) ∧ k < min N (Nat.floor ((s - 1) / 2 + 1)) ∨
      b ∈ Ioo (-α) α ∧ k < N) →
    MemLp (spectralZeroJet (χ ω) b t k) 2 (weight(F, α, s))

/-- Paper: Theorem 10.2.2.1 and (10.2.2.5), p. 446. Take F = ℚ,
the trivial character, s = 1, α = b = 0 and a+it the first nontrivial
Riemann zeta zero with positive ordinate. The printed cutoff includes k = 0.
Its squared norm has a 1/|x| tail in log coordinates. -/
theorem Printed.spectralStripJet_memLp_false : ¬ Printed.spectralStripJet_memLp := by sorry

/-- Paper: Proposition 10.2.2.2, p. 447. The asserted noncontainment in an
open ball is specialized to the allowed singleton interval, where the
repeated boundary reference and the stated ambient line norm both apply. -/
def Printed.spectralStripJet_not_subset_ball_singleton : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ¬ (∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < min (order(χ ω, shift(a, t))) (Nat.floor ((s - 1) / 2 + 1)) →
      ∃ h : MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s)),
        ‖h.toLp (spectralZeroJet (χ ω) 0 t k)‖ < C⁻¹)

/-- Paper: Proposition 10.2.2.2, p. 447. Take F = ℚ, a = 2, s = 2 and
I = {0}. On that strip every Hecke L-function is zero-free, so the empty
family is contained in every open ball. -/
theorem Printed.spectralStripJet_not_subset_ball_singleton_false :
    ¬ Printed.spectralStripJet_not_subset_ball_singleton := by sorry

end RiemannMasullo
