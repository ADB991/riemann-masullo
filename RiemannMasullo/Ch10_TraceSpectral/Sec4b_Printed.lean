module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # False assertions in §10.4.3 -/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 900000

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "μ(" F ")" => ideleClassTamagawaMeasure F
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "logNorm(" F ")" => (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "h₀" => le_refl (0 : ℝ)
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs))
local notation "w(" F ", " α ", " s ")" => (fun g : C𝔽(F) ↦
  intervalSobolevDensity (-α) α s (logNorm(F) g))
local notation "W(" F ", " α ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) (-α) α s
local notation "W'(" F ", " α ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) (-α) α s true
local notation "A(" F ", " hα ", " hs ", " φ ")" =>
  hardySobolevTestAction (μ(F)) m𝔽(F) _ _ _ (hStrip(hα)) hs φ
local notation "mixed(" F ", " α ", " s ")" => Lp ℂ 2
  (((μ(F)).withDensity fun g ↦ ENNReal.ofReal (w(F, α, s) g)).prod
    ((μ(F)).withDensity fun g ↦ ENNReal.ofReal (w(F, α, s) g)⁻¹))

/-- Paper: (10.4.3.1), p. 465. The displayed polynomial is claimed to
regularize the completed Hecke L-function for every unitary character. -/
def Printed.unshiftedHeckeRegularization_entire : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)),
    Differentiable ℂ fun z : ℂ ↦
      (z * (z - 1) / 2) ^ (if ∀ g : C₁(F), χ g.val = 1 then (1 : ℕ) else 0) *
        continuedCompletedHeckeL χ z

/-- Paper: (10.4.3.1), p. 465. For F = ℚ and χ = |·|^i the completed
L-function is completed zeta at z + i. Its pole at 1 − i survives
multiplication by z(z − 1)/2, which is nonzero there. -/
theorem Printed.unshiftedHeckeRegularization_entire_false :
    ¬ Printed.unshiftedHeckeRegularization_entire := by sorry

/-- Paper: (10.4.3.5), p. 466. For a fixed character and shift, a unique
family of isotypic exponential-decay tests is biorthogonal to the zero jets.
The functional label uses the unshifted zero, as in the displayed formula. -/
def Printed.spectralSchwartzBiorthogonal_unique : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (a : ℝ),
    let E := {v : ModulatedExponentialDecay m𝔽(F) univ //
      ∀ (k : C₁(F)) (g : C𝔽(F)), v.val (k.val⁻¹ * g) = (χ k.val : ℂ) * v.val g}
    let J := {j : ℂ × ℕ // j.2 <
      (meromorphicOrderAt (continuedCompletedHeckeL χ) ((a : ℂ) + j.1)).untop₀.toNat}
    ∃! ψ : J → E, ∀ j j' : J,
      (∫ g, (ψ j').val.val g * ideleClassNormTwist χ ((a : ℂ) + j.val.1) g *
        (logNorm(F) g : ℂ) ^ j.val.2 ∂(μ(F))) = if j = j' then 1 else 0

/-- Paper: (10.4.3.5), p. 466. For F = ℚ, χ = 1 and a = 0, add the
theta function of the rational test with finite factor 1_{ℤ̂} and archimedean
factor exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²) to any claimed biorthogonal
vector. This nonzero test has zero values under every zeta jet by divisibility
of its Mellin transform. Its theta function is nonzero at large norm. -/
theorem Printed.spectralSchwartzBiorthogonal_unique_false :
    ¬ Printed.spectralSchwartzBiorthogonal_unique := by sorry

local notation "represents(" F ", " α ", " s ", " B ", " k ")" =>
  (∀ u : W(F, α, s), ∀ᵐ x ∂(μ(F)),
    Integrable (fun y ↦ k (x, y) * u y) (μ(F)) ∧
      B u x = ∫ y, k (x, y) * u y ∂(μ(F)))
local notation "printedWeight(" F ", " α ", " s ", " ρ ", " k ")" =>
  (fun p : C𝔽(F) × C𝔽(F) ↦ (ρ p.1 * (w(F, α, s) p.2)⁻¹ ^ 2 : ℝ) • k p)

/-- Paper: (10.4.3.25), p. 470. The tensor representative is integrated
against Haar measure with an additional reciprocal input weight. The
mixed-weight tensor kernel is written in output-first coordinates. -/
def Printed.spectralLineKernel_extraWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → ∀ hs : 1 < s,
    ∀ (φ : BruhatCompactSupport C𝔽(F)) (k : mixed(F, 0, s)),
      let B := (spectralProjection (F := F) a h₀ hs₀(hs)).comp (A(F, h₀, hs₀(hs), φ))
      represents(F, 0, s, B, k) →
      represents(F, 0, s, B, (fun p ↦ ((w(F, 0, s) p.2)⁻¹ : ℝ) • k p))

/-- Paper: (10.4.3.25), p. 470. Take F = ℚ, s = 4 and a equal to the
abscissa of the first positive-ordinate nontrivial zeta zero. A nonnegative
smooth test supported in a sufficiently small log-norm band about zero has
nonzero Mellin value there after shifting by a. The order-zero jet shows
spectral projection after convolution is nonzero. If k and k/w(y) both
represented it, uniqueness would force k to be supported on log |y| = 0,
which is Haar null. -/
theorem Printed.spectralLineKernel_extraWeight_false :
    ¬ Printed.spectralLineKernel_extraWeight := by sorry

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471, second formula. The cutoff
spectral function is claimed to represent the geometric truncation.
The two reciprocal weights account for (10.4.3.26) and (10.4.3.30). -/
def Printed.spectralLineTruncatedKernel_geometric : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → ∀ hs : 1 < s,
    ∀ (Λ ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff m𝔽(F) Λ ε ρ),
      0 < Λ⁻¹ + ε → Λ⁻¹ + ε < Λ - ε →
      ∀ (φ : BruhatCompactSupport C𝔽(F)) (k : mixed(F, 0, s)),
        represents(F, 0, s, (spectralProjection (F := F) a h₀ hs₀(hs)).comp
          (A(F, h₀, hs₀(hs), φ)), k) →
        IsSobolevHilbertSchmidtKernel (geometricTruncatedConvolution a h₀ hs₀(hs) hρ φ)
          (printedWeight(F, 0, s, ρ, k))

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471. For F = ℚ, a = 2 and s = 4
there are no line zeros, so the spectral projector and its kernel vanish.
Use Λ = 2, ε = 1/8 and the indicator of the outer norm band as cutoff.
An even nonnegative bump in the log-norm band (−1/8, 1/8) convolved with
itself is positive near the identity, where the cutoff equals one. -/
theorem Printed.spectralLineTruncatedKernel_geometric_false :
    ¬ Printed.spectralLineTruncatedKernel_geometric := by sorry

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "Z(" F ", " a ", " α ", " χ ")" => {z : PontryaginDual C₁(F) × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" a ", " α ", " s ", " χ ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

/-- Paper: Theorem 10.4.3.5(2)–(3), pp. 472–473. The ambient tensors with
convolution transposed onto their first factors are asserted to converge
to a tensor representing convolution after spectral projection.
Deviation: Read (10.4.3.42) as (10.4.3.43) in part (3), so that the limit has
the stated ambient type. Use the strip indices and the rectangular order. -/
def Printed.spectralStripTransposeLimit_operator : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α s : ℝ), 0 < a →
    ∀ (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽(F))
      (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (eχ : PontryaginDual C₁(F) ↪ ℕ) (e : Z(F, a, α, χ) ↪ ℕ × ℕ),
      (∀ z, (e z).1 = eχ z.val.1) →
      (∀ z z' : Z(F, a, α, χ), z.val.1 = z'.val.1 → (e z).2 ≤ (e z').2 →
        |z.val.2.2| ≤ |z'.val.2.2|) →
      let Θ := globalThetaSobolev F a (hStrip(hα)) hs₀(hs)
      let H := spectralSobolevQuotient F a (hStrip(hα)) hs₀(hs)
      let D := spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
      let Aq := spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ
      ∀ (x : SpectralStripJetIndex χ a α s → H)
        (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H),
        IsSpectralMarkushevichBasis x f →
        (∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp
          (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) →
        ∃ K : Completion (ProjectiveTensor W'(F, α, s) W(F, α, s)),
          Tendsto (spectralKernelRectangle e (fun z ↦ N(a, α, s, χ, z))
            (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)
            (fun j ↦ D ((f j).comp Aq))
            (fun j ↦ (Θ.quotientEquivOrthogonal (x j) : W(F, α, s)))) atTop (𝓝 K) ∧
          sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K =
            (A(F, hα, hs₀(hs), φ)).comp (spectralProjection a hα hs₀(hs))

/-- Paper: Theorem 10.4.3.5(3), p. 473. Over ℚ use α = 0, s = 4
and a nontrivial zeta zero a + iγ. Its order-zero Riesz vector on the
log-norm line is g(t) = exp(−iγt)/(1+t²)². Every printed finite section
has spectral output. Take the nonzero weighted theta vector q of the
polar-free rational test with finite factor 1_{ℤ̂} and real factor
exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²).
The Fourier transform of (1+t²)⁻² is everywhere positive, so pairing q
with translates of g cannot vanish identically. Choose a smooth bump
of integral one concentrated at such a shift as φ. Then A(φ)g has a
nonzero geometric component, whereas any limit of the printed tensors
has spectral output. -/
theorem Printed.spectralStripTransposeLimit_operator_false :
    ¬ Printed.spectralStripTransposeLimit_operator := by sorry

/-- Paper: Theorem 10.4.3.6(2), p. 473, second formula. The cutoff
spectral function is claimed to represent the geometric restriction.
The two reciprocal weights account for (10.4.3.47) and (10.4.3.49).
Deviation: Interpret the weight using the cited interval [−α, α]. -/
def Printed.spectralStripRestrictionKernel_geometric : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α s : ℝ), 0 < a →
    ∀ (hα : 0 ≤ α) (hs : 1 < s) (Λ ε : ℝ) (ρ : C𝔽(F) → ℝ)
      (hρ : IsModulatedCutoff m𝔽(F) Λ ε ρ),
      0 < Λ⁻¹ + ε → Λ⁻¹ + ε < Λ - ε →
      ∀ (φ : BruhatCompactSupport C𝔽(F)) (k : mixed(F, α, s)),
        represents(F, α, s, (A(F, hα, hs₀(hs), φ)).comp
          (spectralProjection (F := F) a hα hs₀(hs)), k) →
        IsSobolevHilbertSchmidtKernel (geometricRestriction a hα hs₀(hs) hρ φ)
          (printedWeight(F, α, s, ρ, k))

/-- Paper: Theorem 10.4.3.6(2), p. 473. For F = ℚ, a = 3, α = 1
and s = 4 the strip lies in the zero-free half-plane. The spectral
kernel vanishes. With Λ = 2, ε = 1/8 and the outer-band indicator,
geometric restriction is nonzero on the same even log-norm bump used
for the line counterexample. -/
theorem Printed.spectralStripRestrictionKernel_geometric_false :
    ¬ Printed.spectralStripRestrictionKernel_geometric := by sorry

end RiemannMasullo
