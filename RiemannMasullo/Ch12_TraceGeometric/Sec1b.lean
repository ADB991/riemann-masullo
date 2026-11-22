module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-!
# Localization along the global diagonal

Masullo, Theorem 12.1.1.3, pp. 502–503. The product averages use Haar
measure and a chosen Borel D′-sequence on the idele class group. The
operators whose traces are computed act on the weighted Sobolev space.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 900000

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 logNorm (-(0 : ℝ)) 0 s
local notation "hline" => (le_refl (0 : ℝ))
local notation "hbase" => ((neg_nonpos.mpr hline).trans hline)
local notation "hs₀(" hs ")" => (le_trans (by norm_num : (0 : ℝ) ≤ 3) hs)
local notation "convKernel(" φ ")" =>
  (fun p : C𝔽 × C𝔽 ↦ (φ : BruhatCompactSupport C𝔽).val (p.1 * p.2⁻¹))
local notation "innerBand(" Λ ", " ε ")" => (0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε)

-- TODO(paper-gap): The printed standard sequence on the idele class group
-- need not shrink to the identity. Use a Borel D′-sequence as in §12.1a.
variable {U : ℕ → Set (IdeleClassGroup (𝓞 F) F)}
  (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U) (hBorel : ∀ n, MeasurableSet (U n))

local notation "regular(" k ")" =>
  dSequenceRegularSet ((μ𝔽).prod μ𝔽) (fun n ↦ U n ×ˢ U n) k
local notation "diagonal(" k ")" => (fun x ↦ dSequenceKernelSmoothening μ𝔽 U k (x, x))

include hU hBorel

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal points of the convolution
kernel are regular for the Haar product averages.
Deviation: A valid Borel D′-sequence is explicit throughout. -/
theorem diagonal_mem_convolutionKernelRegularSet (φ : BruhatCompactSupport C𝔽) (x : C𝔽) :
    (x, x) ∈ regular(convKernel(φ)) := by sorry

section GlobalKernels

variable (a : ℝ) {s : ℝ} (hs : 3 ≤ s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))

local notation "Tspec" => (spectralProjection (F := F) a hline hs₀(hs)).comp
  (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ)
local notation "Tgeom(" hρ ")" => geometricTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ

variable (k : Lp ℂ 2
  (((ideleClassTamagawaMeasure F).withDensity (fun g ↦ ENNReal.ofReal
    (intervalSobolevDensity (-(0 : ℝ)) 0 s (Real.log ((ideleClassNorm F g).val : ℝ))))).prod
   ((ideleClassTamagawaMeasure F).withDensity (fun g ↦ ENNReal.ofReal
    (intervalSobolevDensity (-(0 : ℝ)) 0 s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹))))

local notation "kspec" => globalSpectralKernel (F := F) (α := 0) (s := s) k
local notation "kgeom" => globalGeometricKernel (F := F) (α := 0) (s := s) φ k
local notation "spectralKernelFor" => (∀ u : W(s), ∀ᵐ x ∂μ𝔽,
  Integrable (fun y ↦ kspec (x, y) * u y) μ𝔽 ∧ Tspec u x = ∫ y, kspec (x, y) * u y ∂μ𝔽)

-- TODO(paper-gap): On p. 503 the proof applies the weighted L² trace theorem
-- to the Haar kernels directly. The actual Hilbert-Schmidt representatives
-- in §10.4.3.4 carry the reciprocal input weight. Its effect on the diagonal
-- smoothening must be justified for Haar-almost every center.

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal of the global spectral
kernel is regular for Haar-almost every center.
Deviation: The mixed-weight representative from §10.4.3 and its Haar
integral representation of spectral projection after convolution are explicit. -/
theorem ae_diagonal_mem_globalSpectralKernelRegularSet
    (_ha : 0 < a) (_hk : spectralKernelFor) :
    ∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kspec) := by sorry

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal of the global geometric
kernel is regular for Haar-almost every center.
Deviation: The spectral representative used to form the geometric kernel is explicit. -/
theorem ae_diagonal_mem_globalGeometricKernelRegularSet
    (_ha : 0 < a) (_hk : spectralKernelFor) :
    ∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kgeom) := by sorry

/-- Paper: Theorem 12.1.1.3(2), p. 502. In (12.1.1.20), geometric
truncation after convolution is trace class. Its trace is the Haar integral
of the cutoff times the smoothened geometric diagonal.
Deviation: The spectral representative is explicit. The real smooth cutoff
uses §9.3.3.1, and absolute integrability of the trace integrand is explicit. -/
theorem geometricTruncatedConvolution_trace_eq_integral_globalDiagonal
    (_ha : 0 < a) (_hk : spectralKernelFor)
    {Λ ε : ℝ} {ρ : C𝔽 → ℝ} (hρ : IsSmoothModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand(Λ, ε)) :
    let T := Tgeom(hρ.1)
    ∃ hT : IsNuclearOperator T,
      Integrable (fun x ↦ (ρ x : ℂ) * diagonal(kgeom) x) μ𝔽 ∧
      hilbertTrace (H := W(s)) ⟨T, hT⟩ =
        ∫ x, (ρ x : ℂ) * diagonal(kgeom) x ∂μ𝔽 := by sorry

/-- Paper: Theorem 12.1.1.3(2), p. 503. In (12.1.1.21), spectral
projection after convolution is trace class. Its trace is the Haar integral
of the smoothened spectral diagonal.
Deviation: The representative and absolute integrability are explicit. -/
theorem spectralProjection_convolution_trace_eq_integral_globalDiagonal
    (_ha : 0 < a) (_hk : spectralKernelFor) :
    let T := Tspec
    ∃ hT : IsNuclearOperator T,
      Integrable diagonal(kspec) μ𝔽 ∧
      hilbertTrace (H := W(s)) ⟨T, hT⟩ = ∫ x, diagonal(kspec) x ∂μ𝔽 := by sorry

-- TODO(paper-gap): The citation of Theorem 10.4.3.1(4) for integrability
-- points to an enumeration condition. Theorem 10.4.3.4(4), cited in the
-- following remark for the same assertion, has no part (4).

/-- Paper: Theorem 12.1.1.3(3), p. 503. When the test vanishes at the
identity, the smoothened geometric diagonal is absolutely Haar integrable.
Deviation: The spectral representative is explicit. -/
theorem integrable_globalGeometricKernel_diagonal
    (_ha : 0 < a) (_hk : spectralKernelFor) (_hφ : φ.val 1 = 0) :
    Integrable diagonal(kgeom) μ𝔽 := by sorry

/-- Paper: Theorem 12.1.1.3(3), p. 503. In (12.1.1.22), as the radius
tends to infinity and the width times the radius tends to zero, the
geometric truncation traces tend to the Haar mass of the smoothened diagonal.
Deviation: The spectral representative is explicit. A filter represents
the joint limit, with smooth real cutoffs and their traces specified eventually. -/
theorem geometricTruncatedConvolution_trace_tendsto_integral_globalDiagonal
    (_ha : 0 < a) (_hk : spectralKernelFor)
    (_hφ : φ.val 1 = 0) {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsSmoothModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    ∃ traces : ι → ℂ,
      (∀ᶠ i in l, ∃ hcut : IsSmoothModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i),
        let T := Tgeom(hcut.1)
        ∃ hT : IsNuclearOperator T, traces i = hilbertTrace (H := W(s)) ⟨T, hT⟩) ∧
      Tendsto traces l (𝓝 (∫ x, diagonal(kgeom) x ∂μ𝔽)) := by sorry

/-- Paper: (12.1.1.23), p. 503. If the test vanishes at the identity, the
smoothened geometric diagonal is the negative of the spectral diagonal.
The smoothening uses the zero extension from Definition 12.1.1.1. -/
theorem globalGeometricKernel_diagonal_eq_neg_spectral (_hφ : φ.val 1 = 0) (x : C𝔽) :
    diagonal(kgeom) x = -diagonal(kspec) x := by sorry

/-- Paper: (12.1.1.24), p. 503. If the test vanishes at the identity, the
cutoff integrals of the smoothened geometric diagonal converge to its full Haar integral.
Deviation: The spectral representative is explicit. A filter expresses the
joint limit for the radius and width. -/
theorem tendsto_integral_cutoff_globalGeometricKernel_diagonal
    (_ha : 0 < a) (_hk : spectralKernelFor)
    (_hφ : φ.val 1 = 0) {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsSmoothModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    Tendsto (fun i ↦ ∫ x, (ρ i x : ℂ) * diagonal(kgeom) x ∂μ𝔽) l
      (𝓝 (∫ x, diagonal(kgeom) x ∂μ𝔽)) := by sorry

-- TODO(paper-gap): The end of the proof cites (10.4.3.31) as its conclusion.
-- The intended conclusion is (12.1.1.22). The geometric kernel formula is
-- (10.4.3.31), while (10.4.3.32) starts a computation of the kernel action.

end GlobalKernels

end RiemannMasullo
