module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # §10.1 assertions that are false as printed -/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

local instance instSIdeleQuotientMeasurableSpaceSec1Printed
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (SIdeleQuotient F S) := borel _

local instance instIdeleClassMeasurableSpaceSec1Printed (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _

local instance instNormOneSIdeleQuotientMeasurableSpaceSec1Printed
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (sIdeleQuotientNorm F S).ker := borel _

/-- Paper: Definition 10.1.1.1(2) and Remark 10.1.1.2, p. 434. As printed,
the integral defining the local norm is finite at every positive weight and
every compact nonempty interval. -/
def Printed.sLocalThetaSobolev_integrable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a α β s : ℝ), 0 < a → α ≤ β → 0 ≤ s →
    ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      Integrable (fun g : SIdeleQuotient F S ↦ ‖sLocalAdelicThetaOnClasses F S f g‖ ^ 2 *
        intervalSobolevDensity (a + α) (a + β) s
          (Real.log ((sIdeleQuotientNorm F S g).val : ℝ))) (sLocalQuotientTamagawaMeasure F S)

/-- Paper: Definition 10.1.1.1(2) and Remark 10.1.1.2, p. 434.
For ℚ with S consisting of the real place, take f(x) = exp(-πx²), a = 1,
I = {-1} and s = 0. The two S-units give theta(t) = 2 exp(-πt²), whose
square is not integrable near zero against dt/t. -/
theorem Printed.sLocalThetaSobolev_integrable_false :
    ¬ Printed.sLocalThetaSobolev_integrable := by sorry

/-- Paper: Proof of Lemma 10.1.1.4(1), p. 436. As printed, the density of
the weighted S-idele measure vanishes at infinity. -/
def Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (α β s : ℝ), α ≤ β → 0 ≤ s →
    Tendsto (fun g : (SAdeleRing F S)ˣ ↦
      intervalSobolevDensity α β s (Real.log ((sIdeleNorm F S g).val : ℝ)))
      (cocompact _) (nhds 0)

/-- Paper: Proof of Lemma 10.1.1.4(1), p. 436. For ℚ with S the real place,
I = {1} and s = 0, the density is t² on the positive ideles t, so it
grows without bound as t tends to infinity. -/
theorem Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity_false :
    ¬ Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity := by sorry

/-- Paper: Proposition 10.1.1.5, pp. 436–437. As printed, the global Sobolev
completion in the proposition uses theta functions of all Schwartz–Bruhat tests.
The proposed completion requires their weighted square integrability. -/
def Printed.globalThetaSobolev_allTests_integrable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α β s : ℝ), α ≤ β → 0 ≤ s →
    ∀ f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)),
      Integrable (fun g : IdeleClassGroup (𝓞 F) F ↦ ‖adelicTheta f g‖ ^ 2 *
        intervalSobolevDensity (a + α) (a + β) s
          (Real.log ((ideleClassNorm F g).val : ℝ))) (ideleClassTamagawaMeasure F)

/-- Paper: Proposition 10.1.1.5, pp. 436–437. For ℚ, set a = s = 0
and I = {0}. The real Gaussian times the characteristic functions of the finite
integer rings has theta(t) = Σ_{n ≠ 0} exp(-πn²t²), asymptotic to 1/t at zero
on each norm-one fibre, so its square is not integrable. -/
theorem Printed.globalThetaSobolev_allTests_integrable_false :
    ¬ Printed.globalThetaSobolev_allTests_integrable := by sorry

/-- Paper: Proposition 10.1.1.5(2), p. 437. With the global completion read
as the polar-free one from Definition 10.1.1.1, the printed isometry would
have the raw global Tamagawa averages as its coordinates. -/
def Printed.globalThetaSobolev_rawIsotypeDecomposition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (a α β s : ℝ) (hI : α ≤ β) (hs : 0 ≤ s),
    let H := ↥(globalThetaSobolev F a hI hs)
    let ρ := (exists_globalThetaSobolevAction (F := F) a hI hs).choose
    let E := actionIsotype (ρ.comp (ideleClassNorm F).ker.subtype)
    let P := fun ω : PontryaginDual (ideleClassNorm F).ker ↦
      (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose
    ∃ T : H ≃ₗᵢ[ℂ] lp (fun ω ↦ ↥(E ω)) 2, ∀ u ω, T u ω = P ω u

/-- Paper: Proposition 10.1.1.5(2), p. 437. Take ℚ(i), a = s = 0 and I = {0}.
Use the finite integer indicators and a radial smooth archimedean bump equal to 1
at radius 1 and supported in (0.9, 1.1). Subtract a radial bump supported in (0.4, 0.6)
scaled to cancel the integral. Both zero terms vanish and theta at the identity is 4.
This theta lies in the trivial isotype. The norm-one mass π/4 scales its only
nonzero coordinate and prevents an isometry. -/
theorem Printed.globalThetaSobolev_rawIsotypeDecomposition_false :
    ¬ Printed.globalThetaSobolev_rawIsotypeDecomposition := by sorry

/-- Paper: Proposition 10.1.1.5(2), p. 437. The norm-preservation clause of the
printed S-local Hilbert-sum factorization says that the squares of the norms of
the raw coordinates sum to the square of the norm of the original vector. -/
def Printed.sLocalThetaSobolev_rawIsotypeDecomposition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a α β s : ℝ) (ha : 0 < a) (hI : α ≤ β) (hs : 0 ≤ s) (hα : 0 < α),
    ∀ u : sLocalThetaSobolev F S ha hI hs (add_pos ha hα),
      HasSum (fun ω : PontryaginDual (sIdeleQuotientNorm F S).ker ↦
        ‖(existsUnique_sLocalThetaSobolevAverage (F := F) (S := S) ha hI hs hα ω).exists.choose u‖ ^ 2)
        (‖u‖ ^ 2)

/-- Paper: Proposition 10.1.1.5(2), p. 437. Take ℚ(i), S consisting of the
complex place, a = 1, I = {1}, and s = 0. A nonzero radial Gaussian theta
function lies in the trivial isotype. Its raw average is π/2 times itself
and every other character average is zero, so the Hilbert sum norm grows by π/2. -/
theorem Printed.sLocalThetaSobolev_rawIsotypeDecomposition_false :
    ¬ Printed.sLocalThetaSobolev_rawIsotypeDecomposition := by sorry

/-- Paper: Theorem 10.1.2.1, p. 437. As printed, inversion in the idele class
group defines a continuous linear automorphism of the same ambient Sobolev space
for every compact nonempty interval. -/
def Printed.ideleClassSobolev_inversion_automorphism : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (α β s : ℝ), α ≤ β → 0 ≤ s →
    let μ := ideleClassTamagawaMeasure F
    let W := CompactIntervalSobolev μ
      (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) α β s
    ∃ J : W ≃L[ℂ] W, ∀ u : W,
      (J u : IdeleClassGroup (𝓞 F) F → ℂ) =ᵐ[μ] fun g ↦ u g⁻¹

/-- Paper: Theorem 10.1.2.1, p. 437. Take ℚ, I = {1} and s = 0. The indicator
of |g| < 1 is square integrable for t² dt/t in the norm coordinate t, while its
inverse pullback is the indicator of |g| > 1, which has infinite squared integral. -/
theorem Printed.ideleClassSobolev_inversion_automorphism_false :
    ¬ Printed.ideleClassSobolev_inversion_automorphism := by sorry

end RiemannMasullo
