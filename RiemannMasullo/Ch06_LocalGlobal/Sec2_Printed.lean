module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.Ch02_AdelicTheta.Sec4
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian
import RiemannMasullo.ForMathlib.RingTheory.PicardGroup
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Chapter 6.2: statements that are false as printed -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped DirectSum NNReal

namespace RiemannMasullo

set_option quotPrecheck false

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Picₛ(" F ", " S ")" => CommRing.Pic ((S : Set (Places(F))).integer F)
local notation "Iₛ(" F ", " S ")" => (SAdeleRing F S)ˣ
local notation "Nₛ(" F ", " S ")" => (sIdeleNorm F S).ker
local notation "J₁(" F ", " S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "ℬ∞(" F ")" => ℬ(InfiniteAdeleRing F)
local notation "L(" F ", " v ")" => HeightOneSpectrum.adicCompletion (R := 𝓞 F) F v
local notation "O(" F ", " v ")" => HeightOneSpectrum.adicCompletionIntegers (R := 𝓞 F) F v

open Classical in
/-- Paper: Remark 6.2.1.4(1), (6.2.1.2), p. 297. As printed: the locally convex direct sum
topologies of the S-local and global isotypes are strictly finer than the topologies induced by
their inclusions into the ordinary theta quotients. See `sLocalThetaIsotypeSum_dense`,
`globalThetaIsotypeSum_dense` and ERRATA F71. -/
def Printed.thetaIsotypeSum_strictlyFiner : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∀ S : Finset (Places(F)),
      let ρ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
      let E := actionIsotype (ρ.comp (sIdeleQuotientNorm F S).ker.subtype)
      let X := fun χ : PontryaginDual J₁(F, S) ↦ ↥(E χ)
      let _ := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
      ¬ IsInducing (DirectSum.toModule ℂ _ (SLocalAdelicThetaSpace F S) fun χ ↦ (E χ).subtype)) ∧
    (let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
      let E := actionIsotype (ρ.comp (ideleClassNorm F).ker.subtype)
      let X := fun ω : PontryaginDual C₁(F) ↦ ↥(E ω)
      let _ := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
      ¬ IsInducing (DirectSum.toModule ℂ _ (GlobalAdelicThetaSpace F) fun ω ↦ (E ω).subtype))

/-- A norm-one rational idele at the archimedean stage is represented by a diagonal sign. -/
private theorem thetaIsotypeSum_strictlyFiner_false_rat :
    Subsingleton (sIdeleQuotientNorm ℚ ∅).ker := by
  classical
  refine subsingleton_of_forall_eq 1 ?_
  rintro ⟨q, hq⟩
  apply Subtype.ext
  change q = 1
  revert hq
  refine Quotient.inductionOn q fun g hg ↦ ?_
  change sIdeleNorm ℚ ∅ g = 1 at hg
  let w := Rat.infinitePlace
  let coord : SAdeleRing ℚ ∅ ≃+* ℝ :=
    ((RingEquiv.prodZeroRing _ _).symm.trans
      (RingEquiv.piUnique fun v : InfinitePlace ℚ ↦ v.Completion)).trans
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
  have hn : ‖g.val.1 w‖ = 1 := by
    have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hg
    rwa [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (Places(ℚ)))),
      Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ w,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one] at h
  have ha : |coord g.val| = 1 :=
    ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) _).trans hn
  apply (sIdeleQuotient_mk_eq_one ℚ ∅ g).mpr
  rcases eq_or_eq_neg_of_abs_eq ha with h | h
  · refine ⟨1, Units.ext (coord.injective ?_)⟩
    simpa only [map_one, Units.val_one] using h
  · refine ⟨-1, Units.ext (coord.injective ?_)⟩
    change coord g.val = coord (((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅ (-1)))
    simpa only [map_neg, map_one] using h

/-- For a single submodule, the locally convex direct sum induces the subspace topology. -/
private theorem thetaIsotypeSum_strictlyFiner_false_single
    {E I : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    [Subsingleton I] [DecidableEq I] (X : I → Submodule ℂ E) (k : I) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I fun i ↦ ↥(X i))
    IsInducing (DirectSum.toModule ℂ I E fun i ↦ (X i).subtype) := by
  let D := ⨁ i, ↥(X i)
  let j := DirectSum.lof ℂ I fun i ↦ ↥(X i)
  let : TopologicalSpace D := locallyConvexFinalTopology j
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ j i)} → Seminorm ℂ D) := ⟨rfl⟩
  let := hD.isTopologicalAddGroup
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  let c := DirectSum.component ℂ I (fun i ↦ ↥(X i)) k
  have hj : Continuous (j k) := hD.continuous_of_continuous_comp _ fun p ↦ p.property k
  have hc : Continuous c := by
    apply (PolynormableSpace.withSeminorms ℂ (X k)).continuous_of_continuous_comp c
    intro p
    apply hD.continuous_seminorm ⟨p.val.comp c, ?_⟩
    intro i
    obtain rfl := Subsingleton.elim i k
    change Continuous fun x : X i ↦ p.val ((j i x) i)
    simp only [j, DirectSum.lof_apply]
    exact p.property
  -- Projection onto the only component is inverse to its inclusion.
  have hleft : LeftInverse (j k) c := by
    intro x
    apply DFinsupp.ext
    intro i
    obtain rfl := Subsingleton.elim i k
    exact DFinsupp.single_eq_same
  have hsum : ⇑(DirectSum.toModule ℂ I E fun i ↦ (X i).subtype) = Subtype.val ∘ c := by
    funext x
    conv_lhs => rw [← hleft x]
    exact DirectSum.toModule_lof (M := fun i ↦ ↥(X i)) (φ := fun i ↦ (X i).subtype) ℂ k (c x)
  rw [hsum]
  exact IsInducing.subtypeVal.comp (hleft.isEmbedding hj hc).isInducing

/-- Paper: Remark 6.2.1.4(1), (6.2.1.2), p. 297. Over ℚ at the archimedean stage the norm-one
quotient is `{±1}/{±1}`, so the sole summand is the entire theta space with its own topology.
Globally over ℚ, the action of the profinite norm-one group factors through a finite group on
each finite test level. The finite character projections extend through the inductive limit and
the theta quotient to a continuous inverse to the sum map. -/
theorem Printed.thetaIsotypeSum_strictlyFiner_false :
    ¬ Printed.thetaIsotypeSum_strictlyFiner := by
  classical
  intro h
  apply (h ℚ).1 ∅
  let G := (sIdeleQuotientNorm ℚ ∅).ker
  let : Subsingleton G := thetaIsotypeSum_strictlyFiner_false_rat
  let : Subsingleton (PontryaginDual G) := subsingleton_of_forall_eq 1 fun χ ↦
    PontryaginDual.ext fun g ↦ by rw [Subsingleton.elim g 1, map_one, map_one]
  let : DecidableEq (PontryaginDual G) := Classical.decEq _
  let : PolynormableSpace ℂ (SLocalAdelicThetaSpace ℚ ∅) := sLocalAdelicThetaSpace_polynormable
  let ρ := (existsUnique_sLocalThetaAction (F := ℚ) (S := ∅)).exists.choose
  let X := actionIsotype (ρ.comp (sIdeleQuotientNorm ℚ ∅).ker.subtype)
  exact thetaIsotypeSum_strictlyFiner_false_single (E := SLocalAdelicThetaSpace ℚ ∅)
    (I := PontryaginDual G) X 1

/-- Paper: Remark 6.2.1.4(2), p. 298. As printed: the S-local theta quotient has nonclosed
image in the product of its homogeneous theta quotients, and the topology induced by the product
is strictly coarser. We take the product in (5.2.3.13), Proposition 5.2.3.2(2), p. 236.
The remark gives conflicting references, including (5.2.2.3), which defines a quotient. See the
global versions `globalThetaToHomogeneousProduct_not_isClosed_range` and
`globalThetaToHomogeneousProduct_not_isInducing`, and ERRATA F72. -/
def Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    let P := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose
    ¬ IsInducing P ∧ ¬ IsClosed (Set.range P)

/-- At the rational archimedean stage, the two norm-one ideles are both diagonal units. -/
private theorem sLocalThetaToHomogeneousProduct_normOne_rat :
    Subsingleton (sIdeleQuotientNorm ℚ ∅).ker := by
  refine subsingleton_of_forall_eq 1 fun ⟨x, hx⟩ ↦ Subtype.ext ?_
  change x = 1
  revert hx
  refine Quotient.inductionOn x fun g hg ↦ ?_
  change sIdeleNorm ℚ ∅ g = 1 at hg
  let j := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let e : SAdeleRing ℚ ∅ ≃+* ℝ := ((RingEquiv.prodZeroRing _ _).symm.trans
    (RingEquiv.piUnique fun w : InfinitePlace ℚ ↦ w.Completion)).trans j
  have hnorm : |e g.val| = 1 := by
    trans ‖g.val.1 Rat.infinitePlace‖
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
        Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) _
    have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hg
    rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))),
      Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ Rat.infinitePlace,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one] at h
    exact h
  rcases eq_or_eq_neg_of_abs_eq hnorm with h | h
  · have hg1 : g = 1 := Units.ext (e.injective (h.trans (map_one e).symm))
    simp [hg1]
  · have hgneg : g = -1 := Units.ext (e.injective (by simpa using h))
    refine (sIdeleQuotient_mk_eq_one ℚ ∅ g).2 ⟨-1, ?_⟩
    apply Units.ext
    simp [hgneg]

/-- With just the trivial norm-one character, any element of the product is represented
by a test function in its sole coordinate. Thus the product map has closed range. -/
private theorem sLocalThetaToHomogeneousProduct_isClosed_of_subsingleton
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hG : Subsingleton (sIdeleQuotientNorm F S).ker) :
    IsClosed (Set.range (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose) := by
  let P := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose
  suffices hs : Surjective P by
    exact (congrArg IsClosed hs.range_eq).mpr isClosed_univ
  let χ₀ : PontryaginDual (sIdeleQuotientNorm F S).ker := 1
  have hχ (χ : PontryaginDual (sIdeleQuotientNorm F S).ker) : χ = χ₀ := by
    apply PontryaginDual.ext
    intro g
    rw [hG.allEq g 1, map_one, map_one]
  intro y
  let K := LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S χ₀)
  let f := (K.mkQ_surjective (y χ₀)).choose
  have hf : K.mkQ f = y χ₀ := (K.mkQ_surjective (y χ₀)).choose_spec
  let x := (sLocalAdelicTheta F S).ker.mkQ f
  have hx := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose_spec.2 f χ₀
  refine ⟨x, ?_⟩
  funext χ
  exact (congrArg (fun i ↦ P x i = y i) (hχ χ)).mpr (hx.trans hf)

/-- Paper: Remark 6.2.1.4(2), p. 298. Take ℚ and the archimedean stage. The norm-one quotient
is trivial, and projection to the sole factor identifies the product map with the identity on
the theta quotient. The range is closed and the induced topology is the intrinsic topology. -/
theorem Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed_false :
    ¬ Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed := by
  intro h
  exact (h ℚ ∅).2 (sLocalThetaToHomogeneousProduct_isClosed_of_subsingleton ℚ ∅
    sLocalThetaToHomogeneousProduct_normOne_rat)

section StandardFunctions

variable {F : Type*} [Field F] [NumberField F]

local instance printedCh06Sec2FiniteIdeleMeasurableSpace (v : Places(F)) :
    MeasurableSpace (L(F, v))ˣ := borel _

local notation "U(" F ", " v ")" => ((O(F, v)).units : Set (L(F, v))ˣ)
local notation "μ(" F ", " v ")" => finiteLocalMultiplicativeTamagawaMeasure F v

open Classical in
/-- Paper: Theorem 6.2.2.1, first numbered definition, p. 298. As printed: at a ramified place
in S the standard test has zeta integral equal to the integer-unit mass when the character
matches on integer units and has positive abscissa, and zero otherwise. See
`finiteStandardGaussian_zeta_of_ramified` and ERRATA F73. -/
def Printed.finiteStandardGaussian_zeta_of_ramified_positive : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S) (v : S)
      (d : QuasiCharacter (L(F, v.val))ˣ),
      let c := sLocalFiniteRestriction v (sIdeleRestriction F S hω.choose)
      let Uv := U(F, v.val)
      (∃ u ∈ Uv, c u ≠ 1) →
        localIdelicZetaIntegral (μ(F, v.val))
          (fun x ↦ finiteStandardGaussian v.val c (Multiplicative.ofAdd x)) d =
        if (∀ u ∈ Uv, d u = c u) ∧ (∃ σ : ℝ, 0 < σ ∧ ∀ g : (L(F, v.val))ˣ,
          ‖d g‖ = ‖g.val‖ ^ σ) then ((μ(F, v.val)) Uv).toReal else 0

/-- Paper: Theorem 6.2.2.1, first numbered definition, p. 298. Over ℚ take the even quadratic
idele class character modulo 5, S consisting of the infinite place and 5, and the unitary local
character at 5 as d. Its abscissa is zero. The standard test is its conjugate on the integer
units, so the integrand is their indicator and the integral is their positive mass. -/
theorem Printed.finiteStandardGaussian_zeta_of_ramified_positive_false :
    ¬ Printed.finiteStandardGaussian_zeta_of_ramified_positive := by sorry

-- The sum in (6.2.2.3) uses a list of norm-one representatives of the full class group.
local notation "ClassRepresentatives(" F ", " S ", " r ")" =>
  (r ⟨0, classNumber_pos F⟩ = 1 ∧
    Bijective (fun k ↦ ideleIdealClass F (sIdeleInsertion F S (r k).val)))

local notation "Lifts(" F ", " S ", " χ ", " ωₛ ")" =>
  (∀ (g : Nₛ(F, S)) (y : J₁(F, S)), y.val = QuotientGroup.mk g.val → χ g.val = ωₛ y)

open Classical in
/-- Paper: Theorem 6.2.2.1(1), (6.2.2.7)–(6.2.2.10), pp. 299–301. As printed: on pure tensors
of archimedean tests and punctured finite tests the norm-one integral (6.2.2.7) equals the product
of the archimedean operator (6.2.2.3) and the finite convolutions (6.2.2.4). This is the
pointwise identity asserted for the tensor extension. See
`sLocalStandardThetaTensor_toGlobal_openQuotient` and ERRATA F74. -/
def Printed.sLocalStandardThetaTensor_factorization : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S)
      (χ : PontryaginDual Iₛ(F, S)),
      Lifts(F, S, χ, sLocalNormOneCharacter S ω hω) →
      ∀ (r : Fin (classNumber F) → Nₛ(F, S)), ClassRepresentatives(F, S, r) →
      ∀ (f : ℬ∞(F)) (fv : ∀ v : S, finitePuncturedThetaTestSpace v.val) (x : Iₛ(F, S)),
        let xArch := Units.map (RingHom.fst (InfiniteAdeleRing F) (∀ v : S, L(F, v.val))).toMonoidHom x
        let ins (v : S) := Units.map ((MonoidHom.inr (InfiniteAdeleRing F) _).comp
          (MonoidHom.mulSingle (fun v : S ↦ L(F, v.val)) v))
        (∫ g : Nₛ(F, S),
          let y := g.val⁻¹ * x
          f (Multiplicative.ofAdd y.val.1) *
            (∏ v : S, (fv v).val (Multiplicative.ofAdd (y.val.2 v))) * (χ g.val : ℂ)
          ∂sNormOneIdeleTamagawaMeasure F S) =
        infiniteStandardThetaAverage χ r f xArch *
          ∏ v : S, ∫ g : (L(F, v.val))ˣ,
            (fv v).val (Multiplicative.ofAdd ((g⁻¹).val * x.val.2 v)) * (χ (ins v g) : ℂ)
            ∂μ(F, v.val)

/-- Over ℚ every ring of S-integers has trivial Picard group: it is a localization of `𝓞 ℚ`,
which is a principal ideal domain. -/
private theorem sLocalStandardThetaTensor_factorization_false_pic (S : Finset (Places(ℚ))) :
    Subsingleton Picₛ(ℚ, S) := by
  have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
  have hs := picMapAlgebra_surjective_of_isLocalization
    (Localization.submonoid (S : Set (Places(ℚ)))) (R := 𝓞 ℚ)
    (A := (S : Set (Places(ℚ))).integer ℚ)
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a', rfl⟩ := hs a
  obtain ⟨b', rfl⟩ := hs b
  rw [Subsingleton.elim a' b']

/-- The trivial norm-one character is unramified outside any set of places. -/
private theorem sLocalStandardThetaTensor_factorization_false_unramified
    (S : Finset (Places(ℚ))) :
    NormOneCharacterUnramifiedOutside (1 : PontryaginDual C₁(ℚ)) S :=
  ⟨⟨1, (mem_unramifiedOutside_iff ℚ S 1).mpr fun _ _ _ ↦ rfl⟩, fun _ ↦ rfl⟩

/-- The descent of the trivial norm-one character is trivial. -/
private theorem sLocalStandardThetaTensor_factorization_false_descent
    (S : Finset (Places(ℚ))) (hω : NormOneCharacterUnramifiedOutside (1 : PontryaginDual C₁(ℚ)) S) :
    sLocalNormOneCharacter S (1 : PontryaginDual C₁(ℚ)) hω = 1 :=
  ((normOneCharacterUnramifiedOutside_iff (F := ℚ) (S := S) 1).mp hω).unique
    ((normOneCharacterUnramifiedOutside_iff (F := ℚ) (S := S) 1).mp hω).exists.choose_spec
    (fun _ _ _ _ _ ↦ rfl)

/-- Over ℚ the constant family `1` lists representatives of the (trivial) class group. -/
private theorem sLocalStandardThetaTensor_factorization_false_classes (S : Finset (Places(ℚ))) :
    ClassRepresentatives(ℚ, S, fun _ : Fin (classNumber ℚ) ↦ (1 : Nₛ(ℚ, S))) := by
  have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
  refine ⟨rfl, ⟨fun a b _ ↦ ?_, fun c ↦ ⟨⟨0, classNumber_pos ℚ⟩, Subsingleton.elim _ _⟩⟩⟩
  have ha := a.isLt
  have hb := b.isLt
  have hc := Rat.classNumber_eq
  exact Fin.ext (by omega)

/-- The archimedean test `(q² - t²) exp(-t²)` on the infinite adeles of ℚ, written in terms of
the norm of the real coordinate. -/
private theorem sLocalStandardThetaTensor_factorization_false_arch (q : ℝ) :
    ∃ f : ℬ∞(ℚ), ∀ x : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd x) =
      (((q ^ 2 - ‖x Rat.infinitePlace‖ ^ 2) * Real.exp (-‖x Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ) := by
  let g0 : SchwartzMap ℝ ℝ := SchwartzMap.gaussian 1 zero_lt_one
  let g : SchwartzMap ℝ ℂ := SchwartzMap.postcompCLM Complex.ofRealCLM g0
  let h1 : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) g
  let h2 : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) h1
  let b : SchwartzMap ℝ ℂ := ((q : ℂ) ^ 2) • g - h2
  have hg : ∀ x : ℝ, g x = (Real.exp (-(x ^ 2)) : ℂ) := by
    intro x
    simp [g, g0, SchwartzMap.postcompCLM_apply, SchwartzMap.gaussian_apply]
  have hb : ∀ x : ℝ, b x = (((q ^ 2 - x ^ 2) * Real.exp (-x ^ 2) : ℝ) : ℂ) := by
    intro x
    have e1 : h1 x = (x : ℂ) * g x := by
      change SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) g x = _
      rw [SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal]
      rfl
    have e2 : h2 x = (x : ℂ) * h1 x := by
      change SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) h1 x = _
      rw [SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal]
      rfl
    change ((q : ℂ) ^ 2) * g x - h2 x = _
    rw [e2, e1, hg]
    push_cast
    ring_nf
  obtain ⟨T, hT⟩ := realSchwartzBruhat_equiv
  let realEquiv := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let realIso := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let eInfHomeo : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
    (Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans realIso.toHomeomorph
  let eArch : Multiplicative (InfiniteAdeleRing ℚ) ≃ₜ* Multiplicative ℝ :=
    { toEquiv :=
        { toFun := fun x ↦ Multiplicative.ofAdd (realEquiv (x.toAdd Rat.infinitePlace))
          invFun := fun y ↦ Multiplicative.ofAdd (eInfHomeo.symm y.toAdd)
          left_inv := fun x ↦ by
            apply congrArg Multiplicative.ofAdd
            exact eInfHomeo.symm_apply_apply x.toAdd
          right_inv := fun y ↦ by
            apply congrArg Multiplicative.ofAdd
            exact eInfHomeo.apply_symm_apply y.toAdd }
      map_mul' := fun x y ↦ congrArg Multiplicative.ofAdd (map_add realEquiv _ _)
      continuous_toFun := eInfHomeo.continuous
      continuous_invFun := eInfHomeo.symm.continuous }
  have : T2Space (Multiplicative (InfiniteAdeleRing ℚ)) := eArch.isEmbedding.t2Space
  have : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing ℚ)) :=
    eArch.isOpenEmbedding.locallyCompactSpace
  have : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  have : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  refine ⟨⟨(T b).val ∘ eArch, schwartzBruhat_mem_comp_equiv eArch (T b).property⟩, fun x ↦ ?_⟩
  have hnorm : ‖realEquiv (x Rat.infinitePlace)‖ = ‖x Rat.infinitePlace‖ :=
    realIso.isometry.norm_map_of_map_zero (map_zero realEquiv) _
  change (T b) (Multiplicative.ofAdd (realEquiv (x Rat.infinitePlace))) = _
  rw [hT b, hb, ← hnorm, Real.norm_eq_abs, sq_abs]

/-- The indicator of the sphere of radius `‖π‖ = q⁻¹` is a punctured finite test. -/
private theorem sLocalStandardThetaTensor_factorization_false_fin (v : Places(ℚ)) (r : ℝ)
    (hr : r ≠ 0) :
    ∃ fv : finitePuncturedThetaTestSpace v, ∀ z : L(ℚ, v),
      fv.val (Multiplicative.ofAdd z) = if ‖z‖ = r then 1 else 0 := by
  classical
  let : ProperSpace (L(ℚ, v)) := properSpace_adicCompletion v
  have hloc : IsLocallyConstant (fun z : L(ℚ, v) ↦ if ‖z‖ = r then (1 : ℂ) else 0) := by
    have hs : IsClopen (Metric.sphere (0 : L(ℚ, v)) r) := IsUltrametricDist.isClopen_sphere (0 : L(ℚ, v)) hr
    have hlc :=
      (LocallyConstant.indicator (LocallyConstant.const (L(ℚ, v)) (1 : ℂ)) hs).isLocallyConstant
    convert hlc using 1
    funext z
    change _ = Set.indicator _ _ z
    simp [Set.indicator_apply, mem_sphere_iff_norm]
  have hcpt : HasCompactSupport (fun z : L(ℚ, v) ↦ if ‖z‖ = r then (1 : ℂ) else 0) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : L(ℚ, v)) |r|) fun z hz ↦ ?_
    refine ite_eq_right_iff.mpr fun h ↦ absurd ?_ hz
    simpa [h] using le_abs_self r
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff ℚ v _).mpr ⟨hloc, hcpt⟩
  refine ⟨⟨g, ?_⟩, hg⟩
  rw [mem_finitePuncturedThetaTestSpace, hg, norm_zero]
  exact ite_eq_right_iff.mpr fun h ↦ absurd h.symm hr

/-- Norm-one condition at the archimedean stage of ℚ. -/
private theorem sLocalStandardThetaTensor_factorization_false_normEmpty
    (y : Iₛ(ℚ, (∅ : Finset (Places(ℚ))))) (hy : sIdeleNorm ℚ ∅ y = 1) :
    ‖y.val.1 Rat.infinitePlace‖ = 1 := by
  have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hy
  rwa [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (Places(ℚ)))),
    Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ Rat.infinitePlace,
    Rat.isReal_infinitePlace.mult_eq_one, pow_one] at h

/-- Norm-one condition at the stage with one finite place over ℚ. -/
private theorem sLocalStandardThetaTensor_factorization_false_normSingle (v : Places(ℚ))
    (y : Iₛ(ℚ, ({v} : Finset (Places(ℚ))))) (hy : sIdeleNorm ℚ {v} y = 1) :
    ‖y.val.1 Rat.infinitePlace‖ * ‖y.val.2 ⟨v, Finset.mem_singleton_self v⟩‖ = 1 := by
  have : Subsingleton ({v} : Finset (Places(ℚ))) :=
    ⟨fun a b ↦ Subtype.ext ((Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm)⟩
  have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hy
  rwa [sIdeleNorm, Fintype.prod_subsingleton _ Rat.infinitePlace,
    Rat.isReal_infinitePlace.mult_eq_one, pow_one,
    Fintype.prod_subsingleton _ ⟨v, Finset.mem_singleton_self v⟩] at h

/-- The norm-one archimedean ideles of ℚ are `±1`, a finite group. -/
private theorem sLocalStandardThetaTensor_factorization_false_finite :
    Finite Nₛ(ℚ, (∅ : Finset (Places(ℚ)))) := by
  let realEquiv := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let realIso := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  have hmem (g : Nₛ(ℚ, (∅ : Finset (Places(ℚ))))) :
      realEquiv (g.val.val.1 Rat.infinitePlace) ∈ ({1, -1} : Set ℝ) := by
    have hn := sLocalStandardThetaTensor_factorization_false_normEmpty g.val
      (MonoidHom.mem_ker.mp g.property)
    have hnorm : ‖realEquiv (g.val.val.1 Rat.infinitePlace)‖ = ‖g.val.val.1 Rat.infinitePlace‖ :=
      realIso.isometry.norm_map_of_map_zero (map_zero realEquiv) _
    rw [hn, Real.norm_eq_abs] at hnorm
    rcases eq_or_eq_neg_of_abs_eq hnorm with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine Finite.of_injective (β := ({1, -1} : Set ℝ)) (fun g ↦ ⟨_, hmem g⟩) fun a b hab ↦ ?_
  have h1 : a.val.val.1 Rat.infinitePlace = b.val.val.1 Rat.infinitePlace :=
    realEquiv.injective (congrArg Subtype.val hab)
  have h2 : a.val.val.1 = b.val.val.1 := funext fun w ↦ by
    rw [Subsingleton.elim w Rat.infinitePlace]
    exact h1
  have h3 : a.val.val.2 = b.val.val.2 := funext fun w ↦ absurd w.2 (Finset.notMem_empty _)
  exact Subtype.ext (Units.ext (Prod.ext h2 h3))

/-- A Haar measure on a finite group has finite positive total mass. -/
private theorem sLocalStandardThetaTensor_factorization_false_mass {G : Type*} [Group G]
    [TopologicalSpace G] [Finite G] {m : MeasurableSpace G} (ν : Measure G)
    (hH : @Measure.IsHaarMeasure G _ _ m ν) : ν.real Set.univ ≠ 0 := by
  have : CompactSpace G := Finite.compactSpace
  have : IsFiniteMeasure ν := CompactSpace.isFiniteMeasure
  exact ENNReal.toReal_ne_zero.mpr
    ⟨Measure.measure_univ_ne_zero.mpr (NeZero.ne ν), measure_ne_top ν _⟩

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.7)–(6.2.2.10), pp. 299–301. Over ℚ take S with one finite
prime p, the trivial character, the identity class representative, and x = 1. Use the finite
indicator of `pℤₚˣ` and an even nonnegative smooth compactly supported function positive at ±1
and supported away from ±p. The norm-one integral is zero since the finite support forces the
inverse real component to have absolute value p. The separate factors are both positive. -/
theorem Printed.sLocalStandardThetaTensor_factorization_false :
    ¬ Printed.sLocalStandardThetaTensor_factorization := by
  classical
  intro h
  let v : Places(ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  let S : Finset (Places(ℚ)) := {v}
  let v' : S := ⟨v, Finset.mem_singleton_self v⟩
  have : Subsingleton S :=
    ⟨fun a b ↦ Subtype.ext ((Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm)⟩
  let q : ℝ := (v.asIdeal.absNorm : ℝ)
  have hq : 2 ≤ q := by
    have h0 : v.asIdeal.absNorm ≠ 0 := fun h0 ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
    have h1 : v.asIdeal.absNorm ≠ 1 := fun h1 ↦ v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h1)
    have h2 : 2 ≤ v.asIdeal.absNorm := by omega
    have h3 := (Nat.cast_le (α := ℝ)).mpr h2
    rwa [Nat.cast_ofNat] at h3
  obtain ⟨f, hf⟩ := sLocalStandardThetaTensor_factorization_false_arch q
  have hq0 : q⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  let G : ∀ w : Places(ℚ), finitePuncturedThetaTestSpace w := fun w ↦
    (sLocalStandardThetaTensor_factorization_false_fin w q⁻¹ hq0).choose
  have hfv₀ := (sLocalStandardThetaTensor_factorization_false_fin v q⁻¹ hq0).choose_spec
  have hω := sLocalStandardThetaTensor_factorization_false_unramified S
  have hdesc := sLocalStandardThetaTensor_factorization_false_descent S hω
  have key := h ℚ S (sLocalStandardThetaTensor_factorization_false_pic S) 1 hω 1
    (fun g y _ ↦ by rw [hdesc]; rfl) (fun _ ↦ 1)
    (sLocalStandardThetaTensor_factorization_false_classes S) f (fun w ↦ G w.val) 1
  dsimp only at key
  have hL : ∀ g : Nₛ(ℚ, S), f (Multiplicative.ofAdd (g.val⁻¹ * 1).val.1) *
      (∏ w : S, (G w.val).val (Multiplicative.ofAdd ((g.val⁻¹ * 1).val.2 w))) *
      ((1 : PontryaginDual Iₛ(ℚ, S)) g.val : ℂ) = 0 := by
    intro g
    have hy : sIdeleNorm ℚ S (g.val⁻¹ * 1) = 1 := by
      rw [mul_one, map_inv, MonoidHom.mem_ker.mp g.property, inv_one]
    have hn := sLocalStandardThetaTensor_factorization_false_normSingle v _ hy
    rw [Fintype.prod_subsingleton _ v', hfv₀]
    split_ifs with hz
    · have h1 : ‖(g.val⁻¹ * 1).val.1 Rat.infinitePlace‖ = q := by
        have hz' : ‖(g.val⁻¹ * 1).val.2 ⟨v, Finset.mem_singleton_self v⟩‖ = q⁻¹ := hz
        rw [hz'] at hn
        have hq0 : q ≠ 0 := by linarith
        field_simp at hn
        linarith
      rw [hf, h1]
      simp
    · simp
  simp only [hL, integral_zero] at key
  refine absurd key (Ne.symm (mul_ne_zero ?_ ?_))
  · -- the archimedean average is a positive multiple of the norm-one mass
    let ν := sNormOneIdeleTamagawaMeasure ℚ ∅
    let c : ℂ := (((q ^ 2 - 1) * Real.exp (-1) : ℝ) : ℂ)
    refine ne_of_eq_of_ne (?_ : _ = ∑ _k : Fin (classNumber ℚ), ∫ _g, c ∂ν) ?_
    · rw [infiniteStandardThetaAverage_apply]
      refine Finset.sum_congr rfl fun k _ ↦ integral_congr_ae
        (Filter.Eventually.of_forall fun g ↦ ?_)
      dsimp only
      have hy : sIdeleNorm ℚ ∅ g.val⁻¹ = 1 := by
        rw [map_inv, MonoidHom.mem_ker.mp g.property, inv_one]
      have hn := sLocalStandardThetaTensor_factorization_false_normEmpty _ hy
      rw [hf]
      simp only [OneMemClass.coe_one, map_one, one_mul, mul_one, ← map_inv, Units.coe_map,
        PontryaginDual.one_apply, Circle.coe_one]
      rw [show ‖((RingHom.fst (InfiniteAdeleRing ℚ)
          ((w : (∅ : Finset (Places(ℚ)))) → L(ℚ, w.val))).toMonoidHom ((g.val)⁻¹ : Iₛ(ℚ, ∅)).val)
          Rat.infinitePlace‖ = 1 from hn]
      simp [c]
    · rw [integral_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Rat.classNumber_eq, one_smul]
      have : Finite Nₛ(ℚ, (∅ : Finset (Places(ℚ)))) :=
        sLocalStandardThetaTensor_factorization_false_finite
      refine smul_ne_zero ?_ ?_
      · exact sLocalStandardThetaTensor_factorization_false_mass ν
          (sNormOneIdeleTamagawaMeasure_existsUnique ℚ ∅).exists.choose_spec.1
      · refine Complex.ofReal_ne_zero.mpr (mul_ne_zero ?_ (Real.exp_pos _).ne')
        nlinarith
  · -- the finite factor is the mass of the elements of norm `q`
    rw [Fintype.prod_subsingleton _ v']
    let μ := finiteLocalMultiplicativeTamagawaMeasure ℚ v
    let T : Set (L(ℚ, v))ˣ := {g | ‖g.val‖ = q}
    have : BorelSpace (L(ℚ, v))ˣ := ⟨rfl⟩
    have hTm : MeasurableSet T :=
      (isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
    refine ne_of_eq_of_ne (?_ : _ = ∫ g, T.indicator (fun _ ↦ (1 : ℂ)) g ∂μ) ?_
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
      change (G v).val (Multiplicative.ofAdd ((g⁻¹).val * (1 : Iₛ(ℚ, S)).val.2 v')) * _ = _
      rw [Units.val_one, Prod.snd_one, Pi.one_apply, mul_one, hfv₀]
      simp only [PontryaginDual.one_apply, Circle.coe_one, mul_one, Set.indicator_apply, T,
        Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, norm_inv, inv_inj]
    · have : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := ℚ) v
      obtain ⟨π, hπ⟩ :=
        (Valued.v (R := L(ℚ, v))).exists_isUniformizer_of_isCyclic_of_nontrivial
      have hπn : ‖π‖ = q⁻¹ := norm_uniformizer_adicCompletion (K := ℚ) v π hπ
      let u : (L(ℚ, v))ˣ := Units.mk0 π hπ.ne_zero
      have hT : T = (fun h ↦ u * h) ⁻¹' ((v.adicCompletionIntegers ℚ).units : Set (L(ℚ, v))ˣ) := by
        ext h
        change ‖h.val‖ = q ↔ u * h ∈ (v.adicCompletionIntegers ℚ).units
        rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
          ← Valued.toNormedField.norm_eq_one_iff, Units.val_mul, norm_mul]
        change ‖h.val‖ = q ↔ ‖π‖ * ‖h.val‖ = 1
        rw [hπn]
        have hq0 : q ≠ 0 := by linarith
        constructor
        · intro e; rw [e, inv_mul_cancel₀ hq0]
        · intro e; field_simp at e; linarith
      rw [integral_indicator_const _ hTm, Measure.real, hT, measure_preimage_mul,
        finiteLocalMultiplicativeTamagawaMeasure_integerUnits]
      refine smul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩) one_ne_zero
      · exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
      · refine ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr ?_)).ne'
        have h0 : v.asIdeal.absNorm ≠ 0 := fun h0 ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
        positivity

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.5), p. 299. As printed: the insertion with the fixed
standard finite tests induces a linear homeomorphism from the quotient by the kernel of the
inverse-argument archimedean average (6.2.2.3) to the S-local homogeneous theta quotient. The
fixed tensor line is expressed by insertion. See `sLocalStandardThetaTensor_quotient_equiv`
and ERRATA F75. -/
def Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S)
      (χ : PontryaginDual Iₛ(F, S)),
      let ωₛ := sLocalNormOneCharacter S ω hω
      Lifts(F, S, χ, ωₛ) →
      ∀ (r : Fin (classNumber F) → Nₛ(F, S)), ClassRepresentatives(F, S, r) →
        let K := (infiniteStandardThetaAverage χ r).ker
        let c := sIdeleRestriction F S hω.choose
        ∃ e : (ℬ∞(F) ⧸ K) ≃L[ℂ] SLocalHomogeneousThetaSpace F S ωₛ,
          ∀ f : ℬ∞(F), e (K.mkQ f) = (sLocalHomogeneousAdelicThetaLinearMap F S ωₛ).ker.mkQ
            (sLocalStandardThetaTensor c f)

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.5), p. 299. Take ℚ(i) at its complex stage, the
identity representative, `χ(z) = (z/|z|)^4` and `f(z) = z^4 exp(-|z|²)`. The character kills
the four global units and extends unramified at all finite places since the class group is
trivial. The inverse-argument average at 1 is the integral of `exp(-1)` on the circle. The
homogeneous theta average uses the positive argument, so its circle integrand has weight 8
and averages to zero. The proposed map sends the resulting nonzero source class to zero. -/
theorem Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv_false :
    ¬ Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv := by sorry

/-- Paper: Theorem 6.2.2.1(2), p. 299. As printed: the archimedean operator has semi-exponential
decay in the norm coordinate. This isolates the requirement of Definition B.2.1.1 that its
unweighted logarithmic profile be Schwartz, tested on the canonical norm section. See
`infiniteStandardThetaAverage_forwardDecay`, `infiniteStandardThetaAverage_logBound` and
ERRATA F76. -/
def Printed.infiniteStandardThetaAverage_schwartz_logProfile : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S)
      (χ : PontryaginDual Iₛ(F, S)),
      Lifts(F, S, χ, sLocalNormOneCharacter S ω hω) →
      ∀ (r : Fin (classNumber F) → Nₛ(F, S)), ClassRepresentatives(F, S, r) →
      ∀ f : ℬ∞(F), ∃ φ : SchwartzMap ℝ ℂ, ∀ t : ℝ,
        let u : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (Real.exp t))
          (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos t)))
        let x := Units.map (RingHom.fst (InfiniteAdeleRing F)
          (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (canonicalIdeleNormSection F u)
        φ t = infiniteStandardThetaAverage χ r f x

private theorem infiniteStandardThetaAverage_ratGaussian : ∃ f : ℬ∞(ℚ), ∀ x : InfiniteAdeleRing ℚ,
    f (Multiplicative.ofAdd x) = (Real.exp (-Real.pi * ‖x Rat.infinitePlace‖ ^ 2) : ℂ) := by
  let e : Multiplicative (InfiniteAdeleRing ℚ) ≃ₜ* Multiplicative Rat.infinitePlace.Completion :=
    { Homeomorph.piUnique InfinitePlace.Completion with map_mul' := fun _ _ ↦ rfl }
  let s := infiniteStandardGaussian Rat.infinitePlace 1
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing ℚ))
  let : LocallyCompactSpace (Multiplicative Rat.infinitePlace.Completion) :=
    inferInstanceAs (LocallyCompactSpace Rat.infinitePlace.Completion)
  let : T2Space (Multiplicative (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (T2Space ((v : InfinitePlace ℚ) → v.Completion))
  let : T2Space (Multiplicative Rat.infinitePlace.Completion) :=
    inferInstanceAs (T2Space Rat.infinitePlace.Completion)
  refine ⟨⟨_, schwartzBruhat_mem_comp_equiv e s.property⟩, fun x ↦ ?_⟩
  change infiniteStandardGaussianValue Rat.infinitePlace 1 (x Rat.infinitePlace) = _
  have hi := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
  have hn := hi.norm_map_of_map_zero (map_zero _) (x Rat.infinitePlace)
  simp [infiniteStandardGaussianValue, Rat.isReal_infinitePlace,
    ← hn, Real.norm_eq_abs, sq_abs]

private theorem infiniteStandardThetaAverage_ratNormOne (g : Nₛ(ℚ, ∅)) :
    ‖g.val.val.1 Rat.infinitePlace‖ = 1 := by
  simpa [MonoidHom.mem_ker.mp g.property] using (rat_sIdeleNorm_eq ∅ g.val).symm

private theorem infiniteStandardThetaAverage_ratFinite : Finite Nₛ(ℚ, ∅) := by
  classical
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let c (g : Nₛ(ℚ, ∅)) := e (g.val.val.1 Rat.infinitePlace)
  have hi := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
  have hc (g : Nₛ(ℚ, ∅)) : |c g| = 1 :=
    (hi.norm_map_of_map_zero (map_zero _) _).trans (infiniteStandardThetaAverage_ratNormOne g)
  let signs : Finset ℝ := {1, -1}
  have hmem (g : Nₛ(ℚ, ∅)) : c g ∈ signs := by
    simpa [signs] using (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp (hc g)
  apply Finite.of_injective (fun g : Nₛ(ℚ, ∅) ↦ (⟨c g, hmem g⟩ : signs))
  intro g h eq
  apply Subtype.ext
  apply Units.ext
  apply Prod.ext _ (Subsingleton.elim _ _)
  funext v
  obtain rfl := Subsingleton.elim v Rat.infinitePlace
  exact e.injective (congrArg Subtype.val eq)

private theorem infiniteStandardThetaAverage_ratGaussian_apply (f : ℬ∞(ℚ))
    (hf : ∀ x : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd x) =
      (Real.exp (-Real.pi * ‖x Rat.infinitePlace‖ ^ 2) : ℂ))
    (x : (InfiniteAdeleRing ℚ)ˣ) :
    infiniteStandardThetaAverage (F := ℚ) (S := ∅) 1 (fun _ ↦ 1) f x =
      (sNormOneIdeleTamagawaMeasure ℚ ∅).real Set.univ •
        (Real.exp (-Real.pi * ‖x.val Rat.infinitePlace‖ ^ 2) : ℂ) := by
  classical
  have : Subsingleton (Fin (classNumber ℚ)) := by
    rw [Rat.classNumber_eq]
    infer_instance
  rw [infiniteStandardThetaAverage_apply, Fintype.sum_subsingleton _ ⟨0, classNumber_pos ℚ⟩,
    ← integral_const]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  simp only [Subgroup.coe_one, map_one, one_mul, PontryaginDual.one_apply, Circle.coe_one,
    mul_one, hf]
  let v := Units.map (Pi.evalRingHom InfinitePlace.Completion Rat.infinitePlace).toMonoidHom
  let a := Units.map (RingHom.fst (InfiniteAdeleRing ℚ)
    (∀ p : (∅ : Finset Places(ℚ)), L(ℚ, p.val))).toMonoidHom g.val
  have harg : ‖(a⁻¹ * x).val Rat.infinitePlace‖ = ‖x.val Rat.infinitePlace‖ := by
    change ‖(v (a⁻¹ * x)).val‖ = _
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
    change ‖g.val.val.1 Rat.infinitePlace‖⁻¹ * ‖x.val Rat.infinitePlace‖ = _
    rw [infiniteStandardThetaAverage_ratNormOne, inv_one, one_mul]
  rw [harg]

private theorem infiniteStandardThetaAverage_ratSection_norm (u : ℝ≥0ˣ) :
    ‖(canonicalIdeleNormSection ℚ u).val.1 Rat.infinitePlace‖ = (u.val : ℝ) := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding Rat.infinitePlace
  have hn := hi.norm_map_of_map_zero (map_zero _) ((canonicalIdeleNormSection ℚ u).val.1 Rat.infinitePlace)
  rw [← hn, canonicalIdeleNormSection_infinite]
  simp

/-- Paper: Theorem 6.2.2.1(2), pp. 299, 302. Over ℚ at the archimedean stage, take the
trivial character, the identity representative and the real Gaussian `exp(-πx²)`. Its unweighted
logarithmic profile is a positive constant times `exp(-π exp(2t))`, which has a nonzero limit
as t tends to negative infinity. -/
theorem Printed.infiniteStandardThetaAverage_schwartz_logProfile_false :
    ¬ Printed.infiniteStandardThetaAverage_schwartz_logProfile := by
  classical
  intro h
  have hω : NormOneCharacterUnramifiedOutside (F := ℚ) 1 ∅ :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  have hchar : sLocalNormOneCharacter (F := ℚ) ∅ 1 hω = 1 := by
    let hu := (normOneCharacterUnramifiedOutside_iff (F := ℚ) 1).mp hω
    exact hu.unique hu.exists.choose_spec (fun _ _ _ _ _ ↦ rfl)
  have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
  have hPic : Subsingleton Picₛ(ℚ, (∅ : Finset Places(ℚ))) := by
    rw [Finset.coe_empty, integer_empty]
    let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)
    let := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
    infer_instance
  have : Subsingleton (Fin (classNumber ℚ)) := by
    rw [Rat.classNumber_eq]
    infer_instance
  have : Nonempty (Fin (classNumber ℚ)) := ⟨⟨0, classNumber_pos ℚ⟩⟩
  obtain ⟨f, hf⟩ := infiniteStandardThetaAverage_ratGaussian
  obtain ⟨φ, hφ⟩ := h ℚ ∅ hPic 1 hω 1 (by simp [hchar]) (fun _ ↦ 1)
    ⟨rfl, bijective_of_subsingleton' _⟩ f
  let μ := sNormOneIdeleTamagawaMeasure ℚ ∅
  have haar := (sNormOneIdeleTamagawaMeasure_existsUnique ℚ ∅).exists.choose_spec.1
  have : Finite Nₛ(ℚ, ∅) := infiniteStandardThetaAverage_ratFinite
  have : CompactSpace Nₛ(ℚ, ∅) := Finite.compactSpace
  have hm : (μ.real Set.univ : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (ENNReal.toReal_pos (haar.open_pos Set.univ isOpen_univ Set.univ_nonempty)
      (haar.lt_top_of_isCompact isCompact_univ).ne).ne'
  have hval (t : ℝ) : φ t =
      (μ.real Set.univ : ℂ) * (Real.exp (-Real.pi * Real.exp t ^ 2) : ℂ) := by
    rw [hφ, infiniteStandardThetaAverage_ratGaussian_apply f hf]
    simp [infiniteStandardThetaAverage_ratSection_norm, Units.coe_map,
      Real.toNNReal_of_nonneg (Real.exp_pos t).le, Algebra.smul_def, μ]
  have hlim : Filter.Tendsto φ Filter.atBot (𝓝 (μ.real Set.univ : ℂ)) := by
    have hc : Continuous (fun s : ℝ ↦ (μ.real Set.univ : ℂ) *
        (Real.exp (-Real.pi * s ^ 2) : ℂ)) := by fun_prop
    rw [funext hval]
    simpa [Function.comp_def] using (hc.tendsto 0).comp Real.tendsto_exp_atBot
  exact hm (tendsto_nhds_unique hlim (φ.tendsto_cocompact.mono_left atBot_le_cocompact))

end StandardFunctions

end RiemannMasullo
