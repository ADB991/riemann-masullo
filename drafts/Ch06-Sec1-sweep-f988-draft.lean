module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Pi

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Structure Theorem IV: local within global

Masullo, §6.1, pp. 287–295. The finite sets index finite places. The
archimedean places are included in every S-adelic ring.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped CompactlySupported MonoidAlgebra NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S T : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Places" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "L(" w ")" => (HeightOneSpectrum.adicCompletion (R := 𝓞 F) F w)
local notation "ℬᵥ(" w ")" => (SchwartzBruhat (Multiplicative (L(w))))
local notation "O(" w ")" => (HeightOneSpectrum.adicCompletionIntegers (R := 𝓞 F) F w)
local notation "U(" w ")" =>
  (Submonoid.units (Subsemiring.toSubmonoid (Subring.toSubsemiring (ValuationSubring.toSubring (O(w))))))

-- TODO(paper-gap): Proposition 6.1.1.1, (6.1.1.1)–(6.1.1.2), multiplies
-- inverses of test-space endomorphisms to obtain transitions between distinct
-- quotients. On the target coinvariants every basis lift acts as the identity,
-- so the differences have no inverse. Already over ℚ, with S = {∞} and
-- S' = {∞, p}, the proposed geometric series does not converge in the target
-- quotient on a nonzero transition class. The global series has the same defect.

section Ranges

private theorem mem_ker_adeleProjection_units_iff (T : Finset (HeightOneSpectrum (𝓞 F)))
    (g : IdeleGroup (𝓞 F) F) :
    g ∈ (Units.map (adeleProjection F T).toMonoidHom).ker ↔
      g.val.1 = 1 ∧ ∀ w : T, g.val.2 w.val = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  simp only [Units.coe_map, Units.val_one]
  rw [Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w ↦ congrFun h2 w⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun w ↦ h2 w⟩

variable (F S) in
/-- Paper: (6.1.2.2), p. 288.
The complementary integral ideles are the ideles integral and invertible outside S
whose S-adelic projection is the identity.
Deviation: In (6.1.2.2) the ambient outside multiplicative factors form a restricted
product. The full product of integer units embeds in the ideles. -/
def outsideIntegralIdeleUnits : Subgroup (IdeleGroup (𝓞 F) F) :=
  (integralIdeleInsertion F S).range ⊓ (Units.map (adeleProjection F S).toMonoidHom).ker

/-- Paper: (6.1.2.2), p. 288.
An idele belongs to the complementary group exactly when its archimedean and S coordinates
are one and its other coordinates are local integer units. -/
theorem mem_outsideIntegralIdeleUnits_iff (g : IdeleGroup (𝓞 F) F) :
    g ∈ outsideIntegralIdeleUnits F S ↔
      g.val.1 = 1 ∧ (∀ w ∈ S, g.val.2 w = 1) ∧
        ∀ w ∉ S, g.val.2 w ∈ O(w) ∧ (g⁻¹).val.2 w ∈ O(w) := by
  unfold outsideIntegralIdeleUnits
  rw [Subgroup.mem_inf, mem_ker_adeleProjection_units_iff,
    show g ∈ (integralIdeleInsertion F S).range ↔ g ∈ Set.range (integralIdeleInsertion F S) from
      Iff.rfl,
    mem_range_integralIdeleInsertion]
  constructor
  · rintro ⟨h2, h1, h3⟩
    exact ⟨h1, fun w hw ↦ h3 ⟨w, hw⟩, h2⟩
  · rintro ⟨h1, h3, h2⟩
    exact ⟨h2, h1, fun w ↦ h3 w.1 w.2⟩

variable (F S T) in
/-- Paper: (6.1.2.1), p. 288.
Projecting the complementary integral ideles to T inserts the integer units at T minus S.
Deviation: The insertion lands in the T-ideles, as required by Theorem 6.1.2.1(1). -/
def relativeIntegralIdeleUnits : Subgroup (SAdeleRing F T)ˣ :=
  (outsideIntegralIdeleUnits F S).map (Units.map (adeleProjection F T).toMonoidHom)

/-- Paper: (6.1.2.1), p. 288.
The relative group has identity coordinates on the archimedean factor and S, and
arbitrary integer-unit coordinates on T minus S. -/
theorem mem_relativeIntegralIdeleUnits_iff (g : (SAdeleRing F T)ˣ) :
    g ∈ relativeIntegralIdeleUnits F S T ↔
      g.val.1 = 1 ∧ (∀ w : T, w.val ∈ S → g.val.2 w = 1) ∧
        ∀ w : T, w.val ∉ S → g.val.2 w ∈ O(w.val) ∧ (g⁻¹).val.2 w ∈ O(w.val) := by
  classical
  unfold relativeIntegralIdeleUnits
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (mem_outsideIntegralIdeleUnits_iff h).1 hh
    refine ⟨h1, fun w hw ↦ h2 w.val hw, fun w hw ↦ h3 w.val hw⟩
  · rintro ⟨h1, h2, h3⟩
    let e (x : (w : T) → HeightOneSpectrum.adicCompletion F w.val) :
        RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) ↦ HeightOneSpectrum.adicCompletion F w)
          (fun w ↦ HeightOneSpectrum.adicCompletionIntegers F w) Filter.cofinite :=
      RestrictedProduct.mk
        (fun w : HeightOneSpectrum (𝓞 F) ↦ if hw : w ∈ T then x ⟨w, hw⟩ else 1)
        (by
          filter_upwards [T.eventually_cofinite_notMem] with w hw
          simp only [hw, dite_false]
          exact one_mem _)
    have he (x) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∈ T) : e x w = x ⟨w, hw⟩ := by
      exact dif_pos hw
    have he' (x) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ T) : e x w = 1 := by
      exact dif_neg hw
    have hmul : ∀ w : T, g.val.2 w * (g⁻¹).val.2 w = 1 := fun w ↦
      congrFun (congrArg Prod.snd g.val_inv) w
    have hmul' : ∀ w : T, (g⁻¹).val.2 w * g.val.2 w = 1 := fun w ↦
      congrFun (congrArg Prod.snd g.inv_val) w
    have hm1 : e g.val.2 * e (g⁻¹).val.2 = 1 := Subtype.ext (funext fun w ↦ by
      by_cases hw : w ∈ T
      · change e _ w * e _ w = 1
        rw [he _ _ hw, he _ _ hw]; exact hmul ⟨w, hw⟩
      · change e _ w * e _ w = 1
        rw [he' _ _ hw, he' _ _ hw]; exact mul_one _)
    have hm2 : e (g⁻¹).val.2 * e g.val.2 = 1 := Subtype.ext (funext fun w ↦ by
      by_cases hw : w ∈ T
      · change e _ w * e _ w = 1
        rw [he _ _ hw, he _ _ hw]; exact hmul' ⟨w, hw⟩
      · change e _ w * e _ w = 1
        rw [he' _ _ hw, he' _ _ hw]; exact mul_one _)
    let h : IdeleGroup (𝓞 F) F :=
      ⟨(1, e g.val.2), (1, e (g⁻¹).val.2), Prod.ext (mul_one 1) hm1, Prod.ext (mul_one 1) hm2⟩
    refine ⟨h, ?_, ?_⟩
    · rw [mem_outsideIntegralIdeleUnits_iff]
      refine ⟨rfl, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · by_cases hT : w ∈ T
        · exact (he _ _ hT).trans (h2 ⟨w, hT⟩ hw)
        · exact he' _ _ hT
      · by_cases hT : w ∈ T
        · exact ⟨(he _ _ hT).symm ▸ (h3 ⟨w, hT⟩ hw).1, (he _ _ hT).symm ▸ (h3 ⟨w, hT⟩ hw).2⟩
        · exact ⟨(he' _ _ hT).symm ▸ one_mem _, (he' _ _ hT).symm ▸ one_mem _⟩
    · refine Units.ext (Prod.ext h1.symm (funext fun w ↦ ?_))
      exact he _ _ w.2

open scoped RestrictedProduct in
/-- The local integer rings form a compact subset of the finite adeles. -/
private theorem outsideIntegralIdeleUnits_isCompact_integral :
    IsCompact {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} := by
  let K := fun v : Places ↦ v.adicCompletion F
  let O := fun v : Places ↦ (v.adicCompletionIntegers F : Set (K v))
  have (v : Places) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let j : (∀ v : Places, v.adicCompletionIntegers F) → Πʳ v, [K v, O v]_[Filter.principal Set.univ] :=
    fun x ↦ ⟨fun v ↦ x v, Filter.Eventually.of_forall fun v ↦ (x v).property⟩
  let i := RestrictedProduct.inclusion K O
    (show Filter.cofinite ≤ Filter.principal (Set.univ : Set Places) by simp)
  have hj : Continuous j := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi fun v ↦ continuous_subtype_val.comp (continuous_apply v))
  have hc := isCompact_range ((RestrictedProduct.continuous_inclusion _).comp hj :
    Continuous (i ∘ j))
  have h : Set.range (i ∘ j) =
      {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
    apply Set.ext
    intro a
    exact ⟨fun ⟨x, hx⟩ v ↦ hx ▸ (x v).property,
      fun ha ↦ ⟨fun v ↦ ⟨a v, ha v⟩, rfl⟩⟩
  rwa [← h]

/-- Paper: (6.1.2.2), p. 288.
The group of integral idelic units outside S is compact in the global ideles. -/
theorem outsideIntegralIdeleUnits_isCompact :
    IsCompact (outsideIntegralIdeleUnits F S : Set (IdeleGroup (𝓞 F) F)) := by
  classical
  let K : Submonoid (AdeleRing (𝓞 F) F) :=
    { carrier := {a | a.1 = 1 ∧ (∀ w ∈ S, a.2 w = 1) ∧ ∀ w, a.2 w ∈ O(w)}
      mul_mem' := fun {a b} ha hb ↦ ⟨by rw [Prod.fst_mul, ha.1, hb.1, one_mul],
        fun w hw ↦ by
          change a.2 w * b.2 w = 1
          rw [ha.2.1 w hw, hb.2.1 w hw, one_mul],
        fun w ↦ by
          change a.2 w * b.2 w ∈ O(w)
          exact mul_mem (ha.2.2 w) (hb.2.2 w)⟩
      one_mem' := ⟨rfl, fun _ _ ↦ rfl, fun w ↦ one_mem (O(w))⟩ }
  have hK : IsCompact (K : Set (AdeleRing (𝓞 F) F)) := by
    have hcl : IsClosed {a : FiniteAdeleRing (𝓞 F) F | ∀ w ∈ S, a w = 1} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun w ↦ isClosed_iInter fun _ ↦
        isClosed_eq (RestrictedProduct.continuous_eval w) continuous_const
    have h1 := (isCompact_singleton (x := (1 : InfiniteAdeleRing F))).prod
      (outsideIntegralIdeleUnits_isCompact_integral.inter_right hcl)
    have he : (K : Set (AdeleRing (𝓞 F) F)) = ({1} : Set (InfiniteAdeleRing F)) ×ˢ
        ({a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} ∩
          {a : FiniteAdeleRing (𝓞 F) F | ∀ w ∈ S, a w = 1}) := by
      ext a
      change (a.1 = 1 ∧ (∀ w ∈ S, a.2 w = 1) ∧ ∀ w, a.2 w ∈ O(w)) ↔
        a.1 = 1 ∧ ((∀ v, a.2 v ∈ O(v)) ∧ ∀ w ∈ S, a.2 w = 1)
      tauto
    exact he ▸ h1
  have hinv (g : IdeleGroup (𝓞 F) F) : (g⁻¹).val * g.val = 1 := Units.inv_mul g
  have heq : (outsideIntegralIdeleUnits F S : Set (IdeleGroup (𝓞 F) F)) = K.units := by
    ext g
    rw [SetLike.mem_coe, mem_outsideIntegralIdeleUnits_iff, SetLike.mem_coe,
      Submonoid.mem_units_iff]
    have h1 := congrArg Prod.fst (hinv g)
    have h2 := fun w ↦ congrFun (congrArg (fun a : AdeleRing (𝓞 F) F ↦ ⇑a.2) (hinv g)) w
    change (g⁻¹).val.1 * g.val.1 = 1 at h1
    change ∀ w, (g⁻¹).val.2 w * g.val.2 w = 1 at h2
    constructor
    · rintro ⟨ha, hS, hO⟩
      refine ⟨⟨ha, hS, fun w ↦ ?_⟩, ⟨?_, fun w hw ↦ ?_, fun w ↦ ?_⟩⟩
      · by_cases hw : w ∈ S
        · rw [hS w hw]; exact one_mem _
        · exact (hO w hw).1
      · rwa [ha, mul_one] at h1
      · have := h2 w
        rwa [hS w hw, mul_one] at this
      · by_cases hw : w ∈ S
        · have := h2 w
          rw [hS w hw, mul_one] at this
          change (g⁻¹).val.2 w ∈ O(w)
          rw [this]; exact one_mem _
        · exact (hO w hw).2
    · rintro ⟨⟨ha, hS, hO⟩, ⟨_, _, hO'⟩⟩
      exact ⟨ha, hS, fun w _ ↦ ⟨hO w, hO' w⟩⟩
  rw [heq]
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous
      (f := fun a : FiniteAdeleRing (𝓞 F) F ↦ (⇑a : ∀ v : Places, v.adicCompletion F))
      (fun _ _ h ↦ Subtype.ext h) (continuous_pi fun v ↦ RestrictedProduct.continuous_eval v)
  have : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  have : T2Space (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  exact Submonoid.units_isCompact hK

/-- Paper: (6.1.2.1), p. 288.
The group of integer units inserted at the additional finite places is compact in the T-ideles. -/
theorem relativeIntegralIdeleUnits_isCompact :
    IsCompact (relativeIntegralIdeleUnits F S T : Set (SAdeleRing F T)ˣ) := by
  classical
  let H (v : T) : Set (L(v.val))ˣ := if v.val ∈ S then {1} else U(v.val)
  have hc (v : T) : IsCompact (H v) := by
    by_cases hv : v.val ∈ S
    · simpa only [H, ite_eq_left hv] using (isCompact_singleton (x := (1 : (L(v.val))ˣ)))
    · have hO : IsCompact (O(v.val) : Set (L(v.val))) :=
        isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v.val)
      simpa only [H, ite_eq_right hv] using Submonoid.units_isCompact hO
  have memH (v : T) (u : (L(v.val))ˣ) : u ∈ H v ↔
      (v.val ∈ S → u.val = 1) ∧
        (v.val ∉ S → u.val ∈ O(v.val) ∧ (u⁻¹).val ∈ O(v.val)) := by
    by_cases hv : v.val ∈ S
    · simp only [H, ite_eq_left hv, Set.mem_singleton_iff]
      exact ⟨fun h ↦ ⟨fun _ ↦ congrArg Units.val h, fun hn ↦ (hn hv).elim⟩, fun h ↦ Units.ext (h.1 hv)⟩
    · simp only [H, ite_eq_right hv]
      exact ⟨fun h ↦ ⟨fun hs ↦ (hv hs).elim, fun _ ↦ h⟩, fun h ↦ h.2 hv⟩
  let p := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((v : T) → L(v.val))
  let q := ContinuousMulEquiv.piUnits (M := fun v : T ↦ L(v.val))
  let e := p.toHomeomorph.trans ((Homeomorph.refl _).prodCongr q.toHomeomorph)
  have he : (relativeIntegralIdeleUnits F S T : Set (SAdeleRing F T)ˣ) =
      e ⁻¹' (({1} : Set (InfiniteAdeleRing F)ˣ) ×ˢ Set.univ.pi H) := by
    ext g
    refine (mem_relativeIntegralIdeleUnits_iff (F := F) (S := S) (T := T) g).trans ?_
    change _ ↔ (p g).1 ∈ ({1} : Set (InfiniteAdeleRing F)ˣ) ∧ q (p g).2 ∈ Set.univ.pi H
    rw [Set.mem_singleton_iff, Units.ext_iff, Set.mem_univ_pi]
    refine and_congr_right fun _ ↦ ?_
    simp_rw [memH]
    exact ⟨fun ⟨hs, hd⟩ v ↦ ⟨hs v, hd v⟩, fun h ↦ ⟨fun v ↦ (h v).1, fun v ↦ (h v).2⟩⟩
  exact (congrArg IsCompact he).mpr (e.isCompact_preimage.mpr
    (isCompact_singleton.prod (isCompact_univ_pi hc)))

-- TODO(paper-gap): The proof of Theorem 6.1.2.1 applies its invariant-space
-- tensor identification to the full test space and has mismatched indices
-- in (6.1.2.21). The argument on pp. 294–295 assumes convergent Cauchy nets
-- have bounded tails in the strict LF topology. Equation (5.1.1.3) defines the
-- two theta spaces as quotients by the theta kernels. Remark 5.2.3.4 concerns
-- the separate comparison with closures of principal translation differences.

/-- Paper: Theorem 6.1.2.1(1), p. 288.
When the S-integers have trivial Picard group, the range of the transition is the fixed
subspace for the relative integral units in the T-local theta quotient of (5.1.1.3). -/
theorem sLocalThetaTransition_range_eq_invariants (hST : S ⊂ T)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F))) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    Set.range (sLocalThetaTransition (F := F) hST.le) =
      {x : Θₛ(T) | ∀ g : relativeIntegralIdeleUnits F S T,
        ρ (QuotientGroup.mk g.val) x = x} := by sorry

/-- Paper: Theorem 6.1.2.1(2), p. 288.
When the S-integers have trivial Picard group, the range of the global insertion is the fixed
subspace for the complementary integral units in the global theta quotient of (5.1.1.3). -/
theorem sLocalThetaToGlobal_range_eq_invariants
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F))) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    Set.range (sLocalThetaToGlobal F S) =
      {x : Θ𝔽 | ∀ g : outsideIntegralIdeleUnits F S, ρ (QuotientGroup.mk g.val) x = x} := by sorry

end Ranges

section UnitRepresentation

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "translate" => fun (g : Rˣ) ↦
  ((LinearMap.funLeft ℂ ℂ (fun x : Multiplicative R ↦
    Multiplicative.ofAdd ((g⁻¹ : Rˣ).val * x.toAdd))).comp
    (schwartzBruhatSubmodule (Multiplicative R)).subtype).codRestrict
      (schwartzBruhatSubmodule (Multiplicative R)) (schwartzBruhat_unitTranslate_mem g)

/-- Paper: Remark 6.1.2.3, p. 289.
The identity unit acts by the identity on the additive Schwartz–Bruhat space. -/
theorem schwartzBruhatUnitRepresentation_map_one :
    translate (1 : Rˣ) = (1 : Module.End ℂ ℬ(R)) := by
  refine LinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦ ?_)
  simp
  rfl

/-- Paper: Remark 6.1.2.3, p. 289.
Pullback by the inverse of a product agrees with the composition of the two translations. -/
theorem schwartzBruhatUnitRepresentation_map_mul (g h : Rˣ) :
    translate (g * h) = (translate g : Module.End ℂ ℬ(R)) * translate h := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change f.val (Multiplicative.ofAdd (((g * h)⁻¹ : Rˣ).val * x.toAdd)) =
    f.val (Multiplicative.ofAdd ((h⁻¹ : Rˣ).val * ((g⁻¹ : Rˣ).val * x.toAdd)))
  rw [mul_inv_rev, Units.val_mul, mul_assoc]

/-- Paper: Remark 6.1.2.3, p. 289.
The inverse-multiplication pullback action on additive Schwartz–Bruhat functions,
bundled as a complex linear representation of the unit group. -/
def schwartzBruhatUnitRepresentation : Representation ℂ Rˣ ℬ(R) where
  toFun := translate
  map_one' := schwartzBruhatUnitRepresentation_map_one
  map_mul' := schwartzBruhatUnitRepresentation_map_mul

/-- Paper: Remark 6.1.2.3, p. 289.
The bundled representation acts by the existing left-translation operator. -/
theorem schwartzBruhatUnitRepresentation_apply (g : Rˣ) (f : ℬ(R)) :
    schwartzBruhatUnitRepresentation (R := R) g f = schwartzBruhatUnitTranslate g f := by
  rfl

end UnitRepresentation

local notation "ρ(" w ")" =>
  (schwartzBruhatUnitRepresentation (R := L(w))).comp
    (Subgroup.subtype (U(w)))

section Laurent

open scoped ENNReal in
/-- Point evaluation is continuous in the Schwartz–Bruhat topology since its
norm is bounded on each stage by the zeroth Schwartz seminorm. -/
private theorem schwartzBruhat_eval_continuous {G : Type*} [CommGroup G] [TopologicalSpace G]
    (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let _ := e.finiteGroup
    let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e))
    refine Seminorm.continuous_of_le hq ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ q f
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f y‖₊ : ℝ≥0∞).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      refine ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne ?_
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖f z‖₊ : ℝ≥0∞)) y
    · simpa only [norm_zero] using apply_nonneg q f
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hstage⟩

private theorem unitInvariants_isClosed {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (H : Subgroup Rˣ) :
    IsClosed (SetLike.coe (Representation.invariants
      ((schwartzBruhatUnitRepresentation (R := R)).comp H.subtype)) : Set ℬ(R)) := by
  have : (SetLike.coe (Representation.invariants
      ((schwartzBruhatUnitRepresentation (R := R)).comp H.subtype)) : Set ℬ(R)) =
      ⋂ g : H, ⋂ x : R, {f | f (Multiplicative.ofAdd (((g⁻¹ : H) : Rˣ).val * x)) =
        f (Multiplicative.ofAdd x)} := by
    ext f
    simp only [SetLike.mem_coe, Representation.mem_invariants, Set.mem_iInter, Set.mem_setOf_eq]
    refine forall_congr' fun g ↦ ?_
    constructor
    · intro h x
      exact congrArg (fun φ : ℬ(R) ↦ φ.val (Multiplicative.ofAdd x)) h
    · intro h
      exact Subtype.ext (funext fun x ↦ h x.toAdd)
  rw [this]
  exact isClosed_iInter fun g ↦ isClosed_iInter fun x ↦
    isClosed_eq (schwartzBruhat_eval_continuous (Multiplicative.ofAdd _))
      (schwartzBruhat_eval_continuous (Multiplicative.ofAdd _))

open Classical in
/-- Paper: Lemma 6.1.2.2(1), p. 288.
The monomial of exponent n corresponds to the indicator of the integral ball
scaled by the n-th power of the uniformizer. -/
def finitePlaceBallIndicator (w : Places) (π : (L(w))ˣ) (n : ℤ)
    (x : L(w)) : ℂ :=
  (O(w) : Set L(w)).indicator (fun _ ↦ (1 : ℂ)) ((π ^ (-n)).val * x)

/-- Paper: Lemma 6.1.2.2(1), p. 288.
The translated ball contains the m-th uniformizer power exactly when m is at least its
defining exponent n. -/
theorem finitePlaceBallIndicator_at_power (w : Places) (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val)
    (m n : ℤ) :
    finitePlaceBallIndicator w π n (π ^ m).val = (if n ≤ m then 1 else 0) := by
  have hv : Valued.v (π.val) = (WithZero.exp (-1 : ℤ)) := _hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (w.valuedAdicCompletion_surjective F)))
  have h1 : (π ^ (-n)).val * (π ^ m).val = ((π ^ (m - n)).val) := by
    rw [← Units.val_mul, ← zpow_add]; congr 2; ring
  have h2 : Valued.v ((π ^ (m - n)).val) = WithZero.exp (-(m - n)) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hv, ← WithZero.exp_zsmul]; simp
  unfold finitePlaceBallIndicator
  rw [h1]
  by_cases h : n ≤ m
  · rw [if_pos h, Set.indicator_of_mem]
    show _ ∈ O(w)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, h2]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  · rw [if_neg h, Set.indicator_of_notMem]
    show _ ∉ O(w)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, h2]
    rw [not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega


/-- Evaluation at a point is a linear functional on Schwartz–Bruhat functions. -/
private theorem finitePlaceSchwartz_invariants_laurent_eval {G : Type*} [CommGroup G]
    [TopologicalSpace G] (y : G) : ∃ L : SchwartzBruhat G →ₗ[ℂ] ℂ, ∀ f, L f = f y :=
  ⟨(LinearMap.proj y).comp (schwartzBruhatSubmodule G).subtype, fun _ ↦ rfl⟩

/-- The local Schwartz–Bruhat space is Hausdorff. -/
private theorem finitePlaceSchwartz_invariants_laurent_t2 (w : Places) : T2Space ℬᵥ(w) := by
  exact (congrArg (fun t ↦ @T2Space ℬᵥ(w) t) (finitePlaceSchwartz_finestTopology (F := F) w)).mpr
    (finestLocallyConvex_t2 (schwartzBruhatSubmodule (Multiplicative (L(w)))))

/-- Every linear map out of the local Schwartz–Bruhat space into a Hausdorff locally convex
space is continuous, since its topology is the finest locally convex one. -/
private theorem finitePlaceSchwartz_invariants_laurent_continuous (w : Places) {M : Type*}
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M] [PolynormableSpace ℂ M] [T2Space M]
    (T : ℬᵥ(w) →ₗ[ℂ] M) : Continuous T := by
  exact (congrArg (fun t ↦ @Continuous ℬᵥ(w) M t _ T)
    (finitePlaceSchwartz_finestTopology (F := F) w)).mpr
    (continuous_of_finestLocallyConvex (schwartzBruhatSubmodule (Multiplicative (L(w)))) (M := M) T)

/-- The integer-ball indicators are local Schwartz–Bruhat functions. -/
private theorem finitePlaceSchwartz_invariants_laurent_ball (w : Places) (π : (L(w))ˣ) (n : ℤ) :
    ∃ g : ℬᵥ(w), ∀ x, g (Multiplicative.ofAdd x) = finitePlaceBallIndicator w π n x := by
  have hO : IsClopen (O(w) : Set L(w)) := Valued.isClopen_valuationSubring _
  let a := Homeomorph.mulLeft₀ ((π ^ (-n)).val) (π ^ (-n)).ne_zero
  refine (mem_finitePlaceSchwartz_iff (F := F) w _).2 ⟨?_, ?_⟩
  · have hlc : IsLocallyConstant ((O(w) : Set L(w)).indicator (fun _ ↦ (1 : ℂ))) := by
      refine (IsLocallyConstant.iff_exists_open _).2 fun x ↦ ?_
      by_cases hx : x ∈ (O(w) : Set L(w))
      · exact ⟨_, hO.isOpen, hx, fun y hy ↦ by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
      · exact ⟨_, hO.isClosed.isOpen_compl, hx, fun y hy ↦ by
          rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
    exact hlc.comp_continuous a.continuous
  · have hc : IsCompact (a ⁻¹' (O(w) : Set L(w))) :=
      a.isCompact_preimage.2 (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w))
    exact HasCompactSupport.intro hc fun x hx ↦ by
      unfold finitePlaceBallIndicator
      exact Set.indicator_of_notMem hx (fun _ ↦ (1 : ℂ))

/-- Integer-unit dilation preserves the integer-ball indicators. -/
private theorem finitePlaceSchwartz_invariants_laurent_ball_unit (w : Places) (π : (L(w))ˣ)
    (n : ℤ) {u : (L(w))ˣ} (hu : u ∈ U(w)) (x : L(w)) :
    finitePlaceBallIndicator w π n (u.val * x) = finitePlaceBallIndicator w π n x := by
  have hiff : ∀ y : L(w), u.val * y ∈ O(w) ↔ y ∈ O(w) := fun y ↦ ⟨fun h ↦ by
      have := mul_mem ((Submonoid.mem_units_iff _ _).1 hu).2 h
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this,
    fun h ↦ mul_mem ((Submonoid.mem_units_iff _ _).1 hu).1 h⟩
  unfold finitePlaceBallIndicator
  rw [mul_left_comm]
  by_cases h : (π ^ (-n)).val * x ∈ O(w)
  · rw [Set.indicator_of_mem (show _ ∈ (O(w) : Set L(w)) from (hiff _).2 h),
      Set.indicator_of_mem (show _ ∈ (O(w) : Set L(w)) from h)]
  · rw [Set.indicator_of_notMem (show _ ∉ (O(w) : Set L(w)) from mt (hiff _).1 h),
      Set.indicator_of_notMem (show _ ∉ (O(w) : Set L(w)) from h)]

/-- Every nonzero element is an integer unit times a power of the uniformizer. -/
private theorem finitePlaceSchwartz_invariants_laurent_decomp (w : Places) (π : (L(w))ˣ)
    (hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val)
    (x : L(w)) (hx : x ≠ 0) : ∃ (m : ℤ) (u : (L(w))ˣ), u ∈ U(w) ∧ x = u.val * (π ^ m).val := by
  have hv : Valued.v (π.val) = (WithZero.exp (-1 : ℤ)) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (w.valuedAdicCompletion_surjective F)))
  have hpow (n : ℤ) : Valued.v ((π ^ n).val) = WithZero.exp (-n) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hv, ← WithZero.exp_zsmul]; simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v x = WithZero.exp k :=
    ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm⟩
  refine ⟨-k, Units.mk0 x hx * (π ^ (-k))⁻¹, ?_, ?_⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one, Units.val_mul,
      map_mul, Units.val_mk0, hk, ← zpow_neg, neg_neg, Units.val_zpow_eq_zpow_val, map_zpow₀, hv,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  · have hne : (π.val ^ k) ≠ 0 := zpow_ne_zero k π.ne_zero
    simp [mul_assoc, hne]

/-- Each unit-invariant local test function is a finite combination of integer-ball
indicators and differences of consecutive ones. -/
private theorem finitePlaceSchwartz_invariants_laurent_span (w : Places) (π : (L(w))ˣ)
    (hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val)
    (h : ℬᵥ(w)) (hh : h ∈ Representation.invariants (ρ(w))) :
    ∃ (c : ℂ) (N : ℤ) (s : Finset ℤ) (a : ℤ → ℂ), ∀ x, h (Multiplicative.ofAdd x) =
      c * finitePlaceBallIndicator w π N x +
        ∑ n ∈ s, a n * (finitePlaceBallIndicator w π n x - finitePlaceBallIndicator w π (n + 1) x) := by
  classical
  let k : L(w) → ℂ := fun x ↦ h (Multiplicative.ofAdd x)
  have hinv : ∀ u ∈ U(w), ∀ x, k (u.val * x) = k x := by
    intro u hu x
    have := congrArg (fun φ : ℬᵥ(w) ↦ φ (Multiplicative.ofAdd x))
      ((Representation.mem_invariants _ _).1 hh ⟨u⁻¹, (U(w)).inv_mem hu⟩)
    change h (Multiplicative.ofAdd ((↑(u⁻¹)⁻¹ : L(w)) * x)) = _ at this
    rwa [inv_inv] at this
  obtain ⟨hl, hc⟩ := (mem_finitePlaceSchwartz_iff (F := F) w k).1 ⟨h, fun _ ↦ rfl⟩
  have hv : Valued.v (π.val) = (WithZero.exp (-1 : ℤ)) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (w.valuedAdicCompletion_surjective F)))
  let r : ℝ := ‖π.val‖
  have hr0 : 0 < r := norm_pos_iff.2 π.ne_zero
  have hr1 : r < 1 := by
    change ‖π.val‖ < 1
    rw [Valued.toNormedField.norm_lt_one_iff, hv]
    exact WithZero.exp_lt_exp.2 (by norm_num)
  have hnorm (n : ℤ) : ‖(π ^ n).val‖ = r ^ n := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow]
  -- small powers: the support is bounded
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn continuous_norm.continuousOn
  obtain ⟨n₁, hn₁⟩ := pow_unbounded_of_one_lt R (one_lt_inv₀ hr0 |>.2 hr1)
  have hlow : ∀ m : ℤ, m < -(n₁ : ℤ) → k ((π ^ m).val) = 0 := by
    intro m hm
    by_contra hne
    have h1 := hR _ (subset_tsupport k hne)
    rw [hnorm, Real.norm_of_nonneg (zpow_pos hr0 m).le] at h1
    have h2 : r⁻¹ ^ (n₁ : ℤ) ≤ r⁻¹ ^ (-m) :=
      zpow_le_zpow_right₀ (one_lt_inv₀ hr0 |>.2 hr1).le (by omega)
    rw [zpow_natCast, inv_zpow', neg_neg] at h2
    linarith
  -- large powers: local constancy at zero
  obtain ⟨ε, hε, hεk⟩ := Metric.eventually_nhds_iff.1 (hl.eventually_eq 0)
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hε hr1
  have hhigh : ∀ m : ℤ, (n₀ : ℤ) ≤ m → k ((π ^ m).val) = k 0 := by
    intro m hm
    apply hεk
    rw [dist_zero_right, hnorm]
    calc r ^ m ≤ r ^ (n₀ : ℤ) := zpow_le_zpow_right_of_le_one₀ hr0 hr1.le hm
      _ = r ^ n₀ := zpow_natCast r n₀
      _ < ε := hn₀
  have hball0 (n : ℤ) : finitePlaceBallIndicator w π n 0 = 1 := by
    unfold finitePlaceBallIndicator
    rw [mul_zero, Set.indicator_of_mem (show (0 : L(w)) ∈ (O(w) : Set L(w)) from zero_mem _)]
  refine ⟨k 0, n₀, Finset.Ico (-(n₁ : ℤ)) n₀, fun n ↦ k ((π ^ n).val), fun x ↦ ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp only [hball0, sub_self, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
    rfl
  obtain ⟨m, u, hu, rfl⟩ := finitePlaceSchwartz_invariants_laurent_decomp w π hπ x hx
  change k _ = _
  rw [hinv u hu]
  simp only [finitePlaceSchwartz_invariants_laurent_ball_unit w π _ hu,
    finitePlaceBallIndicator_at_power w π hπ]
  have hsum : ∑ n ∈ Finset.Ico (-(n₁ : ℤ)) (n₀ : ℤ), k ((π ^ n).val) *
      ((if n ≤ m then (1 : ℂ) else 0) - if n + 1 ≤ m then 1 else 0) =
      ∑ n ∈ Finset.Ico (-(n₁ : ℤ)) (n₀ : ℤ), if m = n then k ((π ^ n).val) else 0 := by
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    by_cases h1 : m = n
    · subst h1; simp
    · rw [if_neg h1]
      by_cases h2 : n ≤ m
      · rw [if_pos h2, if_pos (by omega)]; ring
      · rw [if_neg h2, if_neg (by omega)]; ring
  rw [hsum, Finset.sum_ite_eq]
  by_cases hm : (n₀ : ℤ) ≤ m
  · rw [if_pos hm, if_neg (by simp; omega), hhigh m hm]; ring
  · rw [if_neg hm]
    by_cases hm' : -(n₁ : ℤ) ≤ m
    · rw [if_pos (by simp; omega)]; ring
    · rw [if_neg (by simp; omega), hlow m (by omega)]; ring

/-- The integer-ball indicators give a linear equivalence of the Laurent polynomials with
the integer-unit invariants, sending each monomial to the matching ball indicator. -/
private theorem finitePlaceSchwartz_invariants_laurent_exists (w : Places) (π : (L(w))ˣ)
    (hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    ∃ e : LaurentPolynomial ℂ ≃ₗ[ℂ] (Representation.invariants (ρ(w))),
      ∀ n x, (e (LaurentPolynomial.T n)).val (Multiplicative.ofAdd x) =
        finitePlaceBallIndicator w π n x := by
  classical
  choose B hB using finitePlaceSchwartz_invariants_laurent_ball w π
  have hext (a b : ℬᵥ(w)) (h : ∀ x, a (Multiplicative.ofAdd x) = b (Multiplicative.ofAdd x)) :
      a = b := Subtype.ext (funext fun x ↦ h x.toAdd)
  have key : ∃ Φ : LaurentPolynomial ℂ →ₗ[ℂ] ℬᵥ(w),
      (∀ n, Φ (LaurentPolynomial.T n) = B n) ∧
        ∀ p, Φ p = ∑ n ∈ p.coeff.support, p.coeff n • B n :=
    ⟨Finsupp.linearCombination ℂ B ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap,
      fun n ↦ by
        change Finsupp.linearCombination ℂ B (Finsupp.single n 1) = B n
        rewrite [Finsupp.linearCombination_single, one_smul],
      fun p ↦ rfl⟩
  choose Φ hΦT hΦsum using key
  have hBinv (n : ℤ) : B n ∈ Representation.invariants (ρ(w)) :=
    (Representation.mem_invariants _ _).2 fun g ↦ hext _ _ fun x ↦ by
      change (B n) (Multiplicative.ofAdd ((↑(g.val)⁻¹ : L(w)) * x)) = _
      rewrite [hB, hB, finitePlaceSchwartz_invariants_laurent_ball_unit w π n ((U(w)).inv_mem g.2)]
  have hΦinv (p : LaurentPolynomial ℂ) : Φ p ∈ Representation.invariants (ρ(w)) := by
    have hs : ∑ n ∈ p.coeff.support, p.coeff n • B n ∈ Representation.invariants (ρ(w)) :=
      Submodule.sum_mem (Representation.invariants (ρ(w)))
        (fun n _ ↦ Submodule.smul_mem (Representation.invariants (ρ(w))) (p.coeff n) (hBinv n))
    exact (congrArg (· ∈ Representation.invariants (ρ(w))) (hΦsum p)).mpr hs
  have hΦev (p : LaurentPolynomial ℂ) (x : L(w)) : Φ p (Multiplicative.ofAdd x) =
      ∑ n ∈ p.coeff.support, p.coeff n * finitePlaceBallIndicator w π n x := by
    rewrite [hΦsum]
    change (∑ n ∈ p.coeff.support, (p.coeff n • B n : schwartzBruhatSubmodule _)).val _ = _
    rewrite [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rewrite [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg (p.coeff n * ·) (hB n x)
  have hinj : Function.Injective Φ := by
    rewrite [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have hz (x : L(w)) : Φ p (Multiplicative.ofAdd x) = 0 := by rewrite [hp]; rfl
    have hcoeff (m : ℤ) : p.coeff m = 0 := by
      have h1 := hz (π ^ m).val
      have h2 := hz (π ^ (m - 1)).val
      rewrite [hΦev] at h1 h2
      simp only [finitePlaceBallIndicator_at_power w π hπ] at h1 h2
      have h3 : ∑ n ∈ p.coeff.support, p.coeff n * ((if n ≤ m then (1 : ℂ) else 0) -
          if n ≤ m - 1 then 1 else 0) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]
      have h4 : ∑ n ∈ p.coeff.support, p.coeff n * ((if n ≤ m then (1 : ℂ) else 0) -
          if n ≤ m - 1 then 1 else 0) = ∑ n ∈ p.coeff.support, if m = n then p.coeff n else 0 := by
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        by_cases h1 : m = n
        · subst h1; simp
        · rewrite [if_neg h1]
          by_cases h2 : n ≤ m
          · rewrite [if_pos h2, if_pos (by omega)]; ring
          · rewrite [if_neg h2, if_neg (by omega)]; ring
      rewrite [h4, Finset.sum_ite_eq] at h3
      split_ifs at h3 with hm
      · exact h3
      · exact Finsupp.notMem_support_iff.1 hm
    exact AddMonoidAlgebra.ext fun m ↦ hcoeff m
  have hsurj : Function.Surjective (Φ.codRestrict _ hΦinv) := by
    intro h
    choose c N s a hcs using finitePlaceSchwartz_invariants_laurent_span w π hπ h.val h.property
    have heq : h.val = c • B N + ∑ n ∈ s, a n • (B n - B (n + 1)) := hext _ _ fun x ↦ by
      rewrite [hcs x]
      change _ = (c • (B N : schwartzBruhatSubmodule _) +
        ∑ n ∈ s, a n • ((B n : schwartzBruhatSubmodule _) - B (n + 1))).val _
      rewrite [Submodule.coe_add, Submodule.coe_sum, Pi.add_apply, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      congr 1
      · exact congrArg (c * ·) (hB N x).symm
      · refine Finset.sum_congr rfl fun n _ ↦ ?_
        rewrite [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_sub, Pi.sub_apply]
        exact congrArg (a n * ·) (congrArg₂ (· - ·) (hB n x).symm (hB (n + 1) x).symm)
    refine ⟨c • LaurentPolynomial.T N + ∑ n ∈ s,
      a n • (LaurentPolynomial.T n - LaurentPolynomial.T (n + 1)), Subtype.ext ?_⟩
    rewrite [LinearMap.codRestrict_apply, heq, map_add, map_smul, map_sum, hΦT]
    refine congrArg (c • B N + ·) (Finset.sum_congr rfl fun n _ ↦ ?_)
    rewrite [map_smul, map_sub, hΦT, hΦT]
  refine ⟨LinearEquiv.ofBijective (Φ.codRestrict _ hΦinv)
    ⟨fun p q hpq ↦ hinj (congrArg Subtype.val hpq), hsurj⟩, fun n x ↦ ?_⟩
  change Φ (LaurentPolynomial.T n) (Multiplicative.ofAdd x) = _
  rewrite [hΦT, hB]

/-- Paper: Lemma 6.1.2.2(1)(1), p. 288.
The integer-unit invariants form a free Laurent module on the integer-ball indicator.
Deviation: A complex linear equivalence spells out the Laurent action by the generator
and the image of the free generator, without installing an extra module instance. -/
theorem finitePlaceSchwartz_invariants_laurent_free (w : Places)
    (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    ∃ e : LaurentPolynomial ℂ ≃ₗ[ℂ] (Representation.invariants (ρ(w))),
      (∀ x, (e 1).val (Multiplicative.ofAdd x) = finitePlaceBallIndicator w π 0 x) ∧
      ∀ P, (e (LaurentPolynomial.T 1 * P)).val =
        schwartzBruhatUnitTranslate π (e P).val := by
  choose e he using finitePlaceSchwartz_invariants_laurent_exists w π _hπ
  refine ⟨e, fun x ↦ by rw [← LaurentPolynomial.T_zero]; exact he 0 x, fun P ↦ ?_⟩
  have hext (a b : ℬᵥ(w)) (h : ∀ x, a (Multiplicative.ofAdd x) = b (Multiplicative.ofAdd x)) :
      a = b := Subtype.ext (funext fun x ↦ h x.toAdd)
  have hlin : (Representation.invariants (ρ(w))).subtype ∘ₗ e.toLinearMap ∘ₗ
      LinearMap.mulLeft ℂ (LaurentPolynomial.T 1) =
      (schwartzBruhatUnitRepresentation (R := L(w)) π) ∘ₗ
        (Representation.invariants (ρ(w))).subtype ∘ₗ e.toLinearMap := by
    refine (AddMonoidAlgebra.basis ℤ ℂ).ext fun n ↦ hext _ _ fun x ↦ ?_
    change (e (LaurentPolynomial.T 1 * LaurentPolynomial.T n)).val (Multiplicative.ofAdd x) =
      (e (LaurentPolynomial.T n)).val (Multiplicative.ofAdd ((↑π⁻¹ : L(w)) * x))
    rw [← LaurentPolynomial.T_add, he, he]
    unfold finitePlaceBallIndicator
    rw [← mul_assoc, ← Units.val_mul, ← zpow_neg_one, ← zpow_add]
    congr 4
    ring
  exact congrArg (fun φ ↦ φ P) hlin

/-- Paper: Lemma 6.1.2.2(1)(2), p. 288.
The integer-unit invariants are closed in the local Schwartz–Bruhat space. -/
theorem finitePlaceSchwartz_invariants_isClosed (w : Places) :
    IsClosed (SetLike.coe (Representation.invariants (V := ℬᵥ(w)) (ρ(w))) : Set ℬᵥ(w)) :=
  unitInvariants_isClosed _

/-- Paper: Lemma 6.1.2.2(1)(2), p. 288.
With the finest locally convex topology on Laurent polynomials, the monomial-to-ball
correspondence is a linear homeomorphism onto the unit invariants. -/
theorem finitePlaceSchwartz_invariants_laurent_equiv (w : Places)
    (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    ∃ e : FinestLocallyConvex (LaurentPolynomial ℂ) ≃L[ℂ] (Representation.invariants (ρ(w))),
      ∀ n x, (e (LaurentPolynomial.T n)).val (Multiplicative.ofAdd x) =
        finitePlaceBallIndicator w π n x := by
  choose e he using finitePlaceSchwartz_invariants_laurent_exists w π _hπ
  have := finitePlaceSchwartz_invariants_laurent_t2 w
  have := finestLocallyConvex_t2 (LaurentPolynomial ℂ)
  let S := Representation.invariants (ρ(w))
  let e' : FinestLocallyConvex (LaurentPolynomial ℂ) ≃ₗ[ℂ] S := e
  have hfwd : Continuous e' := continuous_of_finestLocallyConvex _ e'.toLinearMap
  obtain ⟨q, hq⟩ := S.exists_isCompl
  let P := S.linearProjOfIsCompl q hq
  let G : ℬᵥ(w) →ₗ[ℂ] FinestLocallyConvex (LaurentPolynomial ℂ) := e'.symm.toLinearMap ∘ₗ P
  have hG : Continuous G := finitePlaceSchwartz_invariants_laurent_continuous w G
  have hbwd : Continuous e'.symm := by
    have : (e'.symm : S → FinestLocallyConvex (LaurentPolynomial ℂ)) = G ∘ Subtype.val := by
      funext h
      change e'.symm h = e'.symm (P h.val)
      rw [Submodule.linearProjOfIsCompl_apply_left]
    rw [this]
    exact hG.comp continuous_subtype_val
  exact ⟨e'.toContinuousLinearEquivOfContinuous hfwd hbwd, fun n x ↦ he n x⟩

end Laurent

section RelativeLaurent

-- TODO(paper-gap): Lemma 6.1.2.2(2), (6.1.2.5), specifies the projective
-- topology, but §2.1.4.2 uses the inductive topology on this algebraic tensor.
-- For ℚ with one new prime the invariant space is a locally convex direct sum
-- of copies of the real Schwartz space. The canonical tensor pairing into
-- this sum is separately continuous and is not jointly continuous.
-- TODO(paper-gap): After (6.1.2.9) the kernel is the image of the outside unit
-- group itself. Its intersection with the principal ideles is trivial by the
-- archimedean coordinate. The extra quotient by the S-units is unjustified.
-- TODO(paper-gap): The restriction used on p. 291 need not be compactly
-- supported on the multiplicative group, as the restriction of 1_{ℤₚ} shows.

open Classical in
/-- Paper: Lemma 6.1.2.2(2), (6.1.2.5)–(6.1.2.6), p. 289.
The larger-stage relative unit invariants have a unique linear topological identification
with the S-local test space tensored with the multivariate Laurent polynomials.
Each pure tensor with a monomial multiplies the old test function by the indicated local balls.
Deviation: The tensor topology is inductive, following Corollary 2.1.4.2 as formalized. -/
theorem sLocalSchwartz_invariants_laurent_equiv (hST : S ⊂ T)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (π : ∀ w : ↥(T \ S), (L(w.val))ˣ)
    (_hπ : ∀ w : ↥(T \ S), Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val) :
    ∃! e : InductiveTensor ℬ(SAdeleRing F S)
        (FinestLocallyConvex (AddMonoidAlgebra ℂ (↥(T \ S) → ℤ))) ≃L[ℂ]
        (Representation.invariants <| (schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
          (relativeIntegralIdeleUnits F S T).subtype),
      ∀ (f : ℬ(SAdeleRing F S)) (a : ↥(T \ S) → ℤ) (x : SAdeleRing F T),
        (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)).val (Multiplicative.ofAdd x) =
          f (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST.le w.property⟩)) *
            ∏ w : ↥(T \ S), finitePlaceBallIndicator w.val (π w) (a w)
              (x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) := by sorry

end RelativeLaurent

section Averaging

-- These Borel structures agree with the local instances in Appendix A.3.
local instance instLocalUnitMeasurableSpaceCh06Sec1 (w : Places) :
    MeasurableSpace (L(w))ˣ := borel _

local notation "μ(" w ")" => finiteLocalMultiplicativeTamagawaMeasure F w

private theorem unitsMass_ne_top (w : Places) :
    μ(w) (U(w) : Set (L(w))ˣ) ≠ ⊤ := by
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits F w, ne_eq, ENNReal.inv_eq_top,
    ENNReal.ofReal_eq_zero, not_le]
  exact Real.sqrt_pos.2
    (pow_pos (Nat.cast_pos.2 (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm w))) _)

private theorem units_isCompact (w : Places) : IsCompact (U(w) : Set (L(w))ˣ) :=
  Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w))

private theorem units_isOpen (w : Places) : IsOpen (U(w) : Set (L(w))ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)

private instance unitsRestrict_isFinite (w : Places) :
    IsFiniteMeasure ((μ(w)).restrict (U(w) : Set (L(w))ˣ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (unitsMass_ne_top w).lt_top⟩

private local instance instProperSpaceCh06Sec1 (w : Places) : ProperSpace (L(w)) :=
  properSpace_adicCompletion w
private local instance instSecondCountableUnitsCh06Sec1 (w : Places) :
    SecondCountableTopology (L(w))ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance instBorelUnitsCh06Sec1 (w : Places) : BorelSpace (L(w))ˣ := ⟨rfl⟩

/-- Paper: Lemma 6.1.2.4(1), p. 291.
The span of integer-unit translation differences is closed.
Consequently the algebraic and continuous coinvariant quotients use the same relations.
Deviation: The closure equality states both conclusions on the relation submodule. -/
theorem finitePlaceSchwartz_unitRelations_closure_eq (w : Places) :
    (Representation.Coinvariants.ker (ρ(w))).topologicalClosure =
      Representation.Coinvariants.ker (ρ(w)) := by
  apply IsClosed.submodule_topologicalClosure_eq
  exact (congrArg (fun t ↦ @IsClosed ℬᵥ(w) t (Representation.Coinvariants.ker (ρ(w)) : Set ℬᵥ(w)))
    (finitePlaceSchwartz_finestTopology (F := F) w)).mpr
    (finestLocallyConvex_submodule_isClosed (E := schwartzBruhatSubmodule (Multiplicative (L(w))))
      (Representation.Coinvariants.ker (ρ(w))))

/-- Paper: (6.1.2.14), p. 292.
Averaging a local test function evaluates it along the multiplicative orbit and integrates
over the integer units against the local multiplicative Tamagawa measure. -/
def finitePlaceUnitAverage (w : Places) (f : ℬᵥ(w)) (x : L(w)) : ℂ :=
  ∫ u : (L(w))ˣ, f (Multiplicative.ofAdd (x * u.val)) ∂((μ(w)).restrict (U(w)))

/-- Paper: (6.1.2.14), p. 292.
The orbit integral at zero is the value at zero times the Tamagawa mass of the integer units. -/
theorem finitePlaceUnitAverage_zero (w : Places) (f : ℬᵥ(w)) :
    finitePlaceUnitAverage w f 0 =
      ((μ(w) (U(w) : Set (L(w))ˣ)).toReal : ℂ) *
        f (Multiplicative.ofAdd 0) := by
  unfold finitePlaceUnitAverage
  simp only [zero_mul, integral_const]
  rw [Complex.real_smul, Measure.real, Measure.restrict_apply_univ]

/-- Paper: (6.1.2.14), p. 292.
Each integrand of the local averaging formula is integrable on the integer units. -/
theorem finitePlaceUnitAverage_integrable (w : Places) (f : ℬᵥ(w)) (x : L(w)) :
    IntegrableOn (fun u : (L(w))ˣ ↦ f (Multiplicative.ofAdd (x * u.val)))
      (U(w) : Set (L(w))ˣ) (μ(w)) := by
  have hc : Continuous (fun u : (L(w))ˣ ↦ f (Multiplicative.ofAdd (x * u.val))) :=
    (schwartzBruhat_continuous f).comp
      (continuous_ofAdd.comp (continuous_const.mul Units.continuous_val))
  obtain ⟨C, hC⟩ := (units_isCompact w).exists_bound_of_continuousOn hc.continuousOn
  exact Integrable.of_bound hc.aestronglyMeasurable C
    ((ae_restrict_iff' (units_isOpen w).measurableSet).2 (Filter.Eventually.of_forall hC))


/-- Integration over a subgroup against a left-invariant measure is unchanged by
translating by an element of the subgroup. -/
private theorem finitePlaceUnitAverage_restrict_mul_left {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (H : Subgroup G) (hH : MeasurableSet (H : Set G)) (F : G → ℂ) {g : G} (hg : g ∈ H) :
    ∫ u, F (g * u) ∂μ.restrict H = ∫ u, F u ∂μ.restrict H := by
  rw [← integral_indicator hH, ← integral_indicator hH]
  conv_rhs => rw [← integral_mul_left_eq_self _ g]
  congr 1
  funext u
  by_cases hu : u ∈ H
  · rw [indicator_of_mem (show u ∈ (H : Set G) from hu),
      indicator_of_mem (show g * u ∈ (H : Set G) from H.mul_mem hg hu)]
  · rw [indicator_of_notMem (show u ∉ (H : Set G) from hu),
      indicator_of_notMem (show g * u ∉ (H : Set G) from fun h ↦ hu (by
        simpa using H.mul_mem (H.inv_mem hg) h))]

/-- On a compact subgroup, the integral of a function invariant under an open subgroup is
its mass times the mean of its values on finitely many coset representatives. The
representatives do not depend on the function. -/
private theorem finitePlaceUnitAverage_exists_finset {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (H : Subgroup G) (hHc : IsCompact (H : Set G))
    (hHm : MeasurableSet (H : Set G)) (V : Subgroup G) (hV : IsOpen (V : Set G)) :
    ∃ s : Finset G, s.Nonempty ∧ (∀ g ∈ s, g ∈ H) ∧
      ∀ F : G → ℂ, (∀ u v, v ∈ V → F (u * v) = F u) →
        (∀ g, Integrable (fun u ↦ F (g * u)) (μ.restrict H)) →
        ∫ u, F u ∂μ.restrict H = (μ H).toReal / s.card * ∑ g ∈ s, F g := by
  classical
  have := QuotientGroup.discreteTopology hV
  let mk : G → G ⧸ V := QuotientGroup.mk
  have hfin : (mk '' (H : Set G)).Finite :=
    (hHc.image QuotientGroup.continuous_mk).finite_of_discrete
  let T := hfin.toFinset
  have hmemT : ∀ q, q ∈ T ↔ ∃ h ∈ H, mk h = q := fun q ↦ by simp [T]
  choose! r hr using fun q (hq : q ∈ T) ↦ (hmemT q).1 hq
  have hrinj : Set.InjOn r T := fun a ha b hb hab ↦ by
    rw [← (hr a ha).2, ← (hr b hb).2, hab]
  refine ⟨T.image r, ?_, ?_, ?_⟩
  · exact ⟨r (mk 1), Finset.mem_image_of_mem _ ((hmemT _).2 ⟨1, H.one_mem, rfl⟩)⟩
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hg
    exact (hr q hq).1
  · intro F hF hFi
    have hFV : ∀ a b, mk a = mk b → F a = F b := by
      intro a b hab
      have : b⁻¹ * a ∈ V := QuotientGroup.eq.1 hab.symm
      simpa using hF b (b⁻¹ * a) this
    rw [Finset.card_image_of_injOn hrinj, Finset.sum_image hrinj]
    have hTne : (T.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.2 ⟨mk 1, (hmemT _).2 ⟨1, H.one_mem, rfl⟩⟩).ne'
    have hsum : ∀ u ∈ H, ∑ q ∈ T, F (r q * u) = ∑ q ∈ T, F (r q) := by
      intro u hu
      refine Finset.sum_nbij' (fun q ↦ q * mk u) (fun q ↦ q * (mk u)⁻¹) ?_ ?_ ?_ ?_ ?_
      · intro q hq
        obtain ⟨h, hh, rfl⟩ := (hmemT q).1 hq
        exact (hmemT _).2 ⟨h * u, H.mul_mem hh hu, rfl⟩
      · intro q hq
        obtain ⟨h, hh, rfl⟩ := (hmemT q).1 hq
        exact (hmemT _).2 ⟨h * u⁻¹, H.mul_mem hh (H.inv_mem hu), rfl⟩
      · intro q _; simp
      · intro q _; simp
      · intro q hq
        apply hFV
        rw [(hr _ ((hmemT _).1 hq |>.elim fun h hh ↦ (hmemT _).2
          ⟨h * u, H.mul_mem hh.1 hu, by rw [← hh.2]; rfl⟩)).2]
        show (QuotientGroup.mk (r q * u) : G ⧸ V) = _
        rw [QuotientGroup.mk_mul]
        exact congrArg (· * (QuotientGroup.mk u : G ⧸ V)) (hr q hq).2
    have h1 : ∀ q ∈ T, ∫ u, F (r q * u) ∂μ.restrict H = ∫ u, F u ∂μ.restrict H :=
      fun q hq ↦ finitePlaceUnitAverage_restrict_mul_left μ H hHm F (hr q hq).1
    have h2 : ∫ u, ∑ q ∈ T, F (r q * u) ∂μ.restrict H =
        ∫ _u, ∑ q ∈ T, F (r q) ∂μ.restrict H :=
      integral_congr_ae ((ae_restrict_mem hHm).mono fun u hu ↦ hsum u hu)
    rw [integral_finsetSum _ (fun q _ ↦ hFi (r q)), Finset.sum_congr rfl h1,
      integral_const, Finset.sum_const] at h2
    rw [nsmul_eq_mul, Measure.real, Measure.restrict_apply_univ, Complex.real_smul] at h2
    have hTne' : (T.card : ℂ) ≠ 0 := by exact_mod_cast hTne
    field_simp
    linear_combination h2

/-- Dilating a compactly supported, locally constant function by a continuous family of
units gives a locally constant family of functions. -/
private theorem finitePlaceUnitAverage_locallyConstant_family {G R Y : Type*} [TopologicalSpace G]
    [WeaklyLocallyCompactSpace G] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Zero Y]
    (u : G → Rˣ) (hu : Continuous u) (f : R → Y) (hf : IsLocallyConstant f)
    (hK : HasCompactSupport f) :
    IsLocallyConstant fun g x ↦ f ((u g).inv * x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  obtain ⟨L, hL, hLg⟩ := exists_compact_mem_nhds g
  let K := (fun p : G × R ↦ (u p.1).val * p.2) '' (L ×ˢ tsupport f)
  have hc : IsCompact K := (hL.prod hK).image
    ((Units.continuous_val.comp (hu.comp continuous_fst)).mul continuous_snd)
  let W := {p : G × R | f ((u p.1).inv * p.2) = f ((u g).inv * p.2)}
  have hW : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have h₁ := (Units.continuous_coe_inv.comp (hu.comp continuous_fst)).mul
      (continuous_snd (X := G) (Y := R))
    have h₂ : Continuous (fun p : G × R ↦ (u g).inv * p.2) := continuous_const.mul continuous_snd
    filter_upwards [h₁.continuousAt (hf.eventually_eq _), h₂.continuousAt (hf.eventually_eq _)]
      with q hq hq'
    exact hq.trans (hp.trans hq'.symm)
  obtain ⟨U, V, hU, _, hu₀, hV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := g)) hc hW
    (fun ⟨g', x⟩ h ↦ by rw [show g' = g from h.1]; rfl)
  filter_upwards [hLg, hU.mem_nhds (hu₀ (mem_singleton g))] with t ht hu'
  funext x
  by_cases hx : x ∈ K
  · exact @hUV (t, x) ⟨hu', hV hx⟩
  · have hz (a : G) (ha : a ∈ L) : f ((u a).inv * x) = 0 := by
      by_contra hn
      exact hx ⟨(a, (u a).inv * x), ⟨ha, subset_closure (show (u a).inv * x ∈ support f from hn)⟩,
        by change (u a).val * ((u a).inv * x) = x; rw [← mul_assoc, (u a).val_inv, one_mul]⟩
    exact (hz t ht).trans (hz g (mem_of_mem_nhds hLg)).symm

/-- Each local test function is invariant under dilation by an open subgroup of units. -/
private theorem finitePlaceUnitAverage_exists_openStabilizer (w : Places) (f : ℬᵥ(w)) :
    ∃ V : Subgroup (L(w))ˣ, IsOpen (V : Set (L(w))ˣ) ∧
      ∀ v ∈ V, ∀ x : L(w), f (Multiplicative.ofAdd (v.val * x)) = f (Multiplicative.ofAdd x) := by
  obtain ⟨hl, hc⟩ := (mem_finitePlaceSchwartz_iff (F := F) w (fun x ↦ f (Multiplicative.ofAdd x))).1
    ⟨f, fun _ ↦ rfl⟩
  have hΦ := finitePlaceUnitAverage_locallyConstant_family (G := (L(w))ˣ) (fun g ↦ g⁻¹)
    continuous_inv _ hl hc
  let V : Subgroup (L(w))ˣ :=
    { carrier := {g | ∀ x, f (Multiplicative.ofAdd (g.val * x)) = f (Multiplicative.ofAdd x)}
      mul_mem' := fun {a b} ha hb x ↦ by
        change f (Multiplicative.ofAdd ((a * b).val * x)) = _
        rw [Units.val_mul, mul_assoc, ha, hb]
      one_mem' := fun x ↦ by
        change f (Multiplicative.ofAdd ((1 : (L(w))ˣ).val * x)) = _
        rw [Units.val_one, one_mul]
      inv_mem' := fun {a} ha x ↦ by
        have := ha (↑a⁻¹ * x)
        rw [← mul_assoc, Units.mul_inv, one_mul] at this
        exact this.symm }
  refine ⟨V, Subgroup.isOpen_of_mem_nhds V (g := 1) ?_, fun v hv x ↦ hv x⟩
  refine Filter.mem_of_superset ((hΦ.isOpen_fiber _).mem_nhds rfl) fun g hg x ↦ ?_
  have := congrFun hg x
  simpa [Units.inv_eq_val_inv] using this

/-- The local average is the unit mass times the mean of finitely many unit dilates. -/
private theorem finitePlaceUnitAverage_eq_finset_sum (w : Places) (f : ℬᵥ(w)) :
    ∃ s : Finset (L(w))ˣ, s.Nonempty ∧ (∀ g ∈ s, g ∈ U(w)) ∧ ∀ x,
      finitePlaceUnitAverage w f x = ((μ(w) (U(w) : Set (L(w))ˣ)).toReal / s.card : ℝ) *
        ∑ g ∈ s, f (Multiplicative.ofAdd (x * g.val)) := by
  have := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) w
  obtain ⟨V, hV, hfV⟩ := finitePlaceUnitAverage_exists_openStabilizer w f
  obtain ⟨s, hs, hsU, hsF⟩ := finitePlaceUnitAverage_exists_finset (μ(w)) (U(w))
    (units_isCompact w) (units_isOpen w).measurableSet V hV
  refine ⟨s, hs, hsU, fun x ↦ ?_⟩
  have := hsF (fun u ↦ f (Multiplicative.ofAdd (x * u.val))) ?_ ?_
  · rw [finitePlaceUnitAverage, this]
    push_cast
    rfl
  · intro u v hv
    rw [Units.val_mul, show x * (u.val * v.val) = v.val * (x * u.val) by ring]
    exact hfV v hv _
  · intro g
    have := finitePlaceUnitAverage_integrable w f (x * g.val)
    simpa only [IntegrableOn, Units.val_mul, mul_assoc] using this

/-- Translating a test function by an integer unit leaves its local average unchanged. -/
private theorem finitePlaceUnitAverage_translate (w : Places) (f : ℬᵥ(w)) {g : (L(w))ˣ}
    (hg : g ∈ U(w)) (x : L(w)) :
    finitePlaceUnitAverage w f (g.val * x) = finitePlaceUnitAverage w f x := by
  have := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) w
  unfold finitePlaceUnitAverage
  have h := finitePlaceUnitAverage_restrict_mul_left (μ(w)) (U(w)) (units_isOpen w).measurableSet
    (fun u ↦ f (Multiplicative.ofAdd (x * u.val))) hg
  simp only [Units.val_mul] at h
  rw [← h]
  congr 1
  funext u
  rw [mul_assoc, mul_left_comm]

/-- The local average is additive in the test function. -/
private theorem finitePlaceUnitAverage_add (w : Places) (f g : ℬᵥ(w)) (x : L(w)) :
    finitePlaceUnitAverage w (f + g) x = finitePlaceUnitAverage w f x + finitePlaceUnitAverage w g x :=
  integral_add (finitePlaceUnitAverage_integrable w f x) (finitePlaceUnitAverage_integrable w g x)

/-- The local average is homogeneous in the test function. -/
private theorem finitePlaceUnitAverage_smul (w : Places) (c : ℂ) (f : ℬᵥ(w)) (x : L(w)) :
    finitePlaceUnitAverage w (c • f) x = c * finitePlaceUnitAverage w f x :=
  integral_const_mul c _

/-- Local averaging is a linear endomorphism of the local Schwartz–Bruhat space. -/
private theorem finitePlaceUnitAverage_exists_linearMap (w : Places) :
    ∃ A : ℬᵥ(w) →ₗ[ℂ] ℬᵥ(w), ∀ f x, A f (Multiplicative.ofAdd x) = finitePlaceUnitAverage w f x := by
  have hmem (f : ℬᵥ(w)) : ∃ g : ℬᵥ(w), ∀ x, g (Multiplicative.ofAdd x) = finitePlaceUnitAverage w f x := by
    obtain ⟨s, -, -, hs⟩ := finitePlaceUnitAverage_eq_finset_sum w f
    refine ⟨(((μ(w) (U(w) : Set (L(w))ˣ)).toReal / s.card : ℝ) : ℂ) •
      ∑ g ∈ s, schwartzBruhatUnitTranslate g⁻¹ f, fun x ↦ ?_⟩
    refine Eq.trans ?_ (hs x).symm
    choose L hL using finitePlaceSchwartz_invariants_laurent_eval (Multiplicative.ofAdd x)
    rewrite [← hL, map_smul, map_sum, smul_eq_mul]
    refine congrArg (_ * ·) (Finset.sum_congr rfl fun g _ ↦ ?_)
    rewrite [hL]
    change f (Multiplicative.ofAdd ((↑g⁻¹⁻¹ : L(w)) * x)) = _
    rewrite [inv_inv, mul_comm]
    rfl
  have hext (a b : ℬᵥ(w)) (h : ∀ x, a (Multiplicative.ofAdd x) = b (Multiplicative.ofAdd x)) :
      a = b := Subtype.ext (funext fun x ↦ h x.toAdd)
  choose A hA using hmem
  refine ⟨⟨⟨A, fun f g ↦ hext _ _ (fun x ↦ ?_)⟩, fun c f ↦ hext _ _ (fun x ↦ ?_)⟩, hA⟩
  · choose L hL using finitePlaceSchwartz_invariants_laurent_eval (Multiplicative.ofAdd x)
    refine (hA (f + g) x).trans ((finitePlaceUnitAverage_add w f g x).trans ?_)
    have h1 : (A f + A g) (Multiplicative.ofAdd x) =
        A f (Multiplicative.ofAdd x) + A g (Multiplicative.ofAdd x) :=
      (hL _).symm.trans ((map_add L _ _).trans (congrArg₂ (· + ·) (hL _) (hL _)))
    exact (congrArg₂ (· + ·) (hA f x) (hA g x)).symm.trans h1.symm
  · choose L hL using finitePlaceSchwartz_invariants_laurent_eval (Multiplicative.ofAdd x)
    refine (hA (c • f) x).trans ((finitePlaceUnitAverage_smul w c f x).trans ?_)
    have h1 : (c • A f) (Multiplicative.ofAdd x) = c * A f (Multiplicative.ofAdd x) :=
      (hL _).symm.trans ((map_smul L c (A f)).trans (congrArg (c • ·) (hL _)))
    exact (congrArg (c * ·) (hA f x)).symm.trans h1.symm

/-- Paper: Lemma 6.1.2.4(2), (6.1.2.13)–(6.1.2.14), p. 292.
Local unit averaging defines a linear map to compactly supported continuous functions
which is continuous for their uniform norm. -/
theorem finitePlaceUnitAverage_continuous_uniform (w : Places) :
    ∃ A : ℬᵥ(w) →ₗ[ℂ] C_c(L(w), ℂ),
      (∀ f x, A f x = finitePlaceUnitAverage w f x) ∧
        Continuous (fun f ↦ (A f).toBoundedContinuousFunction) := by
  choose A hA using finitePlaceUnitAverage_exists_linearMap w
  have hcs (f : ℬᵥ(w)) : HasCompactSupport (fun x ↦ A f (Multiplicative.ofAdd x)) :=
    ((mem_finitePlaceSchwartz_iff (F := F) w _).1 ⟨A f, fun _ ↦ rfl⟩).2
  have hct (f : ℬᵥ(w)) : Continuous (fun x ↦ A f (Multiplicative.ofAdd x)) :=
    (schwartzBruhat_continuous (A f)).comp continuous_ofAdd
  have hadd (f g : ℬᵥ(w)) (x : L(w)) : A (f + g) (Multiplicative.ofAdd x) =
      A f (Multiplicative.ofAdd x) + A g (Multiplicative.ofAdd x) := by
    choose L hL using finitePlaceSchwartz_invariants_laurent_eval (Multiplicative.ofAdd x)
    exact (congrArg (fun φ : ℬᵥ(w) ↦ φ (Multiplicative.ofAdd x)) (map_add A f g)).trans
      ((hL _).symm.trans ((map_add L _ _).trans (congrArg₂ (· + ·) (hL _) (hL _))))
  have hsmul (c : ℂ) (f : ℬᵥ(w)) (x : L(w)) : A (c • f) (Multiplicative.ofAdd x) =
      c * A f (Multiplicative.ofAdd x) := by
    choose L hL using finitePlaceSchwartz_invariants_laurent_eval (Multiplicative.ofAdd x)
    exact (congrArg (fun φ : ℬᵥ(w) ↦ φ (Multiplicative.ofAdd x)) (map_smul A c f)).trans
      ((hL _).symm.trans ((map_smul L c _).trans (congrArg (c • ·) (hL _))))
  refine ⟨⟨⟨fun f ↦ ⟨⟨fun x ↦ A f (Multiplicative.ofAdd x), hct f⟩, hcs f⟩, ?_⟩, ?_⟩,
    fun f x ↦ hA f x, ?_⟩
  · intro f g
    ext x
    exact hadd f g x
  · intro c f
    ext x
    exact hsmul c f x
  have keyT : ∃ T : ℬᵥ(w) →ₗ[ℂ] BoundedContinuousFunction (L(w)) ℂ, ∀ f, T f =
      (⟨⟨fun x ↦ A f (Multiplicative.ofAdd x), hct f⟩, hcs f⟩ :
        C_c(L(w), ℂ)).toBoundedContinuousFunction :=
    ⟨⟨⟨fun f ↦ (⟨⟨fun x ↦ A f (Multiplicative.ofAdd x), hct f⟩, hcs f⟩ :
        C_c(L(w), ℂ)).toBoundedContinuousFunction, by
      intro f g
      ext x
      exact hadd f g x⟩, by
      intro c f
      ext x
      exact hsmul c f x⟩, fun _ ↦ rfl⟩
  choose T hT using keyT
  have i1 : PolynormableSpace ℂ (BoundedContinuousFunction (L(w)) ℂ) := inferInstance
  have i2 : T2Space (BoundedContinuousFunction (L(w)) ℂ) := inferInstance
  have hTc : Continuous T := @finitePlaceSchwartz_invariants_laurent_continuous F _ _ w
    (BoundedContinuousFunction (L(w)) ℂ) _ _ _ i1 i2 T
  have e : (⇑T : ℬᵥ(w) → BoundedContinuousFunction (L(w)) ℂ) = fun f ↦
      (⟨⟨fun x ↦ A f (Multiplicative.ofAdd x), hct f⟩, hcs f⟩ :
        C_c(L(w), ℂ)).toBoundedContinuousFunction := funext hT
  exact (congrArg (fun φ : ℬᵥ(w) → BoundedContinuousFunction (L(w)) ℂ ↦ Continuous φ) e).mp hTc

/-- Paper: Lemma 6.1.2.4(2), p. 292.
Local unit averaging also defines a continuous linear map in the intrinsic
Schwartz–Bruhat topology. -/
theorem finitePlaceUnitAverage_continuous_schwartzBruhat (w : Places) :
    ∃ A : ℬᵥ(w) →L[ℂ] ℬᵥ(w),
      ∀ f x, A f (Multiplicative.ofAdd x) = finitePlaceUnitAverage w f x := by
  choose A hA using finitePlaceUnitAverage_exists_linearMap w
  have := finitePlaceSchwartz_invariants_laurent_t2 w
  exact ⟨⟨A, finitePlaceSchwartz_invariants_laurent_continuous w A⟩, hA⟩

/-- The local average is subtractive in the test function. -/
private theorem finitePlaceUnitAverage_eq_zero_iff_sub (w : Places) (f g : ℬᵥ(w)) (x : L(w)) :
    finitePlaceUnitAverage w (f - g) x = finitePlaceUnitAverage w f x - finitePlaceUnitAverage w g x :=
  integral_sub (finitePlaceUnitAverage_integrable w f x) (finitePlaceUnitAverage_integrable w g x)

/-- Averaging a unit translate is averaging the original function at the translated point. -/
private theorem finitePlaceUnitAverage_eq_zero_iff_translate (w : Places) (f : ℬᵥ(w))
    (g : (L(w))ˣ) (x : L(w)) :
    finitePlaceUnitAverage w (schwartzBruhatUnitTranslate g f) x =
      finitePlaceUnitAverage w f ((↑g⁻¹ : L(w)) * x) := by
  unfold finitePlaceUnitAverage
  congr 1
  funext u
  change f (Multiplicative.ofAdd ((↑g⁻¹ : L(w)) * (x * u.val))) = _
  rw [mul_assoc]

/-- The integer units have nonzero finite multiplicative mass. -/
private theorem finitePlaceUnitAverage_eq_zero_iff_mass (w : Places) :
    (μ(w) (U(w) : Set (L(w))ˣ)).toReal ≠ 0 := by
  have := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) w
  exact ENNReal.toReal_ne_zero.2
    ⟨((units_isOpen w).measure_pos (μ(w)) ⟨1, (U(w)).one_mem⟩).ne', unitsMass_ne_top w⟩

/-- Paper: Lemma 6.1.2.4(2), p. 292.
A test function averages to zero exactly when it belongs to the span of unit
translation differences. -/
theorem finitePlaceUnitAverage_eq_zero_iff (w : Places) (f : ℬᵥ(w)) :
    (∀ x, finitePlaceUnitAverage w f x = 0) ↔
      f ∈ Representation.Coinvariants.ker (ρ(w)) := by
  constructor
  · intro h0
    obtain ⟨s, hs, hsU, hsum⟩ := finitePlaceUnitAverage_eq_finset_sum w f
    have hm := finitePlaceUnitAverage_eq_zero_iff_mass w
    have hcard : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    have hz : ∀ x, ∑ g ∈ s, f (Multiplicative.ofAdd (x * g.val)) = 0 := by
      intro x
      have h := (hsum x).symm.trans (h0 x)
      rcases mul_eq_zero.1 h with h | h
      · exfalso
        have hc : ((μ(w) (U(w) : Set (L(w))ˣ)).toReal / s.card : ℝ) ≠ 0 :=
          div_ne_zero hm (by exact_mod_cast hs.card_pos.ne')
        exact hc (by exact_mod_cast h)
      · exact h
    have hmem : ∀ g ∈ s, f - schwartzBruhatUnitTranslate g⁻¹ f ∈
        Representation.Coinvariants.ker (ρ(w)) := by
      intro g hg
      have := Representation.Coinvariants.sub_mem_ker (ρ := ρ(w))
        ⟨g⁻¹, (U(w)).inv_mem (hsU g hg)⟩ f
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
    have heq : f = ∑ g ∈ s, ((s.card : ℂ)⁻¹) • (f - schwartzBruhatUnitTranslate g⁻¹ f) := by
      apply Subtype.ext
      funext y
      change f y = (∑ g ∈ s, ((s.card : ℂ)⁻¹) •
        (f - schwartzBruhatUnitTranslate g⁻¹ f : schwartzBruhatSubmodule _)).val y
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only [Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      have ht : ∑ g ∈ s, (schwartzBruhatUnitTranslate g⁻¹ f : schwartzBruhatSubmodule _).val y =
          0 := by
        rw [← hz y.toAdd]
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        change f (Multiplicative.ofAdd ((↑g⁻¹⁻¹ : L(w)) * y.toAdd)) = _
        rw [inv_inv, mul_comm]
      rw [ht, sub_zero, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
      rfl
    rw [heq]
    exact Submodule.sum_mem _ fun g hg ↦ Submodule.smul_mem _ _ (hmem g hg)
  · intro hf x
    unfold Representation.Coinvariants.ker at hf
    induction hf using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨g, h⟩, rfl⟩ := hv
      rw [finitePlaceUnitAverage_eq_zero_iff_sub]
      change finitePlaceUnitAverage w (schwartzBruhatUnitTranslate g.val h) x - _ = 0
      rw [finitePlaceUnitAverage_eq_zero_iff_translate,
        finitePlaceUnitAverage_translate w h ((U(w)).inv_mem g.2), sub_self]
    | zero =>
      have := finitePlaceUnitAverage_smul w 0 0 x
      rwa [zero_smul, zero_mul] at this
    | add a b _ _ ha hb => rw [finitePlaceUnitAverage_add, ha, hb, add_zero]
    | smul c a _ ha => rw [finitePlaceUnitAverage_smul, ha, mul_zero]

-- TODO(paper-gap): The proof on p. 292 identifies multiplicative unit averaging
-- with additive convolution and deduces vanishing of the function from unramified
-- Mellin values. For the indicator of the integer ring at the trivial character,
-- the shell integrals in (6.1.2.17) all have the same positive mass. A nonzero
-- eigendistribution annihilates every unit difference only for unramified weight.
-- The kernel assertion follows by averaging the finite unit orbit of each test function.

/-- Paper: Lemma 6.1.2.4(2), (6.1.2.15), p. 292.
Multiplicative unit averaging induces a linear homeomorphism from the algebraic
coinvariants with their quotient topology to the integer-unit invariants. -/
theorem finitePlaceUnitAverage_coinvariants_equiv (w : Places) :
    ∃ N : (ℬᵥ(w) ⧸ Representation.Coinvariants.ker (ρ(w))) ≃L[ℂ] (Representation.invariants (ρ(w))),
      ∀ (f : ℬᵥ(w)) x, (N (Submodule.Quotient.mk f)).val (Multiplicative.ofAdd x) =
        finitePlaceUnitAverage w f x := by
  classical
  choose A hA using finitePlaceUnitAverage_exists_linearMap w
  have := finitePlaceSchwartz_invariants_laurent_t2 w
  have hext (a b : ℬᵥ(w)) (h : ∀ x, a (Multiplicative.ofAdd x) = b (Multiplicative.ofAdd x)) :
      a = b := Subtype.ext (funext fun x ↦ h x.toAdd)
  let m : ℂ := ((μ(w) (U(w) : Set (L(w))ˣ)).toReal : ℂ)
  have hm : m ≠ 0 := by exact_mod_cast finitePlaceUnitAverage_eq_zero_iff_mass w
  have hinv (f : ℬᵥ(w)) : A f ∈ Representation.invariants (ρ(w)) := by
    refine (Representation.mem_invariants _ _).2 fun g ↦ hext _ _ fun x ↦ ?_
    change (A f) (Multiplicative.ofAdd ((↑(g.val)⁻¹ : L(w)) * x)) = _
    rw [hA, hA, finitePlaceUnitAverage_translate w f ((U(w)).inv_mem g.2)]
  have havg (h : ℬᵥ(w)) (hh : h ∈ Representation.invariants (ρ(w))) (x : L(w)) :
      finitePlaceUnitAverage w h x = m * h (Multiplicative.ofAdd x) := by
    unfold finitePlaceUnitAverage
    rw [integral_congr_ae (g := fun _ ↦ h (Multiplicative.ofAdd x))
      ((ae_restrict_mem (units_isOpen w).measurableSet).mono fun u hu ↦ ?_)]
    · rw [integral_const, Measure.real, Measure.restrict_apply_univ, Complex.real_smul]
    · have := congrArg (fun φ : ℬᵥ(w) ↦ φ (Multiplicative.ofAdd x))
        ((Representation.mem_invariants _ _).1 hh ⟨u⁻¹, (U(w)).inv_mem hu⟩)
      change h (Multiplicative.ofAdd ((↑(u⁻¹)⁻¹ : L(w)) * x)) = _ at this
      rw [inv_inv] at this
      change h (Multiplicative.ofAdd (x * u.val)) = _
      rw [mul_comm]
      exact this
  let B : ℬᵥ(w) →ₗ[ℂ] Representation.invariants (ρ(w)) := A.codRestrict _ hinv
  have hB (f : ℬᵥ(w)) : (B f).val = A f := rfl
  have hBs : Surjective B := fun h ↦ ⟨m⁻¹ • h.val, Subtype.ext (hext _ _ fun x ↦ by
    rw [hB, hA, finitePlaceUnitAverage_smul, havg h.val h.2, ← mul_assoc, inv_mul_cancel₀ hm,
      one_mul])⟩
  have hker : LinearMap.ker B = Representation.Coinvariants.ker (ρ(w)) := by
    ext f
    rw [LinearMap.mem_ker, ← finitePlaceUnitAverage_eq_zero_iff]
    constructor
    · intro h x
      rw [← hA, ← hB, h]
      rfl
    · intro h
      exact Subtype.ext (hext _ _ fun x ↦ by rw [hB, hA, h]; rfl)
  let N0 := (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective B hBs)
  have hN0 (f : ℬᵥ(w)) : N0 (Submodule.Quotient.mk f) = B f := rfl
  have hBc : Continuous B :=
    continuous_induced_rng.2 (finitePlaceSchwartz_invariants_laurent_continuous w A)
  have hfwd : Continuous N0 :=
    (Submodule.isOpenQuotientMap_mkQ _).isQuotientMap.continuous_iff.2 hBc
  have hsymm : (N0.symm : Representation.invariants (ρ(w)) → _) =
      fun h ↦ Submodule.Quotient.mk (m⁻¹ • h.val) := by
    funext h
    refine N0.symm_apply_eq.2 ?_
    rw [hN0]
    exact Subtype.ext (hext _ _ fun x ↦ by
      rw [hB, hA, finitePlaceUnitAverage_smul, havg h.val h.2, ← mul_assoc, inv_mul_cancel₀ hm,
        one_mul])
  have hbwd : Continuous N0.symm := by
    rw [hsymm]
    exact (Submodule.isOpenQuotientMap_mkQ _).continuous.comp
      ((continuous_const_smul _).comp continuous_subtype_val)
  exact ⟨N0.toContinuousLinearEquivOfContinuous hfwd hbwd, fun f x ↦ hA f x⟩

local notation "K(" D ")" => FinitePlaceProduct F D
local notation "KUnits(" D ")" =>
  (Subgroup.pi Set.univ (fun w : D ↦ U(w.val))).comap
    (MulEquiv.piUnits (M := fun w : D ↦ L(w.val))).toMonoidHom
local notation "ρΠ(" D ")" =>
  (schwartzBruhatUnitRepresentation (R := K(D))).comp (KUnits(D)).subtype

/-- Paper: Lemma 6.1.2.4(3), p. 292.
The product of the local averages integrates the test function along its orbit
against the product of the restricted local multiplicative Tamagawa measures. -/
def finiteProductUnitAverage (D : Finset Places) (f : ℬ(K(D))) (x : K(D)) : ℂ :=
  ∫ u : ∀ v : D, (L(v.val))ˣ,
    f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val))
    ∂(Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val)))

/-- Paper: Lemma 6.1.2.4(3), p. 292.
At the zero tuple, product averaging multiplies the value there by the product
of the local integer-unit masses. -/
theorem finiteProductUnitAverage_zero (D : Finset Places) (f : ℬ(K(D))) :
    finiteProductUnitAverage D f 0 =
      (∏ w : D, ((μ(w.val) (U(w.val) : Set (L(w.val))ˣ)).toReal : ℂ)) *
        f (Multiplicative.ofAdd 0) := by
  unfold finiteProductUnitAverage
  simp only [Pi.zero_apply, zero_mul, integral_const]
  rw [Measure.real, Measure.pi_univ, ENNReal.toReal_prod, Complex.real_smul, Complex.ofReal_prod]
  simp only [Measure.restrict_apply_univ]
  rfl

private local instance (w : HeightOneSpectrum (𝓞 F)) : ProperSpace (L(w)) := properSpace_adicCompletion w
private local instance (w : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (L(w))ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

/-- Paper: Lemma 6.1.2.4(3), p. 292.
The product orbit integral is integrable against the finite product of the restricted measures. -/
theorem finiteProductUnitAverage_integrable (D : Finset Places) (f : ℬ(K(D))) (x : K(D)) :
    Integrable
      (fun u : ∀ v : D, (L(v.val))ˣ ↦
        f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val)))
      (Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))) := by
  have hc : Continuous (fun u : ∀ v : D, (L(v.val))ˣ ↦
        f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val))) :=
    (schwartzBruhat_continuous f).comp
      (continuous_ofAdd.comp (continuous_pi fun v ↦
        continuous_const.mul (Units.continuous_val.comp (continuous_apply v))))
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun v : D ↦ units_isCompact v.val).exists_bound_of_continuousOn
    hc.continuousOn
  refine Integrable.of_bound hc.aestronglyMeasurable C ?_
  have hae : ∀ᵐ u ∂(Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))),
      ∀ v : D, u v ∈ (U(v.val) : Set (L(v.val))ˣ) := by
    rw [ae_all_iff]
    intro v
    exact (Measure.tendsto_eval_ae_ae (μ := fun v : D ↦ (μ(v.val)).restrict (U(v.val))) (i := v)).eventually
      (ae_restrict_mem (units_isOpen v.val).measurableSet)
  filter_upwards [hae] with u hu
  exact hC u (Set.mem_univ_pi.2 hu)


/-- Paper: Lemma 6.1.2.4(3), p. 292.
The integer-unit invariants are closed in the Schwartz–Bruhat space on the finite product.
Deviation: The place set is written directly as the finite set of additional places. -/
theorem finiteProductSchwartz_unitInvariants_isClosed (D : Finset Places) (_hD : D.Nonempty) :
    IsClosed ((Representation.invariants (ρΠ(D))) : Set ℬ(K(D))) :=
  unitInvariants_isClosed _

/-- Paper: Lemma 6.1.2.4(3), (6.1.2.16), p. 292.
The product of the local unit averages induces a linear homeomorphism from
coinvariants with their quotient topology to invariants on the finite product.
Deviation: The place set is written directly as the finite set of additional places. -/
theorem finiteProductUnitAverage_coinvariants_equiv (D : Finset Places) (_hD : D.Nonempty) :
    ∃ N : (ℬ(K(D)) ⧸ Representation.Coinvariants.ker (ρΠ(D))) ≃L[ℂ] (Representation.invariants (ρΠ(D))),
      ∀ (f : ℬ(K(D))) x, (N (Submodule.Quotient.mk f)).val (Multiplicative.ofAdd x) =
        finiteProductUnitAverage D f x := by sorry

end Averaging

end RiemannMasullo
