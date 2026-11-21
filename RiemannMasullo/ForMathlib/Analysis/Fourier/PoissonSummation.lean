module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

local notation "e" => (fun (m : ℤ) (x : ℝ) ↦
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (x : ℂ)))

/-- Integral frequencies are unchanged upon translating the input by an integer. -/
private theorem exp_int_frequency_add (m n : ℤ) (x : ℝ) : e m (x + n) = e m x := by
  push_cast
  rw [mul_add, Complex.exp_add, show
    2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (n : ℂ) =
      ((m * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The integer periodization of an integrable profile is integrable over one period. -/
theorem intervalIntegrable_periodization {g : ℝ → ℂ} (hg : Integrable g) (a : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ ∑' n : ℤ, g (x + n)) volume a (a + 1) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_add_of_nonneg_right zero_le_one)]
  let J := Ioc a (a + 1)
  have hg' (n : ℤ) : IntegrableOn (fun x : ℝ ↦ g (x + n)) J :=
    (hg.comp_add_right (n : ℝ)).integrableOn
  refine ⟨(AEMeasurable.tsum
    (fun n ↦ (hg' n).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable, ?_⟩
  have hshift (n : ℤ) :
      (∫⁻ x in J, ‖g (x + n)‖ₑ) = ∫⁻ x in Ioc (a + n) (a + n + 1), ‖g x‖ₑ := by
    simpa only [J, image_add_const_Ioc, add_right_comm a 1] using
      (measurePreserving_add_right volume (n : ℝ)).setLIntegral_comp_emb
        (MeasurableEquiv.addRight (n : ℝ)).measurableEmbedding (fun x ↦ ‖g x‖ₑ) J
  change (∫⁻ x in J, ‖∑' n : ℤ, g (x + n)‖ₑ) < ⊤
  calc
    (∫⁻ x in J, ‖∑' n : ℤ, g (x + n)‖ₑ) ≤ ∫⁻ x in J, ∑' n : ℤ, ‖g (x + n)‖ₑ :=
      lintegral_mono fun _ ↦ eNorm_tsum_le_tsum_eNorm
    _ = ∑' n : ℤ, ∫⁻ x in J, ‖g (x + n)‖ₑ :=
      lintegral_tsum fun n ↦ (hg' n).aestronglyMeasurable.aemeasurable.eNorm
    _ = ∫⁻ x, ‖g x‖ₑ := by
      simp_rw [hshift]
      rw [← lintegral_iUnion (fun _ ↦ measurableSet_Ioc) (pairwise_disjoint_Ioc_add_intCast a),
        iUnion_Ioc_add_intCast a, Measure.restrict_univ]
    _ < ⊤ := hg.hasFiniteIntegral

/-- The positive-frequency Fourier integral at an integer is the corresponding integral
of the periodization over any interval of length one. -/
theorem integral_exp_mul_eq_intervalIntegral_periodization {g : ℝ → ℂ}
    (hg : Integrable g) (a : ℝ) (m : ℤ) :
    (∫ x : ℝ, e m x * g x) =
      ∫ x in a..(a + 1), e m x * ∑' n : ℤ, g (x + n) := by
  let H (x : ℝ) := e m x * g x
  have hnorm (x : ℝ) : ‖e m x‖ = 1 := by simp [Complex.norm_exp, Complex.mul_re]
  have hH : Integrable H :=
    hg.bdd_mul (show Continuous (e m) by fun_prop).aestronglyMeasurable
      (.of_forall (fun x ↦ (hnorm x).le))
  have hshift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {F : ℝ → E} (hF : Integrable F) :
      HasSum (fun n : ℤ ↦ ∫ x in a..(a + 1), F (x + n)) (∫ x, F x) := by
    simpa only [intervalIntegral.integral_comp_add_right, add_right_comm a 1] using
      hF.hasSum_intervalIntegral a
  have hnormsum : Summable (fun n : ℤ ↦ ∫ x in a..(a + 1), ‖H (x + n)‖) :=
    (hshift (F := fun x ↦ ‖H x‖) hH.norm).summable
  calc
    (∫ x, H x) = ∑' n : ℤ, ∫ x in a..(a + 1), H (x + n) := (hshift hH).tsum_eq.symm
    _ = ∫ x in a..(a + 1), ∑' n : ℤ, H (x + n) := by
      simp only [intervalIntegral.integral_of_le (le_add_of_nonneg_right zero_le_one)] at hnormsum ⊢
      exact integral_tsum_of_summable_integral_norm
        (fun n ↦ (hH.comp_add_right (n : ℝ)).integrableOn) hnormsum
    _ = ∫ x in a..(a + 1), e m x * ∑' n : ℤ, g (x + n) := by
      simp only [H, exp_int_frequency_add, tsum_mul_left]

/-- Multiplying the symmetric exponential sum by its geometric difference
leaves only the two boundary terms. -/
private theorem dirichlet_sum_mul_sub (N : ℕ) (x : ℝ) :
    (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), e m x) * (e 1 x - 1) =
      e ((N : ℤ) + 1) x - e (-(N : ℤ)) x := by
  have hadd (m : ℤ) : e m x * e 1 x = e (1 + m) x := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_sub, mul_one, Finset.sum_mul, ← Finset.Ico_add_one_right_eq_Icc]
  simp_rw [hadd]
  rw [Finset.sum_Ico_add (fun m ↦ e m x) (-(N : ℤ)) ((N : ℤ) + 1) 1]
  have hle : -(N : ℤ) + 1 ≤ (N : ℤ) + 1 := by omega
  have hlt : -(N : ℤ) < (N : ℤ) + 1 := by omega
  rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hle,
    ← Finset.insert_Ico_add_one_left_eq_Ico hlt, Finset.sum_insert (by simp)]
  ring

/-- The geometric difference is bounded below linearly on the centered unit interval. -/
private theorem le_norm_exp_one_sub_one {x : ℝ} (hx : |x| ≤ 1 / 2) :
    4 * |x| ≤ ‖e 1 x - 1‖ := by
  have hsin : 2 * |x| ≤ Real.sin (Real.pi * |x|) := by
    have h := Real.mul_le_sin (x := Real.pi * |x|)
      (mul_nonneg Real.pi_pos.le (abs_nonneg x))
      ((mul_le_mul_of_nonneg_left hx Real.pi_pos.le).trans_eq (by ring))
    convert h using 1
    field_simp
  have hsinabs : |Real.sin (Real.pi * x)| = Real.sin (Real.pi * |x|) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi, abs_mul, abs_of_pos Real.pi_pos]
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith only [hx, Real.pi_pos]
  change 4 * |x| ≤ ‖Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (x : ℂ)) - 1‖
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (x : ℂ) =
      Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    show 2 * Real.pi * x / 2 = Real.pi * x by ring, hsinabs]
  linarith only [hsin]

/-- Dirichlet convergence at zero from a linear bound on the symmetric average
of the integrable profile in a neighborhood of zero. -/
theorem tendsto_sum_intervalIntegral_exp_of_midpoint_bound {F : ℝ → ℂ} {z : ℂ}
    (hF : IntervalIntegrable F volume (-(1 / 2) : ℝ) (1 / 2))
    (hz : ∃ C δ : ℝ, 0 < δ ∧
      ∀ x ∈ Ioo 0 δ, ‖(F x + F (-x)) / 2 - z‖ ≤ C * x) :
    Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ∫ x in (-(1 / 2) : ℝ)..(1 / 2), e m x * F x) atTop (𝓝 z) := by
  let b : ℝ := 1 / 2
  have hab : -b ≤ b := by norm_num [b]
  let J := Ioc (-b) b
  let K (N : ℕ) (x : ℝ) := ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), e m x
  let A (x : ℝ) := (F x + F (-x)) / 2 - z
  have hAeven (x : ℝ) : A (-x) = A x := by simp [A, add_comm]
  have hKcont (N : ℕ) : Continuous (K N) := by
    dsimp [K]
    fun_prop
  have hKeven (N : ℕ) (x : ℝ) : K N (-x) = K N x := by
    apply Finset.sum_nbij' (fun m : ℤ ↦ -m) (fun m : ℤ ↦ -m)
    · simp only [Finset.mem_Icc]
      intro m hm
      omega
    · simp only [Finset.mem_Icc]
      intro m hm
      omega
    · simp
    · simp
    · intro m _
      change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((-x : ℝ) : ℂ)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-m : ℤ) : ℂ) * (x : ℂ))
      congr 1
      push_cast
      ring
  have hmass (N : ℕ) : (∫ x in -b..b, K N x) = 1 := by
    change (∫ x in -b..b, ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), e m x) = 1
    rw [intervalIntegral.integral_finsetSum (f := e)]
    · rw [Finset.sum_eq_single (0 : ℤ)]
      · norm_num [b, intervalIntegral.integral_const]
      · intro m _ hm
        rw [integral_exp_mul_complex (by simp [Real.pi_ne_zero, hm])]
        have heq : e m b = e m (-b) := by
          simpa only [Int.cast_one, show -b + 1 = b by norm_num [b]] using
            exp_int_frequency_add m 1 (-b)
        change (e m b - e m (-b)) / _ = _
        rw [heq, sub_self, zero_div]
      · simp
    · intro m _
      exact (show Continuous (e m) by fun_prop).intervalIntegrable _ _
  have hFneg : IntervalIntegrable (fun x ↦ F (-x)) volume (-b) b := by
    simpa only [neg_neg] using (IntervalIntegrable.iff_comp_neg (by simp)).mp hF.symm
  have hA : IntervalIntegrable A volume (-b) b :=
    ((hF.add hFneg).mul_const (2 : ℂ)⁻¹).sub intervalIntegrable_const
  -- The linear bound on the symmetric difference makes the quotient integrable at zero.
  let G (x : ℝ) := A x / (e 1 x - 1)
  have hG : IntervalIntegrable G volume (-b) b := by
    obtain ⟨C, δ, hδ, hbound⟩ := hz
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hA ⊢
    apply (integrable_const (|C| / 4 : ℝ) |>.add (hA.norm.div_const (4 * δ))).mono'
      (f := G)
      ((hA.aestronglyMeasurable.aemeasurable.div
        (show Continuous (fun x ↦ e 1 x - 1) by fun_prop).measurable.aemeasurable).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    have hx' : |x| ≤ b := abs_le.mpr ⟨hx.1.le, hx.2⟩
    have hden := le_norm_exp_one_sub_one hx'
    change ‖G x‖ ≤ |C| / 4 + ‖A x‖ / (4 * δ)
    by_cases h₀ : x = 0
    · subst x
      simp only [G, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, div_zero, norm_zero]
      positivity
    change ‖A x / (e 1 x - 1)‖ ≤ _
    rw [norm_div]
    by_cases hsmall : |x| < δ
    · have hAx : ‖A x‖ ≤ C * |x| := by
        have h := hbound |x| ⟨abs_pos.mpr h₀, hsmall⟩
        change ‖A |x|‖ ≤ C * |x| at h
        rcases le_or_gt 0 x with hp | hn
        · simpa only [abs_of_nonneg hp] using h
        · simpa only [abs_of_neg hn, hAeven] using h
      have hxpos := abs_pos.mpr h₀
      calc
        _ ≤ (C * |x|) / (4 * |x|) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden |>.trans
            (div_le_div_of_nonneg_right hAx (by positivity))
        _ ≤ _ := by
          rw [mul_div_mul_right _ _ hxpos.ne']
          exact (div_le_div_of_nonneg_right (le_abs_self C) (by norm_num)).trans
            (le_add_of_nonneg_right (by positivity))
    · have hδden : 4 * δ ≤ ‖e 1 x - 1‖ := by linarith only [le_of_not_gt hsmall, hden]
      exact (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hδden).trans
        (le_add_of_nonneg_left (by positivity))
  have hRL (w : ℝ) :
      (𝓕 (J.indicator G)) (-w) =
        ∫ x in -b..b, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * (x : ℂ)) * G x := by
    rw [Real.fourier_real_eq_integral_exp_smul, intervalIntegral.integral_of_le hab,
      ← integral_indicator measurableSet_Ioc]
    congr 1
    funext x
    by_cases hx : x ∈ J
    · simp only [J, indicator_of_mem hx, smul_eq_mul]
      congr 2
      push_cast
      ring
    · simp [J, indicator_of_notMem hx]
  have hnat : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- The two boundary exponentials from the geometric sum tend to zero after integration.
  have hpos := (Real.zero_at_infty_fourier (J.indicator G)).comp
    ((tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right atTop 1 hnat)).mono_right atBot_le_cocompact)
  have hneg := (Real.zero_at_infty_fourier (J.indicator G)).comp (hnat.mono_right atTop_le_cocompact)
  have hosc : Tendsto (fun N : ℕ ↦ (∫ x in -b..b, e ((N : ℤ) + 1) x * G x) -
      ∫ x in -b..b, e (-(N : ℤ)) x * G x) atTop (𝓝 0) := by
    have hpos' : Tendsto (fun N : ℕ ↦ (𝓕 (J.indicator G)) (-((N : ℝ) + 1))) atTop (𝓝 0) := hpos
    have hneg' : Tendsto (fun N : ℕ ↦ (𝓕 (J.indicator G)) (-(-(N : ℝ)))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_neg] using hneg
    simpa only [hRL, Function.comp_def, Int.cast_add, Int.cast_neg, Int.cast_natCast,
      Int.cast_one, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_one, sub_zero] using hpos'.sub hneg'
  have heq (N : ℕ) :
      (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in -b..b, e m x * F x) =
        (∫ x in -b..b, e ((N : ℤ) + 1) x * G x) -
          (∫ x in -b..b, e (-(N : ℤ)) x * G x) + z := by
    have hreflect :
        (∫ x in -b..b, K N x * F (-x)) = ∫ x in -b..b, K N x * F x := by
      simpa only [hKeven, neg_neg] using
        intervalIntegral.integral_comp_neg (f := fun x ↦ K N x * F x) (a := -b) (b := b)
    have hKA :
        (∫ x in -b..b, K N x * A x) = (∫ x in -b..b, K N x * F x) - z := by
      simp only [A, mul_sub, ← mul_div_assoc, mul_add]
      rw [intervalIntegral.integral_sub, intervalIntegral.integral_div, intervalIntegral.integral_add,
        hreflect, intervalIntegral.integral_mul_const, hmass, one_mul, add_self_div_two]
      · exact hF.continuousOn_mul (hKcont N).continuousOn
      · exact hFneg.continuousOn_mul (hKcont N).continuousOn
      · exact ((hF.continuousOn_mul (hKcont N).continuousOn).add
          (hFneg.continuousOn_mul (hKcont N).continuousOn)).mul_const _
      · exact ((hKcont N).mul continuous_const).intervalIntegrable _ _
    have hKG :
        (∫ x in -b..b, K N x * A x) =
          (∫ x in -b..b, e ((N : ℤ) + 1) x * G x) -
            (∫ x in -b..b, e (-(N : ℤ)) x * G x) := by
      rw [← intervalIntegral.integral_sub
        (hG.continuousOn_mul (show Continuous (e _) by fun_prop).continuousOn)
        (hG.continuousOn_mul (show Continuous (e _) by fun_prop).continuousOn)]
      simp only [intervalIntegral.integral_of_le hab]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc,
        ((volume : Measure ℝ).restrict J).ae_ne (0 : ℝ)] with x hx h₀
      have hden : e 1 x - 1 ≠ 0 := by
        apply norm_pos_iff.mp
        exact (mul_pos (by norm_num) (abs_pos.mpr h₀)).trans_le
          (le_norm_exp_one_sub_one (abs_le.mpr ⟨hx.1.le, hx.2⟩))
      rw [← sub_mul, ← dirichlet_sum_mul_sub N x]
      change K N x * A x = K N x * (e 1 x - 1) * (A x / (e 1 x - 1))
      rw [mul_assoc, mul_div_cancel₀ _ hden]
    rw [← intervalIntegral.integral_finsetSum]
    · simp_rw [← Finset.sum_mul]
      change (∫ x in -b..b, K N x * F x) = _
      rw [← hKG, hKA, sub_add_cancel]
    · intro m _
      exact hF.continuousOn_mul (show Continuous (e m) by fun_prop).continuousOn
  change Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ∫ x in -b..b, e m x * F x) atTop (𝓝 z)
  simp_rw [heq]
  simpa only [zero_add] using hosc.add (tendsto_const_nhds (x := z))

/-- The periodization of a Schwartz function over the integer lattice is smooth. -/
theorem schwartz_contDiff_periodization (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (fun x : ℝ ↦ ∑' n : ℤ, f (x + n)) := by
  let a (u : ℝ) : ℂ := 2 * Real.pi * Complex.I * u
  let b (k : ℕ) (n : ℤ) := a n ^ k * (𝓕 f) n
  let t (n : ℤ) (x : ℝ) := (𝓕 f) n * fourier n (x : AddCircle (1 : ℝ))
  have hd (n : ℤ) (k : ℕ) :
      iteratedDeriv k (t n) = fun x : ℝ ↦ b k n * fourier n (x : AddCircle (1 : ℝ)) := by
    induction k with
    | zero => simp [b, t]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      convert ((hasDerivAt_fourier 1 n x).const_mul (b k n)).deriv using 1
      simp [b, a, pow_succ]
      ring
  have hb (k : ℕ) : Summable fun n : ℤ ↦ ‖b k n‖ := by
    have hg : (fun u : ℝ ↦ a u ^ k).HasTemperateGrowth := by
      dsimp [a]
      fun_prop
    let F := SchwartzMap.smulLeftCLM ℂ (fun u : ℝ ↦ a u ^ k) (𝓕 f)
    have hs : Summable (fun n : ℤ ↦ ‖F n‖) :=
      summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
        ((F.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite)
    simpa only [F, b, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul] using hs
  simp_rw [f.tsum_eq_tsum_fourier]
  apply contDiff_tsum (f := t) (v := fun k n ↦ ‖b k n‖)
  · intro n
    have hcoe : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    simp only [t, fourier_coe_apply]
    fun_prop
  · exact fun k _ ↦ hb k
  · intro k n x _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul]
    simp only [fourier_apply, Circle.norm_coe, mul_one, le_rfl]

end RiemannMasullo
