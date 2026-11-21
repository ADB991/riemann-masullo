module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UrysohnsLemma

public section

open MeasureTheory Set Topology
open scoped ENNReal

namespace RiemannMasullo

/-- For a regular measure on a locally compact Hausdorff space, continuous compactly
supported functions approximate every integrable function in the integral norm. -/
theorem exists_hasCompactSupport_integral_sub_le_of_locallyCompact {X E : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} [μ.Regular]
    {f : X → E} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → E, HasCompactSupport g ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε ∧
      Continuous g ∧ Integrable g μ := by
  -- Approximate finite-measure indicators by a bump between compact and open sets.
  have hIndicator (c : E) (S : Set X) (hS : MeasurableSet S) (hμS : μ S < ∞)
      (δ : ℝ≥0∞) (hδ : δ ≠ 0) :
      ∃ g : X → E, eLpNorm (g - S.indicator (fun _ ↦ c)) 1 μ ≤ δ ∧
        Continuous g ∧ HasCompactSupport g := by
    obtain ⟨η, hη, hδ'⟩ := exists_eLpNorm_indicator_le (μ := μ) (p := 1) ENNReal.one_ne_top c hδ
    have hη' : (0 : ℝ≥0∞) < (η : ℝ≥0∞) / 2 :=
      ENNReal.half_pos (ENNReal.coe_pos.2 hη).ne'
    obtain ⟨K, hKS, hK, hKclosed, hSK⟩ :=
      hS.exists_isCompact_isClosed_sdiff_lt hμS.ne hη'.ne'
    obtain ⟨U, hSU, hU, _, hUS⟩ := hS.exists_isOpen_sdiff_lt hμS.ne hη'.ne'
    obtain ⟨b, hbK, hbCompact, hbU, hbBound⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hU (hKS.trans hSU)
    have hUK : μ (U \ K) ≤ η := by
      rw [← sdiff_union_sdiff_cancel hSU hKS]
      exact (measure_union_le _ _).trans <| (add_le_add hUS.le hSK.le).trans_eq
        (ENNReal.add_halves _)
    have hbCont : Continuous (fun x ↦ b x • c) := b.continuous.smul continuous_const
    have hbSupp : HasCompactSupport (fun x ↦ b x • c) :=
      HasCompactSupport.intro hbCompact fun x hx ↦ by
        simp [image_eq_zero_of_notMem_tsupport hx]
    refine ⟨fun x ↦ b x • c, ?_, hbCont, hbSupp⟩
    have hbMeas : AEStronglyMeasurable (fun x ↦ b x • c) μ :=
      (hbCont.stronglyMeasurable_of_hasCompactSupport hbSupp).aestronglyMeasurable
    refine (eLpNorm_mono (hbMeas.sub (aestronglyMeasurable_const.indicator hS)) ?_).trans
      (hδ' _ hUK (hU.measurableSet.diff hKclosed.measurableSet).nullMeasurableSet)
    intro x
    by_cases hxK : x ∈ K
    · simp [hbK hxK, hKS hxK, hxK]
    by_cases hxU : x ∈ U
    · simp only [Pi.sub_apply, indicator_of_mem (show x ∈ U \ K from ⟨hxU, hxK⟩)]
      by_cases hxS : x ∈ S
      · rw [indicator_of_mem hxS]
        calc
          _ = ‖(b x - 1) • c‖ := by rw [sub_smul, one_smul]
          _ ≤ _ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hbBound x).2)]
            exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [(hbBound x).1])
      · rw [indicator_of_notMem hxS, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (hbBound x).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (hbBound x).2
    · have hb0 : b x = 0 := image_eq_zero_of_notMem_tsupport (fun hx ↦ hxU (hbU hx))
      simp [hb0, show x ∉ S from fun hx ↦ hxU (hSU hx), hxU]
  obtain ⟨g, hg, hgCont, hgSupp⟩ :=
    (memLp_one_iff_integrable.2 hf).induction_dense ENNReal.one_ne_top
      (fun g ↦ Continuous g ∧ HasCompactSupport g)
      (fun c S hS hμS δ hδ ↦ hIndicator c S hS hμS δ hδ)
      (fun _ _ hf hg ↦ ⟨hf.1.add hg.1, hf.2.add hg.2⟩) (ENNReal.ofReal_pos.2 hε).ne'
  have hgInt : Integrable g μ :=
    memLp_one_iff_integrable.1 (hgCont.memLp_of_hasCompactSupport hgSupp)
  refine ⟨g, hgSupp, ?_, hgCont, hgInt⟩
  change (∫ x, ‖(f - g) x‖ ∂μ) ≤ ε
  rw [integral_norm_eq_lintegral_eNorm (hf.sub hgInt).aestronglyMeasurable]
  rw [eLpNorm_one_eq_lintegral_eNorm (hf.sub hgInt).aestronglyMeasurable] at hg
  simpa [ENNReal.toReal_ofReal hε.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hg

end RiemannMasullo
