module

public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.Bounds
import Mathlib.Topology.MetricSpace.Bounded

/-! # Bounds for Deligne's real gamma factor -/

public section

open Set

namespace RiemannMasullo

/-- Iterating the real gamma recurrence gains at least one factor of the absolute
imaginary part per step of length two. -/
theorem norm_Gammaℝ_mul_abs_im_pow (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    ‖Complex.Gammaℝ z‖ * |z.im| ^ n ≤
      (2 * Real.pi) ^ n * ‖Complex.Gammaℝ (z + (n : ℂ) * 2)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    let w := z + (n : ℂ) * 2
    have hw : w.im = z.im := by simp [w, Complex.mul_im]
    have hw₀ : w ≠ 0 := fun h ↦ hz (hw.symm.trans (by simp [h]))
    have hrec : ‖Complex.Gammaℝ w‖ * ‖w‖ = (2 * Real.pi) * ‖Complex.Gammaℝ (w + 2)‖ := by
      rw [Complex.Gammaℝ_add_two hw₀, norm_div, norm_div, norm_mul, Complex.norm_two,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      field_simp
    rw [pow_succ, ← mul_assoc]
    calc
      _ ≤ ((2 * Real.pi) ^ n * ‖Complex.Gammaℝ w‖) * ‖w‖ :=
        mul_le_mul ih (hw ▸ Complex.abs_im_le_norm w) (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [mul_assoc, hrec, pow_succ, mul_assoc, Nat.cast_succ]
        rw [show w + 2 = z + (↑n + 1) * 2 by dsimp [w]; ring]
        ring

/-- The real gamma factor is bounded on a strip with positive real parts, by
absolute convergence of Euler's integral uniformly between the two endpoints. -/
theorem exists_norm_Gammaℝ_le_on_strip (l u : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc l u → ‖Complex.Gammaℝ z‖ ≤ C := by
  let g (x : ℝ) := Real.pi ^ (-x / 2) * Real.Gamma (x / 2)
  have hg : ContinuousOn g (Icc l u) := by
    refine ContinuousOn.mul (by fun_prop) (Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (by fun_prop) fun x hx ↦ ?_)
    exact half_pos (hl.trans_le hx.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine ⟨C, fun z hz ↦ ?_⟩
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.div_ofNat_re, Complex.neg_re]
  have h := norm_Gamma_le_real_Gamma (z := z / 2) (by simpa using half_pos (hl.trans_le hz.1))
  rw [Complex.div_ofNat_re] at h
  calc
    _ ≤ g z.re := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg Real.pi_pos.le _)
    _ ≤ C := (le_abs_self _).trans (hC _ hz)

end RiemannMasullo
