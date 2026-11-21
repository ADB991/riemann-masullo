module

public import RiemannMasullo.External.PatelGRH.RationalAdeleClassFourierBasis
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral

/-! # Exhaustion of the adele class characters by rational frequencies -/

open NumberField MeasureTheory Topology
open scoped ComplexConjugate InnerProductSpace

set_option linter.concreteInstances false

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal

variable [CompactSpace Cq] [T2Space Cq]

/-- A continuous circle character of the additive adele classes is a rational
frequency: Otherwise every Fourier coefficient vanishes by Haar translation. -/
public theorem exists_rationalAdeleClassChar_eq (θ : Cq →+ Additive Circle)
    (hθ : Continuous θ) :
    ∃ r : ℚ, ∀ c : Cq, rationalAdeleClassChar r c = (θ c).toMul.val := by
  let : MeasurableSpace Cq := borel Cq
  let : BorelSpace Cq := ⟨rfl⟩
  let μ : Measure Cq := Measure.addHaar
  let T : C(Cq, ℂ) →L[ℂ] Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ
  let g : C(Cq, ℂ) := ⟨fun c ↦ (θ c).toMul.val, continuous_subtype_val.comp hθ⟩
  have hg_add (c d : Cq) : g (c + d) = g c * g d := by
    change (↑(θ (c + d)).toMul : ℂ) = _
    rw [map_add]
    exact Circle.coe_mul _ _
  have hg_norm (c : Cq) : ‖g c‖ = 1 := Circle.norm_coe _
  change ∃ r : ℚ, ∀ c : Cq, rationalAdeleClassChar r c = g c
  by_contra! hn
  have hcoeff (r : ℚ) : ⟪T (rationalAdeleClassCharMap r), T g⟫_ℂ = 0 := by
    let f (c : Cq) := g c * conj (rationalAdeleClassChar r c)
    obtain ⟨d, hd⟩ := hn r
    have hχ (c : Cq) : rationalAdeleClassChar r c ≠ 0 := by
      intro h
      simpa [h] using norm_rationalAdeleClassChar r c
    have hne : f d ≠ 1 := by
      rw [show f d = g d * (rationalAdeleClassChar r d)⁻¹ from
        congrArg (g d * ·) (Complex.inv_eq_conj (norm_rationalAdeleClassChar r d)).symm,
        ← div_eq_mul_inv]
      exact fun h ↦ hd (div_eq_one_iff_eq (hχ d) |>.mp h).symm
    have hshift (c : Cq) : f (d + c) = f d * f c := by
      dsimp [f]
      rw [hg_add, AddChar.map_add_eq_mul, map_mul]
      ring
    have ht := integral_add_left_eq_self (μ := μ) f d
    simp only [hshift, integral_const_mul] at ht
    rw [ContinuousMap.inner_toLp]
    simp only [rationalAdeleClassCharMap_apply]
    change (∫ c, f c ∂μ) = 0
    by_contra hz
    apply hne
    exact mul_right_cancel₀ hz (ht.trans (one_mul _).symm)
  let F : C(Cq, ℂ) →L[ℂ] ℂ := (innerSL ℂ (T g)).comp T
  have hspan : Submodule.span ℂ (Set.range rationalAdeleClassCharMap) ≤ LinearMap.ker F.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    change ⟪T g, T (rationalAdeleClassCharMap r)⟫_ℂ = 0
    rw [← inner_conj_symm, hcoeff, map_zero]
  have hclosed : IsClosed (LinearMap.ker F.toLinearMap : Set C(Cq, ℂ)) :=
    isClosed_eq F.continuous continuous_const
  have hmem : g ∈ LinearMap.ker F.toLinearMap :=
    closure_minimal hspan hclosed (by rw [closure_span_rationalAdeleClassCharMap]; trivial)
  have hzero : T g = 0 := inner_self_eq_zero.mp hmem
  have hz : g = 0 := (ContinuousMap.toLp_injective μ) (hzero.trans (map_zero T).symm)
  exact one_ne_zero (by simpa [hz] using (hg_norm 0).symm : (1 : ℝ) = 0)

end Masullo
