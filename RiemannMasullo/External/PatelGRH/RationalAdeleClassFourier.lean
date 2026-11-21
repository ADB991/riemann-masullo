module

public import RiemannMasullo.External.PatelGRH.RationalDiagonalPairing
public import Mathlib.Topology.Algebra.Group.Quotient
public import RiemannMasullo.External.PatelGRH.RationalAdeleCharacter

import RiemannMasullo.External.PatelGRH.RationalAdeleAnnihilator

/-! # Characters of the rational adele classes -/

open NumberField Topology
open scoped ComplexConjugate

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "C" => A ⧸ rationalDiagonal
local notation "π" => (QuotientAddGroup.mk : A → C)
local notation "ι" => algebraMap ℚ A

private theorem frequency_invariant (r : ℚ) {a b : A} (h : π a = π b) :
    rationalAdeleAddChar (a * ι r) = rationalAdeleAddChar (b * ι r) := by
  obtain ⟨q, hq⟩ := QuotientAddGroup.eq_iff_sub_mem.mp h
  have heq : a = ι q + b := (sub_eq_iff_eq_add.mp hq.symm)
  rw [heq, add_mul, AddChar.map_add_eq_mul, ← map_mul (ι),
    rationalAdeleAddChar_algebraMap, one_mul]

/-- The quotient character obtained from the upstairs frequency `r ∈ ℚ`. -/
public noncomputable def rationalAdeleClassChar (r : ℚ) : AddChar C ℂ where
  toFun := Quotient.lift (fun a : A ↦ rationalAdeleAddChar (a * ι r))
    (fun _ _ h ↦ frequency_invariant r (Quotient.sound h))
  map_zero_eq_one' := by
    change rationalAdeleAddChar ((0 : A) * ι r) = 1
    rw [zero_mul, AddChar.map_zero_eq_one]
  map_add_eq_mul' c e := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective e
    change rationalAdeleAddChar ((a + b) * ι r) = _
    rw [add_mul, AddChar.map_add_eq_mul]
    rfl

@[simp]
public theorem rationalAdeleClassChar_mk (r : ℚ) (a : A) :
    rationalAdeleClassChar r (π a) = rationalAdeleAddChar (a * ι r) := by
  unfold rationalAdeleClassChar
  rfl

public theorem continuous_rationalAdeleClassChar (r : ℚ) :
    Continuous (rationalAdeleClassChar r : C → ℂ) :=
  (QuotientAddGroup.isQuotientMap_mk rationalDiagonal).continuous_iff.mpr
    (continuous_rationalAdeleAddChar.comp (continuous_id.mul continuous_const))

public theorem norm_rationalAdeleClassChar (r : ℚ) (c : C) :
    ‖rationalAdeleClassChar r c‖ = 1 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  exact norm_rationalAdeleAddChar (a * ι r)

/-- The diagonal rational frequencies distinguish the points of the quotient. -/
public theorem rationalAdeleClassChar_separates {c e : C} (h : c ≠ e) :
    ∃ r : ℚ, rationalAdeleClassChar r c ≠ rationalAdeleClassChar r e := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective e
  by_contra! heq
  apply h
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  obtain ⟨q, hq⟩ := (rationalAdele_orthogonal_iff (a - b)).mp (fun r ↦ by
    rw [sub_mul, AddChar.map_sub_eq_div, ← rationalAdeleClassChar_mk,
      ← rationalAdeleClassChar_mk, heq, div_self]
    exact fun hz ↦ by simpa [hz] using norm_rationalAdeleClassChar r (π b))
  exact ⟨q, hq.symm⟩

end Masullo
