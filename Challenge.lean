import Statements

/-!
# Challenge

The theorems Comparator checks `Main.lean` against. This file and `Statements.lean` import only
Mathlib and must stay free of project code.
-/

/-- The headline claim, stated with Mathlib's definition only. -/
theorem riemannHypothesis : RiemannHypothesis := by sorry

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := by sorry

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := by sorry

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := by sorry

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := by sorry

theorem dedekindZeta_zeros_re : DedekindZetaZerosOnLine := by sorry

theorem heckeLFunction_zeros_re : HeckeLZerosOnLine := by sorry
