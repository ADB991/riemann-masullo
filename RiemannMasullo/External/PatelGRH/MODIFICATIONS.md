# Modifications to the upstream Lean files

The imports use the local `RiemannMasullo.External.PatelGRH` module path. Upstream
declaration names and the `Masullo` namespace are retained.

- `RationalDiagonalPairing` includes the diagonal subgroup, its parametrization by ℚ,
  and the evaluation lemma from `RationalIntegralAdeles`. The finite interpolation
  argument uses an adele supported at the real place directly.
- `RationalDiagonalDual` and `RationalAdeleDual` take their topological instances from
  the caller. The comparison in Appendix A.3 supplies them.
- `RationalAdeleClassFourier` retains the quotient characters and their separation
  property. `RationalAdeleClassFourierBasis` retains the Stone–Weierstrass argument
  and the real-place test character.
- `RationalAdeleClassDual` uses Mathlib’s additive Haar measure on the compact
  quotient. Under the assumption that a character differs from every rational
  frequency, translation invariance makes each Fourier coefficient zero. The proof
  from `RationalAdelePoisson` that the orthogonal complement of their span is zero
  then applies directly. This removes the need for a normalized quotient measure
  and a Fourier series reconstruction theorem.
