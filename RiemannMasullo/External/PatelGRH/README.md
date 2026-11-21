# Rational adelic self-duality

These modules are adapted from Neal Patel’s Lean formalization of the rational adelic
pairing, at commit `d4591b6356de29272f7796e68ec0c2535935cb71`.
[Upstream source](https://github.com/thatnealpatel/grh/tree/d4591b6356de29272f7796e68ec0c2535935cb71/Proofs)

The entry point is `Masullo.rationalAdelePontryaginDualEquiv` in
[RationalAdeleDual.lean](RationalAdeleDual.lean). It identifies the rational adeles
with their compact-open character group. Appendix A.3 supplies compactness and
separation of the adelic quotient, local compactness and σ-compactness of the adeles,
and the equality with the character defined in this project.

The [source map](SOURCE_MAP.json) lists the upstream paths and SHA-256 hashes for each
file. [Modifications](MODIFICATIONS.md) records the adaptations. The original proofs
are distributed under Neal Patel’s [MIT license](LICENSE).
