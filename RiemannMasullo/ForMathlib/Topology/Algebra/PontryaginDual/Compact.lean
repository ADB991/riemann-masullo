module

public import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.Equicontinuity

public section

open Filter Set Topology
open scoped UniformConvergence

namespace RiemannMasullo

/-- Characters that map a fixed identity neighborhood into the open right semicircle
have compact closure in the Pontryagin dual. -/
theorem isCompact_closure_pontryaginDual_mapsTo_centeredArc {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    IsCompact (closure {χ : PontryaginDual G | MapsTo χ U (Circle.centeredArc (Real.pi / 2))}) := by
  let S := {χ : PontryaginDual G | MapsTo χ U (Circle.centeredArc (Real.pi / 2))}
  let V (n : ℕ) := Circle.centeredArc (Real.pi / 2 ^ (n + 1))
  have hV (n : ℕ) {z : Circle} (hz : z ∈ V n) (hz₂ : z ^ 2 ∈ V n) : z ∈ V (n + 1) := by
    have hπ : Real.pi / 2 ^ (n + 1) ≤ Real.pi :=
      div_le_self Real.pi_nonneg (one_le_pow₀ one_le_two)
    have hHalf : z ∈ Circle.centeredArc (Real.pi / 2) :=
      Circle.centeredArc_mono (by gcongr; exact le_self_pow₀ one_le_two n.succ_ne_zero) hz
    simpa only [V, pow_succ (2 : ℝ) (n + 1), div_div, Nat.cast_ofNat] using
      (Circle.mem_centeredArc_div hπ (n := 2) (by simpa using hHalf) hz₂)
  -- Squaring gives a smaller uniform arc bound on a smaller identity neighborhood.
  have hSmall (n : ℕ) : ∀ᶠ x in 𝓝 (1 : G), ∀ χ : S, χ.val x ∈ V n := by
    induction n with
    | zero =>
      filter_upwards [hU] with x hx χ
      simpa [V] using χ.property hx
    | succ n ih =>
      have hSq : Tendsto (fun x : G ↦ x ^ 2) (𝓝 1) (𝓝 1) := by
        simpa using (continuous_pow (M := G) 2).tendsto (1 : G)
      filter_upwards [ih, hSq.eventually ih] with x hx hx₂ χ
      exact hV n (hx χ) (map_pow χ.val x 2 ▸ hx₂ χ)
  have hEqui : Equicontinuous (fun χ : S ↦ (χ.val : G → Circle)) := by
    apply equicontinuous_of_equicontinuousAt_one Subtype.val
    rw [Circle.hasBasis_centeredArc_div_two_pow.uniformity_of_nhds_one.equicontinuousAt_iff_right]
    intro n _
    simpa [V, Function.comp_def, map_one] using hSmall n
  let : T2Space (G →ᵤ[{K : Set G | IsCompact K}] Circle) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr fun x ↦
      mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hEmbedding : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set G | IsCompact K} ∘ ((↑) : PontryaginDual G → G → Circle)) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding.comp
      (ContinuousMonoidHom.isClosedEmbedding_toContinuousMap G Circle)
  exact ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ hK ↦ hK) hEmbedding
    (fun K _ ↦ hEqui.equicontinuousOn K) (fun _ _ _ _ ↦ ⟨univ, isCompact_univ, fun _ _ ↦ trivial⟩)

end RiemannMasullo
