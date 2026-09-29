/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
import Mathlib.Topology.UrysohnsLemma

/-!
# Measurability and local bounds for the spatial gradient

Tools for the time localization in the proof of **Theorem 3.10** of F. Abedin, W. M. Feldman,
K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase
problem*, arXiv:2609.14981: for `u` continuous on an open space-time set `Ω` and locally Lipschitz
in space (Definition 3.7(i)), the pointwise spatial gradient `gradₓ u` is locally bounded and
locally integrable on `Ω`, hence a.e.-strongly measurable on `Ω`.

Definition 3.7(i) of the paper assumes `∇u ∈ L^∞_loc`; here we assume local spatial Lipschitz
bounds, uniform in time near each point, which is equivalent for continuous `u`.

## Main results

* `PerronVariational.LongTime.measurable_gradₓ_of_continuous`
* `PerronVariational.LongTime.exists_cutoff`: continuous cutoffs `θ = 1` near a compact set.
* `PerronVariational.LongTime.norm_gradₓ_le_of_lip`: local bound from the local Lipschitz bound.
* `PerronVariational.LongTime.locallyIntegrableOn_gradₓ`,
  `PerronVariational.LongTime.aestronglyMeasurable_gradₓ`.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-- `gradₓ v` is measurable for a (jointly) continuous `v`. -/
theorem measurable_gradₓ_of_continuous {v : E d × ℝ → ℝ} (hv : Continuous v) :
    Measurable (gradₓ v) := by
  have h := measurable_fderiv_with_param (𝕜 := ℝ) (f := fun (t : ℝ) (y : E d) ↦ v (y, t))
    (show Continuous fun p : ℝ × E d ↦ v (p.2, p.1) by fun_prop)
  have h2 : Measurable fun p : E d × ℝ ↦ fderiv ℝ (fun y ↦ v (y, p.2)) p.1 :=
    h.comp measurable_swap
  exact (toDual ℝ (E d)).symm.continuous.measurable.comp h2

/-- `gradₓ` only depends on the spatial germ of the time slice. -/
theorem gradₓ_congr {u v : E d × ℝ → ℝ} {p : E d × ℝ}
    (h : ∀ᶠ y in 𝓝 p.1, v (y, p.2) = u (y, p.2)) : gradₓ v p = gradₓ u p :=
  Filter.EventuallyEq.gradient_eq h

/-- A continuous cutoff equal to `1` on a thickening of a compact `K ⊆ Ω`, with support in `Ω`. -/
theorem exists_cutoff {K Ω : Set (E d × ℝ)} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ δ > 0, ∃ θ : E d × ℝ → ℝ, Continuous θ ∧ tsupport θ ⊆ Ω ∧
      ∀ p ∈ thickening δ K, θ p = 1 := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨f, hf1, hf0, -, -⟩ := exists_continuous_one_zero_of_isCompact
    (hK.cthickening (r := δ / 2)) (isOpen_thickening (δ := δ) (E := K)).isClosed_compl
    (disjoint_compl_right_iff_subset.2
      (cthickening_subset_thickening' hδ (by linarith) K))
  refine ⟨δ / 2, by positivity, f, f.continuous, ?_,
    fun p hp ↦ hf1 (thickening_subset_cthickening _ _ hp)⟩
  have hsupp : Function.support f ⊆ thickening δ K := fun p hp ↦ by
    by_contra h
    exact hp (hf0 h)
  exact (closure_mono hsupp).trans ((closure_thickening_subset_cthickening _ _).trans hδΩ)

/-- The product of a cutoff supported in `Ω` with a function continuous on `Ω` is continuous. -/
theorem continuous_cutoff_mul {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {θ u : E d × ℝ → ℝ}
    (hθ : Continuous θ) (hsupp : tsupport θ ⊆ Ω) (hu : ContinuousOn u Ω) :
    Continuous fun p ↦ θ p * u p := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ Ω
  · exact hθ.continuousAt.mul (hu.continuousAt (hΩ.mem_nhds hp))
  · have hnot : p ∉ tsupport θ := fun h ↦ hp (hsupp h)
    have h0 : (fun _ : E d × ℝ ↦ (0 : ℝ)) =ᶠ[𝓝 p] fun q ↦ θ q * u q :=
      (notMem_tsupport_iff_eventuallyEq.1 hnot).mono fun q hq ↦ by simp [hq]
    exact (continuousAt_const).congr h0

/-- The local Lipschitz bound of Definition 3.7(i) bounds `gradₓ u` near `p`. -/
theorem norm_gradₓ_le_of_lip {u : E d × ℝ → ℝ} {p : E d × ℝ} {K : ℝ} {N : Set (E d × ℝ)}
    (hN : N ∈ 𝓝 p)
    (hK : ∀ q ∈ N, ∀ q' ∈ N, q.2 = q'.2 → |u q - u q'| ≤ K * ‖q.1 - q'.1‖) :
    ∃ r > 0, ∀ q ∈ ball p r, ‖gradₓ u q‖ ≤ max K 0 := by
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨r, hr, fun q hq ↦ ?_⟩
  set S := {y : E d | (y, q.2) ∈ ball p r}
  have hS : S ∈ 𝓝 q.1 :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (show (q.1, q.2) ∈ ball p r from hq))
  have hlip : LipschitzOnWith (max K 0).toNNReal (fun y ↦ u (y, q.2)) S := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)]
    calc |u (y, q.2) - u (z, q.2)| ≤ K * ‖(y, q.2).1 - (z, q.2).1‖ :=
          hK _ (hrN hy) _ (hrN hz) rfl
      _ ≤ max K 0 * ‖y - z‖ := by gcongr; exact le_max_left _ _
  have h := norm_fderiv_le_of_lipschitzOn ℝ hS hlip
  rw [Real.coe_toNNReal _ (le_max_right _ _)] at h
  simpa [gradₓ, gradient] using h

/-- `gradₓ u` is locally integrable on `Ω` when `u` is continuous on the open set `Ω` and locally
Lipschitz in space. -/
theorem locallyIntegrableOn_gradₓ {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u Ω)
    (hlip : ∀ p ∈ Ω, ∃ K : ℝ, ∃ N ∈ 𝓝 p, ∀ q ∈ N, ∀ q' ∈ N, q.2 = q'.2 →
      |u q - u q'| ≤ K * ‖q.1 - q'.1‖) :
    LocallyIntegrableOn (gradₓ u) Ω volume := by
  intro p hp
  obtain ⟨K, N, hN, hK⟩ := hlip p hp
  obtain ⟨r, hr, hbound⟩ := norm_gradₓ_le_of_lip hN hK
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ p hp
  set ρ := min r (ε / 2)
  have hρ : 0 < ρ := lt_min hr (by linarith)
  have hcl : closedBall p ρ ⊆ Ω :=
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))).trans hεΩ
  obtain ⟨δ, hδ, θ, hθ, hθΩ, hθ1⟩ := exists_cutoff (isCompact_closedBall p ρ) hΩ hcl
  have hcont := continuous_cutoff_mul hΩ hθ hθΩ hu
  have heq : ∀ q ∈ ball p ρ, gradₓ (fun q ↦ θ q * u q) q = gradₓ u q := by
    intro q hq
    refine gradₓ_congr ?_
    have hmem : ∀ᶠ y in 𝓝 q.1, (y, q.2) ∈ thickening δ (closedBall p ρ) := by
      have : (q.1, q.2) ∈ thickening δ (closedBall p ρ) :=
        self_subset_thickening hδ _ (ball_subset_closedBall hq)
      exact (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_thickening.mem_nhds this)
    filter_upwards [hmem] with y hy
    rw [hθ1 _ hy, one_mul]
  refine ⟨ball p ρ, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p hρ), ?_⟩
  refine IntegrableOn.of_bound measure_ball_lt_top
    ((measurable_gradₓ_of_continuous hcont).aestronglyMeasurable.congr ?_) (max K 0) ?_
  · exact (ae_restrict_mem measurableSet_ball).mono fun q hq ↦ heq q hq
  · exact (ae_restrict_mem measurableSet_ball).mono fun q hq ↦
      hbound q (ball_subset_ball (min_le_left _ _) hq)

/-- `gradₓ u` is a.e.-strongly measurable on `U_∞` for a parabolic inner variational solution. -/
theorem aestronglyMeasurable_gradₓ {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ}
    {u w χ : E d × ℝ → ℝ} (h : IsParaInnerVarSolution U Q u w χ) :
    AEStronglyMeasurable (gradₓ u) (volume.restrict (UInf U)) :=
  (locallyIntegrableOn_gradₓ (hU.prod isOpen_Ioi) h.continuousOn h.locLipₓ).aestronglyMeasurable

/-- `gradₓ u` is locally integrable on `U_∞` for a parabolic inner variational solution. -/
theorem IsParaInnerVarSolution.locallyIntegrableOn_gradₓ {U : Set (E d)} (hU : IsOpen U)
    {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ} (h : IsParaInnerVarSolution U Q u w χ) :
    LocallyIntegrableOn (gradₓ u) (UInf U) volume :=
  LongTime.locallyIntegrableOn_gradₓ (hU.prod isOpen_Ioi) h.continuousOn h.locLipₓ

end LongTime

end PerronVariational

end
