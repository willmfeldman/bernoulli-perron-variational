/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Setting
import Mathlib.Order.CompletePartialOrder

/-!
# Uniform exterior balls for a `C²` domain

The uniform exterior ball condition (A.12) in the proof of Proposition A.8 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981.

For `U = {ρ < 0}` with `ρ ∈ C²` and `∇ρ ≠ 0` on `∂U`, `U` bounded, there is `ρ₀ > 0` such
that every boundary point `x₀` has an exterior ball `B_{ρ₀}(y₀)`, `|y₀ - x₀| = ρ₀`, with the
quantitative separation `|x - y₀|² ≥ ρ₀² + ½|x - x₀|²` for all `x ∈ Ū` (the paper's (A.12)).
The paper assumes that `∂U` is a `C²` hypersurface; here `U = {ρ < 0}` as above, which is the
standard equivalent description used throughout this library.

The proof follows the paper: a uniform second-order Taylor bound for `ρ` on a ball containing `Ū`
and a positive lower bound for `|∇ρ|` on the compact set `∂U`.

Also: `Setting.mem_of_norm_sub_lt_infDist` (balls avoiding `∂U` around points of `U` lie in `U`).
-/

open Set Filter Topology Metric
open scoped Gradient RealInnerProductSpace

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- Uniform first-order Taylor bound for a `C²` function on a closed ball. -/
theorem exists_taylor_bound_closedBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [ProperSpace F] {g : F → ℝ} (hg : ContDiff ℝ 2 g) (c : F) (R : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
      |g y - g x - fderiv ℝ g x (y - x)| ≤ K * ‖y - x‖ ^ 2 := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdf : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have hdf1 : Differentiable ℝ (fderiv ℝ g) := hdf.differentiable (by norm_num)
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn
    (hdf.continuous_fderiv (by norm_num)).continuousOn
  set K := max K₀ 0 with hK
  refine ⟨K, le_max_right _ _, fun x hx y hy ↦ ?_⟩
  -- `‖Dg(z) - Dg(x)‖ ≤ K ‖z - x‖` on the ball
  have hD : ∀ z ∈ closedBall c R, ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ K * ‖z - x‖ := fun z hz ↦
    (convex_closedBall c R).norm_image_sub_le_of_norm_fderiv_le (fun w _ ↦ hdf1 w)
      (fun w hw ↦ (hK₀ w hw).trans (le_max_left _ _)) hx hz
  set r := ‖y - x‖ with hr
  set s := closedBall c R ∩ closedBall x r with hs
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := g)
    (f' := fderiv ℝ g) (φ := fderiv ℝ g x) (s := s) (C := K * r) (x := x) (y := y)
    (fun z _ ↦ (hg1 z).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz ↦ (hD z hz.1).trans (mul_le_mul_of_nonneg_left
      (by rw [← dist_eq_norm]; exact mem_closedBall.1 hz.2) (le_max_right _ _)))
    ((convex_closedBall c R).inter (convex_closedBall x r))
    ⟨hx, mem_closedBall_self (norm_nonneg _)⟩
    ⟨hy, by simp [hr, dist_eq_norm]⟩
  rw [Real.norm_eq_abs] at key
  calc _ ≤ K * r * ‖y - x‖ := key
    _ = K * ‖y - x‖ ^ 2 := by rw [hr]; ring

/-- A continuous function which is positive on a compact set has a positive lower bound there. -/
theorem exists_pos_forall_le_of_isCompact {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ m > 0, ∀ x ∈ K, m ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun x hx ↦ hx.elim⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x₀, hpos x₀ hx₀, fun x hx ↦ hmin hx⟩

/-- **Uniform exterior ball** (the paper's (A.12)): there is `ρ₀ > 0` such that for
every `x₀ ∈ ∂U` there is `y₀` with `|x₀ - y₀| = ρ₀` and `ρ₀² + ½|x - x₀|² ≤ |x - y₀|²` for all
`x ∈ Ū`. -/
theorem Setting.exists_uniformExteriorBall (S : Setting d) :
    ∃ ρ₀ > 0, ∀ x₀ ∈ frontier S.U, ∃ y₀ : E d, ‖x₀ - y₀‖ = ρ₀ ∧
      ∀ x ∈ closure S.U, ρ₀ ^ 2 + ‖x - x₀‖ ^ 2 / 2 ≤ ‖x - y₀‖ ^ 2 := by
  obtain ⟨ρ, hρ, hUρ, hgrad⟩ := S.c2
  obtain ⟨R, hR⟩ := S.isBounded.isCompact_closure.isBounded.subset_closedBall (0 : E d)
  obtain ⟨K, hK0, hK⟩ := exists_taylor_bound_closedBall hρ 0 R
  -- `|∇ρ| ≥ m > 0` on `∂U`
  have hgc : Continuous (∇ ρ) := by
    have : ∇ ρ = fun x ↦ (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ ρ x) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp
      (hρ.continuous_fderiv (by norm_num))
  have hfc : IsCompact (frontier S.U) :=
    S.isBounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨m, hm, hmle⟩ := exists_pos_forall_le_of_isCompact hfc
    (continuous_norm.comp hgc).continuousOn fun x hx ↦ norm_pos_iff.2 (hgrad x hx)
  set C := K / m with hC
  have hC0 : 0 ≤ C := div_nonneg hK0 hm.le
  set ρ₀ := 1 / (4 * C + 4) with hρ₀
  have hρ₀0 : 0 < ρ₀ := by positivity
  have hρC : 2 * ρ₀ * C ≤ 1 / 2 := by
    rw [hρ₀, show 2 * (1 / (4 * C + 4)) * C = 2 * C / (4 * C + 4) by ring,
      div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  refine ⟨ρ₀, hρ₀0, fun x₀ hx₀ ↦ ?_⟩
  -- `ρ ≤ 0` on `Ū`, `ρ(x₀) ≥ 0`
  have hρcl : ∀ x ∈ closure S.U, ρ x ≤ 0 := by
    have : closure S.U ⊆ {x | ρ x ≤ 0} :=
      closure_minimal (by rw [hUρ]; exact fun x (hx : ρ x < 0) ↦ (le_of_lt hx : ρ x ≤ 0))
        (isClosed_le hρ.continuous continuous_const)
    exact fun x hx ↦ this hx
  have hρx₀ : 0 ≤ ρ x₀ := by
    have hx₀U : x₀ ∉ S.U := by
      rw [S.isOpen.frontier_eq] at hx₀; exact hx₀.2
    rw [hUρ] at hx₀U
    exact not_lt.1 hx₀U
  set a := ‖∇ ρ x₀‖ with ha
  have ha0 : m ≤ a := hmle x₀ hx₀
  have hapos : 0 < a := hm.trans_le ha0
  set n : E d := a⁻¹ • ∇ ρ x₀ with hn
  have hn1 : ‖n‖ = 1 := by
    rw [hn, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hapos.ne']
  have hfd : ∀ v, fderiv ℝ ρ x₀ v = a * ⟪n, v⟫ := fun v ↦ by
    have : fderiv ℝ ρ x₀ v = ⟪∇ ρ x₀, v⟫ := by
      simp [gradient, InnerProductSpace.toDual_symm_apply]
    rw [this, hn, inner_smul_left]
    simp [hapos.ne']
  -- `⟨n, x - x₀⟩ ≤ C |x - x₀|²` on `Ū`
  have hx₀cl : x₀ ∈ closure S.U := frontier_subset_closure hx₀
  have hkey : ∀ x ∈ closure S.U, ⟪n, x - x₀⟫ ≤ C * ‖x - x₀‖ ^ 2 := by
    intro x hx
    have h1 := hK x₀ (hR hx₀cl) x (hR hx)
    rw [hfd] at h1
    have h2 := (abs_le.1 h1).1
    have h3 : a * ⟪n, x - x₀⟫ ≤ K * ‖x - x₀‖ ^ 2 := by linarith [hρcl x hx]
    have h4 : m * ⟪n, x - x₀⟫ ≤ K * ‖x - x₀‖ ^ 2 := by
      rcases le_or_gt ⟪n, x - x₀⟫ 0 with h | h
      · nlinarith [sq_nonneg ‖x - x₀‖]
      · nlinarith
    rw [hC, div_mul_eq_mul_div, le_div_iff₀ hm]
    linarith
  refine ⟨x₀ + ρ₀ • n, ?_, fun x hx ↦ ?_⟩
  · rw [show x₀ - (x₀ + ρ₀ • n) = -(ρ₀ • n) by abel, norm_neg, norm_smul, hn1,
      Real.norm_eq_abs, abs_of_pos hρ₀0, mul_one]
  · have e : x - (x₀ + ρ₀ • n) = (x - x₀) - ρ₀ • n := by abel
    rw [e, norm_sub_sq_real (x - x₀) (ρ₀ • n), norm_smul, Real.norm_eq_abs, abs_of_pos hρ₀0, hn1,
      real_inner_smul_right, real_inner_comm]
    have h1 := hkey x hx
    have h2 : 2 * ρ₀ * ⟪n, x - x₀⟫ ≤ 1 / 2 * ‖x - x₀‖ ^ 2 := by
      calc 2 * ρ₀ * ⟪n, x - x₀⟫ ≤ 2 * ρ₀ * (C * ‖x - x₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (2 * ρ₀ * C) * ‖x - x₀‖ ^ 2 := by ring
        _ ≤ 1 / 2 * ‖x - x₀‖ ^ 2 := mul_le_mul_of_nonneg_right hρC (sq_nonneg _)
    nlinarith

/-- Around a point `x ∈ U`, the ball of radius `dist(x, ∂U)` lies in `U`. -/
theorem Setting.mem_of_norm_sub_lt_infDist (S : Setting d) {x z : E d} (hx : x ∈ S.U)
    (hz : ‖z - x‖ < infDist x (frontier S.U)) : z ∈ S.U := by
  set r := infDist x (frontier S.U)
  have hB : ball x r ⊆ S.U := by
    have hdisj : Disjoint S.U (closure S.U)ᶜ :=
      disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)
    refine (convex_ball x r).isPreconnected.subset_left_of_subset_union S.isOpen
      isClosed_closure.isOpen_compl hdisj (fun w hw ↦ ?_)
      ⟨x, mem_ball_self ((norm_nonneg _).trans_lt (by simpa using hz)), hx⟩
    by_cases hwc : w ∈ closure S.U
    · left
      rw [closure_eq_interior_union_frontier, S.isOpen.interior_eq] at hwc
      rcases hwc with h | h
      · exact h
      · exfalso
        have := infDist_le_dist_of_mem (x := x) h
        rw [mem_ball, dist_comm] at hw
        linarith
    · right; exact hwc
  exact hB (by rw [mem_ball, dist_eq_norm]; exact hz)

end PerronVariational

end
