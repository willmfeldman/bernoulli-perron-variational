/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Regular level sets are null

For any function `g` on a finite-dimensional real inner product space, the set of points `x`
where `g(x) = 0`, `g` is differentiable at `x` and `∇g(x) ≠ 0` has Haar measure zero.

Proof: by the Lebesgue density theorem (`Besicovitch.ae_tendsto_measure_inter_div`), almost every
point of a set is a density point. At a point `x` of the set, the half-ball
`{y ∈ B̄_r(x) : ⟨u, y - x⟩ > r/2}` (`u = ∇g(x)/|∇g(x)|`) lies in `{g > 0}` for small `r`, and its
measure is a fixed positive fraction of `|B̄_r(x)|`, so `x` is not a density point.

Used for the `H¹` convergence `g_ε → g₊` of the well-prepared data (item (i') of the formal
Proposition 3.8 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981). The paper's proof of
Theorem 3.9 applies Proposition 4.1, which needs this convergence, without checking it; for
strict supersolutions it rests on the set `{g = 0, ∇g = 0}`, where `∇g₊ = 0` a.e.
-/

open Set Filter Topology MeasureTheory Metric Module
open scoped Gradient ENNReal RealInnerProductSpace

@[expose] public section

namespace PerronVariational

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-- At a point where `g = 0` and `∇g ≠ 0`, a fixed fraction of small balls lies in `{g > 0}`:
there are `c > 0` and `r₀ > 0` with `μ (Z ∩ B̄_r(x)) / μ (B̄_r(x)) + c ≤ 1` for `0 < r < r₀`
whenever `Z ⊆ {g ≤ 0}`. -/
theorem exists_density_le_of_gradient_ne_zero {g : F → ℝ} {x : F} (hgx : g x = 0)
    (hd : DifferentiableAt ℝ g x) (hne : ∇ g x ≠ 0) (Z : Set F) (hZ : ∀ y ∈ Z, g y ≤ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ (Z ∩ closedBall x r) / μ (closedBall x r) + c ≤ 1 := by
  set a := ‖∇ g x‖ with ha_def
  have ha : 0 < a := norm_pos_iff.2 hne
  set u : F := a⁻¹ • ∇ g x with hu_def
  -- `g(y) = ⟨∇g(x), y - x⟩ + o(|y - x|)`
  have hL : ∀ w, fderiv ℝ g x w = a * ⟪u, w⟫ := by
    intro w
    have : fderiv ℝ g x w = ⟪∇ g x, w⟫ := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [this, hu_def, inner_smul_left]
    simp [ha.ne']
  have hlo := hd.hasFDerivAt.isLittleO.def (show 0 < a / 4 by positivity)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff_ball.1 hlo
  -- the reference half-ball at scale `1`
  set W : Set F := {y | ‖y - x‖ ≤ 1 ∧ 1 / 2 < ⟪u, y - x⟫} with hW_def
  have hu1 : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ha.ne']
  have hWpos : 0 < μ W := by
    refine lt_of_lt_of_le (measure_ball_pos μ (x + (3 / 4 : ℝ) • u)
      (by norm_num : (0 : ℝ) < 1 / 4)) (measure_mono fun y hy ↦ ?_)
    rw [mem_ball, dist_eq_norm] at hy
    have h1 : ‖y - x - (3 / 4 : ℝ) • u‖ < 1 / 4 := by
      rwa [show y - x - (3 / 4 : ℝ) • u = y - (x + (3 / 4 : ℝ) • u) by abel]
    have h2 : ‖y - x‖ ≤ ‖y - x - (3 / 4 : ℝ) • u‖ + 3 / 4 := by
      calc ‖y - x‖ = ‖(y - x - (3 / 4 : ℝ) • u) + (3 / 4 : ℝ) • u‖ := by abel_nf
        _ ≤ ‖y - x - (3 / 4 : ℝ) • u‖ + ‖(3 / 4 : ℝ) • u‖ := norm_add_le _ _
        _ = ‖y - x - (3 / 4 : ℝ) • u‖ + 3 / 4 := by rw [norm_smul, hu1]; norm_num
    have h3 : |⟪u, y - x - (3 / 4 : ℝ) • u⟫| ≤ ‖y - x - (3 / 4 : ℝ) • u‖ := by
      simpa [hu1] using abs_real_inner_le_norm u (y - x - (3 / 4 : ℝ) • u)
    have h4 : ⟪u, y - x⟫ = ⟪u, y - x - (3 / 4 : ℝ) • u⟫ + 3 / 4 := by
      rw [inner_sub_right u (y - x) ((3 / 4 : ℝ) • u), real_inner_smul_right,
        real_inner_self_eq_norm_sq, hu1]; ring
    refine ⟨by linarith, ?_⟩
    rw [h4]; linarith [(abs_le.1 h3).1]
  have hB1 : μ (ball (0 : F) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hB1' : μ (ball (0 : F) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  refine ⟨μ W / μ (ball (0 : F) 1), (ENNReal.div_pos hWpos.ne' hB1).ne', ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
  have hr0 := hr.1
  -- the half-ball at scale `r`
  set H : Set F := {y | ‖y - x‖ ≤ r ∧ r / 2 < ⟪u, y - x⟫} with hH_def
  have hHmeas : MeasurableSet H := by
    refine (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet.inter ?_
    have hc : Continuous fun y : F ↦ ⟪u, y - x⟫ :=
      continuous_const.inner (continuous_id.sub continuous_const)
    exact measurableSet_lt measurable_const hc.measurable
  have hHpos : ∀ y ∈ H, 0 < g y := by
    intro y hy
    have hy1 : y ∈ ball x r₀ := by
      rw [mem_ball, dist_eq_norm]; exact hy.1.trans_lt hr.2
    have hlit := hball y hy1
    rw [hgx, sub_zero, Real.norm_eq_abs, hL] at hlit
    have := (abs_le.1 hlit).1
    have hya : a * (r / 2) < a * ⟪u, y - x⟫ := mul_lt_mul_of_pos_left hy.2 ha
    nlinarith [hy.1, norm_nonneg (y - x)]
  have hdisj : Disjoint (Z ∩ closedBall x r) H := by
    rw [disjoint_left]
    intro y hy hyH
    exact absurd (hZ y hy.1) (not_le.2 (hHpos y hyH))
  have hsub : Z ∩ closedBall x r ∪ H ⊆ closedBall x r := by
    refine union_subset inter_subset_right fun y hy ↦ ?_
    rw [mem_closedBall, dist_eq_norm]; exact hy.1
  have hsum : μ (Z ∩ closedBall x r) + μ H ≤ μ (closedBall x r) := by
    rw [← measure_union hdisj hHmeas]; exact measure_mono hsub
  -- `μ H ≥ r^n μ W`
  have hHW : AffineMap.homothety x r '' W ⊆ H := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    refine ⟨?_, ?_⟩
    · rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [hy.1]
    · rw [add_sub_cancel_right, real_inner_smul_right]
      nlinarith [hy.2]
  have hHge : ENNReal.ofReal (r ^ finrank ℝ F) * μ W ≤ μ H := by
    have := measure_mono (μ := μ) hHW
    rwa [Measure.addHaar_image_homothety, abs_of_nonneg (by positivity)] at this
  have hBr : μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ F) * μ (ball 0 1) :=
    Measure.addHaar_closedBall μ x hr0.le
  have hrn : ENNReal.ofReal (r ^ finrank ℝ F) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hc : μ W / μ (ball (0 : F) 1) ≤ μ H / μ (closedBall x r) := by
    rw [hBr, ← ENNReal.mul_div_mul_left (μ W) _ hrn ENNReal.ofReal_ne_top]
    exact ENNReal.div_le_div_right hHge _
  calc μ (Z ∩ closedBall x r) / μ (closedBall x r) + μ W / μ (ball (0 : F) 1)
      ≤ μ (Z ∩ closedBall x r) / μ (closedBall x r) + μ H / μ (closedBall x r) :=
        add_le_add le_rfl hc
    _ = (μ (Z ∩ closedBall x r) + μ H) / μ (closedBall x r) := ENNReal.div_add_div_same
    _ ≤ 1 := ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hsum)

/-- **Regular level sets are null**: `{x | g x = 0, g differentiable at x, ∇g(x) ≠ 0}` has Haar
measure zero. -/
theorem measure_zero_levelSet_gradient_ne_zero (g : F → ℝ) :
    μ {x | g x = 0 ∧ DifferentiableAt ℝ g x ∧ ∇ g x ≠ 0} = 0 := by
  set Z := {x | g x = 0 ∧ DifferentiableAt ℝ g x ∧ ∇ g x ≠ 0}
  have hdens := Besicovitch.ae_tendsto_measure_inter_div μ Z
  have hnot : ∀ x ∈ Z, ¬ Tendsto (fun r ↦ μ (Z ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1) := by
    intro x hx htend
    obtain ⟨c, hc, hev⟩ := exists_density_le_of_gradient_ne_zero μ hx.1 hx.2.1 hx.2.2 Z
      fun y hy ↦ hy.1.le
    have hlim : 1 + c ≤ 1 := le_of_tendsto (htend.add tendsto_const_nhds) hev
    have : c ≤ 0 := ENNReal.le_of_add_le_add_left ENNReal.one_ne_top (by simpa using hlim)
    exact hc (le_antisymm this bot_le)
  have h0 : μ.restrict Z Z = 0 := by
    rw [ae_iff] at hdens
    exact measure_mono_null (fun x hx ↦ hnot x hx) hdens
  rwa [Measure.restrict_apply_self] at h0

end PerronVariational

end
