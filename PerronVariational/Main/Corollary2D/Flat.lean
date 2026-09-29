/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Appendix.Nondegeneracy
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder

/-!
# Corollary 1.2: flatness from half-plane blow-ups

Part of **Corollary 1.2** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: if a blow-up at a
free boundary point is a half-plane solution, the solution is flat there
(`flat_of_halfPlane_blowup`, `flat_or_pos_of_halfPlane_blowup`).

The ε-regularity theory needs two-sided flatness `(x·e - ε)₊ ≤ u ≤ (x·e + ε)₊`. The paper's proof
sketch of Corollary 1.2 derives it from locally uniform convergence of the rescalings to the
half-plane solution, which gives only the lower bound. Here the upper bound (`u = 0` on the far
side) comes from non-degeneracy.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian NNReal RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Corollary2D

variable {d : ℕ}

section Flat

theorem blowup_inv_smul {u : E d → ℝ} {x₀ : E d} {s : ℝ} (hs : 0 < s) (y : E d) :
    blowup u x₀ s (s⁻¹ • (y - x₀)) = u y / s := by
  simp [blowup, smul_smul, mul_inv_cancel₀ hs.ne']

/-- **Non-degenerate blow-ups are nonzero.** If `u` is non-degenerate at `x₀`, no blow-up limit
of `u` at `x₀` vanishes identically. -/
theorem exists_ne_zero_of_isBlowupLimit {u : E d → ℝ} {x₀ : E d} (hnd : IsNondegenerateAt u x₀)
    {v : E d → ℝ} (hv : IsBlowupLimit u x₀ v) : ∃ y, v y ≠ 0 := by
  obtain ⟨c, hc, ρ, hρ, hnd⟩ := hnd
  obtain ⟨r, hr, hr0, hconv⟩ := hv
  have hK := (tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) (closedBall 0 1)
    (isCompact_closedBall 0 1)
  obtain ⟨n, hn1, hn2⟩ := ((Metric.tendstoUniformlyOn_iff.1 hK (c / 2) (half_pos hc)).and
    ((tendsto_order.1 hr0).2 ρ hρ)).exists
  obtain ⟨y, hy, hcy⟩ := hnd (r n) (hr n) hn2.le
  set w := (r n)⁻¹ • (y - x₀)
  have hw : w ∈ closedBall (0 : E d) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (hr n), ← dist_eq_norm]
    rw [mem_closedBall] at hy
    rw [inv_mul_le_iff₀ (hr n)]; linarith
  have h1 := hn1 w hw
  rw [blowup_inv_smul (hr n), Real.dist_eq] at h1
  have h2 : c ≤ u y / r n := by rw [le_div_iff₀ (hr n)]; linarith
  refine ⟨w, fun h ↦ ?_⟩
  rw [h, zero_sub, abs_neg, abs_of_nonneg (by linarith)] at h1
  linarith

/-- The core of the flatness step, for `ε ≤ 1`. -/
theorem flat_of_halfPlane_blowup_aux {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hnn : ∀ x ∈ U, 0 ≤ u x) {x₀ : E d} (hx₀ : x₀ ∈ U)
    (hnd : IsUniformlyNondegenerateNear U u x₀) {q : ℝ} (hq : 0 < q) {e : E d} (he : ‖e‖ = 1)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hconv : TendstoLocallyUniformly (fun n ↦ blowup u x₀ (r n)) (fun y ↦ q * max ⟪y, e⟫ 0)
      atTop) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ s, 0 < s ∧ s ≤ ε ∧ ball x₀ s ⊆ U ∧ ∀ y ∈ ball x₀ s,
      q * max (⟪y - x₀, e⟫ - ε * s) 0 ≤ u y ∧ u y ≤ q * max (⟪y - x₀, e⟫ + ε * s) 0 := by
  obtain ⟨c, hc, ρ, hρ, hnd⟩ := hnd
  obtain ⟨η, hη, hηU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set δ := min (q * ε / 2) (c * ε / 8) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ q * ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ c * ε / 8 := min_le_right _ _
  have hK := (tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) (closedBall 0 2)
    (isCompact_closedBall 0 2)
  have hsmall : ∀ᶠ n in atTop, r n < min (min ρ ε) η :=
    (tendsto_order.1 hr0).2 _ (lt_min (lt_min hρ hε) hη)
  obtain ⟨n, hn1, hn2⟩ := ((Metric.tendstoUniformlyOn_iff.1 hK δ hδ0).and hsmall).exists
  set s := r n with hs_def
  have hs : 0 < s := hr n
  have hsρ : s < ρ := (hn2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hsε : s < ε := (hn2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hsη : s < η := hn2.trans_le (min_le_right _ _)
  have hballU : ball x₀ s ⊆ U := (ball_subset_ball hsη.le).trans hηU
  refine ⟨s, hs, hsε.le, hballU, fun y hy ↦ ?_⟩
  -- blown-up coordinates
  have hyU : y ∈ U := hballU hy
  set w := s⁻¹ • (y - x₀) with hw_def
  have hinner : ⟪y - x₀, e⟫ = s * ⟪w, e⟫ := by
    rw [hw_def, inner_smul_left]
    simp [mul_inv_cancel_left₀ hs.ne']
  have hwn : ‖w‖ < 1 := by
    rw [hw_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs, ← dist_eq_norm,
      inv_mul_lt_iff₀ hs, mul_one]
    exact hy
  have hw2 : w ∈ closedBall (0 : E d) 2 := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hconvw := hn1 w hw2
  rw [blowup_inv_smul hs, Real.dist_eq] at hconvw
  set t := ⟪w, e⟫ with ht
  set a := u y / s with ha
  have hya : u y = s * a := by rw [ha]; field_simp
  have ha0 : 0 ≤ a := div_nonneg (hnn y hyU) hs.le
  have habs := abs_lt.1 hconvw
  rw [hinner, hya]
  constructor
  · -- lower bound
    have : q * max (t - ε) 0 ≤ a := by
      rcases le_or_gt t ε with htε | htε
      · rw [max_eq_right (by linarith)]; simpa using ha0
      · rw [max_eq_left (by linarith)]
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ t)] at habs
        linarith
    calc q * max (s * t - ε * s) 0 = s * (q * max (t - ε) 0) := by
          rw [show s * t - ε * s = s * (t - ε) by ring,
            show max (s * (t - ε)) 0 = s * max (t - ε) 0 by
              rw [mul_max_of_nonneg _ _ hs.le, mul_zero]]
          ring
      _ ≤ s * a := mul_le_mul_of_nonneg_left this hs.le
  · -- upper bound
    have : a ≤ q * max (t + ε) 0 := by
      rcases le_or_gt (-(ε / 2)) t with htε | htε
      · rw [max_eq_left (by linarith)]
        rcases le_or_gt 0 t with ht0 | ht0
        · rw [max_eq_left ht0] at habs; linarith
        · rw [max_eq_right ht0.le] at habs; nlinarith
      · -- far side: `u y = 0` by non-degeneracy
        refine (le_of_eq ?_).trans (by positivity)
        by_contra ha_ne
        have hpos : 0 < u y := by
          rw [hya]; exact mul_pos hs (lt_of_le_of_ne ha0 (Ne.symm ha_ne))
        have hycl : y ∈ closure (posSet u U) ∩ ball x₀ ρ :=
          ⟨subset_closure ⟨hyU, hpos⟩, ball_subset_ball hsρ.le hy⟩
        set σ := s * ε / 4 with hσ
        have hσ0 : 0 < σ := by positivity
        have hσρ : σ ≤ ρ := by
          rw [hσ]; nlinarith
        obtain ⟨y', hy', hcy'⟩ := hnd y hycl σ hσ0 hσρ
        set w' := s⁻¹ • (y' - x₀) with hw'_def
        have hww' : ‖w' - w‖ ≤ ε / 4 := by
          rw [hw'_def, hw_def, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, norm_inv,
            Real.norm_eq_abs, abs_of_pos hs, ← dist_eq_norm, inv_mul_le_iff₀ hs]
          rw [mem_closedBall] at hy'
          linarith
        have hw'2 : w' ∈ closedBall (0 : E d) 2 := by
          rw [mem_closedBall, dist_zero_right]
          have := norm_le_norm_add_norm_sub' w' w
          have := norm_sub_rev w' w
          linarith [norm_sub_norm_le w' w]
        have ht' : ⟪w', e⟫ < 0 := by
          have h1 : ⟪w', e⟫ - t = ⟪w' - w, e⟫ := by rw [inner_sub_left]
          have h2 : |⟪w' - w, e⟫| ≤ ‖w' - w‖ := by
            have := abs_real_inner_le_norm (w' - w) e
            rw [he, mul_one] at this; exact this
          have := (abs_le.1 (h2.trans hww')).2
          linarith
        have hconv' := hn1 w' hw'2
        rw [blowup_inv_smul hs, Real.dist_eq, max_eq_right ht'.le, mul_zero, zero_sub,
          abs_neg] at hconv'
        have h3 : u y' / s < δ := (le_abs_self _).trans_lt hconv'
        rw [div_lt_iff₀ hs] at h3
        have : c * σ < c * σ := by
          calc c * σ ≤ u y' := hcy'
            _ < δ * s := h3
            _ ≤ c * ε / 8 * s := mul_le_mul_of_nonneg_right hδ2 hs.le
            _ < c * σ := by rw [hσ]; nlinarith
        exact lt_irrefl _ this
    calc s * a ≤ s * (q * max (t + ε) 0) := mul_le_mul_of_nonneg_left this hs.le
      _ = q * max (s * t + ε * s) 0 := by
          rw [show s * t + ε * s = s * (t + ε) by ring,
            show max (s * (t + ε)) 0 = s * max (t + ε) 0 by
              rw [mul_max_of_nonneg _ _ hs.le, mul_zero]]
          ring

/-- **Flatness from a half-plane blow-up.** If `u ≥ 0` is uniformly
non-degenerate near `x₀` and some blow-up of `u` at `x₀` is the half-plane solution
`q (y · e)₊`, then for every `ε > 0` there is `0 < s ≤ ε` with `B_s(x₀) ⊆ U` in which `u` is
`ε`-flat: `q ((y - x₀) · e - ε s)₊ ≤ u(y) ≤ q ((y - x₀) · e + ε s)₊`. The upper bound uses the
non-degeneracy, which the paper's proof sketch does not invoke. -/
theorem flat_of_halfPlane_blowup {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hnn : ∀ x ∈ U, 0 ≤ u x) {x₀ : E d} (hx₀ : x₀ ∈ U)
    (hnd : IsUniformlyNondegenerateNear U u x₀) {q : ℝ} (hq : 0 < q) {e : E d} (he : ‖e‖ = 1)
    (hv : IsBlowupLimit u x₀ fun y ↦ q * max ⟪y, e⟫ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, 0 < s ∧ s ≤ ε ∧ ball x₀ s ⊆ U ∧ ∀ y ∈ ball x₀ s,
      q * max (⟪y - x₀, e⟫ - ε * s) 0 ≤ u y ∧ u y ≤ q * max (⟪y - x₀, e⟫ + ε * s) 0 := by
  obtain ⟨r, hr, hr0, hconv⟩ := hv
  obtain ⟨s, hs, hsε, hsU, hflat⟩ := flat_of_halfPlane_blowup_aux hU hnn hx₀ hnd hq he hr hr0
    hconv (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨s, hs, hsε.trans (min_le_left _ _), hsU, fun y hy ↦ ⟨?_, ?_⟩⟩
  · refine le_trans ?_ (hflat y hy).1
    gcongr
    linarith [min_le_left ε 1]
  · refine (hflat y hy).2.trans ?_
    gcongr
    linarith [min_le_left ε 1]

theorem convex_halfSpace_inner_lt (e : E d) (a : ℝ) : Convex ℝ {y : E d | ⟪y, e⟫ < a} := by
  have h := convex_halfSpace_lt (𝕜 := ℝ) (innerSL ℝ e).isLinear a
  convert h using 2 with y
  simp [real_inner_comm]

/-- **Flat or positive far side** (largest case, first two steps of the flatness argument). If
`u ≥ 0` is continuous, non-degenerate at the free boundary points near `x₀` (uniformly), and its
blow-ups along `r_n` converge to `q (y · e)₊`, then for `ε ≤ 1` and all large `n` (with
`s = r_n / 2`): either `u` is `ε`-flat in `B_s(x₀)`, or `u > 0` on the whole far region
`{(y - x₀) · e < -ε r_n / 4} ∩ B_s(x₀)`. The far region has no free boundary points (by
non-degeneracy and smallness), so by connectedness `u` vanishes identically or nowhere there. -/
theorem flat_or_pos_of_halfPlane_blowup {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hnn : ∀ x ∈ U, 0 ≤ u x) {x₀ : E d} (hx₀ : x₀ ∈ U)
    (hnd : ∃ c > 0, ∃ ρ > 0, ∀ z ∈ freeBoundary u U ∩ ball x₀ ρ, ∀ r, 0 < r → r ≤ ρ →
      ∃ y ∈ closedBall z r, c * r ≤ u y)
    {q : ℝ} (hq : 0 < q) {e : E d} (he : ‖e‖ = 1)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hconv : TendstoLocallyUniformly (fun n ↦ blowup u x₀ (r n)) (fun y ↦ q * max ⟪y, e⟫ 0)
      atTop) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ n in atTop, r n / 2 ≤ ε ∧ ball x₀ (r n / 2) ⊆ U ∧
      ((∀ y ∈ ball x₀ (r n / 2), q * max (⟪y - x₀, e⟫ - ε * (r n / 2)) 0 ≤ u y ∧
          u y ≤ q * max (⟪y - x₀, e⟫ + ε * (r n / 2)) 0) ∨
        ∀ y ∈ ball x₀ (r n / 2), ⟪y - x₀, e⟫ < -(ε / 4) * r n → 0 < u y) := by
  obtain ⟨c, hc, ρ, hρ, hnd⟩ := hnd
  obtain ⟨η, hη, hηU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set δ := min (q * ε / 4) (c * ε / 16) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ q * ε / 4 := min_le_left _ _
  have hδ2 : δ ≤ c * ε / 16 := min_le_right _ _
  have hK := (tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) (closedBall 0 2)
    (isCompact_closedBall 0 2)
  have hsmall : ∀ᶠ n in atTop, r n < min (min ρ ε) η :=
    (tendsto_order.1 hr0).2 _ (lt_min (lt_min hρ hε) hη)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hK δ hδ0, hsmall] with n hn1 hn2
  set s := r n with hs_def
  have hs : 0 < s := hr n
  have hsρ : s < ρ := (hn2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hsε : s < ε := (hn2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hsη : s < η := hn2.trans_le (min_le_right _ _)
  have hballU : ball x₀ s ⊆ U := (ball_subset_ball hsη.le).trans hηU
  have hballU' : ball x₀ (s / 2) ⊆ U := (ball_subset_ball (by linarith)).trans hballU
  refine ⟨by linarith, hballU', ?_⟩
  by_cases hpos : ∀ y ∈ ball x₀ (s / 2), ⟪y - x₀, e⟫ < -(ε / 4) * s → 0 < u y
  · exact Or.inr hpos
  refine Or.inl ?_
  push Not at hpos
  obtain ⟨y₀, hy₀, hy₀e, hy₀u⟩ := hpos
  -- blow-up coordinates
  have hcoord : ∀ y, ⟪y - x₀, e⟫ = s * ⟪s⁻¹ • (y - x₀), e⟫ := fun y ↦ by
    rw [inner_smul_left]; simp [mul_inv_cancel_left₀ hs.ne']
  have hnorm : ∀ y, ‖s⁻¹ • (y - x₀)‖ = dist y x₀ / s := fun y ↦ by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs, ← dist_eq_norm, inv_mul_eq_div]
  have hconvy : ∀ y, dist y x₀ ≤ 2 * s →
      |q * max ⟪s⁻¹ • (y - x₀), e⟫ 0 - u y / s| < δ := fun y hy ↦ by
    have := hn1 (s⁻¹ • (y - x₀)) (by
      rw [mem_closedBall, dist_zero_right, hnorm, div_le_iff₀ hs]; linarith)
    rwa [blowup_inv_smul hs, Real.dist_eq] at this
  -- the far region `A`
  set P := posSet u U with hP
  set A := {y : E d | ⟪y, e⟫ < ⟪x₀, e⟫ - ε / 4 * s} ∩ ball x₀ (s / 2) with hA
  have hmemA : ∀ y ∈ ball x₀ (s / 2), ⟪y - x₀, e⟫ < -(ε / 4) * s → y ∈ A := fun y hy hye ↦
    ⟨by simp only [mem_setOf_eq]; rw [inner_sub_left] at hye; linarith, hy⟩
  have hAU : A ⊆ U := fun y hy ↦ hballU' hy.2
  -- no free boundary points in `A`
  have hnofb : ∀ z ∈ A, z ∉ frontier P := by
    intro z hzA hzfb
    have hzρ : z ∈ ball x₀ ρ := ball_subset_ball (by linarith) hzA.2
    set σ := s * ε / 8 with hσ
    have hσ0 : 0 < σ := by positivity
    have hσρ : σ ≤ ρ := by rw [hσ]; nlinarith
    obtain ⟨y, hy, hcy⟩ := hnd z ⟨⟨hzfb, hAU hzA⟩, hzρ⟩ σ hσ0 hσρ
    rw [mem_closedBall] at hy
    have hze := hzA.1
    simp only [mem_setOf_eq] at hze
    have hyz : ⟪y - z, e⟫ ≤ σ := by
      have := real_inner_le_norm (y - z) e
      rw [he, mul_one, ← dist_eq_norm] at this; linarith
    have hye : ⟪y - x₀, e⟫ < 0 := by
      have : ⟪y - x₀, e⟫ = ⟪y - z, e⟫ + ⟪z, e⟫ - ⟪x₀, e⟫ := by
        rw [inner_sub_left, inner_sub_left]; ring
      rw [this]; linarith [mul_pos hs hε]
    have hdist : dist y x₀ ≤ 2 * s := by
      have := dist_triangle y z x₀
      have := mem_ball.1 hzA.2
      rw [hσ] at hy; nlinarith
    have h1 := hconvy y hdist
    have hte : ⟪s⁻¹ • (y - x₀), e⟫ < 0 := by
      rw [hcoord y] at hye
      exact neg_of_mul_neg_right (by linarith) hs.le
    rw [max_eq_right hte.le, mul_zero, zero_sub, abs_neg] at h1
    have h2 : u y / s < c * ε / 16 := (le_abs_self _).trans_lt (h1.trans_le hδ2)
    rw [div_lt_iff₀ hs] at h2
    rw [hσ] at hcy
    nlinarith
  -- all or nothing
  have hAconv : Convex ℝ A := (convex_halfSpace_inner_lt e _).inter (convex_ball _ _)
  have hcover : A ⊆ interior P ∪ (closure P)ᶜ := by
    intro z hz
    by_cases hzi : z ∈ interior P
    · exact Or.inl hzi
    · exact Or.inr fun hzc ↦ hnofb z hz ⟨hzc, hzi⟩
  have hdisj : Disjoint (interior P) (closure P)ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 (interior_subset.trans subset_closure)
  have hzeroA : ∀ y ∈ A, u y = 0 := by
    rcases hAconv.isPreconnected.subset_or_subset isOpen_interior
      isClosed_closure.isOpen_compl hdisj hcover with h | h
    · have := (interior_subset (h (hmemA y₀ hy₀ hy₀e))).2
      linarith
    · intro y hy
      refine le_antisymm (not_lt.1 fun hpos ↦ h hy (subset_closure ⟨hAU hy, hpos⟩))
        (hnn y (hAU hy))
  -- the flatness bounds
  intro y hy
  have hyU : y ∈ U := hballU' hy
  have hdist : dist y x₀ ≤ 2 * s := by have := mem_ball.1 hy; linarith
  set t := ⟪s⁻¹ • (y - x₀), e⟫ with ht
  set a := u y / s with ha
  have hya : u y = s * a := by rw [ha]; field_simp
  have ha0 : 0 ≤ a := div_nonneg (hnn y hyU) hs.le
  have habs := abs_lt.1 (hconvy y hdist)
  rw [hcoord y, hya]
  have hmax : ∀ b : ℝ, max (s * t + b * s) 0 = s * max (t + b) 0 := fun b ↦ by
    rw [show s * t + b * s = s * (t + b) by ring, mul_max_of_nonneg _ _ hs.le, mul_zero]
  constructor
  · have : q * max (t - ε / 2) 0 ≤ a := by
      rcases le_or_gt t (ε / 2) with htε | htε
      · rw [max_eq_right (by linarith)]; simpa using ha0
      · rw [max_eq_left (by linarith)]
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ t)] at habs
        linarith
    calc q * max (s * t - ε * (s / 2)) 0 = s * (q * max (t - ε / 2) 0) := by
          rw [show s * t - ε * (s / 2) = s * t + (-(ε / 2)) * s by ring, hmax]; ring
      _ ≤ s * a := mul_le_mul_of_nonneg_left this hs.le
  · have : a ≤ q * max (t + ε / 2) 0 := by
      rcases le_or_gt (-(ε / 4)) t with htε | htε
      · rw [max_eq_left (by linarith)]
        rcases le_or_gt 0 t with ht0 | ht0
        · rw [max_eq_left ht0] at habs; linarith
        · rw [max_eq_right ht0.le] at habs; nlinarith
      · have hyA : y ∈ A := hmemA y hy (by rw [hcoord y]; nlinarith)
        have : a = 0 := by
          have := hzeroA y hyA
          rw [hya] at this
          exact (mul_eq_zero.1 this).resolve_left hs.ne'
        rw [this]; positivity
    calc s * a ≤ s * (q * max (t + ε / 2) 0) := mul_le_mul_of_nonneg_left this hs.le
      _ = q * max (s * t + ε * (s / 2)) 0 := by
          rw [show s * t + ε * (s / 2) = s * t + (ε / 2) * s by ring, hmax]; ring

end Flat

end Corollary2D

end PerronVariational

end
