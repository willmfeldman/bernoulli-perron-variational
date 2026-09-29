/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.TwoDisc.Upper

/-!
# The lower bound in the two-disc model example

For the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 (`[AFS]`):
every `V ∈ 𝒮_{gSub}` lies above the radial solutions `w_± = (a log (a/|x ∓ p|))₊`
(`wIn_le_of_mem_perronSuperClass`), hence so does `u_min` (`wIn_le_perronSmallest`).

The barriers are `Φ_θ = β log (R/|x ∓ p|) + θ (|x ∓ p|² - R²)`, `R = a - θ`, `β = R + 3θR²`, on the
annuli `K_θ = {r ≤ |x ∓ p| ≤ R}`. They satisfy `ΔΦ_θ = 4θ > 0`, `|∇Φ_θ| ≥ 1 + θR > 1` on `K_θ`,
`Φ_θ ≤ c ≤ V` on the inner circle and `Φ_θ = 0 ≤ V` on the outer one. If `Φ_θ - V` had a positive
maximum on `K_θ`, it would be attained inside, where `Φ_θ - max` touches `V` from below: this is
excluded by `IsViscSuper.false_of_touch_contDiff_two`. Letting `θ → 0⁺` gives `V ≥ w_±`.
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian ContDiff

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

/-! ### Geometry near the holes -/

/-- The two holes. -/
def IsHole (z : E 2) : Prop := z = hole ∨ z = -hole

theorem geom_near {z x : E 2} (hz : IsHole z) (h : ‖x - z‖ ^ 2 ≤ 1 / 100) :
    1 / 100 ≤ ‖x - (-z)‖ ^ 2 ∧ ‖x - 0‖ ^ 2 ≤ 1 / 25 := by
  rcases hz with rfl | rfl
  · rw [sq_sub_neg_hole]; exact geom_plus_le h
  · rw [neg_neg]; rw [sq_sub_neg_hole] at h; exact geom_minus_le h

theorem mem_domain_of_near {z x : E 2} (hz : IsHole z) (h1 : 1 / 400 < ‖x - z‖ ^ 2)
    (h2 : ‖x - z‖ ^ 2 ≤ 1 / 100) : x ∈ domain := by
  obtain ⟨h3, h4⟩ := geom_near hz h2
  have key : ‖x - 0‖ ^ 2 < 1 ∧ 1 / 400 < ‖x - hole‖ ^ 2 ∧ 1 / 400 < ‖x + hole‖ ^ 2 := by
    rcases hz with rfl | rfl
    · rw [sq_sub_neg_hole] at h3; exact ⟨by linarith, h1, by linarith⟩
    · rw [neg_neg] at h3; rw [sq_sub_neg_hole] at h1; exact ⟨by linarith, by linarith, h1⟩
  rw [mem_domain_iff]
  rw [sub_zero, norm_sq_eq, norm_sub_hole_sq, norm_add_hole_sq] at key
  exact key

theorem mem_closure_of_near {z x : E 2} (hz : IsHole z) (h1 : 1 / 400 ≤ ‖x - z‖ ^ 2)
    (h2 : ‖x - z‖ ^ 2 ≤ 1 / 100) : x ∈ closure domain := by
  rcases lt_or_eq_of_le h1 with h1 | h1
  · exact subset_closure (mem_domain_of_near hz h1 h2)
  -- on the inner circle, approach radially from outside
  have ht : Tendsto (fun t : ℝ ↦ z + (1 + t) • (x - z)) (𝓝[>] 0) (𝓝 x) := by
    have : Continuous fun t : ℝ ↦ z + (1 + t) • (x - z) := by fun_prop
    have h := this.tendsto 0
    simp only [add_zero, one_smul, add_sub_cancel] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hn : ‖z + (1 + t) • (x - z) - z‖ ^ 2 = (1 + t) ^ 2 * (1 / 400) := by
    rw [add_sub_cancel_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← h1]
  refine mem_domain_of_near hz ?_ ?_ <;> rw [hn] <;> nlinarith [ht.1, ht.2]

theorem gSub_on_circle {z x : E 2} (hz : IsHole z) (h : ‖x - z‖ ^ 2 = 1 / 400) : gSub x = cst := by
  rcases hz with rfl | rfl
  · obtain ⟨hm, h0⟩ := geom_plus (x := x) (by rw [h]; norm_num)
    rw [gSub, qIn_of_circle h, (qIn_floor (z := -hole) (x := x)
      (by rw [sq_sub_neg_hole]; exact hm)).1, (qOut_floor h0).1]; ring
  · rw [sq_sub_neg_hole] at h
    obtain ⟨hp, h0⟩ := geom_minus (x := x) (by rw [h]; norm_num)
    have h' : ‖x - -hole‖ ^ 2 = 1 / 400 := by rw [sq_sub_neg_hole]; exact h
    rw [gSub, qIn_of_circle h', (qIn_floor (z := hole) (x := x) hp).1, (qOut_floor h0).1]; ring

/-! ### The barriers -/

/-- The outer radius `R = 1/10 - θ`. -/
def barR (θ : ℝ) : ℝ := 1 / 10 - θ

/-- The slope `β = R + 3θR²`. -/
def barB (θ : ℝ) : ℝ := barR θ + 3 * θ * barR θ ^ 2

/-- The radial part `β log (10R) + θ (τ - R²)`, as a function of `τ = |x - z|²`. -/
def barG (θ τ : ℝ) : ℝ := barB θ * Real.log (10 * barR θ) + θ * (τ - barR θ ^ 2)

/-- The barrier `Φ_θ = 10β w + β log (10R) + θ (|x - z|² - R²) = β log (R/|x - z|) + θ(...)`. -/
def barrier (z : E 2) (θ : ℝ) (y : E 2) : ℝ := 10 * barB θ * wIn z y + barG θ (‖y - z‖ ^ 2)

theorem contDiff_barG (θ : ℝ) : ContDiff ℝ ⊤ (barG θ) := by unfold barG; fun_prop

theorem contDiff_barrier (z : E 2) (θ : ℝ) : ContDiff ℝ 2 (barrier z θ) := by
  unfold barrier
  exact (contDiff_const.mul (contDiff_wIn z)).add
    (((contDiff_barG θ).of_le le_top).comp ((contDiff_norm_sq ℝ).comp
      (contDiff_id.sub contDiff_const)))

section Params

variable {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1 / 20)
include hθ hθ'

theorem barR_bounds : 1 / 20 < barR θ ∧ barR θ < 1 / 10 := by
  unfold barR; constructor <;> linarith

theorem barB_le : barB θ ≤ 1 / 10 := by
  have := barR_bounds hθ hθ'
  unfold barB
  have : barR θ ^ 2 ≤ 1 / 100 := by nlinarith
  unfold barR at *; nlinarith

theorem barB_pos : 0 < barB θ := by
  have := barR_bounds hθ hθ'
  unfold barB
  exact add_pos_of_pos_of_nonneg (by linarith)
    (mul_nonneg (mul_nonneg (by norm_num) hθ.le) (sq_nonneg _))

omit hθ hθ' in
theorem barrier_eq {z y : E 2} (h1 : 1 / 400 ≤ ‖y - z‖ ^ 2) (h2 : ‖y - z‖ ^ 2 ≤ 1 / 100) :
    barrier z θ y = barB θ * ((Real.log (1 / 100) - Real.log (‖y - z‖ ^ 2)) / 2 +
      Real.log (10 * barR θ)) + θ * (‖y - z‖ ^ 2 - barR θ ^ 2) := by
  rw [barrier, wIn_eq h1 h2, barG]; ring

/-- On the inner circle the barrier is at most `c`. -/
theorem barrier_le_cst {z y : E 2} (h : ‖y - z‖ ^ 2 = 1 / 400) : barrier z θ y ≤ cst := by
  obtain ⟨hR1, hR2⟩ := barR_bounds hθ hθ'
  rw [barrier_eq (by rw [h]) (by rw [h]; norm_num), h]
  have e : (Real.log (1 / 100) - Real.log (1 / 400)) / 2 + Real.log (10 * barR θ) =
      Real.log (20 * barR θ) := by
    have h20 : Real.log (20 * barR θ) = Real.log 2 + Real.log (10 * barR θ) := by
      rw [← Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < 10 * barR θ).ne']; ring_nf
    rw [log_hundredth_sub, h20]; ring
  rw [e]
  have hl0 : 0 ≤ Real.log (20 * barR θ) := Real.log_nonneg (by linarith)
  have hl2 : Real.log (20 * barR θ) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
  have hB := barB_le hθ hθ'
  have hBp := barB_pos hθ hθ'
  have : θ * (1 / 400 - barR θ ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθ.le (by nlinarith)
  unfold cst
  nlinarith [mul_le_mul hB hl2 hl0 (by norm_num : (0 : ℝ) ≤ 1 / 10)]

/-- On the outer circle `|y - z| = R` the barrier vanishes. -/
theorem barrier_outer {z y : E 2} (h : ‖y - z‖ ^ 2 = barR θ ^ 2) : barrier z θ y = 0 := by
  obtain ⟨hR1, hR2⟩ := barR_bounds hθ hθ'
  rw [barrier_eq (by rw [h]; nlinarith) (by rw [h]; nlinarith), h, sub_self, mul_zero,
    add_zero]
  have e : (Real.log (1 / 100) - Real.log (barR θ ^ 2)) / 2 + Real.log (10 * barR θ) = 0 := by
    rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num) (by linarith), show (10 : ℝ) = (1 / 10)⁻¹ by norm_num,
      Real.log_inv]
    push_cast; ring_nf
  rw [e, mul_zero]

omit hθ hθ' in
theorem laplacian_barrier {z y : E 2} (h1 : 1 / 400 ≤ ‖y - z‖ ^ 2) (h2 : ‖y - z‖ ^ 2 ≤ 1 / 100) :
    Δ (barrier z θ) y = 4 * θ := by
  have hw := (contDiff_wIn z).contDiffAt (x := y)
  have hG : ContDiffAt ℝ 2 (fun y : E 2 ↦ barG θ (‖y - z‖ ^ 2)) y :=
    (((contDiff_barG θ).of_le le_top).comp ((contDiff_norm_sq ℝ).comp
      (contDiff_id.sub contDiff_const))).contDiffAt
  have hcw : ContDiffAt ℝ 2 ((10 * barB θ) • wIn z) y := hw.const_smul (10 * barB θ)
  change Δ ((10 * barB θ) • wIn z + fun y : E 2 ↦ barG θ (‖y - z‖ ^ 2)) y = _
  rw [hcw.laplacian_add hG, InnerProductSpace.laplacian_smul _ hw, laplacian_wIn h1 h2,
    laplacian_radial ((contDiff_barG θ).of_le le_top)]
  have d1 : deriv (barG θ) = fun _ ↦ θ := by
    funext τ; unfold barG
    simp
  rw [d1]
  simp

theorem hasGradientAt_barrier {z y : E 2} (h1 : 1 / 400 ≤ ‖y - z‖ ^ 2)
    (h2 : ‖y - z‖ ^ 2 ≤ 1 / 100) :
    HasGradientAt (barrier z θ) ((2 * θ - barB θ / ‖y - z‖ ^ 2) • (y - z)) y := by
  have hτ : (1 / 3200 : ℝ) < ‖y - z‖ ^ 2 := by linarith
  have hw := hasGradientAt_logRad (P₁ := floorCapD (-1 / 10) (1 / 10) cst cst) contDiff_floorCap
    (hasDerivAt_floorCap (by norm_num) cst_pos.ne') (by norm_num) (by norm_num) clamp_wIn hτ
  rw [floorCapD_of_mem_Icc (by norm_num) cst_pos (wIn_mid h1 h2)] at hw
  have hG := hasGradientAt_radial (G := barG θ) (z := z) (x := y)
    ((contDiff_barG θ).differentiable (by simp) _)
  have d1 : deriv (barG θ) (‖y - z‖ ^ 2) = θ := by
    unfold barG
    simp
  rw [d1] at hG
  rw [hasGradientAt_iff_hasFDerivAt] at hw hG ⊢
  have := (hw.const_mul (10 * barB θ)).add hG
  convert this using 1
  have hτ0 : ‖y - z‖ ^ 2 ≠ 0 := by linarith
  ext w
  simp only [map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    toDual_apply_apply, smul_eq_mul]
  field_simp
  ring

theorem norm_gradient_barrier {z y : E 2} (h1 : 1 / 400 ≤ ‖y - z‖ ^ 2)
    (h2 : ‖y - z‖ ^ 2 ≤ barR θ ^ 2) : 1 < ‖∇ (barrier z θ) y‖ := by
  obtain ⟨hR1, hR2⟩ := barR_bounds hθ hθ'
  have h2' : ‖y - z‖ ^ 2 ≤ 1 / 100 := by nlinarith
  rw [(hasGradientAt_barrier hθ hθ' h1 h2').gradient, norm_smul, Real.norm_eq_abs]
  set s := ‖y - z‖ with hs
  have hs0 : 1 / 20 ≤ s := by nlinarith [norm_nonneg (y - z)]
  have hsR : s ≤ barR θ := by nlinarith [norm_nonneg (y - z)]
  have hB : barB θ = barR θ + 3 * θ * barR θ ^ 2 := rfl
  have hneg : 2 * θ - barB θ / s ^ 2 < 0 := by
    rw [sub_neg, lt_div_iff₀ (by positivity)]
    nlinarith
  rw [abs_of_neg hneg]
  have : (barB θ / s ^ 2) * s = barB θ / s := by field_simp
  have key : 1 < barB θ / s - 2 * θ * s := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
    nlinarith [mul_pos hθ (show 0 < barR θ by linarith)]
  nlinarith

end Params

/-! ### Comparison -/

/-- **Barrier comparison.** Every `V ∈ 𝒮_{gSub}` lies above `Φ_θ` on `K_θ`. -/
theorem barrier_le_of_mem {V : E 2 → ℝ} (hV : V ∈ perronSuperClass domain (fun _ ↦ 1) gSub)
    {z : E 2} (hz : IsHole z) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1 / 20) {y : E 2}
    (hy1 : 1 / 400 ≤ ‖y - z‖ ^ 2) (hy2 : ‖y - z‖ ^ 2 ≤ barR θ ^ 2) : barrier z θ y ≤ V y := by
  obtain ⟨hR1, hR2⟩ := barR_bounds hθ hθ'
  have hR2' : barR θ ^ 2 ≤ 1 / 100 := by nlinarith
  set K := {y : E 2 | 1 / 400 ≤ ‖y - z‖ ^ 2 ∧ ‖y - z‖ ^ 2 ≤ barR θ ^ 2} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · simp only [hK, Set.setOf_and]
      exact (isClosed_le continuous_const (by fun_prop)).inter
        (isClosed_le (by fun_prop) continuous_const)
    · refine (Metric.isBounded_closedBall (x := z) (r := 1)).subset fun w hw ↦ ?_
      rw [mem_closedBall, dist_eq_norm]
      nlinarith [hw.2, norm_nonneg (w - z)]
  have hKcl : K ⊆ closure domain := fun w hw ↦ mem_closure_of_near hz hw.1 (hw.2.trans hR2')
  have hF : ContinuousOn (fun w ↦ barrier z θ w - V w) K :=
    ((contDiff_barrier z θ).continuous.continuousOn).sub (hV.1.mono hKcl)
  obtain ⟨m, hmK, hmax⟩ := hKc.exists_isMaxOn ⟨y, hy1, hy2⟩ hF
  by_contra hcon
  push Not at hcon
  have hpos : 0 < barrier z θ m - V m :=
    lt_of_lt_of_le (sub_pos.2 hcon) (hmax ⟨hy1, hy2⟩)
  have hVg : ∀ w ∈ closure domain, max (gSub w) 0 ≤ V w := hV.2.2
  rcases eq_or_lt_of_le hmK.1 with hin | hin
  · -- the inner circle
    have h1 := hVg m (hKcl hmK)
    rw [gSub_on_circle hz hin.symm] at h1
    have h2 := barrier_le_cst hθ hθ' hin.symm
    linarith [le_max_left cst 0]
  rcases eq_or_lt_of_le hmK.2 with hout | hout
  · -- the outer circle
    have := hVg m (hKcl hmK)
    rw [barrier_outer hθ hθ' hout] at hpos
    linarith [le_max_right (gSub m) 0]
  -- an interior maximum: `Φ_θ - max` touches `V` from below
  set M := barrier z θ m - V m with hM
  have hmU : m ∈ domain := mem_domain_of_near hz hin (hmK.2.trans hR2')
  have hnhds : K ∈ 𝓝 m := by
    refine Filter.mem_of_superset ((isOpen_gt_normsq z (1 / 400)).inter
      (isOpen_lt_normsq z (barR θ ^ 2)) |>.mem_nhds ⟨hin, hout⟩) ?_
    rintro w ⟨h1, h2⟩
    exact ⟨le_of_lt h1, le_of_lt h2⟩
  refine IsViscSuper.false_of_touch_contDiff_two (Φ := fun w ↦ barrier z θ w - M) two_pos
    isOpen_domain hV.2.1 hmU ((contDiff_barrier z θ).sub contDiff_const) ?_ (by rw [hM]; ring) ?_ ?_
  · filter_upwards [hnhds] with w hw
    have := hmax hw
    simp only [mem_setOf_eq] at this
    linarith
  · rw [show (fun w ↦ barrier z θ w - M) = fun w ↦ barrier z θ w + (-M) by funext w; ring,
      laplacian_add_const (contDiff_barrier z θ).contDiffAt,
      laplacian_barrier hmK.1 (hmK.2.trans hR2')]
    linarith
  · show (1 : ℝ) < _
    have : ∇ (fun w ↦ barrier z θ w - M) m = ∇ (barrier z θ) m := by
      rw [show (fun w ↦ barrier z θ w - M) = fun w ↦ barrier z θ w + (-M) by
        funext w; ring, gradient_add_const]
    rw [this]
    exact norm_gradient_barrier hθ hθ' hmK.1 hmK.2

/-- **The lower bound.** Every `V ∈ 𝒮_{gSub}` lies above the disc piece `w` on
`{r ≤ |x ∓ p| < a}`. -/
theorem wIn_le_of_mem_perronSuperClass {V : E 2 → ℝ}
    (hV : V ∈ perronSuperClass domain (fun _ ↦ 1) gSub) {z : E 2} (hz : IsHole z) {y : E 2}
    (hy1 : 1 / 400 ≤ ‖y - z‖ ^ 2) (hy2 : ‖y - z‖ ^ 2 < 1 / 100) : wIn z y ≤ V y := by
  set τ := ‖y - z‖ ^ 2 with hτ
  have hs : ‖y - z‖ < 1 / 10 := by nlinarith [norm_nonneg (y - z)]
  -- the barriers at `y` converge to `w(y)` as `θ → 0⁺`
  set f : ℝ → ℝ := fun θ ↦ barB θ * ((Real.log (1 / 100) - Real.log τ) / 2 +
      Real.log (10 * barR θ)) + θ * (τ - barR θ ^ 2) with hf
  have hcont : ContinuousAt f 0 := by
    have hl : ContinuousAt (fun θ : ℝ ↦ Real.log (10 * barR θ)) 0 := by
      refine ContinuousAt.log (by unfold barR; fun_prop) ?_
      unfold barR; norm_num
    unfold barB barR at *
    exact ((continuousAt_id.const_sub _).add ((continuousAt_const.mul continuousAt_id).mul
      ((continuousAt_id.const_sub _).pow 2))).mul (continuousAt_const.add hl) |>.add
      (continuousAt_id.mul (continuousAt_const.sub ((continuousAt_id.const_sub _).pow 2)))
  have hf0 : f 0 = wIn z y := by
    have h1 : barB 0 = 1 / 10 := by norm_num [barB, barR]
    have h2 : barR 0 = 1 / 10 := by norm_num [barR]
    rw [hf]; dsimp only
    rw [h1, h2, show (10 : ℝ) * (1 / 10) = 1 by norm_num, Real.log_one, wIn_eq hy1 hy2.le]
    ring
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 (wIn z y)) := by
    rw [← hf0]; exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  have hgap : 0 < 1 / 10 - ‖y - z‖ := by linarith
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (1 / 20) (1 / 10 - ‖y - z‖) by positivity)]
    with θ hθ
  have hθ' : θ < 1 / 20 := lt_of_lt_of_le hθ.2 (min_le_left _ _)
  have hθ'' : θ < 1 / 10 - ‖y - z‖ := lt_of_lt_of_le hθ.2 (min_le_right _ _)
  have hyR : τ ≤ barR θ ^ 2 := by
    rw [hτ]; unfold barR
    have : ‖y - z‖ ≤ 1 / 10 - θ := by linarith
    nlinarith [norm_nonneg (y - z)]
  have := barrier_le_of_mem hV hz hθ.1 hθ' hy1 hyR
  rwa [barrier_eq hy1 hy2.le] at this

/-- `u_min ≥ w` on `{r ≤ |x ∓ p| < a}`. -/
theorem wIn_le_perronSmallest {z : E 2} (hz : IsHole z) {y : E 2}
    (hy1 : 1 / 400 ≤ ‖y - z‖ ^ 2) (hy2 : ‖y - z‖ ^ 2 < 1 / 100) :
    wIn z y ≤ perronSmallest domain (fun _ ↦ 1) gSub y := by
  have hne : (perronSuperClass domain (fun _ ↦ (1 : ℝ)) gSub).Nonempty :=
    ⟨vSup, vSup_mem_perronSuperClass⟩
  unfold perronSmallest
  exact le_csInf (hne.image _)
    (by rintro _ ⟨V, hV, rfl⟩; exact wIn_le_of_mem_perronSuperClass hV hz hy1 hy2)

end PerronVariational.TwoDisc

end
