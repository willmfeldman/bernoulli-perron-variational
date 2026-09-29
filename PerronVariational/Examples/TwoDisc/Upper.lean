/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.TwoDisc.Strict
public import PerronVariational.Examples.TwoDisc.Touch
public import PerronVariational.Stationary.Perron

/-!
# The explicit supersolution of the two-disc model example

For the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 (`[AFS]`),
the function
`v = (a log (a/|x - p|))₊ + (a log (a/|x + p|))₊ + (ρ log (|x|/ρ))₊`, `a = 1/10`,
is a viscosity supersolution in `U` with `Q ≡ 1` lying above `gSub₊`
(`vSup_mem_perronSuperClass`); hence `u_min ≤ v`. The three positivity sets are the discs
`B_a(±p)`, which touch at `0`, and the outer layer `{ρ < |x| < 1}`.

The pieces are written as log-radial profiles (`wIn`, `hOut`), smooth on all of `ℝ²` and equal to
the logarithms on `Ū`. At a free boundary point the test function touches `W₊` from below for a
single smooth `W` with `|∇W| = 1` along the ray `x + t∇φ(x)`, which gives `|∇φ(x)| ≤ 1`
(`norm_gradient_le_of_ray`); at `0` we choose the disc on the side of `∇φ(0)`.
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian ContDiff

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

/-! ### The pieces -/

/-- The profile of the disc pieces: floor at `-1/10`, cap at `c` (inside the holes). -/
def pV : ℝ → ℝ := floorCap (-1 / 10) (1 / 10) cst cst

/-- The profile of the outer piece: floor at `-1/10`, cap at `1` (inactive on `B̄₁`). -/
def pH : ℝ → ℝ := floorCap (-1 / 10) (1 / 10) 1 1

/-- The constant `k` with `-(1/20) log τ + k = (log (1/100) - log τ)/20`. -/
def kV : ℝ := Real.log (1 / 100) / 20

/-- The disc piece around `z`: `a log (a/|x - z|) = (log (1/100) - log |x - z|²)/20`. -/
def wIn (z : E 2) : E 2 → ℝ := logRad pV z (-(1 / 20)) kV (1 / 3200)

/-- The outer piece: `ρ log (|x|/ρ) = (ρ/2) log |x|² + ε`. -/
def hOut : E 2 → ℝ := logRad pH 0 (rho / 2) eps (1 / 4)

/-- The explicit supersolution `v = w₊ + w₋ + h`. -/
def vSup (x : E 2) : ℝ := max (wIn hole x) 0 + max (wIn (-hole) x) 0 + max (hOut x) 0

theorem aw_eq (τ : ℝ) : -(1 / 20) * Real.log τ + kV = (Real.log (1 / 100) - Real.log τ) / 20 := by
  unfold kV; ring

theorem log_hundredth_sub : Real.log (1 / 100) - Real.log (1 / 400) = 2 * Real.log 2 := by
  rw [show (1 / 400 : ℝ) = (1 / 100) / 2 ^ 2 by norm_num,
    Real.log_div (show (1 / 100 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ^ 2 ≠ 0 by norm_num),
    Real.log_pow]; push_cast; ring

theorem rho_sq_bounds : 81 / 100 ≤ rho ^ 2 ∧ rho ^ 2 < 1 := by
  obtain ⟨h1, h2⟩ := rho_bounds
  constructor <;> nlinarith

theorem ah_eq (τ : ℝ) :
    rho / 2 * Real.log τ + eps = rho / 2 * (Real.log τ - Real.log (rho ^ 2)) := by
  rw [Real.log_pow, log_rho]; unfold eps; push_cast; ring

theorem clamp_wIn : ClampConst pV (-(1 / 20)) kV (1 / 3200) (1 / 1600) := by
  have hc := cst_pos
  have key : ∀ τ ∈ Icc (1 / 3200 : ℝ) (1 / 1600),
      pV (-(1 / 20) * Real.log τ + kV) = cst + cst / 2 := by
    intro τ hτ
    refine floorCap_of_cap_le (by norm_num) hc (by linarith) ?_
    have hl : Real.log τ ≤ Real.log (1 / 100) - 4 * Real.log 2 := by
      calc Real.log τ ≤ Real.log (1 / 1600) := Real.log_le_log (by linarith [hτ.1]) hτ.2
        _ = _ := by
          rw [show (1 / 1600 : ℝ) = (1 / 100) / 2 ^ 4 by norm_num,
            Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    rw [aw_eq]; unfold cst; linarith
  intro τ hτ
  rw [key τ hτ, key _ ⟨le_rfl, by norm_num⟩]

theorem ah_floor {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 1 / 2) : rho / 2 * Real.log τ + eps ≤ -1 / 5 := by
  have hl : Real.log τ ≤ -Real.log 2 := by
    calc Real.log τ ≤ Real.log (1 / 2) := Real.log_le_log hτ h
      _ = _ := by rw [one_div, Real.log_inv]
  obtain ⟨h1, h2⟩ := rho_bounds
  have := log_two_bounds.1
  unfold eps
  nlinarith

theorem pH_floor {t : ℝ} (h : t ≤ -1 / 5) : pH t = -3 / 20 := by
  rw [pH, floorCap_of_le_floor (by norm_num) one_pos (by norm_num) (by linarith)]; norm_num

theorem clamp_hOut : ClampConst pH (rho / 2) eps (1 / 4) (1 / 2) := by
  intro τ hτ
  rw [pH_floor (ah_floor (by linarith [hτ.1]) hτ.2),
    pH_floor (ah_floor (by norm_num) (by norm_num))]

theorem contDiff_wIn (z : E 2) : ContDiff ℝ 2 (wIn z) :=
  contDiff_logRad_floorCap (by norm_num) (by norm_num) clamp_wIn

theorem contDiff_hOut : ContDiff ℝ 2 hOut :=
  contDiff_logRad_floorCap (by norm_num) (by norm_num) clamp_hOut

theorem continuous_vSup : Continuous vSup := by
  unfold vSup
  have h1 := (contDiff_wIn hole).continuous
  have h2 := (contDiff_wIn (-hole)).continuous
  have h3 := contDiff_hOut.continuous
  fun_prop

theorem vSup_nonneg (x : E 2) : 0 ≤ vSup x := by
  unfold vSup
  have := le_max_right (wIn hole x) 0
  have := le_max_right (wIn (-hole) x) 0
  have := le_max_right (hOut x) 0
  linarith

/-! ### Values of the pieces -/

theorem max_floorCap_eq {tc lc t : ℝ} (hlc : 0 < lc) (htc : -1 / 10 ≤ tc) (ht : t ≤ tc) :
    max (floorCap (-1 / 10) (1 / 10) tc lc t) 0 = max t 0 := by
  by_cases h : -1 / 10 ≤ t
  · rw [floorCap_of_mem_Icc (by norm_num) hlc ⟨h, ht⟩]
  · push Not at h
    have := floorCap_le_floor (tc := tc) (Lc := lc) (Lf := 1 / 10) (by norm_num) hlc htc h.le
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]

/-- On `Ū`, the argument of a disc piece is at most `c`. -/
theorem aw_le_cst {τ : ℝ} (hτ : 1 / 400 ≤ τ) : (Real.log (1 / 100) - Real.log τ) / 20 ≤ cst := by
  have := Real.log_le_log (by norm_num) hτ
  have := log_hundredth_sub
  unfold cst; linarith

theorem wIn_val {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) :
    wIn z x = pV ((Real.log (1 / 100) - Real.log (‖x - z‖ ^ 2)) / 20) := by
  rw [wIn, logRad_apply, max_eq_left (by linarith), aw_eq]

/-- Outside its disc, a disc piece contributes `0`. -/
theorem max_wIn_eq_zero {z x : E 2} (hτ : 1 / 100 ≤ ‖x - z‖ ^ 2) : max (wIn z x) 0 = 0 := by
  rw [wIn_val (by linarith), pV, max_floorCap_eq cst_pos (by linarith [cst_pos])
    (aw_le_cst (by linarith))]
  refine max_eq_right ?_
  have := Real.log_le_log (by norm_num) hτ
  linarith

/-- On its closed disc (and in `Ū`), a disc piece is the logarithm. -/
theorem wIn_eq {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) (hτ' : ‖x - z‖ ^ 2 ≤ 1 / 100) :
    wIn z x = (Real.log (1 / 100) - Real.log (‖x - z‖ ^ 2)) / 20 := by
  rw [wIn_val hτ, pV, floorCap_of_mem_Icc (by norm_num) cst_pos ⟨?_, aw_le_cst hτ⟩]
  have := Real.log_le_log (by linarith) hτ'
  linarith

theorem wIn_mid {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) (hτ' : ‖x - z‖ ^ 2 ≤ 1 / 100) :
    -(1 / 20) * Real.log (‖x - z‖ ^ 2) + kV ∈ Icc (-1 / 10) cst := by
  rw [aw_eq]
  refine ⟨?_, aw_le_cst hτ⟩
  have := Real.log_le_log (by linarith) hτ'
  linarith

theorem wIn_pos {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) (hτ' : ‖x - z‖ ^ 2 < 1 / 100) :
    0 < wIn z x := by
  rw [wIn_eq hτ hτ'.le]
  have := Real.log_lt_log (by linarith) hτ'
  linarith

theorem wIn_eq_zero {z x : E 2} (hτ : ‖x - z‖ ^ 2 = 1 / 100) : wIn z x = 0 := by
  rw [wIn_eq (by rw [hτ]; norm_num) hτ.le, hτ]; ring

theorem laplacian_wIn {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) (hτ' : ‖x - z‖ ^ 2 ≤ 1 / 100) :
    Δ (wIn z) x = 0 :=
  laplacian_logRad_mid (by norm_num) cst_pos (by norm_num) (by norm_num) clamp_wIn
    (by linarith) (wIn_mid hτ hτ')

theorem norm_eq_of_sq {v : E 2} {s : ℝ} (hs : 0 ≤ s) (h : ‖v‖ ^ 2 = s ^ 2) : ‖v‖ = s :=
  (sq_eq_sq₀ (norm_nonneg _) hs).1 h

theorem norm_gradient_wIn {z x : E 2} (hτ : ‖x - z‖ ^ 2 = 1 / 100) : ‖∇ (wIn z) x‖ = 1 := by
  rw [wIn, pV, norm_gradient_logRad_mid (by norm_num) cst_pos (by norm_num) (by norm_num) clamp_wIn
    (by rw [hτ]; norm_num) (wIn_mid (by rw [hτ]; norm_num) hτ.le),
    norm_eq_of_sq (s := 1 / 10) (by norm_num) (by rw [hτ]; norm_num)]
  norm_num

/-- Inside the unit circle and off the outer layer, the outer piece contributes `0`. -/
theorem max_hOut_eq_zero {x : E 2} (hτ : ‖x - 0‖ ^ 2 ≤ rho ^ 2) : max (hOut x) 0 = 0 := by
  rcases le_or_gt (‖x - 0‖ ^ 2) (1 / 4) with h | h
  · rw [hOut, logRad_apply, max_eq_right h, pH_floor (ah_floor (by norm_num) (by norm_num))]
    norm_num
  · rw [hOut, logRad_apply, max_eq_left h.le]
    unfold pH
    rw [max_floorCap_eq one_pos (by norm_num)]
    · refine max_eq_right ?_
      rw [ah_eq]
      have := Real.log_le_log (by linarith) hτ
      nlinarith [rho_bounds.1]
    · have := Real.log_nonpos (by linarith) (hτ.trans rho_sq_bounds.2.le)
      have := rho_bounds; have := eps_bounds
      nlinarith

theorem ah_mid {x : E 2} (hτ : rho ^ 2 ≤ ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 1) :
    rho / 2 * Real.log (‖x - 0‖ ^ 2) + eps ∈ Icc (-1 / 10) 1 := by
  have h0 : 0 < ‖x - 0‖ ^ 2 := lt_of_lt_of_le (by nlinarith [rho_bounds.1]) hτ
  constructor
  · rw [ah_eq]
    have := Real.log_le_log (by nlinarith [rho_bounds.1]) hτ
    nlinarith [rho_bounds.1]
  · have := Real.log_nonpos h0.le hτ1
    have := rho_bounds; have := eps_bounds
    nlinarith

theorem hOut_eq {x : E 2} (hτ : rho ^ 2 ≤ ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 1) :
    hOut x = rho / 2 * Real.log (‖x - 0‖ ^ 2) + eps := by
  have hq : 1 / 4 ≤ ‖x - 0‖ ^ 2 := le_trans (by nlinarith [rho_bounds.1]) hτ
  rw [hOut, logRad_apply, max_eq_left hq, pH,
    floorCap_of_mem_Icc (by norm_num) one_pos (ah_mid hτ hτ1)]

theorem hOut_pos {x : E 2} (hτ : rho ^ 2 < ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 1) : 0 < hOut x := by
  rw [hOut_eq hτ.le hτ1, ah_eq]
  have := Real.log_lt_log (by nlinarith [rho_bounds.1]) hτ
  nlinarith [rho_bounds.1]

theorem hOut_eq_zero {x : E 2} (hτ : ‖x - 0‖ ^ 2 = rho ^ 2) : hOut x = 0 := by
  rw [hOut_eq hτ.ge (by rw [hτ]; exact rho_sq_bounds.2.le), ah_eq, hτ]; ring

theorem laplacian_hOut {x : E 2} (hτ : rho ^ 2 ≤ ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 1) :
    Δ hOut x = 0 :=
  laplacian_logRad_mid (by norm_num) one_pos (by norm_num) (by norm_num) clamp_hOut
    (lt_of_lt_of_le (by nlinarith [rho_bounds.1]) hτ) (ah_mid hτ hτ1)

theorem norm_gradient_hOut {x : E 2} (hτ : ‖x - 0‖ ^ 2 = rho ^ 2) : ‖∇ hOut x‖ = 1 := by
  have hr := rho_bounds
  rw [hOut, pH, norm_gradient_logRad_mid (by norm_num) one_pos (by norm_num) (by norm_num)
    clamp_hOut (by rw [hτ]; nlinarith) (ah_mid hτ.ge (by rw [hτ]; exact rho_sq_bounds.2.le)),
    norm_eq_of_sq (s := rho) (by linarith) hτ, abs_of_pos (by linarith)]
  field_simp
  exact div_self (by linarith)

/-! ### `v` on the regions of `U` -/

theorem mem_domain_norm {x : E 2} (hx : x ∈ domain) :
    ‖x - 0‖ ^ 2 < 1 ∧ 1 / 400 < ‖x - hole‖ ^ 2 ∧ 1 / 400 < ‖x + hole‖ ^ 2 := by
  rw [mem_domain_iff] at hx
  rw [sub_zero, norm_sq_eq, norm_sub_hole_sq, norm_add_hole_sq]
  exact hx

theorem geom_plus_le {x : E 2} (h : ‖x - hole‖ ^ 2 ≤ 1 / 100) :
    1 / 100 ≤ ‖x + hole‖ ^ 2 ∧ ‖x - 0‖ ^ 2 ≤ 1 / 25 := by
  rw [norm_sub_hole_sq] at h
  rw [norm_add_hole_sq, sub_zero, norm_sq_eq]
  constructor <;> nlinarith [sq_nonneg (x 0 - 1 / 10), sq_nonneg (x 1)]

theorem geom_minus_le {x : E 2} (h : ‖x + hole‖ ^ 2 ≤ 1 / 100) :
    1 / 100 ≤ ‖x - hole‖ ^ 2 ∧ ‖x - 0‖ ^ 2 ≤ 1 / 25 := by
  rw [norm_add_hole_sq] at h
  rw [norm_sub_hole_sq, sub_zero, norm_sq_eq]
  constructor <;> nlinarith [sq_nonneg (x 0 + 1 / 10), sq_nonneg (x 1)]

theorem eq_zero_of_both {x : E 2} (h1 : ‖x - hole‖ ^ 2 = 1 / 100) (h2 : ‖x + hole‖ ^ 2 = 1 / 100) :
    x = 0 := by
  rw [norm_sub_hole_sq] at h1
  rw [norm_add_hole_sq] at h2
  have h0 : x 0 = 0 := by nlinarith
  have h1' : x 1 ^ 2 = 0 := by rw [h0] at h1; nlinarith
  have : ‖x‖ ^ 2 = 0 := by rw [norm_sq_eq, h0, h1']; ring
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

theorem rho_sq_gt_quarter : 1 / 25 < rho ^ 2 := by linarith [rho_sq_bounds.1]

theorem vSup_eq_plus {y : E 2} (h : ‖y - hole‖ ^ 2 ≤ 1 / 100) :
    vSup y = max (wIn hole y) 0 := by
  obtain ⟨hm, h0⟩ := geom_plus_le h
  rw [vSup, max_wIn_eq_zero (z := -hole) (by rw [sq_sub_neg_hole]; exact hm),
    max_hOut_eq_zero (by linarith [rho_sq_gt_quarter])]
  ring

theorem vSup_eq_minus {y : E 2} (h : ‖y + hole‖ ^ 2 ≤ 1 / 100) :
    vSup y = max (wIn (-hole) y) 0 := by
  obtain ⟨hp, h0⟩ := geom_minus_le h
  rw [vSup, max_wIn_eq_zero (z := hole) hp, max_hOut_eq_zero (by linarith [rho_sq_gt_quarter])]
  ring

theorem vSup_eq_out {y : E 2} (h : 1 / 2 < ‖y - 0‖ ^ 2) : vSup y = max (hOut y) 0 := by
  obtain ⟨hp, hm⟩ := geom_out h
  rw [vSup, max_wIn_eq_zero (z := hole) hp,
    max_wIn_eq_zero (z := -hole) (by rw [sq_sub_neg_hole]; exact hm)]
  ring

/-! ### `v` is a viscosity supersolution -/

theorem tendsto_ray (x ξ : E 2) :
    Tendsto (fun t : ℝ ↦ x + t • ξ) (𝓝[>] 0) (𝓝 x) := by
  have : Continuous fun t : ℝ ↦ x + t • ξ := by fun_prop
  have h := this.tendsto 0
  simp only [zero_smul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem isOpen_lt_normsq (z : E 2) (c : ℝ) : IsOpen {y : E 2 | ‖y - z‖ ^ 2 < c} :=
  isOpen_lt (by fun_prop) continuous_const

theorem isOpen_gt_normsq (z : E 2) (c : ℝ) : IsOpen {y : E 2 | c < ‖y - z‖ ^ 2} :=
  isOpen_lt continuous_const (by fun_prop)

/-- The free boundary step: if `φ(x) = 0 = W(x)`, `|∇W(x)| = 1` and `φ ≤ max W 0` near `x`, then
`|∇φ(x)| ≤ 1`. -/
theorem fb_step {φ W : E 2 → ℝ} {x : E 2} (hφ : ContDiff ℝ 2 φ) (hW : ContDiff ℝ 2 W)
    (hφx : φ x = 0) (hWx : W x = 0) (hg : ‖∇ W x‖ = 1)
    (hle : ∀ᶠ y in 𝓝 x, φ y ≤ max (W y) 0) : ‖∇ φ x‖ ≤ 1 := by
  have := norm_gradient_le_of_ray (hφ.differentiable (by norm_num) x)
    (hW.differentiable (by norm_num) x).hasGradientAt hφx hWx
    ((tendsto_ray x (∇ φ x)).eventually hle)
  rwa [hg] at this

theorem isViscSuper_vSup : IsViscSuper domain (fun _ ↦ 1) vSup := by
  refine ⟨continuous_vSup.continuousOn, fun x _ ↦ vSup_nonneg x, fun φ hφ x hx htouch ↦ ?_⟩
  obtain ⟨-, hφx, hle⟩ := htouch
  rw [isOpen_domain.nhdsWithin_eq hx] at hle
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_of_smooth hφ
  obtain ⟨h0, hp, hm⟩ := mem_domain_norm hx
  have hUn := isOpen_domain.mem_nhds hx
  -- the right disc
  rcases lt_or_ge (‖x - hole‖ ^ 2) (1 / 100) with A | A
  · left
    have hO : ∀ᶠ y in 𝓝 x, vSup y = wIn hole y := by
      filter_upwards [hUn, (isOpen_lt_normsq hole _).mem_nhds A] with y hyU hyA
      obtain ⟨-, hyp, -⟩ := mem_domain_norm hyU
      rw [vSup_eq_plus (le_of_lt hyA), max_eq_left (wIn_pos hyp.le hyA).le]
    calc Δ φ x ≤ Δ (wIn hole) x := laplacian_le_of_touch hφ2 (contDiff_wIn hole)
          (by filter_upwards [hle, hO] with y h1 h2; rwa [← h2]) (hφx.trans hO.self_of_nhds)
      _ = 0 := laplacian_wIn hp.le A.le
  -- the left disc
  rcases lt_or_ge (‖x + hole‖ ^ 2) (1 / 100) with B | B
  · left
    have hO : ∀ᶠ y in 𝓝 x, vSup y = wIn (-hole) y := by
      filter_upwards [hUn, (isOpen_lt_normsq (-hole) (1 / 100)).mem_nhds
        (by rw [mem_setOf_eq, sq_sub_neg_hole]; exact B)] with y hyU hyB
      obtain ⟨-, -, hym⟩ := mem_domain_norm hyU
      rw [sq_sub_neg_hole] at hyB
      rw [vSup_eq_minus hyB.le, max_eq_left
        (wIn_pos (by rw [sq_sub_neg_hole]; exact hym.le) (by rw [sq_sub_neg_hole]; exact hyB)).le]
    calc Δ φ x ≤ Δ (wIn (-hole)) x := laplacian_le_of_touch hφ2 (contDiff_wIn (-hole))
          (by filter_upwards [hle, hO] with y h1 h2; rwa [← h2]) (hφx.trans hO.self_of_nhds)
      _ = 0 := laplacian_wIn (by rw [sq_sub_neg_hole]; exact hm.le)
          (by rw [sq_sub_neg_hole]; exact B.le)
  -- the outer layer
  rcases lt_or_ge (rho ^ 2) (‖x - 0‖ ^ 2) with C | C
  · left
    have hO : ∀ᶠ y in 𝓝 x, vSup y = hOut y := by
      filter_upwards [hUn, (isOpen_gt_normsq 0 _).mem_nhds C] with y hyU hyC
      obtain ⟨hy0, -, -⟩ := mem_domain_norm hyU
      rw [vSup_eq_out (by linarith [rho_sq_bounds.1, show rho ^ 2 < ‖y - 0‖ ^ 2 from hyC]),
        max_eq_left (hOut_pos hyC hy0.le).le]
    calc Δ φ x ≤ Δ hOut x := laplacian_le_of_touch hφ2 contDiff_hOut
          (by filter_upwards [hle, hO] with y h1 h2; rwa [← h2]) (hφx.trans hO.self_of_nhds)
      _ = 0 := laplacian_hOut C.le h0.le
  -- the zero set
  right
  have hv0 : vSup x = 0 := by
    rw [vSup, max_wIn_eq_zero (z := hole) A,
      max_wIn_eq_zero (z := -hole) (by rw [sq_sub_neg_hole]; exact B), max_hOut_eq_zero C]
    ring
  have hφ0 : φ x = 0 := hφx.trans hv0
  refine ⟨hφ0, ?_⟩
  by_cases hx0 : x = 0
  · -- the two-plane point: use the disc on the side of `∇φ(0)`
    subst hx0
    set ξ := ∇ φ 0 with hξ
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖(0 : E 2) + t • ξ - 0‖ ^ 2 < 1 / 25 := by
      have := (tendsto_ray (0 : E 2) ξ).eventually ((isOpen_lt_normsq 0 (1 / 25)).mem_nhds
        (by simp))
      exact this
    have hle' := (tendsto_ray (0 : E 2) ξ).eventually hle
    have hφd := hφ2.differentiable (by norm_num) (0 : E 2)
    rcases le_total 0 (ξ 0) with hξ0 | hξ0
    · have hW0 : ‖(0 : E 2) - hole‖ ^ 2 = 1 / 100 := by simp [norm_hole]; norm_num
      refine le_trans (norm_gradient_le_of_ray hφd
        ((contDiff_wIn hole).differentiable (by norm_num) 0).hasGradientAt hφ0 (wIn_eq_zero hW0)
        ?_) (norm_gradient_wIn hW0).le
      filter_upwards [hle', hsmall, self_mem_nhdsWithin] with t h1 h2 h3
      have h3 : (0 : ℝ) < t := h3
      rw [vSup, max_wIn_eq_zero (z := -hole) ?_, max_hOut_eq_zero (by linarith [rho_sq_gt_quarter])]
        at h1
      · linarith
      · rw [sq_sub_neg_hole, norm_add_hole_sq]
        simp only [zero_add, PiLp.smul_apply, smul_eq_mul]
        nlinarith [mul_nonneg h3.le hξ0, sq_nonneg (t * ξ 1)]
    · have hW0 : ‖(0 : E 2) - -hole‖ ^ 2 = 1 / 100 := by simp [norm_hole]; norm_num
      refine le_trans (norm_gradient_le_of_ray hφd
        ((contDiff_wIn (-hole)).differentiable (by norm_num) 0).hasGradientAt hφ0
        (wIn_eq_zero hW0) ?_) (norm_gradient_wIn hW0).le
      filter_upwards [hle', hsmall, self_mem_nhdsWithin] with t h1 h2 h3
      have h3 : (0 : ℝ) < t := h3
      rw [vSup, max_wIn_eq_zero (z := hole) ?_, max_hOut_eq_zero (by linarith [rho_sq_gt_quarter])]
        at h1
      · linarith
      · rw [norm_sub_hole_sq]
        simp only [zero_add, PiLp.smul_apply, smul_eq_mul]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h3.le hξ0, sq_nonneg (t * ξ 1)]
  -- free boundary points other than `0`, and interior zeros
  by_cases hA : ‖x - hole‖ ^ 2 = 1 / 100
  · have hB' : 1 / 100 < ‖x + hole‖ ^ 2 :=
      lt_of_le_of_ne B fun h ↦ hx0 (eq_zero_of_both hA h.symm)
    have hC' : ‖x - 0‖ ^ 2 < rho ^ 2 := by
      linarith [(geom_plus_le hA.le).2, rho_sq_gt_quarter]
    refine fb_step hφ2 (contDiff_wIn hole) hφ0 (wIn_eq_zero hA) (norm_gradient_wIn hA) ?_
    filter_upwards [hle, (isOpen_gt_normsq (-hole) (1 / 100)).mem_nhds
      (show 1 / 100 < ‖x - -hole‖ ^ 2 by rw [sq_sub_neg_hole]; exact hB'),
      (isOpen_lt_normsq 0 (rho ^ 2)).mem_nhds hC'] with y h1 h2 h3
    have h2 : 1 / 100 < ‖y - -hole‖ ^ 2 := h2
    have h3 : ‖y - 0‖ ^ 2 < rho ^ 2 := h3
    rw [vSup, max_wIn_eq_zero (z := -hole) h2.le, max_hOut_eq_zero h3.le] at h1
    linarith
  by_cases hB : ‖x + hole‖ ^ 2 = 1 / 100
  · have hA' : 1 / 100 < ‖x - hole‖ ^ 2 :=
      lt_of_le_of_ne A fun h ↦ hx0 (eq_zero_of_both h.symm hB)
    have hC' : ‖x - 0‖ ^ 2 < rho ^ 2 := by
      linarith [(geom_minus_le hB.le).2, rho_sq_gt_quarter]
    have hB2 : ‖x - -hole‖ ^ 2 = 1 / 100 := by rw [sq_sub_neg_hole]; exact hB
    refine fb_step hφ2 (contDiff_wIn (-hole)) hφ0 (wIn_eq_zero hB2) (norm_gradient_wIn hB2) ?_
    filter_upwards [hle, (isOpen_gt_normsq hole (1 / 100)).mem_nhds hA',
      (isOpen_lt_normsq 0 (rho ^ 2)).mem_nhds hC'] with y h1 h2 h3
    have h2 : 1 / 100 < ‖y - hole‖ ^ 2 := h2
    have h3 : ‖y - 0‖ ^ 2 < rho ^ 2 := h3
    rw [vSup, max_wIn_eq_zero (z := hole) h2.le, max_hOut_eq_zero h3.le] at h1
    linarith
  by_cases hC : ‖x - 0‖ ^ 2 = rho ^ 2
  · refine fb_step hφ2 contDiff_hOut hφ0 (hOut_eq_zero hC) (norm_gradient_hOut hC) ?_
    filter_upwards [hle, (isOpen_gt_normsq 0 (1 / 2)).mem_nhds
      (show 1 / 2 < ‖x - 0‖ ^ 2 by rw [hC]; linarith [rho_sq_bounds.1])] with y h1 h2
    rwa [vSup_eq_out h2] at h1
  -- interior zeros: `φ` has a local maximum
  have hA' : 1 / 100 < ‖x - hole‖ ^ 2 := lt_of_le_of_ne A (Ne.symm hA)
  have hB' : 1 / 100 < ‖x - -hole‖ ^ 2 := by
    rw [sq_sub_neg_hole]; exact lt_of_le_of_ne B (Ne.symm hB)
  have hC' : ‖x - 0‖ ^ 2 < rho ^ 2 := lt_of_le_of_ne C hC
  have hmax : IsLocalMax φ x := by
    filter_upwards [hle, (isOpen_gt_normsq hole (1 / 100)).mem_nhds hA',
      (isOpen_gt_normsq (-hole) (1 / 100)).mem_nhds hB',
      (isOpen_lt_normsq 0 (rho ^ 2)).mem_nhds hC'] with y h1 h2 h3 h4
    have h2 : 1 / 100 < ‖y - hole‖ ^ 2 := h2
    have h3 : 1 / 100 < ‖y - -hole‖ ^ 2 := h3
    have h4 : ‖y - 0‖ ^ 2 < rho ^ 2 := h4
    rw [vSup, max_wIn_eq_zero h2.le, max_wIn_eq_zero h3.le, max_hOut_eq_zero h4.le] at h1
    rw [hφ0]; linarith
  rw [gradient_eq_zero_of_isLocalMax hmax, norm_zero]
  norm_num

/-! ### `v` lies above `gSub` -/

theorem le_vSup_of_wIn {x : E 2} {z : E 2} (hz : z = hole ∨ z = -hole) {t : ℝ}
    (ht : t ≤ wIn z x) : t ≤ vSup x := by
  unfold vSup
  have := le_max_right (wIn hole x) 0
  have := le_max_right (wIn (-hole) x) 0
  have := le_max_right (hOut x) 0
  rcases hz with rfl | rfl
  · have := le_max_left (wIn hole x) 0; linarith
  · have := le_max_left (wIn (-hole) x) 0; linarith

/-- The inner pieces of `gSub` lie below the disc pieces of `v` (both are affine in `log τ`,
equal at `τ = 1/400`, and `gSub` decreases faster). -/
theorem qIn_le_wIn {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) (hτ' : ‖x - z‖ ^ 2 ≤ 1 / 100)
    (hpos : 0 < qIn z x) : qIn z x ≤ wIn z x := by
  set τ := ‖x - z‖ ^ 2 with hτdef
  have hval : qIn z x = pIn (-cst * Real.log τ + kIn) := by
    rw [qIn, logRad_apply, max_eq_left (by linarith)]
  have htf : tF ≤ -cst * Real.log τ + kIn := by
    by_contra h
    have := floorCap_le_floor (Lc := cst) (tc := cst) lF_pos cst_pos tF_le_cst (not_le.1 h).le
    rw [← pIn, ← hval] at this
    unfold tF at this; linarith
  rw [hval, pIn, floorCap_of_mem_Icc lF_pos cst_pos ⟨htf, qIn_arg_le_cst hτ⟩, wIn_eq hτ hτ']
  have hL : Real.log (1 / 400) ≤ Real.log τ := Real.log_le_log (by norm_num) hτ
  have := log_hundredth_sub
  have hc := cst_bounds
  unfold kIn
  have hc' : cst = Real.log 2 / 10 := rfl
  nlinarith

theorem gSub_le_vSup {x : E 2} (hx : x ∈ closure domain) : gSub x ≤ vSup x := by
  obtain ⟨h0, hp, hm⟩ := mem_closure_domain hx
  rcases le_or_gt (gSub x) 0 with hg | hg
  · exact hg.trans (vSup_nonneg x)
  by_cases A : ‖x - hole‖ ^ 2 < 1 / 100
  · obtain ⟨hm', h0'⟩ := geom_plus A
    have hval : gSub x = qIn hole x := by
      rw [gSub, (qIn_floor (z := -hole) (x := x) (by rw [sq_sub_neg_hole]; exact hm')).1,
        (qOut_floor h0').1]; ring
    rw [hval] at hg ⊢
    exact le_vSup_of_wIn (Or.inl rfl) (qIn_le_wIn hp A.le hg)
  by_cases B : ‖x + hole‖ ^ 2 < 1 / 100
  · obtain ⟨hp', h0'⟩ := geom_minus B
    have hval : gSub x = qIn (-hole) x := by
      rw [gSub, (qIn_floor (z := hole) (x := x) hp').1, (qOut_floor h0').1]; ring
    rw [hval] at hg ⊢
    exact le_vSup_of_wIn (Or.inr rfl)
      (qIn_le_wIn (by rw [sq_sub_neg_hole]; exact hm) (by rw [sq_sub_neg_hole]; exact B.le) hg)
  push Not at A B
  have f1 := qIn_floor (z := hole) (x := x) A
  have f2 := qIn_floor (z := -hole) (x := x) (by rw [sq_sub_neg_hole]; exact B)
  by_cases C : 1 / 2 < ‖x - 0‖ ^ 2
  · have hval : gSub x = qOut x := by rw [gSub, f1.1, f2.1]; ring
    rw [hval] at hg ⊢
    set τ := ‖x - 0‖ ^ 2 with hτdef
    have hqv : qOut x = pOut (rho * Real.log τ + eps) := by
      rw [qOut, logRad_apply, max_eq_left (by linarith)]
    have htf : tF ≤ rho * Real.log τ + eps := by
      by_contra h
      have := floorCap_le_floor (Lc := 1) (tc := 1) lF_pos one_pos tF_le_one (not_le.1 h).le
      rw [← pOut, ← hqv] at this
      unfold tF at this; linarith
    have hlog : Real.log τ ≤ 0 := Real.log_nonpos (by positivity) h0
    have hq : qOut x = rho * Real.log τ + eps := by
      rw [hqv, pOut, floorCap_of_mem_Icc lF_pos one_pos ⟨htf, ?_⟩]
      have := rho_bounds; have := eps_bounds; nlinarith
    have hr := rho_bounds
    rcases le_or_gt (rho ^ 2) τ with D | D
    · have hh : hOut x = rho / 2 * Real.log τ + eps := hOut_eq D h0
      have : qOut x ≤ hOut x := by rw [hq, hh]; nlinarith
      unfold vSup
      have := le_max_left (hOut x) 0
      have := le_max_right (wIn hole x) 0
      have := le_max_right (wIn (-hole) x) 0
      linarith
    · -- off the outer layer `gSub ≤ 0`
      exfalso
      have : rho / 2 * Real.log τ + eps < 0 := by
        rw [ah_eq]
        have := Real.log_lt_log (by positivity) D
        nlinarith
      rw [hq] at hg
      nlinarith
  · push Not at C
    have : gSub x = -3 / 200 := by rw [gSub, f1.1, f2.1, (qOut_floor C).1]; ring
    linarith

/-- **The upper bound.** `v` belongs to Perron's class `𝒮_{gSub}`. -/
theorem vSup_mem_perronSuperClass : vSup ∈ perronSuperClass domain (fun _ ↦ 1) gSub :=
  ⟨continuous_vSup.continuousOn, isViscSuper_vSup,
    fun x hx ↦ max_le (gSub_le_vSup hx) (vSup_nonneg x)⟩

/-- `u_min ≤ v` on `Ū`. -/
theorem perronSmallest_le_vSup {x : E 2} (hx : x ∈ closure domain) :
    perronSmallest domain (fun _ ↦ 1) gSub x ≤ vSup x :=
  perronSmallest_le vSup_mem_perronSuperClass hx

end PerronVariational.TwoDisc

end
