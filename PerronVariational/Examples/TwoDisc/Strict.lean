/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.TwoDisc.Data
public import PerronVariational.Defs.Stationary

/-!
# The data of the two-disc model example are strict

For the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 (`[AFS]`):

* `isStrictSub_gSub`: `gSub` is a smooth strict subsolution in `U` with `Q ≡ 1`
  ([AFS, Definition 2.2]), with `a₀ = 1/1000`, `δ₀ = 1`;
* `isStrictSuper_gSuper`: `gSuper` is a smooth strict supersolution, with `a₀ = 1/1000`,
  `δ₀ = 1/10`;
* `gSub_eq_gSuper_of_mem_frontier`, `gSub_pos_of_mem_frontier`: the two data agree on `∂U`, where
  they are positive.

In each case at most one piece is off its floor, and on the zero level band the active piece is in
the middle of its profile, where it is a logarithm of the distance with explicit slope.
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

/-! ### Numeric facts -/

theorem exp_bound : Real.exp (1 + 3 / 200) < 3 := by
  rw [Real.exp_add]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_bound_div_one_sub_of_interval' (x := 3 / 200) (by norm_num) (by norm_num)
  have h0 : 0 < Real.exp (3 / 200) := Real.exp_pos _
  calc Real.exp 1 * Real.exp (3 / 200) < 2.7182818286 * (1 / (1 - 3 / 200)) := by
        apply mul_lt_mul'' h1 h2 (Real.exp_pos _).le h0.le
    _ < 3 := by norm_num

theorem aZero_div_cst : aZero / cst ≤ 3 / 200 := by
  have := cst_bounds.1
  rw [div_le_iff₀ cst_pos]; unfold aZero; linarith

/-! ### The active pieces on the zero level band -/

/-- The inner pieces of `gSub` on `Ū` stay below their cap. -/
theorem qIn_arg_le_cst {τ : ℝ} (hτ : 1 / 400 ≤ τ) : -cst * Real.log τ + kIn ≤ cst := by
  have := Real.log_le_log (by norm_num) hτ
  unfold kIn; nlinarith [cst_pos]

theorem qIn_band {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) (hband : |qIn z x| ≤ aZero) :
    2 ≤ ‖∇ (qIn z) x‖ ^ 2 := by
  set τ := ‖x - z‖ ^ 2 with hτdef
  have hτ0 : 0 < τ := by linarith
  have hval : qIn z x = pIn (-cst * Real.log τ + kIn) := by
    rw [qIn, logRad_apply, max_eq_left (by linarith)]
  set t := -cst * Real.log τ + kIn with ht
  have htc : t ≤ cst := qIn_arg_le_cst hτ
  have htf : tF ≤ t := by
    by_contra h
    have := floorCap_le_floor (Lc := cst) (tc := cst) lF_pos cst_pos tF_le_cst (not_le.1 h).le
    rw [← pIn, ← hval] at this
    have := (abs_le.1 hband).1
    unfold tF aZero at *; linarith
  have hmid : t ∈ Icc tF cst := ⟨htf, htc⟩
  have hq : qIn z x = t := by rw [hval, pIn, floorCap_of_mem_Icc lF_pos cst_pos hmid]
  rw [qIn, pIn, norm_gradient_logRad_mid lF_pos cst_pos (by norm_num) (by norm_num) clamp_qIn
    (by rw [← hτdef]; linarith) hmid, abs_neg, abs_of_pos cst_pos, div_pow, ← hτdef]
  -- `t ≥ -a₀` gives `400 τ ≤ e^{1 + a₀/c} ≤ 3`
  have hlow : -aZero ≤ t := by rw [← hq]; exact (abs_le.1 hband).1
  have hlog : Real.log (400 * τ) ≤ 1 + 3 / 200 := by
    have e : Real.log (400 * τ) = Real.log τ - Real.log (1 / 400) := by
      rw [Real.log_mul (by norm_num) hτ0.ne', one_div, Real.log_inv]; ring
    rw [e]
    have hc := cst_pos
    have h1 : cst * (Real.log τ - Real.log (1 / 400)) ≤ cst + aZero := by
      rw [ht] at hlow; unfold kIn at hlow; nlinarith
    have h2 : Real.log τ - Real.log (1 / 400) ≤ 1 + aZero / cst := by
      calc _ ≤ (cst + aZero) / cst := by rw [le_div_iff₀ hc]; linarith
        _ = _ := by field_simp
    linarith [aZero_div_cst]
  have h400 : 400 * τ ≤ 3 := by
    have := Real.exp_le_exp.2 hlog
    rw [Real.exp_log (by positivity)] at this
    linarith [exp_bound]
  have hc2 : 3 / 800 ≤ cst ^ 2 := by nlinarith [cst_bounds.1]
  rw [le_div_iff₀ hτ0]
  nlinarith

theorem qOut_band {x : E 2} (hτ : 1 / 2 < ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 1)
    (hband : |qOut x| ≤ aZero) : 2 ≤ ‖∇ qOut x‖ ^ 2 := by
  set τ := ‖x - 0‖ ^ 2 with hτdef
  have hτ0 : 0 < τ := by linarith
  have hval : qOut x = pOut (rho * Real.log τ + eps) := by
    rw [qOut, logRad_apply, max_eq_left (by linarith)]
  set t := rho * Real.log τ + eps with ht
  have htc : t ≤ 1 := by
    have := Real.log_nonpos hτ0.le hτ1
    have := rho_bounds; have := eps_bounds
    nlinarith
  have htf : tF ≤ t := by
    by_contra h
    have := floorCap_le_floor (Lc := 1) (tc := 1) lF_pos one_pos tF_le_one (not_le.1 h).le
    rw [← pOut, ← hval] at this
    have := (abs_le.1 hband).1
    unfold tF aZero at *; linarith
  rw [qOut, pOut, norm_gradient_logRad_mid lF_pos one_pos (by norm_num) (by norm_num) clamp_qOut
    (by rw [← hτdef]; linarith) ⟨htf, htc⟩, abs_of_pos (by linarith [rho_bounds.1]), div_pow,
    ← hτdef, le_div_iff₀ hτ0]
  nlinarith [rho_bounds.1]

theorem rIn_band {x : E 2} (hband : |rIn x| ≤ aZero) : ‖∇ rIn x‖ ^ 2 ≤ 1 - 1 / 10 := by
  set τ := ‖x - 0‖ ^ 2 with hτdef
  have hca := cst_bounds
  -- off the cap region
  have hτ32 : 1 / 32 < τ := by
    by_contra h
    push Not at h
    have hmax : max τ (1 / 100) ≤ 1 / 32 := max_le h (by norm_num)
    have : rIn x = cst := by
      rw [rIn, logRad_apply, pSup_cap (by positivity) hmax]
    rw [this, abs_of_pos cst_pos] at hband
    unfold aZero at hband; linarith
  have hτ0 : 0 < τ := by linarith
  have hval : rIn x = pSup (-(9 / 40) * Real.log τ + -(9 / 20) * Real.log 2) := by
    rw [rIn, logRad_apply, max_eq_left (by linarith)]
  set t := -(9 / 40) * Real.log τ + -(9 / 20) * Real.log 2 with ht
  have htf : tF ≤ t := by
    by_contra h
    have := floorCap_le_floor (Lc := cst) (tc := cst / 2) lF_pos cst_pos tF_le_half_cst
      (not_le.1 h).le
    rw [← pSup, ← hval] at this
    have := (abs_le.1 hband).1
    unfold tF aZero at *; linarith
  have htc : t ≤ cst / 2 := by
    by_contra h
    have := cap_le_floorCap (tf := tF) (lf := lF) (lc := cst) cst_pos lF_pos tF_le_half_cst
      (not_le.1 h).le
    rw [← pSup, ← hval] at this
    have := (abs_le.1 hband).2
    unfold aZero at *; linarith
  have hq : rIn x = t := by rw [hval, pSup, floorCap_of_mem_Icc lF_pos cst_pos ⟨htf, htc⟩]
  rw [rIn, pSup, norm_gradient_logRad_mid lF_pos cst_pos (by norm_num) (by norm_num) clamp_rIn
    (by rw [← hτdef]; linarith) ⟨htf, htc⟩, abs_neg, abs_of_pos (by norm_num), div_pow, ← hτdef]
  -- `t ≤ a₀` gives `4τ ≥ e^{-40 a₀/9} ≥ 1 - 40 a₀/9`
  have hup : t ≤ aZero := by rw [← hq]; exact (abs_le.1 hband).2
  have hlog : -(1 / 225) ≤ Real.log (4 * τ) := by
    have e : Real.log (4 * τ) = Real.log τ + 2 * Real.log 2 := by
      rw [Real.log_mul (by norm_num) hτ0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [e]; rw [ht] at hup; unfold aZero at hup; linarith
  have h4 : 224 / 225 ≤ 4 * τ := by
    have := Real.exp_le_exp.2 hlog
    rw [Real.exp_log (by positivity)] at this
    have := Real.add_one_le_exp (-(1 / 225))
    linarith
  rw [div_le_iff₀ hτ0]
  nlinarith

theorem rOut_band {x : E 2} (hτ : 1 / 2 < ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 1)
    (hband : |rOut x| ≤ aZero) : ‖∇ rOut x‖ ^ 2 ≤ 1 - 1 / 10 := by
  set τ := ‖x - 0‖ ^ 2 with hτdef
  have hτ0 : 0 < τ := by linarith
  have hval : rOut x = pOut (2 * eps * Real.log τ + eps) := by
    rw [rOut, logRad_apply, max_eq_left (by linarith)]
  set t := 2 * eps * Real.log τ + eps with ht
  have htc : t ≤ 1 := by
    have := Real.log_nonpos hτ0.le hτ1
    have := eps_bounds
    nlinarith
  have htf : tF ≤ t := by
    by_contra h
    have := floorCap_le_floor (Lc := 1) (tc := 1) lF_pos one_pos tF_le_one (not_le.1 h).le
    rw [← pOut, ← hval] at this
    have := (abs_le.1 hband).1
    unfold tF aZero at *; linarith
  rw [rOut, pOut, norm_gradient_logRad_mid lF_pos one_pos (by norm_num) (by norm_num) clamp_rOut
    (by rw [← hτdef]; linarith) ⟨htf, htc⟩, abs_of_pos (by linarith [eps_bounds.1]), div_pow,
    ← hτdef, div_le_iff₀ hτ0]
  nlinarith [eps_bounds.2, eps_bounds.1]

/-! ### `gSub` is a strict subsolution -/

theorem laplacian_qIn_nonneg {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) : 0 ≤ Δ (qIn z) x :=
  laplacian_logRad_nonneg lF_pos cst_pos (by norm_num) (by norm_num) clamp_qIn (by linarith)
    (qIn_arg_le_cst hτ)

theorem laplacian_qOut_nonneg {x : E 2} (hτ1 : ‖x - 0‖ ^ 2 ≤ 1) : 0 ≤ Δ qOut x := by
  rcases le_or_gt (‖x - 0‖ ^ 2) (1 / 2) with h | h
  · rw [(qOut_floor h).2.2]
  · refine laplacian_logRad_nonneg lF_pos one_pos (by norm_num) (by norm_num) clamp_qOut
      (by linarith) ?_
    have := Real.log_nonpos (by positivity) hτ1
    have := rho_bounds; have := eps_bounds
    nlinarith

theorem isStrictSub_gSub : IsStrictSub domain (fun _ ↦ 1) gSub := by
  refine ⟨contDiff_gSub, aZero, by norm_num [aZero], 1, one_pos, fun x hx _ ↦ ?_,
    fun x hx hband ↦ ?_⟩
  · obtain ⟨h0, hp, hm⟩ := mem_closure_domain hx
    rw [laplacian_gSub]
    have := laplacian_qIn_nonneg (z := hole) hp
    have := laplacian_qIn_nonneg (z := -hole) (x := x) (by rw [sq_sub_neg_hole]; exact hm)
    have := laplacian_qOut_nonneg h0
    linarith
  obtain ⟨h0, hp, hm⟩ := mem_closure_domain hx
  have hd := fun z ↦ ((contDiff_qIn z).differentiable (by norm_num) x).hasGradientAt
  have hdo := (contDiff_qOut.differentiable (by norm_num) x).hasGradientAt
  norm_num only
  by_cases A : ‖x - hole‖ ^ 2 < 1 / 100
  · obtain ⟨hm', h0'⟩ := geom_plus A
    have f2 := qIn_floor (z := -hole) (x := x) (by rw [sq_sub_neg_hole]; exact hm')
    have f3 := qOut_floor h0'
    have hval : gSub x = qIn hole x := by rw [gSub, f2.1, f3.1]; ring
    rw [(hasGradientAt_gSub (hd hole) f2.2.1 f3.2.1).gradient, add_zero, add_zero]
    exact qIn_band hp (hval ▸ hband)
  by_cases B : ‖x + hole‖ ^ 2 < 1 / 100
  · obtain ⟨hp', h0'⟩ := geom_minus B
    have f1 := qIn_floor (z := hole) (x := x) hp'
    have f3 := qOut_floor h0'
    have hval : gSub x = qIn (-hole) x := by rw [gSub, f1.1, f3.1]; ring
    rw [(hasGradientAt_gSub f1.2.1 (hd (-hole)) f3.2.1).gradient, zero_add, add_zero]
    exact qIn_band (by rw [sq_sub_neg_hole]; exact hm) (hval ▸ hband)
  push Not at A B
  have f1 := qIn_floor (z := hole) (x := x) A
  have f2 := qIn_floor (z := -hole) (x := x) (by rw [sq_sub_neg_hole]; exact B)
  by_cases C : 1 / 2 < ‖x - 0‖ ^ 2
  · have hval : gSub x = qOut x := by rw [gSub, f1.1, f2.1]; ring
    rw [(hasGradientAt_gSub f1.2.1 f2.2.1 hdo).gradient, zero_add, zero_add]
    exact qOut_band C h0 (hval ▸ hband)
  · push Not at C
    have hval : gSub x = -3 / 200 := by rw [gSub, f1.1, f2.1, (qOut_floor C).1]; ring
    rw [hval] at hband
    norm_num [aZero] at hband

/-! ### `gSuper` is a strict supersolution -/

theorem isStrictSuper_gSuper : IsStrictSuper domain (fun _ ↦ 1) gSuper := by
  refine ⟨contDiff_gSuper, aZero, by norm_num [aZero], 1 / 10, by norm_num,
    fun x hx hpos ↦ ?_, fun x hx hband ↦ ?_⟩
  · obtain ⟨h0, -, -⟩ := mem_closure_domain hx
    rw [laplacian_gSuper]
    rcases le_or_gt (3 / 10) (‖x - 0‖ ^ 2) with A | A
    · rw [(rIn_floor A).2.2, zero_add]
      rcases le_or_gt (‖x - 0‖ ^ 2) (1 / 2) with B | B
      · rw [(rOut_floor B).2.2]
      · have hval : gSuper x = rOut x := by rw [gSuper, (rIn_floor A).1]; ring
        have hmax : max (‖x - 0‖ ^ 2) (1 / 4) = ‖x - 0‖ ^ 2 := max_eq_left (by linarith)
        refine laplacian_logRad_nonpos lF_pos one_pos (by norm_num) (by norm_num) clamp_rOut
          (by linarith) ?_
        by_contra h
        have := floorCap_le_floor (Lc := 1) (tc := 1) lF_pos one_pos tF_le_one (not_le.1 h).le
        have hr : rOut x = pOut (2 * eps * Real.log (‖x - 0‖ ^ 2) + eps) := by
          rw [rOut, logRad_apply, hmax]
        rw [← pOut, ← hr, ← hval] at this
        unfold tF aZero at *; linarith
    · rw [(rOut_floor (by linarith)).2.2, add_zero]
      rcases lt_or_ge (‖x - 0‖ ^ 2) (1 / 50) with B | B
      · exact (laplacian_logRad_of_lt_clamp contDiff_floorCap (by norm_num) (by norm_num)
          clamp_rIn B).le
      · have hval : gSuper x = rIn x := by rw [gSuper, (rOut_floor (by linarith)).1]; ring
        have hmax : max (‖x - 0‖ ^ 2) (1 / 100) = ‖x - 0‖ ^ 2 := max_eq_left (by linarith)
        refine laplacian_logRad_nonpos lF_pos cst_pos (by norm_num) (by norm_num) clamp_rIn
          (by linarith) ?_
        by_contra h
        have := floorCap_le_floor (Lc := cst) (tc := cst / 2) lF_pos cst_pos tF_le_half_cst
          (not_le.1 h).le
        have hr : rIn x = pSup (-(9 / 40) * Real.log (‖x - 0‖ ^ 2) + -(9 / 20) * Real.log 2) := by
          rw [rIn, logRad_apply, hmax]
        rw [← pSup, ← hr, ← hval] at this
        unfold tF aZero at *; linarith
  obtain ⟨h0, -, -⟩ := mem_closure_domain hx
  have hdi := (contDiff_rIn.differentiable (by norm_num) x).hasGradientAt
  have hdo := (contDiff_rOut.differentiable (by norm_num) x).hasGradientAt
  norm_num only
  rcases le_or_gt (3 / 10) (‖x - 0‖ ^ 2) with A | A
  · have f1 := rIn_floor A
    rcases le_or_gt (‖x - 0‖ ^ 2) (1 / 2) with B | B
    · have hval : gSuper x = -3 / 200 := by rw [gSuper, f1.1, (rOut_floor B).1]; ring
      rw [hval] at hband; norm_num [aZero] at hband
    · have hval : gSuper x = rOut x := by rw [gSuper, f1.1]; ring
      rw [(hasGradientAt_gSuper f1.2.1 hdo).gradient, zero_add]
      have := rOut_band B h0 (hval ▸ hband)
      linarith
  · have f2 := rOut_floor (x := x) (by linarith)
    have hval : gSuper x = rIn x := by rw [gSuper, f2.1]; ring
    rw [(hasGradientAt_gSuper hdi f2.2.1).gradient, add_zero]
    have := rIn_band (hval ▸ hband)
    linarith

/-! ### Boundary values -/

theorem geom_plus_small {x : E 2} (h : ‖x - hole‖ ^ 2 ≤ 1 / 400) : ‖x - 0‖ ^ 2 ≤ 1 / 32 := by
  rw [norm_sub_hole_sq] at h
  rw [sub_zero, norm_sq_eq]
  nlinarith [sq_nonneg (x 0 - 1 / 10), sq_nonneg (x 1)]

theorem geom_minus_small {x : E 2} (h : ‖x + hole‖ ^ 2 ≤ 1 / 400) : ‖x - 0‖ ^ 2 ≤ 1 / 32 := by
  rw [norm_add_hole_sq] at h
  rw [sub_zero, norm_sq_eq]
  nlinarith [sq_nonneg (x 0 + 1 / 10), sq_nonneg (x 1)]

theorem rIn_of_small {x : E 2} (h : ‖x - 0‖ ^ 2 ≤ 1 / 32) : rIn x = cst := by
  rw [rIn, logRad_apply, pSup_cap (by positivity) (max_le h (by norm_num))]

theorem qIn_of_circle {z x : E 2} (h : ‖x - z‖ ^ 2 = 1 / 400) : qIn z x = cst := by
  rw [qIn, logRad_apply, max_eq_left (by rw [h]; norm_num), h, pIn,
    floorCap_of_mem_Icc lF_pos cst_pos]
  · unfold kIn; ring
  · unfold kIn; constructor <;> nlinarith [cst_pos, tF_le_cst]

theorem gSub_eq_gSuper_of_mem_frontier {x : E 2} (hx : x ∈ frontier domain) :
    gSub x = gSuper x ∧ 0 < gSub x := by
  have h0 := rhoU_eq_zero_of_mem_frontier hx
  rw [rhoU] at h0
  rcases mul_eq_zero.1 h0 with hA | hBC
  · -- the unit circle
    have h1 : ‖x - 0‖ ^ 2 = 1 := by rw [sub_zero]; linarith
    obtain ⟨hp, hm⟩ := geom_out (x := x) (by rw [h1]; norm_num)
    have e1 : qOut x = eps := by
      rw [qOut, logRad_apply, max_eq_left (by rw [h1]; norm_num), h1, Real.log_one, mul_zero,
        zero_add, pOut, floorCap_of_mem_Icc lF_pos one_pos]
      constructor <;> linarith [eps_bounds.1, eps_bounds.2, tF_le_one, show tF < 0 by norm_num [tF]]
    have e2 : rOut x = eps := by
      rw [rOut, logRad_apply, max_eq_left (by rw [h1]; norm_num), h1, Real.log_one, mul_zero,
        zero_add, pOut, floorCap_of_mem_Icc lF_pos one_pos]
      constructor <;> linarith [eps_bounds.1, eps_bounds.2, tF_le_one, show tF < 0 by norm_num [tF]]
    have f1 := qIn_floor (z := hole) (x := x) hp
    have f2 := qIn_floor (z := -hole) (x := x) (by rw [sq_sub_neg_hole]; exact hm)
    have f3 := rIn_floor (x := x) (by rw [h1]; norm_num)
    refine ⟨?_, ?_⟩
    · rw [gSub, gSuper, f1.1, f2.1, e1, f3.1, e2]; ring
    · rw [gSub, f1.1, f2.1, e1]; linarith [eps_pos]
  rcases mul_eq_zero.1 hBC with hB | hC
  · have h1 : ‖x - hole‖ ^ 2 = 1 / 400 := by linarith
    obtain ⟨hm, h0'⟩ := geom_plus (x := x) (by rw [h1]; norm_num)
    have f2 := qIn_floor (z := -hole) (x := x) (by rw [sq_sub_neg_hole]; exact hm)
    have f3 := qOut_floor h0'
    have g1 := rIn_of_small (geom_plus_small h1.le)
    have g2 := rOut_floor h0'
    refine ⟨?_, ?_⟩
    · rw [gSub, gSuper, qIn_of_circle h1, f2.1, f3.1, g1, g2.1]; ring
    · rw [gSub, qIn_of_circle h1, f2.1, f3.1]; linarith [cst_pos]
  · have h1 : ‖x + hole‖ ^ 2 = 1 / 400 := by linarith
    obtain ⟨hp, h0'⟩ := geom_minus (x := x) (by rw [h1]; norm_num)
    have h1' : ‖x - -hole‖ ^ 2 = 1 / 400 := by rw [sq_sub_neg_hole]; exact h1
    have f1 := qIn_floor (z := hole) (x := x) hp
    have f3 := qOut_floor h0'
    have g1 := rIn_of_small (geom_minus_small h1.le)
    have g2 := rOut_floor h0'
    refine ⟨?_, ?_⟩
    · rw [gSub, gSuper, qIn_of_circle h1', f1.1, f3.1, g1, g2.1]; ring
    · rw [gSub, qIn_of_circle h1', f1.1, f3.1]; linarith [cst_pos]

end PerronVariational.TwoDisc

end
