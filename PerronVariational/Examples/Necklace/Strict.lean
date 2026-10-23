/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.Data
public import PerronVariational.Examples.TwoDisc.Strict

/-!
# Strictness of the data of the necklace example

For the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M. Feldman, K.
Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`):

* `isStrictSub_gSub`: `gSub` is a smooth strict subsolution with `a₀ = 1/1000`, `δ₀ = 1`. Its
  pieces are subharmonic on `Ū`; on the band `{|gSub| ≤ a₀}` exactly one piece is active, with
  slope `≥ √2`.
* `isStrictSuper_gSuper`: `gSuper` is a smooth strict supersolution with `a₀ = 1/1000`,
  `δ₀ = 1/10`. Where `gSuper > -a₀` it is a concave profile of a harmonic function, and its slope
  on the band is at most `2/|x| ≤ 0.61`.
* `gSub_eq_gSuper_of_mem_frontier`: `gSub = gSuper > 0` on `∂U` (`= c` on the hole circles, `= ε`
  on `∂B₄`).
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian

@[expose] public noncomputable section

namespace PerronVariational.Necklace

open TwoDisc (floorCap logRad logRad_apply pIn pOut pSup qIn tF lF cst cst_pos cst_bounds
  lF_pos tF_le_one tF_le_cst tF_le_half_cst floor_val floor_thr floorCap_of_le_floor
  floorCap_of_cap_le floorCap_of_mem_Icc floorCap_le_floor cap_le_floorCap contDiff_floorCap
  logRad_eq_floor norm_gradient_logRad_mid laplacian_logRad_nonpos laplacian_logRad_nonneg
  laplacian_logRad_of_lt_clamp qIn_floor contDiff_qIn aZero qIn_band laplacian_qIn_nonneg
  qIn_of_circle)

/-! ### The band estimates -/

theorem qLayer_band {x : E 2} (hτ : 15 < ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 16)
    (hband : |qLayer x| ≤ aZero) : 2 ≤ ‖∇ qLayer x‖ ^ 2 := by
  set τ := ‖x - 0‖ ^ 2 with hτdef
  have hτ0 : 0 < τ := by linarith
  have hval : qLayer x = pOut (4 * Real.log τ + (epsOut - 4 * Real.log 16)) := by
    rw [qLayer, logRad_apply, max_eq_left (by linarith)]
  set t := 4 * Real.log τ + (epsOut - 4 * Real.log 16) with ht
  have htc : t ≤ 1 := by
    have : Real.log τ ≤ Real.log 16 := Real.log_le_log hτ0 hτ1
    have := epsOut_bounds.2; linarith
  have htf : tF ≤ t := by
    by_contra h
    have := floorCap_le_floor (Lc := 1) (tc := 1) lF_pos one_pos tF_le_one (not_le.1 h).le
    rw [← pOut, ← hval] at this
    have := (abs_le.1 hband).1
    unfold tF aZero at *; linarith
  rw [qLayer, pOut, norm_gradient_logRad_mid lF_pos one_pos one_pos (by norm_num) clamp_qLayer
    (by rw [← hτdef]; linarith) ⟨htf, htc⟩, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_pow,
    ← hτdef, le_div_iff₀ hτ0]
  linarith

theorem sOut_band {x : E 2} (hτ : 15 < ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 16)
    (hband : |sOut x| ≤ aZero) : ‖∇ sOut x‖ ^ 2 ≤ 1 - 1 / 10 := by
  set τ := ‖x - 0‖ ^ 2 with hτdef
  have hτ0 : 0 < τ := by linarith
  have hval : sOut x = pOut (1 * Real.log τ + (epsOut - Real.log 16)) := by
    rw [sOut, logRad_apply, max_eq_left (by linarith)]
  set t := 1 * Real.log τ + (epsOut - Real.log 16) with ht
  have htc : t ≤ 1 := by
    have : Real.log τ ≤ Real.log 16 := Real.log_le_log hτ0 hτ1
    have := epsOut_bounds.2; linarith
  have htf : tF ≤ t := by
    by_contra h
    have := floorCap_le_floor (Lc := 1) (tc := 1) lF_pos one_pos tF_le_one (not_le.1 h).le
    rw [← pOut, ← hval] at this
    have := (abs_le.1 hband).1
    unfold tF aZero at *; linarith
  rw [sOut, pOut, norm_gradient_logRad_mid lF_pos one_pos one_pos (by norm_num) clamp_sOut
    (by rw [← hτdef]; linarith) ⟨htf, htc⟩, abs_one, div_pow, ← hτdef, div_le_iff₀ hτ0]
  linarith

theorem sIn_band {x : E 2} (hband : |sIn x| ≤ aZero) : ‖∇ sIn x‖ ^ 2 ≤ 1 - 1 / 10 := by
  set τ := ‖x - 0‖ ^ 2 with hτdef
  have hτ : 10.83 < τ := by
    by_contra h
    push Not at h
    rw [sIn_of_le h, abs_of_pos cst_pos] at hband
    have := cst_bounds.1; unfold aZero at hband; linarith
  have hτ0 : 0 < τ := by linarith
  have hval : sIn x = pSup (-1 * Real.log τ + Real.log (49 / 4)) := by
    rw [sIn, logRad_apply, max_eq_left (by linarith)]
  set t := -1 * Real.log τ + Real.log (49 / 4) with ht
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
    have := cst_bounds.1
    unfold aZero at *; linarith
  rw [sIn, pSup, norm_gradient_logRad_mid lF_pos cst_pos one_pos (by norm_num) clamp_sIn
    (by rw [← hτdef]; linarith) ⟨htf, htc⟩, abs_neg, abs_one, div_pow, ← hτdef, div_le_iff₀ hτ0]
  linarith

/-! ### `gSub` is a strict subsolution -/

theorem laplacian_qLayer_nonneg {x : E 2} (hτ1 : ‖x - 0‖ ^ 2 ≤ 16) : 0 ≤ Δ qLayer x := by
  rcases le_or_gt (‖x - 0‖ ^ 2) 15 with h | h
  · rw [(qLayer_floor h).2.2]
  · refine laplacian_logRad_nonneg lF_pos one_pos one_pos (by norm_num) clamp_qLayer
      (by linarith) ?_
    have : Real.log (‖x - 0‖ ^ 2) ≤ Real.log 16 := Real.log_le_log (by linarith) hτ1
    have := epsOut_bounds.2
    linarith

theorem isStrictSub_gSub : IsStrictSub domain (fun _ ↦ 1) gSub := by
  refine ⟨contDiff_gSub, aZero, by norm_num [aZero], 1, one_pos, fun x hx _ ↦ ?_,
    fun x hx hband ↦ ?_⟩
  · obtain ⟨h0, hk⟩ := normSq_of_mem_closure hx
    rw [laplacian_gSub, laplacian_qSum]
    have := Finset.sum_nonneg fun (k : Fin numHoles) (_ : k ∈ Finset.univ) ↦
      laplacian_qIn_nonneg (z := cen ((k : ℕ) : ℤ)) (hk k)
    have := laplacian_qLayer_nonneg h0
    linarith
  obtain ⟨h0, hk⟩ := normSq_of_mem_closure hx
  norm_num only
  by_cases A : ∃ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 < 1 / 100
  · obtain ⟨k, hk'⟩ := A
    obtain ⟨hs, hg⟩ := qSum_of_disc hk'.le
    have h15 : ‖x - 0‖ ^ 2 ≤ 15 := by linarith [(geom_disc hk'.le).2]
    have f := qLayer_floor h15
    have hval : gSub x = qIn (cen ((k : ℕ) : ℤ)) x := by rw [gSub_eq, hs, f.1]; ring
    rw [(hasGradientAt_gSub hg f.2.1).gradient, add_zero]
    exact qIn_band (hk k) (hval ▸ hband)
  push Not at A
  obtain ⟨hs, hg⟩ := qSum_of_far A
  by_cases C : 15 < ‖x - 0‖ ^ 2
  · have hval : gSub x = qLayer x := by rw [gSub_eq, hs]; ring
    rw [(hasGradientAt_gSub hg
      (contDiff_qLayer.differentiable (by norm_num) x).hasGradientAt).gradient, zero_add]
    exact qLayer_band C h0 (hval ▸ hband)
  · push Not at C
    have hval : gSub x = -3 / 200 := by rw [gSub_eq, hs, (qLayer_floor C).1]; ring
    rw [hval] at hband
    norm_num [aZero] at hband

/-! ### `gSuper` is a strict supersolution -/

theorem isStrictSuper_gSuper : IsStrictSuper domain (fun _ ↦ 1) gSuper := by
  refine ⟨contDiff_gSuper, aZero, by norm_num [aZero], 1 / 10, by norm_num,
    fun x hx hpos ↦ ?_, fun x hx hband ↦ ?_⟩
  · obtain ⟨h0, -⟩ := normSq_of_mem_closure hx
    rw [laplacian_gSuper]
    rcases le_or_gt 12.5 (‖x - 0‖ ^ 2) with A | A
    · rw [(sIn_floor A).2.2, zero_add]
      rcases le_or_gt (‖x - 0‖ ^ 2) 15 with B | B
      · rw [(sOut_floor B).2.2]
      · have hval : gSuper x = sOut x := by rw [gSuper, (sIn_floor A).1]; ring
        have hmax : max (‖x - 0‖ ^ 2) 1 = ‖x - 0‖ ^ 2 := max_eq_left (by linarith)
        refine laplacian_logRad_nonpos lF_pos one_pos one_pos (by norm_num) clamp_sOut
          (by linarith) ?_
        by_contra h
        have := floorCap_le_floor (Lc := 1) (tc := 1) lF_pos one_pos tF_le_one (not_le.1 h).le
        have hr : sOut x = pOut (1 * Real.log (‖x - 0‖ ^ 2) + (epsOut - Real.log 16)) := by
          rw [sOut, logRad_apply, hmax]
        rw [← pOut, ← hr, ← hval] at this
        unfold tF aZero at *; linarith
    · rw [(sOut_floor (by linarith)).2.2, add_zero]
      rcases lt_or_ge (‖x - 0‖ ^ 2) 2 with B | B
      · exact (laplacian_logRad_of_lt_clamp contDiff_floorCap one_pos (by norm_num)
          clamp_sIn B).le
      · have hval : gSuper x = sIn x := by rw [gSuper, (sOut_floor (by linarith)).1]; ring
        have hmax : max (‖x - 0‖ ^ 2) 1 = ‖x - 0‖ ^ 2 := max_eq_left (by linarith)
        refine laplacian_logRad_nonpos lF_pos cst_pos one_pos (by norm_num) clamp_sIn
          (by linarith) ?_
        by_contra h
        have := floorCap_le_floor (Lc := cst) (tc := cst / 2) lF_pos cst_pos tF_le_half_cst
          (not_le.1 h).le
        have hr : sIn x = pSup (-1 * Real.log (‖x - 0‖ ^ 2) + Real.log (49 / 4)) := by
          rw [sIn, logRad_apply, hmax]
        rw [← pSup, ← hr, ← hval] at this
        unfold tF aZero at *; linarith
  obtain ⟨h0, -⟩ := normSq_of_mem_closure hx
  have hdi := (contDiff_sIn.differentiable (by norm_num) x).hasGradientAt
  have hdo := (contDiff_sOut.differentiable (by norm_num) x).hasGradientAt
  norm_num only
  rcases le_or_gt 12.5 (‖x - 0‖ ^ 2) with A | A
  · have f1 := sIn_floor A
    rcases le_or_gt (‖x - 0‖ ^ 2) 15 with B | B
    · have hval : gSuper x = -3 / 200 := by rw [gSuper, f1.1, (sOut_floor B).1]; ring
      rw [hval] at hband; norm_num [aZero] at hband
    · have hval : gSuper x = sOut x := by rw [gSuper, f1.1]; ring
      rw [(hasGradientAt_gSuper f1.2.1 hdo).gradient, zero_add]
      have := sOut_band B h0 (hval ▸ hband)
      linarith
  · have f2 := sOut_floor (x := x) (by linarith)
    have hval : gSuper x = sIn x := by rw [gSuper, f2.1]; ring
    rw [(hasGradientAt_gSuper hdi f2.2.1).gradient, add_zero]
    have := sIn_band (hval ▸ hband)
    linarith

/-! ### Boundary values -/

/-- A point of `∂U` lies on the outer circle or on a hole circle. -/
theorem mem_frontier_cases {x : E 2} (hx : x ∈ frontier domain) :
    ‖x - 0‖ ^ 2 = 16 ∨ ∃ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 = 1 / 400 := by
  have h0 := rhoU_eq_zero_of_mem_frontier hx
  rw [rhoU] at h0
  rcases mul_eq_zero.1 h0 with hA | hB
  · left; rw [sub_zero]; unfold outerRad at hA; linarith
  · right
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hB
    exact ⟨k, by unfold holeRad at hk; linarith⟩

theorem qLayer_of_outer {x : E 2} (h : ‖x - 0‖ ^ 2 = 16) : qLayer x = epsOut := by
  have := epsOut_bounds
  rw [qLayer, logRad_apply, max_eq_left (by rw [h]; norm_num), h, pOut,
    floorCap_of_mem_Icc lF_pos one_pos] <;> [ring; (constructor <;> norm_num [tF] <;> linarith)]

theorem sOut_of_outer {x : E 2} (h : ‖x - 0‖ ^ 2 = 16) : sOut x = epsOut := by
  have := epsOut_bounds
  rw [sOut, logRad_apply, max_eq_left (by rw [h]; norm_num), h, pOut,
    floorCap_of_mem_Icc lF_pos one_pos] <;> [ring; (constructor <;> norm_num [tF] <;> linarith)]

theorem gSub_eq_gSuper_of_mem_frontier {x : E 2} (hx : x ∈ frontier domain) :
    gSub x = gSuper x ∧ 0 < gSub x := by
  rcases mem_frontier_cases hx with h | ⟨k, hk⟩
  · -- the outer circle
    have hfar : ∀ j : Fin numHoles, 1 / 100 ≤ ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 :=
      fun j ↦ (geom_far (by rw [h]; norm_num) _).le
    have hs := (qSum_of_far hfar).1
    have f1 := sIn_floor (x := x) (by rw [h]; norm_num)
    refine ⟨?_, ?_⟩
    · rw [gSub_eq, gSuper, hs, qLayer_of_outer h, f1.1, sOut_of_outer h]; ring
    · rw [gSub_eq, hs, qLayer_of_outer h]; linarith [epsOut_pos]
  · -- a hole circle
    obtain ⟨-, h0⟩ := geom_disc (x := x) (k := k) (by rw [hk]; norm_num)
    have hs := (qSum_of_disc (x := x) (k := k) (by rw [hk]; norm_num)).1
    have f3 := qLayer_floor (x := x) (by linarith)
    have g2 := sOut_floor (x := x) (by linarith)
    refine ⟨?_, ?_⟩
    · rw [gSub_eq, gSuper, hs, qIn_of_circle hk, f3.1, sIn_of_le h0, g2.1]; ring
    · rw [gSub_eq, hs, qIn_of_circle hk, f3.1]; linarith [cst_pos]

end PerronVariational.Necklace

end
