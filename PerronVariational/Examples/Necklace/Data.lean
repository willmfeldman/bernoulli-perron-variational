/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.Domain
public import PerronVariational.Examples.TwoDisc.Data

/-!
# The data of the necklace example

The boundary data of the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M.
Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981 (`[AFS]`). Write `c = log 2 / 10`, `ρ_o = 4 e^{-1/100}`,
`ε = ρ_o / 100`, and `m = -3/200` for the common floor value of the pieces. The pieces are the
floor-and-cap profiles of logarithms of the two-disc model example (`TwoDisc.floorCap`,
`TwoDisc.logRad`).

* `gSub = Σ_k qIn(z_k) + qLayer - 100 m`: `qIn(z_k)` is the inner piece of the two-disc example
  around the centre `z_k` (equal to `c` on the hole circle, active only on `B_a(z_k)`), and
  `qLayer` is a floor profile of `4 log (|x|²/16) + ε` (equal to `ε` on `∂B₄`, active only for
  `|x| > 3.97`).
* `gSuper = sIn + sOut - m`: `sIn` is a profile of `log (12.25/|x|²)`, capped flat at `c` for
  `|x|² ≤ 10.83` (so `gSuper = c` on all holes and on `B̄_{R+a}`), with floor for `|x|² ≥ 12.5`;
  `sOut` is a floor profile of `log (|x|²/16) + ε` (active only for `|x|² > 15`). Between the two
  active regions `gSuper = m < 0`: the dip where the largest subsolution vanishes.

The active regions of the pieces of each datum are pairwise disjoint on `Ū`; outside its active
region each piece sits on its floor `m`.
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian

@[expose] public noncomputable section

namespace PerronVariational.Necklace

open TwoDisc (floorCap logRad logRad_apply pIn pOut pSup qIn tF lF cst cst_pos cst_bounds
  log_two_bounds lF_pos tF_le_one tF_le_cst tF_le_half_cst floor_val floor_thr floorCap_of_le_floor
  floorCap_of_cap_le floorCap_of_mem_Icc ClampConst logRad_eq_floor hasGradientAt_logRad_floor
  laplacian_logRad_floor contDiff_logRad_floorCap qIn_floor contDiff_qIn)

/-! ### Constants -/

/-- The free boundary radius of the outer layer, `ρ_o = 4 e^{-1/100}`. -/
def layerRad : ℝ := 4 * Real.exp (-(1 / 100))

/-- The boundary value on the outer circle, `ε = ρ_o / 100`. -/
def epsOut : ℝ := layerRad / 100

theorem layerRad_bounds : 3.96 ≤ layerRad ∧ layerRad < 4 := by
  have h1 := Real.add_one_le_exp (-(1 / 100))
  have h2 : Real.exp (-(1 / 100)) < 1 := by
    have := Real.exp_lt_exp.2 (show -(1 / 100 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at this
  unfold layerRad; constructor <;> linarith

theorem epsOut_bounds : 0.0396 ≤ epsOut ∧ epsOut < 0.04 := by
  have := layerRad_bounds; unfold epsOut; constructor <;> linarith [this.1, this.2]

theorem epsOut_pos : 0 < epsOut := by linarith [epsOut_bounds.1]

theorem log_layerRad : Real.log layerRad = Real.log 4 - 1 / 100 := by
  rw [layerRad, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]; ring

theorem log_sixteen : Real.log 16 = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring

theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- The constant `3/2 = 100 · (3/200)` compensating the floors of the hole pieces. -/
theorem sum_floor_const : (numHoles : ℝ) * (3 / 200) = 3 / 2 := by norm_num [numHoles]

/-! ### The pieces -/

/-- The outer piece of `gSub`: a floor profile of `4 log (|x|²/16) + ε`. -/
def qLayer : E 2 → ℝ := logRad pOut 0 4 (epsOut - 4 * Real.log 16) 1

/-- The strict subsolution `gSub = Σ_k qIn(z_k) + qLayer + 3/2`. -/
def gSub (x : E 2) : ℝ :=
  ∑ k : Fin numHoles, qIn (cen ((k : ℕ) : ℤ)) x + qLayer x + 3 / 2

/-- The inner piece of `gSuper`: a profile of `log (12.25/|x|²)`, capped flat at `c`. -/
def sIn : E 2 → ℝ := logRad pSup 0 (-1) (Real.log (49 / 4)) 1

/-- The outer piece of `gSuper`: a floor profile of `log (|x|²/16) + ε`. -/
def sOut : E 2 → ℝ := logRad pOut 0 1 (epsOut - Real.log 16) 1

/-- The strict supersolution `gSuper = sIn + sOut + 3/200`. -/
def gSuper (x : E 2) : ℝ := sIn x + sOut x + 3 / 200

/-! ### Arguments of the pieces -/

theorem pOut_floor_of_le {α k τ : ℝ} (h : α * Real.log τ + k ≤ -1 / 50) :
    pOut (α * Real.log τ + k) = -3 / 200 :=
  TwoDisc.pOut_floor_of_le h

theorem log_le_log_fifteen_sixteen {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 15) :
    Real.log τ - Real.log 16 ≤ -(1 / 16) := by
  have h1 : Real.log τ - Real.log 16 = Real.log (τ / 16) := by
    rw [Real.log_div hτ.ne' (by norm_num)]
  rw [h1]
  have := Real.log_le_sub_one_of_pos (show 0 < τ / 16 by positivity)
  linarith

theorem qLayer_arg_floor {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 15) :
    4 * Real.log τ + (epsOut - 4 * Real.log 16) ≤ -1 / 50 := by
  have := log_le_log_fifteen_sixteen hτ h
  have := epsOut_bounds.2
  linarith

theorem sOut_arg_floor {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 15) :
    1 * Real.log τ + (epsOut - Real.log 16) ≤ -1 / 50 := by
  have := log_le_log_fifteen_sixteen hτ h
  have := epsOut_bounds.2
  linarith

theorem sIn_arg_cap {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 10.83) :
    cst / 2 + cst ≤ -1 * Real.log τ + Real.log (49 / 4) := by
  have e : -1 * Real.log τ + Real.log (49 / 4) = Real.log ((49 / 4) / τ) := by
    rw [Real.log_div (by norm_num) hτ.ne']; ring
  rw [e]
  have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < (49 / 4) / τ by positivity)
  rw [inv_div] at h1
  have h2 : τ / (49 / 4) ≤ 10.83 / (49 / 4) := by gcongr
  have := cst_bounds.2
  linarith [show (10.83 : ℝ) / (49 / 4) < 0.885 by norm_num]

theorem sIn_arg_floor {τ : ℝ} (h : 12.5 ≤ τ) : -1 * Real.log τ + Real.log (49 / 4) ≤ -1 / 50 := by
  have hτ : 0 < τ := by linarith
  have e : -1 * Real.log τ + Real.log (49 / 4) = Real.log ((49 / 4) / τ) := by
    rw [Real.log_div (by norm_num) hτ.ne']; ring
  rw [e]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < (49 / 4) / τ by positivity)
  have h2 : (49 / 4) / τ ≤ (49 / 4) / 12.5 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h
  linarith [show (49 / 4 : ℝ) / 12.5 = 0.98 by norm_num]

theorem pSup_cap {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 10.83) :
    pSup (-1 * Real.log τ + Real.log (49 / 4)) = cst := by
  rw [pSup, floorCap_of_cap_le lF_pos cst_pos tF_le_half_cst (sIn_arg_cap hτ h)]; ring

/-! ### Clamping -/

theorem clamp_qLayer : ClampConst pOut 4 (epsOut - 4 * Real.log 16) 1 2 := by
  intro τ hτ
  rw [pOut_floor_of_le (qLayer_arg_floor (by linarith [hτ.1]) (by linarith [hτ.2])),
    pOut_floor_of_le (qLayer_arg_floor (by norm_num) (by norm_num))]

theorem clamp_sOut : ClampConst pOut 1 (epsOut - Real.log 16) 1 2 := by
  intro τ hτ
  rw [pOut_floor_of_le (sOut_arg_floor (by linarith [hτ.1]) (by linarith [hτ.2])),
    pOut_floor_of_le (sOut_arg_floor (by norm_num) (by norm_num))]

theorem clamp_sIn : ClampConst pSup (-1) (Real.log (49 / 4)) 1 2 := by
  intro τ hτ
  rw [pSup_cap (by linarith [hτ.1]) (by linarith [hτ.2]), pSup_cap (by norm_num) (by norm_num)]

/-! ### Floors of the pieces -/

theorem qLayer_floor {x : E 2} (h : ‖x - 0‖ ^ 2 ≤ 15) :
    qLayer x = -3 / 200 ∧ HasGradientAt qLayer 0 x ∧ Δ qLayer x = 0 := by
  have harg : 4 * Real.log (max (‖x - 0‖ ^ 2) 1) + (epsOut - 4 * Real.log 16) ≤ tF - lF := by
    rw [floor_thr]; exact qLayer_arg_floor (by positivity) (max_le h (by norm_num))
  refine ⟨?_, hasGradientAt_logRad_floor lF_pos one_pos tF_le_one one_pos (by norm_num)
    clamp_qLayer harg, laplacian_logRad_floor lF_pos one_pos tF_le_one one_pos (by norm_num)
    clamp_qLayer harg⟩
  rw [qLayer, pOut, logRad_eq_floor lF_pos one_pos tF_le_one harg, floor_val]

theorem sOut_floor {x : E 2} (h : ‖x - 0‖ ^ 2 ≤ 15) :
    sOut x = -3 / 200 ∧ HasGradientAt sOut 0 x ∧ Δ sOut x = 0 := by
  have harg : 1 * Real.log (max (‖x - 0‖ ^ 2) 1) + (epsOut - Real.log 16) ≤ tF - lF := by
    rw [floor_thr]; exact sOut_arg_floor (by positivity) (max_le h (by norm_num))
  refine ⟨?_, hasGradientAt_logRad_floor lF_pos one_pos tF_le_one one_pos (by norm_num)
    clamp_sOut harg, laplacian_logRad_floor lF_pos one_pos tF_le_one one_pos (by norm_num)
    clamp_sOut harg⟩
  rw [sOut, pOut, logRad_eq_floor lF_pos one_pos tF_le_one harg, floor_val]

theorem sIn_floor {x : E 2} (h : 12.5 ≤ ‖x - 0‖ ^ 2) :
    sIn x = -3 / 200 ∧ HasGradientAt sIn 0 x ∧ Δ sIn x = 0 := by
  have harg : -1 * Real.log (max (‖x - 0‖ ^ 2) 1) + Real.log (49 / 4) ≤ tF - lF := by
    rw [max_eq_left (by linarith), floor_thr]; exact sIn_arg_floor h
  refine ⟨?_, hasGradientAt_logRad_floor lF_pos cst_pos tF_le_half_cst one_pos (by norm_num)
    clamp_sIn harg, laplacian_logRad_floor lF_pos cst_pos tF_le_half_cst one_pos (by norm_num)
    clamp_sIn harg⟩
  rw [sIn, pSup, logRad_eq_floor lF_pos cst_pos tF_le_half_cst harg, floor_val]

theorem sIn_of_le {x : E 2} (h : ‖x - 0‖ ^ 2 ≤ 10.83) : sIn x = cst := by
  rw [sIn, logRad_apply, pSup_cap (by positivity) (max_le h (by norm_num))]

/-! ### Smoothness -/

theorem contDiff_qLayer : ContDiff ℝ 2 qLayer :=
  contDiff_logRad_floorCap one_pos (by norm_num) clamp_qLayer

theorem contDiff_sIn : ContDiff ℝ 2 sIn :=
  contDiff_logRad_floorCap one_pos (by norm_num) clamp_sIn

theorem contDiff_sOut : ContDiff ℝ 2 sOut :=
  contDiff_logRad_floorCap one_pos (by norm_num) clamp_sOut

/-- The sum of the hole pieces of `gSub`. -/
def qSum (x : E 2) : ℝ := ∑ k : Fin numHoles, qIn (cen ((k : ℕ) : ℤ)) x

theorem gSub_eq (x : E 2) : gSub x = qSum x + qLayer x + 3 / 2 := rfl

theorem contDiff_qSum : ContDiff ℝ 2 qSum :=
  ContDiff.sum fun _ _ ↦ contDiff_qIn _

theorem contDiff_gSub : ContDiff ℝ 2 gSub :=
  (contDiff_qSum.add contDiff_qLayer).add contDiff_const

theorem contDiff_gSuper : ContDiff ℝ 2 gSuper :=
  (contDiff_sIn.add contDiff_sOut).add contDiff_const

/-! ### Laplacians and gradients of sums -/

theorem laplacian_finset_sum {ι : Type*} (s : Finset ι) {f : ι → E 2 → ℝ} {x : E 2}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) :
    Δ (fun y ↦ ∑ i ∈ s, f i y) x = ∑ i ∈ s, Δ (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi IH =>
    simp only [Finset.sum_insert hi]
    have h1 : ContDiffAt ℝ 2 (f i) x := (hf i).contDiffAt
    have h2 : ContDiffAt ℝ 2 (fun y ↦ ∑ j ∈ s, f j y) x :=
      ContDiffAt.sum fun j _ ↦ (hf j).contDiffAt
    rw [← IH]
    exact h1.laplacian_add h2

theorem laplacian_qSum (x : E 2) :
    Δ qSum x = ∑ k : Fin numHoles, Δ (qIn (cen ((k : ℕ) : ℤ))) x :=
  laplacian_finset_sum _ fun _ ↦ contDiff_qIn _

theorem laplacian_gSub (x : E 2) : Δ gSub x = Δ qSum x + Δ qLayer x := by
  have h1 := contDiff_qSum.contDiffAt (x := x)
  have h2 := contDiff_qLayer.contDiffAt (x := x)
  change Δ ((qSum + qLayer) + (fun _ : E 2 ↦ (3 / 2 : ℝ))) x = _
  have h12 : ContDiffAt ℝ 2 (qSum + qLayer) x := h1.add h2
  rw [h12.laplacian_add contDiffAt_const, h1.laplacian_add h2]
  simp

theorem laplacian_gSuper (x : E 2) : Δ gSuper x = Δ sIn x + Δ sOut x := by
  have h1 := contDiff_sIn.contDiffAt (x := x)
  have h2 := contDiff_sOut.contDiffAt (x := x)
  change Δ ((sIn + sOut) + (fun _ : E 2 ↦ (3 / 200 : ℝ))) x = _
  have h12 : ContDiffAt ℝ 2 (sIn + sOut) x := h1.add h2
  rw [h12.laplacian_add contDiffAt_const, h1.laplacian_add h2]
  simp

theorem hasGradientAt_finset_sum {ι : Type*} (s : Finset ι) {f : ι → E 2 → ℝ} {G : ι → E 2}
    {x : E 2} (hf : ∀ i ∈ s, HasGradientAt (f i) (G i) x) :
    HasGradientAt (fun y ↦ ∑ i ∈ s, f i y) (∑ i ∈ s, G i) x := by
  rw [hasGradientAt_iff_hasFDerivAt, map_sum]
  exact HasFDerivAt.fun_sum fun i hi ↦ hasGradientAt_iff_hasFDerivAt.1 (hf i hi)

theorem hasGradientAt_gSub {x : E 2} {G₁ G₂ : E 2} (h1 : HasGradientAt qSum G₁ x)
    (h2 : HasGradientAt qLayer G₂ x) : HasGradientAt gSub (G₁ + G₂) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at h1 h2 ⊢
  rw [map_add]
  exact (h1.add h2).add_const (3 / 2 : ℝ)

theorem hasGradientAt_gSuper {x : E 2} {G₁ G₂ : E 2} (h1 : HasGradientAt sIn G₁ x)
    (h2 : HasGradientAt sOut G₂ x) : HasGradientAt gSuper (G₁ + G₂) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at h1 h2 ⊢
  rw [map_add]
  exact (h1.add h2).add_const (3 / 200 : ℝ)

/-! ### Geometry of the active regions -/

theorem mem_closure_domain {x : E 2} (hx : x ∈ closure domain) :
    ‖x‖ ≤ outerRad ∧ ∀ k : Fin numHoles, holeRad ≤ ‖x - cen ((k : ℕ) : ℤ)‖ := by
  have hcl : IsClosed {y : E 2 | ‖y‖ ≤ outerRad ∧
      ∀ k : Fin numHoles, holeRad ≤ ‖y - cen ((k : ℕ) : ℤ)‖} := by
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_iInter fun k ↦ isClosed_le continuous_const (by fun_prop))
  refine closure_minimal (fun y hy ↦ ?_) hcl hx
  obtain ⟨h1, h2⟩ := mem_domain_iff.1 hy
  exact ⟨h1.le, fun k ↦ (h2 k).le⟩

theorem sq_le_sq_of_le {s t : ℝ} (hs : 0 ≤ s) (h : s ≤ t) : s ^ 2 ≤ t ^ 2 :=
  pow_le_pow_left₀ hs h 2

/-- In `Ū`, `|x - z_k|² ≥ r² = 1/400` and `|x|² ≤ 16`. -/
theorem normSq_of_mem_closure {x : E 2} (hx : x ∈ closure domain) :
    ‖x - 0‖ ^ 2 ≤ 16 ∧ ∀ k : Fin numHoles, 1 / 400 ≤ ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := mem_closure_domain hx
  refine ⟨?_, fun k ↦ ?_⟩
  · rw [sub_zero]
    have := sq_le_sq_of_le (norm_nonneg _) h1
    unfold outerRad at this; linarith
  · have := sq_le_sq_of_le (by norm_num [holeRad]) (h2 k)
    unfold holeRad at this; linarith

/-- Near a centre (`|x - z_k| ≤ a`), every other centre is at distance `≥ a`. -/
theorem kissRad_le_norm_sub_cen {x : E 2} {j k : Fin numHoles} (h : j ≠ k)
    (hx : ‖x - cen ((k : ℕ) : ℤ)‖ ≤ kissRad) : kissRad ≤ ‖x - cen ((j : ℕ) : ℤ)‖ := by
  have hd := two_kissRad_le_norm_cen_sub_cen (not_dvd_of_ne h)
  have := norm_sub_le_norm_sub_add_norm_sub (cen ((j : ℕ) : ℤ)) x (cen ((k : ℕ) : ℤ))
  have e := norm_sub_rev x (cen ((j : ℕ) : ℤ))
  linarith

/-- Strict version: inside the open disc `B_a(z_k)`, every other centre is at distance `> a`. -/
theorem kissRad_lt_norm_sub_cen {x : E 2} {j k : Fin numHoles} (h : j ≠ k)
    (hx : ‖x - cen ((k : ℕ) : ℤ)‖ < kissRad) : kissRad < ‖x - cen ((j : ℕ) : ℤ)‖ := by
  have hd := two_kissRad_le_norm_cen_sub_cen (not_dvd_of_ne h)
  have := norm_sub_le_norm_sub_add_norm_sub (cen ((j : ℕ) : ℤ)) x (cen ((k : ℕ) : ℤ))
  have e := norm_sub_rev x (cen ((j : ℕ) : ℤ))
  linarith

theorem normSq_lt_iff {v : E 2} {s : ℝ} (hs : 0 ≤ s) : ‖v‖ ^ 2 < s ^ 2 ↔ ‖v‖ < s :=
  pow_lt_pow_iff_left₀ (norm_nonneg _) hs two_ne_zero

theorem normSq_le_iff {v : E 2} {s : ℝ} (hs : 0 ≤ s) : ‖v‖ ^ 2 ≤ s ^ 2 ↔ ‖v‖ ≤ s :=
  pow_le_pow_iff_left₀ (norm_nonneg _) hs two_ne_zero

theorem ringRad_add_kissRad_sq : (ringRad + kissRad) ^ 2 < 10.83 := by
  have := ringRad_bounds; unfold kissRad; nlinarith

/-- **Geometry of a disc `B̄_a(z_k)`**: the other discs are outside, and `|x|² ≤ 10.83`. -/
theorem geom_disc {x : E 2} {k : Fin numHoles} (h : ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 ≤ 1 / 100) :
    (∀ j ≠ k, 1 / 100 ≤ ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2) ∧ ‖x - 0‖ ^ 2 ≤ 10.83 := by
  have hx : ‖x - cen ((k : ℕ) : ℤ)‖ ≤ kissRad := by
    rw [← normSq_le_iff (by norm_num [kissRad])]; unfold kissRad; linarith
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · have := sq_le_sq_of_le (by norm_num [kissRad]) (kissRad_le_norm_sub_cen hj hx)
    unfold kissRad at this; linarith
  · have h1 := norm_le_norm_add_norm_sub' x (cen ((k : ℕ) : ℤ))
    rw [norm_cen] at h1
    rw [sub_zero]
    have := sq_le_sq_of_le (norm_nonneg _) (h1.trans (add_le_add_right hx _))
    linarith [ringRad_add_kissRad_sq, show (kissRad + ringRad) = ringRad + kissRad by ring]

/-- Strict version of `geom_disc` for the open disc. -/
theorem geom_disc_lt {x : E 2} {k : Fin numHoles} (h : ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 < 1 / 100) :
    ∀ j ≠ k, 1 / 100 < ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 := by
  have hx : ‖x - cen ((k : ℕ) : ℤ)‖ < kissRad := by
    rw [← normSq_lt_iff (by norm_num [kissRad])]; unfold kissRad; linarith
  intro j hj
  have := pow_lt_pow_left₀ (kissRad_lt_norm_sub_cen hj hx) (by norm_num [kissRad]) two_ne_zero
  unfold kissRad at this; linarith

/-- Far from the necklace (`|x|² > 10.83`), every disc `B̄_a(z_k)` is far. -/
theorem geom_far {x : E 2} (h : 10.83 < ‖x - 0‖ ^ 2) (k : ℤ) :
    1 / 100 < ‖x - cen k‖ ^ 2 := by
  rw [sub_zero] at h
  have hk0 : (0 : ℝ) < kissRad := by norm_num [kissRad]
  have h1 : ringRad + kissRad < ‖x‖ := by
    refine (pow_lt_pow_iff_left₀ (by linarith [ringRad_pos]) (norm_nonneg _) two_ne_zero).1 ?_
    linarith [ringRad_add_kissRad_sq]
  have h2 := norm_sub_norm_le x (cen k)
  rw [norm_cen] at h2
  have h3 : kissRad < ‖x - cen k‖ := by linarith
  have := pow_lt_pow_left₀ h3 (by norm_num [kissRad]) two_ne_zero
  unfold kissRad at this; linarith

/-! ### Sums with all but one term on the floor -/

theorem sum_eq_of_floor {f : Fin numHoles → ℝ} (k : Fin numHoles) {c : ℝ}
    (h : ∀ j ≠ k, f j = c) : ∑ j, f j = f k + 99 * c := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Finset.sum_congr rfl
    (fun j hj ↦ h j (Finset.ne_of_mem_erase hj)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  simp [numHoles]

theorem sum_eq_of_floor_all {f : Fin numHoles → ℝ} {c : ℝ} (h : ∀ j, f j = c) :
    ∑ j, f j = 100 * c := by
  rw [Finset.sum_congr rfl (fun j _ ↦ h j), Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [numHoles]

theorem sum_eq_single_of_zero {G : Fin numHoles → E 2} (k : Fin numHoles)
    (h : ∀ j ≠ k, G j = 0) : ∑ j, G j = G k :=
  Finset.sum_eq_single k (fun j _ hj ↦ h j hj) (fun hk ↦ absurd (Finset.mem_univ k) hk)

/-- On a disc `B_a(z_k)` (inside `Ū`), `qSum = qIn(z_k) - 99·3/200`, with gradient `∇qIn(z_k)`. -/
theorem qSum_of_disc {x : E 2} {k : Fin numHoles}
    (h : ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 ≤ 1 / 100) :
    qSum x = qIn (cen ((k : ℕ) : ℤ)) x + 99 * (-3 / 200) ∧
      HasGradientAt qSum (∇ (qIn (cen ((k : ℕ) : ℤ))) x) x := by
  have hj := (geom_disc h).1
  refine ⟨sum_eq_of_floor k fun j hjk ↦ (qIn_floor (hj j hjk)).1, ?_⟩
  have hg := hasGradientAt_finset_sum Finset.univ
    (f := fun j : Fin numHoles ↦ qIn (cen ((j : ℕ) : ℤ)))
    (G := fun j : Fin numHoles ↦ if j = k then ∇ (qIn (cen ((k : ℕ) : ℤ))) x else 0) (x := x)
    (fun j _ ↦ by
      by_cases hjk : j = k
      · subst hjk; simp only [ite_true]
        exact ((contDiff_qIn _).differentiable (by norm_num) x).hasGradientAt
      · simp only [hjk, ite_false]; exact (qIn_floor (hj j hjk)).2.1)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hg
  exact hg

/-- Off the discs, `qSum = 100·(-3/200)`, with zero gradient. -/
theorem qSum_of_far {x : E 2} (h : ∀ j : Fin numHoles, 1 / 100 ≤ ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2) :
    qSum x = 100 * (-3 / 200) ∧ HasGradientAt qSum 0 x := by
  refine ⟨sum_eq_of_floor_all fun j ↦ (qIn_floor (h j)).1, ?_⟩
  have hg := hasGradientAt_finset_sum Finset.univ
    (f := fun j : Fin numHoles ↦ qIn (cen ((j : ℕ) : ℤ))) (G := fun _ : Fin numHoles ↦ 0) (x := x)
    (fun j _ ↦ (qIn_floor (h j)).2.1)
  simp only [Finset.sum_const_zero] at hg
  exact hg

end PerronVariational.Necklace

end
