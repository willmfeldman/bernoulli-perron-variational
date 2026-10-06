/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.TwoDisc.Pieces
public import PerronVariational.Examples.TwoDisc.Domain
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The data of the two-disc model example

The boundary data of the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`). Write `c = log 2 / 10`, `ρ = e^{-1/10}`, `ε = ρ/10`, and `m = -3/200`
for the common floor value of the pieces.

* `gSub = qIn(p) + qIn(-p) + qOut - 2m`, where `qIn(±p)` is a floor-and-cap profile of
  `c (1 - log (400 |x ∓ p|²))` (equal to `c` on the inner circles, slope `2c/|x ∓ p| > 1` on its
  zero level) and `qOut` is a floor profile of `ρ (log |x|² + 1/10)` (equal to `ε` on `∂B₁`).
  It is a smooth strict subsolution (`isStrictSub_gSub`), since its pieces are harmonic and
  convex profiles of harmonic functions on `Ū`.
* `gSuper = rIn + rOut - m`, where `rIn` is a profile of `(9/40) log (1/(4|x|²))`, capped flat at
  `c` for `|x|² ≤ 1/10` (so it equals `c` on both inner circles), and `rOut` is a floor profile of
  `ε (2 log |x|² + 1)`. It is a smooth strict supersolution (`isStrictSuper_gSuper`): where it is
  above `-a₀` it is a concave profile of a harmonic function, with slope `≤ 0.91` at its zero level.
* `gSub = gSuper` on `∂U` (`gSub_eq_gSuper_of_mem_frontier`), and `gSub > 0` there.

The active regions `{|x ∓ p|² < 1/100}`, `{|x|² > 1/2}` (for `gSub`) and `{|x|² < 3/10}`,
`{|x|² > 1/2}` (for `gSuper`) are disjoint; outside its active region each piece sits on its floor.
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

/-! ### Constants -/

/-- `c = a log 2` with `a = 1/10`: the boundary value on the inner circles. -/
def cst : ℝ := Real.log 2 / 10

/-- `ρ = e^{-1/10}`: the free boundary radius of the outer layer. -/
def rho : ℝ := Real.exp (-(1 / 10))

/-- `ε = ρ log (1/ρ) = ρ/10`: the boundary value on the unit circle. -/
def eps : ℝ := rho / 10

/-- The floor threshold `tf = -1/100`. -/
def tF : ℝ := -1 / 100

/-- The floor width `lf = 1/100`. -/
def lF : ℝ := 1 / 100

/-- The strictness constant `a₀ = 1/1000`. -/
def aZero : ℝ := 1 / 1000

theorem log_two_bounds : 0.6931 < Real.log 2 ∧ Real.log 2 < 0.6932 :=
  ⟨lt_trans (by norm_num) Real.log_two_gt_d9, lt_trans Real.log_two_lt_d9 (by norm_num)⟩

theorem cst_bounds : 0.06931 < cst ∧ cst < 0.06932 := by
  obtain ⟨h1, h2⟩ := log_two_bounds
  constructor <;> (unfold cst; linarith)

theorem cst_pos : 0 < cst := by linarith [cst_bounds.1]

theorem rho_bounds : 9 / 10 ≤ rho ∧ rho < 1 := by
  refine ⟨?_, Real.exp_lt_one_iff.2 (by norm_num)⟩
  have := Real.add_one_le_exp (-(1 / 10))
  unfold rho; linarith

theorem eps_bounds : 9 / 100 ≤ eps ∧ eps < 1 / 10 := by
  obtain ⟨h1, h2⟩ := rho_bounds
  constructor <;> (unfold eps; linarith)

theorem eps_pos : 0 < eps := by linarith [eps_bounds.1]

theorem log_rho : Real.log rho = -(1 / 10) := Real.log_exp _

/-! ### Profiles and pieces -/

/-- The profile of the inner pieces of `gSub`: floor at `-1/100`, cap at `c`. -/
def pIn : ℝ → ℝ := floorCap tF lF cst cst

/-- The profile of the outer pieces: floor at `-1/100`, cap at `1` (inactive on `B̄₁`). -/
def pOut : ℝ → ℝ := floorCap tF lF 1 1

/-- The profile of the inner piece of `gSuper`: floor at `-1/100`, capped flat at `c`. -/
def pSup : ℝ → ℝ := floorCap tF lF (cst / 2) cst

/-- The constant of the inner pieces of `gSub`: `k = c + c log (1/400)`. -/
def kIn : ℝ := cst + cst * Real.log (1 / 400)

/-- The inner piece of `gSub` around `z`: a profile of `c (1 - log (400 |x - z|²))`. -/
def qIn (z : E 2) : E 2 → ℝ := logRad pIn z (-cst) kIn (1 / 3200)

/-- The outer piece of `gSub`: a profile of `ρ (log |x|² + 1/10)`. -/
def qOut : E 2 → ℝ := logRad pOut 0 rho eps (1 / 4)

/-- The strict subsolution `gSub = qIn(p) + qIn(-p) + qOut + 3/100`. -/
def gSub (x : E 2) : ℝ := qIn hole x + qIn (-hole) x + qOut x + 3 / 100

/-- The inner piece of `gSuper`: a profile of `(9/40) log (1/(4|x|²))`. -/
def rIn : E 2 → ℝ := logRad pSup 0 (-(9 / 40)) (-(9 / 20) * Real.log 2) (1 / 100)

/-- The outer piece of `gSuper`: a profile of `ε (2 log |x|² + 1)`. -/
def rOut : E 2 → ℝ := logRad pOut 0 (2 * eps) eps (1 / 4)

/-- The strict supersolution `gSuper = rIn + rOut + 3/200`. -/
def gSuper (x : E 2) : ℝ := rIn x + rOut x + 3 / 200

/-! ### Basic facts about the profiles -/

theorem lF_pos : (0 : ℝ) < lF := by norm_num [lF]

theorem tF_le_cst : tF ≤ cst := by unfold tF; linarith [cst_pos]

theorem tF_le_half_cst : tF ≤ cst / 2 := by unfold tF; linarith [cst_pos]

theorem tF_le_one : tF ≤ 1 := by norm_num [tF]

theorem floor_val : tF - lF / 2 = -3 / 200 := by norm_num [tF, lF]

theorem floor_thr : tF - lF = -1 / 50 := by norm_num [tF, lF]

theorem log_quarter_le {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 1 / 32) : Real.log τ ≤ -(5 * Real.log 2) := by
  calc Real.log τ ≤ Real.log (1 / 32) := Real.log_le_log hτ h
    _ = -(5 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; push_cast; ring

/-! ### Clamping -/

theorem clamp_qIn : ClampConst pIn (-cst) kIn (1 / 3200) (1 / 1600) := by
  have hc := cst_pos
  have key : ∀ τ ∈ Icc (1 / 3200 : ℝ) (1 / 1600),
      pIn (-cst * Real.log τ + kIn) = cst + cst / 2 := by
    intro τ hτ
    refine floorCap_of_cap_le lF_pos hc tF_le_cst ?_
    have hl : Real.log τ ≤ Real.log (1 / 400) - 1 := by
      calc Real.log τ ≤ Real.log (1 / 1600) := Real.log_le_log (by linarith [hτ.1]) hτ.2
        _ = Real.log (1 / 400) - 2 * Real.log 2 := by
          rw [show (1 / 1600 : ℝ) = (1 / 400) / 2 ^ 2 by norm_num,
            Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
        _ ≤ _ := by linarith [log_two_bounds.1]
    unfold kIn; nlinarith
  intro τ hτ
  rw [key τ hτ, key _ ⟨le_rfl, by norm_num⟩]

theorem pOut_floor_of_le {α k τ : ℝ} (h : α * Real.log τ + k ≤ -1 / 50) :
    pOut (α * Real.log τ + k) = -3 / 200 := by
  rw [pOut, floorCap_of_le_floor lF_pos one_pos tF_le_one (by rw [floor_thr]; exact h), floor_val]

theorem qOut_arg_floor {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 1 / 2) : rho * Real.log τ + eps ≤ -1 / 50 := by
  have hl : Real.log τ ≤ -Real.log 2 := by
    calc Real.log τ ≤ Real.log (1 / 2) := Real.log_le_log hτ h
      _ = _ := by rw [one_div, Real.log_inv]
  obtain ⟨h1, h2⟩ := rho_bounds
  have := log_two_bounds.1
  unfold eps
  nlinarith

theorem clamp_qOut : ClampConst pOut rho eps (1 / 4) (1 / 2) := by
  intro τ hτ
  rw [pOut_floor_of_le (qOut_arg_floor (by linarith [hτ.1]) hτ.2),
    pOut_floor_of_le (qOut_arg_floor (by norm_num) (by norm_num))]

theorem rOut_arg_floor {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 1 / 2) :
    2 * eps * Real.log τ + eps ≤ -1 / 50 := by
  have hl : Real.log τ ≤ -Real.log 2 := by
    calc Real.log τ ≤ Real.log (1 / 2) := Real.log_le_log hτ h
      _ = _ := by rw [one_div, Real.log_inv]
  obtain ⟨h1, h2⟩ := eps_bounds
  have := log_two_bounds.1
  nlinarith

theorem clamp_rOut : ClampConst pOut (2 * eps) eps (1 / 4) (1 / 2) := by
  intro τ hτ
  rw [pOut_floor_of_le (rOut_arg_floor (by linarith [hτ.1]) hτ.2),
    pOut_floor_of_le (rOut_arg_floor (by norm_num) (by norm_num))]

/-- For `|x|² ≤ 1/32`, the argument of `rIn` is past the cap. -/
theorem rIn_arg_cap {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 1 / 32) :
    cst / 2 + cst ≤ -(9 / 40) * Real.log τ + -(9 / 20) * Real.log 2 := by
  have := log_quarter_le hτ h
  have := log_two_bounds.1
  unfold cst; nlinarith

theorem pSup_cap {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 1 / 32) :
    pSup (-(9 / 40) * Real.log τ + -(9 / 20) * Real.log 2) = cst := by
  rw [pSup, floorCap_of_cap_le lF_pos cst_pos tF_le_half_cst (rIn_arg_cap hτ h)]; ring

theorem clamp_rIn : ClampConst pSup (-(9 / 40)) (-(9 / 20) * Real.log 2) (1 / 100) (1 / 50) := by
  intro τ hτ
  rw [pSup_cap (by linarith [hτ.1]) (by linarith [hτ.2]), pSup_cap (by norm_num) (by norm_num)]

/-! ### Floors of the pieces -/

theorem qIn_arg_floor {τ : ℝ} (h : 1 / 100 ≤ τ) : -cst * Real.log τ + kIn ≤ -1 / 50 := by
  have hl : Real.log (1 / 100) ≤ Real.log τ := Real.log_le_log (by norm_num) h
  have h4 : Real.log (1 / 400) = Real.log (1 / 100) - 2 * Real.log 2 := by
    rw [show (1 / 400 : ℝ) = (1 / 100) / 2 ^ 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  obtain ⟨h1, h2⟩ := log_two_bounds
  have hc := cst_bounds
  unfold kIn
  rw [h4]
  have : cst * (1 - 2 * Real.log 2) ≤ -1 / 50 := by unfold cst; nlinarith
  nlinarith [cst_pos]

theorem rIn_arg_floor {τ : ℝ} (h : 3 / 10 ≤ τ) :
    -(9 / 40) * Real.log τ + -(9 / 20) * Real.log 2 ≤ -1 / 50 := by
  have h4 : Real.log τ + 2 * Real.log 2 = Real.log (4 * τ) := by
    rw [Real.log_mul (by norm_num) (by linarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]; push_cast; ring
  have h6 : 1 / 6 ≤ Real.log (4 * τ) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 4 * τ) (by linarith)
    have : (4 * τ)⁻¹ ≤ 5 / 6 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  linarith

/-! ### The distance functions -/

/-- `τ₊ = |x - p|²`, `τ₋ = |x + p|²`, `τ₀ = |x|²`. -/
theorem sq_sub_neg_hole (x : E 2) : ‖x - -hole‖ ^ 2 = ‖x + hole‖ ^ 2 := by rw [sub_neg_eq_add]

theorem geom_plus {x : E 2} (h : ‖x - hole‖ ^ 2 < 1 / 100) :
    1 / 100 ≤ ‖x + hole‖ ^ 2 ∧ ‖x - 0‖ ^ 2 ≤ 1 / 2 := by
  rw [norm_sub_hole_sq] at h
  rw [norm_add_hole_sq, sub_zero, norm_sq_eq]
  constructor <;> nlinarith [sq_nonneg (x 0 - 1 / 10), sq_nonneg (x 1)]

theorem geom_minus {x : E 2} (h : ‖x + hole‖ ^ 2 < 1 / 100) :
    1 / 100 ≤ ‖x - hole‖ ^ 2 ∧ ‖x - 0‖ ^ 2 ≤ 1 / 2 := by
  rw [norm_add_hole_sq] at h
  rw [norm_sub_hole_sq, sub_zero, norm_sq_eq]
  constructor <;> nlinarith [sq_nonneg (x 0 + 1 / 10), sq_nonneg (x 1)]

theorem geom_out {x : E 2} (h : 1 / 2 < ‖x - 0‖ ^ 2) :
    1 / 100 ≤ ‖x - hole‖ ^ 2 ∧ 1 / 100 ≤ ‖x + hole‖ ^ 2 := by
  rw [sub_zero, norm_sq_eq] at h
  rw [norm_sub_hole_sq, norm_add_hole_sq]
  constructor <;> nlinarith [sq_nonneg (x 0 - 1 / 10), sq_nonneg (x 0 + 1 / 10), sq_nonneg (x 1)]

theorem mem_closure_domain {x : E 2} (hx : x ∈ closure domain) :
    ‖x - 0‖ ^ 2 ≤ 1 ∧ 1 / 400 ≤ ‖x - hole‖ ^ 2 ∧ 1 / 400 ≤ ‖x + hole‖ ^ 2 := by
  have hcl : IsClosed {y : E 2 | ‖y - 0‖ ^ 2 ≤ 1 ∧ 1 / 400 ≤ ‖y - hole‖ ^ 2 ∧
      1 / 400 ≤ ‖y + hole‖ ^ 2} := by
    simp only [Set.ofPred_and]
    refine (isClosed_le ?_ continuous_const).inter
      ((isClosed_le continuous_const ?_).inter (isClosed_le continuous_const ?_)) <;> fun_prop
  refine closure_minimal (fun y hy ↦ ?_) hcl hx
  rw [mem_domain_iff] at hy
  rw [Set.mem_ofPred_eq, sub_zero, norm_sub_hole_sq, norm_add_hole_sq, norm_sq_eq]
  exact ⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩

/-! ### Values of the pieces on their floors -/

theorem qIn_floor {z : E 2} {x : E 2} (h : 1 / 100 ≤ ‖x - z‖ ^ 2) :
    qIn z x = -3 / 200 ∧ HasGradientAt (qIn z) 0 x ∧ Δ (qIn z) x = 0 := by
  have harg : -cst * Real.log (max (‖x - z‖ ^ 2) (1 / 3200)) + kIn ≤ tF - lF := by
    rw [max_eq_left (by linarith), floor_thr]; exact qIn_arg_floor h
  refine ⟨?_, hasGradientAt_logRad_floor lF_pos cst_pos tF_le_cst (by norm_num) (by norm_num)
    clamp_qIn harg, laplacian_logRad_floor lF_pos cst_pos tF_le_cst (by norm_num) (by norm_num)
    clamp_qIn harg⟩
  rw [qIn, pIn, logRad_eq_floor lF_pos cst_pos tF_le_cst harg, floor_val]

theorem qOut_floor {x : E 2} (h : ‖x - 0‖ ^ 2 ≤ 1 / 2) :
    qOut x = -3 / 200 ∧ HasGradientAt qOut 0 x ∧ Δ qOut x = 0 := by
  have harg : rho * Real.log (max (‖x - 0‖ ^ 2) (1 / 4)) + eps ≤ tF - lF := by
    rw [floor_thr]; exact qOut_arg_floor (by positivity) (max_le h (by norm_num))
  refine ⟨?_, hasGradientAt_logRad_floor lF_pos one_pos tF_le_one (by norm_num) (by norm_num)
    clamp_qOut harg, laplacian_logRad_floor lF_pos one_pos tF_le_one (by norm_num) (by norm_num)
    clamp_qOut harg⟩
  rw [qOut, pOut, logRad_eq_floor lF_pos one_pos tF_le_one harg, floor_val]

theorem rOut_floor {x : E 2} (h : ‖x - 0‖ ^ 2 ≤ 1 / 2) :
    rOut x = -3 / 200 ∧ HasGradientAt rOut 0 x ∧ Δ rOut x = 0 := by
  have harg : 2 * eps * Real.log (max (‖x - 0‖ ^ 2) (1 / 4)) + eps ≤ tF - lF := by
    rw [floor_thr]; exact rOut_arg_floor (by positivity) (max_le h (by norm_num))
  refine ⟨?_, hasGradientAt_logRad_floor lF_pos one_pos tF_le_one (by norm_num) (by norm_num)
    clamp_rOut harg, laplacian_logRad_floor lF_pos one_pos tF_le_one (by norm_num) (by norm_num)
    clamp_rOut harg⟩
  rw [rOut, pOut, logRad_eq_floor lF_pos one_pos tF_le_one harg, floor_val]

theorem rIn_floor {x : E 2} (h : 3 / 10 ≤ ‖x - 0‖ ^ 2) :
    rIn x = -3 / 200 ∧ HasGradientAt rIn 0 x ∧ Δ rIn x = 0 := by
  have harg : -(9 / 40) * Real.log (max (‖x - 0‖ ^ 2) (1 / 100)) + -(9 / 20) * Real.log 2 ≤
      tF - lF := by
    rw [max_eq_left (by linarith), floor_thr]; exact rIn_arg_floor h
  refine ⟨?_, hasGradientAt_logRad_floor lF_pos cst_pos tF_le_half_cst (by norm_num)
    (by norm_num) clamp_rIn harg, laplacian_logRad_floor lF_pos cst_pos tF_le_half_cst
    (by norm_num) (by norm_num) clamp_rIn harg⟩
  rw [rIn, pSup, logRad_eq_floor lF_pos cst_pos tF_le_half_cst harg, floor_val]

/-! ### Smoothness -/

theorem contDiff_qIn (z : E 2) : ContDiff ℝ 2 (qIn z) :=
  contDiff_logRad_floorCap (by norm_num) (by norm_num) clamp_qIn

theorem contDiff_qOut : ContDiff ℝ 2 qOut :=
  contDiff_logRad_floorCap (by norm_num) (by norm_num) clamp_qOut

theorem contDiff_rIn : ContDiff ℝ 2 rIn :=
  contDiff_logRad_floorCap (by norm_num) (by norm_num) clamp_rIn

theorem contDiff_rOut : ContDiff ℝ 2 rOut :=
  contDiff_logRad_floorCap (by norm_num) (by norm_num) clamp_rOut

theorem contDiff_gSub : ContDiff ℝ 2 gSub := by
  unfold gSub
  exact (((contDiff_qIn _).add (contDiff_qIn _)).add contDiff_qOut).add contDiff_const

theorem contDiff_gSuper : ContDiff ℝ 2 gSuper := by
  unfold gSuper
  exact (contDiff_rIn.add contDiff_rOut).add contDiff_const

theorem laplacian_gSub (x : E 2) :
    Δ gSub x = Δ (qIn hole) x + Δ (qIn (-hole)) x + Δ qOut x := by
  have h1 := (contDiff_qIn hole).contDiffAt (x := x)
  have h2 := (contDiff_qIn (-hole)).contDiffAt (x := x)
  have h3 := contDiff_qOut.contDiffAt (x := x)
  change Δ ((qIn hole + qIn (-hole) + qOut) + (fun _ : E 2 ↦ (3 / 100 : ℝ))) x = _
  have h12 : ContDiffAt ℝ 2 (qIn hole + qIn (-hole)) x := h1.add h2
  have h123 : ContDiffAt ℝ 2 (qIn hole + qIn (-hole) + qOut) x := h12.add h3
  rw [h123.laplacian_add contDiffAt_const, h12.laplacian_add h3, h1.laplacian_add h2]
  simp

theorem laplacian_gSuper (x : E 2) : Δ gSuper x = Δ rIn x + Δ rOut x := by
  have h1 := contDiff_rIn.contDiffAt (x := x)
  have h2 := contDiff_rOut.contDiffAt (x := x)
  change Δ ((rIn + rOut) + (fun _ : E 2 ↦ (3 / 200 : ℝ))) x = _
  have h12 : ContDiffAt ℝ 2 (rIn + rOut) x := h1.add h2
  rw [h12.laplacian_add contDiffAt_const, h1.laplacian_add h2]
  simp

theorem hasGradientAt_gSub {x : E 2} {G₁ G₂ G₃ : E 2} (h1 : HasGradientAt (qIn hole) G₁ x)
    (h2 : HasGradientAt (qIn (-hole)) G₂ x) (h3 : HasGradientAt qOut G₃ x) :
    HasGradientAt gSub (G₁ + G₂ + G₃) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at h1 h2 h3 ⊢
  rw [map_add, map_add]
  exact ((h1.add h2).add h3).add_const (3 / 100 : ℝ)

theorem hasGradientAt_gSuper {x : E 2} {G₁ G₂ : E 2} (h1 : HasGradientAt rIn G₁ x)
    (h2 : HasGradientAt rOut G₂ x) : HasGradientAt gSuper (G₁ + G₂) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at h1 h2 ⊢
  rw [map_add]
  exact (h1.add h2).add_const (3 / 200 : ℝ)

end PerronVariational.TwoDisc

end
