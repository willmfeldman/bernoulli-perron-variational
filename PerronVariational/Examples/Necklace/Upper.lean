/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.Strict
public import PerronVariational.Examples.TwoDisc.Upper

/-!
# The explicit supersolution of the necklace example

For the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M. Feldman, K.
Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`), the function
`v = Σ_k (a log (a/|x - z_k|))₊ + (ρ_o log (|x|/ρ_o))₊`, `a = 1/10`,
is a viscosity supersolution in `U` with `Q ≡ 1` lying above `gSub₊`
(`vSup_mem_perronSuperClass`), hence `u_min ≤ v`; and `v ≤ gSuper₊` on `Ū` (`vSup_le_gSuper`).
The positivity sets are the discs `B_a(z_k)`, neighbouring discs touching at the kissing points,
and the outer layer `{ρ_o < |x| < 4}`.

At a free boundary point `x` the test function `φ` touches `v` from below, and we pick one disc
`k` with `x ∈ ∂B_a(z_k)` such that the ray `x + t∇φ(x)`, `t > 0`, stays outside every other disc
(`exists_good_index`: at a kissing point the two discs are on opposite sides). Along that ray
`v = (W_k)₊` with `|∇W_k(x)| = 1`, so `|∇φ(x)| ≤ 1` (`TwoDisc.norm_gradient_le_of_ray`).
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational.Necklace

open TwoDisc (floorCap logRad logRad_apply pOut pSup qIn tF lF cst cst_pos cst_bounds
  lF_pos tF_le_one tF_le_half_cst floor_val floorCap_of_le_floor floorCap_of_mem_Icc
  floorCap_le_floor ClampConst norm_gradient_logRad_mid laplacian_logRad_mid qIn_floor
  contDiff_logRad_floorCap pH pH_floor wIn contDiff_wIn wIn_val wIn_pos wIn_eq_zero
  max_wIn_eq_zero laplacian_wIn norm_gradient_wIn max_floorCap_eq aw_le_cst qIn_le_wIn
  norm_eq_of_sq tendsto_ray isOpen_lt_normsq isOpen_gt_normsq fb_step
  laplacian_le_of_touch norm_gradient_le_of_ray gradient_eq_zero_of_isLocalMax ramp_nonneg
  ramp_of_nonpos log_two_bounds)

/-! ### The outer layer -/

/-- The outer layer `h = ρ_o log (|x|/ρ_o) = (ρ_o/2) log (|x|²/16) + ε`. -/
def hLayer : E 2 → ℝ := logRad pH 0 (layerRad / 2) (epsOut - layerRad / 2 * Real.log 16) 1

/-- The explicit supersolution `v = Σ_k (W_k)₊ + h₊`. -/
def vSup (x : E 2) : ℝ :=
  ∑ k : Fin numHoles, max (wIn (cen ((k : ℕ) : ℤ)) x) 0 + max (hLayer x) 0

/-- The sum of the disc pieces of `v`. -/
def wSum (x : E 2) : ℝ := ∑ k : Fin numHoles, max (wIn (cen ((k : ℕ) : ℤ)) x) 0

theorem vSup_eq (x : E 2) : vSup x = wSum x + max (hLayer x) 0 := rfl

theorem log_layerRad_sq : Real.log (layerRad ^ 2) = Real.log 16 - 1 / 50 := by
  rw [Real.log_pow, log_layerRad, log_sixteen, log_four]; push_cast; ring

theorem layerRad_sq_bounds : 15.68 ≤ layerRad ^ 2 ∧ layerRad ^ 2 < 16 := by
  obtain ⟨h1, h2⟩ := layerRad_bounds
  constructor <;> nlinarith

theorem ah_eq (τ : ℝ) : layerRad / 2 * Real.log τ + (epsOut - layerRad / 2 * Real.log 16) =
    layerRad / 2 * (Real.log τ - Real.log (layerRad ^ 2)) := by
  rw [log_layerRad_sq]; unfold epsOut; ring

theorem ah_floor {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ 2) :
    layerRad / 2 * Real.log τ + (epsOut - layerRad / 2 * Real.log 16) ≤ -1 / 5 := by
  rw [ah_eq, log_layerRad_sq, log_sixteen]
  have : Real.log τ ≤ Real.log 2 := Real.log_le_log hτ h
  have := log_two_bounds.1
  have := layerRad_bounds.1
  nlinarith

theorem clamp_hLayer : ClampConst pH (layerRad / 2) (epsOut - layerRad / 2 * Real.log 16) 1 2 := by
  intro τ hτ
  rw [pH_floor (ah_floor (by linarith [hτ.1]) hτ.2), pH_floor (ah_floor one_pos (by norm_num))]

theorem contDiff_hLayer : ContDiff ℝ 2 hLayer :=
  contDiff_logRad_floorCap one_pos (by norm_num) clamp_hLayer

/-- Off the outer layer, `h₊ = 0`. -/
theorem max_hLayer_eq_zero {x : E 2} (hτ : ‖x - 0‖ ^ 2 ≤ layerRad ^ 2) : max (hLayer x) 0 = 0 := by
  have hr := layerRad_bounds
  rcases le_or_gt (‖x - 0‖ ^ 2) 1 with h | h
  · rw [hLayer, logRad_apply, max_eq_right h, pH_floor (ah_floor one_pos (by norm_num))]
    norm_num
  · rw [hLayer, logRad_apply, max_eq_left h.le]
    unfold pH
    have hl : Real.log (‖x - 0‖ ^ 2) ≤ Real.log (layerRad ^ 2) := Real.log_le_log (by linarith) hτ
    rw [max_floorCap_eq one_pos (by norm_num)]
    · refine max_eq_right ?_
      rw [ah_eq]; nlinarith
    · rw [ah_eq]; nlinarith

theorem ah_mid {x : E 2} (hτ : layerRad ^ 2 ≤ ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 16) :
    layerRad / 2 * Real.log (‖x - 0‖ ^ 2) + (epsOut - layerRad / 2 * Real.log 16) ∈
      Icc (-1 / 10) 1 := by
  have hr := layerRad_bounds
  have hr0 : 0 < layerRad ^ 2 := pow_pos (by linarith) 2
  have h0 : 0 < ‖x - 0‖ ^ 2 := lt_of_lt_of_le hr0 hτ
  have h1 : Real.log (layerRad ^ 2) ≤ Real.log (‖x - 0‖ ^ 2) := Real.log_le_log hr0 hτ
  have h2 : Real.log (‖x - 0‖ ^ 2) ≤ Real.log 16 := Real.log_le_log h0 hτ1
  have := log_layerRad_sq
  rw [ah_eq]
  constructor <;> nlinarith

theorem hLayer_eq {x : E 2} (hτ : layerRad ^ 2 ≤ ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 16) :
    hLayer x = layerRad / 2 * (Real.log (‖x - 0‖ ^ 2) - Real.log (layerRad ^ 2)) := by
  have hq : 1 ≤ ‖x - 0‖ ^ 2 := le_trans (by linarith [layerRad_sq_bounds.1]) hτ
  rw [hLayer, logRad_apply, max_eq_left hq, pH,
    floorCap_of_mem_Icc (by norm_num) one_pos (ah_mid hτ hτ1), ah_eq]

theorem hLayer_pos {x : E 2} (hτ : layerRad ^ 2 < ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 16) :
    0 < hLayer x := by
  rw [hLayer_eq hτ.le hτ1]
  have := Real.log_lt_log (pow_pos (by linarith [layerRad_bounds.1]) 2) hτ
  have := layerRad_bounds.1
  nlinarith

theorem hLayer_eq_zero {x : E 2} (hτ : ‖x - 0‖ ^ 2 = layerRad ^ 2) : hLayer x = 0 := by
  rw [hLayer_eq hτ.ge (by rw [hτ]; exact layerRad_sq_bounds.2.le), hτ]; ring

theorem laplacian_hLayer {x : E 2} (hτ : layerRad ^ 2 ≤ ‖x - 0‖ ^ 2) (hτ1 : ‖x - 0‖ ^ 2 ≤ 16) :
    Δ hLayer x = 0 :=
  laplacian_logRad_mid (by norm_num) one_pos one_pos (by norm_num) clamp_hLayer
    (lt_of_lt_of_le (by linarith [layerRad_sq_bounds.1]) hτ) (ah_mid hτ hτ1)

theorem norm_gradient_hLayer {x : E 2} (hτ : ‖x - 0‖ ^ 2 = layerRad ^ 2) :
    ‖∇ hLayer x‖ = 1 := by
  have hr := layerRad_bounds
  rw [hLayer, pH, norm_gradient_logRad_mid (by norm_num) one_pos one_pos (by norm_num)
    clamp_hLayer (by rw [hτ]; nlinarith) (ah_mid hτ.ge (by rw [hτ]; exact layerRad_sq_bounds.2.le)),
    norm_eq_of_sq (s := layerRad) (by linarith) hτ, abs_of_pos (by linarith)]
  field_simp
  exact div_self (by linarith)

/-! ### Basic properties of `v` -/

theorem continuous_wSum : Continuous wSum :=
  continuous_finsetSum _ fun _ _ ↦ ((contDiff_wIn _).continuous).max continuous_const

theorem continuous_vSup : Continuous vSup :=
  continuous_wSum.add (contDiff_hLayer.continuous.max continuous_const)

theorem wSum_nonneg (x : E 2) : 0 ≤ wSum x :=
  Finset.sum_nonneg fun _ _ ↦ le_max_right _ _

theorem vSup_nonneg (x : E 2) : 0 ≤ vSup x :=
  add_nonneg (wSum_nonneg x) (le_max_right _ _)

/-- If only the `k`-th disc piece can be positive at `x`, then `wSum x = (W_k)₊(x)`. -/
theorem wSum_eq_single {x : E 2} (k : Fin numHoles)
    (h : ∀ j ≠ k, 1 / 100 ≤ ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2) :
    wSum x = max (wIn (cen ((k : ℕ) : ℤ)) x) 0 :=
  Finset.sum_eq_single k (fun j _ hj ↦ max_wIn_eq_zero (h j hj))
    (fun hk ↦ absurd (Finset.mem_univ k) hk)

theorem wSum_eq_zero {x : E 2} (h : ∀ j : Fin numHoles, 1 / 100 ≤ ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2) :
    wSum x = 0 :=
  Finset.sum_eq_zero fun j _ ↦ max_wIn_eq_zero (h j)

theorem normSq_of_mem_domain {x : E 2} (hx : x ∈ domain) :
    ‖x - 0‖ ^ 2 < 16 ∧ ∀ k : Fin numHoles, 1 / 400 < ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := mem_domain_iff.1 hx
  refine ⟨?_, fun k ↦ ?_⟩
  · rw [sub_zero]
    have := pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
    unfold outerRad at this; linarith
  · have := pow_lt_pow_left₀ (h2 k) (by norm_num [holeRad]) two_ne_zero
    unfold holeRad at this; linarith

theorem ten_lt_layerRad_sq : 10.83 < layerRad ^ 2 := by linarith [layerRad_sq_bounds.1]

/-! ### Free boundary points on the circles `∂B_a(z_k)` -/

/-- Two circles `∂B_a(z_j)`, `∂B_a(z_k)` (`j ≠ k`) can only meet at a kissing point, where
`x - z_j = -(x - z_k)`. -/
theorem sub_cen_eq_neg_of_kiss {x : E 2} {j k : Fin numHoles} (hjk : j ≠ k)
    (hj : ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 = 1 / 100) (hk : ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 = 1 / 100) :
    x - cen ((j : ℕ) : ℤ) = -(x - cen ((k : ℕ) : ℤ)) := by
  set u := x - cen ((k : ℕ) : ℤ)
  set w := x - cen ((j : ℕ) : ℤ)
  have hd := two_kissRad_le_norm_cen_sub_cen (not_dvd_of_ne hjk)
  have e : cen ((j : ℕ) : ℤ) - cen ((k : ℕ) : ℤ) = u - w := by simp only [u, w]; abel
  rw [e] at hd
  have hd2 : (2 * kissRad) ^ 2 ≤ ‖u - w‖ ^ 2 := pow_le_pow_left₀ (by norm_num [kissRad]) hd 2
  have hp : ‖u + w‖ ^ 2 + ‖u - w‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
    have := parallelogram_law_with_norm ℝ u w
    rw [sq, sq, sq, sq]; linarith
  have h0 : ‖w + u‖ ^ 2 = 0 := by
    rw [add_comm]; unfold kissRad at hd2; nlinarith [sq_nonneg ‖u + w‖]
  have := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
  exact eq_neg_of_add_eq_zero_left this

/-- At most two circles `∂B_a(z_k)` pass through a point. -/
theorem eq_of_three {x : E 2} {i j k : Fin numHoles} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : ‖x - cen ((i : ℕ) : ℤ)‖ ^ 2 = 1 / 100) (hj : ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 = 1 / 100)
    (hk : ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 = 1 / 100) : False := by
  have h1 := sub_cen_eq_neg_of_kiss hik hi hk
  have h2 := sub_cen_eq_neg_of_kiss hjk hj hk
  have : cen ((i : ℕ) : ℤ) = cen ((j : ℕ) : ℤ) := by
    have := h1.trans h2.symm
    simpa using this
  have hd := two_kissRad_le_norm_cen_sub_cen (not_dvd_of_ne hij)
  rw [this, sub_self, norm_zero] at hd
  norm_num [kissRad] at hd

/-- At a point on some circle `∂B_a(z_{k₀})`, for a direction `ξ` there is a circle `∂B_a(z_k)`
through the point such that every other circle through it has `⟪x - z_j, ξ⟫ ≥ 0`. -/
theorem exists_good_index {x : E 2} (ξ : E 2) {k₀ : Fin numHoles}
    (hk₀ : ‖x - cen ((k₀ : ℕ) : ℤ)‖ ^ 2 = 1 / 100) :
    ∃ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 = 1 / 100 ∧
      ∀ j ≠ k, ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 = 1 / 100 → 0 ≤ ⟪x - cen ((j : ℕ) : ℤ), ξ⟫ := by
  by_cases h : ∀ j ≠ k₀, ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 = 1 / 100 → 0 ≤ ⟪x - cen ((j : ℕ) : ℤ), ξ⟫
  · exact ⟨k₀, hk₀, h⟩
  push Not at h
  obtain ⟨j₀, hj₀k, hj₀, hneg⟩ := h
  refine ⟨j₀, hj₀, fun j hj hj1 ↦ ?_⟩
  by_cases hjk : j = k₀
  · subst hjk
    rw [sub_cen_eq_neg_of_kiss hj₀k hj₀ hk₀, inner_neg_left] at hneg
    linarith
  · exact absurd (eq_of_three hj hjk hj₀k hj1 hj₀ hk₀) not_false

theorem norm_ray_sub_sq (x z ξ : E 2) (t : ℝ) :
    ‖x + t • ξ - z‖ ^ 2 = ‖x - z‖ ^ 2 + 2 * t * ⟪x - z, ξ⟫ + t ^ 2 * ‖ξ‖ ^ 2 := by
  rw [show x + t • ξ - z = (x - z) + t • ξ by abel, norm_add_sq_real, inner_smul_right,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-! ### `v` is a viscosity supersolution -/

theorem isViscSuper_vSup : IsViscSuper domain (fun _ ↦ 1) vSup := by
  refine ⟨continuous_vSup.continuousOn, fun x _ ↦ vSup_nonneg x, fun φ hφ x hx htouch ↦ ?_⟩
  obtain ⟨-, hφx, hle⟩ := htouch
  rw [isOpen_domain.nhdsWithin_eq hx] at hle
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_of_smooth hφ
  obtain ⟨h0, hk⟩ := normSq_of_mem_domain hx
  have hUn := isOpen_domain.mem_nhds hx
  -- inside a disc
  by_cases A : ∃ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 < 1 / 100
  · obtain ⟨k, hkA⟩ := A
    left
    have hO : ∀ᶠ y in 𝓝 x, vSup y = wIn (cen ((k : ℕ) : ℤ)) y := by
      filter_upwards [hUn, (isOpen_lt_normsq _ _).mem_nhds hkA] with y hyU hyA
      have hyA : ‖y - cen ((k : ℕ) : ℤ)‖ ^ 2 < 1 / 100 := hyA
      obtain ⟨hothers, hy0⟩ := geom_disc hyA.le
      rw [vSup_eq, wSum_eq_single k hothers, max_hLayer_eq_zero (by linarith [ten_lt_layerRad_sq]),
        max_eq_left (wIn_pos ((normSq_of_mem_domain hyU).2 k).le hyA).le, add_zero]
    calc Δ φ x ≤ Δ (wIn (cen ((k : ℕ) : ℤ))) x := laplacian_le_of_touch hφ2 (contDiff_wIn _)
          (by filter_upwards [hle, hO] with y h1 h2; rwa [← h2]) (hφx.trans hO.self_of_nhds)
      _ = 0 := laplacian_wIn (hk k).le hkA.le
  push Not at A
  -- in the outer layer
  rcases lt_or_ge (layerRad ^ 2) (‖x - 0‖ ^ 2) with C | C
  · left
    have hO : ∀ᶠ y in 𝓝 x, vSup y = hLayer y := by
      filter_upwards [hUn, (isOpen_gt_normsq 0 _).mem_nhds C] with y hyU hyC
      have hyC : layerRad ^ 2 < ‖y - 0‖ ^ 2 := hyC
      rw [vSup_eq, wSum_eq_zero fun j ↦ (geom_far (by linarith [ten_lt_layerRad_sq]) _).le,
        max_eq_left (hLayer_pos hyC (normSq_of_mem_domain hyU).1.le).le, zero_add]
    calc Δ φ x ≤ Δ hLayer x := laplacian_le_of_touch hφ2 contDiff_hLayer
          (by filter_upwards [hle, hO] with y h1 h2; rwa [← h2]) (hφx.trans hO.self_of_nhds)
      _ = 0 := laplacian_hLayer C.le h0.le
  -- the zero set
  right
  have hv0 : vSup x = 0 := by rw [vSup_eq, wSum_eq_zero A, max_hLayer_eq_zero C]; ring
  have hφ0 : φ x = 0 := hφx.trans hv0
  refine ⟨hφ0, ?_⟩
  have hφd := hφ2.differentiable (by norm_num) x
  -- on the circle of the outer layer
  by_cases hC : ‖x - 0‖ ^ 2 = layerRad ^ 2
  · refine fb_step hφ2 contDiff_hLayer hφ0 (hLayer_eq_zero hC) (norm_gradient_hLayer hC) ?_
    filter_upwards [hle, (isOpen_gt_normsq 0 10.83).mem_nhds
      (show 10.83 < ‖x - 0‖ ^ 2 by rw [hC]; exact ten_lt_layerRad_sq)] with y h1 h2
    rwa [vSup_eq, wSum_eq_zero fun j ↦ (geom_far h2 _).le, zero_add] at h1
  -- on a disc circle
  by_cases hB : ∃ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 = 1 / 100
  · obtain ⟨k₀, hk₀⟩ := hB
    obtain ⟨k, hkc, hgood⟩ := exists_good_index (∇ φ x) hk₀
    have hx0 : ‖x - 0‖ ^ 2 < layerRad ^ 2 := by
      linarith [(geom_disc hkc.le).2, ten_lt_layerRad_sq]
    refine le_trans (norm_gradient_le_of_ray hφd
      ((contDiff_wIn _).differentiable (by norm_num) x).hasGradientAt hφ0 (wIn_eq_zero hkc) ?_)
      (norm_gradient_wIn hkc).le
    have hray := tendsto_ray x (∇ φ x)
    have hothers : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j ≠ k,
        1 / 100 ≤ ‖x + t • ∇ φ x - cen ((j : ℕ) : ℤ)‖ ^ 2 := by
      refine Filter.eventually_all.2 fun j ↦ ?_
      by_cases hjk : j = k
      · exact Filter.Eventually.of_forall fun _ h ↦ absurd hjk h
      rcases (A j).lt_or_eq with hlt | heq
      · filter_upwards [hray.eventually ((isOpen_gt_normsq _ _).mem_nhds hlt)] with t ht _
        exact (show 1 / 100 < ‖x + t • ∇ φ x - cen ((j : ℕ) : ℤ)‖ ^ 2 from ht).le
      · filter_upwards [self_mem_nhdsWithin] with t ht _
        have ht : (0 : ℝ) < t := ht
        rw [norm_ray_sub_sq, ← heq]
        have := hgood j hjk heq.symm
        nlinarith [sq_nonneg t, sq_nonneg ‖∇ φ x‖]
    filter_upwards [hray.eventually hle, hothers,
      hray.eventually ((isOpen_lt_normsq 0 _).mem_nhds hx0)] with t h1 h2 h3
    rwa [vSup_eq, wSum_eq_single k h2, max_hLayer_eq_zero (show
      ‖x + t • ∇ φ x - 0‖ ^ 2 < layerRad ^ 2 from h3).le, add_zero] at h1
  -- interior zeros: `φ` has a local maximum
  push Not at hB
  have hA' : ∀ j : Fin numHoles, 1 / 100 < ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 :=
    fun j ↦ lt_of_le_of_ne (A j) (Ne.symm (hB j))
  have hC' : ‖x - 0‖ ^ 2 < layerRad ^ 2 := lt_of_le_of_ne C hC
  have hall : ∀ᶠ y in 𝓝 x, ∀ j : Fin numHoles, 1 / 100 ≤ ‖y - cen ((j : ℕ) : ℤ)‖ ^ 2 :=
    Filter.eventually_all.2 fun j ↦ by
      filter_upwards [(isOpen_gt_normsq _ _).mem_nhds (hA' j)] with y hy
      exact (show 1 / 100 < ‖y - cen ((j : ℕ) : ℤ)‖ ^ 2 from hy).le
  have hmax : IsLocalMax φ x := by
    filter_upwards [hle, hall, (isOpen_lt_normsq 0 _).mem_nhds hC'] with y h1 h2 h3
    rw [vSup_eq, wSum_eq_zero h2,
      max_hLayer_eq_zero (show ‖y - 0‖ ^ 2 < layerRad ^ 2 from h3).le] at h1
    rw [hφ0]; linarith
  rw [gradient_eq_zero_of_isLocalMax hmax, norm_zero]
  norm_num

/-! ### `v` lies above `gSub` -/

theorem gSub_le_vSup {x : E 2} (hx : x ∈ closure domain) : gSub x ≤ vSup x := by
  obtain ⟨h0, hk⟩ := normSq_of_mem_closure hx
  rcases le_or_gt (gSub x) 0 with hg | hg
  · exact hg.trans (vSup_nonneg x)
  by_cases A : ∃ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 < 1 / 100
  · obtain ⟨k, hkA⟩ := A
    obtain ⟨hothers, hx0⟩ := geom_disc hkA.le
    have hval : gSub x = qIn (cen ((k : ℕ) : ℤ)) x := by
      rw [gSub_eq, (qSum_of_disc hkA.le).1, (qLayer_floor (by linarith)).1]; ring
    rw [hval] at hg ⊢
    rw [vSup_eq, wSum_eq_single k hothers]
    have := qIn_le_wIn (hk k) hkA.le hg
    have := le_max_left (wIn (cen ((k : ℕ) : ℤ)) x) 0
    have := le_max_right (hLayer x) 0
    linarith
  push Not at A
  have hval : gSub x = qLayer x := by rw [gSub_eq, (qSum_of_far A).1]; ring
  rw [hval] at hg ⊢
  have hC : 15 < ‖x - 0‖ ^ 2 := by
    by_contra hc; push Not at hc
    rw [(qLayer_floor hc).1] at hg; norm_num at hg
  set τ := ‖x - 0‖ ^ 2 with hτdef
  have hτ0 : 0 < τ := by linarith
  have hqv : qLayer x = pOut (4 * Real.log τ + (epsOut - 4 * Real.log 16)) := by
    rw [qLayer, logRad_apply, max_eq_left (by linarith)]
  have hlog : Real.log τ ≤ Real.log 16 := Real.log_le_log hτ0 h0
  have htf : tF ≤ 4 * Real.log τ + (epsOut - 4 * Real.log 16) := by
    by_contra h
    have := floorCap_le_floor (Lc := 1) (tc := 1) lF_pos one_pos tF_le_one (not_le.1 h).le
    rw [← pOut, ← hqv] at this
    unfold tF at this; linarith
  have hq : qLayer x = 4 * Real.log τ + (epsOut - 4 * Real.log 16) := by
    rw [hqv, pOut, floorCap_of_mem_Icc lF_pos one_pos ⟨htf, ?_⟩]
    have := epsOut_bounds.2; linarith
  rcases le_or_gt (layerRad ^ 2) τ with D | D
  · have hh := hLayer_eq D h0
    have hr := layerRad_bounds
    have hls := log_layerRad_sq
    have : qLayer x ≤ hLayer x := by
      rw [hq, hh, hls]; unfold epsOut; nlinarith
    rw [vSup_eq, wSum_eq_zero A]
    have := le_max_left (hLayer x) 0
    linarith
  · exfalso
    have := Real.log_lt_log hτ0 D
    rw [log_layerRad_sq] at this
    have := epsOut_bounds.2
    rw [hq] at hg
    linarith

/-- **The upper bound.** `v` belongs to Perron's class `𝒮_{gSub}`. -/
theorem vSup_mem_perronSuperClass : vSup ∈ perronSuperClass domain (fun _ ↦ 1) gSub :=
  ⟨continuous_vSup.continuousOn, isViscSuper_vSup,
    fun x hx ↦ max_le (gSub_le_vSup hx) (vSup_nonneg x)⟩

/-- `u_min ≤ v` on `Ū`. -/
theorem perronSmallest_le_vSup {x : E 2} (hx : x ∈ closure domain) :
    perronSmallest domain (fun _ ↦ 1) gSub x ≤ vSup x :=
  perronSmallest_le vSup_mem_perronSuperClass hx

/-! ### `v` lies below `gSuper₊` -/

/-- Below the cap, a floor-and-cap profile lies above its argument. -/
theorem le_floorCap {tf lf tc lc t : ℝ} (hlf : 0 < lf) (hlc : 0 < lc) (ht : t ≤ tc) :
    t ≤ floorCap tf lf tc lc t := by
  rw [floorCap, ramp_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hlc.le)]
  have := ramp_nonneg ((tf - t) / lf)
  nlinarith

theorem wIn_le_cst {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) : max (wIn z x) 0 ≤ cst := by
  rw [wIn_val hτ, TwoDisc.pV, max_floorCap_eq cst_pos (by linarith [cst_pos]) (aw_le_cst hτ)]
  exact max_le (aw_le_cst hτ) cst_pos.le

/-- **`v ≤ gSuper₊` on `Ū`.** -/
theorem vSup_le_gSuper {x : E 2} (hx : x ∈ closure domain) : vSup x ≤ max (gSuper x) 0 := by
  obtain ⟨h0, hk⟩ := normSq_of_mem_closure hx
  rcases le_or_gt (‖x - 0‖ ^ 2) 10.83 with A | A
  · -- on `B̄_{R+a}`: `gSuper = c` and `v ≤ c`
    have hg : gSuper x = cst := by
      rw [gSuper, sIn_of_le A, (sOut_floor (by linarith)).1]; ring
    rw [hg, vSup_eq, max_hLayer_eq_zero (by linarith [ten_lt_layerRad_sq]), add_zero,
      max_eq_left cst_pos.le]
    by_cases B : ∃ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 < 1 / 100
    · obtain ⟨k, hkB⟩ := B
      rw [wSum_eq_single k (geom_disc hkB.le).1]
      exact wIn_le_cst (hk k)
    · push Not at B
      rw [wSum_eq_zero B]; exact cst_pos.le
  · rw [vSup_eq, wSum_eq_zero fun j ↦ (geom_far A _).le, zero_add]
    rcases le_or_gt (‖x - 0‖ ^ 2) (layerRad ^ 2) with D | D
    · rw [max_hLayer_eq_zero D]; exact le_max_right _ _
    · refine max_le_max ?_ le_rfl
      have hτ0 : 0 < ‖x - 0‖ ^ 2 := by linarith
      have hsIn := (sIn_floor (x := x) (by linarith [layerRad_sq_bounds.1])).1
      have hval : gSuper x = sOut x := by rw [gSuper, hsIn]; ring
      have hlog : Real.log (‖x - 0‖ ^ 2) ≤ Real.log 16 := Real.log_le_log hτ0 h0
      have hso : 1 * Real.log (‖x - 0‖ ^ 2) + (epsOut - Real.log 16) ≤ sOut x := by
        rw [sOut, logRad_apply, max_eq_left (by linarith)]
        exact le_floorCap lF_pos one_pos (by have := epsOut_bounds.2; linarith)
      rw [hval, hLayer_eq D.le h0, log_layerRad_sq]
      have hr := layerRad_bounds
      unfold epsOut at hso
      nlinarith

end PerronVariational.Necklace

end
