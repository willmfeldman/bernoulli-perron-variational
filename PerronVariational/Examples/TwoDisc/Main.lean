/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.TwoDisc.TwoPlane
public import PerronVariational.Examples.TwoDisc.Statement
public import PerronVariational.Main.Corollary2D.Structure
import PerronVariational.Main.Final
import PerronVariational.Main.InnerSmallest
import PerronVariational.Inner.LongTime

/-!
# The two-disc model example

The model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 (`[AFS]`):
`model_example : ModelExampleStatement`.

In `U = B₁(0) \ (B̄_{1/20}(p) ∪ B̄_{1/20}(-p))`, `p = (1/10, 0)`, with `Q ≡ 1`, the data `gSub`,
`gSuper` agree on `∂U`, and:
* `u_min = perronSmallest U 1 gSub` equals `(a log (a/|x - p|))₊ + (a log (a/|x + p|))₊` near `0`,
  so `0` is a two-plane point (`TwoPlane.lean`);
* `u_min` is a viscosity solution ([AFS, Theorem 1.1]), continuous on `Ū`, and lies below
  `gSuper₊` (`vSup_le_gSuper`), so `u_min ≤ u_max = perronLargest U 1 gSuper`; hence `u_max` is
  positive near the holes, and it vanishes where `gSuper < 0`;
* `u_min ≠ u_max`: otherwise `0` would be a free boundary point of `u_max`, which is classical
  there ([AFS, Corollary 1.2(ii)]); but `∇u_min(± t e₁) · e₁ = ± a/(a - t)`, so the continuous
  extension `G` of `∇u_max` would satisfy `G(0) · e₁ ≥ 1` and `≤ -1`.
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

/-- The largest subsolution of the example. -/
abbrev uMax : E 2 → ℝ := perronLargest domain (fun _ ↦ 1) gSuper

/-! ### `u_min` lies below `gSuper₊` -/

theorem gSuper_eq_cst {x : E 2} (h : ‖x - 0‖ ^ 2 ≤ 1 / 16) : gSuper x = cst := by
  have hr : rIn x = cst := by
    rw [rIn, logRad_apply, pSup, floorCap_of_cap_le lF_pos cst_pos tF_le_half_cst]
    · ring
    have hτ : 0 < max (‖x - 0‖ ^ 2) (1 / 100) := lt_max_of_lt_right (by norm_num)
    have hl : Real.log (max (‖x - 0‖ ^ 2) (1 / 100)) ≤ -(4 * Real.log 2) := by
      calc _ ≤ Real.log (1 / 16) := Real.log_le_log hτ (max_le h (by norm_num))
        _ = _ := by
          rw [one_div, Real.log_inv, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
          push_cast; ring
    have := log_two_bounds.1
    unfold cst; nlinarith
  rw [gSuper, hr, (rOut_floor (by linarith)).1]; ring

theorem vSup_le_gSuper {x : E 2} (hx : x ∈ closure domain) : vSup x ≤ max (gSuper x) 0 := by
  obtain ⟨h0, hp, hm⟩ := mem_closure_domain hx
  have hmax_w : ∀ z : E 2, 1 / 400 ≤ ‖x - z‖ ^ 2 → max (wIn z x) 0 ≤ cst := fun z hz ↦ by
    rw [max_wIn_eq hz]; exact max_le (aw_le_cst hz) cst_pos.le
  have hm' : 1 / 400 ≤ ‖x - -hole‖ ^ 2 := by rw [sq_sub_neg_hole]; exact hm
  rcases le_or_gt (‖x - 0‖ ^ 2) (1 / 16) with A | A
  · rw [gSuper_eq_cst A, max_eq_left cst_pos.le]
    rcases lt_or_ge (‖x - hole‖ ^ 2) (1 / 100) with B | B
    · rw [vSup_eq_plus B.le]; exact hmax_w hole hp
    rcases lt_or_ge (‖x + hole‖ ^ 2) (1 / 100) with C | C
    · rw [vSup_eq_minus C.le]; exact hmax_w (-hole) hm'
    rw [vSup, max_wIn_eq_zero B, max_wIn_eq_zero (z := -hole) (by rw [sq_sub_neg_hole]; exact C),
      max_hOut_eq_zero (by linarith [rho_sq_bounds.1])]
    linarith [cst_pos]
  have hB : 1 / 100 ≤ ‖x - hole‖ ^ 2 := by
    rw [sub_zero, norm_sq_eq] at A; rw [norm_sub_hole_sq]
    nlinarith [sq_nonneg (x 0 - 1 / 10), sq_nonneg (x 0 - 1 / 4)]
  have hC : 1 / 100 ≤ ‖x + hole‖ ^ 2 := by
    rw [sub_zero, norm_sq_eq] at A; rw [norm_add_hole_sq]
    nlinarith [sq_nonneg (x 0 + 1 / 10), sq_nonneg (x 0 + 1 / 4)]
  have hv : vSup x = max (hOut x) 0 := by
    rw [vSup, max_wIn_eq_zero hB, max_wIn_eq_zero (z := -hole) (by rw [sq_sub_neg_hole]; exact hC)]
    ring
  rw [hv]
  rcases le_or_gt (‖x - 0‖ ^ 2) (rho ^ 2) with D | D
  · rw [max_hOut_eq_zero D]; exact le_max_right _ _
  -- in the outer layer, `h ≤ rOut = gSuper`
  have hr := rho_bounds
  have he := eps_bounds
  set τ := ‖x - 0‖ ^ 2 with hτ
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) D
  have hlog : Real.log τ ≤ 0 := Real.log_nonpos hτ0.le h0
  have hh : hOut x = rho / 2 * Real.log τ + eps := hOut_eq D.le h0
  have hpos : 0 < hOut x := hOut_pos D h0
  have harg : rho / 2 * Real.log τ + eps ≤ 2 * eps * Real.log τ + eps := by nlinarith
  have hro : rOut x = 2 * eps * Real.log τ + eps := by
    rw [rOut, logRad_apply, max_eq_left (by nlinarith), pOut, floorCap_of_mem_Icc lF_pos one_pos]
    constructor
    · unfold tF; linarith
    · nlinarith
  have hri : rIn x = -3 / 200 := (rIn_floor (by nlinarith)).1
  rw [max_eq_left hpos.le]
  refine le_trans ?_ (le_max_left _ _)
  rw [gSuper, hri, hro, hh]
  linarith

/-! ### The inputs from [AFS] -/

theorem mainSmallest :
    IsViscSolution domain (fun _ ↦ 1) uMin ∧ ContinuousOn uMin (closure domain) := by
  obtain ⟨h1, -, h3⟩ := inner_smallest_of parabolic_existence_bdd longtime_innerVar 2 setting gSub
    isStrictSub_gSub fun x hx ↦ (gSub_eq_gSuper_of_mem_frontier hx).2
  exact ⟨h1, h3⟩

theorem uMin_mem_perronSubClass : uMin ∈ perronSubClass domain (fun _ ↦ 1) gSuper :=
  ⟨mainSmallest.2, mainSmallest.1.2, fun _ hx ↦
    (perronSmallest_le_vSup hx).trans (vSup_le_gSuper hx)⟩

theorem uMin_le_uMax {x : E 2} (hx : x ∈ closure domain) : uMin x ≤ uMax x :=
  le_perronLargest uMin_mem_perronSubClass hx

theorem isViscSolution_uMax : IsViscSolution domain (fun _ ↦ 1) uMax :=
  (main_largest 2 setting gSuper isStrictSuper_gSuper).1

/-! ### Nontriviality -/

theorem smul_eOne_mem {t : ℝ} (ht : |t| ≤ 1 / 100) : t • eOne ∈ domain :=
  (mem_domain_of_small (by rw [norm_smul_eOne]; exact ht)).1

theorem half_eOne_mem : (3 / 5 : ℝ) • eOne ∈ domain := by
  rw [mem_domain_iff]; simp; norm_num

theorem uMin_eq_zero_at : uMin ((3 / 5 : ℝ) • eOne) = 0 := by
  have hx := half_eOne_mem
  have h0 : ‖(3 / 5 : ℝ) • eOne - 0‖ ^ 2 = 9 / 25 := by
    rw [sub_zero, norm_smul_eOne]; norm_num
  refine le_antisymm ?_ (perronSmallest_nonneg perronSuperClass_nonempty' (subset_closure hx))
  refine (perronSmallest_le_vSup (subset_closure hx)).trans (le_of_eq ?_)
  rw [vSup, max_wIn_eq_zero (z := hole) (by rw [norm_sub_hole_sq]; simp; norm_num),
    max_wIn_eq_zero (z := -hole) (by rw [sq_sub_neg_hole, norm_add_hole_sq]; simp; norm_num),
    max_hOut_eq_zero (by rw [h0]; linarith [rho_sq_bounds.1])]
  ring

theorem uMax_eq_zero_at : uMax ((3 / 5 : ℝ) • eOne) = 0 := by
  have hx := subset_closure half_eOne_mem
  refine le_antisymm ((perronLargest_le hx).trans (le_of_eq ?_)) (perronLargest_nonneg hx)
  have h0 : ‖(3 / 5 : ℝ) • eOne - 0‖ ^ 2 = 9 / 25 := by
    rw [sub_zero, norm_smul_eOne]; norm_num
  rw [gSuper, (rIn_floor (by rw [h0]; norm_num)).1, (rOut_floor (by rw [h0]; norm_num)).1]
  norm_num

/-- A continuous function on a preconnected open set that is positive somewhere and zero
somewhere has a free boundary point. -/
theorem freeBoundary_nonempty {U : Set (E 2)} {u : E 2 → ℝ} (hU : IsOpen U)
    (hc : IsPreconnected U) (hu : ContinuousOn u U) {a b : E 2} (ha : a ∈ U) (hpos : 0 < u a)
    (hb : b ∈ U) (hzero : u b = 0) : (freeBoundary u U).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hA : IsOpen (posSet u U) := by
    have := hu.isOpen_inter_preimage hU (isOpen_Ioi (a := (0 : ℝ)))
    convert this using 1
    rfl
  have hB : IsOpen (closure (posSet u U))ᶜ := isClosed_closure.isOpen_compl
  obtain ⟨y, hyU, hyA, hyB⟩ := hc _ _ hA hB (fun y hy ↦ by
      by_cases h : y ∈ closure (posSet u U)
      · left
        by_contra hyA
        have : y ∈ freeBoundary u U := ⟨⟨h, fun hi ↦ hyA (interior_subset hi)⟩, hy⟩
        rw [hne] at this; exact this
      · exact Or.inr h)
    ⟨a, ha, ha, hpos⟩ ⟨b, hb, fun h ↦ by
      have hbA : b ∈ posSet u U := by
        by_contra hbA
        have : b ∈ freeBoundary u U :=
          ⟨⟨h, fun hi ↦ hbA (interior_subset hi)⟩, hb⟩
        rw [hne] at this; exact this
      exact absurd hbA.2 (by rw [hzero]; exact lt_irrefl 0)⟩
  exact hyB (subset_closure hyA)

/-! ### `u_min ≠ u_max` -/

theorem hasGradientAt_wIn {z y : E 2} (h1 : 1 / 400 ≤ ‖y - z‖ ^ 2) (h2 : ‖y - z‖ ^ 2 ≤ 1 / 100) :
    HasGradientAt (wIn z) ((-(1 / 10) / ‖y - z‖ ^ 2) • (y - z)) y := by
  have hw := hasGradientAt_logRad (P₁ := floorCapD (-1 / 10) (1 / 10) cst cst) contDiff_floorCap
    (hasDerivAt_floorCap (by norm_num) cst_pos.ne') (by norm_num) (by norm_num) clamp_wIn
    (show (1 / 3200 : ℝ) < ‖y - z‖ ^ 2 by linarith)
  rw [floorCapD_of_mem_Icc (by norm_num) cst_pos (wIn_mid h1 h2)] at hw
  convert hw using 2
  · simp only [wIn, pV]
  ring

/-- Near `t e₁`, `0 < t < 1/100`, `u_min` is the right radial solution. -/
theorem uMin_eventuallyEq_wIn {z : E 2} (hz : IsHole z) {y : E 2} (hy : ‖y‖ < 1 / 100)
    (h1 : ‖y - z‖ ^ 2 < 1 / 100) : uMin =ᶠ[𝓝 y] wIn z := by
  filter_upwards [(isOpen_lt_normsq z (1 / 100)).mem_nhds h1,
    (isOpen_lt_normsq 0 (1 / 10000)).mem_nhds (show ‖y - 0‖ ^ 2 < 1 / 10000 by
      rw [sub_zero]; nlinarith [norm_nonneg y])] with w hw1 hw2
  have hw1 : ‖w - z‖ ^ 2 < 1 / 100 := hw1
  have hw2 : ‖w - 0‖ ^ 2 < 1 / 10000 := hw2
  have hwn : ‖w‖ ≤ 1 / 100 := by
    rw [sub_zero] at hw2; nlinarith [norm_nonneg w]
  obtain ⟨hwU, hw0⟩ := mem_domain_of_small hwn
  obtain ⟨-, hp, hm⟩ := mem_domain_norm hwU
  have hzw : 1 / 400 ≤ ‖w - z‖ ^ 2 := by
    rcases hz with rfl | rfl
    · exact hp.le
    · rw [sq_sub_neg_hole]; exact hm.le
  rw [perronSmallest_eq_vSup hwU hw0]
  rcases hz with rfl | rfl
  · rw [vSup_eq_plus hw1.le, max_eq_left (wIn_pos hzw hw1).le]
  · rw [sq_sub_neg_hole] at hw1
    rw [vSup_eq_minus hw1.le, max_eq_left (wIn_pos hzw (by rw [sq_sub_neg_hole]; exact hw1)).le]

theorem gradient_uMin_e₁ {t : ℝ} (ht : 0 < t) (ht' : t < 1 / 100) :
    1 ≤ ⟪∇ uMin (t • eOne), eOne⟫ := by
  have hn : ‖t • eOne‖ < 1 / 100 := by rw [norm_smul_eOne, abs_of_pos ht]; exact ht'
  have hτ : ‖t • eOne - hole‖ ^ 2 = (1 / 10 - t) ^ 2 := by rw [norm_sub_hole_sq]; simp; ring
  have h1 : ‖t • eOne - hole‖ ^ 2 < 1 / 100 := by rw [hτ]; nlinarith
  rw [(uMin_eventuallyEq_wIn (Or.inl rfl) hn h1).gradient_eq,
    (hasGradientAt_wIn (by rw [hτ]; nlinarith) h1.le).gradient, hτ, real_inner_smul_left]
  have : ⟪t • eOne - hole, eOne⟫ = t - 1 / 10 := by
    simp [eOne, hole, EuclideanSpace.inner_single_right, inner_sub_left]
  rw [this, show t - 1 / 10 = -(1 / 10 - t) by ring]
  have hpos : 0 < 1 / 10 - t := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

theorem gradient_uMin_neg_e₁ {t : ℝ} (ht : 0 < t) (ht' : t < 1 / 100) :
    ⟪∇ uMin ((-t) • eOne), eOne⟫ ≤ -1 := by
  have hn : ‖(-t) • eOne‖ < 1 / 100 := by rw [norm_smul_eOne, abs_neg, abs_of_pos ht]; exact ht'
  have hτ : ‖(-t) • eOne - -hole‖ ^ 2 = (1 / 10 - t) ^ 2 := by
    rw [sq_sub_neg_hole, norm_add_hole_sq]; simp; ring
  have h1 : ‖(-t) • eOne - -hole‖ ^ 2 < 1 / 100 := by rw [hτ]; nlinarith
  rw [(uMin_eventuallyEq_wIn (Or.inr rfl) hn h1).gradient_eq,
    (hasGradientAt_wIn (by rw [hτ]; nlinarith) h1.le).gradient, hτ, real_inner_smul_left]
  have : ⟪(-t) • eOne - -hole, eOne⟫ = 1 / 10 - t := by
    simp [eOne, hole, EuclideanSpace.inner_single_right]
    ring
  rw [this]
  have hpos : 0 < 1 / 10 - t := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **`u_min ≠ u_max`.** -/
theorem exists_uMin_ne_uMax : ∃ x ∈ domain, uMin x ≠ uMax x := by
  by_contra hcon
  push Not at hcon
  -- `0` is a free boundary point of `u_max`
  have hpos : posSet uMax domain = posSet uMin domain := by
    ext y; simp only [posSet, Set.mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, by rwa [hcon y h1]⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, by rwa [← hcon y h1]⟩⟩
  have hfb : (0 : E 2) ∈ freeBoundary uMax domain := by
    have := zero_mem_freeBoundary
    rwa [freeBoundary, ← hpos] at this
  obtain ⟨r, hr, hball, -, -, -, G, hGc, hGeq, -⟩ :=
    corollary_2d_largest setting gSuper isStrictSuper_gSuper 0 hfb
  -- `G = ∇u_max = ∇u_min` at `± t e₁`
  have hgrad : ∀ t : ℝ, t ≠ 0 → |t| < min r (1 / 100) →
      t • eOne ∈ posSet uMax domain ∩ ball 0 r ∧ G (t • eOne) = ∇ uMin (t • eOne) := by
    intro t ht0 ht
    have htr : |t| < r := lt_of_lt_of_le ht (min_le_left _ _)
    have ht1 : |t| < 1 / 100 := lt_of_lt_of_le ht (min_le_right _ _)
    have hmem : t • eOne ∈ domain := smul_eOne_mem ht1.le
    have hball' : t • eOne ∈ ball (0 : E 2) r := by
      rw [mem_ball, dist_zero_right, norm_smul_eOne]; exact htr
    have hposm : t • eOne ∈ posSet uMax domain := by
      refine ⟨hmem, ?_⟩
      rw [← hcon _ hmem]
      rcases lt_or_gt_of_ne ht0 with hneg | hpos'
      · -- `t < 0`: the left disc
        have hn : ‖t • eOne‖ < 1 / 100 := by rw [norm_smul_eOne]; exact ht1
        have hτ : ‖t • eOne - -hole‖ ^ 2 < 1 / 100 := by
          rw [sq_sub_neg_hole, norm_add_hole_sq]; simp
          rw [abs_lt] at ht1; nlinarith
        rw [(uMin_eventuallyEq_wIn (Or.inr rfl) hn hτ).eq_of_nhds]
        have hzw : 1 / 400 ≤ ‖t • eOne - -hole‖ ^ 2 := by
          rw [sq_sub_neg_hole]; exact (mem_domain_norm hmem).2.2.le
        exact wIn_pos hzw hτ
      · rw [abs_of_pos hpos'] at ht1
        exact uMin_pos_e₁ hpos' ht1.le
    refine ⟨⟨hposm, hball'⟩, ?_⟩
    rw [hGeq _ ⟨hposm, hball'⟩]
    have heq : uMax =ᶠ[𝓝 (t • eOne)] uMin := by
      filter_upwards [isOpen_domain.mem_nhds hmem] with w hw using (hcon w hw).symm
    exact heq.gradient_eq
  -- continuity of `G` at `0` along `± t e₁`
  have h0mem : (0 : E 2) ∈ closure (posSet uMax domain) ∩ ball 0 r :=
    ⟨hfb.1.1, mem_ball_self hr⟩
  have hGc0 := hGc 0 h0mem
  have hpr : (0 : ℝ) < min r (1 / 100) := lt_min hr (by norm_num)
  have htend : ∀ s : ℝ, s ≠ 0 → Tendsto (fun t : ℝ ↦ G ((s * t) • eOne)) (𝓝[>] 0) (𝓝 (G 0)) := by
    intro s hs
    have h1 : Tendsto (fun t : ℝ ↦ (s * t) • eOne) (𝓝[>] 0)
        (𝓝[closure (posSet uMax domain) ∩ ball 0 r] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Continuous fun t : ℝ ↦ (s * t) • eOne := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · have hsp : 0 < min r (1 / 100) / |s| := div_pos hpr (abs_pos.2 hs)
        filter_upwards [Ioo_mem_nhdsGT hsp] with t ht
        have hst : |s * t| < min r (1 / 100) := by
          rw [abs_mul, abs_of_pos ht.1]
          have := ht.2; rw [lt_div_iff₀ (abs_pos.2 hs)] at this; linarith
        obtain ⟨hA, -⟩ := hgrad (s * t) (mul_ne_zero hs ht.1.ne') hst
        exact ⟨subset_closure hA.1, hA.2⟩
    exact hGc0.tendsto.comp h1
  have hlim1 : 1 ≤ ⟪G 0, eOne⟫ := by
    have := (((continuous_id.inner continuous_const : Continuous fun w : E 2 ↦ ⟪w, eOne⟫).tendsto
      _).comp (htend 1 one_ne_zero))
    refine ge_of_tendsto this ?_
    filter_upwards [Ioo_mem_nhdsGT hpr] with t ht
    simp only [Function.comp_apply, one_mul]
    have htt : |t| < min r (1 / 100) := by rw [abs_of_pos ht.1]; exact ht.2
    rw [(hgrad t ht.1.ne' htt).2]
    exact gradient_uMin_e₁ ht.1 (lt_of_lt_of_le ht.2 (min_le_right _ _))
  have hlim2 : ⟪G 0, eOne⟫ ≤ -1 := by
    have := (((continuous_id.inner continuous_const : Continuous fun w : E 2 ↦ ⟪w, eOne⟫).tendsto
      _).comp (htend (-1) (by norm_num)))
    refine le_of_tendsto this ?_
    filter_upwards [Ioo_mem_nhdsGT hpr] with t ht
    simp only [Function.comp_apply, neg_one_mul]
    have htt : |-t| < min r (1 / 100) := by rw [abs_neg, abs_of_pos ht.1]; exact ht.2
    rw [(hgrad (-t) (neg_ne_zero.2 ht.1.ne') htt).2]
    exact gradient_uMin_neg_e₁ ht.1 (lt_of_lt_of_le ht.2 (min_le_right _ _))
  linarith

/-! ### The theorem -/

/-- **The two-disc model example.** -/
theorem model_example : ModelExampleStatement := by
  have hUc := isConnected_domain
  have hpt : (1 / 100 : ℝ) • eOne ∈ domain := smul_eOne_mem (by norm_num)
  have hminpos : 0 < uMin ((1 / 100 : ℝ) • eOne) := uMin_pos_e₁ (by norm_num) le_rfl
  have hmaxpos : 0 < uMax ((1 / 100 : ℝ) • eOne) :=
    lt_of_lt_of_le hminpos (uMin_le_uMax (subset_closure hpt))
  refine ⟨setting, gSub, gSuper, rfl, isStrictSub_gSub,
    fun x hx ↦ (gSub_eq_gSuper_of_mem_frontier hx).2, isStrictSuper_gSuper,
    fun x hx ↦ (gSub_eq_gSuper_of_mem_frontier hx).1,
    ⟨_, hpt, hminpos⟩, ⟨_, half_eOne_mem, uMin_eq_zero_at⟩, ⟨0, zero_mem_freeBoundary⟩,
    ⟨_, hpt, hmaxpos⟩, ⟨_, half_eOne_mem, uMax_eq_zero_at⟩, ?_, zero_mem_freeBoundary,
    tendstoLocallyUniformly_blowup, fun v hv y ↦ isBlowupLimit_eq hv y, exists_uMin_ne_uMax⟩
  exact freeBoundary_nonempty isOpen_domain hUc.isPreconnected isViscSolution_uMax.1.1 hpt hmaxpos
    half_eOne_mem uMax_eq_zero_at

end PerronVariational.TwoDisc

end
