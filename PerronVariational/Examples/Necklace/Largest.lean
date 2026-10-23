/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.TwoPlane
public import PerronVariational.Examples.TwoDisc.Main
public import PerronVariational.Main.Corollary2D.Structure
import PerronVariational.Main.Final
import PerronVariational.Main.InnerSmallest
import PerronVariational.Main.InnerLargest
import PerronVariational.Inner.LongTime
import PerronVariational.Stationary.ViscosityJet
import PerronVariational.Stationary.ViscosityLocal
import Mathlib.Topology.Order.Lattice

/-!
# The largest subsolution fills the inside of the necklace

For the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M. Feldman, K.
Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`), with `u_max = perronLargest U 1 gSuper`:

* `perronSmallest_le_perronLargest`: `u_min ≤ u_max` on `Ū` (`u_min` is a continuous viscosity
  solution, [AFS, [Theorem 1.1](#AFS:t.main)], lying below `v ≤ gSuper₊`);
* `perronLargest_kiss_pos`: `u_max > 0` at every kissing point `m_k`. Otherwise `m_k` would be a
  free boundary point of `u_max`, which is classical there ([AFS,
  [Corollary 1.2(ii)](#AFS:part.largest-reg)]): the continuous extension `G` of `∇u_max` to the
  closure of the positivity set exists near `m_k`. On both segments `m_k ± s e_k` we have
  `u_max ≥ u_min ≥ w ≥ s`, so the mean value theorem gives `⟪G(m_k), e_k⟫ ≥ 1` and
  `⟪G(m_k), -e_k⟫ ≥ 1`, which is absurd;
* `perronLargest_pos_of_mem_sphere`: hence `u_max > 0` on the compact set `∂B_{ρ_in}(0) ∩ Ū`,
  which is covered by the discs `B_a(z_k)` and the kissing points;
* `uMax_pos_of_mem_inner`: gluing `max(u_max, κ)` into `U ∩ B_{ρ_in}(0)` gives an element
  of `𝒮^{gSuper}` (`IsViscSub.max_const`, `isViscSub_piecewise`), so `u_max ≥ κ > 0` on
  `U ∩ B_{ρ_in}(0)`;
* `not_uMin_ae_eq_uMax`: `u_min = 0 < u_max` on `B₃(0)`, so `u_min ≠ u_max` on a
  set of positive measure;
* nontriviality of `u_max`: it vanishes in the dip of `gSuper` (`perronLargest_dip`) and has a
  nonempty free boundary (`freeBoundary_perronLargest_nonempty`).
-/

open Set Filter Topology Metric InnerProductSpace Real MeasureTheory
open scoped Gradient Laplacian ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational

/-- `max(u, κ)` with `κ > 0` is a viscosity subsolution if `u` is one. -/
theorem IsViscSub.max_const {d : ℕ} {W : Set (E d)} {Q u : E d → ℝ} (hW : IsOpen W)
    (hu : IsViscSub W Q u) {κ : ℝ} (hκ : 0 < κ) : IsViscSub W Q (fun x ↦ max (u x) κ) := by
  refine ⟨ContinuousOn.sup hu.1 continuousOn_const, fun x _ ↦ hκ.le.trans (le_max_right _ _),
    fun φ hφ x htouch ↦ ?_⟩
  obtain ⟨⟨-, hxW⟩, hφx, hle⟩ := htouch
  have hS : closure (posSet (fun x ↦ max (u x) κ) W) ∩ W = W := by
    ext y
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨subset_closure ⟨h, hκ.trans_le (le_max_right _ _)⟩, h⟩⟩
  rw [hS, hW.nhdsWithin_eq hxW] at hle
  simp only at hφx hle
  have hφpos : 0 < φ x := by
    by_contra h
    push Not at h
    rw [max_eq_right h] at hφx
    linarith [le_max_right (u x) κ]
  rw [max_eq_left hφpos.le] at hφx
  rcases lt_or_ge (u x) κ with hux | hux
  · -- `φ` has a local minimum at `x`
    left
    rw [max_eq_right hux.le] at hφx
    refine IsLocalMin.laplacian_nonneg (contDiff_two_of_smooth hφ) ?_
    filter_upwards [hle] with y hy
    have h1 : κ ≤ max (φ y) 0 := (le_max_right _ _).trans hy
    have h2 : 0 < φ y := by
      by_contra h
      push Not at h
      rw [max_eq_right h] at h1
      linarith
    rw [max_eq_left h2.le] at h1
    linarith
  · rw [max_eq_left hux] at hφx
    have hupos : 0 < u x := hκ.trans_le hux
    refine hu.2.2 φ hφ x ⟨⟨subset_closure ⟨hxW, hupos⟩, hxW⟩, ?_, ?_⟩
    · simp only; rw [max_eq_left hφpos.le, hφx]
    · refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [hle] with y hy
      exact (le_max_left _ _).trans hy

namespace Necklace

open TwoDisc (cst cst_pos cst_bounds wIn wIn_eq wIn_pos freeBoundary_nonempty)

/-- The largest subsolution of the example. -/
abbrev uMax : E 2 → ℝ := perronLargest domain (fun _ ↦ 1) gSuper

/-! ### The inputs from [AFS] -/

theorem mainSmallest :
    IsViscSolution domain (fun _ ↦ 1) uMin ∧ ContinuousOn uMin (closure domain) := by
  obtain ⟨h1, -, h3⟩ := inner_smallest_of parabolic_existence_bdd longtime_innerVar 2 setting gSub
    isStrictSub_gSub fun x hx ↦ (gSub_eq_gSuper_of_mem_frontier hx).2
  exact ⟨h1, h3⟩

theorem mainLargest :
    IsViscSolution domain (fun _ ↦ 1) uMax ∧ ContinuousOn uMax (closure domain) := by
  obtain ⟨h1, -, h3⟩ := inner_largest_of parabolic_existence_bdd longtime_innerVar 2 setting
    gSuper isStrictSuper_gSuper
  exact ⟨h1, h3⟩

theorem perronSmallest_mem_perronSubClass : uMin ∈ perronSubClass domain (fun _ ↦ 1) gSuper :=
  ⟨mainSmallest.2, mainSmallest.1.2, fun _ hx ↦
    (perronSmallest_le_vSup hx).trans (vSup_le_gSuper hx)⟩

/-- `u_min ≤ u_max` on `Ū`. -/
theorem perronSmallest_le_perronLargest {x : E 2} (hx : x ∈ closure domain) : uMin x ≤ uMax x :=
  le_perronLargest perronSmallest_mem_perronSubClass hx

/-! ### `u_max > 0` at the kissing points -/

/-- On the segment from the circle `|x - z| = a` towards `z`, `w ≥ s` at distance `s`. -/
theorem le_wIn {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 20) {z x : E 2}
    (hx : ‖x - z‖ = kissRad - s) : s ≤ wIn z x := by
  unfold kissRad at hx
  set u := 1 / 10 - s with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  have hτ : ‖x - z‖ ^ 2 = u ^ 2 := by rw [hx]
  rw [wIn_eq (by rw [hτ]; nlinarith) (by rw [hτ]; nlinarith), hτ, Real.log_pow,
    show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.log_pow]
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (1 / 10) / u by positivity)
  rw [Real.log_div (by norm_num) hu0.ne', inv_div] at hl
  have : u / (1 / 10) = 10 * u := by field_simp
  rw [this] at hl
  push_cast
  nlinarith

/-- The derivative bound along a segment into the positivity set: if `u_max(x₀) = 0` and
`u_max(x₀ + s v) ≥ s` for small `s > 0`, then the continuous extension `G` of `∇u_max` satisfies
`⟪G(x₀), v⟫ ≥ 1` (mean value theorem and continuity of `G`). -/
theorem one_le_inner_of_classical {x₀ v : E 2} (hv : ‖v‖ = 1) {r s₁ : ℝ} (hr : 0 < r)
    (hs₁ : 0 < s₁) {G : E 2 → E 2} (hx₀ : x₀ ∈ domain) (h0 : uMax x₀ = 0)
    (hC2 : ContDiffOn ℝ 2 uMax (posSet uMax domain ∩ ball x₀ r))
    (hGc : ContinuousOn G (closure (posSet uMax domain) ∩ ball x₀ r))
    (hGeq : ∀ y ∈ posSet uMax domain ∩ ball x₀ r, G y = ∇ uMax y)
    (hseg : ∀ s ∈ Ioc 0 s₁, x₀ + s • v ∈ domain ∧ s ≤ uMax (x₀ + s • v)) :
    1 ≤ ⟪G x₀, v⟫ := by
  have hcU : ContinuousOn uMax domain := mainLargest.1.1.1
  have hO : IsOpen (posSet uMax domain ∩ ball x₀ r) := by
    refine IsOpen.inter ?_ isOpen_ball
    exact hcU.isOpen_inter_preimage isOpen_domain (isOpen_Ioi (a := (0 : ℝ)))
  have hdist : ∀ s : ℝ, dist (x₀ + s • v) x₀ = |s| := by
    intro s; rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs]
  have hmemO : ∀ s, 0 < s → s ≤ s₁ → s < r → x₀ + s • v ∈ posSet uMax domain ∩ ball x₀ r := by
    intro s hs hs1 hsr
    obtain ⟨hU, hle⟩ := hseg s ⟨hs, hs1⟩
    exact ⟨⟨hU, hs.trans_le hle⟩, by rw [mem_ball, hdist, abs_of_pos hs]; exact hsr⟩
  have hmem : x₀ ∈ closure (posSet uMax domain) ∩ ball x₀ r := by
    refine ⟨?_, mem_ball_self hr⟩
    have ht : Tendsto (fun s : ℝ ↦ x₀ + s • v) (𝓝[>] 0) (𝓝 x₀) := by
      have : Continuous fun s : ℝ ↦ x₀ + s • v := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min s₁ r by positivity)] with s hs
    exact (hmemO s hs.1 (hs.2.le.trans (min_le_left _ _)) (hs.2.trans_le (min_le_right _ _))).1
  by_contra hlt
  push Not at hlt
  have hcont : ContinuousWithinAt (fun y ↦ ⟪G y, v⟫)
      (closure (posSet uMax domain) ∩ ball x₀ r) x₀ :=
    (hGc x₀ hmem).inner continuousWithinAt_const
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.1 (hcont (isOpen_Iio.mem_nhds hlt))
  set t := min (min s₁ r) ε / 2 with htdef
  have ht0 : 0 < t := by positivity
  have hts : t < min (min s₁ r) ε := by rw [htdef]; linarith
  have ht1 : t < s₁ := hts.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have htr : t < r := hts.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hte : t < ε := hts.trans_le (min_le_right _ _)
  -- the mean value theorem on `[0, t]`
  have hfc : ContinuousOn (fun s : ℝ ↦ uMax (x₀ + s • v)) (Icc 0 t) := by
    refine hcU.comp (by fun_prop : Continuous fun s : ℝ ↦ x₀ + s • v).continuousOn ?_
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; simpa using hx₀
    · exact (hseg s ⟨h, hs.2.trans ht1.le⟩).1
  have hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun s : ℝ ↦ uMax (x₀ + s • v))
      (⟪∇ uMax (x₀ + s • v), v⟫) s := by
    intro s hs
    have hsO := hmemO s hs.1 (hs.2.le.trans ht1.le) (hs.2.trans htr)
    have hd : DifferentiableAt ℝ uMax (x₀ + s • v) :=
      (hC2.contDiffAt (hO.mem_nhds hsO)).differentiableAt (by norm_num)
    have hp : HasDerivAt (fun s : ℝ ↦ x₀ + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add x₀
    have hc := hd.hasFDerivAt.comp_hasDerivAt s hp
    rw [show ⟪∇ uMax (x₀ + s • v), v⟫ = fderiv ℝ uMax (x₀ + s • v) v by
      rw [gradient, InnerProductSpace.toDual_symm_apply]]
    exact hc
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope _ _ ht0 hfc hderiv
  have hcO := hmemO c hc.1 (hc.2.le.trans ht1.le) (hc.2.trans htr)
  have hslope : 1 ≤ ⟪∇ uMax (x₀ + c • v), v⟫ := by
    rw [hceq, zero_smul, add_zero, h0, sub_zero, sub_zero, le_div_iff₀ ht0, one_mul]
    exact (hseg t ⟨ht0, ht1.le⟩).2
  have hin : x₀ + c • v ∈ ball x₀ ε ∩ (closure (posSet uMax domain) ∩ ball x₀ r) :=
    ⟨by rw [mem_ball, hdist, abs_of_pos hc.1]; exact hc.2.trans hte,
      subset_closure hcO.1, hcO.2⟩
  have := hεsub hin
  simp only [mem_preimage, mem_Iio] at this
  rw [hGeq _ hcO] at this
  linarith

/-- On the segment `m_k + s e_k` (into `B_a(z_k)`), `u_max ≥ s`. -/
theorem le_perronLargest_kiss_add (k : ℤ) {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 100) :
    kiss k + s • tang k ∈ domain ∧ s ≤ uMax (kiss k + s • tang k) := by
  have hU := kiss_add_smul_mem_domain k (s := s) (by rw [abs_of_pos hs]; exact hs')
  obtain ⟨h1, h2⟩ := normSq_kiss_add_smul_tang k hs (by linarith)
  refine ⟨hU, ?_⟩
  have hw := le_wIn (z := cen k) (x := kiss k + s • tang k) hs (by linarith)
    (by rw [norm_kiss_add_smul_tang_sub_cen, abs_of_neg (by unfold kissRad; linarith)]; ring)
  exact hw.trans ((wIn_le_perronSmallest k h1 h2).trans
    (perronSmallest_le_perronLargest (subset_closure hU)))

/-- On the segment `m_k - s e_k` (into `B_a(z_{k-1})`), `u_max ≥ s`. -/
theorem le_perronLargest_kiss_sub (k : ℤ) {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 100) :
    kiss k + s • (-tang k) ∈ domain ∧ s ≤ uMax (kiss k + s • (-tang k)) := by
  rw [smul_neg, ← neg_smul]
  have hU := kiss_add_smul_mem_domain k (s := -s) (by rw [abs_neg, abs_of_pos hs]; exact hs')
  obtain ⟨h1, h2⟩ := normSq_kiss_sub_smul_tang k hs (by linarith)
  refine ⟨hU, ?_⟩
  have hw := le_wIn (z := cen (k - 1)) (x := kiss k + (-s) • tang k) hs (by linarith)
    (by rw [norm_kiss_sub_smul_tang_sub_cen, abs_of_neg (by unfold kissRad; linarith)]; ring)
  exact hw.trans ((wIn_le_perronSmallest (k - 1) h1 h2).trans
    (perronSmallest_le_perronLargest (subset_closure hU)))

/-- **`u_max > 0` at every kissing point.** -/
theorem perronLargest_kiss_pos (k : ℤ) : 0 < uMax (kiss k) := by
  by_contra hneg
  have hU := kiss_mem_domain k
  have h0 : uMax (kiss k) = 0 :=
    le_antisymm (not_lt.1 hneg) (perronLargest_nonneg (subset_closure hU))
  have hfb : kiss k ∈ freeBoundary uMax domain := by
    refine ⟨⟨?_, fun h ↦ ?_⟩, hU⟩
    · have ht : Tendsto (fun s : ℝ ↦ kiss k + s • tang k) (𝓝[>] 0) (𝓝 (kiss k)) := by
        have : Continuous fun s : ℝ ↦ kiss k + s • tang k := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 100 by norm_num)] with s hs
      obtain ⟨hU', hle⟩ := le_perronLargest_kiss_add k hs.1 hs.2.le
      exact ⟨hU', hs.1.trans_le hle⟩
    · have := (interior_subset h).2
      rw [h0] at this
      exact lt_irrefl 0 this
  obtain ⟨r, hr, -, -, hC2, -, G, hGc, hGeq, -⟩ :=
    corollary_2d_largest setting gSuper isStrictSuper_gSuper (kiss k) hfb
  have h1 := one_le_inner_of_classical (norm_tang k) hr (by norm_num : (0 : ℝ) < 1 / 100) hU h0
    hC2 hGc hGeq fun s hs ↦ le_perronLargest_kiss_add k hs.1 hs.2
  have h2 := one_le_inner_of_classical (v := -tang k) (by rw [norm_neg, norm_tang]) hr
    (by norm_num : (0 : ℝ) < 1 / 100) hU h0 hC2 hGc hGeq
    fun s hs ↦ le_perronLargest_kiss_sub k hs.1 hs.2
  rw [inner_neg_right] at h2
  linarith

/-! ### `u_max > 0` on the inscribed circle -/

/-- The circle `∂B_{ρ_in}(0)` inside `Ū`. -/
def innerCircle : Set (E 2) := sphere 0 innerRad ∩ closure domain

theorem isCompact_innerCircle : IsCompact innerCircle :=
  (isCompact_sphere 0 innerRad).inter_right isClosed_closure

theorem kiss_mem_innerCircle (k : ℤ) : kiss k ∈ innerCircle :=
  ⟨by rw [mem_sphere, dist_zero_right, norm_kiss], subset_closure (kiss_mem_domain k)⟩

theorem perronLargest_pos_of_mem_sphere {x : E 2} (hx : x ∈ innerCircle) : 0 < uMax x := by
  obtain ⟨hs, hcl⟩ := hx
  rw [mem_sphere, dist_zero_right] at hs
  obtain ⟨k, hk | hk⟩ := exists_norm_sub_cen_lt_or_eq_kiss hs
  · obtain ⟨j, hj⟩ := exists_fin_cen_eq k
    have h1 : 1 / 400 ≤ ‖x - cen k‖ ^ 2 := by rw [← hj]; exact (normSq_of_mem_closure hcl).2 j
    have h2 : ‖x - cen k‖ ^ 2 < 1 / 100 := by
      have := pow_lt_pow_left₀ hk (norm_nonneg _) two_ne_zero
      unfold kissRad at this; linarith
    exact (perronSmallest_pos k h1 h2).trans_le (perronSmallest_le_perronLargest hcl)
  · rw [hk]; exact perronLargest_kiss_pos k

theorem exists_pos_le_on_innerCircle : ∃ δ > 0, ∀ x ∈ innerCircle, δ ≤ uMax x := by
  obtain ⟨m, hm, hmin⟩ := isCompact_innerCircle.exists_isMinOn ⟨_, kiss_mem_innerCircle 0⟩
    (mainLargest.2.mono inter_subset_right)
  exact ⟨uMax m, perronLargest_pos_of_mem_sphere hm, fun x hx ↦ hmin hx⟩

/-! ### Gluing `max(u_max, κ)` inside the inscribed circle -/

theorem gSuper_eq_cst {x : E 2} (h : ‖x - 0‖ ^ 2 ≤ 10.83) : gSuper x = cst := by
  rw [gSuper, sIn_of_le h, (sOut_floor (by linarith)).1]; ring

theorem normSq_lt_of_mem_ball {x : E 2} (hx : x ∈ ball (0 : E 2) innerRad) :
    ‖x - 0‖ ^ 2 ≤ 10.83 := by
  rw [mem_ball, dist_zero_right] at hx
  rw [sub_zero]
  have := pow_lt_pow_left₀ hx (norm_nonneg _) two_ne_zero
  nlinarith [innerRad_bounds.2, innerRad_pos]

/-- On a hole circle inside `Ū`, `u_max ≥ c`. -/
theorem cst_le_perronLargest_of_frontier {x : E 2} (hx : x ∈ frontier domain)
    (hx0 : ‖x - 0‖ ^ 2 < 16) : cst ≤ uMax x := by
  have hcl : x ∈ closure domain := frontier_subset_closure hx
  have h1 : gSub x ≤ uMin x := le_perronSmallest' perronSuperClass_nonempty hcl
  rcases mem_frontier_cases hx with h | ⟨k, hk⟩
  · linarith
  · rw [gSub_on_circle hk] at h1
    exact h1.trans (perronSmallest_le_perronLargest hcl)

/-- **`u_max` fills the inside of the necklace**: `u_max ≥ κ > 0` on `U ∩ B_{ρ_in}(0)`. -/
theorem uMax_pos_of_mem_inner :
    ∃ κ > 0, ∀ x ∈ domain ∩ ball (0 : E 2) innerRad, κ ≤ uMax x := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_on_innerCircle
  set κ := min δ cst / 2 with hκ
  have hκ0 : 0 < κ := by have := cst_pos; positivity
  have hκδ : κ < δ := by rw [hκ]; linarith [min_le_left δ cst]
  have hκc : κ < cst := by rw [hκ]; linarith [min_le_right δ cst, cst_pos]
  set W := domain ∩ ball (0 : E 2) innerRad with hW
  have hWo : IsOpen W := isOpen_domain.inter isOpen_ball
  have hWU : W ⊆ domain := inter_subset_left
  have hcU := mainLargest.2
  set K := (closedBall (0 : E 2) innerRad ∩ closure domain) ∩ uMax ⁻¹' Iic κ with hK
  have hKc : IsClosed K :=
    (hcU.mono inter_subset_right).preimage_isClosed_of_isClosed
      (isClosed_closedBall.inter isClosed_closure) isClosed_Iic
  have hKW : K ⊆ W := by
    rintro x ⟨⟨hb, hcl⟩, hle⟩
    simp only [mem_preimage, mem_Iic] at hle
    rw [mem_closedBall, dist_zero_right] at hb
    have hlt : ‖x‖ < innerRad := by
      refine lt_of_le_of_ne hb fun he ↦ ?_
      have := hδle x ⟨by rw [mem_sphere, dist_zero_right, he], hcl⟩
      linarith
    have hxb : x ∈ ball (0 : E 2) innerRad := by rw [mem_ball, dist_zero_right]; exact hlt
    refine ⟨?_, hxb⟩
    by_contra hxU
    have hfr : x ∈ frontier domain := ⟨hcl, by rwa [isOpen_domain.interior_eq]⟩
    have := cst_le_perronLargest_of_frontier hfr (by linarith [normSq_lt_of_mem_ball hxb])
    linarith
  have hgt : ∀ y ∈ W, y ∉ K → κ < uMax y := by
    intro y hy hyK
    by_contra hle
    push Not at hle
    exact hyK ⟨⟨ball_subset_closedBall hy.2, subset_closure hy.1⟩, hle⟩
  let : DecidablePred (· ∈ W) := fun _ ↦ Classical.propDecidable _
  set V := W.piecewise (fun x ↦ max (uMax x) κ) uMax with hV
  have hVsub : IsViscSub domain (fun _ ↦ 1) V :=
    isViscSub_piecewise isOpen_domain hWo hWU hKc hKW mainLargest.1.2
      ((mainLargest.1.2.mono hWo hWU).max_const hWo hκ0)
      fun y hy ↦ max_eq_left (hgt y hy.1 hy.2).le
  have hVcont : ContinuousOn V (closure domain) := by
    intro x hx
    by_cases hxW : x ∈ W
    · have heq : V =ᶠ[𝓝[closure domain] x] fun y ↦ max (uMax y) κ := by
        filter_upwards [nhdsWithin_le_nhds (hWo.mem_nhds hxW)] with y hy
        exact piecewise_eq_of_mem _ _ _ hy
      exact ((hcU x hx).sup continuousWithinAt_const).congr_of_eventuallyEq heq
        (piecewise_eq_of_mem _ _ _ hxW)
    · have hxK : x ∉ K := fun h ↦ hxW (hKW h)
      have heq : V =ᶠ[𝓝[closure domain] x] uMax := by
        filter_upwards [nhdsWithin_le_nhds (hKc.isOpen_compl.mem_nhds hxK)] with y hy
        by_cases hyW : y ∈ W
        · rw [hV, piecewise_eq_of_mem _ _ _ hyW]
          exact max_eq_left (hgt y hyW hy).le
        · exact piecewise_eq_of_notMem _ _ _ hyW
      exact (hcU x hx).congr_of_eventuallyEq heq (piecewise_eq_of_notMem _ _ _ hxW)
  have hVle : ∀ x ∈ closure domain, V x ≤ max (gSuper x) 0 := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [hV, piecewise_eq_of_mem _ _ _ hxW]
      refine max_le (perronLargest_le hx) ?_
      rw [gSuper_eq_cst (normSq_lt_of_mem_ball hxW.2)]
      exact hκc.le.trans (le_max_left _ _)
    · rw [hV, piecewise_eq_of_notMem _ _ _ hxW]; exact perronLargest_le hx
  have hVmem : V ∈ perronSubClass domain (fun _ ↦ 1) gSuper := ⟨hVcont, hVsub, hVle⟩
  refine ⟨κ, hκ0, fun x hx ↦ ?_⟩
  have := le_perronLargest hVmem (subset_closure hx.1)
  rw [hV, piecewise_eq_of_mem _ _ _ hx] at this
  exact (le_max_right _ _).trans this

/-! ### `u_min ≠ u_max` -/

theorem ball_three_subset : ball (0 : E 2) 3 ⊆ domain ∩ ball (0 : E 2) innerRad := by
  intro x hx
  rw [mem_ball, dist_zero_right] at hx
  refine ⟨?_, by rw [mem_ball, dist_zero_right]; linarith [innerRad_bounds.1]⟩
  rw [mem_domain_iff]
  refine ⟨by unfold outerRad; linarith, fun k ↦ holeRad_lt_norm_sub_cen_of_lt' _ ?_⟩
  unfold holeRad; linarith [ringRad_bounds.1]

/-- `u_min = 0` on `B₃(0)`. -/
theorem perronSmallest_eq_zero_of_mem_ball {x : E 2} (hx : x ∈ ball (0 : E 2) 3) : uMin x = 0 := by
  have hU := (ball_three_subset hx).1
  rw [mem_ball, dist_zero_right] at hx
  have h0 : ‖x - 0‖ ^ 2 ≤ layerRad ^ 2 := by
    rw [sub_zero]; nlinarith [layerRad_sq_bounds.1, norm_nonneg x]
  rw [perronSmallest_eq_vSup_near hU h0, vSup_eq, max_hLayer_eq_zero h0, add_zero, wSum_eq_zero]
  intro j
  have := norm_sub_norm_le (cen ((j : ℕ) : ℤ)) x
  rw [norm_cen, norm_sub_rev] at this
  have h1 : 1 / 10 ≤ ‖x - cen ((j : ℕ) : ℤ)‖ := by linarith [ringRad_bounds.1]
  nlinarith

/-- **`u_min ≠ u_max` on a set of positive measure.** -/
theorem not_uMin_ae_eq_uMax : ¬ (uMin =ᵐ[volume.restrict domain] uMax) := by
  intro h
  obtain ⟨κ, hκ, hle⟩ := uMax_pos_of_mem_inner
  have h' : ∀ᵐ x ∂(volume.restrict (ball (0 : E 2) 3)), uMin x = uMax x :=
    ae_restrict_of_ae_restrict_of_subset (fun x hx ↦ (ball_three_subset hx).1) h
  have hfalse : ∀ᵐ x ∂(volume.restrict (ball (0 : E 2) 3)), False := by
    filter_upwards [h', ae_restrict_mem measurableSet_ball] with x hx hxb
    rw [perronSmallest_eq_zero_of_mem_ball hxb] at hx
    have := hle x (ball_three_subset hxb)
    linarith
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at hfalse
  exact (measure_ball_pos volume (0 : E 2) (by norm_num : (0 : ℝ) < 3)).ne' hfalse

/-! ### Nontriviality of `u_max` -/

/-- A point in the dip of `gSuper` (`|x| = 3.7`). -/
def dipPt : E 2 := pol (37 / 10) 0

theorem norm_dipPt : ‖dipPt‖ = 37 / 10 := norm_pol (by norm_num) _

theorem dipPt_mem_domain : dipPt ∈ domain := by
  rw [mem_domain_iff, norm_dipPt]
  refine ⟨by norm_num [outerRad], fun k ↦ holeRad_lt_norm_sub_cen_of_lt _ ?_⟩
  rw [norm_dipPt]; unfold holeRad; linarith [ringRad_bounds.2]

/-- **`u_max` vanishes in the dip of `gSuper`.** -/
theorem perronLargest_dip : uMax dipPt = 0 := by
  have hx := subset_closure dipPt_mem_domain
  refine le_antisymm ((perronLargest_le hx).trans (le_of_eq ?_)) (perronLargest_nonneg hx)
  have h0 : ‖dipPt - 0‖ ^ 2 = 13.69 := by rw [sub_zero, norm_dipPt]; norm_num
  rw [gSuper, (sIn_floor (by rw [h0]; norm_num)).1, (sOut_floor (by rw [h0]; norm_num)).1]
  norm_num

theorem exists_perronLargest_pos : ∃ x ∈ domain, 0 < uMax x := by
  obtain ⟨x, hx, hpos⟩ := exists_perronSmallest_pos
  exact ⟨x, hx, hpos.trans_le (perronSmallest_le_perronLargest (subset_closure hx))⟩

theorem exists_perronLargest_eq_zero : ∃ x ∈ domain, uMax x = 0 :=
  ⟨dipPt, dipPt_mem_domain, perronLargest_dip⟩

/-- **The free boundary of `u_max` is nonempty.** -/
theorem freeBoundary_perronLargest_nonempty : (freeBoundary uMax domain).Nonempty := by
  obtain ⟨x, hx, hpos⟩ := exists_perronLargest_pos
  exact freeBoundary_nonempty isOpen_domain isConnected_domain.isPreconnected mainLargest.1.1.1
    hx hpos dipPt_mem_domain perronLargest_dip

end Necklace

end PerronVariational

end
