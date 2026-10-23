/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
public import PerronVariational.Basic.BV
import PerronVariational.Foundations.IVSolution
import PerronVariational.Foundations.IVSigmaH
import InnerVariational.Kernel.BV
import GMTFoundations.Sobolev.Lipschitz
import GMTFoundations.Perimeter.Mollify
import GMTFoundations.Perimeter.BlowUpScaling
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The perimeter bound for inner variational solutions ([Lemma 2.13](#AFS:l.perimeter-bound))

[Lemma 2.13](#AFS:l.perimeter-bound) (`l.perimeter-bound`) of F. Abedin, W. M. Feldman, K.
Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*:
if `(u, χ)` is an inner variational solution in `B_{2r}` with
`‖∇u‖_{L^∞(B_{2r})} = L`, then `χ ∈ BV(B_r)` with `∫_{B_r} |∇χ| ≤ C(L + r‖∇Q²‖_∞) r^{d-1}`.
The paper calls it a small modification of Kriventsov–Weiss, Lemma 3.3.

The estimate is proved in the dependency bernoulli-rectifiability v0.4.2 (Lake package
`inner_variational`), for Lipschitz coefficients `0 < c ≤ Q`:
`InnerVariational.IsVariationalSolutionQ.chi_divergence_bound`,
`|∫ χ div ξ| ≤ 2^{d+1} |B_1| L² sup|ξ| ρ^{d-1} / c²` for Lipschitz fields `ξ` supported in
`B_{3ρ/2}(x)`, when `B̄_{2ρ}(x)` lies in the domain. Its proof tests the inner variation with
`F_k(u) ξ` for smooth steps `F_k`, and replaces `ξ` by `Q⁻² ξ`; so the constant has the form
`C(d) L² / c²` rather than the paper's `C (L + r ‖∇Q²‖_∞)`. Either form gives the local uniform
perimeter bounds used in [Lemma 2.14](#AFS:l.inner-compactness-stability). The bridge from
[Def 2.11](#AFS:d.stationary-inner) (`IsInnerVarSolution`) is
`Foundations.isVariationalSolutionQ_of_isInnerVarSolution`.

## Main results

* `InnerVarCompactness.sub_le_of_nonneg_of_norm_fderiv_le`: a pointwise gradient bound on the
  positivity set gives a Lipschitz bound (used for `‖∇u‖_{L^∞} = L`; no Rademacher theorem).
* `PerimeterBound.perimeter_bound`: **[Lemma 2.13](#AFS:l.perimeter-bound)**, with the constant
  `2^{d+1} |B_1| L² r^{d-1} / c²`.
* `PerimeterBound.exists_totalVariationOn_le`: the uniform local form for a family with locally
  uniform Lipschitz bounds, by a finite cover and a smooth partition of unity (as in
  `GMTFoundations.bound_of_local`). This is the perimeter control of
  [Lemma 2.14](#AFS:l.inner-compactness-stability).
-/

open Set Filter Topology MeasureTheory Metric Function
open scoped Gradient ENNReal NNReal Manifold ContDiff

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

namespace InnerVarCompactness

/-! ### Step 1: Lipschitz bounds from gradient bounds on the positivity set -/

/-- **Lipschitz bound from the gradient on the positivity set.** Let `u ≥ 0` be continuous on the
convex set `s`, differentiable at every point of `s` where `u > 0`, with `‖Du‖ ≤ L` there. Then
`u x - u y ≤ L ‖x - y‖` for `x, y ∈ s`. (Along the segment from `x ∈ {u > 0}` towards `y`, apply
the mean value inequality up to the first zero of `u`, or up to `y` if there is none.) -/
theorem sub_le_of_nonneg_of_norm_fderiv_le {s : Set (E d)} (hs : Convex ℝ s) {u : E d → ℝ}
    (hc : ContinuousOn u s) (h0 : ∀ x ∈ s, 0 ≤ u x) {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x ∈ s, 0 < u x → DifferentiableAt ℝ u x ∧ ‖fderiv ℝ u x‖ ≤ L) {x y : E d}
    (hx : x ∈ s) (hy : y ∈ s) : u x - u y ≤ L * ‖x - y‖ := by
  have hLxy : 0 ≤ L * ‖x - y‖ := mul_nonneg hL (norm_nonneg _)
  rcases (h0 x hx).eq_or_lt with hx0 | hxpos
  · rw [← hx0]; linarith [h0 y hy]
  set γ : ℝ → E d := fun t ↦ x + t • (y - x) with hγdef
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ s := fun t ht ↦ hs.add_smul_sub_mem hx hy ht
  have hγc : Continuous γ := by fun_prop
  set f : ℝ → ℝ := fun t ↦ u (γ t) with hfdef
  have hfc : ContinuousOn f (Icc 0 1) := hc.comp hγc.continuousOn fun t ht ↦ hγ t ht
  have hf0 : f 0 = u x := by simp [f, γ]
  have hf1 : f 1 = u y := by simp [f, γ]
  have hyx : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
  -- the mean value inequality on `[0, b]` if `f > 0` on `[0, b)`
  have key : ∀ b ∈ Icc (0 : ℝ) 1, (∀ t ∈ Ico 0 b, 0 < f t) →
      |f b - f 0| ≤ L * ‖x - y‖ * b := by
    intro b hb hpos
    have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment (f := f)
      (f' := fun t ↦ fderiv ℝ u (γ t) (y - x)) (C := L * ‖x - y‖)
      (hfc.mono (Icc_subset_Icc le_rfl hb.2)) ?_ ?_ b (right_mem_Icc.2 hb.1)
    · simpa [Real.norm_eq_abs] using hmv
    · intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans hb.2⟩
      have hdiff := (hd _ (hγ t htI) (hpos t ht)).1
      have hγd : HasDerivAt γ (y - x) t := by
        convert ((hasDerivAt_id t).smul_const (y - x)).const_add x using 1
        · rfl
        simp
      exact (hdiff.hasFDerivAt.comp_hasDerivAt t hγd).hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans hb.2⟩
      have hbd := (hd _ (hγ t htI) (hpos t ht)).2
      rw [← hyx]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hbd (norm_nonneg _))
  by_cases hT : ∃ t ∈ Icc (0 : ℝ) 1, f t = 0
  · -- the first zero `t₀` of `f`
    set T := Icc (0 : ℝ) 1 ∩ f ⁻¹' {0} with hTdef
    have hTne : T.Nonempty := by
      obtain ⟨t, ht, hft⟩ := hT
      exact ⟨t, ht, hft⟩
    have hTc : IsClosed T := hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hTb : BddBelow T := ⟨0, fun t ht ↦ ht.1.1⟩
    set t₀ := sInf T
    have ht₀ : t₀ ∈ T := hTc.csInf_mem hTne hTb
    have hpos : ∀ t ∈ Ico 0 t₀, 0 < f t := fun t ht ↦ by
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans ht₀.1.2⟩
      rcases (h0 _ (hγ t htI)).eq_or_lt with h | h
      · exact absurd (csInf_le hTb ⟨htI, h.symm⟩) (not_le.2 ht.2)
      · exact h
    have hk := key t₀ ht₀.1 hpos
    have hft₀ : f t₀ = 0 := ht₀.2
    rw [hft₀, hf0, zero_sub, abs_neg, abs_of_pos hxpos] at hk
    have : L * ‖x - y‖ * t₀ ≤ L * ‖x - y‖ := mul_le_of_le_one_right hLxy ht₀.1.2
    linarith [h0 y hy]
  · push Not at hT
    have hk := key 1 (right_mem_Icc.2 zero_le_one) fun t ht ↦
      lt_of_le_of_ne (h0 _ (hγ t ⟨ht.1, ht.2.le⟩)) (hT t ⟨ht.1, ht.2.le⟩).symm
    rw [hf0, hf1, mul_one] at hk
    linarith [neg_abs_le (u y - u x)]

/-- `|u x - u y| ≤ L ‖x - y‖` under the hypotheses of `sub_le_of_nonneg_of_norm_fderiv_le`. -/
theorem abs_sub_le_of_nonneg_of_norm_fderiv_le {s : Set (E d)} (hs : Convex ℝ s) {u : E d → ℝ}
    (hc : ContinuousOn u s) (h0 : ∀ x ∈ s, 0 ≤ u x) {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x ∈ s, 0 < u x → DifferentiableAt ℝ u x ∧ ‖fderiv ℝ u x‖ ≤ L) {x y : E d}
    (hx : x ∈ s) (hy : y ∈ s) : |u x - u y| ≤ L * ‖x - y‖ := by
  refine abs_le.2 ⟨?_, sub_le_of_nonneg_of_norm_fderiv_le hs hc h0 hL hd hx hy⟩
  have := sub_le_of_nonneg_of_norm_fderiv_le hs hc h0 hL hd hy hx
  rw [norm_sub_rev] at this
  linarith

end InnerVarCompactness

namespace PerimeterBound

/-- An inner variational solution with `‖∇u‖ ≤ L` on a convex set `s ⊆ U` is `L`-Lipschitz on
`s` (`u` is `C²` on the open set `{u > 0}`;
`InnerVarCompactness.abs_sub_le_of_nonneg_of_norm_fderiv_le`). -/
theorem lipschitzOnWith_of_norm_gradient_le {U s : Set (E d)} (hU : IsOpen U) {Q u χ : E d → ℝ}
    (h : IsInnerVarSolution U Q u χ) (hs : Convex ℝ s) (hsU : s ⊆ U) {L : ℝ}
    (hL : ∀ y ∈ s, ‖∇ u y‖ ≤ L) (hne : s.Nonempty) :
    LipschitzOnWith (Real.toNNReal L) u s := by
  obtain ⟨y₀, hy₀⟩ := hne
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL y₀ hy₀)
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL0]
  refine InnerVarCompactness.abs_sub_le_of_nonneg_of_norm_fderiv_le hs
    (h.locLip.continuousOn.mono hsU) (fun z hz ↦ h.nonneg z (hsU hz)) hL0
    (fun z hz hpos ↦ ⟨?_, ?_⟩) ha hb
  · have hzW : z ∈ posSet u U := ⟨hsU hz, hpos⟩
    have hO : IsOpen (posSet u U) := h.locLip.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
    exact (h.c2.contDiffAt (hO.mem_nhds hzW)).differentiableAt (by norm_num)
  · rw [← GMTFoundations.norm_gradient_eq_norm_fderiv]
    exact hL z hz

/-- **The divergence estimate of Kriventsov–Weiss, Lemma 3.3**, for
[Def 2.11](#AFS:d.stationary-inner) (from bernoulli-rectifiability,
`IsVariationalSolutionQ.chi_divergence_bound`). Let `(u, χ)` be an inner variational solution in
`U`, with `Q` Lipschitz on `U` and `0 < c ≤ Q ≤ C` there, and let `u` be
`L`-Lipschitz on a ball `B_R(x) ⊆ U` with `2ρ < R`. Then for every Lipschitz field `ξ` supported in
`B_{3ρ/2}(x)` with `|ξ| ≤ M`, `|∫ χ div ξ| ≤ 2^{d+1} |B_1| L² M ρ^{d-1} / c²`. -/
theorem abs_integral_chi_mul_divergence_le (hd : 2 ≤ d) {U : Set (E d)} {Q u χ : E d → ℝ}
    {K : ℝ≥0} (hQ : LipschitzOnWith K Q U) {c C : ℝ} (hc : 0 < c) (hcQ : ∀ y ∈ U, c ≤ Q y)
    (hQC : ∀ y ∈ U, Q y ≤ C) (h : IsInnerVarSolution U Q u χ) {x : E d} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : 2 * ρ < R) (hRU : ball x R ⊆ U) {L : ℝ≥0}
    (hL : LipschitzOnWith L u (ball x R)) {ξ : E d → E d}
    (hξ : GMTFoundations.IsLipTestField (ball x (3 * ρ / 2)) ξ) {M : ℝ} (hM : ∀ y, ‖ξ y‖ ≤ M) :
    |∫ y, χ y * divergence ξ y| ≤
      2 ^ (d + 1) * volume.real (ball (0 : E d) 1) * (L : ℝ) ^ 2 * M * ρ ^ (d - 1) / c ^ 2 := by
  have : NeZero d := ⟨by omega⟩
  have hIV := Foundations.isVariationalSolutionQ_of_isInnerVarSolution h isOpen_ball hRU hL
  have hQB := Foundations.qBounds_of_subset hRU hQ hc hcQ hQC
  exact hIV.chi_divergence_bound hQB hρ (closedBall_subset_ball hρR) hξ hM

/-- **[Lemma 2.13](#AFS:l.perimeter-bound) (perimeter bound).** Let `(u, χ)` be an inner variational
solution ([Def 2.11](#AFS:d.stationary-inner)) in `B_{2r}(x)`, with `Q` Lipschitz on `B_{2r}(x)` and
`0 < c ≤ Q ≤ C` there, and `‖∇u‖ ≤ L` on `B_{2r}(x)`. Then
`∫_{B_r(x)} |∇χ| ≤ 2^{d+1} |B_1| L² r^{d-1} / c²`; in particular `χ ∈ BV(B_r(x))`.

Difference from the paper: the paper's constant is `C (L + r ‖∇Q²‖_{L^∞(B_{2r})}) r^{d-1}`, with
`C` depending on the bounds of `Q`; the constant here, from the proof of Kriventsov–Weiss,
Lemma 3.3 in bernoulli-rectifiability, is `2^{d+1} |B_1| L² r^{d-1} / c²`. Both are uniform for
locally uniformly Lipschitz families, which is how [Lemma 2.14](#AFS:l.inner-compactness-stability)
uses the lemma. -/
theorem perimeter_bound (hd : 2 ≤ d) {Q u χ : E d → ℝ} {x : E d} {r : ℝ} (hr : 0 < r)
    {K : ℝ≥0} (hQ : LipschitzOnWith K Q (ball x (2 * r))) {c C : ℝ} (hc : 0 < c)
    (hcQ : ∀ y ∈ ball x (2 * r), c ≤ Q y) (hQC : ∀ y ∈ ball x (2 * r), Q y ≤ C)
    (h : IsInnerVarSolution (ball x (2 * r)) Q u χ) {L : ℝ}
    (hL : ∀ y ∈ ball x (2 * r), ‖∇ u y‖ ≤ L) :
    totalVariationOn (ball x r) χ ≤
      ENNReal.ofReal (2 ^ (d + 1) * volume.real (ball (0 : E d) 1) * L ^ 2 * r ^ (d - 1) /
        c ^ 2) := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL x (mem_ball_self (by linarith)))
  have hLip := lipschitzOnWith_of_norm_gradient_le isOpen_ball h (convex_ball x (2 * r))
    subset_rfl hL ⟨x, mem_ball_self (by linarith)⟩
  unfold totalVariationOn GMTFoundations.weightedTV
  refine iSup₂_le fun ψ hψ ↦ ENNReal.ofReal_le_ofReal ?_
  rw [GMTFoundations.setIntegral_mul_divergence_eq_integral χ hψ.2.2.1]
  have hξ : GMTFoundations.IsLipTestField (ball x (3 * (5 * r / 6) / 2)) ψ :=
    ⟨hψ.1.lipschitzWith_of_hasCompactSupport hψ.2.1 one_ne_zero, hψ.2.1,
      hψ.2.2.1.trans (ball_subset_ball (by linarith))⟩
  have hb := abs_integral_chi_mul_divergence_le hd hQ hc hcQ hQC h (ρ := 5 * r / 6)
    (by positivity) (by linarith) subset_rfl hLip hξ (M := 1) (fun y ↦ by simpa using hψ.2.2.2 y)
  rw [Real.coe_toNNReal _ hL0] at hb
  refine (le_abs_self _).trans (hb.trans ?_)
  have hρr : (5 * r / 6) ^ (d - 1) ≤ r ^ (d - 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hB : 0 ≤ volume.real (ball (0 : E d) 1) := measureReal_nonneg
  rw [mul_one]
  gcongr

/-- Local bounds on balls, uniform in a parameter `i`, give a bound on each compact subset of `U`,
uniform in `i` (finite cover and a smooth partition of unity). This is
`GMTFoundations.bound_of_local` for a family of sets `E i`, with the same proof. -/
theorem bound_of_local_family {ι : Type*} {U : Set (E d)} {S : ι → Set (E d)}
    (h : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ C : ℝ, ∀ i, ∀ φ : E d → E d,
      GMTFoundations.IsSmoothTestField (ball x r) φ →
        |∫ y in S i, divergence φ y| ≤ C * ⨆ y, ‖φ y‖)
    (K : Set (E d)) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ i, ∀ φ, GMTFoundations.IsSmoothTestField U φ → tsupport φ ⊆ K →
      ∀ M, (∀ x, ‖φ x‖ ≤ M) → |∫ x in S i, divergence φ x| ≤ C * M := by
  classical
  choose! r hr hrU C hC using h
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K ↦ ball (x : E d) (r x))
    (fun _ ↦ isOpen_ball) (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr x (hKU hx))⟩)
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E d) hK.isClosed
    (fun i : t ↦ ball ((i : K) : E d) (r i)) (fun _ ↦ isOpen_ball)
    (by rw [iUnion_subtype]; exact ht)
  refine ⟨∑ i : t, max (C ((i : K) : E d)) 0, fun j φ hφ hφK M hM ↦ ?_⟩
  have hfs : ∀ i : t, ContDiff ℝ ∞ (f i) := fun i ↦ contMDiff_iff_contDiff.1 (f i).contMDiff
  have hterm : ∀ i : t, GMTFoundations.IsSmoothTestField (ball ((i : K) : E d) (r i))
      (fun x ↦ f i x • φ x) := by
    intro i
    refine ⟨(hfs i).smul hφ.1, ?_, ?_⟩
    · exact HasCompactSupport.smul_left (f := fun x ↦ f i x) hφ.2.1
    · exact (tsupport_smul_subset_left (fun x ↦ f i x) φ).trans (hf i)
  have hdecomp : φ = ∑ i : t, fun x ↦ f i x • φ x := by
    funext x
    rw [Finset.sum_apply, ← Finset.sum_smul]
    by_cases hx : x ∈ K
    · rw [← finsum_eq_sum_of_fintype, f.sum_eq_one hx, one_smul]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hφK h')
      simp [this]
  have hU' : ∀ i : t, GMTFoundations.IsSmoothTestField U (fun x ↦ f i x • φ x) := fun i ↦
    ⟨(hterm i).1, (hterm i).2.1, (hterm i).2.2.trans (hrU _ (hKU (i : K).2))⟩
  rw [hdecomp, GMTFoundations.integral_divergence_finsetSum _ fun i _ ↦ hU' i]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ GMTFoundations.abs_le_of_le_mul_iSup
    (hC _ (hKU (i : K).2) j _ (hterm i)) fun x ↦ ?_
  rw [norm_smul, Real.norm_of_nonneg (f.nonneg i x)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (f.le_one i x)).trans (hM x)

/-- For `{0, 1}`-valued `χ` on `U` and a field supported in `U`,
`∫_{U ∩ {χ = 1}} div φ = ∫ χ div φ`. -/
theorem setIntegral_divergence_eq_integral_chi_mul {U : Set (E d)} (hU : MeasurableSet U)
    {χ : E d → ℝ} (hχ : Measurable χ) (h01 : ∀ x ∈ U, χ x = 0 ∨ χ x = 1) {φ : E d → E d}
    (hφ : tsupport φ ⊆ U) :
    ∫ y in U ∩ {y | χ y = 1}, divergence φ y = ∫ y, χ y * divergence φ y := by
  rw [← integral_indicator (hU.inter (measurableSet_eq_fun hχ measurable_const))]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  change (U ∩ {y | χ y = 1}).indicator (divergence φ) y = χ y * divergence φ y
  by_cases hy : y ∈ U
  · rcases h01 y hy with h0 | h1
    · rw [indicator_of_notMem (fun h' ↦ by rw [h'.2] at h0; exact zero_ne_one h0.symm), h0,
        zero_mul]
    · rw [indicator_of_mem (show y ∈ U ∩ {y | χ y = 1} from ⟨hy, h1⟩), h1, one_mul]
  · rw [indicator_of_notMem (fun h' ↦ hy h'.1),
      image_eq_zero_of_notMem_tsupport
        (fun h' ↦ hy (hφ (GMTFoundations.tsupport_divergence_subset φ h'))),
      mul_zero]

/-- **Uniform local perimeter bounds** ([Lemma 2.13](#AFS:l.perimeter-bound), used in
[Lemma 2.14](#AFS:l.inner-compactness-stability)). Let `(u_k, χ_k)` be inner variational solutions
([Def 2.11](#AFS:d.stationary-inner)) in `U`, with `Q` Lipschitz on `U` and `0 < c ≤ Q ≤ C` there,
and let the `u_k` be locally uniformly Lipschitz: every `y ∈ U` has a ball `B_ε(y) ⊆ U` on which all
`u_k` are `L`-Lipschitz. Then for every open `V ⊂⊂ U`, `sup_k ∫_V |∇χ_k| < ∞`. -/
theorem exists_totalVariationOn_le (hd : 2 ≤ d) {U : Set (E d)} (hU : IsOpen U)
    {Q : E d → ℝ} {K : ℝ≥0} (hQ : LipschitzOnWith K Q U) {c C : ℝ} (hc : 0 < c)
    (hcQ : ∀ y ∈ U, c ≤ Q y) (hQC : ∀ y ∈ U, Q y ≤ C) {u χ : ℕ → E d → ℝ}
    (h : ∀ k, IsInnerVarSolution U Q (u k) (χ k))
    (hULL : ∀ y ∈ U, ∃ ε > 0, ball y ε ⊆ U ∧ ∃ L : ℝ≥0, ∀ k, LipschitzOnWith L (u k) (ball y ε))
    (V : Set (E d)) (hV : IsOpen V) (hVU : CompactlyContained V U) :
    ∃ P : ℝ, ∀ k, totalVariationOn V (χ k) ≤ ENNReal.ofReal P := by
  set S : ℕ → Set (E d) := fun k ↦ U ∩ {y | χ k y = 1} with hSdef
  have hS : ∀ k, MeasurableSet (S k) := fun k ↦
    hU.measurableSet.inter (measurableSet_eq_fun (h k).meas measurable_const)
  -- local bounds on balls, uniform in `k`
  have hloc : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ B : ℝ, ∀ k, ∀ φ : E d → E d,
      GMTFoundations.IsSmoothTestField (ball x r) φ →
        |∫ y in S k, divergence φ y| ≤ B * ⨆ y, ‖φ y‖ := by
    intro x hx
    obtain ⟨ε, hε, hεU, L, hL⟩ := hULL x hx
    refine ⟨3 * (ε / 3) / 2, by positivity, (ball_subset_ball (by linarith)).trans hεU,
      2 ^ (d + 1) * volume.real (ball (0 : E d) 1) * (L : ℝ) ^ 2 * (ε / 3) ^ (d - 1) / c ^ 2,
      fun k φ hφ ↦ ?_⟩
    obtain ⟨D, hD⟩ := hφ.isLipTestField.1
    have hM : ∀ y, ‖φ y‖ ≤ ⨆ y, ‖φ y‖ := fun y ↦
      le_ciSup (hD.continuous.norm.bddAbove_range_of_hasCompactSupport hφ.2.1.norm) y
    have hb := abs_integral_chi_mul_divergence_le hd hQ hc hcQ hQC (h k) (R := ε)
      (ρ := ε / 3) (by positivity) (by linarith) hεU (hL k) hφ.isLipTestField hM
    rw [hSdef, setIntegral_divergence_eq_integral_chi_mul hU.measurableSet (h k).meas
      (h k).zero_one (hφ.2.2.trans ((ball_subset_ball (by linarith)).trans hεU))]
    refine hb.trans_eq ?_
    ring
  obtain ⟨B, hB⟩ := bound_of_local_family hloc (closure V) hVU.1 hVU.2
  refine ⟨B, fun k ↦ ?_⟩
  -- `χ_k = 1_{S_k}` on `V`
  have heq : EqOn (χ k) ((S k).indicator 1) V := fun y hy ↦ by
    have hyU : y ∈ U := hVU.2 (subset_closure hy)
    rcases (h k).zero_one y hyU with h0 | h1
    · rw [h0, indicator_of_notMem (fun h' ↦ by rw [h'.2] at h0; exact zero_ne_one h0.symm)]
    · rw [h1, indicator_of_mem (show y ∈ S k from ⟨hyU, h1⟩), Pi.one_apply]
  rw [GMTFoundations.totalVariationOn_congr_of_eqOn hV.measurableSet heq,
    GMTFoundations.totalVariationOn_indicator_eq_iSup hV (hS k)]
  refine iSup₂_le fun φ hφ ↦ iSup_le fun hφ1 ↦ ENNReal.ofReal_le_ofReal ?_
  have hφU : GMTFoundations.IsSmoothTestField U φ :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans fun y hy ↦ hVU.2 (subset_closure hy)⟩
  have := hB k φ hφU (hφ.2.2.trans subset_closure) 1 hφ1
  rw [mul_one] at this
  exact (le_abs_self _).trans this

end PerimeterBound

end PerronVariational

end
