/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.DirectionalStable.Blowup
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Semilinear.Calculus
import PerronVariational.Stationary.TwoPlane.Basic
import PerronVariational.Stationary.ViscosityLocal
import PerronVariational.Stationary.ViscosityStability

/-!
# Corollary 1.2: classical points and blow-ups of supersolutions

Part of **Corollary 1.2** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: the set of
classical points is open
(`isOpen_setOf_isClassicalNear`), blow-ups of viscosity supersolutions are supersolutions
(`isViscSuper_blowup`, `isViscSuper_of_isBlowupLimit`), and two-plane functions with slope
below `Q` fail the supersolution test (`not_isViscSuper_twoPlane`, `le_of_isBlowupLimit_twoPlane`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian NNReal RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Corollary2D

variable {d : ℕ}

/-! ### Part 1: openness of the set of classical points -/

/-- A `C^{1,γ}` graph in `B_r(x₀)` is a `C^{1,γ}` graph (in the same direction) in every ball
`B_s(y) ⊆ B_r(x₀)`, after re-centring the graph at `y`. -/
theorem IsC1GammaHypersurfaceNear.mono {S : Set (E d)} {x₀ y : E d} {r s : ℝ}
    (h : IsC1GammaHypersurfaceNear S x₀ r) (hs : ball y s ⊆ ball x₀ r) :
    IsC1GammaHypersurfaceNear S y s := by
  obtain ⟨γ, hγ0, hγ1, e, he, f, C, hf, hH, hS⟩ := h
  set c : E d := (y - x₀) - ⟪y - x₀, e⟫ • e with hc
  set k : ℝ := ⟪y - x₀, e⟫ with hk
  refine ⟨γ, hγ0, hγ1, e, he, fun w ↦ f (w + c) - k, C, ?_, ?_, ?_⟩
  · exact (hf.comp (contDiff_id.add contDiff_const)).sub contDiff_const
  · have hfd : fderiv ℝ (fun w ↦ f (w + c) - k) = fun w ↦ fderiv ℝ f (w + c) := by
      funext w
      rw [fderiv_sub_const, fderiv_comp_add_right]
    rw [hfd]
    intro a b
    simpa using hH (a + c) (b + c)
  · ext z
    simp only [mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hzS, hz⟩
      have hz' : z ∈ S ∩ ball x₀ r := ⟨hzS, hs hz⟩
      rw [hS] at hz'
      refine ⟨hz, ?_⟩
      have h1 := hz'.2
      have hsplit : z - y - ⟪z - y, e⟫ • e + c = z - x₀ - ⟪z - x₀, e⟫ • e := by
        rw [hc]
        have : z - x₀ = (z - y) + (y - x₀) := by abel
        rw [this, inner_add_left, add_smul]
        abel
      rw [hsplit, ← h1]
      have : z - x₀ = (z - y) + (y - x₀) := by abel
      rw [this, inner_add_left]
      ring
    · rintro ⟨hz, h1⟩
      have hzr : z ∈ ball x₀ r := hs hz
      have hmem : z ∈ {y ∈ ball x₀ r | ⟪y - x₀, e⟫ = f (y - x₀ - ⟪y - x₀, e⟫ • e)} := by
        refine ⟨hzr, ?_⟩
        have hsplit : z - x₀ - ⟪z - x₀, e⟫ • e = z - y - ⟪z - y, e⟫ • e + c := by
          rw [hc]
          have : z - x₀ = (z - y) + (y - x₀) := by abel
          rw [this, inner_add_left, add_smul]
          abel
        rw [hsplit]
        have : z - x₀ = (z - y) + (y - x₀) := by abel
        rw [this, inner_add_left]
        linarith [h1, hk]
      rw [← hS] at hmem
      exact ⟨hmem.1, hz⟩

/-- If `u` is a classical solution near `x₀`, it is a classical solution near every point of a
neighbourhood of `x₀`. -/
theorem IsClassicalNear.eventually {U : Set (E d)} {Q u : E d → ℝ} {x₀ : E d}
    (h : IsClassicalNear U Q u x₀) : ∀ᶠ y in 𝓝 x₀, IsClassicalNear U Q u y := by
  obtain ⟨r, hr, hU, hS, hc2, hΔ, G, hGc, hGe, hGQ⟩ := h
  filter_upwards [ball_mem_nhds x₀ hr] with y hy
  have hs : 0 < r - dist y x₀ := by rw [mem_ball] at hy; linarith
  have hsub : ball y (r - dist y x₀) ⊆ ball x₀ r := by
    intro z hz
    rw [mem_ball] at hz ⊢
    linarith [dist_triangle z y x₀]
  refine ⟨r - dist y x₀, hs, hsub.trans hU, IsC1GammaHypersurfaceNear.mono hS hsub,
    hc2.mono (inter_subset_inter_right _ hsub), fun z hz ↦ hΔ z ⟨hz.1, hsub hz.2⟩, G,
    hGc.mono (inter_subset_inter_right _ hsub), fun z hz ↦ hGe z ⟨hz.1, hsub hz.2⟩,
    fun z hz ↦ hGQ z ⟨hz.1, hsub hz.2⟩⟩

/-- The set of points near which `u` is classical is open. -/
theorem isOpen_setOf_isClassicalNear (U : Set (E d)) (Q u : E d → ℝ) :
    IsOpen {x | IsClassicalNear U Q u x} :=
  isOpen_iff_mem_nhds.2 fun _ hx ↦ IsClassicalNear.eventually hx

/-! ### Part 2: blow-ups of supersolutions and the supersolution test for two-plane functions -/

section SuperBlowup

/-- Enlarging `Q` weakens the viscosity supersolution condition. -/
theorem _root_.PerronVariational.IsViscSuper.mono_Q {U : Set (E d)} {Q Q' u : E d → ℝ}
    (hu : IsViscSuper U Q u)
    (hQ : ∀ x ∈ U, Q x ≤ Q' x) : IsViscSuper U Q' u := by
  refine ⟨hu.1, hu.2.1, fun φ hφ x hx h ↦ ?_⟩
  rcases hu.2.2 φ hφ x hx h with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h2, h3.trans (hQ x hx)⟩

/-- **Scaling of viscosity supersolutions.** The blow-up `u_{x₀,r}(y) = r⁻¹ u(x₀ + r y)` of a
viscosity supersolution of (1.1) in `U` is a viscosity supersolution in `U_{x₀,r}` with the
rescaled coefficient `Q(x₀ + r ·)`. -/
theorem isViscSuper_blowup {U : Set (E d)} {Q u : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSuper U Q u) (x₀ : E d) {r : ℝ} (hr : 0 < r) :
    IsViscSuper (DirectionalStable.blowupDomain U x₀ r) (fun y ↦ Q (x₀ + r • y))
      (blowup u x₀ r) := by
  have hD : IsOpen (DirectionalStable.blowupDomain U x₀ r) :=
    DirectionalStable.isOpen_blowupDomain hU x₀ r
  have hA : Continuous fun y : E d ↦ x₀ + r • y := DirectionalStable.continuous_affine x₀ r
  refine ⟨?_, fun y hy ↦ div_nonneg (hu.2.1 _ hy) hr.le, fun φ hφ y hy htouch ↦ ?_⟩
  · intro y hy
    have : ContinuousWithinAt u U (x₀ + r • y) := hu.1 _ hy
    exact (ContinuousWithinAt.comp (g := u) (f := fun z ↦ x₀ + r • z) this
      hA.continuousWithinAt fun z hz ↦ hz).div_const r
  -- the rescaled test function
  set T : E d → E d := fun x ↦ r⁻¹ • (x - x₀) with hT
  set ψ : E d → ℝ := fun x ↦ r * φ (T x) with hψ
  have hTc : ContDiff ℝ ∞ T := (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hψs : ContDiff ℝ ∞ ψ := contDiff_const.mul (hφ.comp hTc)
  set x := x₀ + r • y with hx
  have hTx : T x = y := by simp [hT, hx, smul_smul, inv_mul_cancel₀ hr.ne']
  have hxU : x ∈ U := hy
  have hTcont : Continuous T := hTc.continuous
  have hψx : ψ x = u x := by
    simp only [hψ, hTx]
    rw [htouch.2.1]
    simp only [blowup, hx]
    field_simp
  have hev : ∀ᶠ z in 𝓝 x, ψ z ≤ u z := by
    have h1 := htouch.eventually_le_of_isOpen hD
    have h2 : Tendsto T (𝓝 x) (𝓝 y) := by
      rw [← hTx]; exact hTcont.continuousAt
    filter_upwards [h2.eventually h1] with z hz
    have hz' : x₀ + r • T z = z := by
      simp [hT, smul_smul, mul_inv_cancel₀ hr.ne']
    simp only [blowup, hz'] at hz
    simp only [hψ]
    rw [le_div_iff₀ hr] at hz
    linarith
  have htb : TouchesBelow ψ u U x :=
    ⟨hxU, hψx, by rw [hU.nhdsWithin_eq hxU]; exact hev⟩
  -- `φ` is the blow-up of `ψ`
  have hφψ : φ = blowup ψ x₀ r := by
    funext z
    simp only [blowup, hψ, hT, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    field_simp
  have hlap : Δ φ y = r * Δ ψ x := by
    rw [hφψ]
    exact DirectionalStable.laplacian_blowup hr.ne'
      (contDiff_two_of_smooth hψs).contDiffAt
  have hfd : fderiv ℝ ψ x = fderiv ℝ φ y := by
    have hTd : HasFDerivAt T (r⁻¹ • ContinuousLinearMap.id ℝ (E d)) x :=
      ((hasFDerivAt_id x).sub_const x₀).const_smul r⁻¹
    have hφd : HasFDerivAt φ (fderiv ℝ φ y) (T x) := by
      rw [hTx]
      exact (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
    have := (hφd.comp x hTd).const_mul r
    have e : ψ = fun z ↦ r * (φ ∘ T) z := rfl
    rw [e, this.fderiv]
    ext v
    simp [smul_smul, mul_inv_cancel₀ hr.ne']
  have hgrad : ∇ ψ x = ∇ φ y := by simp [gradient, hfd]
  rcases hu.2.2 ψ hψs x hxU htb with h1 | ⟨h2, h3⟩
  · left
    rw [hlap]
    exact mul_nonpos_of_nonneg_of_nonpos hr.le h1
  · right
    refine ⟨?_, by rw [← hgrad]; exact h3⟩
    have : r * φ y = 0 := by simpa [hψ, hTx] using h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hr.ne'
    · exact h

end SuperBlowup

section TwoPlaneTest

/-- The derivative of `y ↦ y · e`. -/
theorem fderiv_inner_const (e : E d) :
    fderiv ℝ (fun y : E d ↦ ⟪y, e⟫) = fun _ ↦ innerSL ℝ e := by
  funext x
  have h : (fun y : E d ↦ ⟪y, e⟫) = innerSL ℝ e := by
    ext y; simp [real_inner_comm]
  rw [h]
  exact (innerSL ℝ e).fderiv

/-- `Δ (y · e) = 0`. -/
theorem laplacian_inner_const (e x : E d) : Δ (fun y : E d ↦ ⟪y, e⟫) x = 0 := by
  rw [laplacian_eq_sum_fderiv_fderiv, fderiv_inner_const]
  simp

/-- **Supersolution test for two-plane functions** (proof sketch of Corollary 1.2: "for
`α > Q(x₀)`, `φ_α` is not a viscosity supersolution"). If `0 ≤ q < α` and `‖e‖ = 1`, then
`α |y · e|` is not a viscosity supersolution of (1.1) with constant coefficient `q` in any open
set containing `0`. The test function is `φ(y) = β (y · e) + (y · e)²` with `q < β < α`. -/
theorem not_isViscSuper_twoPlane {q α : ℝ} (hqα : q < α) (hq : 0 ≤ q) {e : E d} (he : ‖e‖ = 1)
    {W : Set (E d)} (hW : IsOpen W) (h0 : (0 : E d) ∈ W) {v : E d → ℝ}
    (hv : ∀ y, v y = α * |⟪y, e⟫|) : ¬ IsViscSuper W (fun _ ↦ q) v := by
  intro hsup
  set β := (α + q) / 2 with hβ
  set f : ℝ → ℝ := fun t ↦ β * t + t ^ 2 with hf
  set φ : E d → ℝ := fun y ↦ f ⟪y, e⟫ with hφ
  have hfs : ContDiff ℝ ∞ f := by rw [hf]; fun_prop
  have hℓ : ContDiff ℝ ∞ (fun y : E d ↦ ⟪y, e⟫) := contDiff_inner_const e
  have hφs : ContDiff ℝ ∞ φ := hfs.comp hℓ
  -- `φ` touches `v` from below at `0`
  have htouch : TouchesBelow φ v W 0 := by
    refine ⟨h0, by simp [hφ, hf, hv], ?_⟩
    rw [hW.nhdsWithin_eq h0]
    have hnhds : {y : E d | |⟪y, e⟫| < α - β} ∈ 𝓝 (0 : E d) := by
      refine (isOpen_lt (continuous_abs.comp (continuous_inner_const e))
        continuous_const).mem_nhds ?_
      change |⟪(0 : E d), e⟫| < α - β
      rw [inner_zero_left, abs_zero, hβ]
      linarith
    filter_upwards [hnhds] with y hy
    replace hy : |⟪y, e⟫| < α - β := hy
    rw [hv y]
    change β * ⟪y, e⟫ + ⟪y, e⟫ ^ 2 ≤ α * |⟪y, e⟫|
    set t := ⟪y, e⟫
    have h1 : β * t ≤ β * |t| := mul_le_mul_of_nonneg_left (le_abs_self t) (by rw [hβ]; linarith)
    have h2 : t ^ 2 ≤ (α - β) * |t| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg t]
    nlinarith
  have hderiv : deriv f = fun t ↦ β + 2 * t := by
    funext t; rw [hf]
    have : HasDerivAt (fun t : ℝ ↦ β * t + t ^ 2) (β + 2 * t) t := by
      convert ((hasDerivAt_id' t).const_mul β).add ((hasDerivAt_id' t).pow 2) using 1
      norm_num
    rw [this.deriv]
  have hderiv2 : deriv (deriv f) = fun _ ↦ 2 := by
    rw [hderiv]; funext t
    have : HasDerivAt (fun t : ℝ ↦ β + 2 * t) 2 t := by
      convert (hasDerivAt_const t β).add ((hasDerivAt_id' t).const_mul 2) using 1
      ring
    rw [this.deriv]
  have hgradℓ : ‖∇ (fun y : E d ↦ ⟪y, e⟫) 0‖ = 1 := by rw [gradient_inner_const, he]
  have hlap : Δ φ 0 = 2 := by
    have := laplacian_comp (f := f) (g := fun y : E d ↦ ⟪y, e⟫) (x := 0)
      (contDiff_two_of_smooth hfs).contDiffAt (contDiff_two_of_smooth hℓ).contDiffAt
    rw [this, hderiv2, hgradℓ, laplacian_inner_const]
    ring
  have hgrad : ‖∇ φ 0‖ = β := by
    rw [norm_gradient_eq_norm_fderiv]
    have hfd : HasDerivAt f (deriv f ⟪(0 : E d), e⟫) ⟪(0 : E d), e⟫ :=
      (hfs.differentiable (by simp)).differentiableAt.hasDerivAt
    have hℓd : HasFDerivAt (fun y : E d ↦ ⟪y, e⟫) (fderiv ℝ (fun y : E d ↦ ⟪y, e⟫) 0) 0 :=
      (hℓ.differentiable (by simp)).differentiableAt.hasFDerivAt
    have e' : φ = f ∘ fun y ↦ ⟪y, e⟫ := rfl
    rw [e', (hfd.comp_hasFDerivAt (0 : E d) hℓd).fderiv, norm_smul, ← norm_gradient_eq_norm_fderiv,
      hgradℓ, hderiv]
    simp only [inner_zero_left, mul_zero, add_zero, Real.norm_eq_abs, mul_one]
    exact abs_of_nonneg (by rw [hβ]; linarith)
  rcases hsup.2.2 φ hφs 0 h0 htouch with h | ⟨-, h⟩
  · rw [hlap] at h; norm_num at h
  · rw [hgrad, hβ] at h; linarith

end TwoPlaneTest

section BlowupSuper

/-- For `r` small, the blow-ups at `x₀ ∈ U` along `r → 0⁺` live on `B_1(0)`, with rescaled
coefficient `Q(x₀ + r ·) ≤ Q(x₀) + δ` there. -/
theorem eventually_blowup_ball {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ} {x₀ : E d}
    (hx₀ : x₀ ∈ U) (hQ : ContinuousAt Q x₀) {δ : ℝ} (hδ : 0 < δ) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ball (0 : E d) 1 ⊆ DirectionalStable.blowupDomain U x₀ (r n) ∧
      ∀ y ∈ ball (0 : E d) 1, Q (x₀ + r n • y) ≤ Q x₀ + δ := by
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.1
    ((show ∀ᶠ y in 𝓝 x₀, y ∈ U from hU.mem_nhds hx₀).and
      (hQ.eventually (Iio_mem_nhds (show Q x₀ < Q x₀ + δ by linarith))))
  filter_upwards [(tendsto_order.1 hr0).2 ρ hρ] with n hn
  have hmem : ∀ y ∈ ball (0 : E d) 1, dist (x₀ + r n • y) x₀ < ρ := by
    intro y hy
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hr n)]
    rw [mem_ball, dist_zero_right] at hy
    calc r n * ‖y‖ ≤ r n * 1 := mul_le_mul_of_nonneg_left hy.le (hr n).le
      _ < ρ := by linarith
  exact ⟨fun y hy ↦ (hρ' (hmem y hy)).1, fun y hy ↦ (hρ' (hmem y hy)).2.le⟩

/-- **Blow-up limits of supersolutions are supersolutions** (proof sketch of Corollary 1.2,
via Lemma 2.4): if `u` is a viscosity supersolution of (1.1) in `U`, `x₀ ∈ U` and `Q` is
continuous at `x₀`, every blow-up limit of `u` at `x₀` is a viscosity supersolution in `B_1(0)`
with constant coefficient `Q(x₀) + δ`, for every `δ > 0`. -/
theorem isViscSuper_of_isBlowupLimit {U : Set (E d)} (hU : IsOpen U) {Q u : E d → ℝ}
    (hu : IsViscSuper U Q u) {x₀ : E d} (hx₀ : x₀ ∈ U) (hQ : ContinuousAt Q x₀) {v : E d → ℝ}
    (hv : IsBlowupLimit u x₀ v) {δ : ℝ} (hδ : 0 < δ) :
    IsViscSuper (ball (0 : E d) 1) (fun _ ↦ Q x₀ + δ) v := by
  obtain ⟨r, hr, hr0, hconv⟩ := hv
  refine isViscSuper_of_tendstoLocallyUniformlyOn (l := atTop) isOpen_ball continuousOn_const
    ?_ hconv.tendstoLocallyUniformlyOn
  filter_upwards [eventually_blowup_ball hU hx₀ hQ hδ hr hr0] with n ⟨hsub, hQn⟩
  exact ((isViscSuper_blowup hU hu x₀ (hr n)).mono isOpen_ball hsub).mono_Q hQn

/-- **Two-plane blow-ups of supersolutions have slope at most `Q(x₀)`** (proof sketch of
Corollary 1.2). -/
theorem le_of_isBlowupLimit_twoPlane {U : Set (E d)} (hU : IsOpen U) {Q u : E d → ℝ}
    (hu : IsViscSuper U Q u) {x₀ : E d} (hx₀ : x₀ ∈ U) (hQ : ContinuousAt Q x₀)
    (hQ0 : 0 ≤ Q x₀) {v : E d → ℝ} (hv : IsBlowupLimit u x₀ v) {α : ℝ} {e : E d}
    (he : ‖e‖ = 1) (hvα : ∀ y, v y = α * |⟪y, e⟫|) : α ≤ Q x₀ := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hδ : 0 < (α - Q x₀) / 2 := by linarith
  exact not_isViscSuper_twoPlane (q := Q x₀ + (α - Q x₀) / 2) (by linarith) (by linarith) he
    isOpen_ball (mem_ball_self one_pos) hvα (isViscSuper_of_isBlowupLimit hU hu hx₀ hQ hv hδ)

end BlowupSuper

end Corollary2D

end PerronVariational

end
