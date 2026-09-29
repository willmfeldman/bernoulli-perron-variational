/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Second-order calculus for viscosity test functions

Pointwise facts about the gradient and the Laplacian of `C²` functions used by the viscosity
theory of §2 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981:

* `iteratedFDeriv_two_eq_of_isLittleO`: a second-order expansion along a line identifies the
  value, the directional derivative and the second directional derivative;
* `laplacian_eq_of_sub_isLittleO`, `laplacian_eq_of_sub_isBigO_pow_three`: two `C²` functions
  whose difference vanishes to second order at `x` ("zero 2-jet") have the same value, gradient
  and Laplacian at `x`;
* `IsLocalMax.laplacian_nonpos`, `IsLocalMin.laplacian_nonneg`;
* continuity of `∇ f` and `Δ f` for `C¹` resp. `C²` functions.
-/

open Set Filter Topology Asymptotics
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

section OneDim

/-- A quadratic polynomial which is `o(t²)` at `0` vanishes identically. -/
theorem quadratic_eq_zero_of_isLittleO {a b c : ℝ}
    (h : (fun t : ℝ ↦ a + b * t + c * t ^ 2) =o[𝓝 0] fun t ↦ t ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a = 0 := by
    have := (isLittleO_pure (x := (0 : ℝ))).1 (h.mono (pure_le_nhds 0))
    simpa using this
  subst ha
  -- `|b| ≤ ε` and `|c| ≤ ε` for every `ε > 0`.
  have key : ∀ ε > 0, |b| ≤ ε ∧ |c| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (h.def hε)
    set t : ℝ := min (δ / 2) 1 with ht
    have ht0 : 0 < t := lt_min (half_pos hδ) one_pos
    have ht1 : t ≤ 1 := min_le_right _ _
    have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
    have h1 := hδ' (y := t) (by simpa [abs_of_pos ht0] using htδ)
    have h2 := hδ' (y := -t) (by simpa [abs_of_pos ht0] using htδ)
    simp only [Real.norm_eq_abs, zero_add, even_two, Even.neg_pow, abs_pow, sq_abs] at h1 h2
    have ht2 : 0 < t ^ 2 := by positivity
    -- `2 c t² = f(t) + f(-t)` and `2 b t = f(t) - f(-t)`.
    have hc : |c| * t ^ 2 ≤ ε * t ^ 2 := by
      have : |2 * (c * t ^ 2)| ≤ 2 * (ε * t ^ 2) := by
        calc |2 * (c * t ^ 2)| = |(b * t + c * t ^ 2) + (b * -t + c * t ^ 2)| := by ring_nf
          _ ≤ |b * t + c * t ^ 2| + |b * -t + c * t ^ 2| := abs_add_le _ _
          _ ≤ 2 * (ε * t ^ 2) := by linarith
      rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos ht2] at this
      linarith
    have hb : |b| * t ≤ ε * t := by
      have : |2 * (b * t)| ≤ 2 * (ε * t ^ 2) := by
        calc |2 * (b * t)| = |(b * t + c * t ^ 2) - (b * -t + c * t ^ 2)| := by ring_nf
          _ ≤ |b * t + c * t ^ 2| + |b * -t + c * t ^ 2| := abs_sub _ _
          _ ≤ 2 * (ε * t ^ 2) := by linarith
      rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos ht0] at this
      have htt : t ^ 2 ≤ t := by nlinarith
      have : ε * t ^ 2 ≤ ε * t := mul_le_mul_of_nonneg_left htt hε.le
      linarith
    exact ⟨le_of_mul_le_mul_right hb ht0, le_of_mul_le_mul_right hc ht2⟩
  refine ⟨rfl, ?_, ?_⟩
  · by_contra hb
    have := (key (|b| / 2) (by positivity)).1
    have : 0 < |b| := abs_pos.2 hb
    linarith
  · by_contra hc
    have := (key (|c| / 2) (by positivity)).2
    have : 0 < |c| := abs_pos.2 hc
    linarith

/-- Second-order Taylor expansion of a `C²` function of one real variable at `0`. -/
theorem taylor_two_isLittleO {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    (fun t ↦ f t - (f 0 + deriv f 0 * t + deriv (deriv f) 0 / 2 * t ^ 2)) =o[𝓝 0]
      fun t ↦ t ^ 2 := by
  have h := taylor_isLittleO_univ (x₀ := 0) (n := 2) hf
  simp only [sub_zero] at h
  refine h.congr_left fun t ↦ ?_
  simp only [taylor_within_apply, iteratedDerivWithin_univ, Finset.sum_range_succ,
    Finset.sum_range_zero, iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, sub_zero]
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  simp only [Nat.factorial, Nat.cast_one]
  ring

end OneDim

section Directional

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivative of `t ↦ k (x + t • v)`. -/
theorem hasDerivAt_comp_line {k : F → ℝ} (hk : Differentiable ℝ k) (x v : F) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ k (x + s • v)) (fderiv ℝ k (x + t • v) v) t := by
  have hl : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hk _).hasFDerivAt.comp_hasDerivAt t hl

/-- For `k ∈ C²`, the second derivative of `t ↦ k (x + t • v)` at `0` is `D²k(x)(v, v)`. -/
theorem deriv_deriv_comp_line {k : F → ℝ} (hk : ContDiff ℝ 2 k) (x v : F) :
    deriv (deriv fun s : ℝ ↦ k (x + s • v)) 0 = iteratedFDeriv ℝ 2 k x ![v, v] := by
  have hk1 : Differentiable ℝ k := hk.differentiable (by norm_num)
  have hd : deriv (fun s : ℝ ↦ k (x + s • v)) = fun s ↦ fderiv ℝ k (x + s • v) v :=
    funext fun s ↦ (hasDerivAt_comp_line hk1 x v s).deriv
  rw [hd, iteratedFDeriv_two_apply]
  have hk' : Differentiable ℝ (fderiv ℝ k) :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hl : HasDerivAt (fun s : ℝ ↦ x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 := ((hk' _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl)
  have h3 := ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h2
  simpa using h3.deriv

/-- A second-order expansion of `k ∈ C²` along the line `x + t • v` identifies `k x`, the
directional derivative `Dk(x) v` and the second directional derivative `D²k(x)(v, v)`. -/
theorem iteratedFDeriv_two_eq_of_isLittleO {k : F → ℝ} (hk : ContDiff ℝ 2 k) {x v : F}
    {a b c : ℝ}
    (h : (fun t : ℝ ↦ k (x + t • v) - (a + b * t + c * t ^ 2)) =o[𝓝 0] fun t ↦ t ^ 2) :
    k x = a ∧ fderiv ℝ k x v = b ∧ iteratedFDeriv ℝ 2 k x ![v, v] = 2 * c := by
  set f : ℝ → ℝ := fun t ↦ k (x + t • v) with hf_def
  have hf : ContDiff ℝ 2 f := hk.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hT := taylor_two_isLittleO hf
  have hdiff := hT.sub h
  have hq := quadratic_eq_zero_of_isLittleO
    (a := a - f 0) (b := b - deriv f 0) (c := c - deriv (deriv f) 0 / 2)
    (hdiff.congr_left fun t ↦ by ring)
  have h0 : f 0 = k x := by simp [f]
  have h1 : deriv f 0 = fderiv ℝ k x v := by
    simpa using (hasDerivAt_comp_line (hk.differentiable (by norm_num)) x v 0).deriv
  have h2 : deriv (deriv f) 0 = iteratedFDeriv ℝ 2 k x ![v, v] := deriv_deriv_comp_line hk x v
  refine ⟨?_, ?_, ?_⟩
  · rw [← h0]; linarith [hq.1]
  · rw [← h1]; linarith [hq.2.1]
  · rw [← h2]; linarith [hq.2.2]

/-- If `k ∈ C²` has a local maximum at `x`, then `D²k(x)(v, v) ≤ 0` for every `v`. -/
theorem IsLocalMax.iteratedFDeriv_two_nonpos {k : F → ℝ} (hk : ContDiff ℝ 2 k) {x : F}
    (h : IsLocalMax k x) (v : F) : iteratedFDeriv ℝ 2 k x ![v, v] ≤ 0 := by
  set f : ℝ → ℝ := fun t ↦ k (x + t • v) with hf_def
  have hf : ContDiff ℝ 2 f := hk.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hmax : IsLocalMax f 0 := by
    have hc : Continuous fun t : ℝ ↦ x + t • v := by fun_prop
    have h0 : IsLocalMax k ((fun t : ℝ ↦ x + t • v) 0) := by
      simp only [zero_smul, add_zero]; exact h
    exact IsLocalMax.comp_continuous h0 hc.continuousAt
  have hd0 : deriv f 0 = 0 := hmax.deriv_eq_zero
  rw [← deriv_deriv_comp_line hk x v]
  change deriv (deriv f) 0 ≤ 0
  by_contra hpos
  push Not at hpos
  set c := deriv (deriv f) 0 / 2 with hc
  have hc0 : 0 < c := by positivity
  have hT := (taylor_two_isLittleO hf).def (half_pos hc0)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hT.and hmax)
  have ht : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; exact half_lt_self hδ
  obtain ⟨h1, h2⟩ := hδ' ht
  rw [hd0] at h1
  simp only [zero_mul, add_zero, Real.norm_eq_abs, abs_pow] at h1
  have hsq : 0 < (δ / 2) ^ 2 := by positivity
  have := neg_abs_le (f (δ / 2) - (f 0 + c * (δ / 2) ^ 2))
  rw [sq_abs] at h1
  nlinarith

/-- **Second-order Taylor expansion** of a `C²` function in a normed space:
`H(y) = H(z) + DH(z)(y - z) + D²H(z)(y - z, y - z)/2 + o(|y - z|²)`. -/
theorem isLittleO_sub_taylor_two {H : F → ℝ} (hH : ContDiff ℝ 2 H) (z : F) :
    (fun y ↦ H y - (H z + fderiv ℝ H z (y - z) + fderiv ℝ (fderiv ℝ H) z (y - z) (y - z) / 2))
      =o[𝓝 z] fun y ↦ ‖y - z‖ ^ 2 := by
  set B := fderiv ℝ (fderiv ℝ H) z with hB
  have hH1 : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ H) B z :=
    ((hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt
  have hsymm : ∀ v w, B v w = B w v :=
    hH.contDiffAt.isSymmSndFDerivAt (by simp)
  set f : F → ℝ := fun y ↦ H y - (H z + fderiv ℝ H z (y - z) + B (y - z) (y - z) / 2) with hf
  have hf' : ∀ y, HasFDerivAt f (fderiv ℝ H y - fderiv ℝ H z - B (y - z)) y := by
    intro y
    have hs : HasFDerivAt (fun y : F ↦ y - z) (ContinuousLinearMap.id ℝ F) y :=
      (hasFDerivAt_id y).sub_const z
    have hlin : HasFDerivAt (fun y ↦ fderiv ℝ H z (y - z)) (fderiv ℝ H z) y := by
      have := (fderiv ℝ H z).hasFDerivAt.comp y hs
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using this
    have hc : HasFDerivAt (fun y ↦ B (y - z)) B y := by
      have := B.hasFDerivAt.comp y hs
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using this
    have hq := (hc.clm_apply hs).mul_const (1 / 2 : ℝ)
    have := (hH1 y).hasFDerivAt.sub (((hasFDerivAt_const (H z) y).add hlin).add hq)
    convert this using 1
    · funext w; simp only [hf, Pi.sub_apply, Pi.add_apply]; ring
    · ext w
      simp [hsymm w]
      ring
  have hsmall := hd.isLittleO
  refine IsLittleO.of_bound fun c hc ↦ ?_
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.1 (hsmall.def hc)
  refine Metric.eventually_nhds_iff.2 ⟨ρ, hρ, fun y hy ↦ ?_⟩
  set r := ‖y - z‖ with hr
  have hs : Metric.closedBall z r ⊆ Metric.ball z ρ :=
    Metric.closedBall_subset_ball (by rwa [hr, ← dist_eq_norm])
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := f)
    (s := Metric.closedBall z r) (x := z) (y := y) (C := c * r)
    (fun w _ ↦ (hf' w).hasFDerivWithinAt)
    (fun w hw ↦ (hρ' (hs hw)).trans (mul_le_mul_of_nonneg_left
      (by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hw) hc.le))
    (convex_closedBall z r) (Metric.mem_closedBall_self (norm_nonneg _))
    (by simp [hr, dist_eq_norm])
  have hfz : f z = 0 := by simp [hf]
  rw [hfz, sub_zero] at key
  rw [Real.norm_eq_abs (‖y - z‖ ^ 2), abs_of_nonneg (by positivity)]
  calc ‖f y‖ ≤ c * r * ‖y - z‖ := key
    _ = c * ‖y - z‖ ^ 2 := by rw [hr]; ring

end Directional

section Laplacian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A `C²` function vanishing to second order at `x` has zero value, derivative and Laplacian
at `x`. -/
theorem laplacian_eq_zero_of_isLittleO {k : F → ℝ} (hk : ContDiff ℝ 2 k) {x : F}
    (h : k =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2) :
    k x = 0 ∧ fderiv ℝ k x = 0 ∧ Δ k x = 0 := by
  have hline : ∀ v : F, (fun t : ℝ ↦ k (x + t • v) - (0 + 0 * t + 0 * t ^ 2)) =o[𝓝 0]
      fun t ↦ t ^ 2 := by
    intro v
    have ht : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝 0) (𝓝 x) := by
      have : Continuous fun t : ℝ ↦ x + t • v := by fun_prop
      simpa using this.tendsto 0
    have h1 := h.comp_tendsto ht
    refine (h1.trans_isBigO ?_).congr_left fun t ↦ by simp
    refine IsBigO.of_bound (‖v‖ ^ 2) (Eventually.of_forall fun t ↦ ?_)
    simp [norm_smul, mul_pow, mul_comm]
  have hv := fun v ↦ iteratedFDeriv_two_eq_of_isLittleO hk (hline v)
  refine ⟨(hv 0).1, ?_, ?_⟩
  · ext v; simpa using (hv v).2.1
  · rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp [(hv _).2.2]

/-- If `k ∈ C²` has a local maximum at `x`, then `Δk(x) ≤ 0`. -/
theorem IsLocalMax.laplacian_nonpos {k : F → ℝ} (hk : ContDiff ℝ 2 k) {x : F}
    (h : IsLocalMax k x) : Δ k x ≤ 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  exact Finset.sum_nonpos fun i _ ↦ IsLocalMax.iteratedFDeriv_two_nonpos hk h _

/-- If `k ∈ C²` has a local minimum at `x`, then `0 ≤ Δk(x)`. -/
theorem IsLocalMin.laplacian_nonneg {k : F → ℝ} (hk : ContDiff ℝ 2 k) {x : F}
    (h : IsLocalMin k x) : 0 ≤ Δ k x := by
  have h' : IsLocalMax (-k) x := IsLocalMin.neg h
  have h2 : Δ (-k) x ≤ 0 := IsLocalMax.laplacian_nonpos hk.neg h'
  rw [InnerProductSpace.laplacian_neg] at h2
  simpa using h2

/-- **Zero 2-jet lemma.** If `φ, ψ ∈ C²` and `φ - ψ = o(|y - x|²)` at `x`, then `φ` and `ψ` have
the same value, gradient and Laplacian at `x`. -/
theorem laplacian_eq_of_sub_isLittleO {φ ψ : F → ℝ} (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    {x : F} (h : (fun y ↦ φ y - ψ y) =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2) :
    φ x = ψ x ∧ ∇ φ x = ∇ ψ x ∧ Δ φ x = Δ ψ x := by
  obtain ⟨h0, h1, h2⟩ := laplacian_eq_zero_of_isLittleO (hφ.sub hψ) h
  have hφ1 : DifferentiableAt ℝ φ x := hφ.differentiable (by norm_num) x
  have hψ1 : DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num) x
  refine ⟨by simpa [sub_eq_zero] using h0, ?_, ?_⟩
  · have : fderiv ℝ φ x = fderiv ℝ ψ x := by
      rw [fderiv_fun_sub hφ1 hψ1] at h1
      exact sub_eq_zero.1 h1
    simp [gradient, this]
  · have := (hφ.contDiffAt (x := x)).laplacian_sub (hψ.contDiffAt (x := x))
    rw [show (fun y ↦ φ y - ψ y) = φ - ψ from rfl, this] at h2
    exact sub_eq_zero.1 h2

/-- **Zero 2-jet lemma**, big-O form: if `φ, ψ ∈ C²` and `φ - ψ = O(|y - x|³)` at `x`, then `φ`
and `ψ` have the same value, gradient and Laplacian at `x`. -/
theorem laplacian_eq_of_sub_isBigO_pow_three {φ ψ : F → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ 2 ψ) {x : F} (h : (fun y ↦ φ y - ψ y) =O[𝓝 x] fun y ↦ ‖y - x‖ ^ 3) :
    φ x = ψ x ∧ ∇ φ x = ∇ ψ x ∧ Δ φ x = Δ ψ x := by
  refine laplacian_eq_of_sub_isLittleO hφ hψ (h.trans_isLittleO ?_)
  have ht : Tendsto (fun y ↦ ‖y - x‖) (𝓝 x) (𝓝 0) := by
    have : Continuous fun y ↦ ‖y - x‖ := by fun_prop
    simpa using this.tendsto x
  exact (isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by norm_num)).comp_tendsto ht

/-- Adding a constant does not change the Laplacian. -/
theorem laplacian_add_const {k : F → ℝ} {x : F} (hk : ContDiffAt ℝ 2 k x) (c : ℝ) :
    Δ (fun y ↦ k y + c) x = Δ k x := by
  have := hk.laplacian_add (contDiffAt_const (c := c))
  simp only [InnerProductSpace.laplacian_const, Pi.zero_apply, add_zero] at this
  exact this

/-- Adding a constant does not change the gradient. -/
theorem gradient_add_const (k : F → ℝ) (x : F) (c : ℝ) :
    ∇ (fun y ↦ k y + c) x = ∇ k x := by
  simp [gradient, fderiv_add_const]

/-- **Smooth majorant with prescribed 2-jet.** For `H ∈ C²`, `z` and `η > 0` there is a smooth
`φ` (a quadratic polynomial) with `φ(z) = H(z)`, `∇φ(z) = ∇H(z)`, `Δφ(z) = ΔH(z) + 2nη`
(`n = dim F`) and `H ≤ φ` near `z`. Used to test viscosity inequalities with `C²` barriers. -/
theorem exists_smooth_ge_of_contDiff_two {H : F → ℝ} (hH : ContDiff ℝ 2 H) (z : F) {η : ℝ}
    (hη : 0 < η) :
    ∃ φ : F → ℝ, ContDiff ℝ ∞ φ ∧ φ z = H z ∧ ∇ φ z = ∇ H z ∧
      Δ φ z = Δ H z + 2 * (Module.finrank ℝ F : ℝ) * η ∧ ∀ᶠ y in 𝓝 z, H y ≤ φ y := by
  set B := fderiv ℝ (fderiv ℝ H) z with hB
  set L := fderiv ℝ H z with hL
  set φ : F → ℝ := fun y ↦ H z + L (y - z) + B (y - z) (y - z) / 2 + η * ‖y - z‖ ^ 2 with hφ
  have hφs : ContDiff ℝ ∞ φ := by
    have h1 : ContDiff ℝ ∞ fun y : F ↦ y - z := contDiff_id.sub contDiff_const
    have h2 : ContDiff ℝ ∞ fun y : F ↦ B (y - z) (y - z) := (B.contDiff.comp h1).clm_apply h1
    exact ((contDiff_const.add (L.contDiff.comp h1)).add (h2.div_const 2)).add
      (contDiff_const.mul ((contDiff_norm_sq ℝ).comp h1))
  have hjet : ∀ w : F, φ z = H z ∧ fderiv ℝ φ z w = L w ∧
      iteratedFDeriv ℝ 2 φ z ![w, w] = 2 * (B w w / 2 + η * ‖w‖ ^ 2) := by
    intro w
    refine iteratedFDeriv_two_eq_of_isLittleO (hφs.of_le (by norm_cast))
      ((isLittleO_zero _ _).congr_left fun t ↦ ?_)
    simp only [hφ, add_sub_cancel_left, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  refine ⟨φ, hφs, (hjet 0).1, ?_, ?_, ?_⟩
  · have : fderiv ℝ φ z = L := by ext w; exact (hjet w).2.1
    simp [gradient, this, hL]
  · rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp_rw [fun i ↦ (hjet ((stdOrthonormalBasis ℝ F) i)).2.2, iteratedFDeriv_two_apply]
    have hn : ∀ i, ‖(stdOrthonormalBasis ℝ F) i‖ = 1 :=
      fun i ↦ (stdOrthonormalBasis ℝ F).orthonormal.1 i
    simp only [hn, one_pow, mul_one, Matrix.cons_val_zero, Matrix.cons_val_one, mul_add,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hB]
    ring_nf
  · filter_upwards [(isLittleO_sub_taylor_two hH z).def hη] with y hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖y - z‖ ^ 2)]
      at hy
    have := (abs_le.1 hy).2
    simp only [hφ]
    linarith

/-- The Laplacian of a `C²` function is continuous. -/
theorem continuous_laplacian {k : F → ℝ} (hk : ContDiff ℝ 2 k) : Continuous (Δ k) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  have hc := hk.continuous_iteratedFDeriv'
  fun_prop

/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient {k : F → ℝ} (hk : ContDiff ℝ 1 k) : Continuous (∇ k) := by
  have : ∇ k = fun y ↦ (InnerProductSpace.toDual ℝ F).symm (fderiv ℝ k y) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ F).symm.continuous.comp (hk.continuous_fderiv one_ne_zero)

end Laplacian

end PerronVariational

end
