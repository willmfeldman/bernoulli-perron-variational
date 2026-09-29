/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Laplacian calculus: chain rule and second-order extremum test

Generic lemmas on a finite-dimensional real inner product space `F` (used with `F = ℝᵈ`):

* `laplacian_eq_sum_fderiv_fderiv`: `Δf(x) = ∑ᵢ D²f(x)(eᵢ, eᵢ)` for an orthonormal basis;
* `laplacian_comp`: the chain rule `Δ(f ∘ g) = f''(g)|∇g|² + f'(g) Δg` at a point, for
  `f : ℝ → ℝ` and `g : F → ℝ` both `C²` near the relevant points (used in the proof of Lemma A.4,
  equations (A.6) and (A.7), of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
  Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981);
* `laplacian_nonneg_of_isLocalMin`: at an interior local minimum of a `C²` function the Laplacian
  is nonnegative (no multi-dimensional second-derivative test exists in Mathlib);
* `laplacian_le_of_eventually_le`: touching comparison of Laplacians of `C²` functions;
* `deriv_nonpos_of_eventually_le_left`, `deriv_nonneg_of_eventually_le_left`: one-sided
  first-derivative tests at a left local extremum.

The second-order extremum test is reduced to one variable along each basis direction.
-/

open Set Filter Topology InnerProductSpace
open scoped Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `Δf(x) = ∑ᵢ D²f(x)(eᵢ, eᵢ)` for the standard orthonormal basis (unconditional). -/
theorem laplacian_eq_sum_fderiv_fderiv (f : F → ℝ) (x : F) :
    Δ f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ F i)
      (stdOrthonormalBasis ℝ F i) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply]
  rfl

/-- The gradient has the same norm as the Fréchet derivative. -/
theorem norm_gradient_eq_norm_fderiv (f : F → ℝ) (x : F) : ‖∇ f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

/-- `∑ᵢ (Dg(x) eᵢ)² = |∇g(x)|²`. -/
theorem sum_fderiv_basis_sq (g : F → ℝ) (x : F) :
    ∑ i, (fderiv ℝ g x (stdOrthonormalBasis ℝ F i)) ^ 2 = ‖∇ g x‖ ^ 2 := by
  have h : ∀ v : F, fderiv ℝ g x v = ⟪∇ g x, v⟫ := fun v ↦ by
    simp [gradient, toDual_symm_apply]
  rw [← real_inner_self_eq_norm_sq, ← (stdOrthonormalBasis ℝ F).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h, sq, real_inner_comm (stdOrthonormalBasis ℝ F i)]

/-- **Chain rule for the Laplacian.** For `f : ℝ → ℝ` `C²` near `g x` and `g : F → ℝ` `C²` near
`x`: `Δ(f ∘ g)(x) = f''(g x) |∇g(x)|² + f'(g x) Δg(x)`. -/
theorem laplacian_comp {f : ℝ → ℝ} {g : F → ℝ} {x : F} (hf : ContDiffAt ℝ 2 f (g x))
    (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y ↦ f (g y)) x =
      deriv (deriv f) (g x) * ‖∇ g x‖ ^ 2 + deriv f (g x) * Δ g x := by
  -- first derivatives near `x`
  have hgev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y := by
    filter_upwards [hg.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hfev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f (g y) := by
    have h1 : ∀ᶠ z in 𝓝 (g x), DifferentiableAt ℝ f z := by
      filter_upwards [hf.eventually (by simp)] with z hz
      exact hz.differentiableAt (by norm_num)
    exact hg.continuousAt.tendsto.eventually h1
  have hD1 : fderiv ℝ (fun y ↦ f (g y)) =ᶠ[𝓝 x] fun y ↦ deriv f (g y) • fderiv ℝ g y := by
    filter_upwards [hgev, hfev] with y hy1 hy2
    exact (hy2.hasDerivAt.comp_hasFDerivAt y hy1.hasFDerivAt).fderiv
  -- second derivatives at `x`
  have hf1 : DifferentiableAt ℝ (deriv f) (g x) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) (g x) := hf.fderiv_right (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun z ↦ fderiv ℝ f z 1) (g x) := h1.clm_apply contDiffAt_const
    have h3 : (fun z ↦ fderiv ℝ f z 1) = deriv f := funext fun z ↦ fderiv_apply_one_eq_deriv
    rw [h3] at h2
    exact h2.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y ↦ deriv f (g y))
      (deriv (deriv f) (g x) • fderiv ℝ g x) x :=
    hf1.hasDerivAt.comp_hasFDerivAt x (hgev.self_of_nhds.hasFDerivAt)
  have hD2 := hc.smul hg1.hasFDerivAt
  have hfd : fderiv ℝ (fderiv ℝ fun y ↦ f (g y)) x =
      deriv f (g x) • fderiv ℝ (fderiv ℝ g) x +
        (deriv (deriv f) (g x) • fderiv ℝ g x).smulRight (fderiv ℝ g x) := by
    rw [hD1.fderiv_eq]; exact hD2.fderiv
  rw [laplacian_eq_sum_fderiv_fderiv, laplacian_eq_sum_fderiv_fderiv, hfd,
    ← sum_fderiv_basis_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-! ### Second-order extremum test -/

/-- 1-D core of the second-derivative test: if `ψ` has a local minimum at `0`, has
derivative `w t` at every `t` near `0`, and `w` has derivative `q` at `0`, then `0 ≤ q`. -/
private theorem nonneg_of_isLocalMin_of_hasDerivAt {ψ w : ℝ → ℝ} {q : ℝ}
    (hmin : IsLocalMin ψ 0) (hw : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt ψ (w t) t)
    (hq : HasDerivAt w q 0) : 0 ≤ q := by
  by_contra hq'
  have hq2 : q < 0 := not_le.1 hq'
  have hw0 : w 0 = 0 := by
    rw [← hw.self_of_nhds.deriv]
    exact hmin.deriv_eq_zero
  have hslope : Tendsto (slope w 0) (𝓝[>] (0 : ℝ)) (𝓝 q) :=
    (hasDerivAt_iff_tendsto_slope.1 hq).mono_left
      (nhdsWithin_mono 0 fun t ht ↦ ne_of_gt ht)
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), w t < 0 := by
    have h5 : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope w 0 t < q / 2 :=
      hslope.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [h5, self_mem_nhdsWithin] with t h5t ht
    have ht' : (0 : ℝ) < t := ht
    rw [slope_def_field, hw0, sub_zero, sub_zero] at h5t
    have h6 := (div_lt_iff₀ ht').1 h5t
    nlinarith
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.eventually_nhds_iff_ball.1 (hw.and hmin)
  obtain ⟨u, hu, h₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hneg
  have hu' : (0 : ℝ) < u := hu
  set b := min (r₁ / 2) (u / 2) with hb
  have hb0 : 0 < b := lt_min (by linarith) (by linarith)
  have hball : ∀ t ∈ Icc (0 : ℝ) b, t ∈ Metric.ball (0 : ℝ) r₁ := by
    rintro t ⟨ht0, htb⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    have : b ≤ r₁ / 2 := min_le_left _ _
    linarith
  have hanti : StrictAntiOn ψ (Icc 0 b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 b) ?_ ?_
    · intro t ht
      exact (h₁ t (hball t ht)).1.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(h₁ t (hball t ⟨ht.1.le, ht.2.le⟩)).1.deriv]
      refine h₂ ⟨ht.1, ?_⟩
      have h7 : b ≤ u / 2 := min_le_right _ _
      linarith [ht.2]
  have hcontra : ψ b < ψ 0 :=
    hanti (left_mem_Icc.2 hb0.le) (right_mem_Icc.2 hb0.le) hb0
  have hmin' : ψ 0 ≤ ψ b := (h₁ b (hball b (right_mem_Icc.2 hb0.le))).2
  linarith

omit [FiniteDimensional ℝ F] in
/-- At a local minimum of a function which is `C²` there, the second derivative is nonnegative
on the diagonal. -/
theorem fderiv_fderiv_nonneg_of_isLocalMin {f : F → ℝ} {x : F} (hmin : IsLocalMin f x)
    (hf : ContDiffAt ℝ 2 f x) (v : F) : 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  set L : ℝ → F := fun t ↦ x + t • v with hLdef
  have hL0 : L 0 = x := by simp [hLdef]
  have hLt : Tendsto L (𝓝 0) (𝓝 x) := by
    have h1 : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
    simpa [hL0] using h1.tendsto 0
  have hLd : ∀ t : ℝ, HasDerivAt L v t := fun t ↦ by
    have h := ((hasDerivAt_id t).smul_const v).const_add x
    rw [one_smul] at h
    exact h
  have hψmin : IsLocalMin (f ∘ L) 0 := by
    have h2 : IsMinFilter f (𝓝 x) (L 0) := by rwa [hL0]
    exact h2.comp_tendsto hLt
  have hf'1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hB : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (L 0) := by
    rw [hL0]; exact (hf'1.differentiableAt one_ne_zero).hasFDerivAt
  have hwq : HasDerivAt (fun t ↦ fderiv ℝ f (L t) v) (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have h1 := hB.comp_hasDerivAt 0 (hLd 0)
    simpa using h1.clm_apply (hasDerivAt_const 0 v)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (f ∘ L) (fderiv ℝ f (L t) v) t := by
    have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
      filter_upwards [hf.eventually (by simp)] with y hy
      exact hy.differentiableAt two_ne_zero
    filter_upwards [hLt.eventually hdiff] with t ht
    exact ht.hasFDerivAt.comp_hasDerivAt t (hLd t)
  exact nonneg_of_isLocalMin_of_hasDerivAt hψmin hev hwq

/-- **Second-order interior test.** At an interior local minimum of a `C²` function the
Laplacian is nonnegative. -/
theorem laplacian_nonneg_of_isLocalMin {f : F → ℝ} {x : F} (hmin : IsLocalMin f x)
    (hf : ContDiffAt ℝ 2 f x) : 0 ≤ Δ f x := by
  rw [laplacian_eq_sum_fderiv_fderiv]
  exact Finset.sum_nonneg fun i _ ↦ fderiv_fderiv_nonneg_of_isLocalMin hmin hf _

/-- **Touching comparison.** If `u ≤ φ` near `x`, `u x = φ x`, and both are `C²` at `x`, then
`Δu(x) ≤ Δφ(x)`. -/
theorem laplacian_le_of_eventually_le {u φ : F → ℝ} {x : F} (hu : ContDiffAt ℝ 2 u x)
    (hφ : ContDiffAt ℝ 2 φ x) (hx : u x = φ x) (hle : ∀ᶠ y in 𝓝 x, u y ≤ φ y) :
    Δ u x ≤ Δ φ x := by
  have hmin : IsLocalMin (φ - u) x := by
    filter_upwards [hle] with y hy
    simp only [Pi.sub_apply, hx, sub_self]
    linarith
  have h := laplacian_nonneg_of_isLocalMin hmin (hφ.sub hu)
  rw [hφ.laplacian_sub hu] at h
  simpa using h

/-! ### One-sided derivative tests in one variable -/

/-- If `f(t) ≤ f(s)` for `s ≤ t` near `t` and `f` is differentiable at `t`, then `f'(t) ≤ 0`. -/
theorem deriv_nonpos_of_eventually_le_left {f : ℝ → ℝ} {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (h : ∀ᶠ s in 𝓝[≤] t, f t ≤ f s) : deriv f t ≤ 0 := by
  have hmin : IsLocalMinOn f (Iic t) t := h
  have hy : (-1 : ℝ) ∈ posTangentConeAt (Iic t) t :=
    mem_posTangentConeAt_of_segment_subset
      ((convex_Iic t).segment_subset self_mem_Iic (by simp))
  have := hmin.hasFDerivWithinAt_nonneg hf.hasDerivAt.hasDerivWithinAt.hasFDerivWithinAt hy
  simpa using this

/-- If `f(s) ≤ f(t)` for `s ≤ t` near `t` and `f` is differentiable at `t`, then `0 ≤ f'(t)`. -/
theorem deriv_nonneg_of_eventually_le_left {f : ℝ → ℝ} {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (h : ∀ᶠ s in 𝓝[≤] t, f s ≤ f t) : 0 ≤ deriv f t := by
  have := deriv_nonpos_of_eventually_le_left (f := fun s ↦ -f s) hf.neg
    (h.mono fun s hs ↦ neg_le_neg hs)
  have hneg : deriv (fun s ↦ -f s) t = -deriv f t := deriv.neg
  linarith

end PerronVariational

end
