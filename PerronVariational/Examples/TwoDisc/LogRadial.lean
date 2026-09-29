/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Setting
public import PerronVariational.Examples.TwoDisc.Ramp
public import ViscositySolns.Applications.Laplace.Weyl.LaplacianInvariance
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Profiles of logarithms of the distance, in the plane

A tool for the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`).

For a `C²` profile `P : ℝ → ℝ`, a centre `z ∈ ℝ²` and constants `α, k`, the function
`y ↦ P(α log |y - z|² + k)` is `C²` away from `z`, with
`Δ = 4 α² P''(α log τ + k) / τ` and `∇ = 2 α P'(α log τ + k) (y - z) / τ`, `τ = |y - z|²`
(the logarithm is harmonic in the plane). To make it globally `C²` we clamp `τ` below at `δ > 0`:
`logRad P z α k δ y = P(α log (max |y - z|² δ) + k)`. This is `C²` as soon as `P ∘ (α log · + k)`
is constant on `[δ, δ']` for some `δ' > δ`.

The planar radial Laplacian `Δ G(|y - z|²) = 4 τ G''(τ) + 4 G'(τ)` comes from
`ContDiff.laplacian_comp_norm_sq` (`viscosity_solns`).
-/

open Set Filter Topology Metric InnerProductSpace
open scoped Gradient Laplacian ContDiff

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

/-! ### Radial functions in the plane -/

/-- **Planar radial Laplacian.** For `G ∈ C²(ℝ)`,
`Δ G(|y - z|²) = 4 τ G''(τ) + 4 G'(τ)` at `τ = |x - z|²`. -/
theorem laplacian_radial {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (z x : E 2) :
    Δ (fun y : E 2 ↦ G (‖y - z‖ ^ 2)) x =
      4 * ‖x - z‖ ^ 2 * deriv (deriv G) (‖x - z‖ ^ 2) + 4 * deriv G (‖x - z‖ ^ 2) := by
  have h1 := congrFun (ViscositySolns.Analysis.laplacian_comp_add_right
    (fun w : E 2 ↦ G (‖w‖ ^ 2)) (-z)) x
  simp only [← sub_eq_add_neg] at h1
  rw [h1, hG.laplacian_comp_norm_sq, finrank_euclideanSpace_fin]
  ring

/-- **Planar radial gradient.** For differentiable `G`,
`∇ G(|y - z|²) = 2 G'(τ) (x - z)` at `τ = |x - z|²`. -/
theorem hasGradientAt_radial {G : ℝ → ℝ} {z x : E 2}
    (hG : DifferentiableAt ℝ G (‖x - z‖ ^ 2)) :
    HasGradientAt (fun y : E 2 ↦ G (‖y - z‖ ^ 2)) ((2 * deriv G (‖x - z‖ ^ 2)) • (x - z)) x := by
  have hf : HasFDerivAt (fun w : E 2 ↦ ‖w - z‖ ^ 2)
      (2 • (innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ (E 2))) x :=
    ((hasFDerivAt_id x).sub_const z).norm_sq
  have h := hG.hasDerivAt.comp_hasFDerivAt x hf
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext w
  simp only [toDual_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_id', id_eq,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-! ### Clamped logarithmic profiles -/

/-- The clamped profile `τ ↦ P(α log (max τ δ) + k)`. -/
def logProfile (P : ℝ → ℝ) (α k δ τ : ℝ) : ℝ := P (α * Real.log (max τ δ) + k)

/-- `logRad P z α k δ y = P(α log (max |y - z|² δ) + k)`. -/
def logRad (P : ℝ → ℝ) (z : E 2) (α k δ : ℝ) (y : E 2) : ℝ :=
  logProfile P α k δ (‖y - z‖ ^ 2)

variable {P P₁ P₂ : ℝ → ℝ} {α k δ δ' : ℝ}

theorem logProfile_of_le {τ : ℝ} (h : δ ≤ τ) : logProfile P α k δ τ = P (α * Real.log τ + k) := by
  rw [logProfile, max_eq_left h]

theorem logProfile_eventuallyEq {τ : ℝ} (h : δ < τ) :
    logProfile P α k δ =ᶠ[𝓝 τ] fun σ ↦ P (α * Real.log σ + k) := by
  filter_upwards [Ioi_mem_nhds h] with σ hσ using logProfile_of_le (le_of_lt hσ)

/-- The clamping hypothesis: `P(α log τ + k)` is constant for `τ ∈ [δ, δ']`. -/
def ClampConst (P : ℝ → ℝ) (α k δ δ' : ℝ) : Prop :=
  ∀ τ ∈ Icc δ δ', P (α * Real.log τ + k) = P (α * Real.log δ + k)

theorem logProfile_of_le_clamp (hc : ClampConst P α k δ δ') (hδ : δ ≤ δ') {τ : ℝ}
    (h : τ ≤ δ') : logProfile P α k δ τ = P (α * Real.log δ + k) :=
  hc _ ⟨le_max_right _ _, max_le h hδ⟩

theorem logProfile_eventuallyEq_const (hc : ClampConst P α k δ δ') (hδ : δ ≤ δ') {τ : ℝ}
    (h : τ < δ') : logProfile P α k δ =ᶠ[𝓝 τ] fun _ ↦ P (α * Real.log δ + k) := by
  filter_upwards [Iio_mem_nhds h] with σ hσ using logProfile_of_le_clamp hc hδ (le_of_lt hσ)

theorem contDiffAt_log_affine {τ : ℝ} (hτ : τ ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun σ ↦ α * Real.log σ + k) τ :=
  (contDiffAt_const.mul (Real.contDiffAt_log.2 hτ)).add contDiffAt_const

theorem contDiff_logProfile (hP : ContDiff ℝ 2 P) (hδ : 0 < δ) (hδδ' : δ < δ')
    (hc : ClampConst P α k δ δ') : ContDiff ℝ 2 (logProfile P α k δ) := by
  refine contDiff_iff_contDiffAt.2 fun τ ↦ ?_
  rcases lt_or_ge τ δ' with h | h
  · exact contDiffAt_const.congr_of_eventuallyEq (logProfile_eventuallyEq_const hc hδδ'.le h)
  · have hτ : δ < τ := hδδ'.trans_le h
    exact (hP.contDiffAt.comp τ (contDiffAt_log_affine (hδ.trans hτ).ne')).congr_of_eventuallyEq
      (logProfile_eventuallyEq hτ)

theorem contDiff_logRad (hP : ContDiff ℝ 2 P) (hδ : 0 < δ) (hδδ' : δ < δ')
    (hc : ClampConst P α k δ δ') (z : E 2) : ContDiff ℝ 2 (logRad P z α k δ) :=
  (contDiff_logProfile hP hδ hδδ' hc).comp
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

/-- The derivative of the unclamped profile. -/
theorem hasDerivAt_log_profile (hP₁ : ∀ t, HasDerivAt P (P₁ t) t) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun σ ↦ P (α * Real.log σ + k)) (P₁ (α * Real.log τ + k) * (α / τ)) τ := by
  have h : HasDerivAt (fun σ ↦ α * Real.log σ + k) (α * τ⁻¹) τ :=
    ((Real.hasDerivAt_log hτ.ne').const_mul α).add_const k
  have := (hP₁ _).comp τ h
  convert this using 1

theorem deriv_logProfile (hP₁ : ∀ t, HasDerivAt P (P₁ t) t) (hδ : 0 < δ) {τ : ℝ} (h : δ < τ) :
    deriv (logProfile P α k δ) τ = P₁ (α * Real.log τ + k) * (α / τ) := by
  rw [(logProfile_eventuallyEq h).deriv_eq, (hasDerivAt_log_profile hP₁ (hδ.trans h)).deriv]

theorem deriv_deriv_logProfile (hP₁ : ∀ t, HasDerivAt P (P₁ t) t)
    (hP₂ : ∀ t, HasDerivAt P₁ (P₂ t) t) (hδ : 0 < δ) {τ : ℝ} (h : δ < τ) :
    deriv (deriv (logProfile P α k δ)) τ =
      (P₂ (α * Real.log τ + k) * α ^ 2 - P₁ (α * Real.log τ + k) * α) / τ ^ 2 := by
  have hτ : 0 < τ := hδ.trans h
  have heq : deriv (logProfile P α k δ) =ᶠ[𝓝 τ] fun σ ↦ P₁ (α * Real.log σ + k) * (α / σ) := by
    filter_upwards [Ioi_mem_nhds h] with σ hσ using deriv_logProfile hP₁ hδ hσ
  rw [heq.deriv_eq]
  have h1 : HasDerivAt (fun σ ↦ P₁ (α * Real.log σ + k)) (P₂ (α * Real.log τ + k) * (α / τ)) τ :=
    hasDerivAt_log_profile hP₂ hτ
  have h2 : HasDerivAt (fun σ : ℝ ↦ α / σ) (-(α / τ ^ 2)) τ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hτ.ne').const_mul α
  rw [show (fun σ ↦ P₁ (α * Real.log σ + k) * (α / σ)) =
      (fun σ ↦ P₁ (α * Real.log σ + k)) * (fun σ : ℝ ↦ α / σ) from rfl, (h1.mul h2).deriv]
  field_simp
  ring

theorem deriv_logProfile_of_lt_clamp (hc : ClampConst P α k δ δ') (hδ : δ ≤ δ') {τ : ℝ}
    (h : τ < δ') : deriv (logProfile P α k δ) τ = 0 := by
  rw [(logProfile_eventuallyEq_const hc hδ h).deriv_eq, deriv_const]

theorem deriv_deriv_logProfile_of_lt_clamp (hc : ClampConst P α k δ δ') (hδ : δ ≤ δ') {τ : ℝ}
    (h : τ < δ') : deriv (deriv (logProfile P α k δ)) τ = 0 := by
  have heq : deriv (logProfile P α k δ) =ᶠ[𝓝 τ] fun _ ↦ 0 := by
    filter_upwards [Iio_mem_nhds h] with σ hσ using deriv_logProfile_of_lt_clamp hc hδ hσ
  rw [heq.deriv_eq, deriv_const]

/-! ### Laplacian and gradient of `logRad` -/

variable (hP : ContDiff ℝ 2 P) (hP₁ : ∀ t, HasDerivAt P (P₁ t) t)
  (hP₂ : ∀ t, HasDerivAt P₁ (P₂ t) t) (hδ : 0 < δ) (hδδ' : δ < δ') (hc : ClampConst P α k δ δ')
include hP hP₁ hP₂ hδ hδδ' hc

/-- **Laplacian of a log-radial profile** in the plane, off the clamp:
`Δ P(α log τ + k) = 4 α² P''(α log τ + k) / τ`. -/
theorem laplacian_logRad {z x : E 2} (h : δ < ‖x - z‖ ^ 2) :
    Δ (logRad P z α k δ) x = 4 * α ^ 2 * P₂ (α * Real.log (‖x - z‖ ^ 2) + k) / ‖x - z‖ ^ 2 := by
  have hτ : 0 < ‖x - z‖ ^ 2 := hδ.trans h
  change Δ (fun y : E 2 ↦ logProfile P α k δ (‖y - z‖ ^ 2)) x = _
  rw [laplacian_radial (contDiff_logProfile hP hδ hδδ' hc), deriv_logProfile hP₁ hδ h,
    deriv_deriv_logProfile hP₁ hP₂ hδ h]
  field_simp
  ring

omit hP₁ hP₂ in
/-- On the clamp, `logRad` is locally constant: its Laplacian vanishes. -/
theorem laplacian_logRad_of_lt_clamp {z x : E 2} (h : ‖x - z‖ ^ 2 < δ') :
    Δ (logRad P z α k δ) x = 0 := by
  change Δ (fun y : E 2 ↦ logProfile P α k δ (‖y - z‖ ^ 2)) x = _
  rw [laplacian_radial (contDiff_logProfile hP hδ hδδ' hc),
    deriv_logProfile_of_lt_clamp hc hδδ'.le h, deriv_deriv_logProfile_of_lt_clamp hc hδδ'.le h]
  ring

omit hP₂ in
/-- **Gradient of a log-radial profile**, off the clamp:
`∇ P(α log τ + k) = 2 α P'(α log τ + k) (x - z) / τ`. -/
theorem hasGradientAt_logRad {z x : E 2} (h : δ < ‖x - z‖ ^ 2) :
    HasGradientAt (logRad P z α k δ)
      ((2 * (P₁ (α * Real.log (‖x - z‖ ^ 2) + k) * (α / ‖x - z‖ ^ 2))) • (x - z)) x := by
  have hG := contDiff_logProfile hP hδ hδδ' hc
  have := hasGradientAt_radial (z := z) (x := x)
    ((hG.differentiable (by norm_num)) (‖x - z‖ ^ 2))
  rwa [deriv_logProfile hP₁ hδ h] at this

omit hP₁ hP₂ in
/-- On the clamp, the gradient of `logRad` vanishes. -/
theorem hasGradientAt_logRad_of_lt_clamp {z x : E 2} (h : ‖x - z‖ ^ 2 < δ') :
    HasGradientAt (logRad P z α k δ) 0 x := by
  have hG := contDiff_logProfile hP hδ hδδ' hc
  have := hasGradientAt_radial (z := z) (x := x)
    ((hG.differentiable (by norm_num)) (‖x - z‖ ^ 2))
  rwa [deriv_logProfile_of_lt_clamp hc hδδ'.le h, mul_zero, zero_smul] at this

omit hP₂ in
theorem norm_gradient_logRad {z x : E 2} (h : δ < ‖x - z‖ ^ 2) :
    ‖∇ (logRad P z α k δ) x‖ =
      2 * |α| * |P₁ (α * Real.log (‖x - z‖ ^ 2) + k)| / ‖x - z‖ := by
  have hs : 0 < ‖x - z‖ := by
    have := hδ.trans h
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by simpa using this)
  rw [(hasGradientAt_logRad hP hP₁ hδ hδδ' hc h).gradient, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖x - z‖ ^ 2)]
  field_simp
  ring

end PerronVariational.TwoDisc

end
