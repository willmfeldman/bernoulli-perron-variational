/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Green's identity on discs for `C²` functions on `ℂ`

For `v : ℂ → ℝ` of class `C²` near `B̄_R(c)`:

* `integral_ball_laplacian`: `∫_{B_s(c)} Δv = s ∫_{-π}^{π} ∂_ρ v(c + s e^{iθ}) dθ`
  (the flux of `∇v` through `∂B_s(c)`), proved in polar coordinates by writing
  `ρ Δv = ∂_ρ(ρ ∂_ρ v) + ∂_θ(ρ⁻¹ ∂_θ v)` and integrating each term.
* `integral_integral_ball_laplacian_div`: the integrated form
  `∫_a^R (∫_{B_s(c)} Δv) / s ds = 2π (⨍_{∂B_R(c)} v - ⨍_{∂B_a(c)} v)`.

These are the smooth cases of the Riesz–Jensen formula used for the Riesz measure
(`CircleMean.exists_isRieszMeasure`), in the proof of Thm B.1 (Appendix B) of F. Abedin, W. M.
Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981 ("the paper").
-/

open Set Filter Topology Metric MeasureTheory Complex
open scoped Laplacian Real

@[expose] public section

namespace PerronVariational.PlanarGreen

variable {v : ℂ → ℝ} {U : Set ℂ}

/-- The Laplacian in the rotated orthonormal frame `e^{iθ}, i e^{iθ}`. -/
theorem laplacian_eq_rotated (v : ℂ → ℝ) (p : ℂ) (θ : ℝ) :
    Δ v p = fderiv ℝ (fderiv ℝ v) p (circleMap 0 1 θ) (circleMap 0 1 θ) +
      fderiv ℝ (fderiv ℝ v) p (circleMap 0 1 θ * I) (circleMap 0 1 θ * I) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis v
    (Complex.orthonormalBasisOneI.map (rotation (Circle.exp θ)))]
  simp [iteratedFDeriv_two_apply, Fin.sum_univ_two, circleMap, Circle.coe_exp]

theorem hasFDerivAt_fderiv (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) {p : ℂ} (hp : p ∈ U) :
    HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) p) p := by
  have h := (hv.contDiffAt (hU.mem_nhds hp)).fderiv_right (m := 1) (by norm_num)
  exact (h.differentiableAt (by norm_num)).hasFDerivAt

theorem hasDerivAt_circleMap_radius (c : ℂ) (ρ θ : ℝ) :
    HasDerivAt (fun r : ℝ ↦ circleMap c r θ) (circleMap 0 1 θ) ρ := by
  have := ((hasDerivAt_id ρ).ofReal_comp.mul_const (exp (θ * I))).const_add c
  simpa [circleMap] using this

/-- `∂_ρ (ρ ∂_ρ v)` in polar coordinates around `c`. -/
noncomputable def radTerm (v : ℂ → ℝ) (c : ℂ) (ρ θ : ℝ) : ℝ :=
  fderiv ℝ v (circleMap c ρ θ) (circleMap 0 1 θ) +
    ρ * fderiv ℝ (fderiv ℝ v) (circleMap c ρ θ) (circleMap 0 1 θ) (circleMap 0 1 θ)

/-- `∂_θ (ρ⁻¹ ∂_θ v)` in polar coordinates around `c`. -/
noncomputable def angTerm (v : ℂ → ℝ) (c : ℂ) (ρ θ : ℝ) : ℝ :=
  ρ * fderiv ℝ (fderiv ℝ v) (circleMap c ρ θ) (circleMap 0 1 θ * I) (circleMap 0 1 θ * I) -
    fderiv ℝ v (circleMap c ρ θ) (circleMap 0 1 θ)

theorem radTerm_add_angTerm (v : ℂ → ℝ) (c : ℂ) (ρ θ : ℝ) :
    radTerm v c ρ θ + angTerm v c ρ θ = ρ * Δ v (circleMap c ρ θ) := by
  rw [laplacian_eq_rotated v _ θ, radTerm, angTerm]
  ring

theorem hasDerivAt_radial (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) (c : ℂ) {ρ : ℝ} (θ : ℝ)
    (hp : circleMap c ρ θ ∈ U) :
    HasDerivAt (fun r : ℝ ↦ r * fderiv ℝ v (circleMap c r θ) (circleMap 0 1 θ))
      (radTerm v c ρ θ) ρ := by
  have h1 : HasDerivAt (fun r : ℝ ↦ fderiv ℝ v (circleMap c r θ))
      (fderiv ℝ (fderiv ℝ v) (circleMap c ρ θ) (circleMap 0 1 θ)) ρ :=
    (hasFDerivAt_fderiv hU hv hp).comp_hasDerivAt ρ (hasDerivAt_circleMap_radius c ρ θ)
  have h2 := h1.clm_apply (hasDerivAt_const ρ (circleMap 0 1 θ))
  have h3 := (hasDerivAt_id ρ).mul h2
  convert h3 using 1
  simp [radTerm]

theorem hasDerivAt_angular (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) (c : ℂ) (ρ : ℝ) {θ : ℝ}
    (hp : circleMap c ρ θ ∈ U) :
    HasDerivAt (fun t : ℝ ↦ fderiv ℝ v (circleMap c ρ t) (circleMap 0 1 t * I))
      (angTerm v c ρ θ) θ := by
  have h1 : HasDerivAt (fun t : ℝ ↦ fderiv ℝ v (circleMap c ρ t))
      (fderiv ℝ (fderiv ℝ v) (circleMap c ρ θ) (circleMap 0 ρ θ * I)) θ :=
    (hasFDerivAt_fderiv hU hv hp).comp_hasDerivAt θ (hasDerivAt_circleMap c ρ θ)
  have h2 := h1.clm_apply ((hasDerivAt_circleMap 0 1 θ).mul_const I)
  convert h2 using 1
  have e1 : circleMap 0 ρ θ * I = (ρ : ℝ) • (circleMap 0 1 θ * I) := by
    simp [circleMap, Complex.real_smul]; ring
  have e2 : circleMap 0 1 θ * I * I = -circleMap 0 1 θ := by
    rw [mul_assoc, I_mul_I]; ring
  rw [e1, e2, map_smul, ContinuousLinearMap.smul_apply, map_neg, angTerm, smul_eq_mul]
  ring

/-! ### Continuity -/

theorem continuous_circleMap_uncurry (c : ℂ) :
    Continuous fun q : ℝ × ℝ ↦ circleMap c q.1 q.2 := by
  unfold circleMap; fun_prop

theorem continuousOn_fderiv_comp (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) (c : ℂ) :
    ContinuousOn (fun q : ℝ × ℝ ↦ fderiv ℝ v (circleMap c q.1 q.2))
      {q | circleMap c q.1 q.2 ∈ U} :=
  (hv.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp
    (continuous_circleMap_uncurry c).continuousOn fun _ hq ↦ hq

theorem continuousOn_fderiv_fderiv (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) :
    ContinuousOn (fderiv ℝ (fderiv ℝ v)) U :=
  (hv.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl

theorem continuousOn_fderiv_fderiv_comp (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) (c : ℂ) :
    ContinuousOn (fun q : ℝ × ℝ ↦ fderiv ℝ (fderiv ℝ v) (circleMap c q.1 q.2))
      {q | circleMap c q.1 q.2 ∈ U} :=
  (continuousOn_fderiv_fderiv hU hv).comp (continuous_circleMap_uncurry c).continuousOn
    fun _ hq ↦ hq

theorem continuousOn_laplacian (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) :
    ContinuousOn (Δ v) U := by
  have h : Δ v = fun p ↦ fderiv ℝ (fderiv ℝ v) p (circleMap 0 1 0) (circleMap 0 1 0) +
      fderiv ℝ (fderiv ℝ v) p (circleMap 0 1 0 * I) (circleMap 0 1 0 * I) := by
    ext p; exact laplacian_eq_rotated v p 0
  rw [h]
  have hD := continuousOn_fderiv_fderiv hU hv
  exact ((hD.clm_apply continuousOn_const).clm_apply continuousOn_const).add
    ((hD.clm_apply continuousOn_const).clm_apply continuousOn_const)

theorem continuousOn_radTerm (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) (c : ℂ) :
    ContinuousOn (fun q : ℝ × ℝ ↦ radTerm v c q.1 q.2) {q | circleMap c q.1 q.2 ∈ U} := by
  have he : Continuous fun q : ℝ × ℝ ↦ circleMap 0 1 q.2 := by unfold circleMap; fun_prop
  unfold radTerm
  exact ((continuousOn_fderiv_comp hU hv c).clm_apply he.continuousOn).add
    (continuousOn_fst.mul (((continuousOn_fderiv_fderiv_comp hU hv c).clm_apply
      he.continuousOn).clm_apply he.continuousOn))

theorem continuousOn_angTerm (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) (c : ℂ) :
    ContinuousOn (fun q : ℝ × ℝ ↦ angTerm v c q.1 q.2) {q | circleMap c q.1 q.2 ∈ U} := by
  have he : Continuous fun q : ℝ × ℝ ↦ circleMap 0 1 q.2 := by unfold circleMap; fun_prop
  have heI : Continuous fun q : ℝ × ℝ ↦ circleMap 0 1 q.2 * I := he.mul continuous_const
  unfold angTerm
  exact (continuousOn_fst.mul (((continuousOn_fderiv_fderiv_comp hU hv c).clm_apply
      heI.continuousOn).clm_apply heI.continuousOn)).sub
    ((continuousOn_fderiv_comp hU hv c).clm_apply he.continuousOn)

theorem circleMap_mem_of_mem_Icc {c : ℂ} {s : ℝ} (hsub : closedBall c s ⊆ U) {ρ : ℝ}
    (hρ : ρ ∈ Icc 0 s) (θ : ℝ) : circleMap c ρ θ ∈ U := by
  apply hsub
  rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hρ.1]
  exact hρ.2

theorem rect_subset {c : ℂ} {s : ℝ} (hsub : closedBall c s ⊆ U) (I' : Set ℝ) :
    Icc 0 s ×ˢ I' ⊆ {q : ℝ × ℝ | circleMap c q.1 q.2 ∈ U} :=
  fun q hq ↦ circleMap_mem_of_mem_Icc hsub hq.1 q.2

theorem integrableOn_rect {g : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ Icc c d)) : IntegrableOn g (Ioo a b ×ˢ Ioo c d) :=
  (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

/-! ### Green's identity on a disc -/

theorem polarCoord_symm_eq_circleMap (c : ℂ) (q : ℝ × ℝ) :
    c + Complex.polarCoord.symm q = circleMap c q.1 q.2 := by
  simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `∫_{B_s(c)} Δv` in polar coordinates. -/
theorem integral_ball_eq_rect (c : ℂ) (s : ℝ) :
    ∫ z in ball c s, Δ v z =
      ∫ q in Ioo 0 s ×ˢ Ioo (-π) π, q.1 * Δ v (circleMap c q.1 q.2) := by
  have hset : Ioi (0 : ℝ) ×ˢ Ioo (-π) π ∩ Ioo 0 s ×ˢ Ioo (-π) π = Ioo 0 s ×ˢ Ioo (-π) π := by
    rw [prod_inter_prod, Ioi_inter_Ioo, inter_self, max_self]
  rw [← integral_indicator measurableSet_ball,
    ← integral_add_left_eq_self (μ := volume) _ c,
    ← Complex.integral_comp_polarCoord_symm, polarCoord_target, ← hset,
    ← setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun q hq ↦ ?_
  simp only [polarCoord_symm_eq_circleMap, smul_eq_mul]
  have hmem : circleMap c q.1 q.2 ∈ ball c s ↔ q ∈ Ioo 0 s ×ˢ Ioo (-π) π := by
    rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_pos hq.1, mem_prod]
    exact ⟨fun h ↦ ⟨⟨hq.1, h⟩, hq.2⟩, fun h ↦ h.1.2⟩
  by_cases h : q ∈ Ioo 0 s ×ˢ Ioo (-π) π
  · rw [indicator_of_mem (hmem.2 h), indicator_of_mem h]
  · rw [indicator_of_notMem (mt hmem.1 h), indicator_of_notMem h, mul_zero]

theorem integral_angTerm (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) (c : ℂ) {ρ : ℝ}
    (hρ : ∀ θ, circleMap c ρ θ ∈ U) : ∫ θ in Ioo (-π) π, angTerm v c ρ θ = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hcont : Continuous fun θ ↦ angTerm v c ρ θ :=
    continuousOn_univ.1 ((continuousOn_angTerm hU hv c).comp
      (continuous_const.prodMk continuous_id).continuousOn fun θ _ ↦ hρ θ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ ↦ hasDerivAt_angular hU hv c ρ (hρ θ)) (hcont.intervalIntegrable _ _)]
  have h1 : ∀ c' R, circleMap c' R π = circleMap c' R (-π) := by
    intro c' R
    have := periodic_circleMap c' R (-π)
    rw [show -π + 2 * π = π by ring] at this
    exact this
  simp only [h1, sub_self]

theorem integral_radTerm (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) {c : ℂ} {s : ℝ}
    (hs : 0 < s) (hsub : closedBall c s ⊆ U) (θ : ℝ) :
    ∫ ρ in Ioo 0 s, radTerm v c ρ θ = s * fderiv ℝ v (circleMap c s θ) (circleMap 0 1 θ) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le]
  have hmem : ∀ ρ ∈ uIcc 0 s, circleMap c ρ θ ∈ U := fun ρ hρ ↦
    circleMap_mem_of_mem_Icc hsub (by rwa [uIcc_of_le hs.le] at hρ) θ
  have hpair : Continuous fun ρ : ℝ ↦ ((ρ, θ) : ℝ × ℝ) := by fun_prop
  have hcont : ContinuousOn (fun ρ ↦ radTerm v c ρ θ) (uIcc 0 s) := by
    have h := (continuousOn_radTerm hU hv c).comp hpair.continuousOn (s := uIcc 0 s)
      (fun ρ hρ ↦ hmem ρ hρ)
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ρ hρ ↦ hasDerivAt_radial hU hv c θ (hmem ρ hρ)) hcont.intervalIntegrable,
    zero_mul, sub_zero]

/-- **Green's identity on a disc**: `∫_{B_s(c)} Δv = s ∫_{-π}^{π} ∂_ρ v(c + s e^{iθ}) dθ`. -/
theorem integral_ball_laplacian (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) {c : ℂ} {s : ℝ}
    (hs : 0 < s) (hsub : closedBall c s ⊆ U) :
    ∫ z in ball c s, Δ v z =
      s * ∫ θ in (-π)..π, fderiv ℝ v (circleMap c s θ) (circleMap 0 1 θ) := by
  rw [integral_ball_eq_rect]
  have hrect := rect_subset hsub (Icc (-π) π)
  have hrad : IntegrableOn (fun q : ℝ × ℝ ↦ radTerm v c q.1 q.2) (Ioo 0 s ×ˢ Ioo (-π) π) :=
    integrableOn_rect ((continuousOn_radTerm hU hv c).mono hrect)
  have hang : IntegrableOn (fun q : ℝ × ℝ ↦ angTerm v c q.1 q.2) (Ioo 0 s ×ˢ Ioo (-π) π) :=
    integrableOn_rect ((continuousOn_angTerm hU hv c).mono hrect)
  simp_rw [← radTerm_add_angTerm]
  rw [integral_add hrad hang]
  -- the angular term integrates to zero
  have hA : ∫ q in Ioo 0 s ×ˢ Ioo (-π) π, angTerm v c q.1 q.2 = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hang]
    refine (setIntegral_congr_fun measurableSet_Ioo fun ρ hρ ↦ ?_).trans (integral_zero ℝ ℝ)
    exact integral_angTerm hU hv c fun θ ↦ circleMap_mem_of_mem_Icc hsub (Ioo_subset_Icc_self hρ) θ
  rw [hA, add_zero]
  -- the radial term: swap and integrate in `ρ`
  rw [Measure.volume_eq_prod, ← setIntegral_prod_swap (Ioo 0 s) (Ioo (-π) π)
    (fun q : ℝ × ℝ ↦ radTerm v c q.1 q.2)]
  have hrad' : IntegrableOn (fun z : ℝ × ℝ ↦ radTerm v c z.swap.1 z.swap.2)
      (Ioo (-π) π ×ˢ Ioo 0 s) := by
    have h := (continuousOn_radTerm hU hv c).comp (s := Icc (-π) π ×ˢ Icc 0 s)
      continuous_swap.continuousOn fun q hq ↦ circleMap_mem_of_mem_Icc hsub hq.2 q.1
    exact integrableOn_rect h
  rw [setIntegral_prod _ hrad', ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  exact integral_radTerm hU hv hs hsub θ

theorem hasDerivAt_comp_circleMap_radius (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) (c : ℂ)
    {ρ : ℝ} (θ : ℝ) (hp : circleMap c ρ θ ∈ U) :
    HasDerivAt (fun r : ℝ ↦ v (circleMap c r θ))
      (fderiv ℝ v (circleMap c ρ θ) (circleMap 0 1 θ)) ρ := by
  have hd : DifferentiableAt ℝ v (circleMap c ρ θ) :=
    (hv.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  exact hd.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_circleMap_radius c ρ θ)

theorem integral_neg_pi_pi_eq_circleAverage {f : ℂ → ℝ} (c : ℂ) (R : ℝ) :
    ∫ θ in (-π)..π, f (circleMap c R θ) = 2 * π * Real.circleAverage f c R := by
  rw [Real.circleAverage, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have h := (periodic_circleMap c R).comp f |>.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h
  exact h

/-- **Integrated Green identity**: for `0 < a ≤ R`,
`∫_a^R (∫_{B_s(c)} Δv) / s ds = 2π (⨍_{∂B_R(c)} v - ⨍_{∂B_a(c)} v)`. -/
theorem integral_integral_ball_laplacian_div (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) {c : ℂ}
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) (hsub : closedBall c R ⊆ U) :
    ∫ s in a..R, (∫ z in ball c s, Δ v z) / s =
      2 * π * (Real.circleAverage v c R - Real.circleAverage v c a) := by
  set g : ℝ → ℝ → ℝ := fun s θ ↦ fderiv ℝ v (circleMap c s θ) (circleMap 0 1 θ) with hg
  have hS : Icc a R ×ˢ Icc (-π) π ⊆ {q : ℝ × ℝ | circleMap c q.1 q.2 ∈ U} :=
    fun q hq ↦ circleMap_mem_of_mem_Icc hsub ⟨ha.le.trans hq.1.1, hq.1.2⟩ q.2
  have hgc' : ContinuousOn (Function.uncurry g) {q : ℝ × ℝ | circleMap c q.1 q.2 ∈ U} := by
    have he : Continuous fun q : ℝ × ℝ ↦ circleMap 0 1 q.2 := by unfold circleMap; fun_prop
    exact (continuousOn_fderiv_comp hU hv c).clm_apply he.continuousOn
  have hgc : ContinuousOn (Function.uncurry g) (Icc a R ×ˢ Icc (-π) π) := hgc'.mono hS
  -- Step 1: Green's identity on each disc
  have h1 : ∫ s in a..R, (∫ z in ball c s, Δ v z) / s =
      ∫ s in a..R, ∫ θ in Ioc (-π) π, g s θ := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le haR] at hs
    have hs0 : 0 < s := ha.trans_le hs.1
    rw [integral_ball_laplacian hU hv hs0 ((closedBall_subset_closedBall hs.2).trans hsub),
      mul_div_cancel_left₀ _ hs0.ne', intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  -- Step 2: swap the integrals
  have hint : Integrable (Function.uncurry g)
      ((volume.restrict (uIoc a R)).prod (volume.restrict (Ioc (-π) π))) := by
    rw [Measure.prod_restrict, uIoc_of_le haR]
    exact (hgc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [h1, intervalIntegral_integral_swap hint]
  -- Step 3: FTC in the radius
  have h3 : ∀ θ, ∫ s in a..R, g s θ = v (circleMap c R θ) - v (circleMap c a θ) := by
    intro θ
    have hmem : ∀ s ∈ uIcc a R, circleMap c s θ ∈ U := fun s hs ↦
      circleMap_mem_of_mem_Icc hsub
        (by rw [uIcc_of_le haR] at hs; exact ⟨ha.le.trans hs.1, hs.2⟩) θ
    have hpair : Continuous fun s : ℝ ↦ ((s, θ) : ℝ × ℝ) := by fun_prop
    have hcont : ContinuousOn (fun s ↦ g s θ) (uIcc a R) := by
      have h := hgc'.comp hpair.continuousOn (s := uIcc a R) fun s hs ↦ hmem s hs
      exact h
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs ↦ hasDerivAt_comp_circleMap_radius hU hv c θ (hmem s hs)) hcont.intervalIntegrable
  simp_rw [h3]
  have hcR : Continuous fun θ ↦ v (circleMap c R θ) :=
    hv.continuousOn.comp_continuous (continuous_circleMap c R)
      fun θ ↦ circleMap_mem_of_mem_Icc hsub ⟨ha.le.trans haR, le_rfl⟩ θ
  have hca : Continuous fun θ ↦ v (circleMap c a θ) :=
    hv.continuousOn.comp_continuous (continuous_circleMap c a)
      fun θ ↦ circleMap_mem_of_mem_Icc hsub ⟨ha.le, haR⟩ θ
  rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_sub (hcR.intervalIntegrable _ _) (hca.intervalIntegrable _ _),
    integral_neg_pi_pi_eq_circleAverage, integral_neg_pi_pi_eq_circleAverage]
  ring

end PerronVariational.PlanarGreen

end
