/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.DirectionalStable.Lemma211
import GMTFoundations.Sobolev.Lattice
import Mathlib.Data.Real.StarOrdered

/-!
# Stability of directional minimality: blow-ups (Corollary 2.13)

The affine change of variables `y ↦ x₀ + r y` (scaling invariance of Definition 2.11,
`blowup_isDownwardMinimizer_scaled`) and **Corollary 2.13** of F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981: `blowup_isDownwardMinimizer`, `blowup_isUpwardMinimizer`,
`blowup_isUpwardMinimizer'`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal NNReal

@[expose] public section

namespace PerronVariational

namespace DirectionalStable

variable {d : ℕ}

/-! ### Scaling: the affine change of variables `y ↦ x₀ + r y` -/

section Scaling

/-- The affine map `y ↦ x₀ + r y` as a measurable equivalence. -/
noncomputable def affE (x₀ : E d) (r : ℝ) (hr : r ≠ 0) : E d ≃ᵐ E d :=
  (MeasurableEquiv.smul₀ r hr).trans (MeasurableEquiv.addLeft x₀)

theorem affE_apply (x₀ : E d) (r : ℝ) (hr : r ≠ 0) (y : E d) : affE x₀ r hr y = x₀ + r • y := rfl

/-- The Jacobian factor `|r|^{-d}`. -/
noncomputable def jac (d : ℕ) (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal |(r ^ d)⁻¹|

theorem map_affE (x₀ : E d) (r : ℝ) (hr : r ≠ 0) :
    Measure.map (affE x₀ r hr) volume = jac d r • (volume : Measure (E d)) := by
  have h : (affE x₀ r hr : E d → E d) = (fun z ↦ x₀ + z) ∘ fun y ↦ r • y := rfl
  rw [h, ← Measure.map_map (measurable_const_add x₀) (measurable_const_smul r),
    Measure.map_addHaar_smul volume hr, Measure.map_smul, map_add_left_eq_self,
    finrank_euclideanSpace_fin]
  rfl

section Affine

variable {x₀ : E d} {r : ℝ} (hr : r ≠ 0)
include hr

theorem jac_ne_zero : jac d r ≠ 0 := by
  unfold jac
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]
  exact abs_pos.2 (inv_ne_zero (pow_ne_zero _ hr))

omit hr in
theorem jac_ne_top : jac d r ≠ ⊤ := ENNReal.ofReal_ne_top

theorem restrict_map_affE (S : Set (E d)) :
    Measure.map (affE x₀ r hr) (volume.restrict (affE x₀ r hr ⁻¹' S)) =
      jac d r • volume.restrict S := by
  rw [← MeasurableEquiv.restrict_map, map_affE, Measure.restrict_smul]

theorem setLIntegral_comp_affE (F : E d → ℝ≥0∞) (S : Set (E d)) :
    ∫⁻ y in affE x₀ r hr ⁻¹' S, F (affE x₀ r hr y) = jac d r * ∫⁻ z in S, F z := by
  rw [← lintegral_map_equiv, restrict_map_affE hr, lintegral_smul_measure, smul_eq_mul]

theorem integral_comp_affE (g : E d → ℝ) :
    ∫ y, g (affE x₀ r hr y) = (jac d r).toReal * ∫ z, g z := by
  rw [← integral_map_equiv, map_affE, integral_smul_measure, smul_eq_mul]

theorem integrableOn_comp_affE {F : Type*} [NormedAddCommGroup F] {g : E d → F} {S : Set (E d)}
    (h : IntegrableOn g S) : IntegrableOn (g ∘ affE x₀ r hr) (affE x₀ r hr ⁻¹' S) := by
  rw [IntegrableOn, ← integrable_map_equiv, restrict_map_affE hr]
  exact h.smul_measure jac_ne_top

theorem memLp_comp_affE {F : Type*} [NormedAddCommGroup F] {g : E d → F} {S : Set (E d)}
    (h : MemLp g 2 (volume.restrict S)) :
    MemLp (g ∘ affE x₀ r hr) 2 (volume.restrict (affE x₀ r hr ⁻¹' S)) := by
  rw [← MeasurableEquiv.memLp_map_measure_iff, restrict_map_affE hr]
  exact h.smul_measure jac_ne_top

theorem ae_comp_affE {P : E d → Prop} {S : Set (E d)} (h : ∀ᵐ z ∂(volume.restrict S), P z) :
    ∀ᵐ y ∂(volume.restrict (affE x₀ r hr ⁻¹' S)), P (affE x₀ r hr y) := by
  refine ae_of_ae_map (affE x₀ r hr).measurable.aemeasurable ?_
  rw [restrict_map_affE hr]
  exact Measure.ae_smul_measure h _

omit hr in
theorem continuous_affE (hr : r ≠ 0) : Continuous (affE x₀ r hr) :=
  continuous_const.add (continuous_const_smul r)

theorem locallyIntegrableOn_comp_affE {F : Type*} [NormedAddCommGroup F] {g : E d → F}
    {U : Set (E d)} (hU : IsOpen U) (h : LocallyIntegrableOn g U) :
    LocallyIntegrableOn (g ∘ affE x₀ r hr) (affE x₀ r hr ⁻¹' U) := by
  rw [locallyIntegrableOn_iff (hU.preimage (continuous_affE hr)).isLocallyClosed]
  intro K hKs hK
  have h1 := (locallyIntegrableOn_iff hU.isLocallyClosed).1 h (affE x₀ r hr '' K)
    (image_subset_iff.2 hKs) (hK.image (continuous_affE hr))
  have h2 := integrableOn_comp_affE (x₀ := x₀) hr h1
  rwa [(affE x₀ r hr).preimage_image] at h2

theorem hasFDerivAt_affE (y : E d) :
    HasFDerivAt (affE x₀ r hr) (r • ContinuousLinearMap.id ℝ (E d)) y :=
  ((hasFDerivAt_id y).const_smul r).const_add x₀

omit hr in
theorem blowup_eq (f : E d → ℝ) (y : E d) (hr : r ≠ 0) :
    blowup f x₀ r y = r⁻¹ * f (affE x₀ r hr y) := by
  simp [blowup, affE_apply, div_eq_inv_mul]

/-- **Weak gradients of blow-ups.** -/
theorem hasWeakGradient_blowup {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d}
    (hf : HasWeakGradient U f G) :
    HasWeakGradient (affE x₀ r hr ⁻¹' U) (blowup f x₀ r) (G ∘ affE x₀ r hr) := by
  have hbl : blowup f x₀ r = fun y ↦ r⁻¹ * (f ∘ (affE x₀ r hr)) y := funext fun y ↦ blowup_eq f y hr
  refine GMTFoundations.HasWeakGradient.of_integral_eq ?_
    (locallyIntegrableOn_comp_affE hr hU hf.2.1)
    fun φ hφ hφc hφU v ↦ ?_
  · rw [hbl]
    exact (locallyIntegrableOn_comp_affE hr hU hf.1).smul r⁻¹
  -- the transported test function
  set ψ : E d → ℝ := fun z ↦ φ (r⁻¹ • (z - x₀)) with hψ
  have hψe : ∀ y, ψ ((affE x₀ r hr) y) = φ y := fun y ↦ by
    simp [hψ, affE_apply, smul_smul, inv_mul_cancel₀ hr]
  have hφψ : φ = ψ ∘ (affE x₀ r hr) := funext fun y ↦ (hψe y).symm
  have haff : ContDiff ℝ ∞ fun z : E d ↦ r⁻¹ • (z - x₀) :=
    (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hψs : ContDiff ℝ ∞ ψ := hφ.comp haff
  set h : E d ≃ₜ E d := (Homeomorph.addRight (-x₀)).trans (Homeomorph.smulOfNeZero r⁻¹
    (inv_ne_zero hr)) with hh
  have hhψ : ψ = φ ∘ h := funext fun z ↦ by simp [hψ, h, sub_eq_add_neg]
  have hψc : HasCompactSupport ψ := hhψ ▸ hφc.comp_homeomorph h
  have hψU : tsupport ψ ⊆ U := by
    rw [hhψ, tsupport_comp_eq_preimage]
    intro z hz
    have := hφU hz
    simp only [mem_preimage] at this
    convert this using 1
    simp [h, affE_apply, smul_smul, mul_inv_cancel₀ hr]
  have hder : ∀ y, fderiv ℝ φ y v = r * fderiv ℝ ψ ((affE x₀ r hr) y) v := fun y ↦ by
    rw [hφψ, fderiv_comp y ((hψs.differentiable (by simp)) _)
      (hasFDerivAt_affE hr y).differentiableAt, (hasFDerivAt_affE hr y).fderiv]
    simp
  have key := hf.integral_eq hψs hψc hψU v
  calc ∫ y, blowup f x₀ r y * fderiv ℝ φ y v
      = ∫ y, (fun z ↦ f z * fderiv ℝ ψ z v) ((affE x₀ r hr) y) := by
        congr 1; funext y
        rw [blowup_eq f y hr, hder]
        field_simp
    _ = (jac d r).toReal * ∫ z, f z * fderiv ℝ ψ z v :=
        integral_comp_affE (x₀ := x₀) hr (fun z ↦ f z * fderiv ℝ ψ z v)
    _ = -((jac d r).toReal * ∫ z, inner ℝ (G z) v * ψ z) := by rw [key, mul_neg]
    _ = -∫ y, (fun z ↦ inner ℝ (G z) v * ψ z) ((affE x₀ r hr) y) := by
        rw [integral_comp_affE (x₀ := x₀) hr (fun z ↦ inner ℝ (G z) v * ψ z)]
    _ = -∫ y, inner ℝ ((G ∘ (affE x₀ r hr)) y) v * φ y := by simp only [hψe, Function.comp]

theorem blowup_eq_fun (f : E d → ℝ) :
    blowup f x₀ r = fun y ↦ r⁻¹ * (f ∘ affE x₀ r hr) y := funext fun y ↦ blowup_eq f y hr

theorem memH1Loc_blowup {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d}
    (hf : MemH1Loc U f G) :
    MemH1Loc (affE x₀ r hr ⁻¹' U) (blowup f x₀ r) (G ∘ affE x₀ r hr) := by
  refine ⟨hasWeakGradient_blowup hr hU hf.1, fun K hK hKc ↦ ?_⟩
  have h := hf.2 (affE x₀ r hr '' K) (image_subset_iff.2 hK) (hKc.image (continuous_affE hr))
  have h1 := memLp_comp_affE (x₀ := x₀) hr h.1
  have h2 := memLp_comp_affE (x₀ := x₀) hr h.2
  rw [(affE x₀ r hr).preimage_image] at h1 h2
  rw [blowup_eq_fun hr]
  exact ⟨h1.const_mul r⁻¹, h2⟩

theorem mem_posSet_blowup (hr0 : 0 < r) {f : E d → ℝ} {S : Set (E d)} {y : E d} :
    y ∈ posSet (blowup f x₀ r) (affE x₀ r hr ⁻¹' S) ↔ affE x₀ r hr y ∈ posSet f S := by
  simp only [posSet, mem_setOf_eq, mem_preimage, blowup, affE_apply, div_pos_iff_of_pos_right hr0]

/-- **Scaling of the energy.** -/
theorem energyJ_blowup (hr0 : 0 < r) (S : Set (E d)) (Q f : E d → ℝ) (G : E d → E d) :
    energyJ (affE x₀ r hr ⁻¹' S) (fun y ↦ Q (affE x₀ r hr y)) (blowup f x₀ r)
      (G ∘ affE x₀ r hr) = jac d r * energyJ S Q f G := by
  unfold energyJ
  rw [← setLIntegral_comp_affE hr]
  refine lintegral_congr fun y ↦ ?_
  have hind : (posSet (blowup f x₀ r) (affE x₀ r hr ⁻¹' S)).indicator (1 : E d → ℝ) y =
      (posSet f S).indicator 1 (affE x₀ r hr y) := by
    by_cases h : affE x₀ r hr y ∈ posSet f S
    · rw [indicator_of_mem h, indicator_of_mem ((mem_posSet_blowup hr hr0).2 h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' ↦ h ((mem_posSet_blowup hr hr0).1 h'))]
  rw [hind, Function.comp_apply]

theorem preimage_ball_affE (hr0 : 0 < r) (y : E d) (R : ℝ) :
    affE x₀ r hr ⁻¹' ball (affE x₀ r hr y) (r * R) = ball y R := by
  ext z
  simp only [mem_preimage, Metric.mem_ball, affE_apply, dist_eq_norm, add_sub_add_left_eq_sub,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
  exact mul_lt_mul_iff_right₀ hr0

theorem preimage_closedBall_affE (hr0 : 0 < r) (y : E d) (R : ℝ) :
    affE x₀ r hr ⁻¹' closedBall (affE x₀ r hr y) (r * R) = closedBall y R := by
  ext z
  simp only [mem_preimage, Metric.mem_closedBall, affE_apply, dist_eq_norm,
    add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
  exact mul_le_mul_iff_right₀ hr0

omit hr in
theorem inv_ne_zero' (hr : r ≠ 0) : r⁻¹ ≠ 0 := inv_ne_zero hr

theorem affE_affE_inv (z : E d) :
    affE x₀ r hr (affE (-(r⁻¹ • x₀)) r⁻¹ (inv_ne_zero hr) z) = z := by
  simp [affE_apply, smul_add, smul_smul, mul_inv_cancel₀ hr]

theorem affE_inv_affE (y : E d) :
    affE (-(r⁻¹ • x₀)) r⁻¹ (inv_ne_zero hr) (affE x₀ r hr y) = y := by
  simp [affE_apply, smul_add, smul_smul, inv_mul_cancel₀ hr]

theorem blowup_blowup_inv (f : E d → ℝ) :
    blowup (blowup f x₀ r) (-(r⁻¹ • x₀)) r⁻¹ = f := by
  funext z
  have := affE_affE_inv (x₀ := x₀) hr z
  simp only [affE_apply] at this
  simp only [blowup, this]
  field_simp

theorem blowup_inv_blowup (f : E d → ℝ) :
    blowup (blowup f (-(r⁻¹ • x₀)) r⁻¹) x₀ r = f := by
  funext y
  have := affE_inv_affE (x₀ := x₀) hr y
  simp only [affE_apply] at this
  simp only [blowup, this]
  field_simp

theorem preimage_preimage_affE (U : Set (E d)) :
    affE (-(r⁻¹ • x₀)) r⁻¹ (inv_ne_zero hr) ⁻¹' (affE x₀ r hr ⁻¹' U) = U := by
  ext z; simp only [mem_preimage, affE_affE_inv hr]

omit hr in
theorem contDiff_affE (hr : r ≠ 0) : ContDiff ℝ ⊤ (affE x₀ r hr) :=
  contDiff_const.add (contDiff_id.const_smul r)

/-- **Scaling of the Laplacian**: `Δ u_{x₀,r}(y) = r Δu(x₀ + r y)`. -/
theorem laplacian_blowup {u : E d → ℝ} {y : E d} (hu : ContDiffAt ℝ 2 u (affE x₀ r hr y)) :
    Δ (blowup u x₀ r) y = r * Δ u (affE x₀ r hr y) := by
  have hb : ContDiffAt ℝ 2 (blowup u x₀ r) y := by
    rw [blowup_eq_fun hr]
    exact contDiffAt_const.mul (hu.comp y ((contDiff_affE hr).contDiffAt.of_le le_top))
  rw [← DirectionalStable.coordLap_eq_laplacian hb, ← DirectionalStable.coordLap_eq_laplacian hu]
  unfold LongTime.coordLap
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  set v := LongTime.coordVec (d := d) i
  have hev : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 u (affE x₀ r hr z) :=
    (continuous_affE hr).continuousAt.eventually (hu.eventually (by simp))
  have hloc : (fun z ↦ fderiv ℝ (blowup u x₀ r) z v) =ᶠ[𝓝 y]
      fun z ↦ fderiv ℝ u (affE x₀ r hr z) v := by
    filter_upwards [hev] with z hz
    have hd : HasFDerivAt u (fderiv ℝ u (affE x₀ r hr z)) (affE x₀ r hr z) :=
      (hz.differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasFDerivAt (blowup u x₀ r)
        (r⁻¹ • (fderiv ℝ u (affE x₀ r hr z)).comp (r • ContinuousLinearMap.id ℝ (E d))) z := by
      rw [blowup_eq_fun hr]
      exact (hd.comp z (hasFDerivAt_affE hr z)).const_mul r⁻¹
    rw [h2.fderiv]
    simp [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hr]
  rw [hloc.fderiv_eq]
  have hg : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w v) (affE x₀ r hr y) :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  have h3 : HasFDerivAt (fun z ↦ fderiv ℝ u (affE x₀ r hr z) v)
      ((fderiv ℝ (fun w ↦ fderiv ℝ u w v) (affE x₀ r hr y)).comp
        (r • ContinuousLinearMap.id ℝ (E d))) y :=
    hg.hasFDerivAt.comp y (hasFDerivAt_affE hr y)
  rw [h3.fderiv]
  simp

/-- **Scaling of the one-sided minimality inequality** (generic in the one-sided constraint
`rel`, which is invariant under division by positive constants). -/
theorem blowup_minimality_scaled {U : Set (E d)} (hU : IsOpen U) {Q u : E d → ℝ} (hr0 : 0 < r)
    (rel : ℝ → ℝ → Prop) (hrel : ∀ a b c : ℝ, 0 < c → rel a b → rel (a / c) (b / c))
    (hmin : ∀ (x : E d) (R : ℝ), 0 < R → closedBall x R ⊆ U →
      ∀ (Gu : E d → E d) (w : E d → ℝ) (Gw : E d → E d), MemH1Loc U u Gu → MemH1Loc U w Gw →
        (∀ᵐ y ∂(volume.restrict U), rel (w y) (u y)) →
        (∀ᵐ y ∂(volume.restrict (U \ ball x R)), w y = u y) →
        energyJ (ball x R) Q u Gu ≤ energyJ (ball x R) Q w Gw) :
    ∀ (y : E d) (R : ℝ), 0 < R → closedBall y R ⊆ affE x₀ r hr ⁻¹' U →
      ∀ (Gu : E d → E d) (w : E d → ℝ) (Gw : E d → E d),
        MemH1Loc (affE x₀ r hr ⁻¹' U) (blowup u x₀ r) Gu →
        MemH1Loc (affE x₀ r hr ⁻¹' U) w Gw →
        (∀ᵐ z ∂(volume.restrict (affE x₀ r hr ⁻¹' U)), rel (w z) (blowup u x₀ r z)) →
        (∀ᵐ z ∂(volume.restrict (affE x₀ r hr ⁻¹' U \ ball y R)),
          w z = blowup u x₀ r z) →
        energyJ (ball y R) (fun z ↦ Q (affE x₀ r hr z)) (blowup u x₀ r) Gu ≤
          energyJ (ball y R) (fun z ↦ Q (affE x₀ r hr z)) w Gw := by
  intro y R hR hB Gu w Gw hGu hGw hrelae heqae
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr
  have hr0' : 0 < r⁻¹ := inv_pos.2 hr0
  set e := affE x₀ r hr with he
  set e' := affE (-(r⁻¹ • x₀)) r⁻¹ hr' with he'
  have hee' : ∀ z, e (e' z) = z := affE_affE_inv hr
  have he'e : ∀ z, e' (e z) = z := affE_inv_affE hr
  have hUo : IsOpen (e ⁻¹' U) := hU.preimage (continuous_affE hr)
  have hpre : e' ⁻¹' (e ⁻¹' U) = U := preimage_preimage_affE hr U
  have hball : e ⁻¹' ball (e y) (r * R) = ball y R := preimage_ball_affE hr hr0 y R
  have hB' : closedBall (e y) (r * R) ⊆ U := by
    intro z hz
    have h1 : e' z ∈ e ⁻¹' closedBall (e y) (r * R) := by
      rw [mem_preimage, hee']; exact hz
    rw [preimage_closedBall_affE hr hr0 y R] at h1
    have h2 := hB h1
    rwa [mem_preimage, hee'] at h2
  -- transported gradient of `u` and competitor
  have hGu'' : MemH1Loc U u (Gu ∘ e') := by
    have := memH1Loc_blowup (x₀ := -(r⁻¹ • x₀)) hr' hUo hGu
    rwa [hpre, blowup_blowup_inv hr] at this
  have hGW : MemH1Loc U (blowup w (-(r⁻¹ • x₀)) r⁻¹) (Gw ∘ e') := by
    have := memH1Loc_blowup (x₀ := -(r⁻¹ • x₀)) hr' hUo hGw
    rwa [hpre] at this
  have hWu : ∀ z, blowup (blowup u x₀ r) (-(r⁻¹ • x₀)) r⁻¹ z = u z := fun z ↦
    congrFun (blowup_blowup_inv hr u) z
  have hrel' : ∀ᵐ z ∂(volume.restrict U), rel (blowup w (-(r⁻¹ • x₀)) r⁻¹ z) (u z) := by
    have := ae_comp_affE (x₀ := -(r⁻¹ • x₀)) hr' hrelae
    rw [hpre] at this
    filter_upwards [this] with z hz
    rw [← hWu z]
    exact hrel _ _ _ hr0' hz
  have heq' : ∀ᵐ z ∂(volume.restrict (U \ ball (e y) (r * R))),
      blowup w (-(r⁻¹ • x₀)) r⁻¹ z = u z := by
    have := ae_comp_affE (x₀ := -(r⁻¹ • x₀)) hr' heqae
    rw [← hball, ← preimage_diff, preimage_preimage_affE hr] at this
    filter_upwards [this] with z hz
    rw [← hWu z]
    simp only [blowup, affE_apply] at hz ⊢
    rw [hz]
  have key := hmin (e y) (r * R) (mul_pos hr0 hR) hB' _ _ _ hGu'' hGW hrel' heq'
  have hJu := energyJ_blowup (x₀ := x₀) hr hr0 (ball (e y) (r * R)) Q u (Gu ∘ e')
  have hJw := energyJ_blowup (x₀ := x₀) hr hr0 (ball (e y) (r * R)) Q
    (blowup w (-(r⁻¹ • x₀)) r⁻¹) (Gw ∘ e')
  have hcomp : ∀ G : E d → E d, (G ∘ e') ∘ e = G := fun G ↦ funext fun z ↦ by
    simp [Function.comp, he'e]
  rw [hball, hcomp] at hJu hJw
  rw [blowup_inv_blowup hr] at hJw
  rw [hJu, hJw]
  gcongr

theorem posSet_blowup (hr0 : 0 < r) (f : E d → ℝ) (U : Set (E d)) :
    posSet (blowup f x₀ r) (affE x₀ r hr ⁻¹' U) = affE x₀ r hr ⁻¹' posSet f U := by
  ext y; exact mem_posSet_blowup hr hr0

/-- The regularity part (i) of Definition 2.11 is invariant under blow-up. -/
theorem blowup_regular {U : Set (E d)} {u : E d → ℝ} (hr0 : 0 < r)
    (hopen : IsOpen (posSet u U)) (hc2 : ContDiffOn ℝ 2 u (posSet u U))
    (hΔ : ∀ x ∈ posSet u U, Δ u x = 0) :
    IsOpen (posSet (blowup u x₀ r) (affE x₀ r hr ⁻¹' U)) ∧
      ContDiffOn ℝ 2 (blowup u x₀ r) (posSet (blowup u x₀ r) (affE x₀ r hr ⁻¹' U)) ∧
      ∀ y ∈ posSet (blowup u x₀ r) (affE x₀ r hr ⁻¹' U), Δ (blowup u x₀ r) y = 0 := by
  rw [posSet_blowup hr hr0]
  refine ⟨hopen.preimage (continuous_affE hr), ?_, fun y hy ↦ ?_⟩
  · rw [blowup_eq_fun hr]
    exact contDiffOn_const.mul (hc2.comp ((contDiff_affE hr).contDiffOn.of_le le_top)
      fun y hy ↦ hy)
  · rw [laplacian_blowup hr (hc2.contDiffAt (hopen.mem_nhds hy)), hΔ _ hy, mul_zero]

end Affine

end Scaling

/-! ### Corollary 2.13: blow-ups -/

section Blowup

/-- The rescaled domain `U_{x₀,r} = {y : x₀ + r y ∈ U}` of the blow-up. -/
def blowupDomain (U : Set (E d)) (x₀ : E d) (r : ℝ) : Set (E d) := {y | x₀ + r • y ∈ U}

theorem continuous_affine (x₀ : E d) (r : ℝ) : Continuous fun y : E d ↦ x₀ + r • y :=
  continuous_const.add (continuous_const_smul r)

theorem isOpen_blowupDomain {U : Set (E d)} (hU : IsOpen U) (x₀ : E d) (r : ℝ) :
    IsOpen (blowupDomain U x₀ r) :=
  hU.preimage (continuous_affine x₀ r)

theorem dist_blowup_le {u : E d → ℝ} {x₀ : E d} {r : ℝ} (hr : 0 < r) {L : ℝ≥0} {S : Set (E d)}
    (hL : LipschitzOnWith L u S) {a b : E d} (ha : x₀ + r • a ∈ S) (hb : x₀ + r • b ∈ S) :
    dist (blowup u x₀ r a) (blowup u x₀ r b) ≤ L * dist a b := by
  have h := hL.dist_le_mul _ ha _ hb
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr] at h
  unfold blowup
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr, div_le_iff₀ hr, ← Real.dist_eq]
  linarith

theorem blowup_locallyLipschitzOn {U : Set (E d)} {u : E d → ℝ} (huL : LocallyLipschitzOn U u)
    (x₀ : E d) {r : ℝ} (hr : 0 < r) :
    LocallyLipschitzOn (blowupDomain U x₀ r) (blowup u x₀ r) := by
  intro y hy
  obtain ⟨K, t, ht, hK⟩ := huL hy
  obtain ⟨o, ho, hyo, hot⟩ := mem_nhdsWithin.1 ht
  refine ⟨K, (fun z ↦ x₀ + r • z) ⁻¹' t, mem_nhdsWithin.2 ⟨(fun z ↦ x₀ + r • z) ⁻¹' o,
    ho.preimage (continuous_affine x₀ r), hyo, fun z hz ↦ hot ⟨hz.1, hz.2⟩⟩, ?_⟩
  exact LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ dist_blowup_le hr hK ha hb

/-- **Scaling invariance of directional minimality** (implicit in the proof of Corollary 2.13):
the blow-up `u_{x₀,r}` is a downward minimizer of `J_{Q(x₀ + r ·)}` in `U_{x₀,r}`. -/
theorem blowup_isDownwardMinimizer_scaled {U : Set (E d)} (hU : IsOpen U) {Q u : E d → ℝ}
    (hmin : IsDownwardMinimizer U Q u) (x₀ : E d) {r : ℝ} (hr : 0 < r) :
    IsDownwardMinimizer (blowupDomain U x₀ r) (fun y ↦ Q (x₀ + r • y)) (blowup u x₀ r) := by
  obtain ⟨⟨G, hG⟩, hopen, hc2, hΔ, hmin'⟩ := hmin
  obtain ⟨h1, h2, h3⟩ := blowup_regular (x₀ := x₀) hr.ne' hr hopen hc2 hΔ
  exact ⟨⟨_, memH1Loc_blowup hr.ne' hU hG⟩, h1, h2, h3, blowup_minimality_scaled hr.ne' hU hr
    (· ≤ ·) (fun a b c hc h ↦ div_le_div_of_nonneg_right h hc.le) hmin'⟩

/-- **Scaling invariance of directional minimality**, upward case. -/
theorem blowup_isUpwardMinimizer_scaled {U : Set (E d)} (hU : IsOpen U) {Q u : E d → ℝ}
    (hmin : IsUpwardMinimizer U Q u) (x₀ : E d) {r : ℝ} (hr : 0 < r) :
    IsUpwardMinimizer (blowupDomain U x₀ r) (fun y ↦ Q (x₀ + r • y)) (blowup u x₀ r) := by
  obtain ⟨⟨G, hG⟩, hopen, hc2, hΔ, hmin'⟩ := hmin
  obtain ⟨h1, h2, h3⟩ := blowup_regular (x₀ := x₀) hr.ne' hr hopen hc2 hΔ
  exact ⟨⟨_, memH1Loc_blowup hr.ne' hU hG⟩, h1, h2, h3, blowup_minimality_scaled hr.ne' hU hr
    (fun a b ↦ b ≤ a) (fun a b c hc h ↦ div_le_div_of_nonneg_right h hc.le) hmin'⟩

/-- The blow-up sequence along `rₙ → 0⁺` satisfies the hypotheses of Lemma 2.12 on the
exhausting domains `U_{x₀,rₙ}`, with `Qₙ = Q(x₀ + rₙ ·) → Q(x₀)`. -/
theorem exhaustData_blowup {U : Set (E d)} (hU : IsOpen U) {Q u : E d → ℝ} {Qmax : ℝ}
    (hQc : ContinuousOn Q U) (hQb : ∀ y ∈ U, |Q y| ≤ Qmax) (huL : LocallyLipschitzOn U u)
    {x₀ : E d} (hx₀ : x₀ ∈ U) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    {v : E d → ℝ} (hv : TendstoLocallyUniformly (fun n ↦ blowup u x₀ (r n)) v atTop) :
    ExhaustData (fun n ↦ blowup u x₀ (r n)) (fun n y ↦ Q (x₀ + r n • y))
      (fun n ↦ blowupDomain U x₀ (r n)) v (fun _ ↦ Q x₀) Qmax := by
  -- a Lipschitz ball around `x₀`
  obtain ⟨L, t, ht, hL⟩ := huL hx₀
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhdsWithin_iff.1 ht
  obtain ⟨δ', hδ', hδU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set η := min δ δ' with hη
  have hη0 : 0 < η := lt_min hδ hδ'
  have hηU : ball x₀ η ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hδU
  have hηt : ball x₀ η ⊆ t := fun z hz ↦
    hδt ⟨ball_subset_ball (min_le_left _ _) hz, hηU hz⟩
  -- points of `B_ρ(0)` are mapped into `B_η(x₀)` for large `n`
  have hin : ∀ ρ : ℝ, 0 ≤ ρ → ∀ᶠ n in atTop, ∀ y ∈ closedBall (0 : E d) ρ,
      x₀ + r n • y ∈ ball x₀ η := by
    intro ρ hρ
    have hlt : ∀ᶠ n in atTop, r n < η / (ρ + 1) :=
      (tendsto_order.1 hr0).2 _ (div_pos hη0 (by linarith))
    filter_upwards [hlt] with n hn y hy
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hr n)]
    rw [mem_closedBall, dist_zero_right] at hy
    rw [lt_div_iff₀ (by linarith)] at hn
    nlinarith [hr n, norm_nonneg y]
  refine ⟨fun n ↦ isOpen_blowupDomain hU x₀ (r n), fun K hK ↦ ?_, fun y ↦ ?_,
    fun n ↦ blowup_locallyLipschitzOn huL x₀ (hr n), hv, fun n ↦ ?_, fun n y hy ↦ hQb _ hy,
    fun y ↦ ?_⟩
  · obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
    filter_upwards [hin (max ρ 0) (le_max_right _ _)] with n hn y hy
    exact hηU (hn y (closedBall_subset_closedBall (le_max_left _ _) (hρ hy)))
  · refine ⟨1, one_pos, L, ?_⟩
    filter_upwards [hin (‖y‖ + 1) (by positivity)] with n hn
    have hsub : ∀ z ∈ ball y 1, x₀ + r n • z ∈ t := fun z hz ↦ hηt (hn z (by
      rw [mem_closedBall, dist_zero_right]
      have := norm_le_norm_add_norm_sub' z y
      rw [mem_ball, dist_eq_norm] at hz
      linarith))
    exact LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦
      dist_blowup_le (hr n) hL (hsub a ha) (hsub b hb)
  · exact hQc.comp (continuous_affine x₀ (r n)).continuousOn fun y hy ↦ hy
  · have hA : Tendsto (fun n ↦ x₀ + r n • y) atTop (𝓝 x₀) := by
      simpa using tendsto_const_nhds.add (hr0.smul_const y)
    exact (hQc.continuousAt (hU.mem_nhds hx₀)).tendsto.comp hA

/-- **Corollary 2.13(i)**. Let `u` be locally Lipschitz in `U`,
`Q` continuous and bounded on `U` (the paper: `Q ∈ C^{0,1}`, `Q_min ≤ Q ≤ Q_max`), and
`x₀ ∈ U`. If `u` is a downward minimizer of `J_Q` in `U`, then every blow-up limit `v` of `u` at
`x₀` is a downward minimizer of `J_{Q(x₀)}` in `ℝᵈ`. -/
theorem blowup_isDownwardMinimizer {U : Set (E d)} (hU : IsOpen U) {Q u : E d → ℝ} {Qmax : ℝ}
    (hQc : ContinuousOn Q U) (hQb : ∀ y ∈ U, |Q y| ≤ Qmax) (huL : LocallyLipschitzOn U u)
    {x₀ : E d} (hx₀ : x₀ ∈ U) (hmin : IsDownwardMinimizer U Q u) {v : E d → ℝ}
    (hv : IsBlowupLimit u x₀ v) : IsDownwardMinimizer univ (fun _ ↦ Q x₀) v := by
  obtain ⟨r, hr, hr0, hconv⟩ := hv
  exact isDownwardMinimizer_of_exhaust (exhaustData_blowup hU hQc hQb huL hx₀ hr hr0 hconv)
    fun n ↦ blowup_isDownwardMinimizer_scaled hU hmin x₀ (hr n)

/-- **Corollary 2.13(ii)**, without the inner-variational hypothesis. -/
theorem blowup_isUpwardMinimizer' {U : Set (E d)} (hU : IsOpen U) {Q u : E d → ℝ} {Qmax : ℝ}
    (hQc : ContinuousOn Q U) (hQb : ∀ y ∈ U, |Q y| ≤ Qmax) (huL : LocallyLipschitzOn U u)
    {x₀ : E d} (hx₀ : x₀ ∈ U) (hmin : IsUpwardMinimizer U Q u) {v : E d → ℝ}
    (hv : IsBlowupLimit u x₀ v) : IsUpwardMinimizer univ (fun _ ↦ Q x₀) v := by
  obtain ⟨r, hr, hr0, hconv⟩ := hv
  exact isUpwardMinimizer_of_exhaust (exhaustData_blowup hU hQc hQb huL hx₀ hr hr0 hconv)
    fun n ↦ blowup_isUpwardMinimizer_scaled hU hmin x₀ (hr n)

/-- **Corollary 2.13(ii)**, with the paper's inner-variational
hypothesis (not needed by the proof, `blowup_isUpwardMinimizer'`). -/
theorem blowup_isUpwardMinimizer {U : Set (E d)} (hU : IsOpen U) {Q u : E d → ℝ} {Qmax : ℝ}
    (hQc : ContinuousOn Q U) (hQb : ∀ y ∈ U, |Q y| ≤ Qmax) (huL : LocallyLipschitzOn U u)
    {x₀ : E d} (hx₀ : x₀ ∈ U) (hmin : IsUpwardMinimizer U Q u) {χ : E d → ℝ}
    (_hinner : IsInnerVarSolution U Q u χ) {v : E d → ℝ} (hv : IsBlowupLimit u x₀ v) :
    IsUpwardMinimizer univ (fun _ ↦ Q x₀) v :=
  blowup_isUpwardMinimizer' hU hQc hQb huL hx₀ hmin hv

end Blowup

end DirectionalStable

end PerronVariational

end
