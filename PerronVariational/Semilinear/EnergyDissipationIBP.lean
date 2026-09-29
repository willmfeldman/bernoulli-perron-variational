/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Sobolev -- shake: keep
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import GMTFoundations.Sobolev.Cutoff
import GMTFoundations.Sobolev.Lattice
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.Order.CompletePartialOrder
import PerronVariational.Inner.Mollify
import PerronVariational.Semilinear.Calculus

/-!
# Energy dissipation, part 1: interior integration by parts and truncations

Tools for the proof of the energy dissipation inequality (A.1), i.e. (3.8), of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981:
every integration by parts is performed against a test function with
compact support in `U`, obtained by truncating (in the values) a function that vanishes on `∂U`.

* `hasWeakGradient_of_contDiffOn`: a `C¹(U)` function has its classical gradient as weak gradient.
* `HasWeakGradient.ae_eq`: uniqueness of weak gradients.
* `HasWeakGradient.ae_eq_zero_of_eq_zero`: `∇w = 0` a.e. on `{w = 0}` for weak gradients.
* `integral_laplacian_mul_eq_neg_of_hasWeakGradient`: `∫ Δf ψ = -∫ ∇f · Ψ` for `f ∈ C²(U)` and
  `ψ ∈ H¹` with weak gradient `Ψ`, both vanishing off a compact subset of `U`.
* `trunc σ`: a `C¹` truncation, `0` on `[-σ, σ]`, with `0 ≤ trunc' ≤ 1`, `trunc' → 1_{s ≠ 0}` and
  `trunc σ s → s` as `σ → 0`; `truncPrim σ` its primitive (nonnegative).

This file must not import `PerronVariational.Registry.Semilinear`, whose energy dissipation
statement is proved from it.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace ContDiff

@[expose] public section

namespace PerronVariational

namespace EnergyDissipation

variable {d : ℕ}

/-! ### Integrability helpers -/

section Integrability

variable {X F : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [T2Space X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup F]

/-- A function continuous on a compact set and vanishing off it is integrable. -/
theorem integrable_of_continuousOn_of_eq_zero {K : Set X} (hK : IsCompact K) {f : X → F}
    (hf : ContinuousOn f K) (h0 : ∀ x ∉ K, f x = 0) : Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset fun x hx ↦
    by_contra fun h ↦ hx (h0 x h)).1 (hf.integrableOn_compact hK)

omit [OpensMeasurableSpace X] [T2Space X] [IsFiniteMeasureOnCompacts μ] in
/-- A function locally integrable on `U` and vanishing off a compact subset of `U` is
integrable. -/
theorem integrable_of_locallyIntegrableOn_of_eq_zero {U K : Set X} {f : X → F}
    (hf : LocallyIntegrableOn f U μ) (hK : IsCompact K) (hKU : K ⊆ U) (h0 : ∀ x ∉ K, f x = 0) :
    Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset fun x hx ↦
    by_contra fun h ↦ hx (h0 x h)).1 (hf.integrableOn_compact_subset hKU hK)

end Integrability

/-- `⟪∇f(x), v⟫ = Df(x) v`. -/
theorem inner_gradient_eq_fderiv' (f : E d → ℝ) (x v : E d) : ⟪∇ f x, v⟫ = fderiv ℝ f x v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

theorem continuousOn_gradient_of_contDiffOn' {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : ContDiffOn ℝ 1 f U) : ContinuousOn (∇ f) U :=
  (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp_continuousOn
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl)

/-! ### Weak gradients -/

/-- A `C¹` function on the open set `U` has its classical gradient as weak gradient in `U`. -/
theorem hasWeakGradient_of_contDiffOn {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : ContDiffOn ℝ 1 f U) : HasWeakGradient U f (∇ f) := by
  refine GMTFoundations.HasWeakGradient.of_integral_eq
    (hf.continuousOn.locallyIntegrableOn hU.measurableSet)
    ((continuousOn_gradient_of_contDiffOn' hU hf).locallyIntegrableOn hU.measurableSet)
    fun φ hφ hφc hφU v ↦ ?_
  have hK : IsCompact (tsupport φ) := hφc
  have hdf : ∀ x ∈ tsupport φ, DifferentiableAt ℝ f x := fun x hx ↦
    (hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hφU hx))
  have hcf : ContinuousOn f (tsupport φ) := hf.continuousOn.mono hφU
  have hcdf : ContinuousOn (fun x ↦ fderiv ℝ f x v) (tsupport φ) :=
    ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).mono hφU
  have hdφ : Continuous (fun x ↦ fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun x ↦ fderiv ℝ f x v * φ x) :=
    integrable_of_continuousOn_of_eq_zero hK (hcdf.mul hφ.continuous.continuousOn)
      fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
  have i2 : Integrable (fun x ↦ f x * fderiv ℝ φ x v) :=
    integrable_of_continuousOn_of_eq_zero hK (hcf.mul hdφ.continuousOn)
      fun x hx ↦ by simp [GMTFoundations.fderiv_apply_eq_zero_of_notMem_tsupport hx]
  have i3 : Integrable (fun x ↦ f x * φ x) :=
    integrable_of_continuousOn_of_eq_zero hK (hcf.mul hφ.continuous.continuousOn)
      fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3 hdf
    fun x _ ↦ (hφ.differentiable (by simp)) x]
  simp_rw [inner_gradient_eq_fderiv']

/-- **Uniqueness of weak gradients.** -/
theorem HasWeakGradient.ae_eq {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G₁ G₂ : E d → E d}
    (h₁ : HasWeakGradient U f G₁) (h₂ : HasWeakGradient U f G₂) :
    ∀ᵐ x ∂(volume.restrict U), G₁ x = G₂ x := by
  have key : ∀ v : E d, ∀ᵐ x ∂(volume : Measure (E d)),
      x ∈ U → ⟪G₁ x, v⟫ - ⟪G₂ x, v⟫ = 0 := by
    intro v
    have hl1 := GMTFoundations.locallyIntegrableOn_inner_apply h₁.2.1 v
    have hl2 := GMTFoundations.locallyIntegrableOn_inner_apply h₂.2.1 v
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hl1.sub hl2) fun φ hφ hφc hφU ↦ ?_
    have e1 := h₁.integral_eq hφ hφc hφU v
    have e2 := h₂.integral_eq hφ hφc hφU v
    have i1 := GMTFoundations.integrable_inner_mul h₁.2.1 hφ.continuous hφc hφU v
    have i2 := GMTFoundations.integrable_inner_mul h₂.2.1 hφ.continuous hφc hφU v
    have : ∫ x, φ x • (⟪G₁ x, v⟫ - ⟪G₂ x, v⟫) =
        (∫ x, ⟪G₁ x, v⟫ * φ x) - ∫ x, ⟪G₂ x, v⟫ * φ x := by
      rw [← integral_sub i1 i2]
      congr 1; funext x; simp only [smul_eq_mul]; ring
    rw [this]
    linarith
  have hall : ∀ᵐ x ∂(volume : Measure (E d)), ∀ i : Fin d,
      x ∈ U → ⟪G₁ x, EuclideanSpace.single i (1 : ℝ)⟫ -
        ⟪G₂ x, EuclideanSpace.single i (1 : ℝ)⟫ = 0 :=
    ae_all_iff.2 fun i ↦ key _
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [hall] with x hx hxU
  have hz : G₁ x - G₂ x = 0 := by
    ext i
    have := hx i hxU
    rw [← inner_sub_left, EuclideanSpace.inner_single_right] at this
    simpa using this
  exact sub_eq_zero.1 hz

/-- **Weak gradients vanish a.e. on the zero set.** If `W` is a weak gradient of `w` in `U`, then
`W = 0` a.e. on `{w = 0} ∩ U`. -/
theorem HasWeakGradient.ae_eq_zero_of_eq_zero {U : Set (E d)} (hU : IsOpen U) {w : E d → ℝ}
    {W : E d → E d} (hw : HasWeakGradient U w W) :
    ∀ᵐ x ∂(volume.restrict U), w x = 0 → W x = 0 := by
  have h1 := hw.posPart hU
  have h2 := hw.neg.posPart hU
  have h3 := (h1.sub h2).congr_fun_ae (w := w)
    (Eventually.of_forall fun x ↦ max_zero_sub_eq_self (w x))
  filter_upwards [HasWeakGradient.ae_eq hU h3 hw] with x hx h0
  rw [← hx]
  simp [h0]

/-! ### Integration by parts against an `H¹` function with compact support -/

/-- **Integration by parts against a compactly supported `H¹` function.** For `f ∈ C²(U)` and
`ψ` with weak gradient `Ψ` in `U`, both vanishing off a compact `K ⊆ U`,
`∫ Δf ψ = -∫ ∇f · Ψ`. -/
theorem integral_laplacian_mul_eq_neg_of_hasWeakGradient {U : Set (E d)} (hU : IsOpen U)
    {f : E d → ℝ} (hf : ContDiffOn ℝ 2 f U) {ψ : E d → ℝ} {Ψ : E d → E d}
    (hψ : HasWeakGradient U ψ Ψ) {K : Set (E d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hψ0 : ∀ x ∉ K, ψ x = 0) (hΨ0 : ∀ x ∉ K, Ψ x = 0) :
    ∫ x, Δ f x * ψ x = -∫ x, ⟪∇ f x, Ψ x⟫ := by
  classical
  have hψi : Integrable ψ := integrable_of_locallyIntegrableOn_of_eq_zero hψ.1 hK hKU hψ0
  have hΨi : Integrable Ψ := integrable_of_locallyIntegrableOn_of_eq_zero hψ.2.1 hK hKU hΨ0
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨θ, hθ, hθc, hθU, -, hθ1⟩ := GMTFoundations.exists_smooth_cutoff hK.cthickening hU hδU
  set e := stdOrthonormalBasis ℝ (E d) with hedef
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  set D : Fin (Module.finrank ℝ (E d)) → E d → ℝ := fun i x ↦ fderiv ℝ f x (e i) with hDdef
  have hD : ∀ i, ContDiffOn ℝ 1 (D i) U := fun i ↦ hf1.clm_apply contDiffOn_const
  set ζ : Fin (Module.finrank ℝ (E d)) → E d → ℝ := fun i x ↦ θ x * D i x with hζdef
  have hζ : ∀ i, ContDiff ℝ 1 (ζ i) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hθ.of_le (by simp)).contDiffAt.mul ((hD i).contDiffAt (hU.mem_nhds hx))
    · have hxθ : x ∉ tsupport θ := fun h ↦ hx (hθU h)
      have : ζ i =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [(isClosed_tsupport θ).isOpen_compl.mem_nhds hxθ] with y hy
        simp [ζ, image_eq_zero_of_notMem_tsupport hy]
      exact contDiffAt_const.congr_of_eventuallyEq this
  have hζc : ∀ i, HasCompactSupport (ζ i) := fun i ↦ hθc.mul_right
  have hζU : ∀ i, tsupport (ζ i) ⊆ U := fun i ↦ (tsupport_mul_subset_left).trans hθU
  have hζeq : ∀ i, ∀ x ∈ K, ζ i =ᶠ[𝓝 x] D i := by
    intro i x hx
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ K hx)] with y hy
    simp [ζ, hθ1 y (thickening_subset_cthickening _ _ hy)]
  -- the weak identity tested against `ζ i`
  have hkey : ∀ i, ∫ x, ⟪Ψ x, e i⟫ * ζ i x + ψ x * fderiv ℝ (ζ i) x (e i) = 0 := by
    intro i
    obtain ⟨C, hC⟩ := (hζ i).lipschitzWith_of_hasCompactSupport (hζc i) one_ne_zero
    have ha : Integrable (fun x ↦ ⟪Ψ x, e i⟫) := by
      have := (innerSL ℝ (e i)).integrable_comp hΨi
      simpa [innerSL_apply_apply, real_inner_comm] using this
    have hg : Integrable (fun x ↦ ψ x • e i) := hψi.smul_const (e i)
    have h := LongTime.firstOrderFunctional_eq_zero_of_bumps (μ := volume)
      (a := fun x ↦ ⟪Ψ x, e i⟫) (g := fun x ↦ ψ x • e i) Measure.AbsolutelyContinuous.rfl ha hg
      hU dense_univ ?_ ⟨C, hC⟩ (hζc i) (hζU i)
    · simpa [LongTime.firstOrderFunctional, map_smul, smul_eq_mul] using h
    · intro n q _ hq
      set φ : E d → ℝ := fun x ↦ LongTime.moll d n (x - q) with hφdef
      have hφ : ContDiff ℝ ∞ φ :=
        (LongTime.contDiff_moll n).comp (contDiff_id.sub contDiff_const)
      have hφs : Function.support φ ⊆ closedBall q (LongTime.bumpRad n) := fun x hx ↦
        by_contra fun h ↦ hx (LongTime.translate_moll_eq_zero_of_notMem h)
      have hφc : HasCompactSupport φ :=
        HasCompactSupport.intro (isCompact_closedBall q (LongTime.bumpRad n))
          fun x hx ↦ LongTime.translate_moll_eq_zero_of_notMem hx
      have hφU : tsupport φ ⊆ U := (closure_minimal hφs isClosed_closedBall).trans hq
      have e1 := hψ.integral_eq hφ hφc hφU (e i)
      have i1 := GMTFoundations.integrable_inner_mul hψ.2.1 hφ.continuous hφc hφU (e i)
      have i2 := GMTFoundations.integrable_fderiv_apply_mul hψ.1 hφ hφc hφU (e i)
      have hfd : ∀ x, fderiv ℝ (fun x ↦ LongTime.moll d n (x - q)) x = fderiv ℝ φ x :=
        fun x ↦ rfl
      simp only [LongTime.firstOrderFunctional, map_smul, smul_eq_mul]
      rw [integral_add i1 i2, e1]
      ring
  -- identify the integrands
  have hpt : ∀ i x, ⟪Ψ x, e i⟫ * ζ i x + ψ x * fderiv ℝ (ζ i) x (e i) =
      ⟪Ψ x, e i⟫ * D i x + ψ x * fderiv ℝ (D i) x (e i) := by
    intro i x
    by_cases hx : x ∈ K
    · rw [(hζeq i x hx).fderiv_eq, (hζeq i x hx).eq_of_nhds]
    · simp [hψ0 x hx, hΨ0 x hx]
  have hsum : ∀ x, ∑ i, (⟪Ψ x, e i⟫ * D i x + ψ x * fderiv ℝ (D i) x (e i)) =
      Δ f x * ψ x + ⟪∇ f x, Ψ x⟫ := by
    intro x
    by_cases hx : x ∈ K
    · have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
        (hf1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hKU hx))
      have hlap : Δ f x = ∑ i, fderiv ℝ (D i) x (e i) := by
        rw [laplacian_eq_sum_fderiv_fderiv]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [D]
        rw [fderiv_clm_apply hdf (differentiableAt_const _)]
        simp [hedef]
      have hin : ⟪∇ f x, Ψ x⟫ = ∑ i, ⟪Ψ x, e i⟫ * D i x := by
        rw [← e.sum_inner_mul_inner (∇ f x) (Ψ x)]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [inner_gradient_eq_fderiv', real_inner_comm (e i) (Ψ x), mul_comm]
      rw [Finset.sum_add_distrib, hlap, hin, Finset.sum_mul, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    · simp [hψ0 x hx, hΨ0 x hx]
  have hint : ∀ i, Integrable (fun x ↦ ⟪Ψ x, e i⟫ * ζ i x + ψ x * fderiv ℝ (ζ i) x (e i)) := by
    intro i
    refine (GMTFoundations.integrable_inner_mul hψ.2.1 (hζ i).continuous (hζc i) (hζU i)
      (e i)).add ?_
    exact GMTFoundations.integrable_mul_of_locallyIntegrableOn hψ.1
      (((hζ i).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hζc i).fderiv_apply (𝕜 := ℝ) (e i)) ((tsupport_fderiv_apply_subset ℝ (e i)).trans (hζU i))
  have hfun : (fun x ↦ Δ f x * ψ x + ⟪∇ f x, Ψ x⟫) =
      fun x ↦ ∑ i, (⟪Ψ x, e i⟫ * ζ i x + ψ x * fderiv ℝ (ζ i) x (e i)) := by
    funext x; rw [← hsum x]; exact Finset.sum_congr rfl fun i _ ↦ (hpt i x).symm
  have hIsum : Integrable (fun x ↦ Δ f x * ψ x + ⟪∇ f x, Ψ x⟫) := by
    rw [hfun]; exact integrable_finsetSum Finset.univ fun i _ ↦ hint i
  have htot : ∫ x, (Δ f x * ψ x + ⟪∇ f x, Ψ x⟫) = 0 := by
    rw [hfun, integral_finsetSum _ fun i _ ↦ hint i]
    exact Finset.sum_eq_zero fun i _ ↦ hkey i
  have hI2 : Integrable (fun x ↦ ⟪∇ f x, Ψ x⟫) := by
    have hc : ContinuousOn (∇ f) K :=
      (continuousOn_gradient_of_contDiffOn' hU (hf.of_le (by norm_num))).mono hKU
    have hΨK : IntegrableOn Ψ K := hΨi.integrableOn
    have : IntegrableOn (fun x ↦ ⟪∇ f x, Ψ x⟫) K := by
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
      refine Integrable.mono' (hΨK.norm.const_mul C) ?_ ?_
      · exact (hc.aestronglyMeasurable hK.measurableSet).inner hΨK.aestronglyMeasurable
      · refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _))
    exact (integrableOn_iff_integrable_of_support_subset fun x hx ↦
      by_contra fun h ↦ hx (by simp [hΨ0 x h])).1 this
  have hI1 : Integrable (fun x ↦ Δ f x * ψ x) := by
    refine (hIsum.sub hI2).congr (Eventually.of_forall fun x ↦ ?_)
    simp
  rw [integral_add hI1 hI2] at htot
  linarith

/-! ### Truncations in the values -/

/-- The ramp `0` on `(-∞, 1]`, `1` on `[2, ∞)`, linear in between. -/
noncomputable def ramp (s : ℝ) : ℝ := min 1 (max 0 (s - 1))

theorem continuous_ramp : Continuous ramp :=
  continuous_const.min (continuous_const.max (continuous_id.sub continuous_const))

theorem ramp_nonneg (s : ℝ) : 0 ≤ ramp s := le_min zero_le_one (le_max_left _ _)

theorem ramp_le_one (s : ℝ) : ramp s ≤ 1 := min_le_left _ _

theorem ramp_eq_zero {s : ℝ} (hs : s ≤ 1) : ramp s = 0 := by
  unfold ramp; rw [max_eq_left (by linarith)]; exact min_eq_right zero_le_one

theorem ramp_eq_one {s : ℝ} (hs : 2 ≤ s) : ramp s = 1 := by
  unfold ramp; rw [max_eq_right (by linarith)]; exact min_eq_left (by linarith)

/-- The derivative of the truncation: `trunc' σ s = ramp (|s| / σ)`. -/
noncomputable def truncDeriv (σ s : ℝ) : ℝ := ramp (|s| / σ)

/-- The `C¹` truncation `T_σ(s) = ∫₀ˢ ramp(|r|/σ) dr`: `0` on `[-σ, σ]`, slope `1` off
`[-2σ, 2σ]`. -/
noncomputable def trunc (σ s : ℝ) : ℝ := ∫ r in (0 : ℝ)..s, truncDeriv σ r

/-- The primitive `Ψ_σ(s) = ∫₀ˢ T_σ`. -/
noncomputable def truncPrim (σ s : ℝ) : ℝ := ∫ r in (0 : ℝ)..s, trunc σ r

theorem continuous_truncDeriv (σ : ℝ) : Continuous (truncDeriv σ) :=
  continuous_ramp.comp (continuous_abs.div_const σ)

theorem truncDeriv_nonneg (σ s : ℝ) : 0 ≤ truncDeriv σ s := ramp_nonneg _

theorem truncDeriv_le_one (σ s : ℝ) : truncDeriv σ s ≤ 1 := ramp_le_one _

theorem truncDeriv_eq_zero {σ s : ℝ} (hσ : 0 < σ) (hs : |s| ≤ σ) : truncDeriv σ s = 0 :=
  ramp_eq_zero ((div_le_one hσ).2 hs)

theorem truncDeriv_eq_one {σ s : ℝ} (hσ : 0 < σ) (hs : 2 * σ ≤ |s|) : truncDeriv σ s = 1 :=
  ramp_eq_one ((le_div_iff₀ hσ).2 hs)

theorem truncDeriv_zero {σ : ℝ} (hσ : 0 < σ) : truncDeriv σ 0 = 0 :=
  truncDeriv_eq_zero hσ (by simp [hσ.le])

theorem hasDerivAt_trunc (σ s : ℝ) : HasDerivAt (trunc σ) (truncDeriv σ s) s :=
  ((continuous_truncDeriv σ).integral_hasStrictDerivAt 0 s).hasDerivAt

theorem deriv_trunc (σ : ℝ) : deriv (trunc σ) = truncDeriv σ :=
  funext fun s ↦ (hasDerivAt_trunc σ s).deriv

theorem continuous_trunc (σ : ℝ) : Continuous (trunc σ) :=
  continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_trunc σ s).continuousAt

theorem contDiff_trunc (σ : ℝ) : ContDiff ℝ 1 (trunc σ) :=
  contDiff_one_iff_deriv.2 ⟨fun s ↦ (hasDerivAt_trunc σ s).differentiableAt,
    by rw [deriv_trunc]; exact continuous_truncDeriv σ⟩

theorem nnnorm_deriv_trunc_le (σ s : ℝ) : ‖deriv (trunc σ) s‖₊ ≤ 1 := by
  rw [deriv_trunc, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (truncDeriv_nonneg σ s)]
  exact truncDeriv_le_one σ s

theorem trunc_eq_zero {σ s : ℝ} (hσ : 0 < σ) (hs : |s| ≤ σ) : trunc σ s = 0 := by
  unfold trunc
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun r hr ↦ ?_]
  · simp
  · have := Set.abs_sub_left_of_mem_uIcc hr
    simp only [sub_zero] at this
    exact truncDeriv_eq_zero hσ (this.trans hs)

theorem abs_trunc_le (σ s : ℝ) : |trunc σ s| ≤ |s| := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s) (C := 1)
    (f := truncDeriv σ) fun r _ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (truncDeriv_nonneg σ r)]
      exact truncDeriv_le_one σ r
  simpa [trunc] using this

theorem trunc_nonneg {σ s : ℝ} (hs : 0 ≤ s) : 0 ≤ trunc σ s :=
  intervalIntegral.integral_nonneg hs fun r _ ↦ truncDeriv_nonneg σ r

theorem trunc_nonpos {σ s : ℝ} (hs : s ≤ 0) : trunc σ s ≤ 0 := by
  unfold trunc
  rw [intervalIntegral.integral_symm]
  exact neg_nonpos.2 (intervalIntegral.integral_nonneg hs fun r _ ↦ truncDeriv_nonneg σ r)

theorem mul_trunc_nonneg (σ s : ℝ) : 0 ≤ s * trunc σ s := by
  rcases le_total 0 s with h | h
  · exact mul_nonneg h (trunc_nonneg h)
  · exact mul_nonneg_of_nonpos_of_nonpos h (trunc_nonpos h)

theorem trunc_zero (σ : ℝ) : trunc σ 0 = 0 := by simp [trunc]

theorem eventually_truncDeriv_eq_one {s : ℝ} (hs : s ≠ 0) :
    ∀ᶠ σ in 𝓝[>] (0 : ℝ), truncDeriv σ s = 1 := by
  filter_upwards [Ioo_mem_nhdsGT (half_pos (abs_pos.2 hs))] with σ hσ
  exact truncDeriv_eq_one hσ.1 (by linarith [hσ.2])

theorem intervalIntegrable_one_sub_truncDeriv (σ a b : ℝ) :
    IntervalIntegrable (fun r ↦ 1 - truncDeriv σ r) volume a b :=
  (continuous_const.sub (continuous_truncDeriv σ)).intervalIntegrable a b

theorem abs_integral_one_sub_truncDeriv_le (σ a b : ℝ) :
    |∫ r in a..b, (1 - truncDeriv σ r)| ≤ |b - a| := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := fun r ↦ 1 - truncDeriv σ r) fun r _ ↦ by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [truncDeriv_nonneg σ r, truncDeriv_le_one σ r]
  simpa using this

theorem abs_sub_trunc_le {σ : ℝ} (hσ : 0 < σ) (s : ℝ) : |s - trunc σ s| ≤ 2 * σ := by
  have hrepr : s - trunc σ s = ∫ r in (0 : ℝ)..s, (1 - truncDeriv σ r) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((continuous_truncDeriv σ).intervalIntegrable 0 s)]
    simp [trunc]
  rw [hrepr]
  rcases le_or_gt (2 * σ) s with h1 | h1
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_one_sub_truncDeriv σ 0 (2 * σ))
      (intervalIntegrable_one_sub_truncDeriv σ (2 * σ) s)]
    have h0 : ∫ r in (2 * σ)..s, (1 - truncDeriv σ r) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun r hr ↦ ?_]
      · simp
      · rw [uIcc_of_le h1] at hr
        simp only
        rw [truncDeriv_eq_one hσ (hr.1.trans (le_abs_self r)), sub_self]
    rw [h0, add_zero]
    refine (abs_integral_one_sub_truncDeriv_le σ 0 (2 * σ)).trans ?_
    rw [sub_zero, abs_of_pos (by linarith)]
  rcases le_or_gt s (-(2 * σ)) with h2 | h2
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_one_sub_truncDeriv σ 0 (-(2 * σ)))
      (intervalIntegrable_one_sub_truncDeriv σ (-(2 * σ)) s)]
    have h0 : ∫ r in (-(2 * σ))..s, (1 - truncDeriv σ r) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun r hr ↦ ?_]
      · simp
      · rw [uIcc_of_ge h2] at hr
        simp only
        rw [truncDeriv_eq_one hσ (by rw [abs_of_neg (by linarith [hr.2])]; linarith [hr.2]),
          sub_self]
    rw [h0, add_zero]
    refine (abs_integral_one_sub_truncDeriv_le σ 0 (-(2 * σ))).trans ?_
    rw [sub_zero, abs_neg, abs_of_pos (by linarith)]
  · refine (abs_integral_one_sub_truncDeriv_le σ 0 s).trans ?_
    rw [sub_zero, abs_le]
    constructor <;> linarith

theorem tendsto_trunc (s : ℝ) : Tendsto (fun σ ↦ trunc σ s) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
  have h2 : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝 (0 : ℝ)) (𝓝 (2 * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun σ ↦ norm_nonneg _) ?_ h2
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_sub_trunc_le hσ s

theorem hasDerivAt_truncPrim (σ s : ℝ) : HasDerivAt (truncPrim σ) (trunc σ s) s :=
  ((continuous_trunc σ).integral_hasStrictDerivAt 0 s).hasDerivAt

theorem truncPrim_zero (σ : ℝ) : truncPrim σ 0 = 0 := by simp [truncPrim]

theorem truncPrim_nonneg (σ s : ℝ) : 0 ≤ truncPrim σ s := by
  unfold truncPrim
  rcases le_total 0 s with h | h
  · exact intervalIntegral.integral_nonneg h fun r hr ↦ trunc_nonneg hr.1
  · rw [intervalIntegral.integral_symm]
    refine neg_nonneg.2 ?_
    rw [← neg_nonneg, ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_nonneg h fun r hr ↦ neg_nonneg.2 (trunc_nonpos hr.2)

theorem truncPrim_eq_zero {σ s : ℝ} (hσ : 0 < σ) (hs : |s| ≤ σ) : truncPrim σ s = 0 := by
  unfold truncPrim
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun r hr ↦ ?_]
  · simp
  · have := Set.abs_sub_left_of_mem_uIcc hr
    simp only [sub_zero] at this
    exact trunc_eq_zero hσ (this.trans hs)

end EnergyDissipation

end PerronVariational

end
