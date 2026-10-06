/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import PerronVariational.Defs.Semilinear
import GMTFoundations.Sobolev.Cutoff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Inner.WeakHeat
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Profiles

/-!
# The semilinear inner-variation identity (4.2)

Identity (4.2) of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. For a classical
solution `u` of (3.4) and `ξ ∈ C¹_c(U_∞; ℝᵈ)`,
`∫_{U_∞} (|∇u|² + Q² χ_ε) div ξ - 2 ∇u · Dξ ∇u + ∇(Q²) · ξ χ_ε - 2 (ξ · ∇u) ∂ₜu = 0`
with `χ_ε = 2 𝓑_ε(u)`: multiply the equation by `2 ξ · ∇u` and integrate by parts in space.

* `Inner.integral_mul_fderiv_eq_neg_of_lipschitz`, `Inner.integral_fderiv_apply_eq_neg`:
  integration by parts against Lipschitz fields (Rademacher, `integral_lineDeriv_mul_eq`);
* `Inner.integral_innerVar_slice`: the identity on a time slice, with `Q²` replaced by a bounded
  Lipschitz function `P` (only Lipschitz, so its derivative exists a.e.);
* `Inner.semilinear_innerVar_identity`: the space-time identity (Fubini).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-- **Integration by parts in one direction against a Lipschitz function.** For `h ∈ C¹(U)` and
`g` Lipschitz with compact support in `U`: `∫ g ∂ᵥh = -∫ (∂ᵥg) h`. -/
theorem integral_mul_fderiv_eq_neg_of_lipschitz {U : Set (E d)} (hU : IsOpen U) {h g : E d → ℝ}
    (hh : ContDiffOn ℝ 1 h U) {Cg : ℝ≥0} (hg : LipschitzWith Cg g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) (v : E d) :
    ∫ x, g x * fderiv ℝ h x v = -∫ x, fderiv ℝ g x v * h x := by
  set K := tsupport g with hKdef
  have hK : IsCompact K := hgc
  have hg0 : ∀ x ∉ K, g x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hdg0 : ∀ x ∉ K, fderiv ℝ g x = 0 := fun x hx ↦ fderiv_of_notMem_tsupport ℝ hx
  obtain ⟨H, CH, hH, δ, hδ, hHeq⟩ := exists_lipschitzWith_eqOn_thickening hU hh hK hgU
  have h1 := hH.integral_lineDeriv_mul_eq (μ := volume) hg hgc v
  have hL : ∀ x, lineDeriv ℝ H x v * g x = g x * fderiv ℝ h x v := by
    intro x
    by_cases hx : x ∈ K
    · have hev : H =ᶠ[𝓝 x] h :=
        Filter.mem_of_superset (isOpen_thickening.mem_nhds (self_subset_thickening hδ K hx))
          fun y hy ↦ (hHeq hy).symm
      have hd : HasFDerivAt H (fderiv ℝ h x) x :=
        ((hh.differentiableOn one_ne_zero).differentiableAt
          (hU.mem_nhds (hgU hx))).hasFDerivAt.congr_of_eventuallyEq hev
      rw [(hd.hasLineDerivAt v).lineDeriv, mul_comm]
    · simp [hg0 x hx]
  have hR : (fun x ↦ lineDeriv ℝ g x (-v) * H x) =ᵐ[volume]
      fun x ↦ -(fderiv ℝ g x v * h x) := by
    filter_upwards [hg.ae_differentiableAt] with x hx
    rw [hx.lineDeriv_eq_fderiv, map_neg]
    by_cases hxK : x ∈ K
    · rw [← hHeq (self_subset_thickening hδ K hxK)]
      ring
    · simp [hdg0 x hxK]
  rw [← integral_neg, ← integral_congr_ae hR, ← h1]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ (hL x).symm)

/-- **Integration by parts against a Lipschitz vector field.** For `h ∈ C¹(U)` and `Y` Lipschitz
with compact support in `U`: `∫ Dh · Y = -∫ h div Y` (`div Y` exists a.e. by Rademacher). -/
theorem integral_fderiv_apply_eq_neg {U : Set (E d)} (hU : IsOpen U) {h : E d → ℝ}
    (hh : ContDiffOn ℝ 1 h U) {Y : E d → E d} {CY : ℝ≥0} (hY : LipschitzWith CY Y)
    (hYc : HasCompactSupport Y) (hYU : tsupport Y ⊆ U) :
    ∫ x, fderiv ℝ h x (Y x) =
      -∫ x, h x * LinearMap.trace ℝ (E d) (fderiv ℝ Y x).toLinearMap := by
  set K := tsupport Y with hKdef
  have hK : IsCompact K := hYc
  have hKm : MeasurableSet K := (isClosed_tsupport Y).measurableSet
  set e := stdOrthonormalBasis ℝ (E d) with hedef
  set g : Fin (Module.finrank ℝ (E d)) → E d → ℝ := fun i x ↦ ⟪e i, Y x⟫ with hgdef
  have hgl : ∀ i, LipschitzWith (‖innerSL ℝ (e i)‖₊ * CY) (g i) := fun i ↦
    (innerSL ℝ (e i)).lipschitzWith.comp hY
  have hgsupp : ∀ i, Function.support (g i) ⊆ Function.support Y := fun i x hx h0 ↦
    hx (by simp [g, h0])
  have hgc : ∀ i, HasCompactSupport (g i) := fun i ↦ hYc.mono (hgsupp i)
  have hgK : ∀ i, tsupport (g i) ⊆ K := fun i ↦ closure_mono (hgsupp i)
  have hibp : ∀ i, ∫ x, g i x * fderiv ℝ h x (e i) = -∫ x, fderiv ℝ (g i) x (e i) * h x :=
    fun i ↦ integral_mul_fderiv_eq_neg_of_lipschitz hU hh (hgl i) (hgc i) ((hgK i).trans hYU)
      (e i)
  have hg0 : ∀ i, ∀ x ∉ K, g i x = 0 := fun i x hx ↦ image_eq_zero_of_notMem_tsupport
    fun h' ↦ hx (hgK i h')
  have hdg0 : ∀ i, ∀ x ∉ K, fderiv ℝ (g i) x = 0 := fun i x hx ↦
    fderiv_of_notMem_tsupport ℝ fun h' ↦ hx (hgK i h')
  have hsumL : ∀ x, fderiv ℝ h x (Y x) = ∑ i, g i x * fderiv ℝ h x (e i) := fun x ↦ by
    conv_lhs => rw [← e.sum_repr' (Y x)]
    simp [g, map_sum, map_smul]
  have hsumR : ∀ᵐ x, h x * LinearMap.trace ℝ (E d) (fderiv ℝ Y x).toLinearMap =
      ∑ i, fderiv ℝ (g i) x (e i) * h x := by
    filter_upwards [hY.ae_differentiableAt] with x hx
    rw [LinearMap.trace_eq_sum_inner _ e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hd : HasFDerivAt (g i) ((innerSL ℝ (e i)).comp (fderiv ℝ Y x)) x :=
      (innerSL ℝ (e i)).hasFDerivAt.comp x hx.hasFDerivAt
    rw [hd.fderiv, mul_comm]
    simp
  have hA : ∀ i, Integrable (fun x ↦ g i x * fderiv ℝ h x (e i)) := fun i ↦
    GMTFoundations.integrable_of_continuousOn_of_zero hK
      ((hgl i).continuous.continuousOn.mul
        (((hh.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).mono hYU))
      fun x hx ↦ by simp [hg0 i x hx]
  have hB : ∀ i, Integrable (fun x ↦ fderiv ℝ (g i) x (e i) * h x) := by
    intro i
    have hhK : IntegrableOn h K := (hh.continuousOn.mono hYU).integrableOn_compact hK
    have hmeas : AEStronglyMeasurable (fun x ↦ fderiv ℝ (g i) x (e i)) (volume.restrict K) :=
      (measurable_fderiv_apply_const ℝ (g i) (e i)).aestronglyMeasurable
    have hbd : ∀ᵐ x ∂(volume.restrict K), ‖fderiv ℝ (g i) x (e i)‖ ≤ ‖innerSL ℝ (e i)‖₊ * CY := by
      refine Eventually.of_forall fun x ↦ ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [e.orthonormal.1 i, mul_one]
      exact norm_fderiv_le_of_lipschitz ℝ (hgl i)
    refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).1
      (hhK.bdd_mul hmeas hbd)
    by_contra h'
    exact hx (by simp [hdg0 i x h'])
  calc ∫ x, fderiv ℝ h x (Y x) = ∫ x, ∑ i, g i x * fderiv ℝ h x (e i) :=
        integral_congr_ae (Eventually.of_forall hsumL)
    _ = ∑ i, ∫ x, g i x * fderiv ℝ h x (e i) := integral_finsetSum _ fun i _ ↦ hA i
    _ = ∑ i, -∫ x, fderiv ℝ (g i) x (e i) * h x := Finset.sum_congr rfl fun i _ ↦ hibp i
    _ = -∫ x, ∑ i, fderiv ℝ (g i) x (e i) * h x := by
        rw [integral_finsetSum _ fun i _ ↦ hB i, Finset.sum_neg_distrib]
    _ = -∫ x, h x * LinearMap.trace ℝ (E d) (fderiv ℝ Y x).toLinearMap := by
        rw [integral_congr_ae (hsumR.mono fun x hx ↦ hx.symm)]

/-- A bounded Lipschitz function times a bounded Lipschitz field is Lipschitz. -/
theorem exists_lipschitzWith_smul {P : E d → ℝ} {X : E d → E d} {CP CX : ℝ≥0}
    (hP : LipschitzWith CP P) (hX : LipschitzWith CX X) {MP MX : ℝ} (hPb : ∀ x, |P x| ≤ MP)
    (hXb : ∀ x, ‖X x‖ ≤ MX) : ∃ C : ℝ≥0, LipschitzWith C fun x ↦ P x • X x := by
  have hMP : 0 ≤ MP := (abs_nonneg _).trans (hPb 0)
  have hMX : 0 ≤ MX := (norm_nonneg _).trans (hXb 0)
  refine ⟨Real.toNNReal (CP * MX + MP * CX), LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  have h1 : |P x - P y| ≤ CP * ‖x - y‖ := by
    have := hP.dist_le_mul x y
    rwa [Real.dist_eq, dist_eq_norm] at this
  have h2 : ‖X x - X y‖ ≤ CX * ‖x - y‖ := by
    have := hX.dist_le_mul x y
    rwa [dist_eq_norm, dist_eq_norm] at this
  calc ‖P x • X x - P y • X y‖ = ‖(P x - P y) • X x + P y • (X x - X y)‖ := by
        congr 1
        rw [sub_smul, smul_sub]
        abel
    _ ≤ |P x - P y| * ‖X x‖ + |P y| * ‖X x - X y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (CP * ‖x - y‖) * MX + MP * (CX * ‖x - y‖) := by
        gcongr
        · exact hXb x
        · exact hPb y
    _ = (CP * MX + MP * CX) * ‖x - y‖ := by ring

/-- **The inner-variation identity on a time slice** (the spatial computation behind (4.2)).
Let `f ∈ C²(U)`, `X ∈ C¹_c(U; ℝᵈ)`, `P` bounded and Lipschitz (it plays the role of `Q²`),
`c ∈ C¹(U)` with `Dc = 2 r Df` on `U` (`c = 2 𝓑_ε(f)`, `r = β_ε(f)`). Then
`∫ (|∇f|² + P c) div X - 2 ∇f · DX ∇f + DP · X c - 2 (X · ∇f) (Δf - P r) = 0`. -/
theorem integral_innerVar_slice {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : ContDiffOn ℝ 2 f U) {X : E d → E d} (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X)
    (hXU : tsupport X ⊆ U) {P : E d → ℝ} {CP : ℝ≥0} (hP : LipschitzWith CP P) {MP : ℝ}
    (hPb : ∀ x, |P x| ≤ MP) {c r : E d → ℝ} (hc : ContDiffOn ℝ 1 c U) (hr : ContinuousOn r U)
    (hcr : ∀ x ∈ U, fderiv ℝ c x = (2 * r x) • fderiv ℝ f x) :
    ∫ x, ((‖∇ f x‖ ^ 2 + P x * c x) * LinearMap.trace ℝ (E d) (fderiv ℝ X x).toLinearMap
      - 2 * ⟪∇ f x, fderiv ℝ X x (∇ f x)⟫ + fderiv ℝ P x (X x) * c x
      - 2 * ⟪X x, ∇ f x⟫ * (Δ f x - P x * r x)) = 0 := by
  set K := tsupport X with hKdef
  have hK : IsCompact K := hXc
  have hKm : MeasurableSet K := (isClosed_tsupport X).measurableSet
  have hX0 : ∀ x ∉ K, X x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hDX0 : ∀ x ∉ K, fderiv ℝ X x = 0 := fun x hx ↦ fderiv_of_notMem_tsupport ℝ hx
  set e := stdOrthonormalBasis ℝ (E d) with hedef
  obtain ⟨tr, htrdef⟩ : ∃ tr : E d → ℝ,
      ∀ x, LinearMap.trace ℝ (E d) (fderiv ℝ X x).toLinearMap = tr x := ⟨_, fun _ ↦ rfl⟩
  simp only [htrdef]
  have htr : ∀ x, tr x = ∑ i, ⟪e i, fderiv ℝ X x (e i)⟫ := fun x ↦ by
    rw [← htrdef, LinearMap.trace_eq_sum_inner _ e]
    rfl
  have htrc : Continuous tr := by
    rw [show tr = fun x ↦ ∑ i, ⟪e i, fderiv ℝ X x (e i)⟫ from funext htr]
    exact continuous_finsetSum _ fun i _ ↦ continuous_const.inner
      ((hX.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have htr0 : ∀ x ∉ K, tr x = 0 := fun x hx ↦ by rw [htr]; simp [hDX0 x hx]
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have hdf : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ f) x := fun x hx ↦
    (hf1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
  -- coordinates of the gradient
  set D : Fin (Module.finrank ℝ (E d)) → E d → ℝ := fun i x ↦ fderiv ℝ f x (e i) with hDdef
  have hD : ∀ i, ContDiffOn ℝ 1 (D i) U := fun i ↦ hf1.clm_apply contDiffOn_const
  have hG : ∀ x, ∇ f x = ∑ i, D i x • e i := fun x ↦ by
    conv_lhs => rw [← e.sum_repr' (∇ f x)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm, inner_gradient_eq_fderiv]
  have hgradc : ContinuousOn (∇ f) U := by
    rw [show ∇ f = fun x ↦ ∑ i, D i x • e i from funext hG]
    exact continuousOn_finsetSum _ fun i _ ↦ (hD i).continuousOn.smul continuousOn_const
  have hlapc : ContinuousOn (Δ f) U := by
    rw [show Δ f = fun x ↦ ∑ i, fderiv ℝ (fderiv ℝ f) x (e i) (e i) from
      funext (laplacian_eq_sum_fderiv_fderiv f)]
    exact continuousOn_finsetSum _ fun i _ ↦
      ((hf1.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).clm_apply
        continuousOn_const
  -- `h = |∇f|²`
  have hh' : (fun x ↦ ‖∇ f x‖ ^ 2) = fun x ↦ ∑ i, D i x * D i x := funext fun x ↦ by
    rw [← sum_fderiv_basis_sq f x]
    exact Finset.sum_congr rfl fun i _ ↦ sq _
  have hh : ContDiffOn ℝ 1 (fun x ↦ ‖∇ f x‖ ^ 2) U := by
    rw [hh']
    exact ContDiffOn.sum fun i _ ↦ (hD i).mul (hD i)
  have hdD : ∀ i, ∀ x ∈ U, ∀ v, fderiv ℝ (D i) x v = fderiv ℝ (fderiv ℝ f) x v (e i) := by
    intro i x hx v
    simp only [D]
    rw [fderiv_clm_apply (hdf x hx) (differentiableAt_const _)]
    simp
  have hdh : ∀ x ∈ U, ∀ v, fderiv ℝ (fun x ↦ ‖∇ f x‖ ^ 2) x v =
      2 * fderiv ℝ (fderiv ℝ f) x v (∇ f x) := by
    intro x hx v
    have hDd : ∀ i, DifferentiableAt ℝ (D i) x := fun i ↦
      ((hD i).differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
    have hsum : HasFDerivAt (fun x ↦ ∑ i, D i x * D i x)
        (∑ i, (D i x • fderiv ℝ (D i) x + D i x • fderiv ℝ (D i) x)) x :=
      HasFDerivAt.fun_sum fun i _ ↦ (hDd i).hasFDerivAt.mul (hDd i).hasFDerivAt
    rw [hh', hsum.fderiv, sum_apply, hG x, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [add_apply, smul_apply, smul_eq_mul, map_smul,
      smul_eq_mul, hdD i x hx v]
    ring
  -- `g = Df · X`
  have hg0 : ∀ x ∉ K, (fun y ↦ fderiv ℝ f y (X y)) =ᶠ[𝓝 x] fun _ ↦ 0 := fun x hx ↦ by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
    simp [show X y = 0 from hy]
  have hgC : ContDiff ℝ 1 fun y ↦ fderiv ℝ f y (X y) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hf1.contDiffAt (hU.mem_nhds hx)).clm_apply hX.contDiffAt
    · exact contDiffAt_const.congr_of_eventuallyEq (hg0 x fun h' ↦ hx (hXU h'))
  have hgsupp : Function.support (fun y ↦ fderiv ℝ f y (X y)) ⊆ Function.support X :=
    fun x hx h0 ↦ hx (by simp [h0])
  have hgc : HasCompactSupport fun y ↦ fderiv ℝ f y (X y) := hXc.mono hgsupp
  have hgK : tsupport (fun y ↦ fderiv ℝ f y (X y)) ⊆ K := closure_mono hgsupp
  obtain ⟨Cg, hgL⟩ := hgC.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  have hI := integral_laplacian_mul_eq_neg hU hf hgL hgc (hgK.trans hXU)
  have hp1 : ∀ x, ⟪∇ f x, ∇ (fun y ↦ fderiv ℝ f y (X y)) x⟫ =
      ⟪∇ f x, fderiv ℝ X x (∇ f x)⟫ + fderiv ℝ (fun x ↦ ‖∇ f x‖ ^ 2) x (X x) / 2 := by
    intro x
    by_cases hx : x ∈ K
    · have hxU := hXU hx
      have hsymm := (hf.contDiffAt (hU.mem_nhds hxU)).isSymmSndFDerivAt (by simp)
      rw [real_inner_comm, inner_gradient_eq_fderiv,
        fderiv_clm_apply (hdf x hxU) (hX.differentiable one_ne_zero x), hdh x hxU]
      simp only [add_apply, ContinuousLinearMap.coe_comp,
        Function.comp_apply, ContinuousLinearMap.flip_apply]
      rw [← inner_gradient_eq_fderiv, hsymm (∇ f x) (X x)]
      ring
    · have h1 : ∇ (fun y ↦ fderiv ℝ f y (X y)) x = 0 := by
        simp only [gradient]
        rw [fderiv_of_notMem_tsupport ℝ (fun h' ↦ hx (hgK h')), map_zero]
      simp [h1, hDX0 x hx, hX0 x hx]
  -- integration by parts for `|∇f|²` and for `c` against `P X`
  obtain ⟨CX, hXL⟩ := hX.lipschitzWith_of_hasCompactSupport hXc one_ne_zero
  have hIII := integral_fderiv_apply_eq_neg hU hh hXL hXc hXU
  simp only [htrdef] at hIII
  obtain ⟨MX, hMX⟩ := hXc.exists_bound_of_continuous hX.continuous
  obtain ⟨CY, hYL⟩ := exists_lipschitzWith_smul hP hXL hPb hMX
  have hYsupp : Function.support (fun x ↦ P x • X x) ⊆ Function.support X :=
    fun x hx h0 ↦ hx (by simp [h0])
  have hIV := integral_fderiv_apply_eq_neg hU hc hYL (hXc.mono hYsupp)
    ((closure_mono hYsupp).trans hXU)
  have htrPX : ∀ᵐ x, c x * LinearMap.trace ℝ (E d) (fderiv ℝ (fun y ↦ P y • X y) x).toLinearMap =
      P x * c x * tr x + fderiv ℝ P x (X x) * c x := by
    filter_upwards [hP.ae_differentiableAt] with x hx
    have hd : HasFDerivAt (fun y ↦ P y • X y)
        (P x • fderiv ℝ X x + (fderiv ℝ P x).smulRight (X x)) x :=
      hx.hasFDerivAt.smul (hX.differentiable one_ne_zero x).hasFDerivAt
    rw [hd.fderiv, LinearMap.trace_eq_sum_inner _ e, htr]
    conv_rhs => rw [← e.sum_repr' (X x)]
    rw [map_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [inner_add_right, inner_smul_right]
    ring
  have hp4 : ∀ x, fderiv ℝ c x (P x • X x) = 2 * (⟪X x, ∇ f x⟫ * (P x * r x)) := by
    intro x
    by_cases hx : x ∈ U
    · rw [hcr x hx, smul_apply, map_smul, smul_eq_mul, smul_eq_mul,
        real_inner_comm, inner_gradient_eq_fderiv]
      ring
    · have hxK : x ∉ K := fun h' ↦ hx (hXU h')
      simp [hX0 x hxK]
  -- integrability
  have i1 : Integrable fun x ↦ ‖∇ f x‖ ^ 2 * tr x :=
    GMTFoundations.integrable_of_continuousOn_of_zero hK
      (((hgradc.mono hXU).norm.pow 2).mul htrc.continuousOn)
      fun x hx ↦ by simp [htr0 x hx]
  have i2 : Integrable fun x ↦ P x * c x * tr x :=
    GMTFoundations.integrable_of_continuousOn_of_zero hK
      ((hP.continuous.continuousOn.mul (hc.continuousOn.mono hXU)).mul htrc.continuousOn)
      fun x hx ↦ by simp [htr0 x hx]
  have i3 : Integrable fun x ↦ ⟪∇ f x, fderiv ℝ X x (∇ f x)⟫ :=
    GMTFoundations.integrable_of_continuousOn_of_zero hK ((hgradc.mono hXU).inner
      ((hX.continuous_fderiv one_ne_zero).continuousOn.clm_apply (hgradc.mono hXU)))
      fun x hx ↦ by simp [hDX0 x hx]
  have i4 : Integrable fun x ↦ fderiv ℝ P x (X x) * c x := by
    obtain ⟨Mc, hMc⟩ := hK.exists_bound_of_continuousOn (hc.continuousOn.mono hXU)
    have hon : IntegrableOn (fun x ↦ fderiv ℝ P x (X x) * c x) K := by
      refine IntegrableOn.of_bound hK.measure_lt_top
        ((((ContinuousLinearMap.apply ℝ ℝ :
            E d →L[ℝ] (E d →L[ℝ] ℝ) →L[ℝ] ℝ).aestronglyMeasurable_comp₂
          hX.continuous.aestronglyMeasurable
          (measurable_fderiv ℝ P).aestronglyMeasurable)).mul
          ((hc.continuousOn.mono hXU).aestronglyMeasurable hKm))
        (CP * MX * Mc) (ae_restrict_of_forall_mem hKm fun x hx ↦ ?_)
      rw [norm_mul]
      refine mul_le_mul ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hP) (hMX x) (norm_nonneg _)
          CP.coe_nonneg)) (hMc x hx) (norm_nonneg _)
        (mul_nonneg CP.coe_nonneg ((norm_nonneg _).trans (hMX x)))
    refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).1 hon
    by_contra h'
    exact hx (by simp [hX0 x h'])
  have i5 : Integrable fun x ↦ Δ f x * fderiv ℝ f x (X x) :=
    GMTFoundations.integrable_of_continuousOn_of_zero hK ((hlapc.mono hXU).mul
      (hgC.continuous.continuousOn)) fun x hx ↦ by simp [hX0 x hx]
  have i6 : Integrable fun x ↦ ⟪X x, ∇ f x⟫ * (P x * r x) :=
    GMTFoundations.integrable_of_continuousOn_of_zero hK ((hX.continuous.continuousOn.inner
      (hgradc.mono hXU)).mul (hP.continuous.continuousOn.mul (hr.mono hXU)))
      fun x hx ↦ by simp [hX0 x hx]
  have i7 : Integrable fun x ↦ fderiv ℝ (fun x ↦ ‖∇ f x‖ ^ 2) x (X x) :=
    GMTFoundations.integrable_of_continuousOn_of_zero hK
      (((hh.continuousOn_fderiv_of_isOpen hU le_rfl).mono hXU).clm_apply
        hX.continuous.continuousOn) fun x hx ↦ by simp [hX0 x hx]
  -- the integral identities
  have hA5 : ∫ x, Δ f x * fderiv ℝ f x (X x) =
      -((∫ x, ⟪∇ f x, fderiv ℝ X x (∇ f x)⟫) - (∫ x, ‖∇ f x‖ ^ 2 * tr x) / 2) := by
    rw [hI, integral_congr_ae (ae_of_all _ hp1), integral_add i3 (i7.div_const 2),
      integral_div, hIII]
    ring
  have hA6 : 2 * ∫ x, ⟪X x, ∇ f x⟫ * (P x * r x) =
      -((∫ x, P x * c x * tr x) + ∫ x, fderiv ℝ P x (X x) * c x) := by
    rw [← integral_const_mul, ← integral_congr_ae (ae_of_all _ hp4), hIV,
      integral_congr_ae htrPX, integral_add i2 i4]
  have htot : ∀ x, ((‖∇ f x‖ ^ 2 + P x * c x) * tr x
      - 2 * ⟪∇ f x, fderiv ℝ X x (∇ f x)⟫ + fderiv ℝ P x (X x) * c x
      - 2 * ⟪X x, ∇ f x⟫ * (Δ f x - P x * r x)) =
      ‖∇ f x‖ ^ 2 * tr x + P x * c x * tr x - 2 * ⟪∇ f x, fderiv ℝ X x (∇ f x)⟫
        + fderiv ℝ P x (X x) * c x - 2 * (Δ f x * fderiv ℝ f x (X x))
        + 2 * (⟪X x, ∇ f x⟫ * (P x * r x)) := by
    intro x
    have hin : ⟪X x, ∇ f x⟫ = fderiv ℝ f x (X x) := by
      rw [real_inner_comm, inner_gradient_eq_fderiv]
    rw [hin]
    ring
  simp only [htot]
  have j1 : Integrable fun x ↦ ‖∇ f x‖ ^ 2 * tr x + P x * c x * tr x := i1.add i2
  have j2 : Integrable fun x ↦ ‖∇ f x‖ ^ 2 * tr x + P x * c x * tr x -
      2 * ⟪∇ f x, fderiv ℝ X x (∇ f x)⟫ := j1.sub (i3.const_mul 2)
  have j3 : Integrable fun x ↦ ‖∇ f x‖ ^ 2 * tr x + P x * c x * tr x -
      2 * ⟪∇ f x, fderiv ℝ X x (∇ f x)⟫ + fderiv ℝ P x (X x) * c x := j2.add i4
  have j4 : Integrable fun x ↦ ‖∇ f x‖ ^ 2 * tr x + P x * c x * tr x -
      2 * ⟪∇ f x, fderiv ℝ X x (∇ f x)⟫ + fderiv ℝ P x (X x) * c x -
      2 * (Δ f x * fderiv ℝ f x (X x)) := j3.sub (i5.const_mul 2)
  rw [integral_add j4 (i6.const_mul 2), integral_sub j3 (i5.const_mul 2), integral_add j2 i4,
    integral_sub j1 (i3.const_mul 2), integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul]
  linarith [hA5, hA6]

/-! ### The space-time identity -/

theorem tsupport_slice_subset_vec (ξ : E d × ℝ → E d) (t : ℝ) :
    tsupport (fun x ↦ ξ (x, t)) ⊆ {x | (x, t) ∈ tsupport ξ} :=
  closure_minimal (fun _ hx ↦ subset_tsupport ξ hx)
    ((isClosed_tsupport ξ).preimage (continuous_id.prodMk continuous_const))

/-- The time slice of a vector field is supported in the projection of its support. -/
theorem tsupport_slice_subset_image (ξ : E d × ℝ → E d) (t : ℝ) :
    tsupport (fun x ↦ ξ (x, t)) ⊆ Prod.fst '' tsupport ξ := fun x hx ↦
  ⟨(x, t), tsupport_slice_subset_vec ξ t hx, rfl⟩

theorem contDiff_bigBEps {β : ℝ → ℝ} (hβ : IsReactionProfile β) (ε : ℝ) :
    ContDiff ℝ 1 (bigBEps β ε) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun z ↦ (hβ.hasDerivAt_bigBEps ε z).differentiableAt, ?_⟩
  rw [show deriv (bigBEps β ε) = betaEps β ε from funext fun z ↦
    (hβ.hasDerivAt_bigBEps ε z).deriv]
  exact hβ.continuous_betaEps ε

/-- **The semilinear inner-variation identity** (4.2) (the paper cites Definition 6.1 of G. S.
Weiss, *Partial regularity for weak solutions of an elliptic free boundary problem*, Comm. Partial
Differential Equations 23 (1998), 439–455, doi:10.1080/03605309808821352): multiply (3.4) by
`2 ξ · ∇u` and integrate by parts in space (`integral_innerVar_slice` on each time slice, then
Fubini). For `ξ ∈ C¹_c(U_∞; ℝᵈ)` the integrand of (3.3) with `(u, ∂ₜu, χ_ε)` is integrable on `U_∞`
and integrates to `0`. Since `Q` is only Lipschitz, `∇(Q²)` exists only a.e.; `Q²` is replaced near
`spt ξ` by a bounded Lipschitz function `P` (McShane extension and truncation). -/
theorem semilinear_innerVar_identity (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {ε : ℝ} (_hε : 0 < ε) {gε : E d → ℝ} {u : E d × ℝ → ℝ}
    (hu : IsSemilinearSolution S.U S.Q β ε gε u) (ξ : E d × ℝ → E d) (hξ : ContDiff ℝ 1 ξ)
    (hξc : HasCompactSupport ξ) (hξs : tsupport ξ ⊆ UInf S.U) :
    Integrable (paraInnerVarIntegrand S.Q u (dₜ u) (chiEps β ε u) ξ)
        (volume.restrict (UInf S.U)) ∧
      ∫ p in UInf S.U, paraInnerVarIntegrand S.Q u (dₜ u) (chiEps β ε u) ξ p = 0 := by
  have hU := S.isOpen
  have hsol := hu.2.1
  set Ω := UInf S.U with hΩdef
  have hΩ : IsOpen Ω := hU.prod isOpen_Ioi
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  set K := tsupport ξ with hKdef
  have hK : IsCompact K := hξc
  have hKm : MeasurableSet K := (isClosed_tsupport ξ).measurableSet
  have hξ0 : ∀ p ∉ K, ξ p = 0 := fun p hp ↦ image_eq_zero_of_notMem_tsupport hp
  set K₁ := Prod.fst '' K with hK₁def
  have hK₁ : IsCompact K₁ := hK.image continuous_fst
  have hK₁U : K₁ ⊆ S.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hξs hp).1
  -- a bounded Lipschitz replacement `P` of `Q²` near `K₁`
  obtain ⟨δ, hδ, hδU⟩ := hK₁.exists_cthickening_subset_open hU hK₁U
  set S₁ := cthickening δ K₁ with hS₁def
  have hS₁ : IsCompact S₁ := hK₁.cthickening
  obtain ⟨LQ, hLQ⟩ := S.lip
  have hQS₁ : LipschitzOnWith LQ S.Q S₁ := hLQ.mono (hδU.trans subset_closure)
  obtain ⟨MQ, hMQ0, hMQ⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S₁, |S.Q x| ≤ M := by
    obtain ⟨M, hM⟩ := hS₁.exists_bound_of_continuousOn hQS₁.continuousOn
    exact ⟨max M 0, le_max_right _ _, fun x hx ↦ (hM x hx).trans (le_max_left _ _)⟩
  have hQ2 : LipschitzOnWith (Real.toNNReal (2 * MQ * LQ)) (fun x ↦ S.Q x ^ 2) S₁ := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
    have h1 : |S.Q x - S.Q y| ≤ LQ * dist x y := by
      have := hQS₁.dist_le_mul x hx y hy
      rwa [Real.dist_eq] at this
    calc |S.Q x ^ 2 - S.Q y ^ 2| = |S.Q x + S.Q y| * |S.Q x - S.Q y| := by
          rw [← abs_mul]; ring_nf
      _ ≤ (MQ + MQ) * (LQ * dist x y) := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add (hMQ x hx) (hMQ y hy))
      _ = 2 * MQ * LQ * dist x y := by ring
  obtain ⟨P₀, hP₀, hP₀eq⟩ := hQ2.extend_real
  set P : E d → ℝ := fun x ↦ min (max (P₀ x) 0) (MQ ^ 2) with hPdef
  have hP : LipschitzWith (Real.toNNReal (2 * MQ * LQ)) P := (hP₀.max_const 0).min_const _
  have hPb : ∀ x, |P x| ≤ MQ ^ 2 := fun x ↦ by
    rw [abs_of_nonneg (le_min (le_max_right _ _) (sq_nonneg _))]
    exact min_le_right _ _
  have hPeq : ∀ x ∈ S₁, P x = S.Q x ^ 2 := fun x hx ↦ by
    have h1 : P₀ x = S.Q x ^ 2 := (hP₀eq hx).symm
    have h2 : S.Q x ^ 2 ≤ MQ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hMQ x hx) 2
    simp only [P, h1, max_eq_left (sq_nonneg _), min_eq_left h2]
  have hPd : ∀ x ∈ K₁, fderiv ℝ (fun y ↦ S.Q y ^ 2) x = fderiv ℝ P x := fun x hx ↦ by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ K₁ hx)] with y hy
    exact (hPeq y (thickening_subset_cthickening _ _ hy)).symm
  -- the modified integrand
  set χ := chiEps β ε u with hχdef
  set G : E d × ℝ → ℝ := fun p ↦ (‖gradₓ u p‖ ^ 2 + P p.1 * χ p) * divₓ ξ p
      - 2 * ⟪gradₓ u p, fderivₓ ξ p (gradₓ u p)⟫ + fderiv ℝ P p.1 (ξ p) * χ p
      - 2 * ⟪ξ p, gradₓ u p⟫ * (lapₓ u p - P p.1 * betaEps β ε (u p)) with hGdef
  have hfx0 : ∀ p ∉ K, fderivₓ ξ p = 0 := fun p hp ↦
    fderiv_of_notMem_tsupport ℝ fun h ↦ hp (tsupport_slice_subset_vec ξ p.2 h)
  have hdiv0 : ∀ p ∉ K, divₓ ξ p = 0 := fun p hp ↦ by simp [divₓ, hfx0 p hp]
  have hG0 : ∀ p ∉ K, G p = 0 := fun p hp ↦ by simp [G, hdiv0 p hp, hfx0 p hp, hξ0 p hp]
  have hFG : ∀ p ∈ Ω, paraInnerVarIntegrand S.Q u (dₜ u) χ ξ p = G p := by
    intro p hp
    by_cases hpK : p ∈ K
    · have hp1 : p.1 ∈ S₁ := self_subset_cthickening K₁ ⟨p, hpK, rfl⟩
      simp only [paraInnerVarIntegrand, G, hsol.2.2.2.2.2.2 p hp, hPeq p.1 hp1,
        hPd p.1 ⟨p, hpK, rfl⟩]
    · simp [paraInnerVarIntegrand, G, hdiv0 p hpK, hfx0 p hpK, hξ0 p hpK]
  -- continuity facts on `K`
  have hgu : ContinuousOn (gradₓ u) K := hsol.2.2.1.mono hξs
  have huc : ContinuousOn u K := hsol.1.mono hξs
  have hχc : ContinuousOn χ K := continuousOn_const.mul
    ((contDiff_bigBEps hβ ε).continuous.comp_continuousOn huc)
  obtain ⟨LQ', hLQ'⟩ := S.lip
  have hRc : ContinuousOn (fun p ↦ S.Q p.1 ^ 2 * betaEps β ε (u p)) Ω :=
    ((hLQ'.continuousOn.comp continuous_fst.continuousOn
      (fun p hp ↦ subset_closure hp.1)).pow 2).mul
      ((hβ.continuous_betaEps ε).comp_continuousOn hsol.1)
  have hlapc : ContinuousOn (lapₓ u) Ω :=
    (hsol.2.2.2.2.2.1.add hRc).congr fun p hp ↦ by
      simp only [Pi.add_apply]; rw [hsol.2.2.2.2.2.2 p hp]; ring
  have hfxc : Continuous (fderivₓ ξ) := by
    have : fderivₓ ξ = fun p ↦ (fderiv ℝ ξ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ) := by
      funext p
      have h1 : HasFDerivAt (fun y : E d ↦ (y, p.2)) (ContinuousLinearMap.inl ℝ (E d) ℝ) p.1 :=
        (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
      exact ((hξ.differentiable one_ne_zero p).hasFDerivAt.comp p.1 h1).fderiv
    rw [this]
    exact (hξ.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have hdivc : Continuous (divₓ ξ) := by
    set e := stdOrthonormalBasis ℝ (E d)
    have : divₓ ξ = fun p ↦ ∑ i, ⟪e i, fderivₓ ξ p (e i)⟫ := funext fun p ↦ by
      rw [divₓ, LinearMap.trace_eq_sum_inner _ e]
      rfl
    rw [this]
    exact continuous_finsetSum _ fun i _ ↦ continuous_const.inner
      (hfxc.clm_apply continuous_const)
  -- integrability of `G`
  set G₁ : E d × ℝ → ℝ := fun p ↦ (‖gradₓ u p‖ ^ 2 + P p.1 * χ p) * divₓ ξ p
      - 2 * ⟪gradₓ u p, fderivₓ ξ p (gradₓ u p)⟫
      - 2 * ⟪ξ p, gradₓ u p⟫ * (lapₓ u p - P p.1 * betaEps β ε (u p)) with hG₁def
  have hG₁c : ContinuousOn G₁ K :=
    ((((hgu.norm.pow 2).add ((hP.continuous.comp continuous_fst).continuousOn.mul hχc)).mul
      hdivc.continuousOn).sub (continuousOn_const.mul (hgu.inner
        (hfxc.continuousOn.clm_apply hgu)))).sub ((continuousOn_const.mul
      (hξ.continuous.continuousOn.inner hgu)).mul ((hlapc.mono hξs).sub
        ((hP.continuous.comp continuous_fst).continuousOn.mul
          ((hβ.continuous_betaEps ε).comp_continuousOn huc))))
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hG₁c
  obtain ⟨Mξ, hMξ⟩ := hξc.exists_bound_of_continuous hξ.continuous
  obtain ⟨Mχ, hMχ⟩ := hK.exists_bound_of_continuousOn hχc
  have hGsplit : ∀ p, G p = G₁ p + fderiv ℝ P p.1 (ξ p) * χ p := fun p ↦ by
    simp only [G, G₁]
    ring
  have hGint : Integrable G := by
    have hon : IntegrableOn G K := by
      refine IntegrableOn.of_bound hK.measure_lt_top ?_ (C₁ + 2 * MQ * LQ * Mξ * Mχ)
        (ae_restrict_of_forall_mem hKm fun p hp ↦ ?_)
      · rw [show G = fun p ↦ G₁ p + fderiv ℝ P p.1 (ξ p) * χ p from funext hGsplit]
        exact (hG₁c.aestronglyMeasurable hKm).add
          (((ContinuousLinearMap.apply ℝ ℝ :
            E d →L[ℝ] (E d →L[ℝ] ℝ) →L[ℝ] ℝ).aestronglyMeasurable_comp₂
            hξ.continuous.aestronglyMeasurable
            ((measurable_fderiv ℝ P).comp measurable_fst).aestronglyMeasurable).mul
            (hχc.aestronglyMeasurable hKm))
      · rw [hGsplit]
        refine (norm_add_le _ _).trans (add_le_add (hC₁ p hp) ?_)
        rw [norm_mul, mul_assoc, mul_assoc]
        have hPn : ‖fderiv ℝ P p.1‖ ≤ 2 * MQ * LQ := by
          have := norm_fderiv_le_of_lipschitz ℝ hP (x₀ := p.1)
          rwa [Real.coe_toNNReal _ (by positivity)] at this
        calc ‖fderiv ℝ P p.1 (ξ p)‖ * ‖χ p‖ ≤ (2 * MQ * LQ * Mξ) * Mχ := by
              refine mul_le_mul ((ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul hPn (hMξ p) (norm_nonneg _) (by positivity))) (hMχ p hp)
                (norm_nonneg _) (by
                  have := (norm_nonneg _).trans (hMξ p)
                  positivity)
          _ = 2 * MQ * (LQ * (Mξ * Mχ)) := by ring
    refine (integrableOn_iff_integrable_of_support_subset fun p hp ↦ ?_).1 hon
    by_contra h
    exact hp (hG0 p h)
  have hFint : Integrable (paraInnerVarIntegrand S.Q u (dₜ u) χ ξ) (volume.restrict Ω) :=
    hGint.restrict.congr ((ae_restrict_iff' hΩm).2 (Eventually.of_forall fun p hp ↦
      (hFG p hp).symm))
  refine ⟨hFint, ?_⟩
  rw [setIntegral_congr_fun hΩm hFG,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ hG0 p fun h ↦ hp (hξs h)]
  rw [Measure.volume_eq_prod] at hGint ⊢
  rw [integral_prod_symm _ hGint]
  refine (integral_congr_ae (Eventually.of_forall fun t ↦ ?_)).trans (integral_zero _ _)
  by_cases ht : 0 < t
  · have hXU : tsupport (fun x ↦ ξ (x, t)) ⊆ S.U :=
      (tsupport_slice_subset_image ξ t).trans hK₁U
    have hXc : HasCompactSupport (fun x ↦ ξ (x, t)) :=
      IsCompact.of_isClosed_subset hK₁ (isClosed_tsupport _) (tsupport_slice_subset_image ξ t)
    have hfs : ContDiffOn ℝ 2 (fun y ↦ u (y, t)) S.U := hsol.2.1 t ht
    have hfc : ContinuousOn (fun y ↦ u (y, t)) S.U := hfs.continuousOn
    have hB := contDiff_bigBEps hβ ε
    have hc : ContDiffOn ℝ 1 (fun y ↦ 2 * bigBEps β ε (u (y, t))) S.U :=
      contDiffOn_const.mul (hB.comp_contDiffOn (hfs.of_le (by norm_num)))
    have hcr : ∀ x ∈ S.U, fderiv ℝ (fun y ↦ 2 * bigBEps β ε (u (y, t))) x =
        (2 * betaEps β ε (u (x, t))) • fderiv ℝ (fun y ↦ u (y, t)) x := by
      intro x hx
      have hfd : HasFDerivAt (fun y ↦ u (y, t)) (fderiv ℝ (fun y ↦ u (y, t)) x) x :=
        ((hfs.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
      have h1 := ((hβ.hasDerivAt_bigBEps ε (u (x, t))).const_mul 2).comp_hasFDerivAt x hfd
      exact h1.fderiv
    have h := integral_innerVar_slice hU hfs (hξ.comp (contDiff_id.prodMk contDiff_const)) hXc
      hXU hP hPb hc ((hβ.continuous_betaEps ε).comp_continuousOn hfc) hcr
    refine Eq.trans ?_ h
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [G, divₓ, fderivₓ, gradₓ, lapₓ, χ, chiEps]
    rfl
  · have hnK : ∀ x, (x, t) ∉ K := fun x h ↦ ht (hξs h).2
    simp [hG0 _ (hnK _)]

end Inner

end PerronVariational

end
