/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Sobolev -- shake: keep
import GMTFoundations.Sobolev.Lattice
import PerronVariational.Semilinear.Calculus

/-!
# Two-plane functions: definition and regularity

Part of **Proposition 2.14** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: the
one-dimensional calculus of Steps 1 and 3 (`oneDim_energy_competitor`, `ratio_ineq`), the two-plane
function `twoPlane α e = α |x · e|`, `C¹` functions are `H¹_loc`, and the regularity of `twoPlane`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal Convolution

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### One-dimensional calculus (Steps 1 and 3) -/

/-- **Proposition 2.14, Step 1**, with general `q`: the energy of the one-dimensional
competitor `φ^ε_α(s) = α/(1-ε) (|s| - ε)₊` on `[-1, 1]` is
`2 [α²/(1-ε) + q²(1-ε)] = 2(α² + q²) - 2ε/(1-ε) (q²(1-ε) - α²)`. -/
theorem oneDim_energy_competitor (α q ε : ℝ) (hε : ε ≠ 1) :
    2 * (α ^ 2 / (1 - ε) + q ^ 2 * (1 - ε)) =
      2 * (α ^ 2 + q ^ 2) - 2 * ε / (1 - ε) * (q ^ 2 * (1 - ε) - α ^ 2) := by
  have h : (1 - ε) ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  field_simp
  ring

/-- **Proposition 2.14, Step 3**, with general `q`: for `x ∈ (0, 1]` and `q² ≤ α²`,
`α²/x + q² x ≥ α² + q²`. Multiplying by `x`, this is `(1 - x)(α² - q² x) ≥ 0`. -/
theorem ratio_ineq {α q x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hqα : q ^ 2 ≤ α ^ 2) :
    α ^ 2 + q ^ 2 ≤ α ^ 2 / x + q ^ 2 * x := by
  rw [div_add' _ _ _ hx.ne', le_div_iff₀ hx]
  have h1 : 0 ≤ 1 - x := by linarith
  have h2 : 0 ≤ α ^ 2 - q ^ 2 * x := by nlinarith [sq_nonneg q]
  nlinarith [mul_nonneg h1 h2]

/-! ### The two-plane function -/

/-- The two-plane solution `φ_α(x) = α |x · e|` (Proposition 2.14: `φ_α(x_d)` with `e = e_d`). -/
noncomputable def twoPlane (α : ℝ) (e : E d) (x : E d) : ℝ := α * |inner ℝ x e|

/-- The (a.e.) gradient of `twoPlane α e`: `α e` on `{x · e > 0}`, `-α e` on `{x · e < 0}`,
`0` on the hyperplane. -/
noncomputable def twoPlaneGrad (α : ℝ) (e : E d) (x : E d) : E d :=
  α • ({y : E d | 0 < inner ℝ y e}.indicator (fun _ ↦ e) x +
    {y : E d | 0 < -inner ℝ y e}.indicator (fun _ ↦ -e) x)

theorem inner_twoPlaneGrad (α : ℝ) (e x : E d) :
    inner ℝ (twoPlaneGrad α e x) x = α * |inner ℝ x e| := by
  unfold twoPlaneGrad
  rcases lt_trichotomy (inner ℝ x e) 0 with h | h | h
  · have h1 : x ∉ {y : E d | 0 < inner ℝ y e} := by simp [h.le]
    have h2 : x ∈ {y : E d | 0 < -inner ℝ y e} := by simp [h]
    rw [indicator_of_notMem h1, indicator_of_mem h2, zero_add, real_inner_smul_left,
      inner_neg_left, real_inner_comm, abs_of_neg h]
  · have h1 : x ∉ {y : E d | 0 < inner ℝ y e} := by simp [h]
    have h2 : x ∉ {y : E d | 0 < -inner ℝ y e} := by simp [h]
    simp [h]
  · have h1 : x ∈ {y : E d | 0 < inner ℝ y e} := by simp [h]
    have h2 : x ∉ {y : E d | 0 < -inner ℝ y e} := by simp [h.le]
    rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero, real_inner_smul_left,
      real_inner_comm, abs_of_pos h]

theorem norm_twoPlaneGrad_le (α : ℝ) {e : E d} (he : ‖e‖ = 1) (x : E d) :
    ‖twoPlaneGrad α e x‖ ≤ |α| := by
  unfold twoPlaneGrad
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  rcases lt_trichotomy (inner ℝ x e) 0 with h | h | h
  · have h1 : x ∉ {y : E d | 0 < inner ℝ y e} := by simp [h.le]
    have h2 : x ∈ {y : E d | 0 < -inner ℝ y e} := by simp [h]
    rw [indicator_of_notMem h1, indicator_of_mem h2, zero_add, norm_neg, he]
  · have h1 : x ∉ {y : E d | 0 < inner ℝ y e} := by simp [h]
    have h2 : x ∉ {y : E d | 0 < -inner ℝ y e} := by simp [h]
    rw [indicator_of_notMem h1, indicator_of_notMem h2, add_zero, norm_zero]
    exact zero_le_one
  · have h1 : x ∈ {y : E d | 0 < inner ℝ y e} := by simp [h]
    have h2 : x ∉ {y : E d | 0 < -inner ℝ y e} := by simp [h.le]
    rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero, he]

/-! ### `C¹` functions are `H¹_loc` -/

section C1

/-- A `C¹` function has its classical gradient as weak gradient. -/
theorem hasWeakGradient_of_contDiff_one {U : Set (E d)} {η : E d → ℝ} (hη : ContDiff ℝ 1 η) :
    HasWeakGradient U η (∇ η) := by
  have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
  have hdη : Continuous (fun x ↦ fderiv ℝ η x) := hη.continuous_fderiv one_ne_zero
  refine GMTFoundations.HasWeakGradient.of_integral_eq
    (hη.continuous.locallyIntegrable.locallyIntegrableOn U)
    ((GMTFoundations.continuous_gradient hη).locallyIntegrable.locallyIntegrableOn U)
    fun φ hφ hφc _ v ↦ ?_
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdφ : Continuous (fun x ↦ fderiv ℝ φ x) := hφ.continuous_fderiv (by simp)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := η) (g := φ) (v := v)
    ((hdη.clm_apply continuous_const).mul hφ.continuous |>.integrable_of_hasCompactSupport
      hφc.mul_left)
    (hη.continuous.mul (hdφ.clm_apply continuous_const) |>.integrable_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) v).mul_left)
    ((hη.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    (fun x _ ↦ hηd x) (fun x _ ↦ hφd x)
  rw [key]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only
  rw [inner_gradient_left (hηd x)]

theorem memLp_two_restrict_compact_of_continuous {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Set (E d)} (hK : IsCompact K) {f : E d → F} (hf : Continuous f) :
    MemLp f 2 (volume.restrict K) := by
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have := GMTFoundations.memLp_smul_continuous hK (memLp_const (1 : ℝ)) hf
  simpa using this

/-- A `C¹` function is in `H¹_loc` with its classical gradient. -/
theorem memH1Loc_of_contDiff_one {U : Set (E d)} {η : E d → ℝ} (hη : ContDiff ℝ 1 η) :
    MemH1Loc U η (∇ η) :=
  ⟨hasWeakGradient_of_contDiff_one hη, fun _ _ hK ↦
    ⟨memLp_two_restrict_compact_of_continuous hK hη.continuous,
      memLp_two_restrict_compact_of_continuous hK (GMTFoundations.continuous_gradient hη)⟩⟩

theorem _root_.GMTFoundations.MemH1Loc.const_mul' {U : Set (E d)} {u : E d → ℝ} {G : E d → E d}
    (hu : MemH1Loc U u G) (c : ℝ) : MemH1Loc U (fun x ↦ c * u x) (fun x ↦ c • G x) :=
  ⟨hu.1.const_smul c, fun K hK hKc ↦ ⟨(hu.2 K hK hKc).1.const_mul c,
    (hu.2 K hK hKc).2.const_smul c⟩⟩

end C1

/-! ### Regularity of the two-plane function -/

section TwoPlaneRegularity

variable {α : ℝ} {e : E d}

theorem gradient_inner_const (e x : E d) : ∇ (fun y : E d ↦ inner ℝ y e) x = e := by
  have h : HasGradientAt (fun y : E d ↦ inner ℝ y e) e x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have := (innerSL ℝ e).hasFDerivAt (x := x)
    convert this using 1
    · ext v; simp [real_inner_comm]
  exact h.gradient

theorem contDiff_inner_const {n : WithTop ℕ∞} (e : E d) :
    ContDiff ℝ n (fun y : E d ↦ inner ℝ y e) :=
  contDiff_id.inner ℝ contDiff_const

theorem continuous_inner_const (e : E d) : Continuous (fun y : E d ↦ inner ℝ y e) :=
  continuous_id.inner continuous_const

/-- `φ_α ∈ H¹_loc(U)` with weak gradient `twoPlaneGrad α e`. -/
theorem memH1Loc_twoPlane {U : Set (E d)} (hU : IsOpen U) (α : ℝ) (e : E d) :
    MemH1Loc U (twoPlane α e) (twoPlaneGrad α e) := by
  have hℓ : MemH1Loc U (fun y : E d ↦ inner ℝ y e) (fun _ ↦ e) := by
    have := memH1Loc_of_contDiff_one (U := U) (contDiff_inner_const e)
    rwa [show ∇ (fun y : E d ↦ inner ℝ y e) = fun _ ↦ e from funext (gradient_inner_const e)]
      at this
  have h1 := GMTFoundations.memH1Loc_posPart hU hℓ
  have h2 := GMTFoundations.memH1Loc_posPart hU hℓ.neg
  have h3 := (h1.add h2).const_mul' α
  convert h3 using 1
  funext x
  simp only [twoPlane]
  congr 1
  rcases le_total (inner ℝ x e) 0 with h | h
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.2 h), zero_add]
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.2 h), add_zero]

theorem posSet_twoPlane (hα : 0 < α) (U : Set (E d)) :
    posSet (twoPlane α e) U = U ∩ {x | inner ℝ x e ≠ 0} := by
  ext x
  simp [posSet, twoPlane, mul_pos_iff_of_pos_left hα]

theorem isOpen_posSet_twoPlane (hα : 0 < α) {U : Set (E d)} (hU : IsOpen U) :
    IsOpen (posSet (twoPlane α e) U) := by
  rw [posSet_twoPlane hα]
  exact hU.inter (isOpen_ne_fun (continuous_inner_const e) continuous_const)

/-- Near a point off the hyperplane, `φ_α` is the linear function `± α (x · e)`. -/
theorem twoPlane_eventuallyEq {x : E d} (hx : inner ℝ x e ≠ 0) :
    twoPlane α e =ᶠ[𝓝 x] fun y ↦ (SignType.sign (inner ℝ x e) : ℝ) * α * inner ℝ y e := by
  rcases hx.lt_or_gt with h | h
  · have hev : ∀ᶠ y in 𝓝 x, inner ℝ y e < 0 :=
      (continuous_inner_const e).continuousAt.eventually (gt_mem_nhds h)
    filter_upwards [hev] with y hy
    simp [twoPlane, abs_of_neg hy, h]
  · have hev : ∀ᶠ y in 𝓝 x, 0 < inner ℝ y e :=
      (continuous_inner_const e).continuousAt.eventually (lt_mem_nhds h)
    filter_upwards [hev] with y hy
    simp [twoPlane, abs_of_pos hy, h]

theorem contDiffOn_twoPlane (hα : 0 < α) (U : Set (E d)) :
    ContDiffOn ℝ 2 (twoPlane α e) (posSet (twoPlane α e) U) := by
  intro x hx
  rw [posSet_twoPlane hα] at hx
  refine (ContDiffAt.congr_of_eventuallyEq ?_ (twoPlane_eventuallyEq hx.2)).contDiffWithinAt
  exact (contDiff_const.mul (contDiff_inner_const e)).contDiffAt

theorem laplacian_twoPlane (hα : 0 < α) {U : Set (E d)} {x : E d}
    (hx : x ∈ posSet (twoPlane α e) U) : Δ (twoPlane α e) x = 0 := by
  rw [posSet_twoPlane hα] at hx
  rw [(InnerProductSpace.laplacian_congr_nhds (twoPlane_eventuallyEq hx.2)).eq_of_nhds,
    laplacian_eq_sum_fderiv_fderiv]
  set c : ℝ := (SignType.sign (inner ℝ x e) : ℝ) * α
  have hfd : fderiv ℝ (fun y : E d ↦ c * inner ℝ y e) = fun _ ↦ c • innerSL ℝ e := by
    funext y
    have := ((innerSL ℝ e).hasFDerivAt (x := y)).const_mul c
    convert this.fderiv using 2
    funext z; simp [real_inner_comm]
  simp [hfd]

end TwoPlaneRegularity

end PerronVariational

end
