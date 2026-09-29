/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.TwoPlane.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import PerronVariational.Defs.Stationary
import GMTFoundations.Sobolev.Lattice
import Mathlib.Order.CompletePartialOrder
import PerronVariational.Semilinear.Calculus

/-!
# Two-plane functions: the competitors of Proposition 2.14 (1) and Step 2

Part of **Proposition 2.14** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: the
first-variation competitor `φ_α + t η` for part (1), coordinates adapted to a unit vector `e`
(`coordEquiv`, `lintegral_eq_lintegral_coord`), the cut-off `cylBump` and Step 2 (the case `α < q`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal Convolution

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### The first-variation competitor for Proposition 2.14 (1) -/

section Bump

/-- The `C¹` bump `η(x) = ((1 - |x|²)₊)²`, supported in `B̄₁(0)`. -/
noncomputable def twoPlaneBump (x : E d) : ℝ := (max (1 - ‖x‖ ^ 2) 0) ^ 2

theorem twoPlaneBump_nonneg (x : E d) : 0 ≤ twoPlaneBump x := sq_nonneg _

theorem twoPlaneBump_eq_zero {x : E d} (hx : 1 ≤ ‖x‖) : twoPlaneBump x = 0 := by
  have : 1 - ‖x‖ ^ 2 ≤ 0 := by nlinarith
  simp [twoPlaneBump, max_eq_right this]

theorem contDiff_twoPlaneBump : ContDiff ℝ 1 (twoPlaneBump (d := d)) :=
  GMTFoundations.contDiff_max_sq.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem hasGradientAt_twoPlaneBump (x : E d) :
    HasGradientAt twoPlaneBump ((-4 * max (1 - ‖x‖ ^ 2) 0) • x) x := by
  have h1 : HasFDerivAt (fun y : E d ↦ 1 - ‖y‖ ^ 2)
      (-(2 • (innerSL ℝ x).comp (ContinuousLinearMap.id ℝ (E d)))) x :=
    ((hasFDerivAt_id x).norm_sq).const_sub 1
  have h2 := (GMTFoundations.hasDerivAt_max_sq (1 - ‖x‖ ^ 2)).comp_hasFDerivAt x h1
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h2 using 1
  ext v
  simp
  ring

theorem gradient_twoPlaneBump (x : E d) :
    ∇ twoPlaneBump x = (-4 * max (1 - ‖x‖ ^ 2) 0) • x :=
  (hasGradientAt_twoPlaneBump x).gradient

theorem inner_twoPlaneGrad_gradient_twoPlaneBump (α : ℝ) (e x : E d) :
    inner ℝ (twoPlaneGrad α e x) (∇ twoPlaneBump x) =
      -4 * (max (1 - ‖x‖ ^ 2) 0 * (α * |inner ℝ x e|)) := by
  rw [gradient_twoPlaneBump, real_inner_smul_right, inner_twoPlaneGrad]
  ring

theorem continuous_gradient_twoPlaneBump : Continuous (∇ (twoPlaneBump (d := d))) := by
  rw [show ∇ (twoPlaneBump (d := d)) = fun x ↦ (-4 * max (1 - ‖x‖ ^ 2) 0) • x from
    funext gradient_twoPlaneBump]
  fun_prop

end Bump

/-- A hyperplane `{x · e = 0}`, `e ≠ 0`, is Lebesgue-null. -/
theorem volume_inner_eq_zero {e : E d} (he : e ≠ 0) : volume {x : E d | inner ℝ x e = 0} = 0 := by
  have hs : LinearMap.ker ((innerSL ℝ e : E d →L[ℝ] ℝ) : E d →ₗ[ℝ] ℝ) ≠ ⊤ := by
    intro h
    have : e ∈ LinearMap.ker ((innerSL ℝ e : E d →L[ℝ] ℝ) : E d →ₗ[ℝ] ℝ) := h ▸ Submodule.mem_top
    simp [he] at this
  have := Measure.addHaar_submodule volume _ hs
  convert this using 2
  ext x
  simp [real_inner_comm]

theorem measurable_twoPlaneGrad (α : ℝ) (e : E d) : Measurable (twoPlaneGrad α e) := by
  have hm : Measurable (fun y : E d ↦ inner ℝ y e) := (continuous_inner_const e).measurable
  unfold twoPlaneGrad
  refine Measurable.const_smul (Measurable.add ?_ ?_) α
  · exact measurable_const.indicator (measurableSet_lt measurable_const hm)
  · exact measurable_const.indicator (measurableSet_lt measurable_const hm.neg)

section Coordinates

variable {n : ℕ}

theorem exists_orthonormalBasis_zero {e : E (n + 1)} (he : ‖e‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1)), b 0 = e := by
  have hv : Orthonormal ℝ (({0} : Set (Fin (n + 1))).restrict fun _ ↦ e) := by
    rw [orthonormal_iff_ite]
    intro i j
    have : i = j := Subsingleton.elim i j
    subst this
    simp [he]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 0 rfl⟩

/-- Coordinates `x ↦ (x · b₀, (x · b_{j+1})_j)` adapted to an orthonormal basis. -/
noncomputable def coordEquiv (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1))) :
    E (n + 1) ≃ᵐ ℝ × (Fin n → ℝ) :=
  (b.measurableEquiv.trans (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0)

theorem measurePreserving_coordEquiv (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1))) :
    MeasurePreserving (coordEquiv b) volume volume :=
  (b.measurePreserving_measurableEquiv.trans
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _)).trans
    (volume_preserving_piFinSuccAbove (fun _ ↦ ℝ) 0)

theorem coordEquiv_apply (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1))) (x : E (n + 1)) :
    coordEquiv b x = (inner ℝ (b 0) x, fun j ↦ inner ℝ (b j.succ) x) := by
  simp only [coordEquiv, OrthonormalBasis.measurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.piFinSuccAbove_apply]
  simp only [Fin.insertNthEquiv]
  simp only [Fin.insertNth_zero', Fin.removeNth_zero, Equiv.symm_mk,
    Homeomorph.toMeasurableEquiv_coe, LinearIsometryEquiv.coe_toHomeomorph,
    MeasurableEquiv.toLp_symm_apply, Equiv.coe_fn_mk, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp [OrthonormalBasis.repr_apply_apply]
  · funext j
    simp [Fin.tail, OrthonormalBasis.repr_apply_apply]

theorem coordEquiv_symm_apply (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1)))
    (p : ℝ × (Fin n → ℝ)) :
    (coordEquiv b).symm p = b.repr.symm (WithLp.toLp 2 (Fin.cons p.1 p.2)) := by
  simp [coordEquiv, OrthonormalBasis.measurableEquiv]
  rfl

variable {e : E (n + 1)} {b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1))}

theorem continuous_coordEquiv_symm (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1))) :
    Continuous (coordEquiv b).symm := by
  rw [funext (coordEquiv_symm_apply b)]
  exact b.repr.symm.continuous.comp ((PiLp.continuous_toLp 2 _).comp
    (Continuous.finCons (A := fun _ ↦ ℝ) continuous_fst continuous_snd))

theorem coordEquiv_fst (hb : b 0 = e) (x : E (n + 1)) : (coordEquiv b x).1 = inner ℝ x e := by
  rw [coordEquiv_apply, hb, real_inner_comm]

theorem coordEquiv_add_smul (hb : b 0 = e) (x : E (n + 1)) (s : ℝ) :
    coordEquiv b (x + s • e) = ((coordEquiv b x).1 + s, (coordEquiv b x).2) := by
  have h0 : inner ℝ (b 0) (b 0) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 0]; norm_num
  have hj : ∀ j : Fin n, inner ℝ (b j.succ) (b 0) = (0 : ℝ) := fun j ↦
    b.orthonormal.2 (Fin.succ_ne_zero j)
  rw [coordEquiv_apply, coordEquiv_apply, ← hb]
  ext j
  · simp [inner_add_right, real_inner_smul_right]
  · simp [inner_add_right, real_inner_smul_right, hj]

theorem inner_coordEquiv_symm (hb : b 0 = e) (p : ℝ × (Fin n → ℝ)) :
    inner ℝ ((coordEquiv b).symm p) e = p.1 := by
  rw [← coordEquiv_fst hb, MeasurableEquiv.apply_symm_apply]

theorem coordEquiv_symm_eq (hb : b 0 = e) (s : ℝ) (y : Fin n → ℝ) :
    (coordEquiv b).symm (s, y) = (coordEquiv b).symm (0, y) + s • e := by
  apply (coordEquiv b).injective
  rw [coordEquiv_add_smul hb, MeasurableEquiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply]
  simp

theorem coordEquiv_symm_zero : (coordEquiv b).symm (0, 0) = 0 := by
  apply (coordEquiv b).injective
  rw [MeasurableEquiv.apply_symm_apply, coordEquiv_apply]
  ext <;> simp

/-- Tonelli in coordinates adapted to `e`. -/
theorem lintegral_eq_lintegral_coord (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1)))
    {f : E (n + 1) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ y, ∫⁻ s, f ((coordEquiv b).symm (s, y)) := by
  rw [← (measurePreserving_coordEquiv b).symm.lintegral_comp_emb
    (coordEquiv b).symm.measurableEmbedding, Measure.volume_eq_prod]
  exact lintegral_prod_symm _ (hf.comp (coordEquiv b).symm.measurable).aemeasurable

end Coordinates

/-! ### The cut-off `η(x')` of Step 2 -/

section CylBump

variable {n : ℕ} {e : E (n + 1)}

/-- The orthogonal projection `x ↦ x - (e · x) e` onto `e^⊥` (for `‖e‖ = 1`). -/
noncomputable def projPerp (e : E (n + 1)) : E (n + 1) →L[ℝ] E (n + 1) :=
  ContinuousLinearMap.id ℝ _ - (innerSL ℝ e).smulRight e

theorem projPerp_apply (x : E (n + 1)) : projPerp e x = x - inner ℝ e x • e := by
  simp [projPerp]

theorem projPerp_self (he : ‖e‖ = 1) : projPerp e e = 0 := by
  rw [projPerp_apply, real_inner_self_eq_norm_sq, he]; simp

/-- A fixed smooth bump on `E (n+1)`, `= 1` on `B̄_{1/2}` and supported in `B₁`. -/
noncomputable def cylBump₀ : ContDiffBump (0 : E (n + 1)) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The cut-off `η(x') = η₀(x - (x · e) e)`, a function of the variables orthogonal to `e`
(Step 2 of the paper's proof: `η(|x'|/L)` with `L = 1`). -/
noncomputable def cylBump (e : E (n + 1)) (x : E (n + 1)) : ℝ := cylBump₀ (projPerp e x)

theorem contDiff_cylBump {k : ℕ∞} : ContDiff ℝ k (cylBump e) :=
  (cylBump₀.contDiff (n := k)).comp (projPerp e).contDiff

theorem continuous_cylBump : Continuous (cylBump e) := (contDiff_cylBump (k := 0)).continuous

theorem cylBump_nonneg (x : E (n + 1)) : 0 ≤ cylBump e x := cylBump₀.nonneg

theorem cylBump_le_one (x : E (n + 1)) : cylBump e x ≤ 1 := cylBump₀.le_one

theorem cylBump_zero : cylBump e 0 = 1 := by
  simp only [cylBump, map_zero]
  exact cylBump₀.one_of_mem_closedBall (mem_closedBall_self (by norm_num [cylBump₀]))

theorem cylBump_add_smul (he : ‖e‖ = 1) (x : E (n + 1)) (s : ℝ) :
    cylBump e (x + s • e) = cylBump e x := by
  simp [cylBump, map_add, map_smul, projPerp_self he]

theorem norm_lt_two_of_cylBump_pos {x : E (n + 1)} (hx : 0 < cylBump e x) (he : ‖e‖ = 1)
    (h : |inner ℝ x e| < 1) : ‖x‖ < 2 := by
  have hs : projPerp e x ∈ ball (0 : E (n + 1)) 1 := by
    have : projPerp e x ∈ Function.support (cylBump₀ (n := n)) := hx.ne'
    rwa [cylBump₀.support_eq] at this
  rw [mem_ball, dist_zero_right] at hs
  have hx' : x = projPerp e x + inner ℝ e x • e := by rw [projPerp_apply]; abel
  rw [hx']
  calc ‖projPerp e x + inner ℝ e x • e‖ ≤ ‖projPerp e x‖ + ‖inner ℝ e x • e‖ := norm_add_le _ _
    _ < 1 + 1 := by
      refine add_lt_add hs ?_
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, real_inner_comm]; exact h
    _ = 2 := by norm_num

theorem hasFDerivAt_cylBump (x : E (n + 1)) :
    HasFDerivAt (cylBump e) ((fderiv ℝ cylBump₀ (projPerp e x)).comp (projPerp e)) x :=
  ((cylBump₀.contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x
    (projPerp e).hasFDerivAt

theorem inner_gradient_cylBump (he : ‖e‖ = 1) (x : E (n + 1)) :
    inner ℝ (∇ (cylBump e) x) e = 0 := by
  rw [inner_gradient_left (hasFDerivAt_cylBump x).differentiableAt,
    (hasFDerivAt_cylBump x).fderiv]
  simp [projPerp_self he]

theorem gradient_cylBump_add_smul (he : ‖e‖ = 1) (x : E (n + 1)) (s : ℝ) :
    ∇ (cylBump e) (x + s • e) = ∇ (cylBump e) x := by
  have h : fderiv ℝ (cylBump e) x = fderiv ℝ (cylBump e) (x + s • e) := by
    rw [← fderiv_comp_add_right]
    congr 1
    funext y
    rw [cylBump_add_smul he]
  simp only [gradient, h]

theorem exists_norm_gradient_cylBump_le :
    ∃ M, 0 ≤ M ∧ ∀ x : E (n + 1), ‖∇ (cylBump e) x‖ ≤ M := by
  obtain ⟨C, hC⟩ := ((cylBump₀ (n := n)).contDiff.continuous_fderiv
    one_ne_zero).bounded_above_of_compact_support (cylBump₀.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨max C 0 * ‖projPerp e‖, mul_nonneg (le_max_right _ _) (norm_nonneg _), fun x ↦ ?_⟩
  rw [norm_gradient_eq_norm_fderiv, (hasFDerivAt_cylBump x).fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right ((hC _).trans (le_max_left _ _)) (norm_nonneg _))

end CylBump

/-! ### Step 2: elementary facts -/

section Step2

theorem volume_abs_mem_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    volume {s : ℝ | a < |s| ∧ |s| < b} = ENNReal.ofReal (2 * (b - a)) := by
  have hset : {s : ℝ | a < |s| ∧ |s| < b} = Ioo (-b) (-a) ∪ Ioo a b := by
    ext s
    simp only [mem_setOf_eq, mem_union, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt 0 s with hs | hs
      · rw [abs_of_nonneg hs] at h1 h2; exact Or.inr ⟨h1, h2⟩
      · rw [abs_of_neg hs] at h1 h2; exact Or.inl ⟨by linarith, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rw [abs_of_neg (by linarith : s < 0)]; exact ⟨by linarith, by linarith⟩
      · rw [abs_of_pos (by linarith : 0 < s)]; exact ⟨h1, h2⟩
  have hdisj : Disjoint (Ioo (-b) (-a)) (Ioo a b) :=
    Set.disjoint_left.2 fun s h1 h2 ↦ by linarith [h1.2, h2.1]
  rw [hset, measure_union hdisj measurableSet_Ioo, Real.volume_Ioo, Real.volume_Ioo,
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  congr 1
  ring

/-- The column inequality of Step 2: with `A = α/(1-ε)`,
`(A²(1 + ε²g²) + q²)(1 - ε) < α² + q²` as soon as `ε (α²M² + q²) < q² - α²` and `g ≤ M`. -/
theorem column_ineq {α q ε g M : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hg0 : 0 ≤ g) (hgM : g ≤ M)
    (hkey : ε * (α ^ 2 * M ^ 2 + q ^ 2) < q ^ 2 - α ^ 2) :
    ((α / (1 - ε)) ^ 2 * (1 + ε ^ 2 * g ^ 2) + q ^ 2) * (1 - ε) < α ^ 2 + q ^ 2 := by
  have hr : 0 < 1 - ε := by linarith
  have hA : (α / (1 - ε)) ^ 2 * (1 - ε) = α ^ 2 / (1 - ε) := by
    field_simp
  have hgg : g ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hg0 hgM 2
  have h1 : α ^ 2 * (1 + ε ^ 2 * g ^ 2) + q ^ 2 * (1 - ε) ^ 2 < (α ^ 2 + q ^ 2) * (1 - ε) := by
    have : ε * (α ^ 2 * g ^ 2 + q ^ 2) < q ^ 2 - α ^ 2 := by
      have := mul_le_mul_of_nonneg_left hgg (sq_nonneg α)
      nlinarith
    nlinarith
  have e1 : ((α / (1 - ε)) ^ 2 * (1 + ε ^ 2 * g ^ 2) + q ^ 2) * (1 - ε) =
      (α ^ 2 * (1 + ε ^ 2 * g ^ 2) + q ^ 2 * (1 - ε) ^ 2) / (1 - ε) := by
    field_simp
  rw [e1, div_lt_iff₀ hr]
  exact h1

/-- The competitor `Φ = A((ℓ - εc)₊ + (-ℓ - εc)₊)` versus `φ = α|ℓ|` (pointwise, `c = η(x)`). -/
theorem sub_pos_iff_of_competitor {α ε c ℓ : ℝ} (hα : 0 < α) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hc : 0 ≤ c) :
    0 < α * |ℓ| - α / (1 - ε) * (max (ℓ - ε * c) 0 + max (-ℓ - ε * c) 0) ↔
      0 < |ℓ| ∧ |ℓ| < c := by
  have hr : 0 < 1 - ε := by linarith
  have hsum : max (ℓ - ε * c) 0 + max (-ℓ - ε * c) 0 = max (|ℓ| - ε * c) 0 := by
    rcases le_total 0 ℓ with h | h
    · rw [abs_of_nonneg h, max_eq_right (by nlinarith : -ℓ - ε * c ≤ 0), add_zero]
    · rw [abs_of_nonpos h, max_eq_right (by nlinarith : ℓ - ε * c ≤ 0), zero_add]
  rw [hsum]
  rcases le_or_gt (|ℓ|) (ε * c) with h | h
  · rw [max_eq_right (by linarith), mul_zero, sub_zero]
    constructor
    · intro h0
      have hl : 0 < |ℓ| := pos_of_mul_pos_right h0 hα.le
      refine ⟨hl, lt_of_le_of_lt h ?_⟩
      have hc0 : 0 < c := by
        by_contra hc0; push Not at hc0; nlinarith
      nlinarith
    · rintro ⟨h1, -⟩; exact mul_pos hα h1
  · rw [max_eq_left (by linarith : 0 ≤ |ℓ| - ε * c)]
    have e1 : α * |ℓ| - α / (1 - ε) * (|ℓ| - ε * c) = α * ε * (c - |ℓ|) / (1 - ε) := by
      field_simp; ring
    rw [e1]
    constructor
    · intro h0
      have : 0 < α * ε * (c - |ℓ|) := by
        rwa [div_pos_iff_of_pos_right hr] at h0
      have : 0 < c - |ℓ| := pos_of_mul_pos_right this (mul_pos hα hε0).le
      exact ⟨lt_of_le_of_lt (mul_nonneg hε0.le hc) h, by linarith⟩
    · rintro ⟨-, h2⟩
      exact div_pos (mul_pos (mul_pos hα hε0) (by linarith)) hr

theorem competitor_pos_iff {α ε c ℓ : ℝ} (hα : 0 < α) (hε1 : ε < 1) :
    0 < α / (1 - ε) * (max (ℓ - ε * c) 0 + max (-ℓ - ε * c) 0) ↔ ε * c < |ℓ| := by
  have hA : 0 < α / (1 - ε) := div_pos hα (by linarith)
  rw [mul_pos_iff_of_pos_left hA]
  rcases le_total 0 ℓ with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h0
      by_contra hn; push Not at hn
      have : max (ℓ - ε * c) 0 = 0 := max_eq_right (by linarith)
      have : max (-ℓ - ε * c) 0 = 0 := max_eq_right (by linarith)
      linarith
    · intro h1
      have := le_max_right (-ℓ - ε * c) 0
      have := le_max_left (ℓ - ε * c) 0
      linarith
  · rw [abs_of_nonpos h]
    constructor
    · intro h0
      by_contra hn; push Not at hn
      have : max (ℓ - ε * c) 0 = 0 := max_eq_right (by linarith)
      have : max (-ℓ - ε * c) 0 = 0 := max_eq_right (by linarith)
      linarith
    · intro h1
      have := le_max_right (ℓ - ε * c) 0
      have := le_max_left (-ℓ - ε * c) 0
      linarith

end Step2

theorem memH1Loc_inner_const {d : ℕ} {U : Set (E d)} (e : E d) :
    MemH1Loc U (fun y : E d ↦ inner ℝ y e) (fun _ ↦ e) := by
  have := memH1Loc_of_contDiff_one (U := U) (contDiff_inner_const (n := 1) e)
  rwa [show ∇ (fun y : E d ↦ inner ℝ y e) = fun _ ↦ e from funext (gradient_inner_const e)]
    at this

theorem norm_sub_smul_sq {d : ℕ} {e w : E d} (he : ‖e‖ = 1) (hw : inner ℝ w e = 0) (ε : ℝ) :
    ‖e - ε • w‖ ^ 2 = 1 + ε ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_sub_sq_real, he, real_inner_smul_right, real_inner_comm, hw, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem norm_twoPlaneGrad_of_ne {d : ℕ} (α : ℝ) {e : E d} (he : ‖e‖ = 1) {x : E d}
    (hx : inner ℝ x e ≠ 0) : ‖twoPlaneGrad α e x‖ = |α| := by
  unfold twoPlaneGrad
  rw [norm_smul, Real.norm_eq_abs]
  rcases hx.lt_or_gt with h | h
  · have h1 : x ∉ {y : E d | 0 < inner ℝ y e} := by simp [h.le]
    have h2 : x ∈ {y : E d | 0 < -inner ℝ y e} := by simp [h]
    rw [indicator_of_notMem h1, indicator_of_mem h2, zero_add, norm_neg, he, mul_one]
  · have h1 : x ∈ {y : E d | 0 < inner ℝ y e} := by simp [h]
    have h2 : x ∉ {y : E d | 0 < -inner ℝ y e} := by simp [h.le]
    rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero, he, mul_one]

section Step2Main

variable {n : ℕ}

/-- **Proposition 2.14 (2), `α < q`, Step 2** in dimension `n + 1`. -/
theorem twoPlane_not_downwardMinimizer_of_lt_aux {α q : ℝ} (hα : 0 < α) (hαq : α < q)
    {e : E (n + 1)} (he : ‖e‖ = 1) :
    ¬ IsDownwardMinimizer univ (fun _ ↦ q) (twoPlane α e) := by
  rintro ⟨-, -, -, -, hmin⟩
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_zero he
  obtain ⟨M, hM0, hM⟩ := exists_norm_gradient_cylBump_le (e := e)
  have hq : 0 < q := hα.trans hαq
  -- the parameters
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (q ^ 2 - α ^ 2) / (2 * (α ^ 2 * M ^ 2 + q ^ 2)) := ⟨_, rfl⟩
  have hden : 0 < 2 * (α ^ 2 * M ^ 2 + q ^ 2) := by positivity
  have hqα2 : 0 < q ^ 2 - α ^ 2 := by nlinarith
  have hε0 : 0 < ε := hεdef ▸ div_pos hqα2 hden
  have hkey : ε * (α ^ 2 * M ^ 2 + q ^ 2) < q ^ 2 - α ^ 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_lt_iff₀ hden]; nlinarith
  have hε1 : ε < 1 := by
    rw [hεdef, div_lt_one hden]; nlinarith [sq_nonneg (α * M)]
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = α / (1 - ε) := ⟨_, rfl⟩
  set η := cylBump e with hηdef
  set ℓ : E (n + 1) → ℝ := fun y ↦ inner ℝ y e with hℓdef
  -- the competitor `ψ = φ - (φ - Φ)₊ = min(φ, Φ)`
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : E (n + 1) → ℝ,
      Φ = fun x ↦ A * (max (ℓ x - ε * η x) 0 + max (-ℓ x - ε * η x) 0) := ⟨_, rfl⟩
  obtain ⟨GΦ, hGΦdef⟩ : ∃ GΦ : E (n + 1) → E (n + 1), GΦ = fun x ↦ A •
      ({y | 0 < ℓ y - ε * η y}.indicator (fun y ↦ e - ε • ∇ η y) x +
        {y | 0 < -ℓ y - ε * η y}.indicator (fun y ↦ -e - ε • ∇ η y) x) := ⟨_, rfl⟩
  set φ := twoPlane α e with hφdef
  set G := twoPlaneGrad α e with hGdef
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : E (n + 1) → ℝ, ψ = fun x ↦ φ x - max (φ x - Φ x) 0 := ⟨_, rfl⟩
  obtain ⟨Gψ, hGψdef⟩ : ∃ Gψ : E (n + 1) → E (n + 1),
      Gψ = fun x ↦ G x - {y | 0 < φ y - Φ y}.indicator (fun y ↦ G y - GΦ y) x := ⟨_, rfl⟩
  have hu : MemH1Loc univ φ G := memH1Loc_twoPlane isOpen_univ α e
  have hη1 : MemH1Loc univ η (∇ η) := memH1Loc_of_contDiff_one contDiff_cylBump
  have hΦ : MemH1Loc univ Φ GΦ := by
    have hp := (memH1Loc_inner_const (U := univ) e).sub (hη1.const_mul' ε)
    have hm := (memH1Loc_inner_const (U := univ) e).neg.sub (hη1.const_mul' ε)
    have := ((GMTFoundations.memH1Loc_posPart isOpen_univ hp).add
      (GMTFoundations.memH1Loc_posPart isOpen_univ hm)).const_mul' A
    rw [hΦdef, hGΦdef]
    exact this
  have hψ : MemH1Loc univ ψ Gψ := by
    have := hu.sub (GMTFoundations.memH1Loc_posPart isOpen_univ (hu.sub hΦ))
    rw [hψdef, hGψdef]
    exact this
  -- pointwise structure
  set B : Set (E (n + 1)) := ball 0 2 with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hℓc : Continuous ℓ := continuous_inner_const e
  have hηc : Continuous η := continuous_cylBump
  have hgc : Continuous (∇ η) := GMTFoundations.continuous_gradient contDiff_cylBump
  set D : Set (E (n + 1)) := {x | 0 < |ℓ x| ∧ |ℓ x| < η x} with hDdef
  have hDm : MeasurableSet D :=
    ((isOpen_lt continuous_const hℓc.abs).inter (isOpen_lt hℓc.abs hηc)).measurableSet
  have hsub : ∀ x, 0 < φ x - Φ x ↔ x ∈ D := by
    intro x
    rw [hΦdef, hAdef]
    exact sub_pos_iff_of_competitor hα hε0 hε1 (cylBump_nonneg x)
  have hΦpos : ∀ x, 0 < Φ x ↔ ε * η x < |ℓ x| := by
    intro x
    rw [hΦdef, hAdef]
    exact competitor_pos_iff hα hε1
  have hDB : D ⊆ B := by
    intro x hx
    rw [hBdef, mem_ball, dist_zero_right]
    exact norm_lt_two_of_cylBump_pos (hx.1.trans hx.2) he
      (hx.2.trans_le (cylBump_le_one x))
  have hψD : ∀ x ∈ D, ψ x = Φ x ∧ Gψ x = GΦ x := by
    intro x hx
    have h := (hsub x).2 hx
    refine ⟨?_, ?_⟩
    · rw [hψdef]; simp only; rw [max_eq_left h.le]; ring
    · rw [hGψdef]; simp only
      rw [indicator_of_mem (show x ∈ {y | 0 < φ y - Φ y} from h)]; abel
  have hψnD : ∀ x ∉ D, ψ x = φ x ∧ Gψ x = G x := by
    intro x hx
    have h : ¬ 0 < φ x - Φ x := fun h ↦ hx ((hsub x).1 h)
    refine ⟨?_, ?_⟩
    · rw [hψdef]; simp only; rw [max_eq_right (not_lt.1 h)]; ring
    · rw [hGψdef]; simp only
      rw [indicator_of_notMem (show x ∉ {y | 0 < φ y - Φ y} from h)]; abel
  have hGΦ : ∀ x, ‖GΦ x‖ ^ 2 = {y | ε * η y < |ℓ y|}.indicator
      (fun y ↦ A ^ 2 * (1 + ε ^ 2 * ‖∇ η y‖ ^ 2)) x := by
    intro x
    have hηx := cylBump_nonneg (e := e) x
    have hw : inner ℝ (∇ η x) e = 0 := inner_gradient_cylBump he x
    rw [hGΦdef]
    simp only
    by_cases h1 : 0 < ℓ x - ε * η x
    · have h2 : ¬ 0 < -ℓ x - ε * η x := by nlinarith
      have h3 : ε * η x < |ℓ x| := by rw [abs_of_pos (by linarith)]; linarith
      rw [indicator_of_mem (show x ∈ {y | 0 < ℓ y - ε * η y} from h1),
        indicator_of_notMem (show x ∉ {y | 0 < -ℓ y - ε * η y} from h2),
        indicator_of_mem (show x ∈ {y | ε * η y < |ℓ y|} from h3), add_zero, norm_smul, mul_pow,
        norm_sub_smul_sq he hw, Real.norm_eq_abs, sq_abs]
    · by_cases h2 : 0 < -ℓ x - ε * η x
      · have h3 : ε * η x < |ℓ x| := by rw [abs_of_neg (by linarith)]; linarith
        have he' : ‖-e‖ = 1 := by rw [norm_neg, he]
        have hw' : inner ℝ (∇ η x) (-e) = 0 := by rw [inner_neg_right, hw, neg_zero]
        rw [indicator_of_notMem (show x ∉ {y | 0 < ℓ y - ε * η y} from h1),
          indicator_of_mem (show x ∈ {y | 0 < -ℓ y - ε * η y} from h2),
          indicator_of_mem (show x ∈ {y | ε * η y < |ℓ y|} from h3), zero_add, norm_smul, mul_pow,
          norm_sub_smul_sq he' hw', Real.norm_eq_abs, sq_abs]
      · have h3 : ¬ ε * η x < |ℓ x| := by
          rcases le_total 0 (ℓ x) with h | h
          · rw [abs_of_nonneg h]; linarith
          · rw [abs_of_nonpos h]; linarith
        rw [indicator_of_notMem (show x ∉ {y | 0 < ℓ y - ε * η y} from h1),
          indicator_of_notMem (show x ∉ {y | 0 < -ℓ y - ε * η y} from h2),
          indicator_of_notMem (show x ∉ {y | ε * η y < |ℓ y|} from h3)]
        simp
  -- admissibility
  have hle : ∀ᵐ y ∂(volume.restrict univ), ψ y ≤ φ y :=
    Eventually.of_forall fun y ↦ by rw [hψdef]; simp only; linarith [le_max_right (φ y - Φ y) 0]
  have heq : ∀ᵐ y ∂(volume.restrict (univ \ ball 0 2)), ψ y = φ y := by
    refine (ae_restrict_iff' (MeasurableSet.univ.diff measurableSet_ball)).2
      (Eventually.of_forall fun y hy ↦ (hψnD y fun hyD ↦ hy.2 (hDB hyD)).1)
  have key := hmin 0 2 two_pos (subset_univ _) G ψ Gψ hu hψ hle heq
  refine absurd key (not_le.2 ?_)
  -- the energy comparison
  set K : ℝ := A ^ 2 * (1 + ε ^ 2 * M ^ 2) + q ^ 2 with hKdef
  set fψ : E (n + 1) → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal (‖Gψ x‖ ^ 2 + q ^ 2 * (posSet ψ B).indicator 1 x) with hfψdef
  set fφ : E (n + 1) → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal (‖G x‖ ^ 2 + q ^ 2 * (posSet φ B).indicator 1 x) with hfφdef
  set Fψ : E (n + 1) → ℝ≥0∞ := fun x ↦ ENNReal.ofReal ({y | ε * η y < |ℓ y|}.indicator
    (fun y ↦ A ^ 2 * (1 + ε ^ 2 * ‖∇ η y‖ ^ 2) + q ^ 2) x) with hFψdef
  have hEψ : energyJ B (fun _ ↦ q) ψ Gψ = ∫⁻ x in B, fψ x := rfl
  have hEφ : energyJ B (fun _ ↦ q) φ G = ∫⁻ x in B, fφ x := rfl
  have hBD : B ∩ D = D := inter_eq_right.2 hDB
  have hoff : ∫⁻ x in B \ D, fψ x = ∫⁻ x in B \ D, fφ x := by
    refine setLIntegral_congr_fun (hBm.diff hDm) fun x hx ↦ ?_
    obtain ⟨h1, h2⟩ := hψnD x hx.2
    have hpos : x ∈ posSet ψ B ↔ x ∈ posSet φ B := by
      simp only [posSet, mem_setOf_eq, h1]
    have hind : (posSet ψ B).indicator (1 : E (n + 1) → ℝ) x = (posSet φ B).indicator 1 x := by
      by_cases h : x ∈ posSet φ B
      · rw [indicator_of_mem h, indicator_of_mem (hpos.2 h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (mt hpos.1 h)]
    simp only [hfψdef, hfφdef, h2, hind]
  have honψ : ∫⁻ x in D, fψ x = ∫⁻ x in D, Fψ x := by
    refine setLIntegral_congr_fun hDm fun x hx ↦ ?_
    obtain ⟨h1, h2⟩ := hψD x hx
    have hxB := hDB hx
    simp only [hfψdef, hFψdef, h2, hGΦ x]
    congr 1
    by_cases h : ε * η x < |ℓ x|
    · have hp : x ∈ posSet ψ B := ⟨hxB, by rw [h1]; exact (hΦpos x).2 h⟩
      rw [indicator_of_mem (show x ∈ {y | ε * η y < |ℓ y|} from h),
        indicator_of_mem (show x ∈ {y | ε * η y < |ℓ y|} from h), indicator_of_mem hp]
      simp
    · have hp : x ∉ posSet ψ B := fun hp ↦ h ((hΦpos x).1 (h1 ▸ hp.2))
      rw [indicator_of_notMem (show x ∉ {y | ε * η y < |ℓ y|} from h),
        indicator_of_notMem (show x ∉ {y | ε * η y < |ℓ y|} from h), indicator_of_notMem hp]
      simp
  have honφ : ∫⁻ x in D, fφ x = ∫⁻ x in D, ENNReal.ofReal (α ^ 2 + q ^ 2) := by
    refine setLIntegral_congr_fun hDm fun x hx ↦ ?_
    have hℓx : ℓ x ≠ 0 := abs_pos.1 hx.1
    have hp : x ∈ posSet φ B := by
      rw [posSet_twoPlane hα]; exact ⟨hDB hx, hℓx⟩
    simp only [hfφdef, indicator_of_mem hp, hGdef, norm_twoPlaneGrad_of_ne α he hℓx, sq_abs,
      Pi.one_apply, mul_one]
  have hfin : ∫⁻ x in B \ D, fφ x ≠ (⊤ : ℝ≥0∞) := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in B, ENNReal.ofReal (α ^ 2 + q ^ 2)) ?_ ?_
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · refine (lintegral_mono_set diff_subset).trans (lintegral_mono fun x ↦ ?_)
      refine ENNReal.ofReal_le_ofReal (add_le_add ?_ ?_)
      · have := norm_twoPlaneGrad_le α he x
        rw [abs_of_pos hα] at this
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      · refine mul_le_of_le_one_right (sq_nonneg _) ?_
        by_cases h : x ∈ posSet φ B
        · simp [indicator_of_mem h]
        · simp [indicator_of_notMem h]
  rw [hEψ, hEφ, ← lintegral_inter_add_diff _ B hDm, ← lintegral_inter_add_diff fφ B hDm, hBD,
    hoff, honψ, honφ]
  refine ENNReal.add_lt_add_right hfin ?_
  -- Fubini in coordinates adapted to `e`
  set Θ := coordEquiv b with hΘdef
  set ηt : (Fin n → ℝ) → ℝ := fun y ↦ η (Θ.symm (0, y)) with hηtdef
  set gt : (Fin n → ℝ) → ℝ := fun y ↦ ‖∇ η (Θ.symm (0, y))‖ with hgtdef
  have hcoord : ∀ s y, ℓ (Θ.symm (s, y)) = s ∧ η (Θ.symm (s, y)) = ηt y ∧
      ‖∇ η (Θ.symm (s, y))‖ = gt y := by
    intro s y
    refine ⟨inner_coordEquiv_symm hb (s, y), ?_, ?_⟩
    · rw [coordEquiv_symm_eq hb, hηdef, cylBump_add_smul he]
    · rw [coordEquiv_symm_eq hb, hηdef, gradient_cylBump_add_smul he]
  have hηt0 : ∀ y, 0 ≤ ηt y := fun y ↦ cylBump_nonneg _
  have hgt0 : ∀ y, 0 ≤ gt y := fun y ↦ norm_nonneg _
  have hgtM : ∀ y, gt y ≤ M := fun y ↦ hM _
  have hΘc : Continuous fun y : Fin n → ℝ ↦ Θ.symm (0, y) :=
    (continuous_coordEquiv_symm b).comp (continuous_const.prodMk continuous_id)
  have hηtc : Continuous ηt := hηc.comp hΘc
  set Kt : (Fin n → ℝ) → ℝ := fun y ↦ A ^ 2 * (1 + ε ^ 2 * gt y ^ 2) + q ^ 2 with hKtdef
  have hKt0 : ∀ y, 0 ≤ Kt y := fun y ↦ by positivity
  have hFm : Measurable Fψ := by
    refine Measurable.ennreal_ofReal (Measurable.indicator ?_
      (isOpen_lt (continuous_const.mul hηc) hℓc.abs).measurableSet)
    exact ((continuous_const.mul (continuous_const.add
      (continuous_const.mul (hgc.norm.pow 2)))).add continuous_const).measurable
  have hFubψ : ∫⁻ x in D, Fψ x = ∫⁻ y, ENNReal.ofReal (Kt y) *
      ENNReal.ofReal (2 * (ηt y - ε * ηt y)) := by
    rw [← lintegral_indicator hDm, lintegral_eq_lintegral_coord b (hFm.indicator hDm)]
    congr 1
    funext y
    have hfun : (fun s ↦ D.indicator Fψ (Θ.symm (s, y))) =
        {s : ℝ | ε * ηt y < |s| ∧ |s| < ηt y}.indicator (fun _ ↦ ENNReal.ofReal (Kt y)) := by
      funext s
      obtain ⟨h1, h2, h3⟩ := hcoord s y
      have hεη : 0 ≤ ε * ηt y := mul_nonneg hε0.le (hηt0 y)
      by_cases hs : ε * ηt y < |s| ∧ |s| < ηt y
      · have hD : Θ.symm (s, y) ∈ D := by
          change 0 < |ℓ _| ∧ |ℓ _| < η _
          rw [h1, h2]; exact ⟨hεη.trans_lt hs.1, hs.2⟩
        rw [indicator_of_mem hD,
          indicator_of_mem (show s ∈ {s : ℝ | ε * ηt y < |s| ∧ |s| < ηt y} from hs), hFψdef]
        simp only
        rw [indicator_of_mem (show Θ.symm (s, y) ∈ {y | ε * η y < |ℓ y|} by
          change ε * η _ < |ℓ _|; rw [h1, h2]; exact hs.1), h3]
      · rw [indicator_of_notMem (show s ∉ {s : ℝ | ε * ηt y < |s| ∧ |s| < ηt y} from hs)]
        by_cases hD : Θ.symm (s, y) ∈ D
        · rw [indicator_of_mem hD, hFψdef]
          simp only
          have hD' := hD
          simp only [hDdef, mem_setOf_eq, h1, h2] at hD'
          rw [indicator_of_notMem (show Θ.symm (s, y) ∉ {y | ε * η y < |ℓ y|} by
            change ¬ ε * η _ < |ℓ _|; rw [h1, h2]; exact fun h ↦ hs ⟨h, hD'.2⟩)]
          simp
        · rw [indicator_of_notMem hD]
    have hm : MeasurableSet {s : ℝ | ε * ηt y < |s| ∧ |s| < ηt y} :=
      ((isOpen_lt continuous_const continuous_abs).inter
        (isOpen_lt continuous_abs continuous_const)).measurableSet
    rw [hfun]
    refine (lintegral_indicator_const hm _).trans ?_
    rw [volume_abs_mem_Ioo (mul_nonneg hε0.le (hηt0 y))
        (mul_le_of_le_one_left (hηt0 y) hε1.le)]
  have hFubφ : ∫⁻ x in D, ENNReal.ofReal (α ^ 2 + q ^ 2) = ∫⁻ y,
      ENNReal.ofReal (α ^ 2 + q ^ 2) * ENNReal.ofReal (2 * (ηt y - 0)) := by
    rw [← lintegral_indicator hDm, lintegral_eq_lintegral_coord b
      (measurable_const.indicator hDm)]
    congr 1
    funext y
    have hfun : (fun s ↦ D.indicator (fun _ ↦ ENNReal.ofReal (α ^ 2 + q ^ 2)) (Θ.symm (s, y))) =
        {s : ℝ | 0 < |s| ∧ |s| < ηt y}.indicator (fun _ ↦ ENNReal.ofReal (α ^ 2 + q ^ 2)) := by
      funext s
      obtain ⟨h1, h2, -⟩ := hcoord s y
      have hiff : Θ.symm (s, y) ∈ D ↔ s ∈ {s : ℝ | 0 < |s| ∧ |s| < ηt y} := by
        change (0 < |ℓ _| ∧ |ℓ _| < η _) ↔ _
        rw [h1, h2]; rfl
      by_cases hs : s ∈ {s : ℝ | 0 < |s| ∧ |s| < ηt y}
      · rw [indicator_of_mem (hiff.2 hs), indicator_of_mem hs]
      · rw [indicator_of_notMem (mt hiff.1 hs), indicator_of_notMem hs]
    have hm : MeasurableSet {s : ℝ | 0 < |s| ∧ |s| < ηt y} :=
      ((isOpen_lt continuous_const continuous_abs).inter
        (isOpen_lt continuous_abs continuous_const)).measurableSet
    rw [hfun]
    refine (lintegral_indicator_const hm _).trans ?_
    rw [volume_abs_mem_Ioo le_rfl (hηt0 y)]
  -- finiteness of the competitor's energy on `D`
  have hfinψ : ∫⁻ x in D, Fψ x ≠ (⊤ : ℝ≥0∞) := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in D, ENNReal.ofReal K) ?_ ?_
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hDB))
    · refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_
      have hK0 : 0 ≤ K := by positivity
      by_cases h : x ∈ {y | ε * η y < |ℓ y|}
      · rw [indicator_of_mem h, hKdef]
        have := pow_le_pow_left₀ (norm_nonneg _) (hM x) 2
        gcongr
      · rw [indicator_of_notMem h]; exact hK0
  rw [hFubψ, hFubφ]
  rw [hFubψ] at hfinψ
  -- pointwise comparison of the columns
  have hcol : ∀ y, Kt y * (1 - ε) < α ^ 2 + q ^ 2 := fun y ↦ by
    rw [hKtdef, hAdef]
    exact column_ineq hε0 hε1 (hgt0 y) (hgtM y) hkey
  have hIψ : ∀ y, ENNReal.ofReal (Kt y) * ENNReal.ofReal (2 * (ηt y - ε * ηt y)) =
      ENNReal.ofReal (2 * ηt y * (Kt y * (1 - ε))) := fun y ↦ by
    rw [← ENNReal.ofReal_mul (hKt0 y)]; congr 1; ring
  have hIφ : ∀ y, ENNReal.ofReal (α ^ 2 + q ^ 2) * ENNReal.ofReal (2 * (ηt y - 0)) =
      ENNReal.ofReal (2 * ηt y * (α ^ 2 + q ^ 2)) := fun y ↦ by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  simp_rw [hIψ, hIφ] at hfinψ ⊢
  have hS : volume {y : Fin n → ℝ | 0 < ηt y} ≠ 0 := by
    refine ((isOpen_lt continuous_const hηtc).measure_pos volume ⟨0, ?_⟩).ne'
    change 0 < η (Θ.symm (0, 0))
    rw [coordEquiv_symm_zero, hηdef, cylBump_zero]; exact one_pos
  refine lintegral_strict_mono_of_ae_le_of_ae_lt_on
    ((continuous_const.mul hηtc).mul continuous_const).measurable.ennreal_ofReal.aemeasurable
    hfinψ (Eventually.of_forall fun y ↦ ENNReal.ofReal_le_ofReal ?_) hS
    (Eventually.of_forall fun y hy ↦ (ENNReal.ofReal_lt_ofReal_iff ?_).2 ?_)
  · exact mul_le_mul_of_nonneg_left (hcol y).le (by linarith [hηt0 y])
  · exact mul_pos (mul_pos two_pos hy) (by positivity)
  · exact mul_lt_mul_of_pos_left (hcol y) (mul_pos two_pos hy)

end Step2Main

end PerronVariational

end
