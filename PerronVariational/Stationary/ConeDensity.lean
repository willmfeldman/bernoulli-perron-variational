/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Setting -- shake: keep
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Order.CompletePartialOrder

/-!
# Positive density of `{φ < 0}` at a touching point (proof of Lemma 2.9)

Measure-theoretic and calculus ingredients of the proof of Lemma 2.9 of F. Abedin, W. M. Feldman,
K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase
problem*, arXiv:2609.14981.

The paper argues that `{φ < 0}` has density `1/2` at `x₀` if `∇φ(x₀) ≠ 0`, and positive lower
density (on a thin cone) if `∇φ(x₀) = 0` and `D²φ(x₀)` has a negative eigenvalue. We only use
positive lower density, in the following scale-invariant form: there is a fixed nonempty open
`K ⊆ B₁(0)` such that `x₀ + r • K ⊆ {φ < 0}` for all small `r > 0`. Then
`|{φ < 0} ∩ B_r(x₀)| ≥ rᵈ |K| = (|K| / |B₁|) |B_r|` by scaling of Lebesgue measure.

* `volume_image_add_smul` — `|x + r • K| = rᵈ |K|`.
* `not_tendsto_density_one` — such a set `A ⊇ x + r • K`, a.e. disjoint from `S` near `x`,
  prevents `S` from having density `1` at `x`.
* `exists_scaled_neg_of_fderiv_ne_zero` — first-order case (`∇φ(x₀) ≠ 0`).
* `exists_scaled_neg_of_laplacian_neg` — second-order case (`∇φ(x₀) = 0`, `Δφ(x₀) < 0`), which
  only needs one direction `e` with `D²φ(x₀) e · e < 0`.

Both negativity lemmas use only `φ(x₀) ≤ 0` and the one-dimensional mean value theorem along
rays (`neg_of_fderiv_neg`), avoiding a multivariate second-order Taylor expansion.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal Laplacian Pointwise

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- Lebesgue measure scales as `rᵈ` under `v ↦ x + r • v`. -/
theorem volume_image_add_smul (x : E d) {r : ℝ} (hr : 0 ≤ r) (K : Set (E d)) :
    volume ((fun v ↦ x + r • v) '' K) = ENNReal.ofReal (r ^ d) * volume K := by
  have h : (fun v ↦ x + r • v) '' K = (fun y ↦ y + x) '' (r • K) := by
    rw [← image_smul, image_image]
    simp only [add_comm]
  rw [h, image_add_right, measure_preimage_add_right, Measure.addHaar_smul_of_nonneg _ hr,
    finrank_euclideanSpace_fin]

/-- **Density obstruction.** Let `K ⊆ B₁(0)` be open and nonempty, and let `A` be a (null)
measurable set with `x + r • K ⊆ A` for all `r ∈ (0, r₀)`. If `S ∩ A` is null near `x`, then
`S` does not have density `1` at `x`: `|S ∩ B_r(x)| / |B_r(x)| ≤ 1 - |K| / |B₁|` for
`r ∈ (0, r₀)`. -/
theorem not_tendsto_density_one {S A K : Set (E d)} {x : E d} {r₀ : ℝ}
    (hA : NullMeasurableSet A) (hK : IsOpen K) (hKne : K.Nonempty) (hK1 : K ⊆ ball 0 1)
    (hr₀ : 0 < r₀) (hsub : ∀ r ∈ Ioo 0 r₀, ∀ v ∈ K, x + r • v ∈ A)
    (hdisj : volume (S ∩ A ∩ ball x r₀) = 0) :
    ¬ Tendsto (fun r ↦ volume (S ∩ ball x r) / volume (ball x r)) (𝓝[>] 0) (𝓝 1) := by
  intro hT
  set m₁ := volume (ball (0 : E d) 1)
  set mK := volume K
  have hm₁0 : m₁ ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hm₁top : m₁ ≠ ∞ := measure_ball_lt_top.ne
  have hmK0 : mK ≠ 0 := (hK.measure_pos volume hKne).ne'
  set q := (m₁ - mK) / m₁
  have hq : q < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hm₁0) (Or.inl hm₁top), one_mul]
    exact ENNReal.sub_lt_self hm₁top hm₁0 hmK0
  obtain ⟨r, hlt, hr⟩ :=
    ((hT.eventually (lt_mem_nhds hq)).and (Ioo_mem_nhdsGT hr₀)).exists
  refine lt_irrefl _ (hlt.trans_le (ENNReal.div_le_of_le_mul ?_))
  set a := ENNReal.ofReal (r ^ d)
  have hball : volume (ball x r) = a * m₁ := by
    rw [Measure.addHaar_ball_of_pos _ _ hr.1, finrank_euclideanSpace_fin]
  -- the scaled copy of `K` lies in `A ∩ B_r(x)`
  have hAB : a * mK ≤ volume (A ∩ ball x r) := by
    rw [← volume_image_add_smul x hr.1.le K]
    refine measure_mono ?_
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨hsub r hr v hv, ?_⟩
    have hv1 : ‖v‖ < 1 := by simpa using hK1 hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.1.le]
    nlinarith [norm_nonneg v, hr.1]
  have hABtop : volume (A ∩ ball x r) ≠ ∞ := (measure_ball_lt_top.trans_le'
    (measure_mono inter_subset_right)).ne
  -- `S ∩ B_r` and `A ∩ B_r` are a.e. disjoint
  have hsum : volume (S ∩ ball x r) + volume (A ∩ ball x r) ≤ volume (ball x r) := by
    rw [← measure_union₀ (hA.inter measurableSet_ball.nullMeasurableSet)]
    · exact measure_mono (union_subset inter_subset_right inter_subset_right)
    · refine measure_mono_null ?_ hdisj
      rintro y ⟨⟨hyS, hyr⟩, hyA, -⟩
      exact ⟨⟨hyS, hyA⟩, ball_subset_ball hr.2.le hyr⟩
  calc volume (S ∩ ball x r) ≤ volume (ball x r) - volume (A ∩ ball x r) :=
        ENNReal.le_sub_of_add_le_right hABtop hsum
    _ ≤ a * m₁ - a * mK := by rw [hball]; exact tsub_le_tsub_left hAB _
    _ = a * (m₁ - mK) := (ENNReal.mul_sub fun _ _ ↦ ENNReal.ofReal_ne_top).symm
    _ = q * volume (ball x r) := by
        rw [hball, ← mul_assoc, mul_comm q a, mul_assoc,
          show q * m₁ = m₁ - mK from ENNReal.div_mul_cancel hm₁0 hm₁top]

/-- **Mean value along a ray.** If `φ(x) ≤ 0` and the directional derivative `Dφ(x + s v) v` is
negative for `s ∈ (0, r)`, then `φ(x + r v) < 0`. -/
theorem neg_of_fderiv_neg {φ : E d → ℝ} (hφ : Differentiable ℝ φ) {x v : E d} {r : ℝ}
    (hr : 0 < r) (hx : φ x ≤ 0) (h : ∀ s ∈ Ioo 0 r, fderiv ℝ φ (x + s • v) v < 0) :
    φ (x + r • v) < 0 := by
  set g : ℝ → ℝ := fun t ↦ φ (x + t • v)
  have hg : ∀ t, HasDerivAt g (fderiv ℝ φ (x + t • v) v) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ ↦ x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact (hφ _).hasFDerivAt.comp_hasDerivAt t hl
  obtain ⟨c, hc, hcg⟩ := exists_hasDerivAt_eq_slope g (fun t ↦ fderiv ℝ φ (x + t • v) v) hr
    (fun t _ ↦ (hg t).continuousAt.continuousWithinAt) (fun t _ ↦ hg t)
  have hneg := h c hc
  rw [hcg, div_lt_iff₀ (by linarith), zero_mul] at hneg
  have : g 0 = φ x := by simp [g]
  have : g r = φ (x + r • v) := rfl
  linarith

/-- **First-order case** (proof of Lemma 2.9). If `φ ∈ C¹`, `φ(x) ≤ 0` and `Dφ(x) ≠ 0`, then
there is a nonempty open `K ⊆ B₁(0)` with `φ < 0` on `x + r • K` for all small `r > 0`
(`K` is a truncated open cone around a direction `e` with `Dφ(x) e < 0`). -/
theorem exists_scaled_neg_of_fderiv_ne_zero {φ : E d → ℝ} (hφ : ContDiff ℝ 1 φ) {x : E d}
    (hx : φ x ≤ 0) (h : fderiv ℝ φ x ≠ 0) :
    ∃ K : Set (E d), IsOpen K ∧ K.Nonempty ∧ K ⊆ ball 0 1 ∧
      ∃ r₀ > (0 : ℝ), ∀ r ∈ Ioo 0 r₀, ∀ v ∈ K, φ (x + r • v) < 0 := by
  set L := fderiv ℝ φ x
  obtain ⟨e, he⟩ : ∃ e, L e < 0 := by
    by_contra! hcon
    refine h (ContinuousLinearMap.ext fun e ↦ le_antisymm ?_ (hcon e))
    have := hcon (-e)
    simp only [map_neg] at this
    simpa using this
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hen : 0 < ‖e‖ := norm_pos_iff.2 he0
  set ε := -L e / (2 * ‖e‖)
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hεe : ε * ‖e‖ = -L e / 2 := by
    simp only [ε]; field_simp
  refine ⟨ball 0 1 ∩ {v | L v + ε * ‖v‖ < 0}, ?_, ?_, fun v hv ↦ hv.1, ?_⟩
  · exact isOpen_ball.inter (isOpen_lt (by fun_prop) continuous_const)
  · refine ⟨(1 / (2 * ‖e‖)) • e, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity)]
      field_simp
      norm_num
    · rw [mem_setOf_eq, map_smul, norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
      have : 1 / (2 * ‖e‖) * L e + ε * (1 / (2 * ‖e‖) * ‖e‖)
          = 1 / (2 * ‖e‖) * (L e / 2) := by linear_combination (1 / (2 * ‖e‖)) * hεe
      rw [this]
      exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  · obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1
      ((hφ.continuous_fderiv one_ne_zero).continuousAt (x := x)) ε hε
    refine ⟨δ, hδ, fun r hr v hv ↦ neg_of_fderiv_neg (hφ.differentiable one_ne_zero) hr.1 hx ?_⟩
    intro s hs
    have hv1 : ‖v‖ < 1 := by simpa using hv.1
    have hdist : dist (x + s • v) x < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1.le]
      nlinarith [norm_nonneg v, hs.1, hs.2, hr.2]
    have hD := hδc hdist
    rw [dist_eq_norm] at hD
    have h1 : (fderiv ℝ φ (x + s • v) - L) v ≤ ε * ‖v‖ :=
      (le_abs_self _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hD.le (norm_nonneg v)))
    rw [ContinuousLinearMap.sub_apply] at h1
    have hv2 : L v + ε * ‖v‖ < 0 := hv.2
    linarith

/-- **Second-order case** (proof of Lemma 2.9). If `φ ∈ C²`, `φ(x) ≤ 0`, `Dφ(x) = 0` and
`Δφ(x) < 0`, then there is a nonempty open `K ⊆ B₁(0)` with `φ < 0` on `x + r • K` for all small
`r > 0` (`K` is a truncated open cone around a direction `e` with `D²φ(x) e · e < 0`). -/
theorem exists_scaled_neg_of_laplacian_neg {φ : E d → ℝ} (hφ : ContDiff ℝ 2 φ) {x : E d}
    (hx : φ x ≤ 0) (h0 : fderiv ℝ φ x = 0) (hΔ : Δ φ x < 0) :
    ∃ K : Set (E d), IsOpen K ∧ K.Nonempty ∧ K ⊆ ball 0 1 ∧
      ∃ r₀ > (0 : ℝ), ∀ r ∈ Ioo 0 r₀, ∀ v ∈ K, φ (x + r • v) < 0 := by
  set B := fderiv ℝ (fderiv ℝ φ) x
  -- a direction of negative second derivative
  obtain ⟨e, he⟩ : ∃ e, B e e < 0 := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis] at hΔ
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (g := fun _ ↦ (0 : ℝ))
      (by simpa using hΔ)
    refine ⟨stdOrthonormalBasis ℝ (E d) i, ?_⟩
    simpa [iteratedFDeriv_two_apply] using hi
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hen : 0 < ‖e‖ := norm_pos_iff.2 he0
  set μ := -B e e / (2 * ‖e‖ ^ 2)
  have hμ : 0 < μ := div_pos (by linarith) (by positivity)
  have hμe : μ * ‖e‖ ^ 2 = -B e e / 2 := by
    simp only [μ]; field_simp
  have hBcont : Continuous fun v ↦ B v v := by fun_prop
  refine ⟨ball 0 1 ∩ {v | B v v + μ * ‖v‖ ^ 2 < 0}, ?_, ?_, fun v hv ↦ hv.1, ?_⟩
  · exact isOpen_ball.inter (isOpen_lt (by fun_prop) continuous_const)
  · set t := 1 / (2 * ‖e‖)
    have ht : 0 < t := by positivity
    refine ⟨t • e, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht.le]
      simp only [t]
      field_simp
      norm_num
    · simp only [mem_setOf_eq, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, norm_smul,
        Real.norm_of_nonneg ht.le]
      have : t * (t * B e e) + μ * (t * ‖e‖) ^ 2 = t ^ 2 * (B e e / 2) := by
        linear_combination t ^ 2 * hμe
      rw [this]
      exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  · -- `Dφ(x + h) = B h + o(|h|)`
    have hdiff : HasFDerivAt (fderiv ℝ φ) B x :=
      ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt
    have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hdiff).def hμ
    obtain ⟨δ, hδ, hδc⟩ := Metric.eventually_nhds_iff.1 ho
    refine ⟨δ, hδ, fun r hr v hv ↦ neg_of_fderiv_neg
      (hφ.differentiable (by norm_num)) hr.1 hx ?_⟩
    intro s hs
    have hv1 : ‖v‖ < 1 := by simpa using hv.1
    have hsv : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hs.1.le]
    have hdist : dist (s • v) 0 < δ := by
      rw [dist_zero_right, hsv]
      nlinarith [norm_nonneg v, hs.1, hs.2, hr.2]
    have hD := hδc hdist
    rw [h0, sub_zero, hsv] at hD
    have h1 : (fderiv ℝ φ (x + s • v) - B (s • v)) v ≤ μ * (s * ‖v‖) * ‖v‖ :=
      (le_abs_self _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg v)))
    rw [ContinuousLinearMap.sub_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul] at h1
    have h2 : s * (B v v + μ * ‖v‖ ^ 2) < 0 := mul_neg_of_pos_of_neg hs.1 hv.2
    nlinarith

end PerronVariational

end
