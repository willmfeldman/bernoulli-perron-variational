/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import BernoulliComparison.Interface.Parabolic
public import PerronVariational.Semilinear.ViscosityLimitCalculus
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Classical strict parabolic barriers: uniform and pointwise forms

The paper (F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, before
[Definition 3.3](#AFS:d.parabolic-supersolution)) defines classical strict sub/supersolutions of
[(3.1)](#AFS:e.bernoulli-parabolic) on `V̄ × [a, b]` with uniform constants `1/2 ≥ a₀, δ₀ > 0`
(`IsClassicalStrictParaSubWith`, `IsClassicalStrictParaSuperWith`). The dependency
bernoulli-parabolic-comparison, which proves the comparison principle
[Theorem 3.7](#AFS:t.comparison), uses the pointwise form: `∂ₜφ - Δφ < 0` on
`\overline{{φ > 0}} ∩ (V̄ × [a, b])` and `|∇φ| > Q` on `∂{φ > 0} ∩ (V̄ × [a, b])` (resp. the reverse
inequalities).

## Main results

* `IsClassicalStrictParaSubWith.toBPC`, `IsClassicalStrictParaSuperWith.toBPC`: a uniform barrier
  is a pointwise barrier when `Q > 0` on `V̄`.
* `IsClassicalStrictParaSubWith.add_const`, `IsClassicalStrictParaSuperWith.add_const`: `φ + c`
  is again a uniform barrier, with `a₀ - |c|`, for `|c| < a₀` (the paper's "`φ - δ` is still a
  smooth strict supersolution", [Proposition 5.3](#AFS:p.semilinear-limit-viscosity), Steps 1–2).
* `exists_isClassicalStrictParaSubWith_of_nonneg` (and the super version): the pointwise
  inequalities on `{φ ≥ 0} ∩ (V̄ × [a, b])` and `{φ = 0} ∩ (V̄ × [a, b])` give uniform constants
  (compactness). This serves the bridge between the pointwise barriers of the dependency and the
  uniform ones of the paper: it is the last step of the regularization below.
* `exists_regularization_sub`, `exists_regularization_super`: a pointwise barrier `φ` can be
  replaced by a uniform barrier `ψ ≤ φ` equal to `φ` near `\overline{{φ > 0}} ∩ (V̄ × [a, b])`,
  namely `ψ = φ - c (1 - ζ)` with a smooth cutoff `ζ` equal to `1` near that set.
  This is the key step of the equivalence of the parabolic solution notions
  (`Parabolic/BernoulliComparisonBridge.lean`).
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Compactness helpers -/

section Compact

variable {X : Type*} [TopologicalSpace X]

/-- A continuous positive function on a compact set has a positive lower bound. -/
theorem exists_pos_le_of_isCompact {s : Set X} (hs : IsCompact s) {f : X → ℝ}
    (hf : ContinuousOn f s) (hpos : ∀ x ∈ s, 0 < f x) :
    ∃ m > 0, ∀ x ∈ s, m ≤ f x := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hne hf
    exact ⟨f x, hpos x hx, fun y hy ↦ hmin hy⟩

/-- **Uniform margin.** If `F > 0` on `{f ≥ 0} ∩ K` (`K` compact, `f, F` continuous on `K`), then
`F ≥ m > 0` on `{f > -a} ∩ K` for some `a > 0`. -/
theorem exists_margin_of_nonneg [T2Space X] {K : Set X} (hK : IsCompact K) {f F : X → ℝ}
    (hf : ContinuousOn f K) (hF : ContinuousOn F K) (h : ∀ p ∈ K, 0 ≤ f p → 0 < F p) :
    ∃ a > 0, ∃ m > 0, ∀ p ∈ K, -a < f p → m ≤ F p := by
  have hS : IsCompact (K ∩ f ⁻¹' Ici 0) :=
    hK.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
      inter_subset_left
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_isCompact hS (hF.mono inter_subset_left)
    fun p hp ↦ h p hp.1 hp.2
  have hB : IsCompact (K ∩ F ⁻¹' Iic (m / 2)) :=
    hK.of_isClosed_subset (hF.preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic)
      inter_subset_left
  obtain ⟨a, ha, hale⟩ := exists_pos_le_of_isCompact hB (hf.mono inter_subset_left).neg
    fun p hp ↦ by
      by_contra hc
      have hc' := not_lt.1 hc
      rw [Pi.neg_apply, neg_nonpos] at hc'
      have h1 := hmle p ⟨hp.1, hc'⟩
      have h2 : F p ≤ m / 2 := hp.2
      linarith
  refine ⟨a, ha, m / 2, by positivity, fun p hp hfp ↦ ?_⟩
  by_contra hc
  have := hale p ⟨hp, show F p ≤ m / 2 by linarith⟩
  rw [Pi.neg_apply] at this
  linarith

end Compact

/-! ### Calculus of the space-time operators -/

section Calculus

variable {φ ψ : E d × ℝ → ℝ}

theorem dₜ_add_const (φ : E d × ℝ → ℝ) (c : ℝ) (p : E d × ℝ) :
    dₜ (fun q ↦ φ q + c) p = dₜ φ p := by
  simp [dₜ]

theorem lapₓ_add_const (hφ : ContDiff ℝ 2 φ) (c : ℝ) (p : E d × ℝ) :
    lapₓ (fun q ↦ φ q + c) p = lapₓ φ p := by
  have h1 : ContDiffAt ℝ 2 (fun y : E d ↦ φ (y, p.2)) p.1 :=
    (contDiff_spaceSlice hφ p.2).contDiffAt
  have hfun : (fun y : E d ↦ φ (y, p.2) + c) = (fun y : E d ↦ φ (y, p.2)) + fun _ ↦ c := rfl
  simp only [lapₓ]
  rw [hfun, h1.laplacian_add contDiffAt_const, InnerProductSpace.laplacian_const]
  simp

theorem gradₓ_add_const (φ : E d × ℝ → ℝ) (c : ℝ) (p : E d × ℝ) :
    gradₓ (fun q ↦ φ q + c) p = gradₓ φ p := by
  simp only [gradₓ, gradient, fderiv_add_const]

theorem dₜ_add_mul (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (c : ℝ) (p : E d × ℝ) :
    dₜ (fun q ↦ φ q + c * ψ q) p = dₜ φ p + c * dₜ ψ p := by
  have h1 := ((contDiff_timeSlice hφ p.1).differentiable one_ne_zero p.2).hasDerivAt
  have h2 := ((contDiff_timeSlice hψ p.1).differentiable one_ne_zero p.2).hasDerivAt
  exact (h1.add (h2.const_mul c)).deriv

theorem lapₓ_add_mul (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (c : ℝ) (p : E d × ℝ) :
    lapₓ (fun q ↦ φ q + c * ψ q) p = lapₓ φ p + c * lapₓ ψ p := by
  have h1 : ContDiffAt ℝ 2 (fun y : E d ↦ φ (y, p.2)) p.1 :=
    (contDiff_spaceSlice hφ p.2).contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun y : E d ↦ ψ (y, p.2)) p.1 :=
    (contDiff_spaceSlice hψ p.2).contDiffAt
  have hfun : (fun y : E d ↦ φ (y, p.2) + c * ψ (y, p.2)) =
      (fun y : E d ↦ φ (y, p.2)) + c • fun y : E d ↦ ψ (y, p.2) := by
    funext y; simp
  have hcs : ContDiffAt ℝ 2 (c • fun y : E d ↦ ψ (y, p.2)) p.1 := h2.const_smul c
  simp only [lapₓ]
  rw [hfun, h1.laplacian_add hcs, InnerProductSpace.laplacian_smul c h2]
  simp

theorem gradₓ_add_mul (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (c : ℝ) (p : E d × ℝ) :
    gradₓ (fun q ↦ φ q + c * ψ q) p = gradₓ φ p + c • gradₓ ψ p := by
  have h1 := ((contDiff_spaceSlice hφ p.2).differentiable one_ne_zero p.1).hasFDerivAt
  have h2 := ((contDiff_spaceSlice hψ p.2).differentiable one_ne_zero p.1).hasFDerivAt
  have hfun : (fun y : E d ↦ φ (y, p.2) + c * ψ (y, p.2)) =
      (fun y : E d ↦ φ (y, p.2)) + c • fun y : E d ↦ ψ (y, p.2) := by
    funext y; simp
  simp only [gradₓ, gradient, hfun]
  rw [(h1.add (h2.const_smul c)).fderiv, h1.fderiv, h2.fderiv, map_add, map_smul]

end Calculus

/-! ### Two elementary inequalities -/

/-- From a gradient margin `|∇φ| + η ≤ Q` (with `Q ≤ M`) to the squared form
`|∇φ|² ≤ (1 - δ) Q²` for `δ M ≤ η`. -/
theorem sq_le_one_sub_mul_sq {x Q η M δ : ℝ} (hx : 0 ≤ x) (hxQ : x + η ≤ Q) (hη : 0 < η)
    (hQM : Q ≤ M) (hδ0 : 0 ≤ δ) (hδ : δ * M ≤ η) : x ^ 2 ≤ (1 - δ) * Q ^ 2 := by
  have hQ : η ≤ Q := by linarith
  have h1 : x ^ 2 ≤ (Q - η) ^ 2 := pow_le_pow_left₀ hx (by linarith) 2
  have h2 : δ * Q ≤ η := (mul_le_mul_of_nonneg_left hQM hδ0).trans hδ
  nlinarith [mul_le_mul_of_nonneg_right h2 (by linarith : 0 ≤ Q),
    mul_nonneg hη.le (sub_nonneg.2 hQ)]

/-- From a gradient margin `Q + η ≤ |∇φ|` (with `0 ≤ Q ≤ M`) to the squared form
`(1 + δ) Q² ≤ |∇φ|²` for `δ M ≤ η`. -/
theorem one_add_mul_sq_le {x Q η M δ : ℝ} (hQ : 0 ≤ Q) (hxQ : Q + η ≤ x) (hη : 0 < η)
    (hQM : Q ≤ M) (hδ0 : 0 ≤ δ) (hδ : δ * M ≤ η) : (1 + δ) * Q ^ 2 ≤ x ^ 2 := by
  have h1 : (Q + η) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hxQ 2
  have h2 : δ * Q ≤ η := (mul_le_mul_of_nonneg_left hQM hδ0).trans hδ
  nlinarith [mul_le_mul_of_nonneg_right h2 hQ, mul_nonneg hη.le hQ]

/-! ### Basic properties of uniform barriers -/

section Basic

variable {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)} {a b a₀ δ₀ : ℝ}

/-- A uniform strict subsolution is a pointwise one (the dependency's notion) when `Q > 0` on
`V̄`. -/
theorem IsClassicalStrictParaSubWith.toBPC (h : IsClassicalStrictParaSubWith Q φ V a b a₀ δ₀)
    (hQ : ∀ x ∈ closure V, 0 < Q x) : BernoulliComparison.IsClassicalStrictParaSub Q φ V a b := by
  have hc := h.contDiff.continuous
  refine ⟨h.contDiff, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · change dₜ φ p - lapₓ φ p < 0
    have h0 : 0 ≤ φ p := closure_lt_subset_le continuous_const hc hp.1
    have := h.heat p ⟨show -a₀ < φ p by linarith [h.a₀_pos], hp.2⟩
    linarith [h.δ₀_pos]
  · change Q p.1 < ‖gradₓ φ p‖
    have h0 : φ p = 0 := by
      rw [(isOpen_lt continuous_const hc).frontier_eq] at hp
      exact le_antisymm (not_lt.1 hp.1.2) (closure_lt_subset_le continuous_const hc hp.1.1)
    have hg := h.grad p ⟨show |φ p| ≤ a₀ by rw [h0, abs_zero]; exact h.a₀_pos.le, hp.2⟩
    have hQp := hQ p.1 hp.2.1
    have hlt : Q p.1 ^ 2 < ‖gradₓ φ p‖ ^ 2 := by
      nlinarith [mul_pos h.δ₀_pos (pow_pos hQp 2)]
    exact (pow_lt_pow_iff_left₀ hQp.le (norm_nonneg _) two_ne_zero).1 hlt

/-- A uniform strict supersolution is a pointwise one (the dependency's notion) when `Q > 0` on
`V̄`. -/
theorem IsClassicalStrictParaSuperWith.toBPC
    (h : IsClassicalStrictParaSuperWith Q φ V a b a₀ δ₀) (hQ : ∀ x ∈ closure V, 0 < Q x) :
    BernoulliComparison.IsClassicalStrictParaSuper Q φ V a b := by
  have hc := h.contDiff.continuous
  refine ⟨h.contDiff, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · change 0 < dₜ φ p - lapₓ φ p
    have h0 : 0 ≤ φ p := closure_lt_subset_le continuous_const hc hp.1
    have := h.heat p ⟨show -a₀ < φ p by linarith [h.a₀_pos], hp.2⟩
    linarith [h.δ₀_pos]
  · change ‖gradₓ φ p‖ < Q p.1
    have h0 : φ p = 0 := by
      rw [(isOpen_lt continuous_const hc).frontier_eq] at hp
      exact le_antisymm (not_lt.1 hp.1.2) (closure_lt_subset_le continuous_const hc hp.1.1)
    have hg := h.grad p ⟨show |φ p| ≤ a₀ by rw [h0, abs_zero]; exact h.a₀_pos.le, hp.2⟩
    have hQp := hQ p.1 hp.2.1
    have hlt : ‖gradₓ φ p‖ ^ 2 < Q p.1 ^ 2 := by
      nlinarith [mul_pos h.δ₀_pos (pow_pos hQp 2)]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hQp.le two_ne_zero).1 hlt

/-- Restriction to a smaller cylinder. -/
theorem IsClassicalStrictParaSubWith.mono {V' : Set (E d)} {a' b' : ℝ}
    (h : IsClassicalStrictParaSubWith Q φ V a b a₀ δ₀) (hV : closure V' ⊆ closure V)
    (ha : a ≤ a') (hb : b' ≤ b) : IsClassicalStrictParaSubWith Q φ V' a' b' a₀ δ₀ :=
  ⟨h.contDiff, h.a₀_pos, h.a₀_le, h.δ₀_pos, h.δ₀_le,
    fun p hp ↦ h.heat p ⟨hp.1, hV hp.2.1, ha.trans hp.2.2.1, hp.2.2.2.trans hb⟩,
    fun p hp ↦ h.grad p ⟨hp.1, hV hp.2.1, ha.trans hp.2.2.1, hp.2.2.2.trans hb⟩⟩

/-- Restriction to a smaller cylinder. -/
theorem IsClassicalStrictParaSuperWith.mono {V' : Set (E d)} {a' b' : ℝ}
    (h : IsClassicalStrictParaSuperWith Q φ V a b a₀ δ₀) (hV : closure V' ⊆ closure V)
    (ha : a ≤ a') (hb : b' ≤ b) : IsClassicalStrictParaSuperWith Q φ V' a' b' a₀ δ₀ :=
  ⟨h.contDiff, h.a₀_pos, h.a₀_le, h.δ₀_pos, h.δ₀_le,
    fun p hp ↦ h.heat p ⟨hp.1, hV hp.2.1, ha.trans hp.2.2.1, hp.2.2.2.trans hb⟩,
    fun p hp ↦ h.grad p ⟨hp.1, hV hp.2.1, ha.trans hp.2.2.1, hp.2.2.2.trans hb⟩⟩

/-- Smaller constants. -/
theorem IsClassicalStrictParaSubWith.mono_const {a₁ δ₁ : ℝ}
    (h : IsClassicalStrictParaSubWith Q φ V a b a₀ δ₀) (ha₁ : 0 < a₁) (ha : a₁ ≤ a₀)
    (hδ₁ : 0 < δ₁) (hδ : δ₁ ≤ δ₀) : IsClassicalStrictParaSubWith Q φ V a b a₁ δ₁ :=
  ⟨h.contDiff, ha₁, ha.trans h.a₀_le, hδ₁, hδ.trans h.δ₀_le,
    fun p hp ↦ (h.heat p ⟨(neg_le_neg ha).trans_lt hp.1, hp.2⟩).trans (neg_le_neg hδ),
    fun p hp ↦ le_trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
      (h.grad p ⟨(show |φ p| ≤ a₁ from hp.1).trans ha, hp.2⟩)⟩

/-- Smaller constants. -/
theorem IsClassicalStrictParaSuperWith.mono_const {a₁ δ₁ : ℝ}
    (h : IsClassicalStrictParaSuperWith Q φ V a b a₀ δ₀) (ha₁ : 0 < a₁) (ha : a₁ ≤ a₀)
    (hδ₁ : 0 < δ₁) (hδ : δ₁ ≤ δ₀) : IsClassicalStrictParaSuperWith Q φ V a b a₁ δ₁ :=
  ⟨h.contDiff, ha₁, ha.trans h.a₀_le, hδ₁, hδ.trans h.δ₀_le,
    fun p hp ↦ hδ.trans (h.heat p ⟨(neg_le_neg ha).trans_lt hp.1, hp.2⟩),
    fun p hp ↦ (h.grad p ⟨(show |φ p| ≤ a₁ from hp.1).trans ha, hp.2⟩).trans
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))⟩

/-- A uniform strict supersolution for `Q'` is one for every `Q ≥ Q' ≥ 0` (on `V̄`). -/
theorem IsClassicalStrictParaSuperWith.mono_Q {Q' : E d → ℝ}
    (h : IsClassicalStrictParaSuperWith Q' φ V a b a₀ δ₀)
    (hQ : ∀ x ∈ closure V, 0 ≤ Q' x ∧ Q' x ≤ Q x) :
    IsClassicalStrictParaSuperWith Q φ V a b a₀ δ₀ :=
  ⟨h.contDiff, h.a₀_pos, h.a₀_le, h.δ₀_pos, h.δ₀_le, h.heat, fun p hp ↦
    (h.grad p hp).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hQ p.1 hp.2.1).1 (hQ p.1 hp.2.1).2 2) (by linarith [h.δ₀_le]))⟩

/-- **Shifts.** For `|c| < a₀`, `φ + c` is again a uniform strict subsolution, with constants
`a₀ - |c|` and `δ₀` (the paper's "`φ + δ` is also a smooth strict subsolution",
[Proposition 5.3](#AFS:p.semilinear-limit-viscosity), Step 2). -/
theorem IsClassicalStrictParaSubWith.add_const {c : ℝ}
    (h : IsClassicalStrictParaSubWith Q φ V a b a₀ δ₀) (hc : |c| < a₀) :
    IsClassicalStrictParaSubWith Q (fun p ↦ φ p + c) V a b (a₀ - |c|) δ₀ := by
  have hφ2 : ContDiff ℝ 2 φ := h.contDiff.of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨h.contDiff.add contDiff_const, by linarith, by linarith [h.a₀_le, abs_nonneg c],
    h.δ₀_pos, h.δ₀_le, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rw [dₜ_add_const, lapₓ_add_const hφ2]
    have h1 : -(a₀ - |c|) < φ p + c := hp.1
    exact h.heat p ⟨show -a₀ < φ p by linarith [neg_abs_le c, le_abs_self c], hp.2⟩
  · rw [gradₓ_add_const]
    have h1 : |φ p + c| ≤ a₀ - |c| := hp.1
    refine h.grad p ⟨?_, hp.2⟩
    change |φ p| ≤ a₀
    have := abs_add_le (φ p + c) (-c)
    simp only [add_neg_cancel_right, abs_neg] at this
    linarith

/-- **Shifts.** For `|c| < a₀`, `φ + c` is again a uniform strict supersolution, with constants
`a₀ - |c|` and `δ₀` (the paper's "`φ - δ` is still a smooth strict supersolution",
[Proposition 5.3](#AFS:p.semilinear-limit-viscosity), Step 1). -/
theorem IsClassicalStrictParaSuperWith.add_const {c : ℝ}
    (h : IsClassicalStrictParaSuperWith Q φ V a b a₀ δ₀) (hc : |c| < a₀) :
    IsClassicalStrictParaSuperWith Q (fun p ↦ φ p + c) V a b (a₀ - |c|) δ₀ := by
  have hφ2 : ContDiff ℝ 2 φ := h.contDiff.of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨h.contDiff.add contDiff_const, by linarith, by linarith [h.a₀_le, abs_nonneg c],
    h.δ₀_pos, h.δ₀_le, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rw [dₜ_add_const, lapₓ_add_const hφ2]
    have h1 : -(a₀ - |c|) < φ p + c := hp.1
    exact h.heat p ⟨show -a₀ < φ p by linarith [neg_abs_le c, le_abs_self c], hp.2⟩
  · rw [gradₓ_add_const]
    have h1 : |φ p + c| ≤ a₀ - |c| := hp.1
    refine h.grad p ⟨?_, hp.2⟩
    change |φ p| ≤ a₀
    have := abs_add_le (φ p + c) (-c)
    simp only [add_neg_cancel_right, abs_neg] at this
    linarith

/-- **Shifts down** (the paper's "`φ - δ` is still a smooth strict supersolution",
[Proposition 5.3](#AFS:p.semilinear-limit-viscosity), Step 1): for `0 ≤ c < a₀`, `φ - c` is a
uniform strict supersolution with constants `a₀ - c, δ₀`. -/
theorem IsClassicalStrictParaSuperWith.sub_const {c : ℝ}
    (h : IsClassicalStrictParaSuperWith Q φ V a b a₀ δ₀) (hc : 0 ≤ c) (hca : c < a₀) :
    IsClassicalStrictParaSuperWith Q (fun p ↦ φ p - c) V a b (a₀ - c) δ₀ := by
  have := h.add_const (c := -c) (by rwa [abs_neg, abs_of_nonneg hc])
  rw [abs_neg, abs_of_nonneg hc] at this
  simpa only [← sub_eq_add_neg] using this

end Basic

/-! ### Uniform constants from pointwise inequalities on `{φ ≥ 0}` -/

section Upgrade

variable {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)} {a b : ℝ}

/-- **Uniform constants by compactness (subsolution).** If `∂ₜφ - Δφ < 0` on
`{φ ≥ 0} ∩ (V̄ × [a, b])` and `|∇φ|² > Q²` on `{φ = 0} ∩ (V̄ × [a, b])` (`V` bounded, `Q`
continuous on `V̄`), then `φ` is a uniform strict subsolution for some constants. -/
theorem exists_isClassicalStrictParaSubWith_of_nonneg (hφ : ContDiff ℝ ∞ φ)
    (hVb : Bornology.IsBounded V) (hQ : ContinuousOn Q (closure V))
    (h1 : ∀ p ∈ closure V ×ˢ Icc a b, 0 ≤ φ p → dₜ φ p - lapₓ φ p < 0)
    (h2 : ∀ p ∈ closure V ×ˢ Icc a b, φ p = 0 → Q p.1 ^ 2 < ‖gradₓ φ p‖ ^ 2) :
    ∃ a₀ δ₀, IsClassicalStrictParaSubWith Q φ V a b a₀ δ₀ := by
  set K := closure V ×ˢ Icc a b with hK_def
  have hK : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hheat : Continuous fun p ↦ dₜ φ p - lapₓ φ p :=
    (continuous_dₜ hφ1).sub (continuous_lapₓ hφ2)
  have hQK : ContinuousOn (fun p : E d × ℝ ↦ Q p.1 ^ 2) K :=
    (hQ.comp continuousOn_fst fun p hp ↦ hp.1).pow 2
  obtain ⟨a₁, ha₁, m₁, hm₁, hmar₁⟩ := exists_margin_of_nonneg (f := φ)
    (F := fun p ↦ -(dₜ φ p - lapₓ φ p)) hK hφ.continuous.continuousOn
    hheat.neg.continuousOn fun p hp h0 ↦ by linarith [h1 p hp h0]
  obtain ⟨a₂, ha₂, m₂, hm₂, hmar₂⟩ := exists_margin_of_nonneg (f := fun p ↦ -|φ p|)
    (F := fun p ↦ ‖gradₓ φ p‖ ^ 2 - Q p.1 ^ 2) hK hφ.continuous.abs.neg.continuousOn
    (((continuous_gradₓ hφ1).norm.pow 2).continuousOn.sub hQK) fun p hp h0 ↦ by
      have : φ p = 0 := abs_eq_zero.1 (le_antisymm (by linarith) (abs_nonneg _))
      linarith [h2 p hp this]
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hQK
  set a₀ := min (min a₁ a₂ / 2) (1 / 2) with ha₀_def
  set δ₀ := min (min m₁ (m₂ / (|M| + 1))) (1 / 2) with hδ₀_def
  have ha₀ : 0 < a₀ := lt_min (by positivity) (by norm_num)
  have hδ₀ : 0 < δ₀ := lt_min (lt_min hm₁ (by positivity)) (by norm_num)
  have ha₀₁ : a₀ < a₁ := by
    have := min_le_left (min a₁ a₂ / 2) (1 / 2); have := min_le_left a₁ a₂; linarith
  have ha₀₂ : a₀ < a₂ := by
    have := min_le_left (min a₁ a₂ / 2) (1 / 2); have := min_le_right a₁ a₂; linarith
  have hδm₁ : δ₀ ≤ m₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδm₂ : δ₀ ≤ m₂ / (|M| + 1) := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨a₀, δ₀, hφ, ha₀, min_le_right _ _, hδ₀, min_le_right _ _, fun p hp ↦ ?_,
    fun p hp ↦ ?_⟩
  · have := hmar₁ p hp.2 (by linarith [hp.1.out])
    linarith
  · have hle : |φ p| ≤ a₀ := hp.1
    have := hmar₂ p hp.2 (by linarith)
    have hQM : Q p.1 ^ 2 ≤ |M| + 1 := by
      have := hM p hp.2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at this
      linarith [le_abs_self M]
    have hkey : δ₀ * Q p.1 ^ 2 ≤ m₂ := by
      calc δ₀ * Q p.1 ^ 2 ≤ m₂ / (|M| + 1) * (|M| + 1) :=
            mul_le_mul hδm₂ hQM (sq_nonneg _) (by positivity)
        _ = m₂ := by field_simp
    nlinarith

/-- **Uniform constants by compactness (supersolution).** If `∂ₜφ - Δφ > 0` on
`{φ ≥ 0} ∩ (V̄ × [a, b])` and `|∇φ|² < Q²` on `{φ = 0} ∩ (V̄ × [a, b])` (`V` bounded, `Q`
continuous on `V̄`), then `φ` is a uniform strict supersolution for some constants. -/
theorem exists_isClassicalStrictParaSuperWith_of_nonneg (hφ : ContDiff ℝ ∞ φ)
    (hVb : Bornology.IsBounded V) (hQ : ContinuousOn Q (closure V))
    (h1 : ∀ p ∈ closure V ×ˢ Icc a b, 0 ≤ φ p → 0 < dₜ φ p - lapₓ φ p)
    (h2 : ∀ p ∈ closure V ×ˢ Icc a b, φ p = 0 → ‖gradₓ φ p‖ ^ 2 < Q p.1 ^ 2) :
    ∃ a₀ δ₀, IsClassicalStrictParaSuperWith Q φ V a b a₀ δ₀ := by
  set K := closure V ×ˢ Icc a b with hK_def
  have hK : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hheat : Continuous fun p ↦ dₜ φ p - lapₓ φ p :=
    (continuous_dₜ hφ1).sub (continuous_lapₓ hφ2)
  have hQK : ContinuousOn (fun p : E d × ℝ ↦ Q p.1 ^ 2) K :=
    (hQ.comp continuousOn_fst fun p hp ↦ hp.1).pow 2
  obtain ⟨a₁, ha₁, m₁, hm₁, hmar₁⟩ := exists_margin_of_nonneg (f := φ)
    (F := fun p ↦ dₜ φ p - lapₓ φ p) hK hφ.continuous.continuousOn hheat.continuousOn h1
  obtain ⟨a₂, ha₂, m₂, hm₂, hmar₂⟩ := exists_margin_of_nonneg (f := fun p ↦ -|φ p|)
    (F := fun p ↦ Q p.1 ^ 2 - ‖gradₓ φ p‖ ^ 2) hK hφ.continuous.abs.neg.continuousOn
    (hQK.sub ((continuous_gradₓ hφ1).norm.pow 2).continuousOn) fun p hp h0 ↦ by
      have : φ p = 0 := abs_eq_zero.1 (le_antisymm (by linarith) (abs_nonneg _))
      linarith [h2 p hp this]
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hQK
  set a₀ := min (min a₁ a₂ / 2) (1 / 2) with ha₀_def
  set δ₀ := min (min m₁ (m₂ / (|M| + 1))) (1 / 2) with hδ₀_def
  have ha₀ : 0 < a₀ := lt_min (by positivity) (by norm_num)
  have hδ₀ : 0 < δ₀ := lt_min (lt_min hm₁ (by positivity)) (by norm_num)
  have ha₀₁ : a₀ < a₁ := by
    have := min_le_left (min a₁ a₂ / 2) (1 / 2); have := min_le_left a₁ a₂; linarith
  have ha₀₂ : a₀ < a₂ := by
    have := min_le_left (min a₁ a₂ / 2) (1 / 2); have := min_le_right a₁ a₂; linarith
  have hδm₁ : δ₀ ≤ m₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδm₂ : δ₀ ≤ m₂ / (|M| + 1) := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨a₀, δ₀, hφ, ha₀, min_le_right _ _, hδ₀, min_le_right _ _, fun p hp ↦ ?_,
    fun p hp ↦ ?_⟩
  · have := hmar₁ p hp.2 (by linarith [hp.1.out])
    linarith
  · have hle : |φ p| ≤ a₀ := hp.1
    have := hmar₂ p hp.2 (by linarith)
    have hQM : Q p.1 ^ 2 ≤ |M| + 1 := by
      have := hM p hp.2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at this
      linarith [le_abs_self M]
    have hkey : δ₀ * Q p.1 ^ 2 ≤ m₂ := by
      calc δ₀ * Q p.1 ^ 2 ≤ m₂ / (|M| + 1) * (|M| + 1) :=
            mul_le_mul hδm₂ hQM (sq_nonneg _) (by positivity)
        _ = m₂ := by field_simp
    nlinarith

end Upgrade

/-! ### Regularization of pointwise barriers -/

section Regularization

variable {φ : E d × ℝ → ℝ} {K N₀ G : Set (E d × ℝ)}

/-- **Regularization of a test function away from its positivity set.** Let `K` be compact,
`A = \overline{{φ > 0}} ∩ K`, `N₀ ⊇ A` and `G ⊇ ∂{φ > 0} ∩ K` open. For every `η > 0` there is a
smooth `ψ = φ - c (1 - ζ) ≤ φ`, equal to `φ` on an open neighbourhood `W` of `A`, whose heat
operator and spatial gradient are `η`-close to those of `φ` on `K`, such that `{ψ ≥ 0} ∩ K ⊆ N₀` and
`{ψ = 0} ∩ K ⊆ G`. Here `ζ` is a smooth cutoff, `ζ = 1` near `A`, supported in a neighbourhood
of `A` where `|φ|` small forces membership in `G`, and `c > 0` is small. -/
theorem exists_regularization (hφ : ContDiff ℝ ∞ φ) (hK : IsCompact K) (hN₀ : IsOpen N₀)
    (hG : IsOpen G) (hAN : closure {q | 0 < φ q} ∩ K ⊆ N₀)
    (hAG : frontier {q | 0 < φ q} ∩ K ⊆ G) {η : ℝ} (hη : 0 < η) :
    ∃ ψ : E d × ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ p, ψ p ≤ φ p) ∧
      (∃ W, IsOpen W ∧ closure {q | 0 < φ q} ∩ K ⊆ W ∧ EqOn ψ φ W) ∧
      (∀ p ∈ K, |(dₜ ψ p - lapₓ ψ p) - (dₜ φ p - lapₓ φ p)| ≤ η) ∧
      (∀ p ∈ K, ‖gradₓ ψ p - gradₓ φ p‖ ≤ η) ∧
      (∀ p ∈ K, 0 ≤ ψ p → p ∈ N₀) ∧ (∀ p ∈ K, ψ p = 0 → p ∈ G) := by
  set P := {q | 0 < φ q} with hP_def
  set A := closure P ∩ K with hA_def
  have hc := hφ.continuous
  have hPo : IsOpen P := isOpen_lt continuous_const hc
  have hAc : IsCompact A := hK.inter_left isClosed_closure
  have hA0 : ∀ p ∈ A, 0 ≤ φ p := fun p hp ↦ closure_lt_subset_le continuous_const hc hp.1
  -- `φ ≥ ε₀ > 0` on `A \ G`
  obtain ⟨ε₀, hε₀, hε₀le⟩ := exists_pos_le_of_isCompact (hAc.inter_right hG.isClosed_compl)
    hc.continuousOn fun p hp ↦ by
      rcases (hA0 p hp.1).lt_or_eq with h | h
      · exact h
      · exfalso
        refine hp.2 (hAG ⟨?_, hp.1.2⟩)
        rw [hPo.frontier_eq]
        exact ⟨hp.1.1, fun h' ↦ by
          have : (0 : ℝ) < φ p := h'
          linarith⟩
  -- the neighbourhood `N` of `A`
  set C := (K ∩ {q | |φ q| ≤ ε₀ / 2}) ∩ Gᶜ with hC_def
  have hCc : IsClosed C :=
    (hK.isClosed.inter (isClosed_le hc.abs continuous_const)).inter hG.isClosed_compl
  set N := N₀ ∩ Cᶜ with hN_def
  have hNo : IsOpen N := hN₀.inter hCc.isOpen_compl
  have hAN' : A ⊆ N := fun p hp ↦ ⟨hAN hp, fun hpC ↦ by
    have h1 := hε₀le p ⟨hp, hpC.2⟩
    have h2 : |φ p| ≤ ε₀ / 2 := hpC.1.2
    linarith [le_abs_self (φ p)]⟩
  obtain ⟨W, hWo, hAW, hWN⟩ := normal_exists_closure_subset hAc.isClosed hNo hAN'
  obtain ⟨ζ, hζ, hζr, hζs, hζ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hNo isClosed_closure hWN
  have hζle : ∀ p, ζ p ≤ 1 := fun p ↦ (hζr (mem_range_self p)).2
  have hζ0 : ∀ p, 0 ≤ ζ p := fun p ↦ (hζr (mem_range_self p)).1
  set ζ' : E d × ℝ → ℝ := fun p ↦ ζ p - 1 with hζ'_def
  have hζ' : ContDiff ℝ ∞ ζ' := hζ.sub contDiff_const
  have hζ'1 : ContDiff ℝ 1 ζ' := hζ'.of_le (WithTop.coe_le_coe.2 le_top)
  have hζ'2 : ContDiff ℝ 2 ζ' := hζ'.of_le (WithTop.coe_le_coe.2 le_top)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn
    ((continuous_dₜ hζ'1).sub (continuous_lapₓ hζ'2)).continuousOn
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn (continuous_gradₓ hζ'1).continuousOn
  set D := |M₁| + |M₂| + 1 with hD_def
  have hD : 0 < D := by positivity
  set c := min (ε₀ / 2) (η / D) with hc_def
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  have hcε : c ≤ ε₀ / 2 := min_le_left _ _
  have hcη : c * D ≤ η := by
    calc c * D ≤ η / D * D := mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le
      _ = η := by field_simp
  set ψ : E d × ℝ → ℝ := fun p ↦ φ p + c * ζ' p with hψ_def
  -- points of `K` where `ψ ≥ 0` lie in `N`
  have hψN : ∀ p ∈ K, 0 ≤ ψ p → p ∈ N := by
    intro p hpK hψp
    by_contra hpN
    have hz : ζ p = 0 := by
      by_contra hz
      exact hpN (hζs ▸ (show p ∈ Function.support ζ from hz))
    have hφp : c ≤ φ p := by simp only [hψ_def, hζ'_def, hz] at hψp; linarith
    have hpA : p ∈ A := ⟨subset_closure (show 0 < φ p by linarith), hpK⟩
    have h1 := (hζ1 p).1 (subset_closure (hAW hpA))
    linarith
  refine ⟨ψ, hφ.add (contDiff_const.mul hζ'), fun p ↦ ?_, ⟨W, hWo, hAW, fun p hp ↦ ?_⟩,
    fun p hp ↦ ?_, fun p hp ↦ ?_, fun p hp h0 ↦ (hψN p hp h0).1, fun p hp h0 ↦ ?_⟩
  · have : c * ζ' p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0.le (by simp [hζ'_def, hζle p])
    simp only [hψ_def]
    linarith
  · have h1 := (hζ1 p).1 (subset_closure hp)
    simp [hψ_def, hζ'_def, h1]
  · rw [hψ_def, dₜ_add_mul hφ1 hζ'1, lapₓ_add_mul hφ2 hζ'2]
    have hb := hM₁ p hp
    rw [Real.norm_eq_abs, Pi.sub_apply] at hb
    have : dₜ φ p + c * dₜ ζ' p - (lapₓ φ p + c * lapₓ ζ' p) - (dₜ φ p - lapₓ φ p) =
        c * (dₜ ζ' p - lapₓ ζ' p) := by ring
    rw [this, abs_mul, abs_of_pos hc0]
    calc c * |dₜ ζ' p - lapₓ ζ' p| ≤ c * D :=
          mul_le_mul_of_nonneg_left (by linarith [abs_nonneg M₂, le_abs_self M₁]) hc0.le
      _ ≤ η := hcη
  · rw [hψ_def, gradₓ_add_mul hφ1 hζ'1, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc0]
    have hb := hM₂ p hp
    calc c * ‖gradₓ ζ' p‖ ≤ c * D :=
          mul_le_mul_of_nonneg_left (by linarith [abs_nonneg M₁, le_abs_self M₂]) hc0.le
      _ ≤ η := hcη
  · have hpN := hψN p hp h0.symm.le
    by_contra hpG
    refine hpN.2 ⟨⟨hp, ?_⟩, hpG⟩
    have h1 : φ p = c * (1 - ζ p) := by
      simp only [hψ_def, hζ'_def] at h0; linarith
    have h2 : 0 ≤ c * (1 - ζ p) := mul_nonneg hc0.le (by linarith [hζle p])
    have h3 : c * (1 - ζ p) ≤ c := by nlinarith [hζ0 p]
    change |φ p| ≤ ε₀ / 2
    rw [h1, abs_of_nonneg h2]
    linarith

/-- **Regularization of a pointwise strict subsolution** (`Q ≥ 0` continuous on the open set
`U ⊇ V̄`): a pointwise strict subsolution `φ` on `V̄ × [a, b]` can be replaced by a uniform
strict subsolution `ψ ≤ φ` equal to `φ` on an open neighbourhood of
`\overline{{φ > 0}} ∩ (V̄ × [a, b])`. -/
theorem exists_regularization_sub {U : Set (E d)} {Q : E d → ℝ} (hU : IsOpen U)
    (hQ : ContinuousOn Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x) {V : Set (E d)} {a b : ℝ}
    (hVb : Bornology.IsBounded V) (hVU : closure V ⊆ U)
    (hφ : BernoulliComparison.IsClassicalStrictParaSub Q φ V a b) :
    ∃ ψ : E d × ℝ → ℝ, (∃ a₀ δ₀, IsClassicalStrictParaSubWith Q ψ V a b a₀ δ₀) ∧
      (∀ p, ψ p ≤ φ p) ∧
      ∃ W, IsOpen W ∧ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b) ⊆ W ∧ EqOn ψ φ W := by
  obtain ⟨hφs, h1, h2⟩ := hφ
  set K := closure V ×ˢ Icc a b with hK_def
  have hK : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hφ1 : ContDiff ℝ 1 φ := hφs.of_le (WithTop.coe_le_coe.2 le_top)
  have hφ2 : ContDiff ℝ 2 φ := hφs.of_le (WithTop.coe_le_coe.2 le_top)
  have hheat : Continuous fun p ↦ dₜ φ p - lapₓ φ p :=
    (continuous_dₜ hφ1).sub (continuous_lapₓ hφ2)
  have hUo : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hgc : ContinuousOn (fun p : E d × ℝ ↦ ‖gradₓ φ p‖ - Q p.1) (U ×ˢ univ) :=
    (continuous_gradₓ hφ1).norm.continuousOn.sub (hQ.comp continuousOn_fst fun p hp ↦ hp.1)
  have hKU : K ⊆ U ×ˢ univ := fun p hp ↦ ⟨hVU hp.1, mem_univ _⟩
  -- heat margin on `A`
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_isCompact (f := fun p ↦ -(dₜ φ p - lapₓ φ p))
    (hK.inter_left isClosed_closure) hheat.neg.continuousOn fun p hp ↦ by
      have : dₜ φ p - lapₓ φ p < 0 := h1 p hp
      linarith
  -- gradient margin on `∂{φ > 0} ∩ K`
  obtain ⟨g, hg, hgle⟩ := exists_pos_le_of_isCompact (hK.inter_left isClosed_frontier)
    (hgc.mono fun p hp ↦ hKU hp.2) fun p hp ↦ by
      have : Q p.1 < ‖gradₓ φ p‖ := h2 p hp
      linarith
  set N₀ := {p | dₜ φ p - lapₓ φ p < -(m / 2)} with hN₀_def
  set G := (U ×ˢ univ) ∩ (fun p : E d × ℝ ↦ ‖gradₓ φ p‖ - Q p.1) ⁻¹' Ioi (g / 2) with hG_def
  have hN₀ : IsOpen N₀ := isOpen_lt hheat continuous_const
  have hG : IsOpen G := hgc.isOpen_inter_preimage hUo isOpen_Ioi
  obtain ⟨ψ, hψs, hψle, hW, hψheat, hψgrad, hψN, hψG⟩ := exists_regularization hφs hK hN₀ hG
    (fun p hp ↦ by
      have := hmle p hp
      change dₜ φ p - lapₓ φ p < -(m / 2)
      linarith)
    (fun p hp ↦ ⟨hKU hp.2, by
      have := hgle p hp
      change g / 2 < ‖gradₓ φ p‖ - Q p.1
      linarith⟩)
    (show 0 < min (m / 4) (g / 4) by positivity)
  refine ⟨ψ, exists_isClassicalStrictParaSubWith_of_nonneg hψs hVb (hQ.mono hVU)
    (fun p hp h0 ↦ ?_) (fun p hp h0 ↦ ?_), hψle, hW⟩
  · have h1 := hψN p hp h0
    have h2 := abs_le.1 (hψheat p hp)
    have h3 : dₜ φ p - lapₓ φ p < -(m / 2) := h1
    have h4 := min_le_left (m / 4) (g / 4)
    linarith
  · have h1 := (hψG p hp h0).2
    have h1' : g / 2 < ‖gradₓ φ p‖ - Q p.1 := h1
    have h2 := hψgrad p hp
    have h3 := min_le_right (m / 4) (g / 4)
    have h4 := norm_sub_norm_le (gradₓ φ p) (gradₓ ψ p)
    rw [norm_sub_rev] at h4
    have hQp := hQ0 p.1 (hVU hp.1)
    have hlt : Q p.1 < ‖gradₓ ψ p‖ := by linarith
    exact pow_lt_pow_left₀ hlt hQp two_ne_zero

/-- **Regularization of a pointwise strict supersolution** (`Q` continuous on the open set
`U ⊇ V̄`): a pointwise strict supersolution `φ` on `V̄ × [a, b]` can be replaced by a
uniform strict supersolution `ψ ≤ φ` equal to `φ` on an open neighbourhood of
`\overline{{φ > 0}} ∩ (V̄ × [a, b])`. -/
theorem exists_regularization_super {U : Set (E d)} {Q : E d → ℝ} (hU : IsOpen U)
    (hQ : ContinuousOn Q U) {V : Set (E d)} {a b : ℝ}
    (hVb : Bornology.IsBounded V) (hVU : closure V ⊆ U)
    (hφ : BernoulliComparison.IsClassicalStrictParaSuper Q φ V a b) :
    ∃ ψ : E d × ℝ → ℝ, (∃ a₀ δ₀, IsClassicalStrictParaSuperWith Q ψ V a b a₀ δ₀) ∧
      (∀ p, ψ p ≤ φ p) ∧
      ∃ W, IsOpen W ∧ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b) ⊆ W ∧ EqOn ψ φ W := by
  obtain ⟨hφs, h1, h2⟩ := hφ
  set K := closure V ×ˢ Icc a b with hK_def
  have hK : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hφ1 : ContDiff ℝ 1 φ := hφs.of_le (WithTop.coe_le_coe.2 le_top)
  have hφ2 : ContDiff ℝ 2 φ := hφs.of_le (WithTop.coe_le_coe.2 le_top)
  have hheat : Continuous fun p ↦ dₜ φ p - lapₓ φ p :=
    (continuous_dₜ hφ1).sub (continuous_lapₓ hφ2)
  have hUo : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hgc : ContinuousOn (fun p : E d × ℝ ↦ Q p.1 - ‖gradₓ φ p‖) (U ×ˢ univ) :=
    (hQ.comp continuousOn_fst fun p hp ↦ hp.1).sub (continuous_gradₓ hφ1).norm.continuousOn
  have hKU : K ⊆ U ×ˢ univ := fun p hp ↦ ⟨hVU hp.1, mem_univ _⟩
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_isCompact (hK.inter_left isClosed_closure)
    hheat.continuousOn fun p hp ↦ h1 p hp
  obtain ⟨g, hg, hgle⟩ := exists_pos_le_of_isCompact (hK.inter_left isClosed_frontier)
    (hgc.mono fun p hp ↦ hKU hp.2) fun p hp ↦ by
      have : ‖gradₓ φ p‖ < Q p.1 := h2 p hp
      linarith
  set N₀ := {p | m / 2 < dₜ φ p - lapₓ φ p} with hN₀_def
  set G := (U ×ˢ univ) ∩ (fun p : E d × ℝ ↦ Q p.1 - ‖gradₓ φ p‖) ⁻¹' Ioi (g / 2) with hG_def
  have hN₀ : IsOpen N₀ := isOpen_lt continuous_const hheat
  have hG : IsOpen G := hgc.isOpen_inter_preimage hUo isOpen_Ioi
  obtain ⟨ψ, hψs, hψle, hW, hψheat, hψgrad, hψN, hψG⟩ := exists_regularization hφs hK hN₀ hG
    (fun p hp ↦ by
      have := hmle p hp
      change m / 2 < dₜ φ p - lapₓ φ p
      linarith)
    (fun p hp ↦ ⟨hKU hp.2, by
      have := hgle p hp
      change g / 2 < Q p.1 - ‖gradₓ φ p‖
      linarith⟩)
    (show 0 < min (m / 4) (g / 4) by positivity)
  refine ⟨ψ, exists_isClassicalStrictParaSuperWith_of_nonneg hψs hVb (hQ.mono hVU)
    (fun p hp h0 ↦ ?_) (fun p hp h0 ↦ ?_), hψle, hW⟩
  · have h1 := hψN p hp h0
    have h2 := abs_le.1 (hψheat p hp)
    have h3 : m / 2 < dₜ φ p - lapₓ φ p := h1
    have h4 := min_le_left (m / 4) (g / 4)
    linarith
  · have h1 := (hψG p hp h0).2
    have h1' : g / 2 < Q p.1 - ‖gradₓ φ p‖ := h1
    have h2 := hψgrad p hp
    have h3 := min_le_right (m / 4) (g / 4)
    have h4 := norm_sub_norm_le (gradₓ ψ p) (gradₓ φ p)
    have hlt : ‖gradₓ ψ p‖ < Q p.1 := by linarith
    exact pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero

end Regularization

/-! ### The existential forms -/

section Exists

variable {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)} {a b : ℝ}

theorem IsClassicalStrictParaSub.contDiff (h : IsClassicalStrictParaSub Q φ V a b) :
    ContDiff ℝ ∞ φ :=
  h.choose_spec.choose_spec.contDiff

theorem IsClassicalStrictParaSuper.contDiff (h : IsClassicalStrictParaSuper Q φ V a b) :
    ContDiff ℝ ∞ φ :=
  h.choose_spec.choose_spec.contDiff

theorem IsClassicalStrictParaSub.toBPC (h : IsClassicalStrictParaSub Q φ V a b)
    (hQ : ∀ x ∈ closure V, 0 < Q x) : BernoulliComparison.IsClassicalStrictParaSub Q φ V a b :=
  h.choose_spec.choose_spec.toBPC hQ

theorem IsClassicalStrictParaSuper.toBPC (h : IsClassicalStrictParaSuper Q φ V a b)
    (hQ : ∀ x ∈ closure V, 0 < Q x) : BernoulliComparison.IsClassicalStrictParaSuper Q φ V a b :=
  h.choose_spec.choose_spec.toBPC hQ

/-- Where `φ ≥ 0` (in `V̄ × [a, b]`), a strict subsolution has `∂ₜφ - Δφ < 0`. -/
theorem IsClassicalStrictParaSub.heat_neg (h : IsClassicalStrictParaSub Q φ V a b)
    {p : E d × ℝ} (hp : p ∈ closure V ×ˢ Icc a b) (h0 : 0 ≤ φ p) : dₜ φ p - lapₓ φ p < 0 := by
  obtain ⟨a₀, δ₀, h⟩ := h
  have := h.heat p ⟨show -a₀ < φ p by linarith [h.a₀_pos], hp⟩
  linarith [h.δ₀_pos]

/-- Where `φ ≥ 0` (in `V̄ × [a, b]`), a strict supersolution has `∂ₜφ - Δφ > 0`. -/
theorem IsClassicalStrictParaSuper.heat_pos (h : IsClassicalStrictParaSuper Q φ V a b)
    {p : E d × ℝ} (hp : p ∈ closure V ×ˢ Icc a b) (h0 : 0 ≤ φ p) : 0 < dₜ φ p - lapₓ φ p := by
  obtain ⟨a₀, δ₀, h⟩ := h
  have := h.heat p ⟨show -a₀ < φ p by linarith [h.a₀_pos], hp⟩
  linarith [h.δ₀_pos]

theorem IsClassicalStrictParaSub.mono {V' : Set (E d)} {a' b' : ℝ}
    (h : IsClassicalStrictParaSub Q φ V a b) (hV : closure V' ⊆ closure V)
    (ha : a ≤ a') (hb : b' ≤ b) : IsClassicalStrictParaSub Q φ V' a' b' :=
  let ⟨a₀, δ₀, h⟩ := h
  ⟨a₀, δ₀, h.mono hV ha hb⟩

theorem IsClassicalStrictParaSuper.mono {V' : Set (E d)} {a' b' : ℝ}
    (h : IsClassicalStrictParaSuper Q φ V a b) (hV : closure V' ⊆ closure V)
    (ha : a ≤ a') (hb : b' ≤ b) : IsClassicalStrictParaSuper Q φ V' a' b' :=
  let ⟨a₀, δ₀, h⟩ := h
  ⟨a₀, δ₀, h.mono hV ha hb⟩

end Exists

end PerronVariational

end
