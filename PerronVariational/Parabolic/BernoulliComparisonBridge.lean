/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import PerronVariational.Parabolic.StrictBarrierEquiv
public import BernoulliComparison.Interface.Parabolic
public import BernoulliComparison.Corollary.StrictComparison

/-!
# Bridge to bernoulli-parabolic-comparison

The strict comparison principle for the parabolic Bernoulli problem,
[Theorem 3.7](#AFS:t.comparison) of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, is a result from
the literature (I. C. Kim,
*A free boundary problem arising in flame propagation*, J. Differential Equations 191 (2003),
470–489, doi:10.1016/S0022-0396(02)00195-X, Theorem 2.2). It is proved in the dependency
bernoulli-parabolic-comparison (`BernoulliComparison.para_strict_comparison`).

Cylinders, parabolic boundaries and the orderings `≺`, `≺_E` agree with the dependency's by `rfl`.
The classical strict sub/supersolutions differ: here they are the paper's, with uniform constants
`a₀, δ₀` (`IsClassicalStrictParaSubWith`), while the dependency uses the pointwise inequalities on
`\overline{{φ > 0}} ∩ (V̄ × [a, b])` and `∂{φ > 0} ∩ (V̄ × [a, b])`. The parabolic solution notions
(Definitions [3.3](#AFS:d.parabolic-supersolution) and [3.5](#AFS:d.parabolic-relaxed-subsolution))
nevertheless coincide when `Q` is continuous and positive on the open set `U`
(`isParaSuper_iff_bpc`, `isParaSub_iff_bpc`, `isParaRelaxedSub_iff_bpc`):

* a uniform barrier is a pointwise barrier (`IsClassicalStrictParaSub.toBPC`), so the dependency's
  notions imply ours;
* a pointwise barrier `φ` is replaced by a uniform barrier `ψ = φ - c (1 - ζ) ≤ φ` which agrees with
  `φ` near `\overline{{φ > 0}} ∩ (V̄ × [a, b])` (`exists_regularization_sub`,
  `exists_regularization_super`); the comparison tests for `φ` and `ψ` are equivalent, so our
  notions imply the dependency's.
-/
open Set

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Definitional agreement -/

theorem parBdry_eq_bpc (V : Set (E d)) (a b : ℝ) :
    parBdry V a b = BernoulliComparison.parBdry V a b :=
  rfl

theorem posSetP_eq_bpc (u : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) :
    posSetP u Ω = BernoulliComparison.posSetP u Ω :=
  rfl

theorem prec_iff_bpc {u v : E d × ℝ → ℝ} {Ω F : Set (E d × ℝ)} :
    Prec u v Ω F ↔ BernoulliComparison.Prec u v Ω F :=
  Iff.rfl

/-! ### Equivalence of the parabolic solution notions -/

section Equiv

variable {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}

theorem AdmissibleCyl.closure_subset {V : Set (E d)} {a b : ℝ} (h : AdmissibleCyl U I V a b) :
    closure V ⊆ U := fun x hx ↦
  (h.2.2.2 (show (x, a) ∈ closure V ×ˢ Icc a b from ⟨hx, le_rfl, h.2.2.1.le⟩)).1

theorem posSetP_univ (φ : E d × ℝ → ℝ) : posSetP φ univ = {q | 0 < φ q} := by
  ext; simp [posSetP]

/-- **[Definition 3.3](#AFS:d.parabolic-supersolution) (supersolutions) agrees with the
dependency's** when `Q` is continuous and positive on the open set `U`. -/
theorem isParaSuper_iff_bpc (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQpos : ∀ x ∈ U, 0 < Q x) :
    IsParaSuper U Q I u ↔ BernoulliComparison.IsParaSuper U Q I u := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun V a b φ hadm hφ hbd ↦ ?_⟩
    have hVU := (AdmissibleCyl.closure_subset hadm)
    obtain ⟨ψ, hψ, hψle, W, hWo, hAW, hψW⟩ :=
      exists_regularization_sub hU hQ (fun x hx ↦ (hQpos x hx).le) hadm.2.1 hVU hφ
    have hcl : closure (posSetP ψ univ) ⊆ closure (posSetP φ univ) :=
      closure_mono fun q hq ↦ ⟨mem_univ _, hq.2.trans_le (hψle q)⟩
    have hin := h3 V a b ψ hadm hψ fun p hp ↦
      (hψle p).trans_lt (hbd p ⟨hcl hp.1, hp.2⟩)
    rintro p ⟨hpcl, hpcyl⟩
    have hpK : p ∈ closure V ×ˢ Icc a b := ⟨subset_closure hpcyl.1, Ioc_subset_Icc_self hpcyl.2⟩
    have hpcl' : p ∈ closure {q | 0 < φ q} := by
      rw [← posSetP_univ]; exact hpcl
    have hpW : p ∈ W := hAW ⟨hpcl', hpK⟩
    have hpψ : p ∈ closure (posSetP ψ univ) := by
      refine closure_mono (fun q hq ↦ ?_) (hWo.inter_closure ⟨hpW, hpcl'⟩)
      exact ⟨mem_univ _, (hψW hq.1).symm ▸ hq.2⟩
    have := hin p ⟨hpψ, hpcyl⟩
    rwa [hψW hpW] at this
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun V a b φ hadm hφ hbd ↦ h3 V a b φ hadm
      (hφ.toBPC fun x hx ↦ hQpos x ((AdmissibleCyl.closure_subset hadm) hx)) hbd⟩

/-- The comparison test on the parabolic boundary transfers from a supersolution `φ` to a
regularization `ψ` equal to `φ` near `\overline{{φ > 0}} ∩ (V̄ × [a, b])`, for `u ≥ 0`. -/
theorem precOn_bdry_of_regularization {V : Set (E d)} {a b : ℝ} {φ ψ : E d × ℝ → ℝ}
    {Eset W : Set (E d × ℝ)} (hab : a ≤ b)
    (hnn : ∀ p ∈ closure V ×ˢ Icc a b, 0 ≤ u p)
    (hAW : closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b) ⊆ W) (hψW : EqOn ψ φ W)
    (hbd : PrecOn u φ Eset (parBdry V a b)) : PrecOn u ψ Eset (parBdry V a b) := by
  rintro p ⟨hpE, hpP⟩
  have hpK : p ∈ closure V ×ˢ Icc a b := by
    rcases hpP with ⟨hx, ht⟩ | ⟨hx, ht⟩
    · exact ⟨hx, by rw [mem_singleton_iff.1 ht]; exact ⟨le_rfl, hab⟩⟩
    · exact ⟨frontier_subset_closure hx, ht⟩
  have h1 := hbd p ⟨hpE, hpP⟩
  have hpos : 0 < φ p := (hnn p hpK).trans_lt h1
  rw [hψW (hAW ⟨subset_closure hpos, hpK⟩)]
  exact h1

/-- **[Definition 3.3](#AFS:d.parabolic-supersolution) (subsolutions) agrees with the
dependency's** when `Q` is continuous and positive on the open set `U`. -/
theorem isParaSub_iff_bpc (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQpos : ∀ x ∈ U, 0 < Q x) :
    IsParaSub U Q I u ↔ BernoulliComparison.IsParaSub U Q I u := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun V a b φ hadm hφ hbd ↦ ?_⟩
    obtain ⟨ψ, hψ, hψle, W, -, hAW, hψW⟩ :=
      exists_regularization_super hU hQ hadm.2.1 (AdmissibleCyl.closure_subset hadm) hφ
    have hin := h3 V a b ψ hadm hψ (precOn_bdry_of_regularization hadm.2.2.1.le
      (fun p hp ↦ h2 p (hadm.2.2.2 hp)) hAW hψW hbd)
    exact fun p hp ↦ (hin p hp).trans_le (hψle p)
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun V a b φ hadm hφ hbd ↦ h3 V a b φ hadm
      (hφ.toBPC fun x hx ↦ hQpos x ((AdmissibleCyl.closure_subset hadm) hx)) hbd⟩

/-- **[Definition 3.5](#AFS:d.parabolic-relaxed-subsolution) (relaxed subsolutions) agrees with
the dependency's** when `Q` is continuous and positive on the open set `U`. -/
theorem isParaRelaxedSub_iff_bpc (hU : IsOpen U) (hQ : ContinuousOn Q U)
    (hQpos : ∀ x ∈ U, 0 < Q x) {Eset : Set (E d × ℝ)} :
    IsParaRelaxedSub U Q I u Eset ↔ BernoulliComparison.IsParaRelaxedSub U Q I u Eset := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, fun V a b φ hadm hφ hbd ↦ ?_⟩
    obtain ⟨ψ, hψ, hψle, W, -, hAW, hψW⟩ :=
      exists_regularization_super hU hQ hadm.2.1 (AdmissibleCyl.closure_subset hadm) hφ
    have hin := h6 V a b ψ hadm hψ (precOn_bdry_of_regularization hadm.2.2.1.le
      (fun p hp ↦ h2 p (hadm.2.2.2 hp)) hAW hψW hbd)
    exact fun p hp ↦ (hin p hp).trans_le (hψle p)
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, fun V a b φ hadm hφ hbd ↦ h6 V a b φ hadm
      (hφ.toBPC fun x hx ↦ hQpos x ((AdmissibleCyl.closure_subset hadm) hx)) hbd⟩

end Equiv

end PerronVariational

end
