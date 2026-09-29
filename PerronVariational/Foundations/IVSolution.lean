/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
public import InnerVariational.Defs.VariationalSolutionQ
import InnerVariational.Kernel.Subharmonic

/-!
# Inner variational solutions and the `Q`-variational solutions of bernoulli-rectifiability

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper"). Def
2.8 of the paper (`IsInnerVarSolution U Q u χ`) and `InnerVariational.IsVariationalSolutionQ` of the
dependency bernoulli-rectifiability v0.2.0 (the variational solutions of D. Kriventsov, G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591, doi:10.1002/cpa.22226, with a
Lipschitz coefficient `Q`) describe the same objects, with three differences of encoding:

* Here `u` is locally Lipschitz on `U`; bernoulli-rectifiability asks for one Lipschitz constant on
  every ball in `Ω`. On an open `V ⊆ U` on which `u` is `C`-Lipschitz the two agree.
* Here the inner variation is integrated over `U`; bernoulli-rectifiability integrates over the
  whole space. The integrand vanishes off `tsupport ξ ⊆ U` (`innerVariationQ_eq_setIntegral`).
* Def 2.8 of the paper contains `Δu = 0` in `{u > 0}`; bernoulli-rectifiability derives it
  (Kriventsov–Weiss, Prop 3.2; `IsVariationalSolution.harmonicOn_pos`). The global converse below
  uses this for constant coefficients.

* `isVariationalSolutionQ_of_isInnerVarSolution` (on an open `V ⊆ U` on which `u` is Lipschitz)
  and `exists_ball_isVariationalSolutionQ` (on a ball around each point of `U`).
* `isInnerVarSolution_univ_of_isVariationalSolutionQ` (global solutions with a constant
  coefficient `q > 0`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped NNReal Gradient Laplacian

@[expose] public section

namespace PerronVariational

namespace Foundations

variable {d : ℕ}

/-- The integrand of `innerVariationQ` (bernoulli-rectifiability) is `innerVarIntegrand`. -/
theorem innerVariationQ_eq_integral (Q u χ : E d → ℝ) (ξ : E d → E d) :
    InnerVariational.innerVariationQ Q u χ ξ = ∫ x, innerVarIntegrand Q u χ ξ x := rfl

/-- The inner variation integrand vanishes outside the support of `ξ`. -/
theorem innerVarIntegrand_eq_zero_of_notMem_tsupport (Q u χ : E d → ℝ) {ξ : E d → E d}
    {x : E d} (hx : x ∉ tsupport ξ) : innerVarIntegrand Q u χ ξ x = 0 := by
  simp [innerVarIntegrand, divergence, fderiv_of_notMem_tsupport ℝ hx,
    image_eq_zero_of_notMem_tsupport hx]

/-- For `tsupport ξ ⊆ U`, the inner variation of bernoulli-rectifiability (an integral over the
whole space) is the integral over `U` used here. -/
theorem innerVariationQ_eq_setIntegral {U : Set (E d)} (Q u χ : E d → ℝ) {ξ : E d → E d}
    (hξ : tsupport ξ ⊆ U) :
    InnerVariational.innerVariationQ Q u χ ξ = ∫ x in U, innerVarIntegrand Q u χ ξ x := by
  rw [innerVariationQ_eq_integral, setIntegral_eq_integral_of_forall_compl_eq_zero]
  exact fun x hx ↦ innerVarIntegrand_eq_zero_of_notMem_tsupport Q u χ fun h ↦ hx (hξ h)

/-- An inner variational solution (Def 2.8) in `U` is a `Q`-variational solution in the sense of
bernoulli-rectifiability on every open `V ⊆ U` on which `u` is `C`-Lipschitz. -/
theorem isVariationalSolutionQ_of_isInnerVarSolution {U V : Set (E d)} {Q u χ : E d → ℝ}
    (h : IsInnerVarSolution U Q u χ) (hV : IsOpen V) (hVU : V ⊆ U) {C : ℝ≥0}
    (hC : LipschitzOnWith C u V) : InnerVariational.IsVariationalSolutionQ V C Q u χ where
  isOpen := hV
  nonneg x hx := h.nonneg x (hVU hx)
  continuousOn := hC.continuousOn
  contDiffOn := h.c2.mono fun x hx ↦ ⟨hVU hx.1, hx.2⟩
  lipschitzOnWith x r hr := hC.mono hr
  measurable_chi := h.meas.indicator hV.measurableSet
  chi_mem x hx := h.zero_one x (hVU hx)
  posIndicator_le_chi := by
    have hpos := ae_restrict_of_ae_restrict_of_subset hVU h.pos_le
    filter_upwards [hpos, ae_restrict_mem hV.measurableSet] with x hx hxV
    by_cases hux : 0 < u x
    · rw [InnerVariational.posIndicator_of_pos hux, hx hux]
    · rw [InnerVariational.posIndicator_of_nonpos (not_lt.1 hux)]
      rcases h.zero_one x (hVU hxV) with h0 | h1 <;> simp [*]
  innerVariationQ_eq_zero ξ hξ := by
    rw [innerVariationQ_eq_setIntegral Q u χ (hξ.2.2.trans hVU)]
    exact h.stationary ξ hξ.1 hξ.2.1 (hξ.2.2.trans hVU)

/-- **Ball form.** Around every point of `U` there is a ball in `U` on which an inner
variational solution (Def 2.8) is a `Q`-variational solution in the sense of
bernoulli-rectifiability. -/
theorem exists_ball_isVariationalSolutionQ {U : Set (E d)} {Q u χ : E d → ℝ}
    (h : IsInnerVarSolution U Q u χ) (hU : IsOpen U) {x : E d} (hx : x ∈ U) :
    ∃ δ > 0, ball x δ ⊆ U ∧ ∃ C : ℝ≥0,
      InnerVariational.IsVariationalSolutionQ (ball x δ) C Q u χ := by
  obtain ⟨C, t, ht, hCt⟩ := h.locLip hx
  rw [hU.nhdsWithin_eq hx] at ht
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.1 (inter_mem ht (hU.mem_nhds hx))
  refine ⟨δ, hδ, fun y hy ↦ (hδt hy).2, C, ?_⟩
  exact isVariationalSolutionQ_of_isInnerVarSolution h isOpen_ball
    (fun y hy ↦ (hδt hy).2) (hCt.mono fun y hy ↦ (hδt hy).1)

/-- A global `Q`-variational solution (bernoulli-rectifiability) with a constant coefficient
`q > 0` is a global inner variational solution (Def 2.8). Harmonicity in `{v > 0}` comes from
`IsVariationalSolution.harmonicOn_pos` applied to `(v / q, χ)`. -/
theorem isInnerVarSolution_univ_of_isVariationalSolutionQ {q : ℝ} (hq : 0 < q) {C : ℝ≥0}
    {v χ : E d → ℝ} (h : InnerVariational.IsVariationalSolutionQ univ C (fun _ ↦ q) v χ) :
    IsInnerVarSolution univ (fun _ ↦ q) v χ where
  nonneg x hx := h.nonneg x hx
  locLip x _ := ⟨C, ball x 1, by rw [nhdsWithin_univ]; exact ball_mem_nhds x one_pos,
    h.lipschitzOnWith x 1 (subset_univ _)⟩
  c2 := by
    exact h.contDiffOn.mono fun x hx ↦ ⟨mem_univ x, hx.2⟩
  harmonic x hx := by
    have hq' : 0 < q.toNNReal := Real.toNNReal_pos.2 hq
    have hQ : (fun _ : E d ↦ q) = fun _ ↦ ((q.toNNReal : ℝ≥0) : ℝ) := by
      rw [Real.coe_toNNReal _ hq.le]
    rw [hQ, InnerVariational.isVariationalSolutionQ_const_iff hq'] at h
    have hvq : 0 < v x / (q.toNNReal : ℝ) := div_pos hx.2 (by exact_mod_cast hq')
    have hharm := (h.harmonicOn_pos (mem_univ x) hvq).const_smul (c := (q.toNNReal : ℝ))
    have hfun : ((q.toNNReal : ℝ) • fun y ↦ v y / (q.toNNReal : ℝ)) = v := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [hfun] at hharm
    exact hharm.2.self_of_nhds
  meas := by
    have := h.measurable_chi
    rwa [indicator_univ] at this
  zero_one x hx := h.chi_mem x hx
  pos_le := by
    filter_upwards [h.posIndicator_le_chi] with x hx hux
    rw [InnerVariational.posIndicator_of_pos hux] at hx
    rcases h.chi_mem x (mem_univ x) with h0 | h1
    · rw [h0] at hx; norm_num at hx
    · exact h1
  stationary ξ hLip hcpt _ := by
    rw [← innerVariationQ_eq_setIntegral _ _ _ (subset_univ _)]
    exact h.innerVariationQ_eq_zero ξ ⟨hLip, hcpt, subset_univ _⟩

end Foundations

end PerronVariational

end
