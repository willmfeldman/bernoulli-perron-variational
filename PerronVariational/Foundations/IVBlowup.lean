/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolutionQ
public import PerronVariational.Defs.Stationary
import InnerVariational.Statements.LipschitzQ
import PerronVariational.Foundations.IVSolution

/-!
# Blow-ups of inner variational solutions, from bernoulli-rectifiability

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper"). The
blow-up results cited by the paper (Weiss's monotonicity formula and its consequence that blow-ups
of inner variational solutions are 1-homogeneous, as used in D. Kriventsov, G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591, doi:10.1002/cpa.22226) are taken from
the dependency bernoulli-rectifiability v0.2.0 (Lake package `inner_variational`, namespace
`InnerVariational`), the Lean formalization of Kriventsov–Weiss with a Lipschitz coefficient `Q`.

* `tendstoLpLoc_one_of_tendsto_integral_abs`: the convergence of the rescaled phases used in
  bernoulli-rectifiability (`∫_K |χ(x₀ + r_k y) - χ₀(y)| dy → 0` for every compact `K`) is
  `TendstoLpLoc 1` here. For large `k` the points `x₀ + r_k y`, `y ∈ K`, lie in `U`, where `χ`
  takes values in `{0, 1}`, so the integrand is bounded and integrable on `K` and
  `‖·‖_{L¹(K)} = ∫_K |·|`.
* `blowup_homogeneous_seq_of_iv` and `blowup_homogeneous_of_iv`: the local solutions of
  `exists_ball_isVariationalSolutionQ` on a ball around `x₀`, then
  `IsVariationalSolutionQ.exists_blowup_limit` and `blowup_homogeneous` of
  bernoulli-rectifiability, then `isInnerVarSolution_univ_of_isVariationalSolutionQ` and the
  convergence lemma above. The rescaling `blowup u x₀ r` is `oneHomRescale u x₀ r` by definition.

The standing assumption `2 ≤ d` (`Setting.two_le`) supplies the instance `NeZero d` that the
homogeneity statement of bernoulli-rectifiability needs.
-/

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

@[expose] public section

namespace PerronVariational

namespace Foundations

variable {d : ℕ}

/-- **Convergence of rescaled phases.** Let `χ` be measurable with values in `{0, 1}` on the open
set `U ∋ x₀`, and `χ₀` measurable with values in `{0, 1}`. If `r_k → 0` and `∫_K |χ(x₀ + r_k y) -
χ₀(y)| dy → 0` for every compact `K`, then `χ(x₀ + r_k ·) → χ₀` in `L¹_loc(ℝᵈ)`. -/
theorem tendstoLpLoc_one_of_tendsto_integral_abs {U : Set (E d)} (hU : IsOpen U)
    {χ χ₀ : E d → ℝ} (hχ : Measurable χ) (h01 : ∀ x ∈ U, χ x = 0 ∨ χ x = 1)
    (hχ₀ : Measurable χ₀) (h01₀ : ∀ y, χ₀ y = 0 ∨ χ₀ y = 1) {x₀ : E d} (hx₀ : x₀ ∈ U)
    {r : ℕ → ℝ} (hr0 : Tendsto r atTop (𝓝 0))
    (hlim : ∀ K, IsCompact K →
      Tendsto (fun k ↦ ∫ y in K, |χ (x₀ + r k • y) - χ₀ y|) atTop (𝓝 0)) :
    TendstoLpLoc 1 volume univ (fun k y ↦ χ (x₀ + r k • y)) χ₀ atTop := by
  intro K _ hK
  -- for large `k`, `x₀ + r k • K ⊆ U`
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y ∈ K, x₀ + t • y ∈ U := by
    refine hK.eventually_forall_of_forall_eventually fun y _ ↦ ?_
    have hc : Continuous fun z : ℝ × E d ↦ x₀ + z.1 • z.2 :=
      continuous_const.add (continuous_fst.smul continuous_snd)
    exact hc.continuousAt.eventually (hU.mem_nhds (by simpa using hx₀))
  have hmeas : ∀ k, Measurable fun y ↦ χ (x₀ + r k • y) - χ₀ y := fun k ↦ by
    have hc : Continuous fun y : E d ↦ x₀ + r k • y := by fun_prop
    exact (hχ.comp hc.measurable).sub hχ₀
  have heq : ∀ᶠ k in atTop, eLpNorm ((fun y ↦ χ (x₀ + r k • y)) - χ₀) 1 (volume.restrict K) =
      ENNReal.ofReal (∫ y in K, |χ (x₀ + r k • y) - χ₀ y|) := by
    filter_upwards [hr0.eventually hev] with k hk
    have hbd : ∀ y ∈ K, ‖χ (x₀ + r k • y) - χ₀ y‖ ≤ 1 := fun y hy ↦ by
      rw [Real.norm_eq_abs, abs_le]
      rcases h01 _ (hk y hy) with h | h <;> rcases h01₀ y with h' | h' <;>
        rw [h, h'] <;> norm_num
    have hint : Integrable (fun y ↦ χ (x₀ + r k • y) - χ₀ y) (volume.restrict K) :=
      IntegrableOn.of_bound hK.measure_lt_top (hmeas k).aestronglyMeasurable 1
        (ae_restrict_of_forall_mem hK.measurableSet hbd)
    rw [eLpNorm_one_eq_lintegral_enorm
      (show AEStronglyMeasurable ((fun y ↦ χ (x₀ + r k • y)) - χ₀) (volume.restrict K) from
        (hmeas k).aestronglyMeasurable)]
    simp only [Pi.sub_apply]
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
    simp only [Real.norm_eq_abs]
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  simpa using (ENNReal.tendsto_ofReal (hlim K hK))

/-- The coefficient bounds of the standing setting on a ball in `U`, in the form used by
bernoulli-rectifiability. -/
theorem exists_qBounds_of_setting (S : Setting d) {B : Set (E d)} (hB : B ⊆ S.U) :
    ∃ L : ℝ≥0, InnerVariational.QBounds B S.Q L S.Qmin S.Qmax := by
  obtain ⟨K, hK⟩ := S.lip
  exact ⟨K, hK.mono (hB.trans subset_closure), S.Qmin_pos,
    fun x hx ↦ (S.Q_mem x (subset_closure (hB hx))).1,
    fun x hx ↦ (S.Q_mem x (subset_closure (hB hx))).2⟩

/-- **Blow-ups are 1-homogeneous, sequence form**, from bernoulli-rectifiability. See
`Registry.blowup_homogeneous_seq`. -/
theorem blowup_homogeneous_seq_of_iv (S : Setting d) {u χ : E d → ℝ}
    (h : IsInnerVarSolution S.U S.Q u χ) {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u S.U)
    {v : E d → ℝ} {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hv : TendstoLocallyUniformly (fun n ↦ blowup u x₀ (r n)) v atTop) :
    (∀ t : ℝ, 0 < t → ∀ y : E d, v (t • y) = t * v y) ∧
      ∃ (φ : ℕ → ℕ) (χ₀ : E d → ℝ), StrictMono φ ∧
        TendstoLpLoc 1 volume univ (fun n y ↦ χ (x₀ + r (φ n) • y)) χ₀ atTop ∧
        IsInnerVarSolution univ (fun _ ↦ S.Q x₀) v χ₀ := by
  have : NeZero d := ⟨by have := S.two_le; omega⟩
  obtain ⟨δ, hδ, hδU, C, hsol⟩ := exists_ball_isVariationalSolutionQ h S.isOpen hx₀.2
  obtain ⟨L, hQ⟩ := exists_qBounds_of_setting S hδU
  have hx : x₀ ∈ ball x₀ δ := mem_ball_self hδ
  have hconv : TendstoLocallyUniformly
      (fun k ↦ InnerVariational.oneHomRescale u x₀ (r k)) v atTop := hv
  obtain ⟨φ, hφ, χ₀, hsol₀, hL1⟩ := hsol.exists_blowup_limit hQ hx hr hr0 hconv
  have hq : 0 < S.Q x₀ := S.Qmin_pos.trans_le (S.Q_mem x₀ (subset_closure hx₀.2)).1
  refine ⟨hsol.blowup_homogeneous hQ hx hr hr0 hconv, φ, χ₀, hφ, ?_,
    isInnerVarSolution_univ_of_isVariationalSolutionQ hq hsol₀⟩
  have hχ₀ : Measurable χ₀ := by
    have := hsol₀.measurable_chi
    rwa [indicator_univ] at this
  exact tendstoLpLoc_one_of_tendsto_integral_abs S.isOpen h.meas h.zero_one hχ₀
    (fun y ↦ hsol₀.chi_mem y (mem_univ y)) hx₀.2 (hr0.comp hφ.tendsto_atTop) hL1

/-- **Blow-ups are 1-homogeneous**, from bernoulli-rectifiability. See
`Registry.blowup_homogeneous`. -/
theorem blowup_homogeneous_of_iv (S : Setting d) {u χ : E d → ℝ}
    (h : IsInnerVarSolution S.U S.Q u χ) {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u S.U)
    {v : E d → ℝ} (hv : IsBlowupLimit u x₀ v) :
    (∀ t : ℝ, 0 < t → ∀ y : E d, v (t • y) = t * v y) ∧
      ∃ χ₀ : E d → ℝ, IsInnerVarSolution univ (fun _ ↦ S.Q x₀) v χ₀ := by
  obtain ⟨r, hr, hr0, hconv⟩ := hv
  obtain ⟨hhom, -, χ₀, -, -, hsol⟩ := blowup_homogeneous_seq_of_iv S h hx₀ hr hr0 hconv
  exact ⟨hhom, χ₀, hsol⟩

end Foundations

end PerronVariational

end
