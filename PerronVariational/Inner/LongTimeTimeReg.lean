/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import PerronVariational.Inner.LongTimeUniform
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Long-time limit: time regularity from the dissipation bound

Used in Step 1 of the proof of **[Theorem 3.14](#AFS:t.longtime-inner)** of F. Abedin, W. M.
Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981, without time monotonicity.

The paper's Step 1 says that the locally uniform limit `u_∞` of `u(·, tᵢ)` "inherits" the interior
Lipschitz estimate [(3.13)](#AFS:eqn:LipEst). Estimate [(3.13)](#AFS:eqn:LipEst) at time `tᵢ`
involves `sup |u|` over the backward cylinder `B_{2r}(x) × (tᵢ - 4r², tᵢ]`, so to get
[(3.15)](#AFS:eqn:inftyLip) (with `‖u_∞‖_{L^∞(B_{2r}(x))}`) one needs `u(·, s)` close to `u(·, tᵢ)`
uniformly for `s ∈ [tᵢ - 4r², tᵢ]`. Without monotonicity this comes from `∂ₜu ∈ L²(U_∞)`: here we
prove, with a spatial average and smooth time steps,

`|u(x, s) - u(x, t)| ≤ 2η + A_δ ∫_{B̄_δ(x) × [t, s+1]} |∂ₜu|`,

where `η` bounds the oscillation of `u(·, τ)` on `B̄_δ(x)` for `τ ∈ [t, s + 1]`
(`abs_sub_le_of_hasWeakTimeDeriv`), and deduce that `sup_{y ∈ K, s ∈ [T - c, T]}
|u(y, s) - u(y, T)| → 0` as `T → ∞` for compact `K ⊆ U`, given uniform local Lipschitz bounds in
space (`eventually_abs_sub_le_window`).

## Main results

* `PerronVariational.LongTime.abs_sub_le_of_hasWeakTimeDeriv`
* `PerronVariational.LongTime.tendsto_integral_abs_window`
* `PerronVariational.LongTime.eventually_abs_sub_le_window`
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal ContDiff

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-! ### Smooth time steps -/

/-- The smooth step from `0` (for `τ ≤ a`) to `1` (for `τ ≥ a + h`). -/
noncomputable def timeStep (a h : ℝ) (τ : ℝ) : ℝ := Real.smoothTransition ((τ - a) / h)

theorem contDiff_timeStep (a h : ℝ) : ContDiff ℝ ∞ (timeStep a h) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const h)

theorem timeStep_mono (h : ℝ) (hh : 0 < h) {a b : ℝ} (hab : a ≤ b) (τ : ℝ) :
    timeStep b h τ ≤ timeStep a h τ :=
  Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hh.le)

theorem timeStep_of_le {a h τ : ℝ} (hh : 0 < h) (hτ : τ ≤ a) : timeStep a h τ = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le)

theorem timeStep_of_ge {a h τ : ℝ} (hh : 0 < h) (hτ : a + h ≤ τ) : timeStep a h τ = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hh]; linarith)

theorem deriv_timeStep_nonneg (a h : ℝ) (hh : 0 < h) (τ : ℝ) : 0 ≤ deriv (timeStep a h) τ :=
  (Real.smoothTransition.monotone.comp fun x y hxy ↦
    div_le_div_of_nonneg_right (by linarith) hh.le).deriv_nonneg

theorem deriv_timeStep_eq_zero {a h τ : ℝ} (hh : 0 < h) (hτ : τ ∉ Icc a (a + h)) :
    deriv (timeStep a h) τ = 0 := by
  rcases not_and_or.1 hτ with hτ | hτ
  · have : timeStep a h =ᶠ[𝓝 τ] fun _ ↦ 0 :=
      Filter.mem_of_superset (Iio_mem_nhds (not_le.1 hτ)) fun σ hσ ↦ timeStep_of_le hh (le_of_lt hσ)
    rw [this.deriv_eq, deriv_const]
  · have : timeStep a h =ᶠ[𝓝 τ] fun _ ↦ 1 :=
      Filter.mem_of_superset (Ioi_mem_nhds (not_le.1 hτ)) fun σ hσ ↦ timeStep_of_ge hh (le_of_lt hσ)
    rw [this.deriv_eq, deriv_const]

theorem continuous_deriv_timeStep (a h : ℝ) : Continuous (deriv (timeStep a h)) :=
  (contDiff_timeStep a h).continuous_deriv (by simp)

theorem integral_deriv_timeStep (a h : ℝ) (hh : 0 < h) : ∫ τ, deriv (timeStep a h) τ = 1 := by
  have hsupp : ∀ τ ∉ Icc a (a + h), deriv (timeStep a h) τ = 0 :=
    fun τ hτ ↦ deriv_timeStep_eq_zero hh hτ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_deriv_eq_sub (fun x _ ↦
      ((contDiff_timeStep a h).differentiable (by simp)) x)
      ((continuous_deriv_timeStep a h).intervalIntegrable _ _),
    timeStep_of_ge hh le_rfl, timeStep_of_le hh le_rfl, sub_zero]

/-! ### Averages against a space-time kernel -/

section Kernel

variable {U : Set (E d)} {u w : E d × ℝ → ℝ}

/-- The integrand `u(p) ρ(p₁) k(p₂)`, for `ρ` continuous supported in `B̄_δ(x) ⊆ U` and `k` the
derivative of a time step at `τ₀ > 0`, is integrable. -/
theorem integrable_mul_kernel (hc : ContinuousOn u (UInf U)) {ρ : E d → ℝ} (hρ : Continuous ρ)
    {x : E d} {δ τ₀ h : ℝ} (hh : 0 < h) (hτ₀ : 0 < τ₀) (hxU : closedBall x δ ⊆ U)
    (hρ0 : ∀ y ∉ closedBall x δ, ρ y = 0) :
    Integrable (fun p : E d × ℝ ↦ u p * (ρ p.1 * deriv (timeStep τ₀ h) p.2)) := by
  set Kc := closedBall x δ ×ˢ Icc τ₀ (τ₀ + h)
  have hKc : IsCompact Kc := (isCompact_closedBall x δ).prod isCompact_Icc
  have hKU : Kc ⊆ UInf U := fun p hp ↦ ⟨hxU hp.1, lt_of_lt_of_le hτ₀ hp.2.1⟩
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Kc) ?_ fun p hp ↦ ?_
  · refine ContinuousOn.integrableOn_compact hKc ((hc.mono hKU).mul ?_)
    exact ((hρ.comp continuous_fst).mul ((continuous_deriv_timeStep τ₀ h).comp
      continuous_snd)).continuousOn
  · rcases not_and_or.1 hp with h1 | h1
    · simp [hρ0 _ h1]
    · simp [deriv_timeStep_eq_zero hh h1]

/-- **Averages against `ρ ⊗ k`.** If `ρ ≥ 0` is continuous, supported in `B̄_δ(x) ⊆ U`, with
`∫ ρ = 1`, `k` is the derivative of the time step at `τ₀ > 0` of width `h`, and
`|u(y, τ) - u(x, τ₀)| ≤ η` on `B̄_δ(x) × [τ₀, τ₀ + h]`, then
`|∫_{U_∞} u ρ k - u(x, τ₀)| ≤ η`. -/
theorem abs_integral_mul_kernel_sub_le (hc : ContinuousOn u (UInf U)) {ρ : E d → ℝ}
    (hρ : Continuous ρ) (hρnn : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1)
    {x : E d} {δ τ₀ h η : ℝ} (hh : 0 < h) (hτ₀ : 0 < τ₀) (hxU : closedBall x δ ⊆ U)
    (hρ0 : ∀ y ∉ closedBall x δ, ρ y = 0)
    (hosc : ∀ τ ∈ Icc τ₀ (τ₀ + h), ∀ y ∈ closedBall x δ, |u (y, τ) - u (x, τ₀)| ≤ η) :
    |(∫ p in UInf U, u p * (ρ p.1 * deriv (timeStep τ₀ h) p.2)) - u (x, τ₀)| ≤ η := by
  set k := deriv (timeStep τ₀ h)
  set g : E d × ℝ → ℝ := fun p ↦ ρ p.1 * k p.2
  have hk0 : ∀ τ, 0 ≤ k τ := deriv_timeStep_nonneg τ₀ h hh
  have hg0 : ∀ p, 0 ≤ g p := fun p ↦ mul_nonneg (hρnn _) (hk0 _)
  have hgcont : Continuous g :=
    (hρ.comp continuous_fst).mul ((continuous_deriv_timeStep τ₀ h).comp continuous_snd)
  have hgsupp : ∀ p, p ∉ closedBall x δ ×ˢ Icc τ₀ (τ₀ + h) → g p = 0 := fun p hp ↦ by
    rcases not_and_or.1 hp with h1 | h1
    · simp [g, hρ0 _ h1]
    · simp [g, k, deriv_timeStep_eq_zero hh h1]
  have hKc : IsCompact (closedBall x δ ×ˢ Icc τ₀ (τ₀ + h)) :=
    (isCompact_closedBall x δ).prod isCompact_Icc
  have hgint : Integrable g :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero
      (hgcont.continuousOn.integrableOn_compact hKc) hgsupp
  have hg1 : ∫ p, g p = 1 := by
    have := integral_prod_mul (μ := (volume : Measure (E d))) (ν := (volume : Measure ℝ)) ρ k
    rw [Measure.volume_eq_prod, this, hρ1, integral_deriv_timeStep τ₀ h hh, one_mul]
  have hug := integrable_mul_kernel hc hρ hh hτ₀ hxU hρ0
  have hKU : ∀ p, p ∉ UInf U → u p * g p = 0 := fun p hp ↦ by
    rw [hgsupp p fun h' ↦ hp ⟨hxU h'.1, lt_of_lt_of_le hτ₀ h'.2.1⟩, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hKU]
  have hdiff : (∫ p, u p * g p) - u (x, τ₀) = ∫ p, (u p - u (x, τ₀)) * g p := by
    simp_rw [sub_mul]
    rw [integral_sub hug (hgint.const_mul _), integral_const_mul, hg1, mul_one]
  rw [hdiff]
  have hη : ∀ p, ‖(u p - u (x, τ₀)) * g p‖ ≤ η * g p := fun p ↦ by
    by_cases hp : p ∈ closedBall x δ ×ˢ Icc τ₀ (τ₀ + h)
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (hg0 p)]
      exact mul_le_mul_of_nonneg_right (hosc p.2 hp.2 p.1 hp.1) (hg0 p)
    · simp [hgsupp p hp]
  calc |∫ p, (u p - u (x, τ₀)) * g p| ≤ ∫ p, η * g p :=
        norm_integral_le_of_norm_le (hgint.const_mul η) (Eventually.of_forall hη)
    _ = η := by rw [integral_const_mul, hg1, mul_one]

/-- **Time regularity from `∂ₜu ∈ L¹_loc`.** Let `u` be continuous on `U_∞` with weak time
derivative `w`, `B̄_δ(x) ⊆ U`, `0 < t ≤ s`, and suppose `|u(y, τ) - u(x, τ)| ≤ η` for
`y ∈ B̄_δ(x)`, `τ ∈ [t, s + 1]`. Then
`|u(x, s) - u(x, t)| ≤ 2η + |B̄_{δ/2}|⁻¹ ∫_{B̄_δ(x) × [t, s+1]} |w|`.

Proof: test the weak time derivative with `ρ(y) (θ_t(τ) - θ_s(τ))`, `ρ` a normalized bump on
`B̄_δ(x)` and `θ_a` a smooth step from `0` to `1` on `[a, a + h]`; the left side is the difference
of two averages of `u` near `(x, s)` and `(x, t)`, which are `η + ε`-close to `u(x, s)`, `u(x, t)`
for `h` small (`abs_integral_mul_kernel_sub_le`). -/
theorem abs_sub_le_of_hasWeakTimeDeriv (hU : IsOpen U) (hc : ContinuousOn u (UInf U))
    (hw : HasWeakTimeDeriv (UInf U) u w) {x : E d} {δ t s η : ℝ} (hδ : 0 < δ)
    (hxU : closedBall x δ ⊆ U) (ht : 0 < t) (hts : t ≤ s)
    (hosc : ∀ τ ∈ Icc t (s + 1), ∀ y ∈ closedBall x δ, |u (y, τ) - u (x, τ)| ≤ η) :
    |u (x, s) - u (x, t)| ≤
      2 * η + (volume.real (closedBall x (δ / 2)))⁻¹ *
        ∫ p in closedBall x δ ×ˢ Icc t (s + 1), |w p| := by
  -- the spatial bump
  let f : ContDiffBump x := ⟨δ / 2, δ, by positivity, by linarith⟩
  set ρ := f.normed volume with hρdef
  have hρc : ContDiff ℝ ∞ ρ := f.contDiff_normed
  have hρnn : ∀ y, 0 ≤ ρ y := f.nonneg_normed
  have hρ1 : ∫ y, ρ y = 1 := f.integral_normed
  have hρ0 : ∀ y ∉ closedBall x δ, ρ y = 0 := fun y hy ↦ by
    rw [← Function.notMem_support, f.support_normed_eq]
    exact fun h' ↦ hy (ball_subset_closedBall h')
  set A := (volume.real (closedBall x (δ / 2)))⁻¹ with hA
  have hρA : ∀ y, ρ y ≤ A := fun y ↦ by
    simpa [hA, one_div] using f.normed_le_div_measure_closedBall_rIn volume y
  set Kw := closedBall x δ ×ˢ Icc t (s + 1)
  have hKw : IsCompact Kw := (isCompact_closedBall x δ).prod isCompact_Icc
  have hKwU : Kw ⊆ UInf U := fun p hp ↦ ⟨hxU hp.1, lt_of_lt_of_le ht hp.2.1⟩
  have hwK : IntegrableOn w Kw := hw.2.1.integrableOn_compact_subset hKwU hKw
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- continuity of `u(x, ·)` at `t` and `s`
  have hcx : ∀ a, 0 < a → ∃ h₀ > 0, ∀ τ ∈ Icc a (a + h₀), |u (x, τ) - u (x, a)| ≤ ε / 2 := by
    intro a ha
    have hxa : (x, a) ∈ UInf U := ⟨hxU (mem_closedBall_self hδ.le), ha⟩
    have hca : ContinuousAt (fun τ ↦ u (x, τ)) a :=
      ((hc.continuousAt ((hU.prod isOpen_Ioi).mem_nhds hxa)).comp
        (by fun_prop : Continuous fun τ : ℝ ↦ (x, τ)).continuousAt)
    obtain ⟨h₀, hh₀, hball⟩ := Metric.continuousAt_iff.1 hca (ε / 2) (half_pos hε)
    refine ⟨h₀ / 2, half_pos hh₀, fun τ hτ ↦ (hball ?_).le⟩
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
  obtain ⟨h₁, hh₁, hc₁⟩ := hcx t ht
  obtain ⟨h₂, hh₂, hc₂⟩ := hcx s (lt_of_lt_of_le ht hts)
  set h := min (min h₁ h₂) 1 with hhdef
  have hh : 0 < h := lt_min (lt_min hh₁ hh₂) one_pos
  have hh1 : h ≤ h₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hh2 : h ≤ h₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hh3 : h ≤ 1 := min_le_right _ _
  -- the two averages
  have havg : ∀ a, 0 < a → t ≤ a → a ≤ s →
      (∀ τ ∈ Icc a (a + h), |u (x, τ) - u (x, a)| ≤ ε / 2) →
      |(∫ p in UInf U, u p * (ρ p.1 * deriv (timeStep a h) p.2)) - u (x, a)| ≤ η + ε / 2 := by
    intro a ha hta has hca
    refine abs_integral_mul_kernel_sub_le hc hρc.continuous hρnn hρ1 hh ha hxU hρ0
      fun τ hτ y hy ↦ ?_
    have hτ' : τ ∈ Icc t (s + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    calc |u (y, τ) - u (x, a)| ≤ |u (y, τ) - u (x, τ)| + |u (x, τ) - u (x, a)| := by
          rw [show u (y, τ) - u (x, a) = (u (y, τ) - u (x, τ)) + (u (x, τ) - u (x, a)) by ring]
          exact abs_add_le _ _
      _ ≤ η + ε / 2 := add_le_add (hosc τ hτ' y hy) (hca τ hτ)
  have hIt := havg t ht le_rfl hts fun τ hτ ↦ hc₁ τ ⟨hτ.1, by linarith [hτ.2]⟩
  have hIs := havg s (lt_of_lt_of_le ht hts) hts le_rfl fun τ hτ ↦ hc₂ τ ⟨hτ.1, by linarith [hτ.2]⟩
  -- the test function
  set θ : ℝ → ℝ := fun τ ↦ timeStep t h τ - timeStep s h τ with hθ
  set ψ : E d × ℝ → ℝ := fun p ↦ ρ p.1 * θ p.2 with hψ
  have hθc : ContDiff ℝ ∞ θ := (contDiff_timeStep t h).sub (contDiff_timeStep s h)
  have hψc : ContDiff ℝ ∞ ψ := (hρc.comp contDiff_fst).mul (hθc.comp contDiff_snd)
  have hθ0 : ∀ τ ∉ Icc t (s + h), θ τ = 0 := fun τ hτ ↦ by
    rcases not_and_or.1 hτ with h1 | h1
    · simp only [hθ, timeStep_of_le hh (not_le.1 h1).le,
        timeStep_of_le hh ((not_le.1 h1).le.trans hts), sub_zero]
    · have h1' := not_le.1 h1
      simp only [hθ, timeStep_of_ge hh (show t + h ≤ τ by linarith),
        timeStep_of_ge hh h1'.le, sub_self]
  have hθb : ∀ τ, |θ τ| ≤ 1 := fun τ ↦ by
    have h1 := timeStep_mono h hh hts τ
    have h2 : timeStep t h τ ≤ 1 := Real.smoothTransition.le_one _
    have h3 : 0 ≤ timeStep s h τ := Real.smoothTransition.nonneg _
    rw [abs_le]; constructor <;> simp only [hθ] <;> linarith
  have hψ0 : ∀ p, p ∉ closedBall x δ ×ˢ Icc t (s + h) → ψ p = 0 := fun p hp ↦ by
    rcases not_and_or.1 hp with h1 | h1
    · simp [hψ, hρ0 _ h1]
    · simp [hψ, hθ0 _ h1]
  have hsuppψ : tsupport ψ ⊆ closedBall x δ ×ˢ Icc t (s + h) :=
    closure_minimal (fun p hp ↦ by_contra fun h' ↦ hp (hψ0 p h'))
      (isClosed_closedBall.prod isClosed_Icc)
  have hKψ : closedBall x δ ×ˢ Icc t (s + h) ⊆ Kw :=
    prod_mono subset_rfl (Icc_subset_Icc le_rfl (by linarith))
  have hψcs : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall x δ).prod isCompact_Icc) (subset_tsupport _ |>.trans hsuppψ)
  have hident := hw.2.2 ψ hψc hψcs (hsuppψ.trans (hKψ.trans hKwU))
  -- `∂ₜψ = ρ (k_t - k_s)`
  have hdt : ∀ p, dₜ ψ p = ρ p.1 * deriv (timeStep t h) p.2 - ρ p.1 * deriv (timeStep s h) p.2 :=
    fun p ↦ by
      have hd1 := ((contDiff_timeStep t h).differentiable (by simp)) p.2
      have hd2 := ((contDiff_timeStep s h).differentiable (by simp)) p.2
      simp only [dₜ, hψ, hθ]
      have hd : HasDerivAt (fun τ ↦ timeStep t h τ - timeStep s h τ)
          (deriv (timeStep t h) p.2 - deriv (timeStep s h) p.2) p.2 :=
        hd1.hasDerivAt.sub hd2.hasDerivAt
      rw [deriv_const_mul _ (by fun_prop), hd.deriv, mul_sub]
  have hlhs : ∫ p in UInf U, u p * dₜ ψ p =
      (∫ p in UInf U, u p * (ρ p.1 * deriv (timeStep t h) p.2)) -
        ∫ p in UInf U, u p * (ρ p.1 * deriv (timeStep s h) p.2) := by
    simp_rw [hdt, mul_sub]
    exact integral_sub
      (integrable_mul_kernel hc hρc.continuous hh ht hxU hρ0).integrableOn
      (integrable_mul_kernel hc hρc.continuous hh (lt_of_lt_of_le ht hts) hxU hρ0).integrableOn
  -- the right side
  have hrhs : |∫ p in UInf U, w p * ψ p| ≤ A * ∫ p in Kw, |w p| := by
    have h1 : ∫ p in UInf U, w p * ψ p = ∫ p in Kw, w p * ψ p := by
      refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
        (f := fun p ↦ w p * ψ p) (hU.prod isOpen_Ioi).measurableSet hKwU fun p hp ↦ ?_)
      rw [hψ0 p fun h' ↦ hp.2 (hKψ h'), mul_zero]
    rw [h1, ← integral_const_mul, ← Real.norm_eq_abs]
    simp_rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hwK.norm.const_mul A) (Eventually.of_forall fun p ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm A]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [hψ, abs_mul, abs_of_nonneg (hρnn _)]
    calc ρ p.1 * |θ p.2| ≤ ρ p.1 * 1 := mul_le_mul_of_nonneg_left (hθb _) (hρnn _)
      _ ≤ A := by rw [mul_one]; exact hρA _
  rw [hlhs] at hident
  set It := ∫ p in UInf U, u p * (ρ p.1 * deriv (timeStep t h) p.2)
  set Is := ∫ p in UInf U, u p * (ρ p.1 * deriv (timeStep s h) p.2)
  have hdiff : |Is - It| ≤ A * ∫ p in Kw, |w p| := by
    rw [show Is - It = -(It - Is) by ring, abs_neg, hident, abs_neg]; exact hrhs
  calc |u (x, s) - u (x, t)| ≤ |u (x, s) - Is| + |Is - It| + |It - u (x, t)| := by
        rw [show u (x, s) - u (x, t) = (u (x, s) - Is) + (Is - It) + (It - u (x, t)) by ring]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (η + ε / 2) + A * (∫ p in Kw, |w p|) + (η + ε / 2) := by
        rw [abs_sub_comm (u (x, s))]
        exact add_le_add (add_le_add hIs hdiff) hIt
    _ = 2 * η + A * (∫ p in Kw, |w p|) + ε := by ring

end Kernel

/-! ### Tails of `∂ₜu` -/

section Tail

variable {U : Set (E d)} {w : E d × ℝ → ℝ}

/-- Tails of `∫_{U_∞} |∂ₜu|²`: `∫_{U × (a, ∞)} w² → 0` as `a → ∞`. -/
theorem tendsto_setIntegral_sq_tail (hU : IsOpen U) (hw2 : MemLp w 2 (volume.restrict (UInf U))) :
    Tendsto (fun a : ℝ ↦ ∫ p in U ×ˢ Ioi a, w p ^ 2) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := fun p ↦ w p ^ 2)
    (s := fun a : ℝ ↦ U ×ˢ Ioi a) (fun a ↦ hU.measurableSet.prod measurableSet_Ioi)
    (fun a b hab ↦ prod_mono subset_rfl (Ioi_subset_Ioi hab)) ⟨0, hw2.integrable_sq⟩
  have hempty : (⋂ a : ℝ, U ×ˢ Ioi a) = ∅ := by
    ext p
    simp only [mem_iInter, mem_prod, mem_Ioi, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨p.2, fun h' ↦ lt_irrefl _ h'.2⟩
  rwa [hempty, Measure.restrict_empty, integral_zero_measure] at h

/-- **Windows of `∂ₜu` in `L¹`.** For compact `K ⊆ U` and `c ≥ 0`,
`∫_{K × [a, a + c]} |∂ₜu| → 0` as `a → ∞` (from `∂ₜu ∈ L²(U_∞)`, via `|w| ≤ w²/λ + λ/4`). -/
theorem tendsto_integral_abs_window (hU : IsOpen U) (hwl : LocallyIntegrableOn w (UInf U))
    (hw2 : MemLp w 2 (volume.restrict (UInf U))) {K : Set (E d)} (hK : IsCompact K)
    (hKU : K ⊆ U) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun a : ℝ ↦ ∫ p in K ×ˢ Icc a (a + c), |w p|) atTop (𝓝 0) := by
  set V := volume.real K * c with hV
  have hV0 : 0 ≤ V := mul_nonneg measureReal_nonneg hc
  have hvol : ∀ a, volume.real (K ×ˢ Icc a (a + c)) = V := fun a ↦ by
    rw [Measure.volume_eq_prod, measureReal_def, Measure.prod_prod, Real.volume_Icc,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
    simp [hV, measureReal_def]
  have htail := tendsto_setIntegral_sq_tail hU hw2
  rw [Metric.tendsto_atTop] at htail ⊢
  intro ε hε
  set lam := 2 * ε / (V + 1) with hlam
  have hlam0 : 0 < lam := by positivity
  obtain ⟨T, hT⟩ := htail (lam * ε / 2) (by positivity)
  refine ⟨max (2 * T) 1, fun a ha ↦ ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le one_pos (le_max_right _ _ |>.trans ha)
  set S := K ×ˢ Icc a (a + c)
  have hSc : IsCompact S := hK.prod isCompact_Icc
  have hSU : S ⊆ UInf U := fun p hp ↦ ⟨hKU hp.1, lt_of_lt_of_le ha0 hp.2.1⟩
  have hST : S ⊆ U ×ˢ Ioi (a / 2) := fun p hp ↦ ⟨hKU hp.1, by
    have := hp.2.1; simp only [mem_Ioi]; linarith⟩
  have hfin : volume S < ⊤ := hSc.measure_lt_top
  have hw1 : IntegrableOn w S := hwl.integrableOn_compact_subset hSU hSc
  have hsq : IntegrableOn (fun p ↦ w p ^ 2) (U ×ˢ Ioi (a / 2)) :=
    IntegrableOn.mono_set (μ := volume) (t := UInf U) hw2.integrable_sq
      (prod_mono subset_rfl (Ioi_subset_Ioi (by linarith)))
  have hsqS : IntegrableOn (fun p ↦ w p ^ 2) S := hsq.mono_set hST
  have hnn : 0 ≤ ∫ p in S, |w p| := setIntegral_nonneg_of_ae (Eventually.of_forall fun _ ↦
    abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hamgm : ∀ p, |w p| ≤ w p ^ 2 / lam + lam / 4 := fun p ↦ by
    rw [div_add_div _ _ hlam0.ne' (by norm_num : (4 : ℝ) ≠ 0), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * |w p| - lam), sq_abs (w p)]
  have hT' : ∫ p in U ×ˢ Ioi (a / 2), w p ^ 2 < lam * ε / 2 := by
    have h1 := hT (a / 2) (by linarith [le_max_left (2 * T) 1, le_max_right (2 * T) 1])
    rw [Real.dist_eq, sub_zero] at h1
    exact (le_abs_self _).trans_lt h1
  have hsqle : ∫ p in S, w p ^ 2 ≤ ∫ p in U ×ˢ Ioi (a / 2), w p ^ 2 :=
    setIntegral_mono_set hsq (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall hST)
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hfin.ne
  have hrhs : IntegrableOn (fun p ↦ w p ^ 2 / lam + lam / 4) S :=
    Integrable.add (f := fun p ↦ w p ^ 2 / lam) (g := fun _ ↦ lam / 4) (hsqS.div_const lam)
      (integrable_const _)
  calc ∫ p in S, |w p| ≤ ∫ p in S, (w p ^ 2 / lam + lam / 4) :=
        setIntegral_mono hw1.abs hrhs hamgm
    _ = (∫ p in S, w p ^ 2) / lam + lam / 4 * V := by
        rw [integral_add (f := fun p ↦ w p ^ 2 / lam) (g := fun _ ↦ lam / 4) (hsqS.div_const lam)
          (integrable_const _), integral_div,
          setIntegral_const, hvol, smul_eq_mul, mul_comm]
    _ < (lam * ε / 2) / lam + lam / 4 * V := by
        gcongr
        exact hsqle.trans_lt hT'
    _ ≤ ε := by
        rw [mul_div_assoc, mul_div_cancel_left₀ _ hlam0.ne', hlam]
        have : 2 * ε / (V + 1) / 4 * V ≤ ε / 2 := by
          rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

end Tail

/-! ### Uniform closeness of backward time slices -/

section Window

variable {U : Set (E d)} {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ} {C M : ℝ}

/-- **Backward slices converge together.** For a bounded parabolic inner variational solution
satisfying [(3.13)](#AFS:eqn:LipEst), compact `K ⊆ U`, `c ≥ 0` and `ε > 0`: for all large `a`,
`|u(y, s) - u(y, a)| ≤ ε` for `y ∈ K`, `s ∈ [a - c, a]`. (From `∂ₜu ∈ L²(U_∞)`,
`abs_sub_le_of_hasWeakTimeDeriv` and the uniform spatial Lipschitz bounds from
[(3.13)](#AFS:eqn:LipEst).) -/
theorem eventually_abs_sub_le_window (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hlip : InteriorLipEst U u C) (hM : ∀ p ∈ UInf U, u p ≤ M) {K : Set (E d)}
    (hK : IsCompact K) (hKU : K ⊆ U) {c : ℝ} (hc : 0 ≤ c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in atTop, ∀ y ∈ K, ∀ s ∈ Icc (a - c) a, |u (y, s) - u (y, a)| ≤ ε := by
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  set r := min (δ₀ / 4) 1 with hr_def
  have hr : 0 < r := lt_min (by linarith) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hrδ : r ≤ δ₀ / 4 := min_le_left _ _
  set L := (C * (M / r + 1)).toNNReal with hL
  -- uniform Lipschitz bounds on the balls `B_r(y)`, `y ∈ K`, for times `τ > 4`
  have hLip : ∀ y ∈ K, ∀ τ, 4 < τ → LipschitzOnWith L (fun z ↦ u (z, τ)) (ball y r) := by
    intro y hy τ hτ
    have hball : ball y (2 * r) ⊆ U := fun z hz ↦ hδ₀U (mem_cthickening_of_dist_le z y δ₀ K hy
      (by have := mem_ball.1 hz; linarith))
    have hcyl : parCyl y τ (2 * r) ⊆ UInf U := fun q hq ↦
      ⟨hball hq.1, show 0 < q.2 by have := hq.2.1; nlinarith⟩
    exact lipschitzOnWith_slice_of_interiorLipEst hlip h hr hr1 hcyl fun q hq ↦
      abs_le.2 ⟨by linarith [h.nonneg q (hcyl hq), hM q (hcyl hq)], hM q (hcyl hq)⟩
  set δ := min (r / 2) (ε / (8 * ((L : ℝ) + 1))) with hδ_def
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  have hδr : δ ≤ r / 2 := min_le_left _ _
  have hLδ : (L : ℝ) * δ ≤ ε / 8 := by
    have h1 : δ ≤ ε / (8 * ((L : ℝ) + 1)) := min_le_right _ _
    have hL0 : (0 : ℝ) ≤ L := L.2
    calc (L : ℝ) * δ ≤ ((L : ℝ) + 1) * (ε / (8 * ((L : ℝ) + 1))) :=
          mul_le_mul (by linarith) h1 hδ.le (by linarith)
      _ = ε / 8 := by field_simp
  set K' := cthickening δ K
  have hK' : IsCompact K' := hK.cthickening
  have hK'U : K' ⊆ U := (cthickening_mono (by linarith) K).trans hδ₀U
  set A := (volume.real (closedBall (0 : E d) (δ / 2)))⁻¹ with hA
  have hA0 : 0 ≤ A := inv_nonneg.2 measureReal_nonneg
  have hwin := tendsto_integral_abs_window hU h.timeDeriv.2.1 h.timeDeriv_memL2 hK' hK'U
    (c := c + 1) (by linarith)
  have hev := (Metric.tendsto_atTop.1 hwin) (ε / (2 * (A + 1))) (by positivity)
  obtain ⟨T, hT⟩ := hev
  filter_upwards [eventually_ge_atTop (T + c), eventually_gt_atTop (c + 4)] with a haT ha4
    y hy s hs
  have hs4 : 4 < s := by linarith [hs.1]
  have hxU : closedBall y δ ⊆ U := (closedBall_subset_closedBall hδr).trans
    (fun z hz ↦ hδ₀U (mem_cthickening_of_dist_le z y δ₀ K hy
      (by have := mem_closedBall.1 hz; linarith)))
  have hosc : ∀ τ ∈ Icc s (a + 1), ∀ z ∈ closedBall y δ, |u (z, τ) - u (y, τ)| ≤ ε / 8 := by
    intro τ hτ z hz
    have hzr : z ∈ ball y r := mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith))
    have := (hLip y hy τ (by linarith [hτ.1])).dist_le_mul z hzr y (mem_ball_self hr)
    rw [Real.dist_eq] at this
    exact this.trans ((mul_le_mul_of_nonneg_left (mem_closedBall.1 hz) L.2).trans hLδ)
  have hmain := abs_sub_le_of_hasWeakTimeDeriv hU h.continuousOn h.timeDeriv hδ hxU
    (by linarith) hs.2 hosc
  rw [Measure.real, Measure.addHaar_closedBall_center, ← Measure.real] at hmain
  have hsub : closedBall y δ ×ˢ Icc s (a + 1) ⊆ K' ×ˢ Icc (a - c) (a - c + (c + 1)) :=
    prod_mono (closedBall_subset_cthickening hy δ)
      (Icc_subset_Icc hs.1 (by linarith))
  have hint : ∫ p in closedBall y δ ×ˢ Icc s (a + 1), |w p| ≤
      ∫ p in K' ×ˢ Icc (a - c) (a - c + (c + 1)), |w p| :=
    setIntegral_mono_set ((h.timeDeriv.2.1.integrableOn_compact_subset
      (fun p hp ↦ ⟨hK'U hp.1, show 0 < p.2 by linarith [hp.2.1]⟩) (hK'.prod isCompact_Icc)).abs)
      (Eventually.of_forall fun _ ↦ abs_nonneg _) (Eventually.of_forall hsub)
  have hT' := hT (a - c) (by linarith)
  rw [Real.dist_eq, sub_zero] at hT'
  have hT'' : ∫ p in K' ×ˢ Icc (a - c) (a - c + (c + 1)), |w p| ≤ ε / (2 * (A + 1)) :=
    (le_abs_self _).trans hT'.le
  rw [abs_sub_comm]
  calc |u (y, a) - u (y, s)| ≤ 2 * (ε / 8) + A * ∫ p in closedBall y δ ×ˢ Icc s (a + 1), |w p| :=
        hmain
    _ ≤ 2 * (ε / 8) + A * (ε / (2 * (A + 1))) := by gcongr; exact hint.trans hT''
    _ ≤ ε := by
        have : A * (ε / (2 * (A + 1))) ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

end Window

end LongTime

end PerronVariational

end
