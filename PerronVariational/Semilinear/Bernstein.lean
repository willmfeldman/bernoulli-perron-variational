/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Bernstein change of variables (proof of Propositions A.5–A.6, Steps 2 and 4)

Steps 2 (properties (a)–(e)) and 4 (construction of `φ`) of the joint proof of Propositions A.5
and A.6 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.4).
This is pure one-variable real analysis.

Given `ε > 0`, `M ≥ 0`, put `v_max = ε + 4M`, `a = 1/(8 v_max²)`, `ρ = ε²/(64 v_max)`, and a
cutoff `ψ : ℝ → [0, 1]` (continuous, `ψ = 1` on `(-∞, 0]`, `ψ = 0` on `[1, ∞)`). Then

* `ℓ(v) = ∫_v^ε (ε⁻² ψ((s - ε)/ρ) + a) ds`, so `ℓ' = -ε⁻² ψ((v - ε)/ρ) - a` (`hasDerivAt_ell`);
* `φ'(v) = exp(∫₀^v ℓ)`, `φ(v) = ∫₀^v φ'`, so `φ'' = ℓ φ'` (`hasDerivAt_phiDeriv`,
  `hasDerivAt_phi`).

## Main results (Step 2, (a)–(e))

* (a) `one_half_le_phiDeriv`, `phiDeriv_le_exp_one`, `two_mul_le_phi_vmax`;
* (b) `le_phi_eps`;
* (c) `ellDeriv_le_of_le`, `ell_nonneg_of_le`, `ell_le_of_mem`, `one_le_phiDeriv_of_mem`;
* (d) `ellDeriv_le_neg_a`;
* (e) `ell_sq_le`.

The paper takes `ψ ∈ C^∞` nonincreasing; only continuity, `0 ≤ ψ ≤ 1` and the boundary values
are used (the smooth choice `ψ(x) = smoothTransition (1 - x)` is `IsBernsteinCutoff`, see
`isBernsteinCutoff_smoothTransition`). We in fact get `φ' ≥ 1` on `[0, v_max]`, which is
stronger than the paper's `φ' ≥ 1/2`.
-/

open Set Filter Topology intervalIntegral Real

@[expose] public section

namespace PerronVariational

namespace Bernstein

/-- The cutoff `ψ` of Step 4: continuous, `[0, 1]`-valued, `1` on `(-∞, 0]`, `0` on
`[1, ∞)`. -/
structure IsBernsteinCutoff (ψ : ℝ → ℝ) : Prop where
  continuous : Continuous ψ
  nonneg : ∀ x, 0 ≤ ψ x
  le_one : ∀ x, ψ x ≤ 1
  eq_one : ∀ x ≤ 0, ψ x = 1
  eq_zero : ∀ x, 1 ≤ x → ψ x = 0

/-- The smooth nonincreasing cutoff `x ↦ smoothTransition (1 - x)`. -/
theorem isBernsteinCutoff_smoothTransition :
    IsBernsteinCutoff fun x ↦ smoothTransition (1 - x) where
  continuous := smoothTransition.continuous.comp (continuous_const.sub continuous_id)
  nonneg _ := smoothTransition.nonneg _
  le_one _ := smoothTransition.le_one _
  eq_one x hx := smoothTransition.one_of_one_le (by linarith)
  eq_zero x hx := smoothTransition.zero_of_nonpos (by linarith)

variable (ψ : ℝ → ℝ) (ε M : ℝ)

/-- `v_max = ε + 4M` (Step 2). -/
noncomputable def vmax : ℝ := ε + 4 * M

/-- `a = 1/(8 v_max²)` (Step 2). -/
noncomputable def acoef : ℝ := 1 / (8 * vmax ε M ^ 2)

/-- `ρ = ε²/(64 v_max)` (Step 4). -/
noncomputable def rho : ℝ := ε ^ 2 / (64 * vmax ε M)

/-- The integrand `-ℓ'(s) = ε⁻² ψ((s - ε)/ρ) + a`. -/
noncomputable def ellIntegrand (s : ℝ) : ℝ := (ε ^ 2)⁻¹ * ψ ((s - ε) / rho ε M) + acoef ε M

/-- `ℓ(v) = ∫_v^ε (ε⁻² ψ((s - ε)/ρ) + a) ds` (Step 4). -/
noncomputable def ell (v : ℝ) : ℝ := ∫ s in v..ε, ellIntegrand ψ ε M s

/-- `ℓ'(v) = -ε⁻² ψ((v - ε)/ρ) - a` (Step 4). -/
noncomputable def ellDeriv (v : ℝ) : ℝ := -ellIntegrand ψ ε M v

/-- `φ'(v) = exp(∫₀^v ℓ)` (Step 4). -/
noncomputable def phiDeriv (v : ℝ) : ℝ := exp (∫ s in (0 : ℝ)..v, ell ψ ε M s)

/-- `φ(v) = ∫₀^v φ'` (Step 4). -/
noncomputable def phi (v : ℝ) : ℝ := ∫ s in (0 : ℝ)..v, phiDeriv ψ ε M s

variable {ψ ε M}

section Params

variable (hε : 0 < ε) (hM : 0 ≤ M)
include hε hM

theorem vmax_pos : 0 < vmax ε M := by unfold vmax; linarith

omit hε in
theorem eps_le_vmax : ε ≤ vmax ε M := by unfold vmax; linarith

theorem acoef_pos : 0 < acoef ε M := by
  have := vmax_pos hε hM; unfold acoef; positivity

theorem rho_pos : 0 < rho ε M := by
  have := vmax_pos hε hM; unfold rho; positivity

theorem acoef_mul_vmax_sq : acoef ε M * vmax ε M ^ 2 = 1 / 8 := by
  have := (vmax_pos hε hM).ne'; unfold acoef; field_simp

theorem acoef_mul_eps_sq_le : acoef ε M * ε ^ 2 ≤ 1 / 8 := by
  have h1 := acoef_mul_vmax_sq hε hM
  have h2 : ε ^ 2 ≤ vmax ε M ^ 2 := pow_le_pow_left₀ hε.le (eps_le_vmax hM) 2
  nlinarith [acoef_pos hε hM]

theorem rho_div_mul_vmax : rho ε M / ε ^ 2 * vmax ε M = 1 / 64 := by
  have := (vmax_pos hε hM).ne'; unfold rho; field_simp

end Params

/-! ### Calculus -/

section Calculus

variable (hψ : IsBernsteinCutoff ψ)
include hψ

theorem continuous_ellIntegrand : Continuous (ellIntegrand ψ ε M) := by
  unfold ellIntegrand
  exact (continuous_const.mul (hψ.continuous.comp
    ((continuous_id.sub continuous_const).div_const _))).add continuous_const

theorem hasDerivAt_ell (v : ℝ) : HasDerivAt (ell ψ ε M) (ellDeriv ψ ε M v) v := by
  have h := (continuous_ellIntegrand hψ (ε := ε) (M := M)).integral_hasStrictDerivAt ε v
  have : ell ψ ε M = fun u ↦ -∫ s in ε..u, ellIntegrand ψ ε M s := by
    funext u; rw [ell, integral_symm]
  rw [this, ellDeriv]
  exact h.hasDerivAt.neg

theorem continuous_ell : Continuous (ell ψ ε M) :=
  continuous_iff_continuousAt.2 fun v ↦ (hasDerivAt_ell hψ v).continuousAt

theorem hasDerivAt_phiDeriv (v : ℝ) :
    HasDerivAt (phiDeriv ψ ε M) (ell ψ ε M v * phiDeriv ψ ε M v) v := by
  have h := ((continuous_ell hψ (ε := ε) (M := M)).integral_hasStrictDerivAt 0 v).hasDerivAt.exp
  rw [mul_comm]
  exact h

theorem continuous_phiDeriv : Continuous (phiDeriv ψ ε M) :=
  continuous_iff_continuousAt.2 fun v ↦ (hasDerivAt_phiDeriv hψ v).continuousAt

theorem hasDerivAt_phi (v : ℝ) : HasDerivAt (phi ψ ε M) (phiDeriv ψ ε M v) v :=
  ((continuous_phiDeriv hψ).integral_hasStrictDerivAt 0 v).hasDerivAt

end Calculus

theorem phiDeriv_pos (v : ℝ) : 0 < phiDeriv ψ ε M v := exp_pos _

theorem phi_zero : phi ψ ε M 0 = 0 := integral_same

theorem phiDeriv_zero : phiDeriv ψ ε M 0 = 1 := by simp [phiDeriv]

/-! ### `ℓ` on `[0, ε]` and on `[ε, ∞)` -/

section Ell

variable (hψ : IsBernsteinCutoff ψ) (hε : 0 < ε) (hM : 0 ≤ M)
include hψ hε hM

theorem ellIntegrand_of_le {s : ℝ} (hs : s ≤ ε) :
    ellIntegrand ψ ε M s = (ε ^ 2)⁻¹ + acoef ε M := by
  rw [ellIntegrand, hψ.eq_one _ (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (rho_pos hε hM).le), mul_one]

omit hε hM in
theorem acoef_le_ellIntegrand (s : ℝ) : acoef ε M ≤ ellIntegrand ψ ε M s := by
  have := hψ.nonneg ((s - ε) / rho ε M)
  unfold ellIntegrand; nlinarith [inv_nonneg.2 (sq_nonneg ε)]

/-- `ℓ(v) = (ε⁻² + a)(ε - v)` for `v ≤ ε` (Step 4). -/
theorem ell_of_le {v : ℝ} (hv : v ≤ ε) : ell ψ ε M v = ((ε ^ 2)⁻¹ + acoef ε M) * (ε - v) := by
  rw [ell, integral_congr (g := fun _ ↦ (ε ^ 2)⁻¹ + acoef ε M) fun s hs ↦ ?_]
  · simp only [integral_const, smul_eq_mul]; ring
  · rw [uIcc_of_le hv] at hs
    exact ellIntegrand_of_le hψ hε hM hs.2

/-- **(c)**, first part: `ℓ' ≤ -ε⁻²` on `(-∞, ε]`. -/
theorem ellDeriv_le_of_le {v : ℝ} (hv : v ≤ ε) : ellDeriv ψ ε M v ≤ -(ε ^ 2)⁻¹ := by
  rw [ellDeriv, ellIntegrand_of_le hψ hε hM hv]
  linarith [acoef_pos hε hM]

/-- **(c)**, `ℓ ≥ 0` on `(-∞, ε]`. -/
theorem ell_nonneg_of_le {v : ℝ} (hv : v ≤ ε) : 0 ≤ ell ψ ε M v := by
  rw [ell_of_le hψ hε hM hv]
  have := acoef_pos hε hM
  have : 0 ≤ (ε ^ 2)⁻¹ := by positivity
  nlinarith

/-- **(c)**, `ℓ ≤ 2/ε` on `[0, ε]`. -/
theorem ell_le_of_mem {v : ℝ} (hv : v ∈ Icc 0 ε) : ell ψ ε M v ≤ 2 / ε := by
  rw [ell_of_le hψ hε hM hv.2]
  have ha := acoef_mul_eps_sq_le hε hM
  have ha0 := acoef_pos hε hM
  have h1 : ((ε ^ 2)⁻¹ + acoef ε M) * (ε - v) ≤ ((ε ^ 2)⁻¹ + acoef ε M) * ε :=
    mul_le_mul_of_nonneg_left (by linarith [hv.1]) (by positivity)
  have h2 : ((ε ^ 2)⁻¹ + acoef ε M) * ε = (1 + acoef ε M * ε ^ 2) / ε := by
    field_simp
  rw [h2] at h1
  refine h1.trans ?_
  rw [div_le_div_iff_of_pos_right hε]
  linarith

omit hε hM in
/-- **(d)**: `ℓ' ≤ -a` everywhere, in particular on `[ε, ∞)`. -/
theorem ellDeriv_le_neg_a (v : ℝ) : ellDeriv ψ ε M v ≤ -acoef ε M := by
  rw [ellDeriv]; linarith [acoef_le_ellIntegrand hψ (ε := ε) (M := M) v]

/-- `ψ((s - ε)/ρ)` integrates to at most `ρ` over `[ε, v]`. -/
theorem integral_cutoff_le {v : ℝ} (hv : ε ≤ v) :
    ∫ s in ε..v, ψ ((s - ε) / rho ε M) ≤ rho ε M := by
  have hρ := rho_pos hε hM
  have hc : Continuous fun s ↦ ψ ((s - ε) / rho ε M) :=
    hψ.continuous.comp ((continuous_id.sub continuous_const).div_const _)
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s ↦ ψ ((s - ε) / rho ε M)) MeasureTheory.volume
      a b := fun a b ↦ hc.intervalIntegrable a b
  have hle1 : ∀ a b : ℝ, a ≤ b → ∫ s in a..b, ψ ((s - ε) / rho ε M) ≤ b - a := fun a b hab ↦ by
    have := integral_mono_on hab (hint a b) (continuous_const.intervalIntegrable a b)
      (fun s _ ↦ hψ.le_one ((s - ε) / rho ε M))
    simpa using this
  rcases le_total v (ε + rho ε M) with h | h
  · exact (hle1 ε v hv).trans (by linarith)
  · rw [← integral_add_adjacent_intervals (hint ε (ε + rho ε M)) (hint (ε + rho ε M) v)]
    have h0 : ∫ s in (ε + rho ε M)..v, ψ ((s - ε) / rho ε M) = 0 := by
      rw [integral_congr (g := fun _ ↦ 0) fun s hs ↦ ?_]
      · simp
      · rw [uIcc_of_le h] at hs
        exact hψ.eq_zero _ (by rw [le_div_iff₀ hρ]; linarith [hs.1])
    rw [h0, add_zero]
    exact (hle1 _ _ (by linarith)).trans (by linarith)

/-- The bounds (A.11): `a(v - ε) ≤ -ℓ(v) ≤ ρ/ε² + a(v - ε)` for
`v ≥ ε`. -/
theorem ell_bounds_of_le {v : ℝ} (hv : ε ≤ v) :
    acoef ε M * (v - ε) ≤ -ell ψ ε M v ∧
      -ell ψ ε M v ≤ rho ε M / ε ^ 2 + acoef ε M * (v - ε) := by
  have hint := (continuous_ellIntegrand hψ (ε := ε) (M := M)).intervalIntegrable
    (μ := MeasureTheory.volume) ε v
  have hneg : -ell ψ ε M v = ∫ s in ε..v, ellIntegrand ψ ε M s := by rw [ell, integral_symm]; ring
  rw [hneg]
  constructor
  · have := integral_mono_on hv (continuous_const.intervalIntegrable ε v) hint
      (fun s _ ↦ acoef_le_ellIntegrand hψ s)
    simpa [mul_comm] using this
  · have hc : Continuous fun s ↦ ψ ((s - ε) / rho ε M) :=
      hψ.continuous.comp ((continuous_id.sub continuous_const).div_const _)
    have : ∫ s in ε..v, ellIntegrand ψ ε M s =
        (ε ^ 2)⁻¹ * (∫ s in ε..v, ψ ((s - ε) / rho ε M)) + (v - ε) * acoef ε M := by
      unfold ellIntegrand
      rw [integral_add ((hc.intervalIntegrable ε v).const_mul _)
        (continuous_const.intervalIntegrable ε v), integral_const_mul, integral_const,
        smul_eq_mul]
    rw [this]
    have h1 := integral_cutoff_le hψ hε hM hv
    have h2 : (ε ^ 2)⁻¹ * (∫ s in ε..v, ψ ((s - ε) / rho ε M)) ≤ (ε ^ 2)⁻¹ * rho ε M :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [div_eq_inv_mul]
    linarith

/-- `ℓ ≤ 0` on `[ε, ∞)`. -/
theorem ell_nonpos_of_le {v : ℝ} (hv : ε ≤ v) : ell ψ ε M v ≤ 0 := by
  have := (ell_bounds_of_le hψ hε hM hv).1
  nlinarith [acoef_pos hε hM]

/-- **(e)**: `ℓ² ≤ 2|ℓ'|` on `[0, v_max]`. -/
theorem ell_sq_le {v : ℝ} (hv : v ∈ Icc 0 (vmax ε M)) :
    ell ψ ε M v ^ 2 ≤ 2 * |ellDeriv ψ ε M v| := by
  have ha := acoef_pos hε hM
  rcases le_total v ε with h | h
  · -- on `[0, ε]`: `ℓ²/|ℓ'| = (ε⁻² + a)(ε - v)² ≤ 1 + aε² ≤ 2`
    rw [ell_of_le hψ hε hM h, ellDeriv, ellIntegrand_of_le hψ hε hM h]
    have hc : 0 < (ε ^ 2)⁻¹ + acoef ε M := by positivity
    rw [abs_neg, abs_of_pos hc]
    have h1 : (ε - v) ^ 2 ≤ ε ^ 2 := by nlinarith [hv.1]
    have h2 : ((ε ^ 2)⁻¹ + acoef ε M) * ε ^ 2 ≤ 2 := by
      have := acoef_mul_eps_sq_le hε hM
      have : (ε ^ 2)⁻¹ * ε ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
      nlinarith
    have : ((ε ^ 2)⁻¹ + acoef ε M) * (ε - v) ^ 2 ≤ 2 :=
      (mul_le_mul_of_nonneg_left h1 hc.le).trans h2
    calc (((ε ^ 2)⁻¹ + acoef ε M) * (ε - v)) ^ 2
        = ((ε ^ 2)⁻¹ + acoef ε M) * (((ε ^ 2)⁻¹ + acoef ε M) * (ε - v) ^ 2) := by ring
      _ ≤ ((ε ^ 2)⁻¹ + acoef ε M) * 2 := mul_le_mul_of_nonneg_left this hc.le
      _ = 2 * ((ε ^ 2)⁻¹ + acoef ε M) := by ring
  · -- on `[ε, v_max]`: `ℓ² ≤ 2(ρ/ε²)² + 2a²(v - ε)² ≤ (1/256 + 2a v_max²) a ≤ a/2`
    obtain ⟨hb1, hb2⟩ := ell_bounds_of_le hψ hε hM h
    have hd : acoef ε M ≤ |ellDeriv ψ ε M v| := by
      have := ellDeriv_le_neg_a hψ (ε := ε) (M := M) v
      rw [abs_of_neg (by linarith)]; linarith
    set r := rho ε M / ε ^ 2
    have hr : r * vmax ε M = 1 / 64 := rho_div_mul_vmax hε hM
    have hav := acoef_mul_vmax_sq hε hM
    have hvp := vmax_pos hε hM
    have hr0 : 0 ≤ r := by have := rho_pos hε hM; positivity
    have hw0 : 0 ≤ v - ε := by linarith
    have hw1 : v - ε ≤ vmax ε M := by linarith [hv.2]
    -- `ℓ² ≤ (r + a(v-ε))²`
    have hsq : ell ψ ε M v ^ 2 ≤ (r + acoef ε M * (v - ε)) ^ 2 := by
      have h0 : 0 ≤ -ell ψ ε M v := by nlinarith
      nlinarith
    -- `r² = a/512`
    have hr2 : r ^ 2 = acoef ε M / 512 := by
      have : r = 1 / (64 * vmax ε M) := by field_simp; linarith
      rw [this]; unfold acoef; field_simp; ring
    have hq : acoef ε M * (v - ε) ^ 2 ≤ 1 / 8 := by
      have : (v - ε) ^ 2 ≤ vmax ε M ^ 2 := pow_le_pow_left₀ hw0 hw1 2
      nlinarith
    nlinarith [sq_nonneg (r - acoef ε M * (v - ε))]

end Ell

/-! ### `φ'` and `φ` -/

section Phi

variable (hψ : IsBernsteinCutoff ψ) (hε : 0 < ε) (hM : 0 ≤ M)
include hψ hε hM

/-- `∫₀^ε ℓ = (1 + a ε²)/2`. -/
theorem integral_ell_eps : ∫ s in (0 : ℝ)..ε, ell ψ ε M s = (1 + acoef ε M * ε ^ 2) / 2 := by
  rw [integral_congr (g := fun s ↦ ((ε ^ 2)⁻¹ + acoef ε M) * (ε - s)) fun s hs ↦ ?_]
  · rw [integral_const_mul, integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id,
      integral_const, integral_id, smul_eq_mul]
    field_simp
    ring
  · rw [uIcc_of_le hε.le] at hs
    exact ell_of_le hψ hε hM hs.2

/-- `∫₀^v ℓ ≤ ∫₀^ε ℓ` for all `v` (`ℓ ≥ 0` on `[0, ε]`, `ℓ ≤ 0` on `[ε, ∞)`). -/
theorem integral_ell_le (v : ℝ) :
    ∫ s in (0 : ℝ)..v, ell ψ ε M s ≤ ∫ s in (0 : ℝ)..ε, ell ψ ε M s := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (ell ψ ε M) MeasureTheory.volume a b :=
    fun a b ↦ (continuous_ell hψ).intervalIntegrable a b
  rw [← integral_add_adjacent_intervals (hint 0 ε) (hint ε v)]
  rcases le_total ε v with h | h
  · have : 0 ≤ ∫ s in ε..v, -ell ψ ε M s := integral_nonneg h fun s hs ↦
      neg_nonneg.2 (ell_nonpos_of_le hψ hε hM hs.1)
    rw [intervalIntegral.integral_neg] at this
    linarith
  · have : 0 ≤ ∫ s in v..ε, ell ψ ε M s := integral_nonneg h fun s hs ↦
      ell_nonneg_of_le hψ hε hM hs.2
    have hs : ∫ s in ε..v, ell ψ ε M s = -∫ s in v..ε, ell ψ ε M s := integral_symm _ _
    linarith

/-- `0 ≤ ∫₀^v ℓ` for `v ∈ [0, v_max]`. -/
theorem integral_ell_nonneg {v : ℝ} (hv : v ∈ Icc 0 (vmax ε M)) :
    0 ≤ ∫ s in (0 : ℝ)..v, ell ψ ε M s := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (ell ψ ε M) MeasureTheory.volume a b :=
    fun a b ↦ (continuous_ell hψ).intervalIntegrable a b
  rcases le_total v ε with h | h
  · exact integral_nonneg hv.1 fun s hs ↦ ell_nonneg_of_le hψ hε hM (hs.2.trans h)
  · rw [← integral_add_adjacent_intervals (hint 0 ε) (hint ε v), integral_ell_eps hψ hε hM]
    -- on `[ε, v]`: `ℓ ≥ -(ρ/ε² + a v_max)`, and `(ρ/ε² + a v_max) v_max = 1/64 + 1/8`
    have hlow : ∀ s ∈ Icc ε v, -(rho ε M / ε ^ 2 + acoef ε M * vmax ε M) ≤ ell ψ ε M s := by
      intro s hs
      have := (ell_bounds_of_le hψ hε hM hs.1).2
      have : acoef ε M * (s - ε) ≤ acoef ε M * vmax ε M :=
        mul_le_mul_of_nonneg_left (by linarith [hs.2, hv.2]) (acoef_pos hε hM).le
      linarith
    have h1 := integral_mono_on h (continuous_const.intervalIntegrable ε v) (hint ε v) hlow
    rw [integral_const, smul_eq_mul] at h1
    have hr := rho_div_mul_vmax hε hM
    have hav := acoef_mul_vmax_sq hε hM
    have hw : v - ε ≤ vmax ε M := by linarith [hv.2]
    have hc0 : 0 ≤ rho ε M / ε ^ 2 + acoef ε M * vmax ε M := by
      have := rho_pos hε hM; have := acoef_pos hε hM; have := vmax_pos hε hM; positivity
    have h2 : (v - ε) * (rho ε M / ε ^ 2 + acoef ε M * vmax ε M) ≤
        vmax ε M * (rho ε M / ε ^ 2 + acoef ε M * vmax ε M) :=
      mul_le_mul_of_nonneg_right hw hc0
    have h3 : vmax ε M * (rho ε M / ε ^ 2 + acoef ε M * vmax ε M) = 1 / 64 + 1 / 8 := by
      rw [mul_add, mul_comm, hr]; nlinarith
    have := acoef_pos hε hM
    have : 0 ≤ acoef ε M * ε ^ 2 := by positivity
    nlinarith

/-- **(a)**, upper bound: `φ' ≤ e` (everywhere). -/
theorem phiDeriv_le_exp_one (v : ℝ) : phiDeriv ψ ε M v ≤ exp 1 := by
  rw [phiDeriv, exp_le_exp]
  refine (integral_ell_le hψ hε hM v).trans ?_
  rw [integral_ell_eps hψ hε hM]
  linarith [acoef_mul_eps_sq_le hε hM]

/-- `φ' ≥ 1` on `[0, v_max]` (stronger than the paper's `φ' ≥ 1/2`). -/
theorem one_le_phiDeriv {v : ℝ} (hv : v ∈ Icc 0 (vmax ε M)) : 1 ≤ phiDeriv ψ ε M v := by
  rw [phiDeriv, one_le_exp_iff]
  exact integral_ell_nonneg hψ hε hM hv

/-- **(a)**, lower bound: `φ' ≥ 1/2` on `[0, v_max]`. -/
theorem one_half_le_phiDeriv {v : ℝ} (hv : v ∈ Icc 0 (vmax ε M)) : 1 / 2 ≤ phiDeriv ψ ε M v :=
  (by norm_num : (1 : ℝ) / 2 ≤ 1).trans (one_le_phiDeriv hψ hε hM hv)

/-- **(c)**, last part: `φ' ≥ 1` on `[0, ε]`. -/
theorem one_le_phiDeriv_of_mem {v : ℝ} (hv : v ∈ Icc 0 ε) : 1 ≤ phiDeriv ψ ε M v :=
  one_le_phiDeriv hψ hε hM ⟨hv.1, hv.2.trans (eps_le_vmax hM)⟩

/-- `φ(v) ≥ v` on `[0, v_max]`. -/
theorem le_phi {v : ℝ} (hv : v ∈ Icc 0 (vmax ε M)) : v ≤ phi ψ ε M v := by
  have := integral_mono_on hv.1
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 v)
    ((continuous_phiDeriv hψ).intervalIntegrable 0 v)
    (fun s hs ↦ one_le_phiDeriv hψ hε hM ⟨hs.1, hs.2.trans hv.2⟩)
  simpa [phi] using this

/-- **(b)**: `φ(ε) ≥ ε`. -/
theorem le_phi_eps : ε ≤ phi ψ ε M ε :=
  le_phi hψ hε hM ⟨hε.le, eps_le_vmax hM⟩

/-- **(a)**, last part: `φ(v_max) ≥ 2M`. -/
theorem two_mul_le_phi_vmax : 2 * M ≤ phi ψ ε M (vmax ε M) := by
  have := le_phi hψ hε hM ⟨(vmax_pos hε hM).le, le_rfl⟩
  unfold vmax at this ⊢
  linarith

end Phi

end Bernstein

end PerronVariational

end
