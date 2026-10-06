/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Semilinear
public import PerronVariational.Semilinear.AutonomousODE
import PerronVariational.Semilinear.Profiles

/-!
# The supersolution profile (Lemma A.3)

Lemma A.3 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.
For `θ̂ > 1` set `θ̃ = (1 + θ̂)/2`, `σ = θ̂/θ̃ - 1 > 0`, let `κ ∈ (0, 1)` solve
`2𝓑(κ) = (θ̃ - 1)/θ̃` ((A.3)) and `P(z) = 2θ̃(𝓑(z) - 𝓑(κ))`.

**Choice of the reparametrization `η` (deviation from the paper).**
The paper assumes an abstract smooth `η` with (A.4)
(`η(p) = p²` near `0`, `η(p) = p` near `1`, `0 < η(p) ≤ p`, `0 ≤ η' ≤ 1 + σ`), whose existence it
asserts without construction. Here we use the explicit
rational function `η(p) = (1 + σ) p² / (p + σ)`, which has all the properties the proof uses:
`η(0) = 0`, `η(1) = 1`, `0 < η(p) ≤ p` on `(0, 1]`, `0 ≤ η' ≤ 1 + σ` on `[0, ∞)`,
`η(p) ≍ p²` and `η'(p) ≲ p` near `0`, and `η` is smooth on `(-σ, ∞)`. Then
`g = √(η ∘ P) = P · √((1 + σ)/(P + σ))` (`superField`) is smooth on `{P > -σ} ⊇ [κ, ∞)`.
(The paper's `η(p) = p` near `1` is only used to make `g` smooth where `P` is near `1`, which the
explicit formula gives directly.)

**Construction of `Ψ` (avoiding ODE theory).** The paper takes the maximal solution of
`Ψ' = g(Ψ)`, `Ψ(1) = 1`. We substitute `Ψ = κ + e^T`: `T' = F(T)` with the globally positive,
bounded, smooth field `F(t) = g(κ + eᵗ) e^{-t}` (`superLogField`), which is solved by inverting
the time map (`odeSol`). This yields `Ψ ∈ C^∞(ℝ)` with values in `(κ, ∞)`.
-/

open Set Filter Topology
open scoped ContDiff

@[expose] public section

-- uniform hypothesis lists `(hβ) (hθh)` for all profile lemmas
set_option linter.unusedSectionVars false

namespace PerronVariational

/-- `θ̃ = (1 + θ̂)/2`. -/
noncomputable def superTheta (θh : ℝ) : ℝ := (1 + θh) / 2

/-- `σ = θ̂/θ̃ - 1`. -/
noncomputable def superSigma (θh : ℝ) : ℝ := θh / superTheta θh - 1

open Classical in
/-- The level `κ = κ_{θ̂} ∈ (0, 1)` of (A.3): `2𝓑(κ) = (θ̃ - 1)/θ̃` (a choice; it
is unique since `𝓑` is strictly increasing on `[0, 1]`). -/
noncomputable def superKappa (β : ℝ → ℝ) (θh : ℝ) : ℝ :=
  if h : ∃ κ ∈ Ioo (0 : ℝ) 1, 2 * bigBEps β 1 κ = (superTheta θh - 1) / superTheta θh then
    h.choose else 0

/-- `P(z) = 2θ̃(𝓑(z) - 𝓑(κ))`. -/
noncomputable def superP (β : ℝ → ℝ) (θh z : ℝ) : ℝ :=
  2 * superTheta θh * (bigBEps β 1 z - bigBEps β 1 (superKappa β θh))

/-- The vector field `g = √(η ∘ P) = P √((1 + σ)/(P + σ))` of the supersolution ODE,
with the explicit reparametrization `η(p) = (1 + σ)p²/(p + σ)`. -/
noncomputable def superField (β : ℝ → ℝ) (θh z : ℝ) : ℝ :=
  superP β θh z * √((1 + superSigma θh) / (superP β θh z + superSigma θh))

/-- `η'(p) = (1 + σ) p (p + 2σ)/(p + σ)²`, so that `Ψ'' = θ̃ β(Ψ) η'(P(Ψ))`. -/
noncomputable def superEtaDeriv (σ p : ℝ) : ℝ := (1 + σ) * p * (p + 2 * σ) / (p + σ) ^ 2

/-- The field `F(t) = g(κ + eᵗ) e^{-t}` of the ODE for `T = log(Ψ - κ)`. -/
noncomputable def superLogField (β : ℝ → ℝ) (θh t : ℝ) : ℝ :=
  superField β θh (superKappa β θh + Real.exp t) * Real.exp (-t)

/-- **Lemma A.3**: the supersolution profile
`Ψ_{1,θ̂}(s) = κ + exp(T(s - 1))`, where `T' = F(T)`, `T(0) = log(1 - κ)`; equivalently
`Ψ' = g(Ψ)`, `Ψ(1) = 1`. -/
noncomputable def profileSuper (β : ℝ → ℝ) (θh s : ℝ) : ℝ :=
  superKappa β θh +
    Real.exp (odeSol (superLogField β θh) (Real.log (1 - superKappa β θh)) (s - 1))

section Constants

variable {θh : ℝ} (hθh : 1 < θh)
include hθh

theorem one_lt_superTheta : 1 < superTheta θh := by unfold superTheta; linarith

theorem superTheta_lt : superTheta θh < θh := by unfold superTheta; linarith

theorem superSigma_pos : 0 < superSigma θh := by
  have h := one_lt_superTheta hθh
  rw [superSigma, sub_pos, one_lt_div (by linarith)]
  exact superTheta_lt hθh

theorem superTheta_mul_one_add_superSigma : superTheta θh * (1 + superSigma θh) = θh := by
  have h := one_lt_superTheta hθh
  rw [superSigma]; field_simp; ring

end Constants

section SuperP

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β) {θh : ℝ} (hθh : 1 < θh)
include hβ hθh

theorem superKappa_spec : superKappa β θh ∈ Ioo (0 : ℝ) 1 ∧
    2 * bigBEps β 1 (superKappa β θh) = (superTheta θh - 1) / superTheta θh := by
  have hθt := one_lt_superTheta hθh
  have hex : ∃ κ ∈ Ioo (0 : ℝ) 1, 2 * bigBEps β 1 κ = (superTheta θh - 1) / superTheta θh := by
    have hmem : (superTheta θh - 1) / superTheta θh ∈
        Ioo (2 * bigBEps β 1 0) (2 * bigBEps β 1 1) := by
      rw [hβ.bigB_of_nonpos le_rfl, hβ.bigB_one]
      constructor
      · norm_num; exact div_pos (by linarith) (by linarith)
      · norm_num; rw [div_lt_one (by linarith)]; linarith
    obtain ⟨κ, hκ, hκ'⟩ := intermediate_value_Ioo zero_le_one
      ((continuous_const.mul hβ.continuous_bigB).continuousOn) hmem
    exact ⟨κ, hκ, hκ'⟩
  rw [superKappa, dite_eq_left hex]
  exact hex.choose_spec

theorem superKappa_pos : 0 < superKappa β θh := (superKappa_spec hβ hθh).1.1

theorem superKappa_lt_one : superKappa β θh < 1 := (superKappa_spec hβ hθh).1.2

theorem hasDerivAt_superP (z : ℝ) :
    HasDerivAt (superP β θh) (2 * superTheta θh * β z) z := by
  have h := ((hβ.hasDerivAt_bigB z).sub_const (bigBEps β 1 (superKappa β θh))).const_mul
    (2 * superTheta θh)
  exact h

theorem continuous_superP : Continuous (superP β θh) :=
  continuous_iff_continuousAt.2 fun z ↦ (hasDerivAt_superP hβ hθh z).continuousAt

theorem contDiff_superP : ContDiff ℝ ∞ (superP β θh) :=
  contDiff_const.mul (hβ.contDiff_bigB.sub contDiff_const)

theorem superP_monotone : Monotone (superP β θh) :=
  monotone_of_hasDerivAt_nonneg' (hasDerivAt_superP hβ hθh) fun z ↦
    mul_nonneg (by linarith [one_lt_superTheta hθh]) (hβ.nonneg z)

theorem superP_kappa : superP β θh (superKappa β θh) = 0 := by simp [superP]

theorem superP_of_one_le {z : ℝ} (hz : 1 ≤ z) : superP β θh z = 1 := by
  have hθt := one_lt_superTheta hθh
  have hκ := (superKappa_spec hβ hθh).2
  rw [superP, hβ.bigB_of_one_le hz]
  have : bigBEps β 1 (superKappa β θh) = (superTheta θh - 1) / superTheta θh / 2 := by
    linarith
  rw [this]; field_simp; ring

theorem superP_le_one (z : ℝ) : superP β θh z ≤ 1 := by
  rw [← superP_of_one_le hβ hθh (le_max_right z 1)]
  exact superP_monotone hβ hθh (le_max_left z 1)

theorem superP_lt_one {z : ℝ} (hz : z < 1) : superP β θh z < 1 := by
  have hθt := one_lt_superTheta hθh
  rw [← superP_of_one_le hβ hθh le_rfl, superP, superP]
  have := hβ.bigB_lt_half hz
  rw [hβ.bigB_one]
  nlinarith

theorem superP_pos {z : ℝ} (hz : superKappa β θh < z) : 0 < superP β θh z := by
  have hθt := one_lt_superTheta hθh
  have hκ0 := superKappa_pos hβ hθh
  have hκ1 := superKappa_lt_one hβ hθh
  have hlt : bigBEps β 1 (superKappa β θh) < bigBEps β 1 z := by
    rcases le_total z 1 with h1 | h1
    · exact hβ.bigB_strictMonoOn ⟨hκ0.le, hκ1.le⟩ ⟨(hκ0.trans hz).le, h1⟩ hz
    · rw [hβ.bigB_of_one_le h1]; exact hβ.bigB_lt_half hκ1
  rw [superP]
  exact mul_pos (by linarith) (sub_pos.2 hlt)

theorem superP_nonneg {z : ℝ} (hz : superKappa β θh ≤ z) : 0 ≤ superP β θh z := by
  rw [← superP_kappa hβ hθh (β := β)]; exact superP_monotone hβ hθh hz

/-- Upper linear bound `P(z) ≤ 2θ̃ M (z - κ)` for `z ≥ κ` (proof of Lemma A.3). -/
theorem superP_le {M : ℝ} (hM : ∀ s, β s ≤ M) {z : ℝ} (hz : superKappa β θh ≤ z) :
    superP β θh z ≤ 2 * superTheta θh * M * (z - superKappa β θh) := by
  have hθt := one_lt_superTheta hθh
  have hmono : Monotone fun z ↦ 2 * superTheta θh * M * z - superP β θh z :=
    monotone_of_hasDerivAt_nonneg' (fun z ↦ ((hasDerivAt_id z).const_mul
      (2 * superTheta θh * M)).sub (hasDerivAt_superP hβ hθh z)) fun z ↦ by
        have := hM z
        simp only [mul_one, sub_nonneg]
        exact mul_le_mul_of_nonneg_left this (by linarith)
  have := hmono hz
  simp only [superP_kappa hβ hθh] at this
  linarith

/-- Lower linear bound `P(z) ≥ θ̃ b (z - κ)` on `[κ, 1]`, where `b ≤ β` on `[κ, (1 + κ)/2]`
(proof of Lemma A.3, extended from `[κ, z₀]` to `[κ, 1]`). -/
theorem le_superP {b : ℝ} (hb : 0 ≤ b)
    (hβb : ∀ s ∈ Icc (superKappa β θh) ((1 + superKappa β θh) / 2), b ≤ β s) {z : ℝ}
    (hz : z ∈ Icc (superKappa β θh) 1) :
    superTheta θh * b * (z - superKappa β θh) ≤ superP β θh z := by
  have hθt := one_lt_superTheta hθh
  have hκ1 := superKappa_lt_one hβ hθh
  set κ := superKappa β θh with hκ
  set z₀ := (1 + κ) / 2 with hz₀
  have hmono : MonotoneOn (fun z ↦ superP β θh z - 2 * superTheta θh * b * z) (Icc κ z₀) := by
    refine monotoneOn_of_hasDerivAt_nonneg' (convex_Icc κ z₀) (fun z ↦ (hasDerivAt_superP hβ hθh
      z).sub ((hasDerivAt_id z).const_mul (2 * superTheta θh * b))) fun z hz' ↦ ?_
    rw [interior_Icc] at hz'
    have := hβb z ⟨hz'.1.le, hz'.2.le⟩
    simp only [mul_one, sub_nonneg]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have hlow : ∀ w ∈ Icc κ z₀, 2 * superTheta θh * b * (w - κ) ≤ superP β θh w := by
    intro w hw
    have := hmono ⟨le_rfl, by linarith [hw.1, hw.2]⟩ hw hw.1
    have hk : superP β θh κ = 0 := superP_kappa hβ hθh
    simp only at this
    linarith
  have hθb : 0 ≤ superTheta θh * b := mul_nonneg (by linarith) hb
  rcases le_total z z₀ with h | h
  · have := hlow z ⟨hz.1, h⟩
    nlinarith [hz.1]
  · have h1 := hlow z₀ ⟨by linarith, le_rfl⟩
    have h2 := superP_monotone hβ hθh h
    nlinarith [hz.2]

end SuperP

section SuperField

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β) {θh : ℝ} (hθh : 1 < θh)
include hβ hθh

theorem superP_add_superSigma_pos {z : ℝ} (hz : superKappa β θh ≤ z) :
    0 < superP β θh z + superSigma θh :=
  add_pos_of_nonneg_of_pos (superP_nonneg hβ hθh hz) (superSigma_pos hθh)

theorem superField_sq {z : ℝ} (hz : superKappa β θh ≤ z) :
    superField β θh z ^ 2 =
      (1 + superSigma θh) * superP β θh z ^ 2 / (superP β θh z + superSigma θh) := by
  have hσ := superSigma_pos hθh
  have hP := superP_add_superSigma_pos hβ hθh hz
  rw [superField, mul_pow, Real.sq_sqrt (div_nonneg (by linarith) hP.le)]
  ring

theorem superField_pos {z : ℝ} (hz : superKappa β θh < z) : 0 < superField β θh z := by
  have hσ := superSigma_pos hθh
  exact mul_pos (superP_pos hβ hθh hz) (Real.sqrt_pos.2 (div_pos (by linarith)
    (superP_add_superSigma_pos hβ hθh hz.le)))

theorem superField_nonneg {z : ℝ} (hz : superKappa β θh ≤ z) : 0 ≤ superField β θh z :=
  mul_nonneg (superP_nonneg hβ hθh hz) (Real.sqrt_nonneg _)

theorem superP_le_superField {z : ℝ} (hz : superKappa β θh ≤ z) :
    superP β θh z ≤ superField β θh z := by
  have hσ := superSigma_pos hθh
  have hP1 := superP_le_one hβ hθh z
  have hP := superP_add_superSigma_pos hβ hθh hz
  have h1 : 1 ≤ √((1 + superSigma θh) / (superP β θh z + superSigma θh)) :=
    Real.one_le_sqrt.2 ((one_le_div hP).2 (by linarith))
  rw [superField]
  exact le_mul_of_one_le_right (superP_nonneg hβ hθh hz) h1

theorem superField_le_mul {z : ℝ} (hz : superKappa β θh ≤ z) :
    superField β θh z ≤ superP β θh z * √((1 + superSigma θh) / superSigma θh) := by
  have hσ := superSigma_pos hθh
  rw [superField]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (superP_nonneg hβ hθh hz)
  exact div_le_div_of_nonneg_left (by linarith) hσ (by linarith [superP_nonneg hβ hθh hz])

theorem superField_le_superP {z : ℝ} (hz : superKappa β θh ≤ z) :
    superField β θh z ^ 2 ≤ superP β θh z := by
  have hσ := superSigma_pos hθh
  have hP1 := superP_le_one hβ hθh z
  have hP0 := superP_nonneg hβ hθh hz
  have hP := superP_add_superSigma_pos hβ hθh hz
  rw [superField_sq hβ hθh hz, div_le_iff₀ hP]
  linarith [mul_nonneg (mul_nonneg hσ.le hP0) (sub_nonneg.2 hP1)]

theorem superField_le_one {z : ℝ} (hz : superKappa β θh ≤ z) : superField β θh z ≤ 1 := by
  have h := (superField_le_superP hβ hθh hz).trans (superP_le_one hβ hθh z)
  nlinarith [superField_nonneg hβ hθh hz]

theorem superField_lt_one {z : ℝ} (hz : superKappa β θh ≤ z) (hz1 : z < 1) :
    superField β θh z < 1 := by
  have h := (superField_le_superP hβ hθh hz).trans_lt (superP_lt_one hβ hθh hz1)
  nlinarith [superField_nonneg hβ hθh hz]

theorem superField_of_one_le {z : ℝ} (hz : 1 ≤ z) : superField β θh z = 1 := by
  have hσ := superSigma_pos hθh
  rw [superField, superP_of_one_le hβ hθh hz, add_comm 1, div_self (by linarith),
    Real.sqrt_one, mul_one]

/-- The derivative of `g` where `g > 0`: `g' = θ̃ β η'(P) / g`, i.e. `(g²)' = 2θ̃ β η'(P)`. -/
theorem hasDerivAt_superField {z : ℝ} (hz : superKappa β θh < z) :
    HasDerivAt (superField β θh)
      (superTheta θh * β z * superEtaDeriv (superSigma θh) (superP β θh z) /
        superField β θh z) z := by
  have hσ := superSigma_pos hθh
  have hPσ := superP_add_superSigma_pos hβ hθh hz.le
  have hP0 := superP_pos hβ hθh hz
  have hu : HasDerivAt (fun w ↦ (1 + superSigma θh) / (superP β θh w + superSigma θh))
      ((0 * (superP β θh z + superSigma θh) - (1 + superSigma θh) *
        (2 * superTheta θh * β z)) / (superP β θh z + superSigma θh) ^ 2) z :=
    HasDerivAt.fun_div (hasDerivAt_const z (1 + superSigma θh))
      ((hasDerivAt_superP hβ hθh z).add_const (superSigma θh)) hPσ.ne'
  have hupos : 0 < (1 + superSigma θh) / (superP β θh z + superSigma θh) :=
    div_pos (by linarith) hPσ
  have hr := hu.sqrt hupos.ne'
  have h := (hasDerivAt_superP hβ hθh z).mul hr
  convert h using 1
  · rfl
  have hr0 : 0 < √((1 + superSigma θh) / (superP β θh z + superSigma θh)) :=
    Real.sqrt_pos.2 hupos
  have hr2 := Real.sq_sqrt hupos.le
  set r := √((1 + superSigma θh) / (superP β θh z + superSigma θh)) with hr_def
  set P := superP β θh z with hP_def
  set σ := superSigma θh with hσ_def
  rw [superField, ← hP_def, ← hr_def, superEtaDeriv]
  field_simp
  rw [hr2]
  field_simp
  ring

end SuperField

theorem superEtaDeriv_nonneg {σ p : ℝ} (hσ : 0 < σ) (hp : 0 ≤ p) : 0 ≤ superEtaDeriv σ p := by
  unfold superEtaDeriv; positivity

theorem superEtaDeriv_le {σ p : ℝ} (hσ : 0 < σ) (hp : 0 ≤ p) : superEtaDeriv σ p ≤ 1 + σ := by
  unfold superEtaDeriv
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg σ]

theorem superEtaDeriv_le_mul {σ p : ℝ} (hσ : 0 < σ) (hp : 0 ≤ p) :
    superEtaDeriv σ p ≤ 2 * (1 + σ) / σ * p := by
  unfold superEtaDeriv
  rw [div_le_iff₀ (by positivity), div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hσ]
  have h1 : 0 ≤ (1 + σ) * p := by positivity
  linarith [mul_nonneg h1 (sq_nonneg p), mul_nonneg h1 (mul_nonneg hp hσ.le),
    mul_nonneg h1 (sq_nonneg σ)]

section ProfileSuper

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β) {θh : ℝ} (hθh : 1 < θh)
include hβ hθh

theorem kappa_lt_kappa_add_exp (t : ℝ) : superKappa β θh < superKappa β θh + Real.exp t := by
  linarith [Real.exp_pos t]

theorem superLogField_pos (t : ℝ) : 0 < superLogField β θh t :=
  mul_pos (superField_pos hβ hθh (kappa_lt_kappa_add_exp hβ hθh t)) (Real.exp_pos _)

theorem contDiff_superLogField : ContDiff ℝ ∞ (superLogField β θh) := by
  have hσ := superSigma_pos hθh
  have hPc : ContDiff ℝ ∞ fun t ↦ superP β θh (superKappa β θh + Real.exp t) :=
    (contDiff_superP hβ hθh).comp (contDiff_const.add Real.contDiff_exp)
  have hden : ∀ t, superP β θh (superKappa β θh + Real.exp t) + superSigma θh ≠ 0 := fun t ↦
    (superP_add_superSigma_pos hβ hθh (kappa_lt_kappa_add_exp hβ hθh t).le).ne'
  have hq : ContDiff ℝ ∞ fun t ↦
      (1 + superSigma θh) / (superP β θh (superKappa β θh + Real.exp t) + superSigma θh) :=
    contDiff_const.div (hPc.add contDiff_const) hden
  have hq0 : ∀ t, (1 + superSigma θh) /
      (superP β θh (superKappa β θh + Real.exp t) + superSigma θh) ≠ 0 := fun t ↦
    (div_pos (by linarith) (lt_of_le_of_ne (by
      linarith [superP_add_superSigma_pos hβ hθh (kappa_lt_kappa_add_exp hβ hθh t).le])
      (hden t).symm)).ne'
  exact (hPc.mul (hq.sqrt hq0)).mul (Real.contDiff_exp.comp contDiff_neg)

theorem continuous_superLogField : Continuous (superLogField β θh) :=
  (contDiff_superLogField hβ hθh).continuous

/-- The field `F` is bounded: `F ≤ 2θ̃ M √((1 + σ)/σ)`. -/
theorem superLogField_le {M : ℝ} (hM : ∀ s, β s ≤ M) (t : ℝ) :
    superLogField β θh t ≤
      2 * superTheta θh * M * √((1 + superSigma θh) / superSigma θh) := by
  have hz := (kappa_lt_kappa_add_exp hβ hθh t).le
  have h1 := superField_le_mul hβ hθh hz
  have h2 := superP_le hβ hθh hM hz
  have hR := Real.sqrt_nonneg ((1 + superSigma θh) / superSigma θh)
  have h3 : superField β θh (superKappa β θh + Real.exp t) ≤
      2 * superTheta θh * M * Real.exp t * √((1 + superSigma θh) / superSigma θh) := by
    rw [add_sub_cancel_left] at h2
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hR)
  rw [superLogField]
  calc _ ≤ 2 * superTheta θh * M * Real.exp t * √((1 + superSigma θh) / superSigma θh) *
        Real.exp (-t) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_neg]; field_simp

/-- The ODE for `T = log(Ψ - κ)`. -/
theorem superLogSol_hasDerivAt (s : ℝ) :
    HasDerivAt (odeSol (superLogField β θh) (Real.log (1 - superKappa β θh)))
      (superLogField β θh (odeSol (superLogField β θh)
        (Real.log (1 - superKappa β θh)) s)) s := by
  obtain ⟨M, -, hM⟩ := hβ.exists_le
  exact odeSol_hasDerivAt (continuous_superLogField hβ hθh) (superLogField_pos hβ hθh)
    (superLogField_le hβ hθh hM) s

theorem superLogSol_strictMono :
    StrictMono (odeSol (superLogField β θh) (Real.log (1 - superKappa β θh))) := by
  obtain ⟨M, -, hM⟩ := hβ.exists_le
  exact odeSol_strictMono (continuous_superLogField hβ hθh) (superLogField_pos hβ hθh)
    (superLogField_le hβ hθh hM)

theorem profileSuper_hasDerivAt (s : ℝ) :
    HasDerivAt (profileSuper β θh) (superField β θh (profileSuper β θh s)) s := by
  have h := (((superLogSol_hasDerivAt hβ hθh (s - 1)).comp s
    ((hasDerivAt_id s).sub_const 1)).exp).const_add (superKappa β θh)
  convert h using 1
  · rfl
  simp only [profileSuper, superLogField, Function.comp, id, mul_one, Real.exp_neg]
  field_simp

theorem profileSuper_deriv :
    deriv (profileSuper β θh) = fun s ↦ superField β θh (profileSuper β θh s) :=
  funext fun s ↦ (profileSuper_hasDerivAt hβ hθh s).deriv

theorem kappa_lt_profileSuper (s : ℝ) : superKappa β θh < profileSuper β θh s :=
  kappa_lt_kappa_add_exp hβ hθh _

theorem profileSuper_one : profileSuper β θh 1 = 1 := by
  obtain ⟨M, -, hM⟩ := hβ.exists_le
  have hκ1 := superKappa_lt_one hβ hθh
  rw [profileSuper, sub_self, odeSol_zero (continuous_superLogField hβ hθh)
    (superLogField_pos hβ hθh), Real.exp_log (by linarith)]
  ring

theorem profileSuper_strictMono : StrictMono (profileSuper β θh) := fun s t hst ↦ by
  simp only [profileSuper, add_lt_add_iff_left, Real.exp_lt_exp]
  exact superLogSol_strictMono hβ hθh (by linarith)

/-- `Ψ_{1,θ̂} ∈ C^∞(ℝ)`. -/
theorem profileSuper_contDiff : ContDiff ℝ ∞ (profileSuper β θh) :=
  contDiff_const.add (Real.contDiff_exp.comp ((contDiff_infty_of_hasDerivAt_comp
    (superLogSol_hasDerivAt hβ hθh) (contDiff_superLogField hβ hθh)).comp
    (contDiff_id.sub contDiff_const)))

theorem profileSuper_continuous : Continuous (profileSuper β θh) :=
  (profileSuper_contDiff hβ hθh).continuous

theorem profileSuper_hasDerivAt_deriv (s : ℝ) :
    HasDerivAt (deriv (profileSuper β θh))
      (superTheta θh * β (profileSuper β θh s) *
        superEtaDeriv (superSigma θh) (superP β θh (profileSuper β θh s))) s := by
  rw [profileSuper_deriv hβ hθh]
  have hg := superField_pos hβ hθh (kappa_lt_profileSuper hβ hθh s)
  have h := (hasDerivAt_superField hβ hθh (kappa_lt_profileSuper hβ hθh s)).comp s
    (profileSuper_hasDerivAt hβ hθh s)
  convert h using 1
  · rfl
  field_simp

theorem profileSuper_deriv_deriv (s : ℝ) :
    deriv (deriv (profileSuper β θh)) s =
      superTheta θh * β (profileSuper β θh s) *
        superEtaDeriv (superSigma θh) (superP β θh (profileSuper β θh s)) :=
  (profileSuper_hasDerivAt_deriv hβ hθh s).deriv

/-- **Lemma A.3(i)**: `0 ≤ Ψ'' ≤ θ̂ β(Ψ)`. -/
theorem profileSuper_deriv_deriv_mem (s : ℝ) :
    0 ≤ deriv (deriv (profileSuper β θh)) s ∧
      deriv (deriv (profileSuper β θh)) s ≤ θh * β (profileSuper β θh s) := by
  have hσ := superSigma_pos hθh
  have hθt := one_lt_superTheta hθh
  have hP := superP_nonneg hβ hθh (kappa_lt_profileSuper hβ hθh s).le
  have hb := hβ.nonneg (profileSuper β θh s)
  rw [profileSuper_deriv_deriv hβ hθh]
  constructor
  · exact mul_nonneg (mul_nonneg (by linarith) hb) (superEtaDeriv_nonneg hσ hP)
  · have := superEtaDeriv_le hσ hP
    have h2 : 0 ≤ superTheta θh * β (profileSuper β θh s) := mul_nonneg (by linarith) hb
    calc _ ≤ superTheta θh * β (profileSuper β θh s) * (1 + superSigma θh) :=
          mul_le_mul_of_nonneg_left this h2
      _ = superTheta θh * (1 + superSigma θh) * β (profileSuper β θh s) := by ring
      _ = _ := by rw [superTheta_mul_one_add_superSigma hθh]

/-- **Lemma A.3(ii)**: `0 < Ψ' ≤ 1`. -/
theorem profileSuper_deriv_mem (s : ℝ) :
    0 < deriv (profileSuper β θh) s ∧ deriv (profileSuper β θh) s ≤ 1 := by
  rw [profileSuper_deriv hβ hθh]
  exact ⟨superField_pos hβ hθh (kappa_lt_profileSuper hβ hθh s),
    superField_le_one hβ hθh (kappa_lt_profileSuper hβ hθh s).le⟩

/-- **Lemma A.3(ii)**: `Ψ(s) = s` for `s ≥ 1`. -/
theorem profileSuper_of_one_le {s : ℝ} (hs : 1 ≤ s) : profileSuper β θh s = s := by
  rcases hs.eq_or_lt with rfl | hs
  · exact profileSuper_one hβ hθh
  have hd : ∀ t, HasDerivAt (fun t ↦ profileSuper β θh t - t)
      (superField β θh (profileSuper β θh t) - 1) t := fun t ↦
    (profileSuper_hasDerivAt hβ hθh t).sub (hasDerivAt_id t)
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun t ↦ profileSuper β θh t - t)
    (fun t ↦ superField β θh (profileSuper β θh t) - 1) hs
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) fun t _ ↦ hd t
  have hc1 : 1 ≤ profileSuper β θh c := by
    rw [← profileSuper_one hβ hθh]; exact (profileSuper_strictMono hβ hθh).monotone hc.1.le
  rw [superField_of_one_le hβ hθh hc1, sub_self, eq_comm, div_eq_zero_iff,
    profileSuper_one hβ hθh] at hc'
  rcases hc' with h | h
  · linarith
  · linarith

/-- **Lemma A.3(iii)**: `Ψ(s) < 1` for `s < 1`. -/
theorem profileSuper_lt_one {s : ℝ} (hs : s < 1) : profileSuper β θh s < 1 := by
  rw [← profileSuper_one hβ hθh]; exact profileSuper_strictMono hβ hθh hs

/-- **Lemma A.3(iii)**: `s < Ψ(s)` for `s < 1`. -/
theorem lt_profileSuper {s : ℝ} (hs : s < 1) : s < profileSuper β θh s := by
  have hmono : StrictMonoOn (fun t ↦ t - profileSuper β θh t) (Iic 1) := by
    have hd : ∀ t, HasDerivAt (fun t ↦ t - profileSuper β θh t)
        (1 - superField β θh (profileSuper β θh t)) t := fun t ↦
      (hasDerivAt_id t).sub (profileSuper_hasDerivAt hβ hθh t)
    refine strictMonoOn_of_deriv_pos (convex_Iic 1)
      (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) fun t ht ↦ ?_
    rw [interior_Iic] at ht
    rw [(hd t).deriv, sub_pos]
    exact superField_lt_one hβ hθh (kappa_lt_profileSuper hβ hθh t).le
      (profileSuper_lt_one hβ hθh ht)
  have := hmono (mem_Iic.2 hs.le) (mem_Iic.2 le_rfl) hs
  simp only [profileSuper_one hβ hθh, sub_self] at this
  linarith

/-- **Lemma A.3(iii)**: `s₊ ≤ Ψ(s)` for all `s` (from `Ψ(s) ≥ s` and `Ψ > κ > 0`). -/
theorem max_le_profileSuper (s : ℝ) : max s 0 ≤ profileSuper β θh s := by
  refine max_le ?_ ((superKappa_pos hβ hθh).trans (kappa_lt_profileSuper hβ hθh s)).le
  rcases lt_or_ge s 1 with hs | hs
  · exact (lt_profileSuper hβ hθh hs).le
  · rw [profileSuper_of_one_le hβ hθh hs]

/-- **Lemma A.3(iii)**: `sup_ℝ |Ψ - s₊| ≤ 1`. -/
theorem abs_profileSuper_sub_le (s : ℝ) : |profileSuper β θh s - max s 0| ≤ 1 := by
  rcases le_total 1 s with hs | hs
  · rw [profileSuper_of_one_le hβ hθh hs, max_eq_left (by linarith), sub_self, abs_zero]
    exact zero_le_one
  · have h1 : profileSuper β θh s ≤ 1 := by
      rw [← profileSuper_one hβ hθh]; exact (profileSuper_strictMono hβ hθh).monotone hs
    have h2 := max_le_profileSuper hβ hθh s
    have h3 : 0 ≤ max s 0 := le_max_right _ _
    rw [abs_le]; constructor <;> linarith

/-- The key tail estimate: `Ψ(s) - κ ≤ e^{cs}` for `s ≤ 1`, with `c = θ̃ b > 0`. -/
theorem exists_profileSuper_sub_kappa_le :
    ∃ c : ℝ, 0 < c ∧ ∀ s ≤ 1, profileSuper β θh s - superKappa β θh ≤ Real.exp (c * s) := by
  have hθt := one_lt_superTheta hθh
  have hκ0 := superKappa_pos hβ hθh
  have hκ1 := superKappa_lt_one hβ hθh
  obtain ⟨b, hb, hβb⟩ := hβ.exists_pos_le hκ0 (show (1 + superKappa β θh) / 2 < 1 by linarith)
  set κ := superKappa β θh with hκ
  set a := Real.log (1 - κ) with ha
  set T := odeSol (superLogField β θh) a with hT
  set c := superTheta θh * b with hc
  have hc0 : 0 < c := mul_pos (by linarith) hb
  -- `F ≥ c` on `(-∞, a]`
  have hF : ∀ t ≤ a, c ≤ superLogField β θh t := by
    intro t ht
    have het : Real.exp t ≤ 1 - κ := by
      rw [← Real.exp_log (show 0 < 1 - κ by linarith)]; exact Real.exp_le_exp.2 ht
    have hz : κ + Real.exp t ∈ Icc κ 1 := ⟨by linarith [Real.exp_pos t], by linarith⟩
    have h1 := le_superP hβ hθh hb.le hβb hz
    have h2 := superP_le_superField hβ hθh hz.1
    rw [add_sub_cancel_left] at h1
    rw [superLogField]
    calc c = c * Real.exp t * Real.exp (-t) := by rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
  have hT0 : T 0 = a := by
    obtain ⟨M, -, hM⟩ := hβ.exists_le
    exact odeSol_zero (continuous_superLogField hβ hθh) (superLogField_pos hβ hθh)
  -- `T(x) ≤ a + c x` for `x ≤ 0`
  have hTle : ∀ x ≤ 0, T x ≤ a + c * x := by
    have hmono : MonotoneOn (fun x ↦ T x - c * x) (Iic 0) := by
      refine monotoneOn_of_hasDerivAt_nonneg' (convex_Iic 0)
        (fun x ↦ (superLogSol_hasDerivAt hβ hθh x).sub ((hasDerivAt_id x).const_mul c))
        fun x hx ↦ ?_
      rw [interior_Iic] at hx
      simp only [mul_one, sub_nonneg]
      refine hF _ ?_
      rw [← hT0]; exact (superLogSol_strictMono hβ hθh).monotone hx.le
    intro x hx
    have := hmono (mem_Iic.2 hx) (mem_Iic.2 le_rfl) hx
    simp only [hT0, mul_zero, sub_zero] at this
    linarith
  refine ⟨c, hc0, fun s hs ↦ ?_⟩
  have h1 := hTle (s - 1) (by linarith)
  have h2 : profileSuper β θh s - κ = Real.exp (T (s - 1)) := by
    simp [profileSuper, hκ, hT, ha]
  rw [h2]
  calc Real.exp (T (s - 1)) ≤ Real.exp (a + c * (s - 1)) := Real.exp_le_exp.2 h1
    _ = (1 - κ) * Real.exp (c * (s - 1)) := by
        rw [Real.exp_add, ha, Real.exp_log (by linarith)]
    _ ≤ 1 * Real.exp (c * s) := by
        refine mul_le_mul (by linarith) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
          zero_le_one
    _ = _ := one_mul _

/-- **Lemma A.3(iv)**: exponential tails
`max(Ψ - κ, Ψ', Ψ'') ≤ C e^{cs}` for `s ≤ 0`, with `C ≥ 1 ≥ c > 0` depending only on `θ̂`, `β`. -/
theorem profileSuper_tail : ∃ C c : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧ ∀ s ≤ 0,
    profileSuper β θh s - superKappa β θh ≤ C * Real.exp (c * s) ∧
    deriv (profileSuper β θh) s ≤ C * Real.exp (c * s) ∧
    deriv (deriv (profileSuper β θh)) s ≤ C * Real.exp (c * s) := by
  obtain ⟨c, hc0, hc⟩ := exists_profileSuper_sub_kappa_le hβ hθh
  obtain ⟨M, hM0, hM⟩ := hβ.exists_le
  have hσ := superSigma_pos hθh
  have hθt := one_lt_superTheta hθh
  set κ := superKappa β θh
  set R := √((1 + superSigma θh) / superSigma θh)
  set K₁ := 2 * superTheta θh * M * R
  set K₂ := superTheta θh * M * (2 * (1 + superSigma θh) / superSigma θh) *
    (2 * superTheta θh * M)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  refine ⟨max 1 (max K₁ K₂), min c 1, lt_min hc0 one_pos, min_le_right _ _, le_max_left _ _,
    fun s hs ↦ ?_⟩
  have hexp : Real.exp (c * s) ≤ Real.exp (min c 1 * s) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left c 1])
  have hE := hc s (by linarith)
  have hE0 : 0 ≤ profileSuper β θh s - κ := (sub_pos.2 (kappa_lt_profileSuper hβ hθh s)).le
  have hz := (kappa_lt_profileSuper hβ hθh s).le
  have hPle := superP_le hβ hθh hM hz
  have hP0 := superP_nonneg hβ hθh hz
  have hCexp : ∀ K, 0 ≤ K → K ≤ max 1 (max K₁ K₂) →
      K * (profileSuper β θh s - κ) ≤ max 1 (max K₁ K₂) * Real.exp (min c 1 * s) := by
    intro K hK hKC
    exact mul_le_mul hKC (hE.trans hexp) hE0 (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · simpa using hCexp 1 zero_le_one (le_max_left _ _)
  · refine le_trans ?_ (hCexp K₁ hK₁ ((le_max_left _ _).trans (le_max_right _ _)))
    rw [profileSuper_deriv hβ hθh]
    refine (superField_le_mul hβ hθh hz).trans ?_
    calc superP β θh (profileSuper β θh s) * R ≤
          2 * superTheta θh * M * (profileSuper β θh s - κ) * R :=
          mul_le_mul_of_nonneg_right hPle hR
      _ = K₁ * (profileSuper β θh s - κ) := by ring
  · refine le_trans ?_ (hCexp K₂ hK₂ ((le_max_right _ _).trans (le_max_right _ _)))
    rw [profileSuper_deriv_deriv hβ hθh]
    have h1 := superEtaDeriv_le_mul hσ hP0
    have h2 := hM (profileSuper β θh s)
    have h3 := hβ.nonneg (profileSuper β θh s)
    have h4 : 0 ≤ superEtaDeriv (superSigma θh) (superP β θh (profileSuper β θh s)) :=
      superEtaDeriv_nonneg hσ hP0
    calc superTheta θh * β (profileSuper β θh s) *
          superEtaDeriv (superSigma θh) (superP β θh (profileSuper β θh s))
        ≤ superTheta θh * M * (2 * (1 + superSigma θh) / superSigma θh *
            superP β θh (profileSuper β θh s)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 (by linarith)) h1 h4 (by positivity)
      _ ≤ superTheta θh * M * (2 * (1 + superSigma θh) / superSigma θh *
            (2 * superTheta θh * M * (profileSuper β θh s - κ))) := by
          gcongr
      _ = K₂ * (profileSuper β θh s - κ) := by ring

/-- **Lemma A.3(iii)**: `Ψ(s) ↓ κ` as `s → -∞`. -/
theorem tendsto_profileSuper_atBot :
    Tendsto (profileSuper β θh) atBot (𝓝 (superKappa β θh)) := by
  obtain ⟨c, hc0, hc⟩ := exists_profileSuper_sub_kappa_le hβ hθh
  have hup : Tendsto (fun s ↦ superKappa β θh + Real.exp (c * s)) atBot
      (𝓝 (superKappa β θh + 0)) :=
    tendsto_const_nhds.add (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atBot hc0))
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun s ↦ (kappa_lt_profileSuper hβ hθh s).le) ?_
  filter_upwards [eventually_le_atBot 1] with s hs
  linarith [hc s hs]

end ProfileSuper


/-! ### (A.5): the rescaled super-profile `Ψ_{ε,θ̂}` -/

/-- (A.5): `Ψ_{ε,θ̂}(s) = ε Ψ_{1,θ̂}(s/ε)`. -/
noncomputable def profileSuperEps (β : ℝ → ℝ) (θh ε : ℝ) (s : ℝ) : ℝ :=
  ε * profileSuper β θh (s / ε)

section ProfileSuperEps

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β) {θh : ℝ} (hθh : 1 < θh) {ε : ℝ} (hε : 0 < ε)
include hβ hθh hε

theorem profileSuperEps_hasDerivAt (s : ℝ) :
    HasDerivAt (profileSuperEps β θh ε) (deriv (profileSuper β θh) (s / ε)) s := by
  have h := ((profileSuper_hasDerivAt hβ hθh (s / ε)).comp s
    ((hasDerivAt_id s).div_const ε)).const_mul ε
  rw [profileSuper_deriv hβ hθh]
  convert h using 1
  · rfl
  field_simp

theorem profileSuperEps_deriv :
    deriv (profileSuperEps β θh ε) = fun s ↦ deriv (profileSuper β θh) (s / ε) :=
  funext fun s ↦ (profileSuperEps_hasDerivAt hβ hθh hε s).deriv

omit hβ hθh in
theorem profileSuperEps_div (s : ℝ) :
    profileSuperEps β θh ε s / ε = profileSuper β θh (s / ε) := by
  rw [profileSuperEps, mul_div_cancel_left₀ _ hε.ne']

theorem profileSuperEps_hasDerivAt_deriv (s : ℝ) :
    HasDerivAt (deriv (profileSuperEps β θh ε))
      (deriv (deriv (profileSuper β θh)) (s / ε) / ε) s := by
  rw [profileSuperEps_deriv hβ hθh hε]
  have h := (profileSuper_hasDerivAt_deriv hβ hθh (s / ε)).comp s
    ((hasDerivAt_id s).div_const ε)
  rw [profileSuper_deriv_deriv hβ hθh]
  convert h using 1
  · rfl
  simp only [one_div]
  ring

theorem profileSuperEps_deriv_deriv (s : ℝ) :
    deriv (deriv (profileSuperEps β θh ε)) s = deriv (deriv (profileSuper β θh)) (s / ε) / ε :=
  (profileSuperEps_hasDerivAt_deriv hβ hθh hε s).deriv

/-- Rescaled Lemma A.3(i): `0 ≤ Ψ_ε'' ≤ θ̂ β_ε(Ψ_ε)`. -/
theorem profileSuperEps_deriv_deriv_mem (s : ℝ) :
    0 ≤ deriv (deriv (profileSuperEps β θh ε)) s ∧
      deriv (deriv (profileSuperEps β θh ε)) s ≤ θh * betaEps β ε (profileSuperEps β θh ε s) := by
  rw [profileSuperEps_deriv_deriv hβ hθh hε, betaEps, profileSuperEps_div hε]
  obtain ⟨h1, h2⟩ := profileSuper_deriv_deriv_mem hβ hθh (s / ε)
  refine ⟨div_nonneg h1 hε.le, ?_⟩
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right h2 hε.le

/-- Rescaled Lemma A.3(ii): `0 < Ψ_ε' ≤ 1`. -/
theorem profileSuperEps_deriv_mem (s : ℝ) :
    0 < deriv (profileSuperEps β θh ε) s ∧ deriv (profileSuperEps β θh ε) s ≤ 1 := by
  rw [profileSuperEps_deriv hβ hθh hε]; exact profileSuper_deriv_mem hβ hθh _

omit hε in
theorem profileSuperEps_contDiff : ContDiff ℝ ∞ (profileSuperEps β θh ε) :=
  contDiff_const.mul ((profileSuper_contDiff hβ hθh).comp (contDiff_id.div_const ε))

/-- Rescaled Lemma A.3(ii): `Ψ_ε(s) = s` for `s ≥ ε`. -/
theorem profileSuperEps_of_le {s : ℝ} (hs : ε ≤ s) : profileSuperEps β θh ε s = s := by
  rw [profileSuperEps, profileSuper_of_one_le hβ hθh ((one_le_div hε).2 hs),
    mul_div_cancel₀ _ hε.ne']

/-- Rescaled Lemma A.3(iii): `ε κ < Ψ_ε`. -/
theorem mul_kappa_lt_profileSuperEps (s : ℝ) :
    ε * superKappa β θh < profileSuperEps β θh ε s :=
  mul_lt_mul_of_pos_left (kappa_lt_profileSuper hβ hθh _) hε

/-- Rescaled Lemma A.3(iii): `s₊ ≤ Ψ_ε(s)`. -/
theorem max_le_profileSuperEps (s : ℝ) : max s 0 ≤ profileSuperEps β θh ε s := by
  have h := max_le_profileSuper hβ hθh (s / ε)
  have e2 : max s 0 = ε * max (s / ε) 0 := by
    rw [mul_max_of_nonneg _ _ hε.le, mul_zero, mul_div_cancel₀ _ hε.ne']
  rw [e2, profileSuperEps]
  exact mul_le_mul_of_nonneg_left h hε.le

/-- Rescaled Lemma A.3(iii): `sup_ℝ |Ψ_ε - s₊| ≤ ε`. -/
theorem abs_profileSuperEps_sub_le (s : ℝ) :
    |profileSuperEps β θh ε s - max s 0| ≤ ε := by
  have h := abs_profileSuper_sub_le hβ hθh (s / ε)
  have e2 : max s 0 = ε * max (s / ε) 0 := by
    rw [mul_max_of_nonneg _ _ hε.le, mul_zero, mul_div_cancel₀ _ hε.ne']
  rw [e2, profileSuperEps, ← mul_sub, abs_mul, abs_of_pos hε]
  exact mul_le_of_le_one_right hε.le h

/-- `Ψ_ε` is `1`-Lipschitz. -/
theorem abs_profileSuperEps_sub_le' (s t : ℝ) :
    |profileSuperEps β θh ε t - profileSuperEps β θh ε s| ≤ |t - s| := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm, abs_sub_comm t]; exact this t s (le_of_not_ge hst)
  have hd : ∀ u, HasDerivAt (profileSuperEps β θh ε) (deriv (profileSuperEps β θh ε) u) u :=
    fun u ↦ by
      rw [profileSuperEps_deriv hβ hθh hε]; exact profileSuperEps_hasDerivAt hβ hθh hε u
  have h1 : Monotone (profileSuperEps β θh ε) := monotone_of_hasDerivAt_nonneg' hd fun u ↦
    (profileSuperEps_deriv_mem hβ hθh hε u).1.le
  have h2 : Monotone fun u ↦ u - profileSuperEps β θh ε u :=
    monotone_of_hasDerivAt_nonneg' (fun u ↦ (hasDerivAt_id u).sub (hd u)) fun u ↦ by
      linarith [(profileSuperEps_deriv_mem hβ hθh hε u).2]
  have h3 := h1 hst
  have h4 := h2 hst
  simp only at h4
  rw [abs_of_nonneg (sub_nonneg.2 h3), abs_of_nonneg (sub_nonneg.2 hst)]
  linarith

end ProfileSuperEps

end PerronVariational

end
