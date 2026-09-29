/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary

/-!
# Linearity of the inner variation integrand in the test field

Equation numbers refer to F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

The integrand `innerVarIntegrand Q v χ ξ x` of (2.5) depends linearly on `(ξ(x), Dξ(x))`. We
record additivity (at differentiability points) and the formula for the fields `ζ eᵢ`:
`innerVarIntegrand Q v χ (ζ eᵢ) x = aᵢ(x) ζ(x) + Dζ(x) gᵢ(x)` with
`aᵢ = ∂ᵢ(Q²) χ` and `gᵢ = (|∇v|² + Q²χ) eᵢ - 2 ∂ᵢv ∇v`. This reduces the density arguments of
the proof of **Theorem 3.10** for vector fields to the scalar ones.

## Main definitions

* `PerronVariational.LongTime.ivCoeffA`, `PerronVariational.LongTime.ivCoeffG`: `aᵢ`, `gᵢ`.

## Main results

* `PerronVariational.LongTime.innerVarIntegrand_sum`
* `PerronVariational.LongTime.innerVarIntegrand_smul_const`
* `PerronVariational.LongTime.innerVarIntegrand_eq_sum_coord`
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-- The coefficient `a_e = D(Q²)(e) χ`. -/
noncomputable def ivCoeffA (Q χ : E d → ℝ) (e : E d) (x : E d) : ℝ :=
  fderiv ℝ (fun y ↦ Q y ^ 2) x e * χ x

/-- The coefficient `g_e = (|∇v|² + Q²χ) e - 2 ⟨∇v, e⟩ ∇v`. -/
noncomputable def ivCoeffG (Q v χ : E d → ℝ) (e : E d) (x : E d) : E d :=
  (‖∇ v x‖ ^ 2 + Q x ^ 2 * χ x) • e - (2 * inner ℝ (∇ v x) e) • ∇ v x

theorem divergence_add {ξ₁ ξ₂ : E d → E d} {x : E d} (h₁ : DifferentiableAt ℝ ξ₁ x)
    (h₂ : DifferentiableAt ℝ ξ₂ x) :
    divergence (fun y ↦ ξ₁ y + ξ₂ y) x = divergence ξ₁ x + divergence ξ₂ x := by
  simp [divergence, fderiv_fun_add h₁ h₂]

theorem innerVarIntegrand_add (Q v χ : E d → ℝ) {ξ₁ ξ₂ : E d → E d} {x : E d}
    (h₁ : DifferentiableAt ℝ ξ₁ x) (h₂ : DifferentiableAt ℝ ξ₂ x) :
    innerVarIntegrand Q v χ (fun y ↦ ξ₁ y + ξ₂ y) x =
      innerVarIntegrand Q v χ ξ₁ x + innerVarIntegrand Q v χ ξ₂ x := by
  simp only [innerVarIntegrand, divergence_add h₁ h₂, fderiv_fun_add h₁ h₂,
    ContinuousLinearMap.add_apply, inner_add_right, map_add]
  ring

theorem innerVarIntegrand_zero (Q v χ : E d → ℝ) (x : E d) :
    innerVarIntegrand Q v χ (fun _ ↦ 0) x = 0 := by
  simp [innerVarIntegrand, divergence]

theorem innerVarIntegrand_sum (Q v χ : E d → ℝ) {ι : Type*} (s : Finset ι)
    {ξ : ι → E d → E d} {x : E d} (h : ∀ i ∈ s, DifferentiableAt ℝ (ξ i) x) :
    innerVarIntegrand Q v χ (fun y ↦ ∑ i ∈ s, ξ i y) x =
      ∑ i ∈ s, innerVarIntegrand Q v χ (ξ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using innerVarIntegrand_zero Q v χ x
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have hs : DifferentiableAt ℝ (fun y ↦ ∑ i ∈ s, ξ i y) x :=
      DifferentiableAt.fun_sum fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    rw [innerVarIntegrand_add Q v χ (h j (Finset.mem_insert_self j s)) hs,
      ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)]

theorem innerVarIntegrand_smul_const (Q v χ : E d → ℝ) {ζ : E d → ℝ} {x : E d}
    (hζ : DifferentiableAt ℝ ζ x) (e : E d) :
    innerVarIntegrand Q v χ (fun y ↦ ζ y • e) x =
      ivCoeffA Q χ e x * ζ x + fderiv ℝ ζ x (ivCoeffG Q v χ e x) := by
  have hD : fderiv ℝ (fun y ↦ ζ y • e) x = (fderiv ℝ ζ x).smulRight e := fderiv_smul_const hζ e
  simp only [innerVarIntegrand, divergence, hD, ivCoeffA, ivCoeffG, map_sub, map_smul,
    ContinuousLinearMap.smulRight_apply, inner_smul_right, smul_eq_mul]
  rw [show ((fderiv ℝ ζ x).smulRight e : E d →L[ℝ] E d).toLinearMap =
    (fderiv ℝ ζ x).toLinearMap.smulRight e from rfl, LinearMap.trace_smulRight]
  simp only [ContinuousLinearMap.coe_coe]
  ring

/-- The coordinate vectors `eᵢ`. -/
noncomputable abbrev coordVec (i : Fin d) : E d := EuclideanSpace.single i 1

theorem sum_coord_smul (v : E d) : ∑ i, v i • coordVec i = v := by
  simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v

/-- **Coordinate decomposition** of the integrand at a differentiability point of `ξ`. -/
theorem innerVarIntegrand_eq_sum_coord (Q v χ : E d → ℝ) {ξ : E d → E d} {x : E d}
    (hξ : DifferentiableAt ℝ ξ x) :
    innerVarIntegrand Q v χ ξ x = ∑ i, (ivCoeffA Q χ (coordVec i) x * ξ x i +
      fderiv ℝ (fun y ↦ ξ y i) x (ivCoeffG Q v χ (coordVec i) x)) := by
  have hcoord : ∀ i, DifferentiableAt ℝ (fun y ↦ ξ y i) x := fun i ↦
    ((EuclideanSpace.proj i : E d →L[ℝ] ℝ).differentiableAt).comp x hξ
  have hξeq : ξ = fun y ↦ ∑ i, ξ y i • coordVec i := funext fun y ↦ (sum_coord_smul _).symm
  conv_lhs => rw [hξeq]
  rw [innerVarIntegrand_sum Q v χ _ fun i _ ↦ (hcoord i).smul_const _]
  exact Finset.sum_congr rfl fun i _ ↦ innerVarIntegrand_smul_const Q v χ (hcoord i) _

end LongTime

end PerronVariational

end
