/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The semilinear approximation

The semilinear approximation of [§3.4](#AFS:s.semilinear-intro) of F. Abedin, W. M. Feldman, K.
Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 ("the paper"):

* Reaction profiles `β` satisfying [(3.5)](#AFS:e.beta-conditions).
* `β_ε`, `𝓑_ε`, `χ_ε = 2 𝓑_ε(u_ε)` ([(3.6)](#AFS:eqn:chiEps)).
* Classical solutions of [(3.4)](#AFS:e.bernoulli-parabolic-semilinear).

Regularity of solutions. Solutions are classical `C^{2,1}` (continuous `∇ₓu`, `D²ₓu`, `∂ₜu`), as
in [Proposition 3.12](#AFS:p.semilinear-wellposed); since `Q` is only Lipschitz, the equation gives
`C^{2,1}` and not `C^∞` regularity (`C^∞` holds for smooth `Q`, [Appendix B](#AFS:s.semilinear)).
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- The reaction profile conditions [(3.5)](#AFS:e.beta-conditions): `β ∈ C^∞(ℝ)`,
`supp β = [0, 1]` and `β > 0` on `(0, 1)` (equivalently: `β = 0` off `(0, 1)` and `β > 0` on
`(0, 1)`), `β` nondecreasing on `[0, 1/2]` and nonincreasing on `[1/2, 1]`, `∫_ℝ β = 1/2`. -/
def IsReactionProfile (β : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ β ∧ (∀ s ∉ Ioo (0 : ℝ) 1, β s = 0) ∧ (∀ s ∈ Ioo (0 : ℝ) 1, 0 < β s) ∧
    MonotoneOn β (Icc 0 (1 / 2)) ∧ AntitoneOn β (Icc (1 / 2) 1) ∧ ∫ s, β s = 1 / 2

/-- `β_ε(z) = ε⁻¹ β(z / ε)` (paper, [§3.4](#AFS:s.semilinear-intro)). -/
noncomputable def betaEps (β : ℝ → ℝ) (ε z : ℝ) : ℝ := β (z / ε) / ε

/-- `𝓑_ε(z) = ∫₀ᶻ β_ε(s) ds` (paper, [§3.4](#AFS:s.semilinear-intro)). -/
noncomputable def bigBEps (β : ℝ → ℝ) (ε z : ℝ) : ℝ := ∫ s in (0 : ℝ)..z, betaEps β ε s

/-- `χ_ε = 2 𝓑_ε(u_ε)`, [(3.6)](#AFS:eqn:chiEps). -/
noncomputable def chiEps (β : ℝ → ℝ) (ε : ℝ) (u : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  2 * bigBEps β ε (u p)

/-- `u` is a classical (`C^{2,1}`) solution of the semilinear equation
`∂ₜu = Δu - Q(x)² β_ε(u)` (first line of [(3.4)](#AFS:e.bernoulli-parabolic-semilinear)) in `U × I`:
`u`, `∇ₓu`, `D²ₓu`, `∂ₜu` exist and are continuous on `U × I` (the time derivative is two-sided, so
for `I = (0, T]` the solution is assumed to be defined and differentiable across `t = T`), and the
equation holds pointwise on `U × I`. -/
def IsSemilinearSolOn (U : Set (E d)) (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ) (I : Set ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧
    (∀ t ∈ I, ContDiffOn ℝ 2 (fun x ↦ u (x, t)) U) ∧
    ContinuousOn (gradₓ u) (U ×ˢ I) ∧
    ContinuousOn (fun p ↦ iteratedFDeriv ℝ 2 (fun y ↦ u (y, p.2)) p.1) (U ×ˢ I) ∧
    (∀ p ∈ U ×ˢ I, DifferentiableAt ℝ (fun s ↦ u (p.1, s)) p.2) ∧
    ContinuousOn (dₜ u) (U ×ˢ I) ∧
    ∀ p ∈ U ×ˢ I, dₜ u p = lapₓ u p - Q p.1 ^ 2 * betaEps β ε (u p)

/-- `u` solves the semilinear problem [(3.4)](#AFS:e.bernoulli-parabolic-semilinear) with parabolic
boundary data `gε`: `u ∈ C(Ū × [0, ∞))`, `u` is a classical `C^{2,1}` solution (see the module
docstring) of the equation in `U_∞`, and `u = gε` on `∂_P U_∞ = (Ū × {0}) ∪ (∂U × [0, ∞))`. -/
def IsSemilinearSolution (U : Set (E d)) (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ) (gε : E d → ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (closure U ×ˢ Ici 0) ∧ IsSemilinearSolOn U Q β ε (Ioi 0) u ∧
    (∀ x ∈ closure U, u (x, 0) = gε x) ∧ ∀ x ∈ frontier U, ∀ t : ℝ, 0 ≤ t → u (x, t) = gε x

end PerronVariational

end
