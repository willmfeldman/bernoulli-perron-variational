/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Setting
public import GMTFoundations.Defs.Sobolev
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Minimal Sobolev notions and the Alt–Caffarelli energy

Notation for F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

* `HasWeakGradient U u G`, `MemH1 U u G`, `MemH1Loc U u G`: the weak gradient is carried as
  explicit data `G`. The paper works with the Sobolev space `H¹(U)` and its (unique a.e.) weak
  gradient; here a function comes with a chosen `L²` weak gradient, which is equivalent and avoids
  quotient spaces.
* `energyJ V Q u G`: the Alt–Caffarelli energy `J_Q(u; V)` (the paper's (1.2)), and
  `energyJχ V Q G χ`: the energy `J(u, χ; V)` of a pair (the paper's §3.4).
* `TendstoLpLoc` (strong `L^p_loc` convergence) and `TendstoWeakL2` (weak `L²` convergence).

The paper's energies are real integrals of integrable functions; here they are `ℝ≥0∞`-valued lower
Lebesgue integrals, so no integrability side conditions are needed. Both agree whenever the
paper's integral is finite.

`HasWeakGradient`, `MemH1`, `MemH1Loc`, `TendstoLpLoc` and `TendstoWeakL2` are defined in
gmt-foundations v0.1.0 (`GMTFoundations.Defs.Sobolev`) and are re-exported here.
-/
open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

export GMTFoundations (HasWeakGradient MemH1 MemH1Loc TendstoLpLoc TendstoWeakL2)

/-- The Alt–Caffarelli energy `J_Q(u; V) = ∫_V |∇u|² + Q² 1_{u>0}` (paper (1.2)),
with the gradient supplied as data `G`. Valued in `ℝ≥0∞` (a lower integral), so no integrability
condition is needed. -/
noncomputable def energyJ (V : Set (E d)) (Q u : E d → ℝ) (G : E d → E d) : ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal (‖G x‖ ^ 2 + Q x ^ 2 * (posSet u V).indicator 1 x)

/-- The energy of a pair, `J(u, χ; V) = ∫_V |∇u|² + Q² χ` (paper §3.4), with the gradient
supplied as data `G`. Valued in `ℝ≥0∞` (a lower integral). -/
noncomputable def energyJχ (V : Set (E d)) (Q : E d → ℝ) (G : E d → E d) (χ : E d → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal (‖G x‖ ^ 2 + Q x ^ 2 * χ x)

end PerronVariational

end
