/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.BV
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.LinearAlgebra.Trace

/-!
# Standing setting

The ambient space, positivity sets, free boundaries, the `C²`-boundary condition, the standing
assumptions, and the (space and space-time) differential operators used throughout the
formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper").

## Conventions

* All functions are total (`E d → ℝ`, `E d × ℝ → ℝ`); every predicate restricts to its domain
  explicitly, and values outside the domain are never used.
* Space-time points are `p : E d × ℝ`, with `p.1` the space and `p.2` the time variable.

## Definitions from gmt-foundations

`E`, `CompactlyContained`, `divergence`, `fderivₓ` and `divₓ` are defined in gmt-foundations v0.1.0
(`GMTFoundations.Defs.Setup`, `Defs.Calculus`, `Defs.BV`) and re-exported into this namespace.
GMT's `divergence` is stated over `Rn n`, which is the same reducible abbreviation as `E n`.
-/

open Set Filter Topology
open scoped Gradient Laplacian

@[expose] public section

namespace PerronVariational

export GMTFoundations (E CompactlyContained divergence fderivₓ divₓ)

variable {d : ℕ}

/-- The positivity set `{u > 0}` of `u` inside the domain `U` (paper: `{u > 0}`, with `u` defined
on `U` only). -/
def posSet (u : E d → ℝ) (U : Set (E d)) : Set (E d) := {x ∈ U | 0 < u x}

/-- The free boundary `∂{u > 0} ∩ U` (paper, e.g. (1.1) and Thm 1.1). -/
def freeBoundary (u : E d → ℝ) (U : Set (E d)) : Set (E d) := frontier (posSet u U) ∩ U

/-- `U` has `C²` boundary (standing assumption (i) of the paper), encoded by a global `C²` defining
function: `U = {ρ < 0}` with `∇ρ ≠ 0` on `∂U`. The paper assumes `∂U` is a `C²` hypersurface; here
we ask for a defining function, which is the standard equivalent formulation and avoids local
charts. -/
def HasC2Boundary (U : Set (E d)) : Prop :=
  ∃ ρ : E d → ℝ, ContDiff ℝ 2 ρ ∧ U = {x | ρ x < 0} ∧ ∀ x ∈ frontier U, ∇ ρ x ≠ 0

/-- The standing assumptions of the paper (§1.2):
(i) `U ⊆ ℝᵈ`, `d ≥ 2`, is open, bounded, connected with `C²` boundary (see `HasC2Boundary`);
(ii) `Q ∈ C^{0,1}(Ū)` with `Q_min ≤ Q ≤ Q_max` on `Ū`, `0 < Q_min ≤ Q_max`.

The function `Q` is total on `E d`; only its values on `closure U` are meaningful. -/
structure Setting (d : ℕ) where
  /-- The domain `U`. -/
  U : Set (E d)
  /-- The coefficient field `Q`. -/
  Q : E d → ℝ
  /-- The lower bound `Q_min`. -/
  Qmin : ℝ
  /-- The upper bound `Q_max`. -/
  Qmax : ℝ
  two_le : 2 ≤ d
  isOpen : IsOpen U
  isBounded : Bornology.IsBounded U
  isConnected : IsConnected U
  c2 : HasC2Boundary U
  lip : ∃ K, LipschitzOnWith K Q (closure U)
  Qmin_pos : 0 < Qmin
  Qmin_le_Qmax : Qmin ≤ Qmax
  Q_mem : ∀ x ∈ closure U, Qmin ≤ Q x ∧ Q x ≤ Qmax

/-! ### Differential operators -/

/-- Spatial gradient `∇ₓφ(x,t)` of a space-time function (gradient of the time slice). -/
noncomputable def gradₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : E d :=
  ∇ (fun y ↦ φ (y, p.2)) p.1

/-- Spatial Laplacian `Δₓφ(x,t)` of a space-time function (Laplacian of the time slice). -/
noncomputable def lapₓ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  Δ (fun y ↦ φ (y, p.2)) p.1

/-- Time derivative `∂ₜφ(x,t)` of a space-time function. -/
noncomputable def dₜ (φ : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  deriv (fun s ↦ φ (p.1, s)) p.2

end PerronVariational

end
