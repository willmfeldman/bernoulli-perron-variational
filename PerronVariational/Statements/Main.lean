/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary

/-!
# Statements of the main results

The main results of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper"):

* `MainSmallestStatement`, `MainLargestStatement`: **Theorem 1.1**.
* `Corollary2DSmallestStatement`, `Corollary2DLargestStatement`: **Corollary 1.2**.
-/

open Set Filter Topology Metric

@[expose] public section

namespace PerronVariational

/-- **Theorem 1.1**, smallest supersolution case. Let `g` be a smooth strict subsolution
(Definition 2.2, with `g ∈ C²(ℝᵈ)`; see `IsStrictSub`) with `g > 0` on `∂U`, and `u` the smallest
supersolution above `g` ((2.4)). Then
(i) `u` is a viscosity solution of (1.1) in `U`;
(ii) `u` is an inner variational solution of (1.1) in `U` (for some `χ`);
(iii) `u` is a downward minimizer of `J_Q` locally around each free boundary point: for every
`x ∈ ∂{u > 0} ∩ U` there is a ball `B_r(x) ⊂⊂ U` such that `u` is a downward minimizer of
`J_Q(·; B_r(x))` (Definition 2.11, in the form of `IsDownwardMinimizer`). -/
def MainSmallestStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (g : E d → ℝ), IsStrictSub S.U S.Q g →
    (∀ x ∈ frontier S.U, 0 < g x) →
    IsViscSolution S.U S.Q (perronSmallest S.U S.Q g) ∧
    (∃ χ : E d → ℝ, IsInnerVarSolution S.U S.Q (perronSmallest S.U S.Q g) χ) ∧
    ∀ x ∈ freeBoundary (perronSmallest S.U S.Q g) S.U, ∃ r > 0, closedBall x r ⊆ S.U ∧
      IsDownwardMinimizer (ball x r) S.Q (perronSmallest S.U S.Q g)

/-- **Theorem 1.1**, largest subsolution case. Let `g` be a smooth strict supersolution
(Definition 2.2; no boundary positivity needed), and `u` the largest subsolution below `g`
((2.2)). Then (i) `u` is a viscosity solution, (ii) an inner variational
solution, and (iii) an upward minimizer of `J_Q` locally around each free boundary point. -/
def MainLargestStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (g : E d → ℝ), IsStrictSuper S.U S.Q g →
    IsViscSolution S.U S.Q (perronLargest S.U S.Q g) ∧
    (∃ χ : E d → ℝ, IsInnerVarSolution S.U S.Q (perronLargest S.U S.Q g) χ) ∧
    ∀ x ∈ freeBoundary (perronLargest S.U S.Q g) S.U, ∃ r > 0, closedBall x r ⊆ S.U ∧
      IsUpwardMinimizer (ball x r) S.Q (perronLargest S.U S.Q g)

/-- **Corollary 1.2(i)**. In `ℝ²`, for `u` the smallest supersolution as in Theorem 1.1,
the free boundary `∂{u > 0} ∩ U` is the disjoint union `FB_reg ∪ FB_TP`, where `FB_reg` is
relatively open in the free boundary and `u` is a classical solution near each of its points,
and at each `x₀ ∈ FB_TP` every subsequential blow-up limit of `u` is `Q(x₀) |y · e|` for some unit
vector `e` (in blow-up coordinates `y`, i.e. the paper's `Q(x₀)|(x - x₀) · e|`). -/
def Corollary2DSmallestStatement : Prop :=
  ∀ (S : Setting 2) (g : E 2 → ℝ), IsStrictSub S.U S.Q g → (∀ x ∈ frontier S.U, 0 < g x) →
    ∃ FBreg FBtp : Set (E 2),
      Disjoint FBreg FBtp ∧
      FBreg ∪ FBtp = freeBoundary (perronSmallest S.U S.Q g) S.U ∧
      (∃ O : Set (E 2), IsOpen O ∧ FBreg = O ∩ freeBoundary (perronSmallest S.U S.Q g) S.U) ∧
      (∀ x₀ ∈ FBreg, IsClassicalNear S.U S.Q (perronSmallest S.U S.Q g) x₀) ∧
      ∀ x₀ ∈ FBtp, ∀ v : E 2 → ℝ, IsBlowupLimit (perronSmallest S.U S.Q g) x₀ v →
        ∃ e : E 2, ‖e‖ = 1 ∧ ∀ y, v y = S.Q x₀ * |inner ℝ y e|

/-- **Corollary 1.2(ii)**. In `ℝ²`, the largest subsolution as in Theorem 1.1 is a classical
solution of (1.1) in `U`: near every free boundary point it is a classical solution (`C^{1,γ}`
free boundary, classical free boundary condition). -/
def Corollary2DLargestStatement : Prop :=
  ∀ (S : Setting 2) (g : E 2 → ℝ), IsStrictSuper S.U S.Q g →
    ∀ x₀ ∈ freeBoundary (perronLargest S.U S.Q g) S.U,
      IsClassicalNear S.U S.Q (perronLargest S.U S.Q g) x₀

end PerronVariational

end
