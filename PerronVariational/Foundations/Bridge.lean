/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Defs.Regularity

/-!
# Bridge to elliptic-bernoulli-foundations

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

The dependency elliptic-bernoulli-foundations v0.1.0 (Lake package
`elliptic_bernoulli_foundations`) exports its theorems in its own vocabulary. Its basic definitions
are verbatim copies of the ones in this library, up to the namespace
`PerronVariational ↦ EllipticBernoulli`. This file checks that the two libraries' definitions still
match, in the direction used by the registry glue (`Foundations/Glue.lean`).

* Plain definitions agree by `rfl`/`Iff.rfl`: `E`, `posSet`, `freeBoundary`, `CompactlyContained`,
  `divergence`, `HasWeakGradient`, `MemH1`, `MemH1Loc`, `energyJ`, `energyJχ`, `TouchesBelow`,
  `TouchesAbove`, `IsViscSuper`, `IsViscSub`, `IsViscSolution`, `innerVarIntegrand`, `blowup`,
  `IsBlowupLimit`, `IsC1GammaHypersurfaceNear`, `IsClassicalNear`.
* `IsInnerVarSolution` is a structure in both libraries, so the two are distinct types:
  `IsInnerVarSolution.toEB` and `IsInnerVarSolution.ofEB` convert field by field.
* elliptic-bernoulli-foundations has no `Setting` structure: its statements take the hypotheses on
  `U` and `Q` explicitly. The lemmas `isOpen_of_setting`, `exists_lipschitzOnWith_of_setting`,
  `continuousOn_of_setting` and `Q_mem_of_setting` extract the fields, restricted from `closure U`
  to `U`, in the form its theorems take them.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

namespace Foundations

/-! ### Plain definitions -/

theorem E_eq_eb : E d = EllipticBernoulli.E d :=
  rfl

theorem posSet_eq_eb (u : E d → ℝ) (U : Set (E d)) :
    posSet u U = EllipticBernoulli.posSet u U :=
  rfl

theorem freeBoundary_eq_eb (u : E d → ℝ) (U : Set (E d)) :
    freeBoundary u U = EllipticBernoulli.freeBoundary u U :=
  rfl

theorem compactlyContained_iff_eb {X : Type*} [TopologicalSpace X] {A B : Set X} :
    CompactlyContained A B ↔ EllipticBernoulli.CompactlyContained A B :=
  Iff.rfl

theorem divergence_eq_eb (ξ : E d → E d) : divergence ξ = EllipticBernoulli.divergence ξ :=
  rfl

theorem hasWeakGradient_iff_eb {U : Set (E d)} {u : E d → ℝ} {G : E d → E d} :
    HasWeakGradient U u G ↔ EllipticBernoulli.HasWeakGradient U u G :=
  Iff.rfl

theorem memH1_iff_eb {U : Set (E d)} {u : E d → ℝ} {G : E d → E d} :
    MemH1 U u G ↔ EllipticBernoulli.MemH1 U u G :=
  Iff.rfl

theorem memH1Loc_iff_eb {U : Set (E d)} {u : E d → ℝ} {G : E d → E d} :
    MemH1Loc U u G ↔ EllipticBernoulli.MemH1Loc U u G :=
  Iff.rfl

theorem energyJ_eq_eb (V : Set (E d)) (Q u : E d → ℝ) (G : E d → E d) :
    energyJ V Q u G = EllipticBernoulli.energyJ V Q u G :=
  rfl

theorem energyJχ_eq_eb (V : Set (E d)) (Q : E d → ℝ) (G : E d → E d) (χ : E d → ℝ) :
    energyJχ V Q G χ = EllipticBernoulli.energyJχ V Q G χ :=
  rfl

theorem touchesBelow_iff_eb {X : Type*} [TopologicalSpace X] {φ u : X → ℝ} {S : Set X} {x : X} :
    TouchesBelow φ u S x ↔ EllipticBernoulli.TouchesBelow φ u S x :=
  Iff.rfl

theorem touchesAbove_iff_eb {X : Type*} [TopologicalSpace X] {φ u : X → ℝ} {S : Set X} {x : X} :
    TouchesAbove φ u S x ↔ EllipticBernoulli.TouchesAbove φ u S x :=
  Iff.rfl

theorem isViscSuper_iff_eb {U : Set (E d)} {Q u : E d → ℝ} :
    IsViscSuper U Q u ↔ EllipticBernoulli.IsViscSuper U Q u :=
  Iff.rfl

theorem isViscSub_iff_eb {U : Set (E d)} {Q u : E d → ℝ} :
    IsViscSub U Q u ↔ EllipticBernoulli.IsViscSub U Q u :=
  Iff.rfl

theorem isViscSolution_iff_eb {U : Set (E d)} {Q u : E d → ℝ} :
    IsViscSolution U Q u ↔ EllipticBernoulli.IsViscSolution U Q u :=
  Iff.rfl

theorem innerVarIntegrand_eq_eb (Q u χ : E d → ℝ) (ξ : E d → E d) :
    innerVarIntegrand Q u χ ξ = EllipticBernoulli.innerVarIntegrand Q u χ ξ :=
  rfl

theorem blowup_eq_eb (u : E d → ℝ) (x₀ : E d) (r : ℝ) :
    blowup u x₀ r = EllipticBernoulli.blowup u x₀ r :=
  rfl

theorem isBlowupLimit_iff_eb {u : E d → ℝ} {x₀ : E d} {v : E d → ℝ} :
    IsBlowupLimit u x₀ v ↔ EllipticBernoulli.IsBlowupLimit u x₀ v :=
  Iff.rfl

theorem isC1GammaHypersurfaceNear_iff_eb {S : Set (E d)} {x₀ : E d} {r : ℝ} :
    IsC1GammaHypersurfaceNear S x₀ r ↔ EllipticBernoulli.IsC1GammaHypersurfaceNear S x₀ r :=
  Iff.rfl

theorem isClassicalNear_iff_eb {U : Set (E d)} {Q u : E d → ℝ} {x₀ : E d} :
    IsClassicalNear U Q u x₀ ↔ EllipticBernoulli.IsClassicalNear U Q u x₀ :=
  Iff.rfl

/-! ### `Setting` fields in the form of elliptic-bernoulli-foundations -/

theorem isOpen_of_setting (S : Setting d) : IsOpen S.U :=
  S.isOpen

theorem exists_lipschitzOnWith_of_setting (S : Setting d) : ∃ K, LipschitzOnWith K S.Q S.U := by
  obtain ⟨K, hK⟩ := S.lip
  exact ⟨K, hK.mono subset_closure⟩

theorem continuousOn_of_setting (S : Setting d) : ContinuousOn S.Q S.U := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_of_setting S
  exact hK.continuousOn

theorem Q_mem_of_setting (S : Setting d) : ∀ x ∈ S.U, S.Qmin ≤ S.Q x ∧ S.Q x ≤ S.Qmax :=
  fun x hx ↦ S.Q_mem x (subset_closure hx)

end Foundations

/-! ### Structures -/

/-- An inner variational solution here is one in the sense of elliptic-bernoulli-foundations
(field by field; the integrands agree by `innerVarIntegrand_eq_eb`). -/
theorem IsInnerVarSolution.toEB {U : Set (E d)} {Q u χ : E d → ℝ}
    (h : IsInnerVarSolution U Q u χ) : EllipticBernoulli.IsInnerVarSolution U Q u χ where
  nonneg := h.nonneg
  locLip := h.locLip
  c2 := h.c2
  harmonic := h.harmonic
  meas := h.meas
  zero_one := h.zero_one
  pos_le := h.pos_le
  stationary ξ hξ hξc hξU := by
    rw [← Foundations.innerVarIntegrand_eq_eb]
    exact h.stationary ξ hξ hξc hξU

/-- An inner variational solution in the sense of elliptic-bernoulli-foundations is one here. -/
theorem IsInnerVarSolution.ofEB {U : Set (E d)} {Q u χ : E d → ℝ}
    (h : EllipticBernoulli.IsInnerVarSolution U Q u χ) : IsInnerVarSolution U Q u χ where
  nonneg := h.nonneg
  locLip := h.locLip
  c2 := h.c2
  harmonic := h.harmonic
  meas := h.meas
  zero_one := h.zero_one
  pos_le := h.pos_le
  stationary ξ hξ hξc hξU := by
    rw [Foundations.innerVarIntegrand_eq_eb]
    exact h.stationary ξ hξ hξc hξU

theorem Foundations.isInnerVarSolution_iff_eb {U : Set (E d)} {Q u χ : E d → ℝ} :
    IsInnerVarSolution U Q u χ ↔ EllipticBernoulli.IsInnerVarSolution U Q u χ :=
  ⟨IsInnerVarSolution.toEB, IsInnerVarSolution.ofEB⟩

end PerronVariational

end
