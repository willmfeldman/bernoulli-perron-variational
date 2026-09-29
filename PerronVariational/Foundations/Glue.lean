/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
import EllipticBernoulli.Blowup.PlanarClassification
import EllipticBernoulli.Flatness.Classical
import EllipticBernoulli.Lipschitz.Estimate
import EllipticBernoulli.Variational.Continuity
import EllipticBernoulli.Variational.Existence
import EllipticBernoulli.Variational.Perturbation
import PerronVariational.Foundations.Bridge

/-!
# Registry glue: results from elliptic-bernoulli-foundations

This file belongs to the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981
("the paper"). It proves several results from the literature that the paper cites, stated exactly
as in `Registry/Obstacle.lean` and `Registry/BlowUp.lean`, from the theorems of the dependency
elliptic-bernoulli-foundations v0.1.0 (Lake package `elliptic_bernoulli_foundations`, namespace
`EllipticBernoulli`). The registry entries are discharged by one-line calls to the theorems here.

* Existence and continuity of minimizers of one-sided obstacle problems for `J_Q`
  (`obstacle_below_exists`, `obstacle_above_exists`, and the variants
  `obstacle_below_exists_continuousOn`, `obstacle_above_exists_continuousOn`):
  `exists_obstacle_below`, `exists_obstacle_above` (`EllipticBernoulli.Variational.Existence`) and
  `IsObstacleMinimizer.exists_continuousOn` (`EllipticBernoulli.Variational.Continuity`).
* Energy-decreasing perturbations (`energy_decrease_of_not_super`, `energy_decrease_of_not_sub`):
  the theorems of the same names in `EllipticBernoulli.Variational.Perturbation`.
* The interior Lipschitz estimate for viscosity solutions
  (`locallyLipschitzOn_of_isViscSolution`): the theorem of the same name in
  `EllipticBernoulli.Lipschitz.Estimate`, from the `Setting` fields `isOpen` and `lip`.
* The classification of 1-homogeneous global inner variational solutions in the plane
  (`classification_homogeneous_planar`): the theorem of the same name in
  `EllipticBernoulli.Blowup.PlanarClassification`.
* Flat free boundaries are classical (`isClassicalNear_of_flat`).

The `_continuousOn` variants of the obstacle results assert continuity of the minimizer on all of
`U` rather than only in `B`.

The obstacle minimizers of elliptic-bernoulli-foundations use the constraint-set encoding
`EllipticBernoulli.IsObstacleMinimizer U B Q u K w Gw` with `K = fun y ↦ Icc 0 (u y)` (the
constraint `0 ≤ w ≤ u`) or `K = fun y ↦ Ici (u y)` (the constraint `w ≥ u`); membership in
`Icc`/`Ici` unfolds definitionally to the registry's inequalities.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

namespace Foundations

variable {d : ℕ}

/-! ### Obstacle problems -/

/-- The bound `|Q| ≤ C` on `U` from `0 < c ≤ Q ≤ C` on `U` (the form of the bound in the
existence theorems of elliptic-bernoulli-foundations). -/
private theorem exists_abs_le {U : Set (E d)} {Q : E d → ℝ} (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) : ∃ C, ∀ x ∈ U, |Q x| ≤ C := by
  obtain ⟨c, hc, hcQ⟩ := hQpos
  obtain ⟨C, hC⟩ := hQb
  exact ⟨C, fun x hx ↦ by rw [abs_of_pos (hc.trans_le (hcQ x hx))]; exact hC x hx⟩

/-- **Constraint `0 ≤ w ≤ u`, with continuity on all of `U`.** As `obstacle_below_exists`, with
`ContinuousOn w U`
in place of `ContinuousOn w (ball x₀ r)`. -/
theorem obstacle_below_exists_continuousOn {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    (hGu : MemH1Loc U u Gu) {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc U w Gw ∧ ContinuousOn w U ∧
      (∀ y ∈ U \ ball x₀ r, w y = u y) ∧ (∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y) ∧
      ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
        (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
        energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv := by
  obtain ⟨K, hK⟩ := hQ
  obtain ⟨w₀, Gw, hmin₀⟩ := EllipticBernoulli.exists_obstacle_below hU hK.continuousOn
    (exists_abs_le hQpos hQb) hu0 (memH1Loc_iff_eb.1 hGu) hr hB
  obtain ⟨w, -, hmin, hcont⟩ := EllipticBernoulli.IsObstacleMinimizer.exists_continuousOn hU
    ⟨K, hK⟩ hQpos hQb hu hu0 hB hr (Or.inl rfl) hmin₀
  refine ⟨w, Gw, memH1Loc_iff_eb.2 hmin.1, hcont, hmin.2.1, fun y hy ↦ hmin.2.2.1 y hy,
    fun v Gv hv h₁ h₂ ↦ ?_⟩
  rw [energyJ_eq_eb, energyJ_eq_eb]
  exact hmin.2.2.2 v Gv (memH1Loc_iff_eb.1 hv) h₁ h₂

/-- **Constraint `w ≥ u`, with continuity on all of `U`.** As `obstacle_above_exists`, with
`ContinuousOn w U`
in place of `ContinuousOn w (ball x₀ r)`. -/
theorem obstacle_above_exists_continuousOn {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    (hGu : MemH1Loc U u Gu) {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc U w Gw ∧ ContinuousOn w U ∧
      (∀ y ∈ U \ ball x₀ r, w y = u y) ∧ (∀ y ∈ U, u y ≤ w y) ∧
      ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
        (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
        energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv := by
  obtain ⟨K, hK⟩ := hQ
  obtain ⟨w₀, Gw, hmin₀⟩ := EllipticBernoulli.exists_obstacle_above hU hK.continuousOn
    (exists_abs_le hQpos hQb) (memH1Loc_iff_eb.1 hGu) hr hB
  obtain ⟨w, -, hmin, hcont⟩ := EllipticBernoulli.IsObstacleMinimizer.exists_continuousOn hU
    ⟨K, hK⟩ hQpos hQb hu hu0 hB hr (Or.inr rfl) hmin₀
  refine ⟨w, Gw, memH1Loc_iff_eb.2 hmin.1, hcont, hmin.2.1, fun y hy ↦ hmin.2.2.1 y hy,
    fun v Gv hv h₁ h₂ ↦ ?_⟩
  rw [energyJ_eq_eb, energyJ_eq_eb]
  exact hmin.2.2.2 v Gv (memH1Loc_iff_eb.1 hv) h₁ h₂

/-- Existence of a minimizer of the obstacle problem with constraint `0 ≤ w ≤ u`
(`Registry.obstacle_below_exists`). -/
theorem obstacle_below_exists {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d} (hU : IsOpen U)
    (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    (hGu : MemH1Loc U u Gu) {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc U w Gw ∧ ContinuousOn w (ball x₀ r) ∧
      (∀ y ∈ U \ ball x₀ r, w y = u y) ∧ (∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y) ∧
      ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
        (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
        energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv := by
  obtain ⟨w, Gw, hGw, hcont, h⟩ :=
    obstacle_below_exists_continuousOn hU hQ hQpos hQb hu hu0 hGu hr hB
  exact ⟨w, Gw, hGw, hcont.mono (ball_subset_closedBall.trans hB), h⟩

/-- Existence of a minimizer of the obstacle problem with constraint `w ≥ u`
(`Registry.obstacle_above_exists`). -/
theorem obstacle_above_exists {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d} (hU : IsOpen U)
    (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    (hGu : MemH1Loc U u Gu) {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc U w Gw ∧ ContinuousOn w (ball x₀ r) ∧
      (∀ y ∈ U \ ball x₀ r, w y = u y) ∧ (∀ y ∈ U, u y ≤ w y) ∧
      ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
        (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
        energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv := by
  obtain ⟨w, Gw, hGw, hcont, h⟩ :=
    obstacle_above_exists_continuousOn hU hQ hQpos hQb hu hu0 hGu hr hB
  exact ⟨w, Gw, hGw, hcont.mono (ball_subset_closedBall.trans hB), h⟩

/-! ### Energy-decreasing perturbations -/

/-- Energy-decreasing perturbation when the supersolution test fails
(`Registry.energy_decrease_of_not_super`). -/
theorem energy_decrease_of_not_super {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (htouch : φ x₀ = w x₀ ∧ ∀ᶠ y in 𝓝[≠] x₀, φ y < w y)
    (hfail : 0 < Δ φ x₀ ∧ (φ x₀ = 0 → Q x₀ < ‖∇ φ x₀‖)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, w y ≤ w' y ∧ w' y ≤ max (w y) (φ y + η)) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  intro ρ hρ hρB η hη
  obtain ⟨w', Gw', hGw', h⟩ := EllipticBernoulli.energy_decrease_of_not_super hU hQ hQpos hQb hw
    hw0 (memH1Loc_iff_eb.1 hGw) hB (compactlyContained_iff_eb.1 hBU) hφ hx₀ htouch hfail ρ hρ
    hρB η hη
  exact ⟨w', Gw', memH1Loc_iff_eb.2 hGw', h⟩

/-- Energy-decreasing perturbation when the subsolution test fails
(`Registry.energy_decrease_of_not_sub`). -/
theorem energy_decrease_of_not_sub {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (hx₀pos : x₀ ∈ closure (posSet w U))
    (htouch : max (φ x₀) 0 = w x₀ ∧
      ∀ᶠ y in 𝓝[(closure (posSet w U) ∩ U) \ {x₀}] x₀, w y < max (φ y) 0)
    (hfail : Δ φ x₀ < 0 ∧ (φ x₀ = 0 → ‖∇ φ x₀‖ < Q x₀)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, min (w y) (max (φ y - η) 0) ≤ w' y ∧ w' y ≤ w y) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  intro ρ hρ hρB η hη
  rw [posSet_eq_eb] at hx₀pos htouch
  obtain ⟨w', Gw', hGw', h⟩ := EllipticBernoulli.energy_decrease_of_not_sub hU hQ hQpos hQb hw
    hw0 (memH1Loc_iff_eb.1 hGw) hB (compactlyContained_iff_eb.1 hBU) hφ hx₀ hx₀pos htouch hfail
    ρ hρ hρB η hη
  exact ⟨w', Gw', memH1Loc_iff_eb.2 hGw', h⟩

/-! ### Interior Lipschitz estimate -/

/-- Interior Lipschitz estimate (`Registry.locallyLipschitzOn_of_isViscSolution`). The theorem of
elliptic-bernoulli-foundations needs only `U` open
and `Q` continuous on `U` (`Setting` fields `isOpen` and `lip`). -/
theorem locallyLipschitzOn_of_isViscSolution (S : Setting d) {u : E d → ℝ}
    (hu : IsViscSolution S.U S.Q u) : LocallyLipschitzOn S.U u :=
  EllipticBernoulli.locallyLipschitzOn_of_isViscSolution (isOpen_of_setting S)
    (continuousOn_of_setting S) (isViscSolution_iff_eb.1 hu)

/-! ### Planar classification of homogeneous global solutions -/

/-- Planar classification of 1-homogeneous global inner variational solutions
(`Registry.classification_homogeneous_planar`). -/
theorem classification_homogeneous_planar {q : ℝ} (hq : 0 < q) {v χ : E 2 → ℝ}
    (h : IsInnerVarSolution univ (fun _ ↦ q) v χ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ y : E 2, v (t • y) = t * v y) :
    ∃ e : E 2, ‖e‖ = 1 ∧
      (((∀ y, v y = q * max (inner ℝ y e) 0) ∧
          ∀ᵐ y, χ y = {z : E 2 | 0 < inner ℝ z e}.indicator 1 y) ∨
        (∃ α : ℝ, 0 ≤ α ∧ (∀ y, v y = α * |inner ℝ y e|) ∧ ∀ᵐ y, χ y = 1) ∨
        ((∀ y, v y = 0) ∧ ∀ᵐ y, χ y = 0)) :=
  EllipticBernoulli.classification_homogeneous_planar hq h.toEB hhom

/-! ### Flatness implies classical near a free boundary point -/

/-- Flat free boundaries are classical (`Registry.isClassicalNear_of_flat`). This is
`EllipticBernoulli.isClassicalNear_of_flat : FlatClassicalStatement` of
elliptic-bernoulli-foundations v0.1.0, which proves D. De Silva, *Free boundary regularity for a
problem with right hand side*, Interfaces Free Bound. 13 (2011), no. 2, 223–238,
doi:10.4171/IFB/255, Thm 1.1, together with the passage from a `C^{1,γ}` free boundary to a
classical solution. It is applied with the `Setting` fields `two_le`, `isOpen`, `lip`, `Qmin_pos`
and `Q_mem` (restricted from `closure U` to `U`). -/
theorem isClassicalNear_of_flat (S : Setting d) :
    ∃ εbar > 0, ∀ (u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsViscSolution S.U S.Q u →
      x₀ ∈ freeBoundary u S.U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ S.U →
      (∀ y ∈ ball x₀ r, S.Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ S.Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsClassicalNear S.U S.Q u x₀ := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_of_setting S
  obtain ⟨εbar, hε, H⟩ :=
    EllipticBernoulli.isClassicalNear_of_flat S.two_le K S.Qmin S.Qmax S.Qmin_pos
  exact ⟨εbar, hε, fun u x₀ e r hu hx₀ he hr hrε hB hflat ↦
    isClassicalNear_iff_eb.2 (H S.U S.Q u x₀ e r (isOpen_of_setting S) hK (Q_mem_of_setting S)
      (isViscSolution_iff_eb.1 hu) ((freeBoundary_eq_eb u S.U) ▸ hx₀) he hr hrε hB hflat)⟩

end Foundations

end PerronVariational

end
