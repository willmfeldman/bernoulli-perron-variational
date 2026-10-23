/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.DirichletMinimizer
public import PerronVariational.Examples.Necklace.Largest
import PerronVariational.Main.Final
import PerronVariational.Main.InnerSmallest
import PerronVariational.Inner.LongTime
import PerronVariational.Stationary.DirectionalStable.Blowup
import PerronVariational.Stationary.TwoPlane.Step3

/-!
# Energy minimizers for the necklace example

For the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M. Feldman, K.
Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`), with `u_min = perronSmallest U 1 gSub`, `u_max = perronLargest U 1
gSuper`, and Dirichlet minimizers of `J_1(·; U)` with boundary values `gSub`
(`IsDirichletEnergyMinimizer`):

* `exists_isDirichletEnergyMinimizer_gSub`: a minimizer exists;
* `not_isDirichletEnergyMinimizer_ae_uMin`: no minimizer is a.e. equal to `u_min`. Otherwise
  `u_min` would itself be a minimizer; since `u_min` is continuous and harmonic in its positivity
  set ([AFS, [Theorem 1.1](#AFS:t.main)]), it would be an upward minimizer in `U` ([AFS,
  [Definition 2.15](#AFS:d.directional)]). Its blow-up at the kissing point `m_0` is the two-plane
  solution `|⟪y, e_0⟫|`, which would then be an upward minimizer in `ℝ²` ([AFS,
  [Corollary 2.18](#AFS:c.blow-up-directional)]), contradicting [AFS,
  [Proposition 2.20](#AFS:p.two-plane-minimizing-props)(1)];
* `not_isDirichletEnergyMinimizer_ae_uMax_of_energyJ_lt`: no minimizer is a.e. equal to `u_max`,
  provided some admissible competitor has energy below `|{u_max > 0}|`.
-/

open Set Filter Topology Metric MeasureTheory
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational.Necklace

/-- A minimizer of `J_1(·; U)` with boundary values `gSub` exists. -/
theorem exists_isDirichletEnergyMinimizer_gSub :
    ∃ u, IsDirichletEnergyMinimizer domain (fun _ ↦ 1) gSub u :=
  exists_isDirichletEnergyMinimizer isOpen_domain isBounded_domain measurable_const
    (C := 1) (fun _ ↦ by simp) (contDiff_gSub.of_le (by norm_num))

theorem volume_domain_ne_top : volume domain ≠ ⊤ :=
  isBounded_domain.measure_lt_top.ne

/-- `u_min` is not a Dirichlet minimizer: its two-plane point at `m_0` is excluded by
[AFS, [Corollary 2.18](#AFS:c.blow-up-directional) and
[Proposition 2.20](#AFS:p.two-plane-minimizing-props)(1)]. -/
theorem not_isDirichletEnergyMinimizer_uMin :
    ¬ IsDirichletEnergyMinimizer domain (fun _ ↦ 1) gSub uMin := by
  intro hmin
  obtain ⟨-, ⟨χ, hχ⟩, hcont⟩ := inner_smallest_of parabolic_existence_bdd longtime_innerVar 2
    setting gSub isStrictSub_gSub fun x hx ↦ (gSub_eq_gSuper_of_mem_frontier hx).2
  have hup : IsUpwardMinimizer domain (fun _ ↦ 1) uMin :=
    hmin.isUpwardMinimizer isOpen_domain volume_domain_ne_top (C := 1) (fun _ _ ↦ by simp)
      (isOpen_posSet_of_continuousOn isOpen_domain (hcont.mono subset_closure)) hχ.c2
      hχ.harmonic
  have hb := DirectionalStable.blowup_isUpwardMinimizer' isOpen_domain continuousOn_const
    (Qmax := 1) (fun _ _ ↦ by simp) hχ.locLip (kiss_mem_domain 0) hup (isBlowupLimit_twoPlane 0)
  have heq : (fun y : E 2 ↦ |⟪y, tang 0⟫|) = twoPlane 1 (tang 0) := by
    funext y
    simp [twoPlane]
  rw [heq] at hb
  exact twoPlane_not_upwardMinimizer one_pos (norm_tang 0) 1 hb

/-- **No energy minimizer is a.e. equal to `u_min`.** -/
theorem not_isDirichletEnergyMinimizer_ae_uMin {u : E 2 → ℝ}
    (hmin : IsDirichletEnergyMinimizer domain (fun _ ↦ 1) gSub u) :
    ¬ (u =ᵐ[volume.restrict domain] uMin) := fun h ↦
  not_isDirichletEnergyMinimizer_uMin (hmin.congr_ae isOpen_domain.measurableSet h)

/-- The positivity set of `u_max` is open, in particular measurable. -/
theorem isOpen_posSet_uMax : IsOpen (posSet uMax domain) :=
  isOpen_posSet_of_continuousOn isOpen_domain (mainLargest.2.mono subset_closure)

/-- **No energy minimizer is a.e. equal to `u_max`**, given an admissible competitor `v` with
`J_1(v; U) < |{u_max > 0}|`. -/
theorem not_isDirichletEnergyMinimizer_ae_uMax_of_energyJ_lt {u v : E 2 → ℝ} {Gv : E 2 → E 2}
    (hmin : IsDirichletEnergyMinimizer domain (fun _ ↦ 1) gSub u) (hv : MemH1 domain v Gv)
    (hvg : MemH10 domain (v - gSub))
    (hlt : energyJ domain (fun _ ↦ 1) v Gv < volume (posSet uMax domain)) :
    ¬ (u =ᵐ[volume.restrict domain] uMax) :=
  hmin.not_ae_eq_of_energyJ_lt isOpen_domain isOpen_posSet_uMax.measurableSet hv hvg hlt

end PerronVariational.Necklace

end
