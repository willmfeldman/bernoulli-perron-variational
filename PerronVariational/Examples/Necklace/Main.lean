/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.Statement
public import PerronVariational.Examples.Necklace.Energy
public import PerronVariational.Examples.Necklace.Minimizer

/-!
# The necklace example ([Figure 1](#AFS:f.necklace))

The configuration of [Figure 1](#AFS:f.necklace) (`f.necklace`) of F. Abedin, W. M. Feldman, K.
Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`): `necklace_example : NecklaceExampleStatement`.

**What is proved.** In `ℝ²` with `Q ≡ 1`, on the domain `U = B₄(0) \ ⋃_k B̄_{1/20}(z_k)`, with
`N = 100` holes centred at the points `z_k` of the circle of radius `R = (1/10) / sin (π/100)`,
there are smooth data `gSub` (a strict subsolution, positive on `∂U`) and `gSuper` (a strict
supersolution) with `gSub = gSuper` on `∂U`, such that `u_min = perronSmallest U 1 gSub`,
`u_max = perronLargest U 1 gSuper` and every minimizer of the Alt–Caffarelli energy
`J_1(·; U)` with boundary values `gSub` are pairwise distinct (as elements of `L¹_loc(U)`,
i.e. up to null sets); `u_min` and `u_max` are nontrivial (positive somewhere, zero somewhere,
nonempty free boundary), `u_min` has a two-plane point, and a minimizer exists.

**Parameters.** [Figure 1](#AFS:f.necklace) of `[AFS]` is numerical, drawn with `18` unit discs on
the circle of radius `24`. Here there are `N = 100` holes of radius `1/20`; the radial solutions
from the holes have free boundaries `∂B_{1/10}(z_k)` (kissing radius `1/10`) that touch their
neighbours at the kissing points `m_k`; and an outer circle of radius `4` makes the domain bounded.
The reason is step 3 below: the comparison of the energy of an explicit competitor (of order `N`)
with the area of the inner disc of the necklace (of order `N²`) needs `N ≳ 40`. With the figure's
numbers the competitor has energy about `1187π`, while the inner disc has area about `541π`.

**Proof outline.**
1. `u_min` coincides with the explicit radial solutions near the necklace (`Lower.lean`,
   `Upper.lean`), so each kissing point `m_k` is a two-plane point (`TwoPlane.lean`). A Dirichlet
   minimizer a.e. equal to `u_min` would make `u_min` an upward minimizer
   ([AFS, [Definition 2.15](#AFS:d.directional)]), and its blow-up `|⟪y, e⟫|` would be one too
   ([AFS, [Corollary 2.18](#AFS:c.blow-up-directional)]), contradicting [AFS,
   [Proposition 2.20](#AFS:p.two-plane-minimizing-props)(1)] (`Minimizer.lean`).
2. `u_max` is positive on the whole inner disc `B_{ρ_in}(0) ∩ U` of the necklace
   (`Largest.lean`, via [AFS, [Corollary 1.2(ii)](#AFS:part.largest-reg)] at the kissing points),
   while `u_min = 0` near `0`; so `u_min ≠ u_max` on a set of positive measure.
3. The competitor `vSup` (the radial pieces near the holes and the outer circle, zero elsewhere)
   has `J_1(vSup; U) ≤ (107/20)π`, while `|{u_max > 0} ∩ U| ≥ (97/10)π` and
   `J_1(u; U) ≥ |{u > 0} ∩ U|`; so no minimizer is a.e. equal to `u_max` (`Energy.lean`).
4. A minimizer exists by the obstacle-problem existence theorem (`DirichletMinimizer.lean`).
-/

open Set Filter Topology Metric MeasureTheory
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational.Necklace

/-- No minimizer of `J_1(·; U)` with boundary values `gSub` is a.e. equal to `u_max`: the
competitor `vSup` has less energy than the measure of `{u_max > 0} ∩ U`. -/
theorem not_isDirichletEnergyMinimizer_ae_uMax {u : E 2 → ℝ}
    (hmin : IsDirichletEnergyMinimizer domain (fun _ ↦ 1) gSub u) :
    ¬ (u =ᵐ[volume.restrict domain] uMax) :=
  not_isDirichletEnergyMinimizer_ae_uMax_of_energyJ_lt hmin vSup_admissible.1 vSup_admissible.2
    (energyJ_vSup_lt_volume_posSet (Filter.EventuallyEq.refl _ _))

/-- **The necklace example** (`[AFS]`, [Figure 1](#AFS:f.necklace)): the smallest supersolution, the
largest subsolution and every energy minimizer with the same boundary data are pairwise distinct. -/
theorem necklace_example : NecklaceExampleStatement := by
  refine ⟨setting, gSub, gSuper, rfl, isStrictSub_gSub,
    fun x hx ↦ (gSub_eq_gSuper_of_mem_frontier hx).2, isStrictSuper_gSuper,
    fun x hx ↦ (gSub_eq_gSuper_of_mem_frontier hx).1, exists_perronSmallest_pos,
    ⟨0, zero_mem_domain, perronSmallest_zero⟩, ⟨kiss 0, kiss_mem_freeBoundary 0⟩,
    exists_perronLargest_pos, exists_perronLargest_eq_zero, freeBoundary_perronLargest_nonempty,
    ⟨kiss 0, kiss_mem_freeBoundary 0, tang 0, norm_tang 0, tendstoLocallyUniformly_blowup 0,
      fun v hv y ↦ isBlowupLimit_eq 0 hv y⟩,
    not_uMin_ae_eq_uMax, exists_isDirichletEnergyMinimizer_gSub, fun u hu ↦ ⟨?_, ?_⟩⟩
  · exact not_isDirichletEnergyMinimizer_ae_uMin hu
  · exact not_isDirichletEnergyMinimizer_ae_uMax hu

end PerronVariational.Necklace

end
