/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary

/-!
# The necklace example ([Figure 1](#AFS:f.necklace)): statement

The configuration of [Figure 1](#AFS:f.necklace) (`f.necklace`) of F. Abedin, W. M. Feldman, K.
Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`): the smallest supersolution, the energy minimizer and the largest
subsolution with the same boundary data are pairwise distinct.

The construction (in `ℝ²`, `Q ≡ 1`): a ring ("necklace") of `N = 100` holes of radius `1/20`,
centred on the circle of radius `R = (1/10) / sin (π / 100)`, inside the disc `B₄(0)`. The data
on the hole circles are chosen so that the radial solutions issuing from neighbouring holes have
free boundaries `∂B_{1/10}(z_k)` (kissing radius `1/10`) that just touch. The parameters differ
from those of the (numerical) [Figure 1](#AFS:f.necklace), which shows `18` unit discs on the circle
of radius `24` and no outer circle: the energy comparison used to separate `u_max` from the
minimizer needs `N ≳ 40` holes, and the outer circle makes the domain bounded. The proof is
`Necklace.necklace_example` in `Examples/Necklace/Main.lean`.

* `MemH10 U w`: `w ∈ H¹₀(U)`, encoded as: the extension of `w` by zero is in `H¹(ℝᵈ)`.
* `IsDirichletEnergyMinimizer U Q g u`: `u` minimizes the Alt–Caffarelli energy `J_Q(·; U)`
  among `v ∈ H¹(U)` with `v - g ∈ H¹₀(U)`.
* `NecklaceExampleStatement`: the claim.
-/

open Set Filter Topology Metric MeasureTheory

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- `w ∈ H¹₀(U)`, encoded as: the extension of `w` by zero lies in `H¹(ℝᵈ)`. For domains with
continuous (in particular `C²`) boundary this is the usual space `H¹₀(U)`, the closure of
`C_c^∞(U)` in `H¹(U)`. -/
def MemH10 (U : Set (E d)) (w : E d → ℝ) : Prop :=
  ∃ H : E d → E d, MemH1 univ (U.indicator w) H

/-- `u` is a minimizer of the Alt–Caffarelli energy `J_Q(v; U) = ∫_U |∇v|² + Q² 1_{v > 0}` among
`v ∈ H¹(U)` with boundary values `g` in the trace sense, i.e. `v - g ∈ H¹₀(U)` (`MemH10`). Weak
gradients are carried as data, as in `MemH1`. -/
def IsDirichletEnergyMinimizer (U : Set (E d)) (Q g u : E d → ℝ) : Prop :=
  ∃ Gu : E d → E d, MemH1 U u Gu ∧ MemH10 U (u - g) ∧
    ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1 U v Gv → MemH10 U (v - g) →
      energyJ U Q u Gu ≤ energyJ U Q v Gv

/-- **The necklace example** (`[AFS]`, [Figure 1](#AFS:f.necklace)). In `ℝ²` with `Q ≡ 1` there are
a setting `S` and data `g_sub`, `g_super` such that `g_sub` is a smooth strict subsolution with
`g_sub > 0` on `∂U`, `g_super` is a smooth strict supersolution, `g_sub = g_super` on `∂U`, and,
writing `u_min = perronSmallest U 1 g_sub` and `u_max = perronLargest U 1 g_super`:
1. `u_min` and `u_max` are nontrivial: each is positive somewhere in `U`, vanishes somewhere in
   `U`, and has a nonempty free boundary;
2. `u_min` has a two-plane point: for some `x₀ ∈ ∂{u_min > 0} ∩ U` and some unit vector `e`,
   the blow-ups `(u_min)_{x₀,t}` converge to `y ↦ |⟪y, e⟫|` locally uniformly as `t → 0⁺`, and
   every blow-up limit of `u_min` at `x₀` is `y ↦ |⟪y, e⟫|`;
3. `u_min ≠ u_max` on a subset of `U` of positive measure;
4. a minimizer of `J_1(·; U)` with boundary values `g_sub` exists, and every such minimizer
   differs from `u_min` and from `u_max` on subsets of `U` of positive measure.

The comparisons are almost-everywhere statements because `J` only sees a function up to null
sets. -/
def NecklaceExampleStatement : Prop :=
  ∃ (S : Setting 2) (gsub gsuper : E 2 → ℝ), S.Q = (fun _ ↦ 1) ∧
    IsStrictSub S.U S.Q gsub ∧ (∀ x ∈ frontier S.U, 0 < gsub x) ∧
    IsStrictSuper S.U S.Q gsuper ∧ (∀ x ∈ frontier S.U, gsub x = gsuper x) ∧
    (∃ x ∈ S.U, 0 < perronSmallest S.U S.Q gsub x) ∧
    (∃ x ∈ S.U, perronSmallest S.U S.Q gsub x = 0) ∧
    (freeBoundary (perronSmallest S.U S.Q gsub) S.U).Nonempty ∧
    (∃ x ∈ S.U, 0 < perronLargest S.U S.Q gsuper x) ∧
    (∃ x ∈ S.U, perronLargest S.U S.Q gsuper x = 0) ∧
    (freeBoundary (perronLargest S.U S.Q gsuper) S.U).Nonempty ∧
    (∃ x₀ ∈ freeBoundary (perronSmallest S.U S.Q gsub) S.U, ∃ e : E 2, ‖e‖ = 1 ∧
      TendstoLocallyUniformly (fun t ↦ blowup (perronSmallest S.U S.Q gsub) x₀ t)
        (fun y ↦ |inner ℝ y e|) (𝓝[>] 0) ∧
      ∀ v, IsBlowupLimit (perronSmallest S.U S.Q gsub) x₀ v → ∀ y, v y = |inner ℝ y e|) ∧
    ¬ (perronSmallest S.U S.Q gsub =ᵐ[volume.restrict S.U] perronLargest S.U S.Q gsuper) ∧
    (∃ u, IsDirichletEnergyMinimizer S.U S.Q gsub u) ∧
    ∀ u, IsDirichletEnergyMinimizer S.U S.Q gsub u →
      ¬ (u =ᵐ[volume.restrict S.U] perronSmallest S.U S.Q gsub) ∧
      ¬ (u =ᵐ[volume.restrict S.U] perronLargest S.U S.Q gsuper)

end PerronVariational

end
