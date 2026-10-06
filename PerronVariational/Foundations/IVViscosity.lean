/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolutionQ
public import PerronVariational.Defs.Stationary
import PerronVariational.Semilinear.Calculus
import PerronVariational.Stationary.Perron
import PerronVariational.Stationary.ViscosityJet

/-!
# Viscosity solutions of bernoulli-rectifiability are viscosity solutions in the sense of Def 2.1

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper").
`InnerVariational.IsViscositySolutionQ W Q u` of the dependency bernoulli-rectifiability v0.2.0 asks
for harmonicity in `{u > 0}` and for the two free boundary conditions `|∇φ(x)| ≤ Q(x)` (touching
from below) and `|∇φ(x)| ≥ Q(x)` (touching `φ₊` from above) at free boundary points, with touching
on a ball in `W`. Def 2.1 of the paper (`IsViscSolution W Q u`) is phrased with touching on a
relative neighbourhood (in `W` for supersolutions, in `\overline{{u > 0}} ∩ W` for subsolutions) and
a disjunction "`Δφ(x) ≤ 0`, or `φ(x) = 0` and the gradient condition".

* Supersolution: at `u(x) > 0`, `Δφ(x) ≤ Δu(x) = 0`. At a free boundary point, the condition of
  bernoulli-rectifiability. At a zero of `u` off the free boundary, `u ≡ 0` near `x`, so `x` is a
  local maximum of `φ` and `Δφ(x) ≤ 0`.
* Subsolution: at `u(x) > 0`, `\overline{{u > 0}} ∩ W` is a neighbourhood of `x` and
  `Δφ(x) ≥ Δu(x) = 0`. At `u(x) = 0` the point lies on the free boundary, `φ(x) = 0` (otherwise
  `u ≡ 0` near `x` on `\overline{{u > 0}}`), and `u ≤ φ₊` holds on a whole ball because `u = 0` off
  `\overline{{u > 0}}`; then the condition of bernoulli-rectifiability applies.

Main result: `isViscSolution_of_isViscositySolutionQ`.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

namespace Foundations

variable {d : ℕ}

/-- **Supersolution half** of `isViscSolution_of_isViscositySolutionQ`. -/
theorem isViscSuper_of_isViscositySolutionQ {W : Set (E d)} {Q u : E d → ℝ} (hW : IsOpen W)
    (h : InnerVariational.IsViscositySolutionQ W Q u) : IsViscSuper W Q u := by
  refine ⟨h.continuousOn, h.nonneg, fun φ hφ x hx ht ↦ ?_⟩
  have hle := ht.eventually_le_of_isOpen hW
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_of_smooth hφ
  rcases (h.nonneg x hx).lt_or_eq with hpos | hzero
  · left
    have harm := h.harmonicAt x hx hpos
    have := laplacian_le_of_eventually_le hφ2.contDiffAt harm.1 ht.2.1 hle
    have h0 : Δ u x = 0 := harm.2.self_of_nhds
    linarith
  · have hφx : φ x = 0 := ht.2.1.trans hzero.symm
    by_cases hfr : x ∈ frontier {y | 0 < u y}
    · right
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hle.and (hW.mem_nhds hx))
      exact ⟨hφx, h.norm_gradient_le x ⟨hx, hfr⟩ r hr (fun y hy ↦ (hball y hy).2) φ hφ hφx
        fun y hy ↦ (hball y hy).1⟩
    · left
      have hncl : x ∉ closure {y | 0 < u y} := fun hcl ↦
        hfr ⟨hcl, fun hint ↦ by
          have : x ∈ {y | 0 < u y} := interior_subset hint; linarith [this.out]⟩
      have hev : ∀ᶠ y in 𝓝 x, y ∉ {y | 0 < u y} :=
        Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hncl)
          fun y hy hy' ↦ hy (subset_closure hy')
      refine IsLocalMax.laplacian_nonpos hφ2 ?_
      filter_upwards [hle, hev] with y hy hy'
      rw [hφx]
      exact hy.trans (not_lt.1 hy')

/-- **Subsolution half** of `isViscSolution_of_isViscositySolutionQ`. -/
theorem isViscSub_of_isViscositySolutionQ {W : Set (E d)} {Q u : E d → ℝ} (hW : IsOpen W)
    (h : InnerVariational.IsViscositySolutionQ W Q u) : IsViscSub W Q u := by
  refine ⟨h.continuousOn, h.nonneg, fun φ hφ x ht ↦ ?_⟩
  obtain ⟨⟨hxcl, hxW⟩, hval, hev⟩ := ht
  beta_reduce at hval hev
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_of_smooth hφ
  have hposS : posSet u W ⊆ closure (posSet u W) ∩ W := fun y hy ↦ ⟨subset_closure hy, hy.1⟩
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhdsWithin_iff.1 hev
  rcases (h.nonneg x hxW).lt_or_eq with hpos | hzero
  · left
    have harm := h.harmonicAt x hxW hpos
    have hφx : φ x = u x := by
      rcases le_total (φ x) 0 with hφ0 | hφ0
      · rw [max_eq_right hφ0] at hval; linarith
      · rwa [max_eq_left hφ0] at hval
    have hposN : ∀ᶠ y in 𝓝 x, 0 < u y :=
      (h.continuousOn.continuousAt (hW.mem_nhds hxW)).eventually (lt_mem_nhds hpos)
    have hφN : ∀ᶠ y in 𝓝 x, 0 < φ y :=
      hφ.continuous.continuousAt.eventually (lt_mem_nhds (hφx ▸ hpos))
    have hle : ∀ᶠ y in 𝓝 x, u y ≤ φ y := by
      filter_upwards [hposN, hφN, hW.mem_nhds hxW, ball_mem_nhds x hε] with y hy hφy hyW hyε
      have := hεS ⟨hyε, hposS ⟨hyW, hy⟩⟩
      rwa [Set.mem_ofPred_eq, max_eq_left hφy.le] at this
    have := laplacian_le_of_eventually_le harm.1 hφ2.contDiffAt hφx.symm hle
    have h0 : Δ u x = 0 := harm.2.self_of_nhds
    linarith
  · right
    have hux : u x = 0 := hzero.symm
    have hφle : φ x ≤ 0 := by
      have := le_max_left (φ x) 0
      rw [hval, hux] at this
      exact this
    have hφx : φ x = 0 := by
      refine le_antisymm hφle (not_lt.1 fun hneg ↦ ?_)
      obtain ⟨ε', hε', hε'φ⟩ := Metric.eventually_nhds_iff_ball.1
        (hφ.continuous.continuousAt.eventually (gt_mem_nhds hneg))
      obtain ⟨b, hb, hxb⟩ := Metric.mem_closure_iff.1 hxcl (min ε ε') (lt_min hε hε')
      have hbx : b ∈ ball x (min ε ε') := by rw [mem_ball, dist_comm]; exact hxb
      have hb1 := hεS ⟨ball_subset_ball (min_le_left _ _) hbx, hposS hb⟩
      have hb2 := hε'φ b (ball_subset_ball (min_le_right _ _) hbx)
      rw [Set.mem_ofPred_eq, max_eq_right hb2.le] at hb1
      exact absurd hb.2 (not_lt.2 hb1)
    have hfr : x ∈ frontier {y | 0 < u y} :=
      ⟨closure_mono (fun y hy ↦ hy.2) hxcl, fun hint ↦ by
        have : x ∈ {y | 0 < u y} := interior_subset hint; linarith [this.out]⟩
    obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW x hxW
    refine ⟨hφx, h.one_le_norm_gradient x ⟨hxW, hfr⟩ (min ε ρ) (lt_min hε hρ)
      ((ball_subset_ball (min_le_right _ _)).trans hρW) φ hφ hφx fun y hy ↦ ?_⟩
    have hyW : y ∈ W := hρW (ball_subset_ball (min_le_right _ _) hy)
    by_cases hycl : y ∈ closure (posSet u W)
    · exact hεS ⟨ball_subset_ball (min_le_left _ _) hy, hycl, hyW⟩
    · have : ¬ 0 < u y := fun hy' ↦ hycl (subset_closure ⟨hyW, hy'⟩)
      exact (not_lt.1 this).trans (le_max_right _ _)

/-- A viscosity solution in the sense of bernoulli-rectifiability (`IsViscositySolutionQ`) on an
open set `W` is a viscosity solution in the sense of Def 2.1 (`IsViscSolution`). -/
theorem isViscSolution_of_isViscositySolutionQ {W : Set (E d)} {Q u : E d → ℝ} (hW : IsOpen W)
    (h : InnerVariational.IsViscositySolutionQ W Q u) : IsViscSolution W Q u :=
  ⟨isViscSuper_of_isViscositySolutionQ hW h, isViscSub_of_isViscositySolutionQ hW h⟩

end Foundations

end PerronVariational

end
