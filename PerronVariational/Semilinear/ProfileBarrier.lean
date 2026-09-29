/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Registry.Semilinear
public import PerronVariational.Semilinear.Profiles
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Monotone

/-!
# Subsolutions from the sub-profile (parabolic version of Lemma A.4(iii))

If `W` is a classical subsolution of the heat equation, `∂ₜW - ΔW ≤ 0`, whose spatial gradient
satisfies `Q² ≤ θ |∇W|²` wherever `ε s₀ < W < ε` (the transition layer of the profile), then
`(Φ_{ε,θ}(W))₊` is a viscosity subsolution of `∂ₜu = Δu - Q² β_ε(u)`. This is the computation
(A.6) in the proof of Lemma A.4 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, for
time-dependent `W`:
`(∂ₜ - Δ)Φ(W) = Φ'(W)(∂ₜ - Δ)W - Φ''(W)|∇W|² ≤ -θ β_ε(Φ(W)) |∇W|² ≤ -Q² β_ε(Φ(W))`,
using `Φ_ε'' = θ β_ε(Φ_ε)` (Lemma A.2(i)).

Used for the lower barriers of the attainment estimate (Proposition A.8, Lemma A.9).
-/

open Set Filter Topology
open scoped Gradient Laplacian ContDiff

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- **Parabolic sub-profile barrier.** See the module docstring. -/
theorem isSemilinearViscSubOn_max_profileSubEps {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {θ ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) {I : Set ℝ}
    {W : E d × ℝ → ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hWc : ContinuousOn W (U ×ˢ I)) (hWx : ∀ t, ContDiff ℝ 2 (fun y ↦ W (y, t)))
    (hWt : ∀ x t, DifferentiableAt ℝ (fun s ↦ W (x, s)) t)
    (hheat : ∀ p ∈ U ×ˢ I, dₜ W p - lapₓ W p ≤ 0)
    (hgrad : ∀ p ∈ U ×ˢ I, ε * profileSubZero β θ < W p → W p < ε →
      Q p.1 ^ 2 ≤ θ * ‖gradₓ W p‖ ^ 2) :
    IsSemilinearViscSubOn U Q β ε I (fun p ↦ max (profileSubEps β θ ε (W p)) 0) := by
  set Φ := profileSubEps β θ ε with hΦ
  have hΦc : ContDiff ℝ ∞ Φ := profileSubEps_contDiff hβ hθ hθ1
  refine ⟨ContinuousOn.sup (hΦc.continuous.comp_continuousOn hWc) continuousOn_const, ?_⟩
  intro ψ hψ p hp htouch
  obtain ⟨x, t⟩ := p
  obtain ⟨-, hpeq, hev⟩ := htouch
  simp only at hpeq
  by_cases hpos : 0 ≤ Φ (W (x, t))
  · -- the touching is also a touching of `Φ ∘ W`
    rw [max_eq_left hpos] at hpeq
    have hev' : ∀ᶠ q in 𝓝[(U ×ˢ I) ∩ {q | q.2 ≤ (x, t).2}] (x, t), Φ (W q) ≤ ψ q :=
      hev.mono fun q hq ↦ (le_max_left _ _).trans hq
    -- space
    have hslice : ContDiff ℝ 2 (fun y ↦ Φ (W (y, t))) :=
      (hΦc.of_le (WithTop.coe_le_coe.2 le_top)).comp (hWx t)
    have hlap : Δ (fun y ↦ Φ (W (y, t))) x ≤ lapₓ ψ (x, t) := by
      have hsl := eventually_slice_of_parabolicPast (U := U) hp.2 hev'
      rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hp.1)] at hsl
      exact laplacian_le_of_eventually_le hslice.contDiffAt
        (contDiff_spaceSlice_two hψ t).contDiffAt hpeq.symm hsl
    have hcomp := laplacian_comp (f := Φ) (g := fun y ↦ W (y, t)) (x := x)
      (hΦc.of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt (hWx t).contDiffAt
    rw [hcomp, profileSubEps_deriv_deriv hβ hθ hθ1 hε] at hlap
    -- time
    have hΦd : HasDerivAt (fun s ↦ Φ (W (x, s))) (deriv Φ (W (x, t)) * dₜ W (x, t)) t :=
      ((hΦc.differentiable (by simp)) _).hasDerivAt.comp t (hWt x t).hasDerivAt
    have hdt : dₜ ψ (x, t) ≤ deriv Φ (W (x, t)) * dₜ W (x, t) := by
      have h := deriv_nonpos_of_eventually_le_left
        ((differentiableAt_timeLine hψ x t).sub hΦd.differentiableAt)
        ((eventually_time_of_parabolicPast hp.1 (hI t hp.2) hev').mono fun s hs ↦ by
          simp only [Pi.sub_apply] at hs ⊢; rw [hpeq]; linarith)
      rw [deriv_sub (differentiableAt_timeLine hψ x t) hΦd.differentiableAt, hΦd.deriv] at h
      simp only [dₜ] at h ⊢; linarith
    -- combine
    have hΦ1 := (profileSubEps_deriv_mem hβ hθ hθ1 hε (W (x, t))).1
    have hheat' := hheat (x, t) hp
    have hB0 := hβ.betaEps_nonneg ε (Φ (W (x, t))) hε.le
    have key : Q x ^ 2 * betaEps β ε (Φ (W (x, t))) ≤
        θ * betaEps β ε (Φ (W (x, t))) * ‖gradₓ W (x, t)‖ ^ 2 := by
      rcases hB0.eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · obtain ⟨h1, h2⟩ := mem_of_betaEps_profileSubEps_pos hβ hθ hθ1 hε h0
        have := hgrad (x, t) hp h1 h2
        calc Q x ^ 2 * betaEps β ε (Φ (W (x, t))) ≤
              θ * ‖gradₓ W (x, t)‖ ^ 2 * betaEps β ε (Φ (W (x, t))) :=
            mul_le_mul_of_nonneg_right this h0.le
          _ = _ := by ring
    have hmul : deriv Φ (W (x, t)) * (dₜ W (x, t) - lapₓ W (x, t)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hΦ1.le hheat'
    simp only [max_eq_left hpos]
    change dₜ ψ (x, t) - lapₓ ψ (x, t) ≤ _
    simp only [lapₓ, gradₓ, dₜ] at hlap hmul key hdt ⊢
    nlinarith
  · -- the touching point lies in the zero phase: `ψ` has a one-sided minimum there
    push Not at hpos
    have hmax : max (Φ (W (x, t))) 0 = 0 := max_eq_right hpos.le
    rw [hmax] at hpeq
    have hev' : ∀ᶠ q in 𝓝[(U ×ˢ I) ∩ {q | q.2 ≤ (x, t).2}] (x, t), 0 ≤ ψ q :=
      hev.mono fun q hq ↦ (le_max_right _ _).trans hq
    have hlap : 0 ≤ lapₓ ψ (x, t) := by
      have hsl := eventually_slice_of_parabolicPast (U := U) hp.2 hev'
      rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hp.1)] at hsl
      refine laplacian_nonneg_of_isLocalMin ?_ (contDiff_spaceSlice_two hψ t).contDiffAt
      filter_upwards [hsl] with y hy
      simp only [hpeq]; exact hy
    have hdt : dₜ ψ (x, t) ≤ 0 :=
      deriv_nonpos_of_eventually_le_left (differentiableAt_timeLine hψ x t)
        ((eventually_time_of_parabolicPast hp.1 (hI t hp.2) hev').mono fun s hs ↦ by
          simp only at hs ⊢; rw [hpeq]; exact hs)
    simp only [hmax, hβ.betaEps_zero, mul_zero, neg_zero]
    linarith

end PerronVariational

end
