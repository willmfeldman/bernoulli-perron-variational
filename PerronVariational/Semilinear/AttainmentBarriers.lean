/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.Profiles
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Registry.Comparison
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.ExteriorBall
import PerronVariational.Semilinear.Monotone
import PerronVariational.Semilinear.PositivityTrace
import PerronVariational.Semilinear.ProfileBarrier

/-!
# Barriers for the attainment estimate (Proposition A.8)

Barriers for the proof of Lemma A.9 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.5).

Tools for the uniform modulus of continuity of Proposition A.8, all uniform in `ε ∈ (0, 1]`:

* `max_profileSubEps_le`, `le_max_profileSubEps`: `w ≤ Φ_ε(w)₊ ≤ (w + c_θ ε)₊`;
* `IsSemilinearSolution.le_of_profileBarrier`: the lower barrier `(Φ_{ε,θ}(W))₊`
  (`isSemilinearViscSubOn_max_profileSubEps`) compared with a solution on a finite horizon;
* `IsSemilinearSolution.shift`: the time translate `u(·, · + s)` solves (3.4) with data `u(·, s)`;
* `IsSemilinearSolution.le_add_of_quadratic`: the caloric upper barrier
  `g(y) + σ + A|x - y|² + 2dAt`;
* `Setting.exists_exteriorBarrier`: a smooth strictly superharmonic barrier `η` at every
  boundary point, with `c|x - x₀|² ≤ η ≤ C|x - x₀|` and `|∇η| ≥ G` on `Ū` (from the uniform
  exterior ball, (A.12)).
-/

open Set Filter Topology Metric
open scoped NNReal Gradient Laplacian ContDiff

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### The sub-profile between `w` and `(w + c_θ ε)₊` -/

section ProfileBounds

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
include hβ hθ hθ1

/-- `Φ_{1,θ}(s)₊ ≤ (s + c_θ)₊`. -/
theorem max_profileSub_le (s : ℝ) : max (profileSub β θ s) 0 ≤ max (s + subConst θ) 0 := by
  have hs₀ := profileSubZero_mem hβ hθ hθ1
  rcases le_or_gt (profileSubZero β θ) s with hs | hs
  · have h1 := profileSub_sub_antitone hβ hθ hθ1 hs
    simp only [profileSub_profileSubZero hβ hθ hθ1] at h1
    exact max_le_max (by linarith [hs₀.1]) le_rfl
  · have : profileSub β θ s ≤ 0 := (profileSub_nonpos_iff hβ hθ hθ1 s).2 hs.le
    rw [max_eq_right this]
    exact le_max_right _ _

/-- `Φ_{ε,θ}(w)₊ ≤ (w + c_θ ε)₊`. -/
theorem max_profileSubEps_le {ε : ℝ} (hε : 0 < ε) (w : ℝ) :
    max (profileSubEps β θ ε w) 0 ≤ max (w + subConst θ * ε) 0 := by
  have h := max_profileSub_le hβ hθ hθ1 (w / ε)
  have e1 : max (profileSubEps β θ ε w) 0 = ε * max (profileSub β θ (w / ε)) 0 := by
    rw [profileSubEps, mul_max_of_nonneg _ _ hε.le, mul_zero]
  have e2 : max (w + subConst θ * ε) 0 = ε * max (w / ε + subConst θ) 0 := by
    rw [mul_max_of_nonneg _ _ hε.le, mul_zero, mul_add, mul_div_cancel₀ _ hε.ne', mul_comm ε]
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h hε.le

/-- `w ≤ Φ_{ε,θ}(w)₊`. -/
theorem le_max_profileSubEps {ε : ℝ} (hε : 0 < ε) (w : ℝ) :
    w ≤ max (profileSubEps β θ ε w) 0 := by
  refine le_trans ?_ (le_max_left _ _)
  have := self_le_profileSub hβ hθ hθ1 (w / ε)
  rw [profileSubEps]
  calc w = ε * (w / ε) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left this hε.le

end ProfileBounds

/-! ### Affine images -/

section Affine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `Δ (a + b η) = b Δη`. -/
theorem laplacian_const_add_mul {η : F → ℝ} {x : F} (hη : ContDiffAt ℝ 2 η x) (a b : ℝ) :
    Δ (fun y ↦ a + b * η y) x = b * Δ η x := by
  have h := laplacian_comp (f := fun z ↦ a + b * z) (g := η) (x := x) (by fun_prop) hη
  have hd : deriv (fun z : ℝ ↦ a + b * z) = fun _ ↦ b := by
    funext z
    simp
  simp only [hd, deriv_const', zero_mul, zero_add] at h
  exact h

/-- `|∇(a + b η)| = |b| |∇η|`. -/
theorem norm_gradient_const_add_mul {η : F → ℝ} {x : F} (hη : DifferentiableAt ℝ η x)
    (a b : ℝ) : ‖∇ (fun y ↦ a + b * η y) x‖ = |b| * ‖∇ η x‖ := by
  rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv, fderiv_const_add,
    fderiv_const_mul hη, norm_smul, Real.norm_eq_abs]

end Affine

/-! ### Comparison with barriers -/

namespace IsSemilinearSolution

variable {S : Setting d} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ}

/-- The time translate `u(·, · + s)` of a solution of (3.4) solves (3.4) with data `u(·, s)`. -/
theorem shift (hu : IsSemilinearSolution S.U S.Q β ε g u) {s : ℝ} (hs : 0 ≤ s) :
    IsSemilinearSolution S.U S.Q β ε (fun y ↦ u (y, s)) (fun q ↦ u (q.1, q.2 + s)) := by
  refine ⟨?_, ?_, fun x _ ↦ by simp, fun x hx t ht ↦ ?_⟩
  · exact hu.1.comp (by fun_prop : Continuous fun q : E d × ℝ ↦ (q.1, q.2 + s)).continuousOn
      fun q hq ↦ ⟨hq.1, by have := hq.2; simp only [mem_Ici] at this ⊢; linarith⟩
  · exact (hu.2.1.comp_add_time s).mono fun t ht ↦ by
      simp only [mem_preimage, mem_Ioi] at ht ⊢; linarith
  · simp only
    rw [hu.2.2.2 x hx (t + s) (by linarith), hu.2.2.2 x hx s hs]

/-- **Lower barrier from the sub-profile** on a finite horizon `T`: if `W` is a classical
subsolution of the heat equation in `U × (0, T]` satisfying the layer condition
`Q² ≤ θ |∇W|²` on `{ε s₀ < W < ε}`, and `(W + c_θ ε)₊ ≤ g` on the parabolic boundary, then
`W ≤ u` on `Ū × [0, T]`. Comparison of `u` with `(Φ_{ε,θ}(W))₊`, by the comparison principle for
(3.4) (from parabolic-basic-theory v0.1.0). -/
theorem le_of_profileBarrier (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {T : ℝ}
    (hT : 0 < T) {W : E d × ℝ → ℝ} (hWc : Continuous W)
    (hWx : ∀ t, ContDiff ℝ 2 (fun y ↦ W (y, t)))
    (hWt : ∀ x t, DifferentiableAt ℝ (fun s ↦ W (x, s)) t)
    (hheat : ∀ p ∈ S.U ×ˢ Ioc 0 T, dₜ W p - lapₓ W p ≤ 0)
    (hgrad : ∀ p ∈ S.U ×ˢ Ioc 0 T, ε * profileSubZero β θ < W p → W p < ε →
      S.Q p.1 ^ 2 ≤ θ * ‖gradₓ W p‖ ^ 2)
    (hbd : ∀ x ∈ closure S.U, ∀ s ∈ Icc 0 T, (s = 0 ∨ x ∈ frontier S.U) →
      max (W (x, s) + subConst θ * ε) 0 ≤ g x) :
    ∀ x ∈ closure S.U, ∀ t ∈ Icc 0 T, W (x, t) ≤ u (x, t) := by
  set B : E d × ℝ → ℝ := fun p ↦ max (profileSubEps β θ ε (W p)) 0 with hB
  have hBc : Continuous B :=
    ((profileSubEps_continuous hβ hθ hθ1).comp hWc).max continuous_const
  have hsub : IsSemilinearViscSubOn S.U S.Q β ε (Ioc 0 T) B :=
    isSemilinearViscSubOn_max_profileSubEps hβ hθ hθ1 hε S.isOpen exists_Ioc_subset_Ioc
      hWc.continuousOn hWx hWt hheat hgrad
  have hcomp := Registry.semilinear_comparison S.isOpen S.isBounded hT S.lip hβ hε
    hBc.continuousOn (hu.continuousOn_Icc T) hsub (hu.viscSuperOn T) ?_
  · intro x hx t ht
    exact (le_max_profileSubEps hβ hθ hθ1 hε _).trans (hcomp (x, t) ⟨hx, ht⟩)
  · intro p hp
    rw [hu.eq_on_parBdry hp]
    refine (max_profileSubEps_le hβ hθ hθ1 hε _).trans ?_
    rcases hp with ⟨hx, hs⟩ | ⟨hx, hs⟩
    · rw [mem_singleton_iff] at hs
      exact hbd p.1 hx p.2 (by rw [hs]; exact ⟨le_rfl, hT.le⟩) (Or.inl hs)
    · exact hbd p.1 (frontier_subset_closure hx) p.2 hs (Or.inr hx)

/-- **Caloric upper barrier**: if `g(z) ≤ g(y) + σ + A |z - y|²` on `Ū`, then
`u(y, t) ≤ g(y) + σ + 2 d A t`. Comparison with `g(y) + σ + A|x - y|² + 2dAt`, a supersolution
since `β_ε ≥ 0`. -/
theorem le_add_of_quadratic (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {y : E d} (hy : y ∈ closure S.U) {σ A : ℝ}
    (hA : 0 ≤ A) (hg : ∀ z ∈ closure S.U, g z ≤ g y + σ + A * ‖z - y‖ ^ 2) :
    ∀ t, 0 ≤ t → u (y, t) ≤ g y + σ + 2 * d * A * t := by
  intro t ht
  set B : E d × ℝ → ℝ := fun q ↦ (g y + σ + 2 * d * A * q.2) + A * ‖q.1 - y‖ ^ 2 with hB
  have hBc : Continuous B := by rw [hB]; fun_prop
  have hsuper : ∀ T > 0, IsSemilinearViscSuperOn S.U S.Q β ε (Ioc 0 T) B := by
    intro T _
    refine isSemilinearViscSuperOn_of_classical S.isOpen exists_Ioc_subset_Ioc hBc.continuousOn
      (fun s ↦ by
        simp only [hB]; exact contDiff_const.add (contDiff_const.mul (contDiff_normSq_sub_const y)))
      (fun x s ↦ by simp only [hB]; fun_prop) fun p _ ↦ ?_
    have hdt : dₜ B p = 2 * d * A := by
      simp only [dₜ, hB]
      simp
    have hlap : lapₓ B p = 2 * d * A := by
      simp only [lapₓ, hB]
      rw [laplacian_const_add_mul_normSq, finrank_euclideanSpace_fin]; ring
    have h1 := hβ.betaEps_nonneg ε (B p) hε.le
    rw [hdt, hlap, sub_self, neg_nonpos]
    have := (sq_nonneg (S.Q p.1))
    positivity
  have key := hu.le_of_super hβ hε hBc.continuousOn hsuper ?_ y hy t ht
  · refine key.trans (le_of_eq ?_)
    simp only [hB, sub_self, norm_zero]; ring
  · intro x hx s hs _
    have h1 := hg x hx
    have h2 : 0 ≤ 2 * d * A * s := by positivity
    simp only [hB]
    linarith

end IsSemilinearSolution

/-! ### The exterior barrier -/

set_option maxHeartbeats 1000000 in
-- many `set` abbreviations with nonlinear real arithmetic in one declaration
/-- **Exterior barrier** (from the uniform exterior ball (A.12)): there are
constants `c, C, G, l > 0` such that every `x₀ ∈ ∂U` carries a smooth `η` with `η(x₀) = 0` and,
on `Ū`, `c |x - x₀|² ≤ η(x) ≤ C |x - x₀|`, `|∇η| ≥ G` and `Δη ≤ -l`. Here
`η(x) = e^{(d+1)/2} - e^{(d+1)(1 - |x - y₀|²/(2ρ₀²))}` (a shifted `trapBarrier` centred at the
exterior ball centre `y₀`). -/
theorem Setting.exists_exteriorBarrier (S : Setting d) :
    ∃ c > 0, ∃ C > 0, ∃ G > 0, ∃ l > 0, ∀ x₀ ∈ frontier S.U, ∃ η : E d → ℝ,
      ContDiff ℝ 2 η ∧ η x₀ = 0 ∧ ∀ x ∈ closure S.U,
        c * ‖x - x₀‖ ^ 2 ≤ η x ∧ η x ≤ C * ‖x - x₀‖ ∧ G ≤ ‖∇ η x‖ ∧ Δ η x ≤ -l := by
  obtain ⟨ρ₀, hρ₀, hball⟩ := S.exists_uniformExteriorBall
  obtain ⟨R, hR⟩ := S.isBounded.isCompact_closure.isBounded.subset_closedBall (0 : E d)
  set R' := |R| with hR'
  have hR'0 : 0 ≤ R' := abs_nonneg R
  set k : ℝ := (d : ℝ) + 1 with hk
  have hk0 : 0 < k := by positivity
  set k' := k / (2 * ρ₀ ^ 2) with hk'
  have hk'0 : 0 < k' := by positivity
  set D := 2 * R' + ρ₀ with hD
  set hmin := k * (1 - D ^ 2 / (2 * ρ₀ ^ 2)) with hhmin
  set h₀ := k / 2 with hh₀
  refine ⟨Real.exp hmin * k / (4 * ρ₀ ^ 2), by positivity,
    Real.exp h₀ * k * (2 * R' + 2 * ρ₀) / (2 * ρ₀ ^ 2), by positivity,
    k' * Real.exp hmin * (2 * ρ₀), by positivity, 2 * k' * Real.exp hmin, by positivity,
    fun x₀ hx₀ ↦ ?_⟩
  obtain ⟨y₀, hy₀, hy₀'⟩ := hball x₀ hx₀
  set c₀ := trapProfile d ρ₀ 1 (ρ₀ ^ 2) with hc₀
  have hη2 : ContDiff ℝ 2 (trapBarrier y₀ ρ₀ 1) := contDiff_trapBarrier y₀
  refine ⟨fun x ↦ -c₀ + 1 * trapBarrier y₀ ρ₀ 1 x, contDiff_const.add (contDiff_const.mul hη2),
    ?_, fun x hx ↦ ?_⟩
  · simp [trapBarrier, hy₀, hc₀]
  have hx₀cl := frontier_subset_closure hx₀
  have hxR : ‖x‖ ≤ R' := (mem_closedBall_zero_iff.1 (hR hx)).trans (le_abs_self R)
  have hx₀R : ‖x₀‖ ≤ R' := (mem_closedBall_zero_iff.1 (hR hx₀cl)).trans (le_abs_self R)
  have hxx₀ : ‖x - x₀‖ ≤ 2 * R' := (norm_sub_le _ _).trans (by linarith)
  have hz1 := hy₀' x hx
  have hxy : ‖x - y₀‖ ≤ ‖x - x₀‖ + ρ₀ := by
    calc ‖x - y₀‖ = ‖(x - x₀) + (x₀ - y₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - x₀‖ + ‖x₀ - y₀‖ := norm_add_le _ _
      _ = ‖x - x₀‖ + ρ₀ := by rw [hy₀]
  set z := ‖x - y₀‖ ^ 2 with hz
  have hn0 := norm_nonneg (x - x₀)
  have hz2 : z ≤ D ^ 2 := by
    have : ‖x - y₀‖ ≤ D := by linarith
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hzρ : ρ₀ ^ 2 ≤ z := by linarith [sq_nonneg ‖x - x₀‖]
  have hρy : ρ₀ ≤ ‖x - y₀‖ := (pow_le_pow_iff_left₀ hρ₀.le (norm_nonneg _) two_ne_zero).1 hzρ
  set h := k * (1 - z / (2 * ρ₀ ^ 2)) with hh
  have hval : -c₀ + 1 * trapBarrier y₀ ρ₀ 1 x = Real.exp h₀ - Real.exp h := by
    have e : ((d : ℝ) + 1) * (1 - ρ₀ ^ 2 / (2 * ρ₀ ^ 2)) = h₀ := by
      rw [hh₀, hk]; field_simp; ring
    simp only [hc₀, trapBarrier, trapProfile, e]
    rw [← hk, ← hz, ← hh]; ring
  have hdiff : h₀ - h = k' * (z - ρ₀ ^ 2) := by
    rw [hh₀, hh, hk']; field_simp; ring
  have hhmin_le : hmin ≤ h := by
    rw [hhmin, hh]
    have : z / (2 * ρ₀ ^ 2) ≤ D ^ 2 / (2 * ρ₀ ^ 2) := by gcongr
    linarith [mul_le_mul_of_nonneg_left this hk0.le]
  have hEmin : Real.exp hmin ≤ Real.exp h := Real.exp_le_exp.2 hhmin_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- lower quadratic bound
    beta_reduce
    rw [hval]
    have h1 : Real.exp h * (h₀ - h) ≤ Real.exp h₀ - Real.exp h := by
      have := Real.add_one_le_exp (h₀ - h)
      have e : Real.exp h * Real.exp (h₀ - h) = Real.exp h₀ := by
        rw [← Real.exp_add]; ring_nf
      linarith [mul_le_mul_of_nonneg_left this (Real.exp_pos h).le]
    have h2 : k' * (‖x - x₀‖ ^ 2 / 2) ≤ h₀ - h := by
      rw [hdiff]; exact mul_le_mul_of_nonneg_left (by linarith) hk'0.le
    have h3 : Real.exp hmin * (k' * (‖x - x₀‖ ^ 2 / 2)) ≤ Real.exp h * (h₀ - h) :=
      mul_le_mul hEmin h2 (by positivity) (Real.exp_pos h).le
    have e : Real.exp hmin * k / (4 * ρ₀ ^ 2) * ‖x - x₀‖ ^ 2 =
        Real.exp hmin * (k' * (‖x - x₀‖ ^ 2 / 2)) := by
      rw [hk']; field_simp; ring
    linarith
  · -- upper linear bound
    beta_reduce
    rw [hval]
    have h1 : Real.exp h₀ - Real.exp h ≤ Real.exp h₀ * (h₀ - h) := by
      have := Real.add_one_le_exp (h - h₀)
      have e : Real.exp h₀ * Real.exp (h - h₀) = Real.exp h := by
        rw [← Real.exp_add]; ring_nf
      linarith [mul_le_mul_of_nonneg_left this (Real.exp_pos h₀).le]
    have h2 : z - ρ₀ ^ 2 ≤ ‖x - x₀‖ * (2 * R' + 2 * ρ₀) := by
      have h4 : z ≤ (‖x - x₀‖ + ρ₀) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
      have h5 : (‖x - x₀‖ + ρ₀) ^ 2 - ρ₀ ^ 2 = ‖x - x₀‖ * (‖x - x₀‖ + 2 * ρ₀) := by ring
      have h6 : ‖x - x₀‖ * (‖x - x₀‖ + 2 * ρ₀) ≤ ‖x - x₀‖ * (2 * R' + 2 * ρ₀) :=
        mul_le_mul_of_nonneg_left (by linarith) hn0
      linarith
    have h3 : Real.exp h₀ * (h₀ - h) ≤ Real.exp h₀ * (k' * (‖x - x₀‖ * (2 * R' + 2 * ρ₀))) := by
      rw [hdiff]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hk'0.le)
        (Real.exp_pos _).le
    have e : Real.exp h₀ * k * (2 * R' + 2 * ρ₀) / (2 * ρ₀ ^ 2) * ‖x - x₀‖ =
        Real.exp h₀ * (k' * (‖x - x₀‖ * (2 * R' + 2 * ρ₀))) := by
      rw [hk']; field_simp
    linarith
  · -- gradient lower bound
    have hg1 : ‖∇ (trapBarrier y₀ ρ₀ 1) x‖ = k' * Real.exp h * (2 * ‖x - y₀‖) := by
      rw [norm_gradient_trapBarrier, one_mul, abs_of_pos (by positivity)]
    rw [norm_gradient_const_add_mul
      ((contDiff_trapBarrier y₀ (n := 1)).differentiable one_ne_zero x), abs_one, one_mul, hg1]
    have h1 : k' * Real.exp hmin ≤ k' * Real.exp h := mul_le_mul_of_nonneg_left hEmin hk'0.le
    have h2 : 2 * ρ₀ ≤ 2 * ‖x - y₀‖ := mul_le_mul_of_nonneg_left hρy (by norm_num)
    have h3 : k' * Real.exp hmin * (2 * ρ₀) ≤ k' * Real.exp h * (2 * ‖x - y₀‖) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    exact h3
  · -- strict superharmonicity
    have hl1 : Δ (trapBarrier y₀ ρ₀ 1) x = 2 * (k' * Real.exp h) * ((d : ℝ) - 2 * k' * z) := by
      rw [laplacian_trapBarrier, one_mul]
    rw [laplacian_const_add_mul hη2.contDiffAt, one_mul, hl1]
    have hd1 : (d : ℝ) - 2 * k' * z ≤ -1 := by
      have : 2 * k' * z = k * (z / ρ₀ ^ 2) := by rw [hk']; field_simp
      have h1 : 1 ≤ z / ρ₀ ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      rw [this]; linarith [mul_le_mul_of_nonneg_left h1 hk0.le]
    have h1 : 0 < 2 * (k' * Real.exp h) := by positivity
    have h2 : 2 * (k' * Real.exp h) * ((d : ℝ) - 2 * k' * z) ≤ 2 * (k' * Real.exp h) * (-1) :=
      mul_le_mul_of_nonneg_left hd1 h1.le
    have h3 : 2 * k' * Real.exp hmin ≤ 2 * (k' * Real.exp h) := by
      linarith [mul_le_mul_of_nonneg_left hEmin hk'0.le]
    linarith


end PerronVariational

end
