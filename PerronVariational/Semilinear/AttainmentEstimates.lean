/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.Profiles
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Semilinear.AttainmentBarriers
import PerronVariational.Semilinear.Monotone
import PerronVariational.Semilinear.PositivityTrace

/-!
# Boundary and initial-time estimates for the attainment of the data (Proposition A.8)

Lemma A.9 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.5).

* `exists_boundary_estimate` (the lateral estimate of Lemma A.9, uniform in `t ≥ 0` and
  `ε ∈ (0, 1]`): `|u(x, t) - g(x₀)| ≤ 2σ + K |x - x₀|` for `x₀ ∈ ∂U`, `x ∈ Ū`. Barriers built
  from the exterior barrier `η` (`Setting.exists_exteriorBarrier`): the stationary supersolution
  `g(x₀) + σ + Aη`, and the subsolutions `(Φ_{ε,1/2}(g(x₀) - 2σ - Aη))₊` for `ε` small and
  `g(x₀) - 2σ - A'η` (strictly subharmonic enough to absorb the reaction term `≤ C/ε`) for `ε`
  bounded below. This replaces the harmonic upper barrier of the paper, so the Dirichlet problem
  for the Laplacian, which the paper solves to build that barrier, is not needed.
* `exists_initial_estimate`: `|u(x₀, t) - g(x₀)| ≤ 3σ` for `t ≤ τ`, given a quadratic modulus
  `|g(y) - g(x₀)| ≤ σ + A |y - x₀|²` of the data on `Ū` (caloric upper barrier, and lower
  barriers `(Φ_{ε,1/2}(g(x₀) - 2σ - A'|y - x₀|² - 2dA't))₊` resp. a classical subsolution).
-/

open Set Filter Topology Metric
open scoped NNReal Gradient Laplacian ContDiff

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- `Q² ≤ Q_max²` on `Ū`. -/
theorem Setting.Q_sq_le (S : Setting d) {x : E d} (hx : x ∈ closure S.U) :
    S.Q x ^ 2 ≤ S.Qmax ^ 2 := by
  obtain ⟨h1, h2⟩ := S.Q_mem x hx
  exact pow_le_pow_left₀ (S.Qmin_pos.le.trans h1) h2 2

/-- `Q² β_ε ≤ Q_max² β_max / ε`. -/
theorem Setting.Q_sq_mul_betaEps_le (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {βmax : ℝ} (hβmax : ∀ s, β s ≤ βmax) {ε ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε) {x : E d}
    (hx : x ∈ closure S.U) (z : ℝ) :
    S.Q x ^ 2 * betaEps β ε z ≤ S.Qmax ^ 2 * βmax / ε₁ := by
  have hε0 : 0 < ε := hε₁.trans_le hε
  have hb0 : 0 ≤ βmax := (hβ.nonneg 0).trans (hβmax 0)
  have h1 : betaEps β ε z ≤ βmax / ε₁ := by
    rw [betaEps]
    calc β (z / ε) / ε ≤ βmax / ε := div_le_div_of_nonneg_right (hβmax _) hε0.le
      _ ≤ βmax / ε₁ := div_le_div_of_nonneg_left hb0 hε₁ hε
  have h2 := S.Q_sq_le hx
  have h3 := hβ.betaEps_nonneg ε z hε0.le
  calc S.Q x ^ 2 * betaEps β ε z ≤ S.Qmax ^ 2 * (βmax / ε₁) :=
        mul_le_mul h2 h1 h3 (sq_nonneg _)
    _ = S.Qmax ^ 2 * βmax / ε₁ := by ring

/-- `L r ≤ σ + (L²/(4σ)) r²`. -/
theorem mul_le_add_sq {L r σ : ℝ} (hσ : 0 < σ) : L * r ≤ σ + L ^ 2 / (4 * σ) * r ^ 2 := by
  have e : σ + L ^ 2 / (4 * σ) * r ^ 2 - L * r = (2 * σ - L * r) ^ 2 / (4 * σ) := by
    field_simp; ring
  have : 0 ≤ (2 * σ - L * r) ^ 2 / (4 * σ) := by positivity
  linarith

/-- The space-time function `(y, t) ↦ a + b η(y)`: time derivative, Laplacian, gradient. -/
theorem dₜ_const_add_mul (η : E d → ℝ) (a b : ℝ) (p : E d × ℝ) :
    dₜ (fun q : E d × ℝ ↦ a + b * η q.1) p = 0 := by
  simp [dₜ]

theorem lapₓ_const_add_mul {η : E d → ℝ} (hη : ContDiff ℝ 2 η) (a b : ℝ) (p : E d × ℝ) :
    lapₓ (fun q : E d × ℝ ↦ a + b * η q.1) p = b * Δ η p.1 :=
  laplacian_const_add_mul hη.contDiffAt a b

theorem norm_gradₓ_const_add_mul {η : E d → ℝ} (hη : ContDiff ℝ 2 η) (a b : ℝ)
    (p : E d × ℝ) : ‖gradₓ (fun q : E d × ℝ ↦ a + b * η q.1) p‖ = |b| * ‖∇ η p.1‖ :=
  norm_gradient_const_add_mul ((hη.differentiable (by norm_num)) p.1) a b

namespace IsSemilinearSolution

variable {S : Setting d} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ}

/-- Upper stationary barrier `a + Aη` for superharmonic `η` (`A ≥ 0`). -/
theorem le_const_add_mul (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {η : E d → ℝ} (hη2 : ContDiff ℝ 2 η) {a A : ℝ}
    (hA : 0 ≤ A) (hΔ : ∀ y ∈ S.U, Δ η y ≤ 0) (hbd : ∀ y ∈ closure S.U, g y ≤ a + A * η y) :
    ∀ x ∈ closure S.U, ∀ t, 0 ≤ t → u (x, t) ≤ a + A * η x := by
  set B : E d × ℝ → ℝ := fun q ↦ a + A * η q.1 with hB
  have hBc : Continuous B := continuous_const.add (continuous_const.mul
    (hη2.continuous.comp continuous_fst))
  have hsuper : ∀ T > 0, IsSemilinearViscSuperOn S.U S.Q β ε (Ioc 0 T) B := by
    intro T _
    refine isSemilinearViscSuperOn_of_classical S.isOpen exists_Ioc_subset_Ioc
      hBc.continuousOn (fun s ↦ contDiff_const.add (contDiff_const.mul hη2))
      (fun y s ↦ differentiableAt_const (c := a + A * η y)) fun p hp ↦ ?_
    rw [hB, dₜ_const_add_mul, lapₓ_const_add_mul hη2]
    have h1 := mul_nonneg hA (neg_nonneg.2 (hΔ p.1 hp.1))
    have h2 : 0 ≤ S.Q p.1 ^ 2 * betaEps β ε (a + A * η p.1) :=
      mul_nonneg (sq_nonneg _) (hβ.betaEps_nonneg ε _ hε.le)
    linarith
  exact hu.le_of_super hβ hε hBc.continuousOn hsuper fun y hy s _ _ ↦ hbd y hy

/-- Lower stationary barrier `(Φ_{ε,1/2}(a - Aη))₊` for superharmonic `η` with
`A |∇η| ≥ 2 Q_max`: if `a - Aη + c_{1/2} ε ≤ g` on `Ū` (and `g ≥ 0`), then `a - Aη ≤ u`. -/
theorem const_sub_mul_le_of_profile (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {η : E d → ℝ} (hη2 : ContDiff ℝ 2 η) {a A : ℝ}
    (hA : 0 ≤ A) (hΔ : ∀ y ∈ S.U, Δ η y ≤ 0) (hG : ∀ y ∈ S.U, 2 * S.Qmax ≤ A * ‖∇ η y‖)
    (hbd : ∀ y ∈ closure S.U, a - A * η y + subConst (1 / 2) * ε ≤ g y)
    (hg0 : ∀ y ∈ closure S.U, 0 ≤ g y) :
    ∀ x ∈ closure S.U, ∀ t, 0 ≤ t → a - A * η x ≤ u (x, t) := by
  intro x hx t ht
  set W : E d × ℝ → ℝ := fun q ↦ a + (-A) * η q.1 with hW
  have hWc : Continuous W := continuous_const.add (continuous_const.mul
    (hη2.continuous.comp continuous_fst))
  have key := hu.le_of_profileBarrier hβ hε (θ := 1 / 2) (by norm_num) (by norm_num)
    (T := t + 1) (by linarith) hWc (fun s ↦ contDiff_const.add (contDiff_const.mul hη2))
    (fun y s ↦ differentiableAt_const (c := a + (-A) * η y)) ?_ ?_ ?_ x hx t ⟨ht, by linarith⟩
  · have e : W (x, t) = a - A * η x := by simp only [hW]; ring
    rw [← e]; exact key
  · intro p hp
    rw [hW, dₜ_const_add_mul, lapₓ_const_add_mul hη2]
    have h1 := mul_nonneg hA (neg_nonneg.2 (hΔ p.1 hp.1))
    linarith
  · intro p hp _ _
    rw [hW, norm_gradₓ_const_add_mul hη2, abs_neg, abs_of_nonneg hA]
    have h1 := S.Q_sq_le (subset_closure hp.1)
    have h4 := hG p.1 hp.1
    have hQ : 0 ≤ S.Qmax := S.Qmin_pos.le.trans S.Qmin_le_Qmax
    have h5 : (2 * S.Qmax) ^ 2 ≤ (A * ‖∇ η p.1‖) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
    nlinarith
  · intro y hy s _ _
    refine max_le ?_ (hg0 y hy)
    have := hbd y hy
    simp only [hW]
    linarith

/-- Lower stationary barrier `a - Aη` when `A(-Δη) ≥ K_r ≥ Q² β_ε`: a classical subsolution. -/
theorem const_sub_mul_le_of_classical (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {η : E d → ℝ} (hη2 : ContDiff ℝ 2 η)
    {a A Kr : ℝ} (hΔ : ∀ y ∈ S.U, Kr ≤ A * (-Δ η y))
    (hreact : ∀ y ∈ S.U, ∀ z, S.Q y ^ 2 * betaEps β ε z ≤ Kr)
    (hbd : ∀ y ∈ closure S.U, a - A * η y ≤ g y) :
    ∀ x ∈ closure S.U, ∀ t, 0 ≤ t → a - A * η x ≤ u (x, t) := by
  intro x hx t ht
  set B : E d × ℝ → ℝ := fun q ↦ a + (-A) * η q.1 with hB
  have hBc : Continuous B := continuous_const.add (continuous_const.mul
    (hη2.continuous.comp continuous_fst))
  have hsub : ∀ T > 0, IsSemilinearViscSubOn S.U S.Q β ε (Ioc 0 T) B := by
    intro T _
    refine isSemilinearViscSubOn_of_classical S.isOpen exists_Ioc_subset_Ioc
      hBc.continuousOn (fun s ↦ contDiff_const.add (contDiff_const.mul hη2))
      (fun y s ↦ differentiableAt_const (c := a + (-A) * η y)) fun p hp ↦ ?_
    rw [hB, dₜ_const_add_mul, lapₓ_const_add_mul hη2]
    have h1 := hΔ p.1 hp.1
    have h2 := hreact p.1 hp.1 (a + -A * η p.1)
    linarith
  have key := hu.ge_of_sub hβ hε hBc.continuousOn hsub (fun y hy s _ _ ↦ ?_) x hx t ht
  · have e : B (x, t) = a - A * η x := by simp only [hB]; ring
    rw [← e]; exact key
  · have := hbd y hy
    simp only [hB]
    linarith

/-- The quadratic `(y, t) ↦ (a - k t) + b |y - x₀|²`: derivatives. -/
theorem dₜ_quad (x₀ : E d) (a k b : ℝ) (p : E d × ℝ) :
    dₜ (fun q : E d × ℝ ↦ (a - k * q.2) + b * ‖q.1 - x₀‖ ^ 2) p = -k := by
  simp only [dₜ]
  simp

theorem lapₓ_quad (x₀ : E d) (a k b : ℝ) (p : E d × ℝ) :
    lapₓ (fun q : E d × ℝ ↦ (a - k * q.2) + b * ‖q.1 - x₀‖ ^ 2) p = 2 * b * d := by
  simp only [lapₓ]
  rw [laplacian_const_add_mul_normSq, finrank_euclideanSpace_fin]

theorem norm_gradₓ_quad (x₀ : E d) (a k b : ℝ) (p : E d × ℝ) :
    ‖gradₓ (fun q : E d × ℝ ↦ (a - k * q.2) + b * ‖q.1 - x₀‖ ^ 2) p‖ =
      |b| * (2 * ‖p.1 - x₀‖) := by
  simp only [gradₓ]
  rw [norm_gradient_const_add_mul ((contDiff_normSq_sub_const x₀ (n := 1)).differentiable
    one_ne_zero p.1), norm_gradient_normSq_sub]

theorem contDiff_quad_slice (x₀ : E d) (a k b t : ℝ) :
    ContDiff ℝ 2 (fun y ↦ (fun q : E d × ℝ ↦ (a - k * q.2) + b * ‖q.1 - x₀‖ ^ 2) (y, t)) := by
  simp only
  exact contDiff_const.add (contDiff_const.mul (contDiff_normSq_sub_const x₀))

theorem continuous_quad (x₀ : E d) (a k b : ℝ) :
    Continuous (fun q : E d × ℝ ↦ (a - k * q.2) + b * ‖q.1 - x₀‖ ^ 2) := by
  fun_prop

theorem differentiableAt_quad_time (x₀ : E d) (a k b : ℝ) (x : E d) (t : ℝ) :
    DifferentiableAt ℝ
      (fun s ↦ (fun q : E d × ℝ ↦ (a - k * q.2) + b * ‖q.1 - x₀‖ ^ 2) (x, s)) t := by
  simp only
  fun_prop

/-- Lower barrier `(Φ_{ε,1/2}(a - A|y - x₀|² - 2dAt))₊` on the horizon `T`, when the layer
condition `Q_max² ≤ 2A²|y - x₀|²` holds where the barrier is `< ε`. -/
theorem const_sub_quad_le_of_profile (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {x₀ : E d} {a A T : ℝ} (hA : 0 ≤ A)
    (hT : 0 < T)
    (hlayer : ∀ y ∈ S.U, ∀ s ∈ Ioc 0 T, (a - 2 * d * A * s) + (-A) * ‖y - x₀‖ ^ 2 < ε →
      S.Qmax ^ 2 ≤ 2 * A ^ 2 * ‖y - x₀‖ ^ 2)
    (hbd : ∀ y ∈ closure S.U, a - A * ‖y - x₀‖ ^ 2 + subConst (1 / 2) * ε ≤ g y)
    (hg0 : ∀ y ∈ closure S.U, 0 ≤ g y) :
    ∀ x ∈ closure S.U, ∀ t ∈ Icc 0 T, a - A * ‖x - x₀‖ ^ 2 - 2 * d * A * t ≤ u (x, t) := by
  intro x hx t ht
  set W : E d × ℝ → ℝ := fun q ↦ (a - 2 * d * A * q.2) + (-A) * ‖q.1 - x₀‖ ^ 2 with hW
  have key := hu.le_of_profileBarrier hβ hε (θ := 1 / 2) (by norm_num) (by norm_num) hT
    (continuous_quad x₀ a (2 * d * A) (-A)) (contDiff_quad_slice x₀ a (2 * d * A) (-A))
    (differentiableAt_quad_time x₀ a (2 * d * A) (-A)) ?_ ?_ ?_ x hx t ht
  · have e : W (x, t) = a - A * ‖x - x₀‖ ^ 2 - 2 * d * A * t := by simp only [hW]; ring
    rw [← e]; exact key
  · intro p _
    rw [dₜ_quad, lapₓ_quad]
    linarith
  · intro p hp _ hlt
    rw [norm_gradₓ_quad, abs_neg, abs_of_nonneg hA]
    have h1 := S.Q_sq_le (subset_closure hp.1)
    have h2 := hlayer p.1 hp.1 p.2 hp.2 hlt
    linarith
  · intro y hy s hs _
    refine max_le ?_ (hg0 y hy)
    have h1 := hbd y hy
    have h2 : 0 ≤ 2 * d * A * s := by have := hs.1; positivity
    linarith

/-- Lower classical barrier `a - A|y - x₀|² - (2dA + K_r)t` when `Q² β_ε ≤ K_r`. -/
theorem const_sub_quad_le_of_classical (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {x₀ : E d} {a A Kr : ℝ} (hA : 0 ≤ A)
    (hKr : 0 ≤ Kr) (hreact : ∀ y ∈ S.U, ∀ z, S.Q y ^ 2 * betaEps β ε z ≤ Kr)
    (hbd : ∀ y ∈ closure S.U, a - A * ‖y - x₀‖ ^ 2 ≤ g y) :
    ∀ x ∈ closure S.U, ∀ t, 0 ≤ t → a - A * ‖x - x₀‖ ^ 2 - (2 * d * A + Kr) * t ≤ u (x, t) := by
  intro x hx t ht
  set B : E d × ℝ → ℝ := fun q ↦ (a - (2 * d * A + Kr) * q.2) + (-A) * ‖q.1 - x₀‖ ^ 2 with hB
  have hsub : ∀ T > 0, IsSemilinearViscSubOn S.U S.Q β ε (Ioc 0 T) B := by
    intro T _
    refine isSemilinearViscSubOn_of_classical S.isOpen exists_Ioc_subset_Ioc
      (continuous_quad x₀ a (2 * d * A + Kr) (-A)).continuousOn
      (contDiff_quad_slice x₀ a (2 * d * A + Kr) (-A))
      (differentiableAt_quad_time x₀ a (2 * d * A + Kr) (-A)) fun p hp ↦ ?_
    rw [hB, dₜ_quad, lapₓ_quad]
    have := hreact p.1 hp.1 (B p)
    rw [hB] at this
    linarith
  have key := hu.ge_of_sub hβ hε (continuous_quad x₀ a (2 * d * A + Kr) (-A)).continuousOn hsub
    (fun y hy s hs _ ↦ ?_) x hx t ht
  · have e : B (x, t) = a - A * ‖x - x₀‖ ^ 2 - (2 * d * A + Kr) * t := by simp only [hB]; ring
    rw [← e]; exact key
  · have h1 := hbd y hy
    have h2 : 0 ≤ (2 * d * A + Kr) * s := by positivity
    linarith

end IsSemilinearSolution

/-- **Lateral estimate** (Lemma A.9, uniform in time): for `σ > 0` there is `K` such that for
`0 < ε ≤ 1`, every solution `u` of (3.4) with nonnegative `L`-Lipschitz data `g` satisfies
`|u(x, t) - g(x₀)| ≤ 2σ + K |x - x₀|` for `x₀ ∈ ∂U`, `x ∈ Ū`, `t ≥ 0`. -/
theorem exists_boundary_estimate (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    (L : ℝ≥0) {σ : ℝ} (hσ : 0 < σ) :
    ∃ K ≥ 0, ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ),
      LipschitzOnWith L g (closure S.U) → (∀ x ∈ closure S.U, 0 ≤ g x) →
      IsSemilinearSolution S.U S.Q β ε g u →
      ∀ x₀ ∈ frontier S.U, ∀ x ∈ closure S.U, ∀ t, 0 ≤ t →
        |u (x, t) - g x₀| ≤ 2 * σ + K * ‖x - x₀‖ := by
  obtain ⟨cη, hcη, Cη, hCη, G, hG, l, hl, hηex⟩ := S.exists_exteriorBarrier
  set θ : ℝ := 1 / 2 with hθ_def
  have hθ : 0 < θ := by norm_num
  have hθ1 : θ < 1 := by norm_num
  set c := subConst θ with hc_def
  have hc0 : 0 ≤ c := subConst_nonneg hθ hθ1
  set eσ := σ / (c + 1) with heσ
  have heσ0 : 0 < eσ := by positivity
  have hceσ : c * eσ ≤ σ := by
    rw [heσ, mul_div_assoc', div_le_iff₀ (by positivity)]; linarith
  obtain ⟨βmax, -, hβmax⟩ := hβ.exists_le
  have hQmax : 0 < S.Qmax := S.Qmin_pos.trans_le S.Qmin_le_Qmax
  set Kr := S.Qmax ^ 2 * βmax / eσ with hKr
  set A₀ := (L : ℝ) ^ 2 / (4 * σ) / cη with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  set A₂ := A₀ + 2 * S.Qmax / G with hA₂
  have hA₂0 : 0 ≤ A₂ := by positivity
  set A₃ := A₀ + |Kr| / l with hA₃
  have hA₃0 : 0 ≤ A₃ := by positivity
  set K := (A₀ + 2 * S.Qmax / G + |Kr| / l) * Cη with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, ?_⟩
  intro ε hε g u hgL hg0 hu x₀ hx₀ x hx t ht
  have hε0 : 0 < ε := hε.1
  obtain ⟨η, hη2, hη0, hη⟩ := hηex x₀ hx₀
  have hx₀cl : x₀ ∈ closure S.U := frontier_subset_closure hx₀
  -- two-sided control of the data by `η`
  have hgη : ∀ y ∈ closure S.U, |g y - g x₀| ≤ σ + A₀ * η y := by
    intro y hy
    have h1 := hgL.dist_le_mul y hy x₀ hx₀cl
    rw [Real.dist_eq, dist_eq_norm] at h1
    have h2 := mul_le_add_sq (L := (L : ℝ)) (r := ‖y - x₀‖) hσ
    have h3 : (L : ℝ) ^ 2 / (4 * σ) * ‖y - x₀‖ ^ 2 ≤ A₀ * η y := by
      have := mul_le_mul_of_nonneg_left (hη y hy).1 hA₀0
      calc (L : ℝ) ^ 2 / (4 * σ) * ‖y - x₀‖ ^ 2 = A₀ * (cη * ‖y - x₀‖ ^ 2) := by
            rw [hA₀]; field_simp
        _ ≤ A₀ * η y := this
    linarith
  have hηlin : ∀ A, 0 ≤ A → A * η x ≤ A * Cη * ‖x - x₀‖ := fun A hA ↦ by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hη x hx).2.1 hA
  have hηnn : ∀ y ∈ closure S.U, 0 ≤ η y := fun y hy ↦
    (by positivity : 0 ≤ cη * ‖y - x₀‖ ^ 2).trans (hη y hy).1
  have hΔ : ∀ y ∈ S.U, Δ η y ≤ -l := fun y hy ↦ (hη y (subset_closure hy)).2.2.2
  -- upper bound
  have hup : u (x, t) ≤ g x₀ + σ + A₀ * η x :=
    hu.le_const_add_mul hβ hε0 hη2 hA₀0 (fun y hy ↦ (hΔ y hy).trans (by linarith))
      (fun y hy ↦ by have := (abs_le.1 (hgη y hy)).2; linarith) x hx t ht
  -- lower bound
  have hlow : g x₀ - 2 * σ - A₃ * η x ≤ u (x, t) ∨ g x₀ - 2 * σ - A₂ * η x ≤ u (x, t) := by
    rcases le_or_gt ε eσ with hεs | hεs
    · -- small `ε`: the profile barrier
      right
      refine hu.const_sub_mul_le_of_profile hβ hε0 hη2 hA₂0
        (fun y hy ↦ (hΔ y hy).trans (by linarith)) (fun y hy ↦ ?_) (fun y hy ↦ ?_) hg0 x hx t ht
      · have h2 := (hη y (subset_closure hy)).2.2.1
        have h3 : 2 * S.Qmax ≤ A₂ * G := by
          rw [hA₂, add_mul, div_mul_cancel₀ _ hG.ne']
          linarith [mul_nonneg hA₀0 hG.le]
        exact h3.trans (mul_le_mul_of_nonneg_left h2 hA₂0)
      · have h1 := (abs_le.1 (hgη y hy)).1
        have h2 : A₀ * η y ≤ A₂ * η y :=
          mul_le_mul_of_nonneg_right (by rw [hA₂]; linarith [(by positivity :
            0 ≤ 2 * S.Qmax / G)]) (hηnn y hy)
        have h3 : c * ε ≤ σ := (mul_le_mul_of_nonneg_left hεs hc0).trans hceσ
        rw [← hθ_def, ← hc_def]
        linarith
    · -- `ε` bounded below: a classical subsolution
      left
      refine hu.const_sub_mul_le_of_classical hβ hε0 hη2 (Kr := |Kr|) (fun y hy ↦ ?_)
        (fun y hy z ↦ ?_) (fun y hy ↦ ?_) x hx t ht
      · have h1 := hΔ y hy
        have h3 : |Kr| ≤ A₃ * l := by
          rw [hA₃, add_mul, div_mul_cancel₀ _ hl.ne']
          linarith [mul_nonneg hA₀0 hl.le]
        exact h3.trans (mul_le_mul_of_nonneg_left (by linarith) hA₃0)
      · exact (S.Q_sq_mul_betaEps_le hβ hβmax heσ0 hεs.le (subset_closure hy) z).trans
          (le_abs_self _)
      · have h1 := (abs_le.1 (hgη y hy)).1
        have h2 : A₀ * η y ≤ A₃ * η y :=
          mul_le_mul_of_nonneg_right (by rw [hA₃]; linarith [(by positivity :
            0 ≤ |Kr| / l)]) (hηnn y hy)
        linarith
  -- conclusion
  have hA₀K : A₀ * Cη ≤ K := by
    rw [hK]; apply mul_le_mul_of_nonneg_right _ hCη.le
    have : 0 ≤ 2 * S.Qmax / G := by positivity
    have : 0 ≤ |Kr| / l := by positivity
    linarith
  have hA₂K : A₂ * Cη ≤ K := by
    rw [hK]; apply mul_le_mul_of_nonneg_right _ hCη.le
    have : 0 ≤ |Kr| / l := by positivity
    rw [hA₂]; linarith
  have hA₃K : A₃ * Cη ≤ K := by
    rw [hK]; apply mul_le_mul_of_nonneg_right _ hCη.le
    have : 0 ≤ 2 * S.Qmax / G := by positivity
    rw [hA₃]; linarith
  have hn := norm_nonneg (x - x₀)
  have e1 := hηlin A₀ hA₀0
  have e2 := hηlin A₂ hA₂0
  have e3 := hηlin A₃ hA₃0
  have f1 := mul_le_mul_of_nonneg_right hA₀K hn
  have f2 := mul_le_mul_of_nonneg_right hA₂K hn
  have f3 := mul_le_mul_of_nonneg_right hA₃K hn
  rw [abs_le]
  constructor
  · rcases hlow with h | h <;> linarith
  · linarith


/-- **Continuity at the initial time**: given `σ > 0` and `A ≥ 0` there is `τ > 0` such that for
`0 < ε ≤ 1`, every solution `u` of (3.4) with data `0 ≤ g ≤ M` and a point `x₀ ∈ Ū` with
`|g(y) - g(x₀)| ≤ σ + A |y - x₀|²` on `Ū` satisfies `|u(x₀, t) - g(x₀)| ≤ 3σ` for `t ∈ [0, τ]`. -/
theorem exists_initial_estimate (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) :
    ∃ τ > 0, ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ) (M : ℝ),
      (∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) → IsSemilinearSolution S.U S.Q β ε g u →
      ∀ x₀ ∈ closure S.U, (∀ y ∈ closure S.U, |g y - g x₀| ≤ σ + A * ‖y - x₀‖ ^ 2) →
        ∀ t ∈ Icc 0 τ, |u (x₀, t) - g x₀| ≤ 3 * σ := by
  set c := subConst (1 / 2 : ℝ) with hc_def
  have hc0 : 0 ≤ c := subConst_nonneg (by norm_num) (by norm_num)
  set eσ := σ / (4 * (c + 1)) with heσ
  have heσ0 : 0 < eσ := by positivity
  have hceσ : c * eσ ≤ σ / 4 := by
    rw [heσ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have heσ4 : eσ ≤ σ / 4 := by
    rw [heσ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [mul_nonneg hc0 hσ.le]
  obtain ⟨βmax, -, hβmax⟩ := hβ.exists_le
  set Kr := |S.Qmax ^ 2 * βmax / eσ| with hKr
  have hKr0 : 0 ≤ Kr := abs_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set A' := A + 2 * S.Qmax ^ 2 / σ with hA'
  have hA'0 : 0 ≤ A' := by positivity
  set T := σ / (4 * d * A' + 1) with hT
  have hT0 : 0 < T := by positivity
  have hTA : 2 * d * A' * T ≤ σ / 2 := by
    rw [hT, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [mul_nonneg hd0 hA'0]
  set τ₁ := σ / (2 * d * A + 1) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁A : 2 * d * A * τ₁ ≤ σ := by
    rw [hτ₁, mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith [mul_nonneg hd0 hA]
  set τ₂ := σ / (2 * d * A + Kr + 1) with hτ₂
  have hτ₂0 : 0 < τ₂ := by positivity
  have hτ₂A : (2 * d * A + Kr) * τ₂ ≤ σ := by
    rw [hτ₂, mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith [mul_nonneg hd0 hA]
  refine ⟨min (min τ₁ T) τ₂, lt_min (lt_min hτ₁0 hT0) hτ₂0, ?_⟩
  intro ε hε g u M hgM hu x₀ hx₀ hgq t ht
  have hε0 : 0 < ε := hε.1
  have htτ₁ : t ≤ τ₁ := ht.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htT : t ≤ T := ht.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have htτ₂ : t ≤ τ₂ := ht.2.trans (min_le_right _ _)
  -- upper bound
  have hup := hu.le_add_of_quadratic hβ hε0 hx₀ (σ := σ) hA
    (fun z hz ↦ by have := (abs_le.1 (hgq z hz)).2; linarith) t ht.1
  have h1 : 2 * d * A * t ≤ σ :=
    (mul_le_mul_of_nonneg_left htτ₁ (by positivity)).trans hτ₁A
  -- lower bound
  have hlow : g x₀ - 3 * σ ≤ u (x₀, t) := by
    rcases le_or_gt (g x₀) (3 * σ) with hg3 | hg3
    · have := (hu.nonneg_le_max hβ hε0 hε.2 hgM (x₀, t) ⟨hx₀, ht.1⟩).1
      linarith
    rcases le_or_gt ε eσ with hεs | hεs
    · have key := hu.const_sub_quad_le_of_profile hβ hε0 (x₀ := x₀) (a := g x₀ - 2 * σ)
        hA'0 hT0 ?_ ?_ (fun y hy ↦ (hgM y hy).1) x₀ hx₀ t ⟨ht.1, htT⟩
      · have h2 : 2 * d * A' * t ≤ σ / 2 :=
          (mul_le_mul_of_nonneg_left htT (by positivity)).trans hTA
        simp only [sub_self, norm_zero] at key
        linarith
      · intro y _ s hs hlt
        have h2 : 2 * d * A' * s ≤ σ / 2 :=
          (mul_le_mul_of_nonneg_left hs.2 (by positivity)).trans hTA
        have h3 : σ / 4 ≤ A' * ‖y - x₀‖ ^ 2 := by linarith
        have h4 : 2 * S.Qmax ^ 2 / σ ≤ A' := by rw [hA']; linarith
        have h5 : S.Qmax ^ 2 ≤ A' * (σ / 2) := by
          rw [div_le_iff₀ hσ] at h4; linarith
        linarith [mul_le_mul_of_nonneg_left h3 hA'0]
      · intro y hy
        have h2 := (abs_le.1 (hgq y hy)).1
        have h3 : A * ‖y - x₀‖ ^ 2 ≤ A' * ‖y - x₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by rw [hA']; linarith [(by positivity :
            (0 : ℝ) ≤ 2 * S.Qmax ^ 2 / σ)]) (sq_nonneg _)
        have h4 : c * ε ≤ σ / 4 := (mul_le_mul_of_nonneg_left hεs hc0).trans hceσ
        rw [← hc_def]
        linarith
    · have key := hu.const_sub_quad_le_of_classical hβ hε0 (x₀ := x₀) (a := g x₀ - 2 * σ) hA
        hKr0 (fun y hy z ↦ (S.Q_sq_mul_betaEps_le hβ hβmax heσ0 hεs.le (subset_closure hy) z).trans
          (le_abs_self _)) (fun y hy ↦ ?_) x₀ hx₀ t ht.1
      · have h2 : (2 * d * A + Kr) * t ≤ σ :=
          (mul_le_mul_of_nonneg_left htτ₂ (by positivity)).trans hτ₂A
        simp only [sub_self, norm_zero] at key
        linarith
      · have := (abs_le.1 (hgq y hy)).1
        linarith
  rw [abs_le]
  constructor <;> linarith

end PerronVariational

end
