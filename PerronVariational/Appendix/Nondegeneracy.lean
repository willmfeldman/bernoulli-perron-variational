/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Monotone
import PerronVariational.Semilinear.PositivityTrace
import PerronVariational.Stationary.ViscosityJet
import PerronVariational.Stationary.ViscosityLocal

/-!
# Non-degeneracy of extremal solutions (Appendix B and the smallest-supersolution analogue)

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper").

* `IsNondegenerateAt u x₀`: linear growth of `u` away from the free boundary point `x₀` (the
  conclusion of **Thm B.1** of the paper, due to B. Orcan-Ekmekci, *On the geometry and regularity
  of largest subsolutions for a free boundary problem in ℝ²: elliptic case*, Calc. Var. Partial
  Differential Equations 49 (2014), no. 3-4, 937–962, doi:10.1007/s00526-013-0606-8, in local form,
  with the supremum over `∂B_r` replaced by the supremum over `B̄_r`, which is weaker).
* `IsUniformlyNondegenerateNear U u x₀`: the form of H. W. Alt, L. A. Caffarelli, *Existence and
  regularity for a minimum problem with free boundary*, J. Reine Angew. Math. 325 (1981), 105–144,
  doi:10.1515/crll.1981.325.105, uniformly at all points of `\overline{{u > 0}}` near `x₀`. This is
  what the ε-regularity step of Cor 1.2 needs: the flatness hypothesis of ε-regularity is two-sided,
  and locally uniform convergence of the rescalings to a half-plane solution gives only the lower
  bound.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- Non-degeneracy at `x₀` (Thm B.1, local form): there are `c, ρ > 0` such that for
`0 < r ≤ ρ`, `sup_{B̄_r(x₀)} u ≥ c r`. -/
def IsNondegenerateAt (u : E d → ℝ) (x₀ : E d) : Prop :=
  ∃ c > 0, ∃ ρ > 0, ∀ r, 0 < r → r ≤ ρ → ∃ y ∈ closedBall x₀ r, c * r ≤ u y

/-- Uniform non-degeneracy near `x₀` (Alt–Caffarelli form): there are `c, ρ > 0` such that for
every `z ∈ \overline{{u > 0}}` with `|z - x₀| < ρ` and `0 < r ≤ ρ`, `sup_{B̄_r(z)} u ≥ c r`. -/
def IsUniformlyNondegenerateNear (U : Set (E d)) (u : E d → ℝ) (x₀ : E d) : Prop :=
  ∃ c > 0, ∃ ρ > 0, ∀ z ∈ closure (posSet u U) ∩ ball x₀ ρ, ∀ r, 0 < r → r ≤ ρ →
    ∃ y ∈ closedBall z r, c * r ≤ u y

/-- Uniform non-degeneracy near a point of `\overline{{u > 0}}` implies non-degeneracy there. -/
theorem IsUniformlyNondegenerateNear.isNondegenerateAt {U : Set (E d)} {u : E d → ℝ}
    {x₀ : E d} (h : IsUniformlyNondegenerateNear U u x₀) (hx₀ : x₀ ∈ closure (posSet u U)) :
    IsNondegenerateAt u x₀ := by
  obtain ⟨c, hc, ρ, hρ, h⟩ := h
  exact ⟨c, hc, ρ, hρ, h x₀ ⟨hx₀, mem_ball_self hρ⟩⟩

/-! ### A radial barrier -/

section Barrier

/-- The Fréchet derivative applied to `v` is the inner product with the gradient. -/
theorem fderiv_apply_eq_inner_gradient {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (f : F → ℝ) (x v : F) : fderiv ℝ f x v = ⟪∇ f x, v⟫ := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

/-- **Gradient comparison at a common zero.** If `φ ≤ max(G, 0)` near `x` and `φ(x) = G(x) = 0`,
then `|∇φ(x)| ≤ |∇G(x)|`. -/
theorem norm_gradient_le_of_le_max {φ G : E d → ℝ} {x : E d} (hφ : DifferentiableAt ℝ φ x)
    (hG : DifferentiableAt ℝ G x) (hφx : φ x = 0) (hGx : G x = 0)
    (hle : ∀ᶠ y in 𝓝 x, φ y ≤ max (G y) 0) : ‖∇ φ x‖ ≤ ‖∇ G x‖ := by
  set p := ∇ φ x with hp
  have hl : HasDerivAt (fun s : ℝ ↦ x + s • p) p 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const p).const_add x
  have hx0 : x + (0 : ℝ) • p = x := by simp
  have ha : HasDerivAt (fun s : ℝ ↦ φ (x + s • p)) ⟪p, p⟫ 0 := by
    have := (hx0 ▸ hφ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [fderiv_apply_eq_inner_gradient, hx0] at this
    exact this
  have hb : HasDerivAt (fun s : ℝ ↦ G (x + s • p)) ⟪∇ G x, p⟫ 0 := by
    have := (hx0 ▸ hG).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [fderiv_apply_eq_inner_gradient, hx0] at this
    exact this
  have ta := ha.tendsto_slope_zero_right
  have tb := (hb.tendsto_slope_zero_right).max (tendsto_const_nhds (x := (0 : ℝ)))
  simp only [zero_add, hx0, hφx, hGx, sub_zero, smul_eq_mul] at ta tb
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * φ (x + t • p) ≤ max (t⁻¹ * G (x + t • p)) 0 := by
    have hc : Tendsto (fun s : ℝ ↦ x + s • p) (𝓝[>] 0) (𝓝 x) := by
      have := hl.continuousAt.tendsto
      rw [hx0] at this
      exact this.mono_left nhdsWithin_le_nhds
    filter_upwards [hc.eventually hle, self_mem_nhdsWithin] with t ht htpos
    have htpos' : 0 < t := htpos
    rw [show max (t⁻¹ * G (x + t • p)) 0 = t⁻¹ * max (G (x + t • p)) 0 by
      rw [mul_max_of_nonneg _ _ (inv_nonneg.2 htpos'.le), mul_zero]]
    exact mul_le_mul_of_nonneg_left ht (inv_nonneg.2 htpos'.le)
  have key : ⟪p, p⟫ ≤ max ⟪∇ G x, p⟫ 0 := le_of_tendsto_of_tendsto ta tb hev
  rw [real_inner_self_eq_norm_sq] at key
  have hcs : ⟪∇ G x, p⟫ ≤ ‖∇ G x‖ * ‖p‖ := real_inner_le_norm _ _
  rcases (norm_nonneg p).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · have : ‖p‖ ^ 2 ≤ ‖∇ G x‖ * ‖p‖ :=
      key.trans (max_le hcs (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    nlinarith

/-- The smooth radial profile `S(y) = A (1 - exp(-λ (|y - z|² - σ²)))`, `λ = d / (2σ²)`. It
vanishes on `∂B_σ(z)`, is positive outside and negative inside `B_σ(z)`, and superharmonic
outside `B_σ(z)`. -/
noncomputable def radialProfile (z : E d) (σ A : ℝ) (y : E d) : ℝ :=
  A - A * Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2)))

/-- The non-degeneracy barrier `w = max(S, 0)`: a viscosity supersolution vanishing on
`B̄_σ(z)` with free boundary slope `A d / σ`. -/
noncomputable def radialBarrier (z : E d) (σ A : ℝ) (y : E d) : ℝ :=
  max (radialProfile z σ A y) 0

theorem contDiff_radialProfile (z : E d) (σ A : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (radialProfile z σ A) := by
  have hg : ContDiff ℝ n (fun y : E d ↦ ‖y - z‖ ^ 2) := contDiff_normSq_sub_const z
  unfold radialProfile
  exact contDiff_const.sub (contDiff_const.mul (Real.contDiff_exp.comp
    ((contDiff_const.mul (hg.sub contDiff_const)).neg)))

section Profile

variable {z : E d} {σ A : ℝ}

/-- The profile as `f ∘ g` with `g(y) = |y - z|²`. -/
noncomputable def radialProfileF (σ A : ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  A - A * Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (t - σ ^ 2)))

theorem radialProfile_eq (y : E d) :
    radialProfile z σ A y = radialProfileF σ A d (‖y - z‖ ^ 2) := rfl

theorem hasDerivAt_radialProfileF (t : ℝ) :
    HasDerivAt (radialProfileF σ A d) (A * ((d : ℝ) / (2 * σ ^ 2)) *
      Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (t - σ ^ 2)))) t := by
  set lm := (d : ℝ) / (2 * σ ^ 2)
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lm * (t - σ ^ 2))) (-lm) t := by
    simpa using (((hasDerivAt_id t).sub_const (σ ^ 2)).const_mul lm).neg
  have h2 := (h1.exp.const_mul A).const_sub A
  convert h2 using 1
  ring

theorem deriv_radialProfileF : deriv (radialProfileF σ A d) = fun t ↦ A * ((d : ℝ) / (2 * σ ^ 2)) *
      Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (t - σ ^ 2))) :=
  funext fun t ↦ (hasDerivAt_radialProfileF t).deriv

theorem deriv_deriv_radialProfileF (t : ℝ) : deriv (deriv (radialProfileF σ A d)) t =
    -(A * ((d : ℝ) / (2 * σ ^ 2)) ^ 2 * Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (t - σ ^ 2)))) := by
  rw [deriv_radialProfileF]
  set lm := (d : ℝ) / (2 * σ ^ 2)
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lm * (t - σ ^ 2))) (-lm) t := by
    simpa using (((hasDerivAt_id t).sub_const (σ ^ 2)).const_mul lm).neg
  have h2 := h1.exp.const_mul (A * lm)
  rw [h2.deriv]
  ring

theorem norm_gradient_radialProfile (y : E d) :
    ‖∇ (radialProfile z σ A) y‖ = |A * ((d : ℝ) / (2 * σ ^ 2)) *
      Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2)))| * (2 * ‖y - z‖) := by
  have hcomp : HasFDerivAt (fun y ↦ radialProfileF σ A d (‖y - z‖ ^ 2))
      ((A * ((d : ℝ) / (2 * σ ^ 2)) * Real.exp (-((d : ℝ) / (2 * σ ^ 2) *
        (‖y - z‖ ^ 2 - σ ^ 2)))) • ((2 : ℝ) • innerSL ℝ (y - z))) y :=
    (hasDerivAt_radialProfileF (σ := σ) (A := A) (d := d) (‖y - z‖ ^ 2)).comp_hasFDerivAt
      (f := fun y : E d ↦ ‖y - z‖ ^ 2) y (hasFDerivAt_normSq_sub_const z y)
  have hS : radialProfile z σ A = fun y ↦ radialProfileF σ A d (‖y - z‖ ^ 2) := rfl
  rw [hS, norm_gradient_eq_norm_fderiv, hcomp.fderiv, norm_smul, norm_smul, innerSL_apply_norm,
    Real.norm_eq_abs]
  norm_num

theorem laplacian_radialProfile_nonpos (hA : 0 ≤ A) (hσ : 0 < σ) {y : E d}
    (hy : σ ≤ ‖y - z‖) : Δ (radialProfile z σ A) y ≤ 0 := by
  have hcomp := laplacian_comp (f := radialProfileF σ A d) (g := fun y : E d ↦ ‖y - z‖ ^ 2) (x := y)
    (by unfold radialProfileF; fun_prop) (contDiff_normSq_sub_const z).contDiffAt
  have hS : radialProfile z σ A = fun y ↦ radialProfileF σ A d (‖y - z‖ ^ 2) := rfl
  rw [hS, hcomp, deriv_deriv_radialProfileF, deriv_radialProfileF, norm_gradient_normSq_sub,
    laplacian_normSq_sub_const, finrank_euclideanSpace_fin]
  simp only
  set E' := Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2)))
  have hE : 0 < E' := Real.exp_pos _
  have hσ2 : 0 < σ ^ 2 := by positivity
  have ht : σ ^ 2 ≤ ‖y - z‖ ^ 2 := pow_le_pow_left₀ hσ.le hy 2
  set t := ‖y - z‖ ^ 2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- `Δ = A λ E (2d - 4 λ t)` with `λ t ≥ d/2`
  have hlt : (d : ℝ) / 2 ≤ (d : ℝ) / (2 * σ ^ 2) * t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have key : -(A * ((d : ℝ) / (2 * σ ^ 2)) ^ 2 * E') * (2 * ‖y - z‖) ^ 2 +
      A * ((d : ℝ) / (2 * σ ^ 2)) * E' * (2 * (d : ℝ)) =
      A * ((d : ℝ) / (2 * σ ^ 2)) * E' * (2 * d - 4 * ((d : ℝ) / (2 * σ ^ 2) * t)) := by
    rw [mul_pow]; ring
  rw [key]
  have hlm : 0 ≤ (d : ℝ) / (2 * σ ^ 2) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem radialProfile_pos (hA : 0 < A) (hσ : 0 < σ) (hd : 1 ≤ d) {y : E d}
    (hy : σ < ‖y - z‖) : 0 < radialProfile z σ A y := by
  unfold radialProfile
  have hlm : 0 < (d : ℝ) / (2 * σ ^ 2) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have ht : σ ^ 2 < ‖y - z‖ ^ 2 := pow_lt_pow_left₀ hy hσ.le two_ne_zero
  have : Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) < 1 :=
    Real.exp_lt_one_iff.2 (by nlinarith)
  nlinarith

theorem radialProfile_neg (hA : 0 < A) (hσ : 0 < σ) (hd : 1 ≤ d) {y : E d}
    (hy : ‖y - z‖ < σ) : radialProfile z σ A y < 0 := by
  unfold radialProfile
  have hlm : 0 < (d : ℝ) / (2 * σ ^ 2) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have ht : ‖y - z‖ ^ 2 < σ ^ 2 := pow_lt_pow_left₀ hy (norm_nonneg _) two_ne_zero
  have : 1 < Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) :=
    Real.one_lt_exp_iff.2 (by nlinarith)
  nlinarith

theorem radialProfile_eq_zero {y : E d} (hy : ‖y - z‖ = σ) : radialProfile z σ A y = 0 := by
  unfold radialProfile
  rw [hy]; simp

/-- Lower bound of the barrier away from `B_{3σ/2}(z)`: `w ≥ 5A/13`. -/
theorem le_radialProfile (hA : 0 ≤ A) (hσ : 0 < σ) (hd : 1 ≤ d) {y : E d}
    (hy : 3 * σ / 2 ≤ ‖y - z‖) : 5 * A / 13 ≤ radialProfile z σ A y := by
  unfold radialProfile
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hσ2 : 0 < σ ^ 2 := by positivity
  have ht : 9 / 4 * σ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hy 2
    linarith
  have harg : 5 / 8 ≤ (d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hexp : Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) ≤ 8 / 13 := by
    have h1 : Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) ≤
        Real.exp (-(5 / 8)) := Real.exp_le_exp.2 (by linarith)
    have h2 : (13 / 8 : ℝ) ≤ Real.exp (5 / 8) := by
      have := Real.add_one_le_exp (5 / 8 : ℝ); linarith
    have h3 : Real.exp (-(5 / 8 : ℝ)) ≤ 8 / 13 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    linarith
  nlinarith

end Profile

/-- **The barrier is a viscosity supersolution** wherever `Q ≥ A d / σ`. -/
theorem isViscSuper_radialBarrier {W : Set (E d)} (hW : IsOpen W) {Q : E d → ℝ} {z : E d}
    {σ A : ℝ} (hA : 0 < A) (hσ : 0 < σ) (hd : 1 ≤ d) (hQ : ∀ x ∈ W, A * d / σ ≤ Q x) :
    IsViscSuper W Q (radialBarrier z σ A) := by
  have hSc : ContDiff ℝ ∞ (radialProfile z σ A) := contDiff_radialProfile z σ A
  refine ⟨(hSc.continuous.max continuous_const).continuousOn, fun _ _ ↦ le_max_right _ _, ?_⟩
  intro φ hφ x hx htouch
  have hle := htouch.eventually_le_of_isOpen hW
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_of_smooth hφ
  have hcont : Continuous fun y : E d ↦ ‖y - z‖ := continuous_norm.comp (continuous_sub_right z)
  rcases lt_trichotomy ‖x - z‖ σ with hlt | heq | hgt
  · left
    have hnear : ∀ᶠ y in 𝓝 x, ‖y - z‖ < σ := hcont.continuousAt.eventually (gt_mem_nhds hlt)
    have hφx : φ x = 0 := by
      rw [htouch.2.1, radialBarrier, max_eq_right (radialProfile_neg hA hσ hd hlt).le]
    refine IsLocalMax.laplacian_nonpos hφ2 ?_
    filter_upwards [hle, hnear] with y hy hy'
    rw [hφx]
    rwa [radialBarrier, max_eq_right (radialProfile_neg hA hσ hd hy').le] at hy
  · right
    have hS0 : radialProfile z σ A x = 0 := radialProfile_eq_zero heq
    have hφx : φ x = 0 := by rw [htouch.2.1, radialBarrier, hS0, max_self]
    refine ⟨hφx, ?_⟩
    have h := norm_gradient_le_of_le_max (hφ.differentiable (by simp)).differentiableAt
      (hSc.differentiable (by simp)).differentiableAt hφx hS0 hle
    rw [norm_gradient_radialProfile, heq] at h
    refine h.trans (le_of_eq_of_le ?_ (hQ x hx))
    simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    rw [abs_of_nonneg (by positivity)]
    field_simp
  · left
    have hnear : ∀ᶠ y in 𝓝 x, σ < ‖y - z‖ := hcont.continuousAt.eventually (lt_mem_nhds hgt)
    have hx' : φ x = radialProfile z σ A x := by
      rw [htouch.2.1, radialBarrier, max_eq_left (radialProfile_pos hA hσ hd hgt).le]
    refine (laplacian_le_of_eventually_le hφ2.contDiffAt
      (contDiff_two_of_smooth hSc).contDiffAt hx' ?_).trans
      (laplacian_radialProfile_nonpos hA.le hσ hgt.le)
    filter_upwards [hle, hnear] with y hy hy'
    rwa [radialBarrier, max_eq_left (radialProfile_pos hA hσ hd hy').le] at hy

theorem radialBarrier_eq_zero {z : E d} {σ A : ℝ} (hA : 0 < A) (hσ : 0 < σ) (hd : 1 ≤ d)
    {y : E d} (hy : ‖y - z‖ ≤ σ) : radialBarrier z σ A y = 0 := by
  rcases hy.lt_or_eq with h | h
  · exact max_eq_right (radialProfile_neg hA hσ hd h).le
  · rw [radialBarrier, radialProfile_eq_zero h, max_self]

/-- The minimum of two viscosity supersolutions is a viscosity supersolution. -/
theorem IsViscSuper.min {W : Set (E d)} {Q u w : E d → ℝ} (hu : IsViscSuper W Q u)
    (hw : IsViscSuper W Q w) : IsViscSuper W Q (fun y ↦ min (u y) (w y)) := by
  refine ⟨ContinuousOn.inf hu.1 hw.1, fun x hx ↦ le_min (hu.2.1 x hx) (hw.2.1 x hx), ?_⟩
  intro φ hφ x hx htouch
  rcases le_total (u x) (w x) with h | h
  · exact hu.2.2 φ hφ x hx ⟨hx, by rw [htouch.2.1]; exact min_eq_left h,
      htouch.2.2.mono fun y hy ↦ hy.trans (min_le_left _ _)⟩
  · exact hw.2.2 φ hφ x hx ⟨hx, by rw [htouch.2.1]; exact min_eq_right h,
      htouch.2.2.mono fun y hy ↦ hy.trans (min_le_right _ _)⟩

end Barrier

/-! ### Lemma B.2: non-degeneracy of subsolutions at outer-regular points -/

section OuterRegular

/-- The radial profile `H(y) = A (1 - exp(-λ (|y - p|² - σ²)))` with a general rate `λ`. -/
noncomputable def expProfile (p : E d) (σ lam A : ℝ) (y : E d) : ℝ :=
  A - A * Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2)))

/-- `expProfile` as a function of `t = |y - p|²`. -/
noncomputable def expProfileF (σ lam A : ℝ) (t : ℝ) : ℝ :=
  A - A * Real.exp (-(lam * (t - σ ^ 2)))

variable {p : E d} {σ lam A : ℝ}

theorem contDiff_expProfile {n : WithTop ℕ∞} : ContDiff ℝ n (expProfile p σ lam A) := by
  have hg : ContDiff ℝ n (fun y : E d ↦ ‖y - p‖ ^ 2) := contDiff_normSq_sub_const p
  unfold expProfile
  exact contDiff_const.sub (contDiff_const.mul (Real.contDiff_exp.comp
    ((contDiff_const.mul (hg.sub contDiff_const)).neg)))

theorem hasDerivAt_expProfileF (t : ℝ) :
    HasDerivAt (expProfileF σ lam A) (A * lam * Real.exp (-(lam * (t - σ ^ 2)))) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lam * (t - σ ^ 2))) (-lam) t := by
    simpa using (((hasDerivAt_id t).sub_const (σ ^ 2)).const_mul lam).neg
  have h2 := (h1.exp.const_mul A).const_sub A
  convert h2 using 1
  ring

theorem deriv_expProfileF :
    deriv (expProfileF σ lam A) = fun t ↦ A * lam * Real.exp (-(lam * (t - σ ^ 2))) :=
  funext fun t ↦ (hasDerivAt_expProfileF t).deriv

theorem deriv_deriv_expProfileF (t : ℝ) :
    deriv (deriv (expProfileF σ lam A)) t = -(A * lam ^ 2 * Real.exp (-(lam * (t - σ ^ 2)))) := by
  rw [deriv_expProfileF]
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lam * (t - σ ^ 2))) (-lam) t := by
    simpa using (((hasDerivAt_id t).sub_const (σ ^ 2)).const_mul lam).neg
  rw [(h1.exp.const_mul (A * lam)).deriv]
  ring

theorem norm_gradient_expProfile (y : E d) :
    ‖∇ (expProfile p σ lam A) y‖ =
      |A * lam * Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2)))| * (2 * ‖y - p‖) := by
  have hcomp : HasFDerivAt (fun y ↦ expProfileF σ lam A (‖y - p‖ ^ 2))
      ((A * lam * Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2)))) • ((2 : ℝ) • innerSL ℝ (y - p))) y :=
    (hasDerivAt_expProfileF (σ := σ) (lam := lam) (A := A) (‖y - p‖ ^ 2)).comp_hasFDerivAt
      (f := fun y : E d ↦ ‖y - p‖ ^ 2) y (hasFDerivAt_normSq_sub_const p y)
  have hS : expProfile p σ lam A = fun y ↦ expProfileF σ lam A (‖y - p‖ ^ 2) := rfl
  rw [hS, norm_gradient_eq_norm_fderiv, hcomp.fderiv, norm_smul, norm_smul, innerSL_apply_norm,
    Real.norm_eq_abs]
  norm_num

/-- `ΔH = A λ E (2d - 4 λ |y - p|²)`, `E = exp(-λ(|y - p|² - σ²))`. -/
theorem laplacian_expProfile (y : E d) :
    Δ (expProfile p σ lam A) y = A * lam * Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2))) *
      (2 * d - 4 * lam * ‖y - p‖ ^ 2) := by
  have hcomp := laplacian_comp (f := expProfileF σ lam A) (g := fun y : E d ↦ ‖y - p‖ ^ 2)
    (x := y) (by unfold expProfileF; fun_prop) (contDiff_normSq_sub_const p).contDiffAt
  have hS : expProfile p σ lam A = fun y ↦ expProfileF σ lam A (‖y - p‖ ^ 2) := rfl
  rw [hS, hcomp, deriv_deriv_expProfileF, deriv_expProfileF, norm_gradient_normSq_sub,
    laplacian_normSq_sub_const, finrank_euclideanSpace_fin]
  simp only
  ring

theorem expProfile_eq_zero {y : E d} (hy : ‖y - p‖ = σ) : expProfile p σ lam A y = 0 := by
  unfold expProfile
  rw [hy]; simp

theorem expProfile_neg (hA : 0 < A) (hlam : 0 < lam) {y : E d}
    (hy : ‖y - p‖ < σ) : expProfile p σ lam A y < 0 := by
  unfold expProfile
  have ht : ‖y - p‖ ^ 2 < σ ^ 2 := pow_lt_pow_left₀ hy (norm_nonneg _) two_ne_zero
  have : 1 < Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2))) :=
    Real.one_lt_exp_iff.2 (by nlinarith)
  nlinarith

/-- **Lemma B.2**, quantitative form. Let `v` be a viscosity
subsolution of (1.1) in `B_{4s}(x₀)` with `Q ≥ q₀ > 0`, `x₀` a free boundary point, and
`B_s(p)` an exterior touching ball at `x₀` (`|x₀ - p| = s`, `v = 0` in `B_s(p)`). Then
`sup_{B_{4s}(x₀)} v ≥ c s` with `c = q₀ / (32 d e^{3d})`.

The paper states the lemma without proof, with exterior ball and domain of the same radius; here we
prove it with an explicit barrier. The paper's version follows by applying this one to the exterior
ball of radius `1/4` inside the given one.

Proof: the radial barrier `H = A (1 - exp(-λ(|y - p|² - s²)))`, `λ = 4d/s²`, is strictly
superharmonic off `B_{s/2}(p)` with `|∇H| ≤ q₀/2` where `H < 0`; if `v < A/2` then
`v ≤ H₊` on `B_{4s}(x₀)` (`IsViscSub.le_max_of_barrier`), and `H₊` then touches `v` from above
at `x₀` with `ΔH(x₀) < 0` and `|∇H(x₀)| < Q(x₀)`, contradicting the subsolution property. -/
theorem exists_le_of_exteriorBall (hd : 1 ≤ d) {Q v : E d → ℝ} {x₀ p : E d} {s q₀ : ℝ}
    (hs : 0 < s) (hq₀ : 0 < q₀) (hv : IsViscSub (ball x₀ (4 * s)) Q v)
    (hQ : ∀ y ∈ ball x₀ (4 * s), q₀ ≤ Q y) (hx₀ : x₀ ∈ freeBoundary v (ball x₀ (4 * s)))
    (hp : ‖x₀ - p‖ = s) (hext : ∀ y ∈ ball p s ∩ ball x₀ (4 * s), v y = 0) :
    ∃ y ∈ ball x₀ (4 * s), q₀ / (32 * d * Real.exp (3 * d)) * s ≤ v y := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set W := ball x₀ (4 * s) with hW
  set lam : ℝ := 4 * d / s ^ 2 with hlam_def
  have hs2 : 0 < s ^ 2 := by positivity
  have hlam : 0 < lam := by positivity
  set eD := Real.exp (3 * d) with heD
  have heD1 : 1 ≤ eD := Real.one_le_exp (by positivity)
  set A : ℝ := q₀ * s / (16 * d * eD) with hA_def
  have hA : 0 < A := by positivity
  set H := expProfile p s lam A with hH_def
  have hHs : ContDiff ℝ ∞ H := contDiff_expProfile
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  -- `c s = A / 2`
  have hcA : q₀ / (32 * d * eD) * s = A / 2 := by rw [hA_def]; field_simp; norm_num
  rw [hcA] at hcon
  set K := closedBall x₀ (3 * s) \ ball p (s / 2) with hK_def
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hKW : K ⊆ W := fun y hy ↦ closedBall_subset_ball (by linarith) hy.1
  have hvx₀ : v x₀ = 0 := eq_zero_of_mem_freeBoundary isOpen_ball hv.1 hv.2.1 hx₀
  -- on `K`, `|y - p| ≥ s/2`
  have hKp : ∀ y ∈ K, s / 2 ≤ ‖y - p‖ := fun y hy ↦ by
    have := hy.2; rw [mem_ball, not_lt, dist_eq_norm] at this; exact this
  have hlap : ∀ y ∈ K, Δ H y < 0 := fun y hy ↦ by
    rw [hH_def, laplacian_expProfile]
    have h1 : s ^ 2 / 4 ≤ ‖y - p‖ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) (hKp y hy) 2; linarith
    have h2 : 2 * (d : ℝ) - 4 * lam * ‖y - p‖ ^ 2 < 0 := by
      have : d ≤ lam * ‖y - p‖ ^ 2 := by
        rw [hlam_def, div_mul_eq_mul_div, le_div_iff₀ hs2]; nlinarith
      linarith
    exact mul_neg_of_pos_of_neg (by positivity) h2
  -- gradient bound where `H ≤ 0`
  have hgradle : ∀ y, s / 2 ≤ ‖y - p‖ → ‖y - p‖ ≤ s → ‖∇ H y‖ ≤ q₀ / 2 := fun y h1 h2 ↦ by
    rw [hH_def, norm_gradient_expProfile]
    have hE : Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) ≤ eD := by
      rw [heD]; refine Real.exp_le_exp.2 ?_
      have : s ^ 2 / 4 ≤ ‖y - p‖ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) h1 2; linarith
      have : lam * (s ^ 2 - ‖y - p‖ ^ 2) ≤ lam * (3 / 4 * s ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam.le
      have hl : lam * (3 / 4 * s ^ 2) = 3 * d := by rw [hlam_def]; field_simp
      linarith
    rw [abs_of_nonneg (by positivity)]
    calc A * lam * Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) * (2 * ‖y - p‖)
        ≤ A * lam * eD * (2 * s) := by gcongr
      _ = q₀ / 2 := by rw [hA_def, hlam_def]; field_simp; ring
  have hgrad : ∀ y ∈ K, H y < 0 → ‖∇ H y‖ < Q y := fun y hy hHy ↦ by
    have hlt : ‖y - p‖ < s := by
      by_contra h
      push Not at h
      have : 0 ≤ H y := by
        rw [hH_def]; unfold expProfile
        have : Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have := pow_le_pow_left₀ hs.le h 2
          nlinarith
        nlinarith
      linarith
    exact (hgradle y (hKp y hy) hlt.le).trans_lt
      (by linarith [hQ y (hKW hy)])
  -- outside `K`
  have hout : ∀ y ∈ W \ K, v y ≤ max (H y) 0 := by
    rintro y ⟨hyW, hyK⟩
    by_cases hyp : y ∈ ball p (s / 2)
    · rw [hext y ⟨ball_subset_ball (by linarith) hyp, hyW⟩]; exact le_max_right _ _
    · have hy3 : 3 * s < ‖y - x₀‖ := by
        by_contra h
        push Not at h
        exact hyK ⟨by rw [mem_closedBall, dist_eq_norm]; exact h, hyp⟩
      have hyp2 : 2 * s < ‖y - p‖ := by
        have := norm_add_le (y - p) (p - x₀)
        rw [sub_add_sub_cancel, norm_sub_rev p x₀, hp] at this
        linarith
      refine (hcon y hyW).le.trans (le_trans ?_ (le_max_left _ _))
      rw [hH_def]; unfold expProfile
      have h4 : 4 * s ^ 2 ≤ ‖y - p‖ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hyp2.le 2; linarith
      have h12 : 12 ≤ lam * (‖y - p‖ ^ 2 - s ^ 2) := by
        have : lam * (3 * s ^ 2) = 12 * d := by rw [hlam_def]; field_simp; ring
        have : lam * (3 * s ^ 2) ≤ lam * (‖y - p‖ ^ 2 - s ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hlam.le
        linarith
      have hE : Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) ≤ 1 / 2 := by
        have h1 : Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) ≤ Real.exp (-1) :=
          Real.exp_le_exp.2 (by linarith)
        have h2 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          have := Real.add_one_le_exp (1 : ℝ); linarith
        linarith
      nlinarith
  have hle := hv.le_max_of_barrier (by omega) isOpen_ball hKc hKW (contDiff_two_of_smooth hHs)
    hlap hgrad hout
  -- touching at `x₀`
  have hx₀K : ∀ y ∈ ball x₀ (s / 2), y ∈ K := fun y hy ↦ by
    rw [mem_ball, dist_eq_norm] at hy
    refine ⟨by rw [mem_closedBall, dist_eq_norm]; linarith, fun hyp ↦ ?_⟩
    rw [mem_ball, dist_eq_norm] at hyp
    have := norm_add_le (x₀ - y) (y - p)
    rw [sub_add_sub_cancel, hp, norm_sub_rev x₀ y] at this
    linarith
  have hHx₀ : H x₀ = 0 := expProfile_eq_zero hp
  have htouch : TouchesAbove (fun y ↦ max (H y) 0) v (closure (posSet v W) ∩ W) x₀ := by
    refine ⟨⟨frontier_subset_closure hx₀.1, mem_ball_self (by positivity)⟩,
      by simp only [hHx₀, max_self, hvx₀], ?_⟩
    refine mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (ball_mem_nhds x₀ (by positivity))
      fun y hy ↦ hle y (hx₀K y hy))
  rcases hv.2.2 H hHs x₀ htouch with h1 | ⟨-, h2⟩
  · have := hlap x₀ (hx₀K x₀ (mem_ball_self (by positivity)))
    linarith
  · have h3 := hgradle x₀ (by rw [hp]; linarith) hp.le
    have := hQ x₀ (mem_ball_self (by positivity))
    linarith

/-- **Lemma B.2**, in the paper's form: exterior touching ball
and domain of the same radius `s` (the paper takes `s = 1`). The conclusion is for the supremum
over the open ball `B_s(x₀)`; the paper's `max_{∂B_1} u` presumes `u` defined up to `∂B_1`. Proof:
the exterior ball `B_{s/4}(p')`, `p' = x₀ + (p - x₀)/4`, lies inside `B_s(p)`; apply
`exists_le_of_exteriorBall` with radius `s/4`. -/
theorem exists_le_of_exteriorBall_sameRadius (hd : 1 ≤ d) {Q v : E d → ℝ} {x₀ p : E d}
    {s q₀ : ℝ} (hs : 0 < s) (hq₀ : 0 < q₀) (hv : IsViscSub (ball x₀ s) Q v)
    (hQ : ∀ y ∈ ball x₀ s, q₀ ≤ Q y) (hx₀ : x₀ ∈ freeBoundary v (ball x₀ s))
    (hp : ‖x₀ - p‖ = s) (hext : ∀ y ∈ ball p s ∩ ball x₀ s, v y = 0) :
    ∃ y ∈ ball x₀ s, q₀ / (128 * d * Real.exp (3 * d)) * s ≤ v y := by
  set p' : E d := x₀ + (1 / 4 : ℝ) • (p - x₀) with hp'
  have h4 : 4 * (s / 4) = s := by ring
  have hp'n : ‖x₀ - p'‖ = s / 4 := by
    rw [hp', sub_add_cancel_left, norm_neg, norm_smul, ← norm_neg (p - x₀), neg_sub, hp]
    norm_num; ring
  have hp'p : ‖p' - p‖ = 3 * s / 4 := by
    have : p' - p = (3 / 4 : ℝ) • (x₀ - p) := by
      rw [hp']; module
    rw [this, norm_smul, hp]; norm_num; ring
  have hsub : ball p' (s / 4) ⊆ ball p s := fun y hy ↦ by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have := norm_add_le (y - p') (p' - p)
    rw [sub_add_sub_cancel] at this
    linarith
  obtain ⟨y, hy, hle⟩ := exists_le_of_exteriorBall hd (by positivity : 0 < s / 4) hq₀
    (by rwa [h4]) (by rwa [h4]) (by rwa [h4]) hp'n
    (fun y hy ↦ hext y ⟨hsub hy.1, by rw [← h4]; exact hy.2⟩)
  refine ⟨y, by rwa [h4] at hy, le_of_eq_of_le ?_ hle⟩
  field_simp
  ring

end OuterRegular

/-! ### Non-degeneracy of smallest supersolutions -/

/-- **Uniform non-degeneracy of Perron's smallest supersolution near its free boundary.**
Not stated in the paper, but needed for Cor 1.2(i). The paper's proof sketch of Cor 1.2(i)
excludes the two-plane blow-ups `α|x·e|` with `α > 0`, but not the degenerate blow-up `φ₀ ≡ 0`,
and the ε-regularity step needs the upper flatness bound, which uniform convergence of the
rescalings does not give. Uniform non-degeneracy settles both, so Cor 1.2(i) holds as stated.

Proof route (barrier): if `sup_{B̄_r(z)} u < c r` for `z ∈ \overline{{u > 0}}`, replace `u` in
`B_r(z)` by `min(u, w)` with the radial supersolution
`w(x) = A (1 - (ρ/|x - z|)^{2d})₊`, `ρ = r/2`, `A = Q_min ρ / (4d)`, which vanishes on `B_ρ(z)`;
the local smallest supersolution property (Lemma 2.7) gives `u ≤ w`, so `u = 0` on `B_ρ(z)`. -/
theorem Setting.perronSmallest_uniformlyNondegenerate (S : Setting d) {g : E d → ℝ}
    (hg : IsStrictSub S.U S.Q g) (hsuper : IsViscSuper S.U S.Q (perronSmallest S.U S.Q g))
    (hcont : ContinuousOn (perronSmallest S.U S.Q g) (closure S.U)) {x₀ : E d}
    (hx₀ : x₀ ∈ freeBoundary (perronSmallest S.U S.Q g) S.U) :
    IsUniformlyNondegenerateNear S.U (perronSmallest S.U S.Q g) x₀ := by
  classical
  set u := perronSmallest S.U S.Q g with hu_def
  have hd : 1 ≤ d := by linarith [S.two_le]
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hQmin := S.Qmin_pos
  obtain ⟨R, hR, hRU, hls⟩ := S.perronSmallest_isLocalSmallestSuper_near_fb hg hsuper hcont hx₀
  refine ⟨S.Qmin / (8 * d), by positivity, R / 4, by positivity, ?_⟩
  rintro z ⟨hzcl, hzB⟩ r hr hrρ
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set σ := r / 2 with hσ_def
  have hσ : 0 < σ := by positivity
  set A := S.Qmin * σ / d with hA_def
  have hA : 0 < A := by positivity
  rw [mem_ball] at hzB
  have hball : closedBall z r ⊆ ball x₀ R := fun y hy ↦ by
    rw [mem_closedBall] at hy
    rw [mem_ball]
    linarith [dist_triangle y z x₀]
  have hbU : ball x₀ R ⊆ S.U := ball_subset_closedBall.trans hRU
  have hWsub : ball z r ⊆ ball x₀ R := ball_subset_closedBall.trans hball
  have hbar : IsViscSuper (ball z r) S.Q (radialBarrier z σ A) := by
    refine isViscSuper_radialBarrier isOpen_ball hA hσ hd fun x hx ↦ ?_
    have : A * d / σ = S.Qmin := by rw [hA_def]; field_simp
    rw [this]
    exact (S.Q_mem x (subset_closure (hbU (hWsub hx)))).1
  have hmin : IsViscSuper (ball z r) S.Q (fun y ↦ min (u y) (radialBarrier z σ A y)) :=
    (hls.1.mono isOpen_ball hWsub).min hbar
  have heq : ∀ y ∈ ball z r \ closedBall z (3 * r / 4),
      min (u y) (radialBarrier z σ A y) = u y := by
    rintro y ⟨hy1, hy2⟩
    rw [mem_closedBall, not_le, dist_eq_norm] at hy2
    refine min_eq_left ((hcon y (ball_subset_closedBall hy1)).le.trans ?_)
    have h1 := le_radialProfile (z := z) hA.le hσ hd (y := y) (by rw [hσ_def]; linarith)
    refine le_trans ?_ (h1.trans (le_max_left _ _))
    rw [hA_def, hσ_def]
    have hX : 0 < S.Qmin * r / d := by positivity
    have e1 : S.Qmin / (8 * d) * r = (S.Qmin * r / d) / 8 := by field_simp
    have e2 : 5 * (S.Qmin * (r / 2) / d) / 13 = 5 * (S.Qmin * r / d) / 26 := by
      field_simp; ring
    rw [e1, e2]; linarith
  have hK : closedBall z (3 * r / 4) ⊆ ball z r := closedBall_subset_ball (by linarith)
  have hv := isViscSuper_piecewise isOpen_ball isOpen_ball hWsub isClosed_closedBall hK hls.1
    hmin heq
  have hcomp := hls.2 z r hr hball _ hv fun y hy ↦ piecewise_eq_of_notMem _ _ _ hy.2
  -- `u` vanishes on `B_σ(z)`, contradicting `z ∈ \overline{{u > 0}}`
  obtain ⟨y, hyσ, hyU, hypos⟩ := mem_closure_iff_nhds.1 hzcl (ball z σ) (ball_mem_nhds z hσ)
  have hyr : y ∈ ball z r := ball_subset_ball (by linarith) hyσ
  have h1 := hcomp y (hWsub hyr)
  rw [piecewise_eq_of_mem _ _ _ hyr] at h1
  have h2 : radialBarrier z σ A y = 0 :=
    radialBarrier_eq_zero hA hσ hd (by rw [← dist_eq_norm]; exact (mem_ball.1 hyσ).le)
  have h3 := h1.trans ((min_le_right _ _).trans h2.le)
  exact absurd hypos (not_lt.2 h3)

/-! ### Theorem B.1 -/

/-- **Thm B.1** (Orcan-Ekmekci) for Perron's largest
subsolution, in local form: in `d = 2`, the largest subsolution below a smooth strict
supersolution is non-degenerate at each free boundary point. Proved in
`Appendix/NondegeneracyLargest.lean` (`largestSub_nondegenerate_of`) and `Main/Corollary2D.lean`
(`largestSub_nondegenerate`). -/
def LargestSubNondegenerateStatement : Prop :=
  ∀ (S : Setting 2) (g : E 2 → ℝ), IsStrictSuper S.U S.Q g →
    ∀ x₀ ∈ freeBoundary (perronLargest S.U S.Q g) S.U,
      IsNondegenerateAt (perronLargest S.U S.Q g) x₀

end PerronVariational

end
