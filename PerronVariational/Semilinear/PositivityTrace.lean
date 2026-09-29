/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.WellPosedData
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Registry.Comparison
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Monotone

/-!
# The positive phase does not jump outward at `t = 0` (Proposition 3.8(vi))

Appendix A.6 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: Lemma A.11, its proof,
and Corollary A.12.

## Main results

* `exists_lt_superKappa`: `κ_{θ̂}` can be made larger than any `1 - μ` (comment below (A.3)).
* `trapBarrier`: the radial barrier `η̂(x) = b(1 - exp((d+1)(1 - |x - x₀|²/(2r²))))`.
* `exists_lt_of_le_mul` (**Lemma A.11**): comparison on `(U ∩ B_{2r}(x₀)) × (0, τ]` with
  the stationary supersolution `Ψ_{ε,θ̂}(η̂)` (Lemma A.4, supersolution case). On the lateral
  boundary piece `Ū ∩ ∂B_{2r}(x₀)` the solution is bounded via the heat barrier
  `IsSemilinearSolution.le_add_of_lipschitzOnWith` (`u(y, t) ≤ g(y) + σ + 2dA_σ t`) instead of the
  paper's appeal to Proposition A.8, so this lemma does not depend on the attainment estimate.
* `exists_superKappa_lt_Ioc_two`: `κ_{θ̂} → 0` as `θ̂ → 1⁺`.
* `exists_lt_of_le_superKappa`: the barrier argument of Lemma A.11 with explicit trap height `b`
  and profile parameter `θ̂`; the time `trapTime d L b` does not depend on `θ̂`.
* `IsWellPreparedData.positivity_trace_small` (item (vi*) of the formal Proposition 3.8,
  increasing case): `u_ε < κ ε` on `K × [0, τ]` for every `κ > 0`, with `τ` independent of `κ`
  (`exists_lt_mul_of_nonpos`, using `g_ε = 0` near `K ⊆ U ∖ \overline{{g > 0}}`).
* `IsWellPreparedData.positivity_trace`: Proposition 3.8(vi) for the well-prepared family, from
  Lemma A.11 by a compactness (finite covering) argument. This replaces the paper's
  Corollary A.12, whose proof claims `B_{3r}(x₀) ⊆ {g_ε = 0}`; that inclusion fails near points
  `x₀ ∈ ∂U` with `g(x₀) = 0` (where `g_ε(x₀) = ε Φ_{1,θ}(0)₊ > 0` is possible), but Lemma A.11
  only needs `g_ε ≤ (1 - μ) ε` on `B_{3r}(x₀) ∩ Ū`, which holds on `{g ≤ 0}`
  (`IsWellPreparedData.le_of_nonpos`) in both the increasing and decreasing case.

The paper states Lemma A.11 with the conclusion `u_ε ≤ ε`; here it has the strict conclusion
`u_ε < ε`, because Proposition 3.8(vi) asserts the strict inequality. The paper's proof gives it:
`u_ε ≤ Ψ_{ε,θ̂}(η̂) ≤ κ ε + C e^{-c δ r/ε}` on `B_r(x₀)` with `κ = 1 - μ/2 < 1`, which is `< ε`
for `ε` small.
-/

open Set Filter Topology Metric
open scoped NNReal Gradient Laplacian ContDiff

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### The level `κ_{θ̂}` close to `1` -/

/-- `κ_{θ̂} → 1` as `θ̂ → ∞` (comment below (A.3)): for `μ ∈ (0, 1)` there is
`δ₀ ∈ (0, 1)` with `1 - μ < κ_{1/(1 - δ₀)}`. -/
theorem exists_lt_superKappa {β : ℝ → ℝ} (hβ : IsReactionProfile β) {μ : ℝ}
    (hμ : μ ∈ Ioo (0 : ℝ) 1) : ∃ δ₀ ∈ Ioo (0 : ℝ) 1, 1 - μ < superKappa β (1 / (1 - δ₀)) := by
  set q := 2 * bigBEps β 1 (1 - μ) with hq
  have hq1 : q < 1 := by
    have := hβ.bigB_lt_half (show 1 - μ < 1 by linarith [hμ.1]); linarith
  have h1q : 0 < 1 - q := by linarith
  set θh := 2 / (1 - q) + 1 with hθh
  have hθh1 : 1 < θh := by have : 0 < 2 / (1 - q) := by positivity
                           linarith
  have hθh0 : 0 < θh := by linarith
  refine ⟨1 - 1 / θh, ⟨?_, ?_⟩, ?_⟩
  · have : 1 / θh < 1 := by rw [div_lt_one hθh0]; exact hθh1
    linarith
  · have : 0 < 1 / θh := by positivity
    linarith
  have he : 1 / (1 - (1 - 1 / θh)) = θh := by rw [sub_sub_cancel, one_div_one_div]
  rw [he]
  obtain ⟨-, hspec⟩ := superKappa_spec hβ hθh1
  by_contra hle
  push Not at hle
  have hB := hβ.bigB_monotone hle
  have h1q' : 1 - q ≠ 0 := h1q.ne'
  have h2q : 2 - q ≠ 0 := by linarith
  have hst : superTheta θh = (2 - q) / (1 - q) := by
    rw [superTheta, hθh]; field_simp; ring
  have ht : (superTheta θh - 1) / superTheta θh = 1 / (2 - q) := by
    rw [hst]; field_simp; ring
  rw [ht] at hspec
  have h2 : 1 / (2 - q) ≤ q := by linarith
  rw [div_le_iff₀ (by linarith)] at h2
  nlinarith

/-! ### The radial barrier -/

/-- The radial profile `f(z) = b (1 - exp((d + 1)(1 - z/(2r²))))`. -/
noncomputable def trapProfile (d : ℕ) (r b z : ℝ) : ℝ :=
  b * (1 - Real.exp ((d + 1) * (1 - z / (2 * r ^ 2))))

/-- The barrier `η̂(x) = f(|x - x₀|²)` of the proof of Lemma A.11 (a smooth replacement of the
paper's `γ r η((x - x₀)/r)`): superharmonic where `η̂ > -b`, `η̂ ≤ -b/2` on `B̄_r(x₀)`,
`η̂ ≥ b/2` off `B_{2r}(x₀)`, and `|∇η̂| ≤ 4 b (d + 1)/r` where `|η̂| ≤ b` in `B̄_{2r}(x₀)`. -/
noncomputable def trapBarrier (x₀ : E d) (r b : ℝ) (x : E d) : ℝ :=
  trapProfile d r b (‖x - x₀‖ ^ 2)

section Barrier

variable {r b : ℝ}

theorem hasDerivAt_trapProfile (z : ℝ) :
    HasDerivAt (trapProfile d r b)
      (b * ((d + 1) / (2 * r ^ 2)) * Real.exp ((d + 1) * (1 - z / (2 * r ^ 2)))) z := by
  have h := ((((hasDerivAt_id' z).div_const (2 * r ^ 2)).const_sub 1).const_mul
    ((d : ℝ) + 1)).exp.const_sub 1 |>.const_mul b
  convert h using 1
  ring

theorem deriv_trapProfile :
    deriv (trapProfile d r b) = fun z ↦
      b * ((d + 1) / (2 * r ^ 2)) * Real.exp ((d + 1) * (1 - z / (2 * r ^ 2))) :=
  funext fun z ↦ (hasDerivAt_trapProfile z).deriv

theorem deriv_deriv_trapProfile (z : ℝ) :
    deriv (deriv (trapProfile d r b)) z =
      -(b * ((d + 1) / (2 * r ^ 2)) ^ 2 * Real.exp ((d + 1) * (1 - z / (2 * r ^ 2)))) := by
  rw [deriv_trapProfile]
  have h := ((((hasDerivAt_id' z).div_const (2 * r ^ 2)).const_sub 1).const_mul
    ((d : ℝ) + 1)).exp.const_mul (b * ((d + 1) / (2 * r ^ 2)))
  rw [h.deriv]
  ring

theorem contDiff_trapProfile {n : WithTop ℕ∞} : ContDiff ℝ n (trapProfile d r b) := by
  unfold trapProfile; fun_prop

theorem contDiff_trapBarrier (x₀ : E d) {n : WithTop ℕ∞} : ContDiff ℝ n (trapBarrier x₀ r b) :=
  contDiff_trapProfile.comp (contDiff_normSq_sub_const x₀)

theorem norm_gradient_normSq_sub (x₀ x : E d) :
    ‖∇ (fun y ↦ ‖y - x₀‖ ^ 2) x‖ = 2 * ‖x - x₀‖ := by
  rw [norm_gradient_eq_norm_fderiv, (hasFDerivAt_normSq_sub_const x₀ x).fderiv, norm_smul,
    innerSL_apply_norm]
  norm_num

theorem laplacian_trapBarrier (x₀ x : E d) :
    Δ (trapBarrier x₀ r b) x = 2 * (b * ((d + 1) / (2 * r ^ 2)) *
      Real.exp ((d + 1) * (1 - ‖x - x₀‖ ^ 2 / (2 * r ^ 2)))) *
        (d - 2 * ((d + 1) / (2 * r ^ 2)) * ‖x - x₀‖ ^ 2) := by
  have h := laplacian_comp (f := trapProfile d r b) (g := fun y ↦ ‖y - x₀‖ ^ 2) (x := x)
    contDiff_trapProfile.contDiffAt (contDiff_normSq_sub_const x₀).contDiffAt
  change Δ (fun y ↦ trapProfile d r b (‖y - x₀‖ ^ 2)) x = _
  rw [h, deriv_deriv_trapProfile, deriv_trapProfile, norm_gradient_normSq_sub,
    laplacian_normSq_sub_const, finrank_euclideanSpace_fin]
  ring

theorem norm_gradient_trapBarrier (x₀ x : E d) :
    ‖∇ (trapBarrier x₀ r b) x‖ = |b * ((d + 1) / (2 * r ^ 2)) *
      Real.exp ((d + 1) * (1 - ‖x - x₀‖ ^ 2 / (2 * r ^ 2)))| * (2 * ‖x - x₀‖) := by
  have h := (hasDerivAt_trapProfile (r := r) (b := b) (d := d) (‖x - x₀‖ ^ 2)).comp_hasFDerivAt x
    (hasFDerivAt_normSq_sub_const x₀ x)
  rw [norm_gradient_eq_norm_fderiv]
  change ‖fderiv ℝ (trapProfile d r b ∘ fun y ↦ ‖y - x₀‖ ^ 2) x‖ = _
  rw [h.fderiv, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  norm_num

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

/-- `η̂` is superharmonic where `η̂ > -b`. -/
theorem laplacian_trapBarrier_nonpos {x₀ x : E d} (hx : -b < trapBarrier x₀ r b x) :
    Δ (trapBarrier x₀ r b) x ≤ 0 := by
  rw [laplacian_trapBarrier]
  set k := ((d : ℝ) + 1) / (2 * r ^ 2) with hk
  set z := ‖x - x₀‖ ^ 2
  set h := ((d : ℝ) + 1) * (1 - z / (2 * r ^ 2)) with hh
  have hk0 : 0 < k := by positivity
  have hE : Real.exp h < 2 := by
    simp only [trapBarrier, trapProfile] at hx
    nlinarith
  have hh1 : h < 1 := by
    by_contra hcon; push Not at hcon
    linarith [Real.add_one_le_exp h]
  have hkz : k * z = ((d : ℝ) + 1) - h := by
    rw [hh, hk]; field_simp; ring
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : (d : ℝ) - 2 * k * z ≤ 0 := by linarith
  have h2 : 0 ≤ 2 * (b * k * Real.exp h) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos h2 h1

/-- Gradient bound where `|η̂| ≤ b` in `B̄_{2r}(x₀)`. -/
theorem norm_gradient_trapBarrier_le {x₀ x : E d} (hx : |trapBarrier x₀ r b x| ≤ b)
    (hxr : ‖x - x₀‖ ≤ 2 * r) : ‖∇ (trapBarrier x₀ r b) x‖ ≤ 4 * b * (d + 1) / r := by
  rw [norm_gradient_trapBarrier]
  set k := ((d : ℝ) + 1) / (2 * r ^ 2) with hk
  set h := ((d : ℝ) + 1) * (1 - ‖x - x₀‖ ^ 2 / (2 * r ^ 2)) with hh
  have hk0 : 0 < k := by positivity
  have hE : Real.exp h ≤ 2 := by
    simp only [trapBarrier, trapProfile] at hx
    have := (abs_le.1 hx).1
    nlinarith
  rw [abs_of_pos (by positivity)]
  calc b * k * Real.exp h * (2 * ‖x - x₀‖) ≤ b * k * 2 * (2 * (2 * r)) := by
        gcongr
    _ = 4 * b * (d + 1) / r := by rw [hk]; field_simp; ring

/-- `η̂ ≤ -b/2` on `B̄_r(x₀)`. -/
theorem trapBarrier_le {x₀ x : E d} (hx : ‖x - x₀‖ ≤ r) : trapBarrier x₀ r b x ≤ -(b / 2) := by
  simp only [trapBarrier, trapProfile]
  set z := ‖x - x₀‖ ^ 2
  have hz : z ≤ r ^ 2 := by
    have := norm_nonneg (x - x₀); simp only [z]; nlinarith
  have hq : z / (2 * r ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : 1 / 2 ≤ ((d : ℝ) + 1) * (1 - z / (2 * r ^ 2)) := by nlinarith
  have := Real.add_one_le_exp (((d : ℝ) + 1) * (1 - z / (2 * r ^ 2)))
  nlinarith

/-- `η̂ ≥ b/2` off `B_{2r}(x₀)`. -/
theorem le_trapBarrier {x₀ x : E d} (hx : 2 * r ≤ ‖x - x₀‖) : b / 2 ≤ trapBarrier x₀ r b x := by
  simp only [trapBarrier, trapProfile]
  set z := ‖x - x₀‖ ^ 2
  have hz : 4 * r ^ 2 ≤ z := by
    simp only [z]; nlinarith
  have hq : 2 ≤ z / (2 * r ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : ((d : ℝ) + 1) * (1 - z / (2 * r ^ 2)) ≤ -1 := by nlinarith
  have h2 : Real.exp (((d : ℝ) + 1) * (1 - z / (2 * r ^ 2))) ≤ Real.exp (-1) :=
    Real.exp_le_exp.2 h1
  have h3 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  nlinarith

/-- Global bound on `|∇η̂|` in `B̄_{2r}(x₀)`. -/
theorem norm_gradient_trapBarrier_le_of_le {x₀ x : E d} (hxr : ‖x - x₀‖ ≤ 2 * r) :
    ‖∇ (trapBarrier x₀ r b) x‖ ≤
      b * ((d + 1) / (2 * r ^ 2)) * Real.exp (d + 1) * (4 * r) := by
  rw [norm_gradient_trapBarrier]
  set k := ((d : ℝ) + 1) / (2 * r ^ 2) with hk
  set h := ((d : ℝ) + 1) * (1 - ‖x - x₀‖ ^ 2 / (2 * r ^ 2)) with hh
  have hk0 : 0 < k := by positivity
  have hhle : h ≤ d + 1 := by
    have : 0 ≤ ‖x - x₀‖ ^ 2 / (2 * r ^ 2) := by positivity
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  rw [abs_of_pos (by positivity)]
  have hE := Real.exp_le_exp.2 hhle
  calc b * k * Real.exp h * (2 * ‖x - x₀‖) ≤ b * k * Real.exp (d + 1) * (2 * (2 * r)) := by
        gcongr
    _ = _ := by ring

/-- Global bound on `|Δη̂|` in `B̄_{2r}(x₀)`. -/
theorem abs_laplacian_trapBarrier_le {x₀ x : E d} (hxr : ‖x - x₀‖ ≤ 2 * r) :
    |Δ (trapBarrier x₀ r b) x| ≤ 2 * (b * ((d + 1) / (2 * r ^ 2)) * Real.exp (d + 1)) *
      (d + 2 * ((d + 1) / (2 * r ^ 2)) * (4 * r ^ 2)) := by
  rw [laplacian_trapBarrier]
  set k := ((d : ℝ) + 1) / (2 * r ^ 2) with hk
  set h := ((d : ℝ) + 1) * (1 - ‖x - x₀‖ ^ 2 / (2 * r ^ 2)) with hh
  have hk0 : 0 < k := by positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hhle : h ≤ d + 1 := by
    have : 0 ≤ ‖x - x₀‖ ^ 2 / (2 * r ^ 2) := by positivity
    nlinarith
  have hz : ‖x - x₀‖ ^ 2 ≤ 4 * r ^ 2 := by nlinarith [norm_nonneg (x - x₀)]
  have hE := Real.exp_le_exp.2 hhle
  have h1 : |(d : ℝ) - 2 * k * ‖x - x₀‖ ^ 2| ≤ d + 2 * k * (4 * r ^ 2) := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖x - x₀‖]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (b * k * Real.exp h))]
  have h2 : 2 * (b * k * Real.exp h) ≤ 2 * (b * k * Real.exp (d + 1)) := by gcongr
  exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)

end Barrier

/-- The existence time `τ = b/(8(2dA + 1))`, `A = L²/(4 σ)`, `σ = b/8`, of the barrier argument of
Lemma A.11: up to time `τ` the heat barrier keeps `u ≤ g + b/4` (for `L`-Lipschitz data). -/
noncomputable def trapTime (d : ℕ) (L : ℝ≥0) (b : ℝ) : ℝ :=
  b / (8 * (2 * d * ((L : ℝ) ^ 2 / (4 * (b / 8))) + 1))

theorem trapTime_pos {L : ℝ≥0} {b : ℝ} (hb : 0 < b) : 0 < trapTime d L b := by
  unfold trapTime; positivity

/-- The barrier argument of **Lemma A.11** with explicit parameters: the trap height `b`, the
profile parameter `θ̂ = 1/(1 - δ₀)` (floor `κ_{θ̂}`), subject to the gradient condition
`4b(d + 1)/r ≤ (1 - δ₀) Q_min`. For any level `m > κ_{θ̂}` there is `ε₁ > 0` such that for
`0 < ε < ε₁`, every solution `u` of (3.4) with `L`-Lipschitz data `g ≤ κ_{θ̂} ε` on
`B_{3r}(x₀) ∩ Ū` satisfies `u < m ε` on `(B̄_r(x₀) ∩ Ū) × [0, trapTime d L b]`. The time does not
depend on `δ₀` or `m`.

Proof: the barrier `v = Ψ_{ε,θ̂}(η̂)` (`η̂ = trapBarrier`) is a stationary supersolution in
`V = U ∩ B_{2r}(x₀)` (Lemma A.4) with `v > κ_{θ̂} ε ≥ g` on `V̄` and `v ≥ η̂ ≥ b/2` on
`∂B_{2r}(x₀)`, where `u ≤ g + b/4 < b/2` for `t ≤ τ` by the heat barrier. Comparison on
`V × (0, τ]` gives `u ≤ v ≤ ε(κ_{θ̂} + C e^{-cb/(2ε)}) < m ε` on `B̄_r(x₀)`. -/
theorem exists_lt_of_le_superKappa (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    (L : ℝ≥0) {r b δ₀ : ℝ} (hr : 0 < r) (hb : 0 < b) (hδ₀ : δ₀ ∈ Ioo (0 : ℝ) 1)
    (hbgrad : 4 * b * (d + 1) / r ≤ (1 - δ₀) * S.Qmin) {m : ℝ}
    (hm : superKappa β (1 / (1 - δ₀)) < m) :
    ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ) (x₀ : E d),
      LipschitzOnWith L g (closure S.U) →
      (∀ x ∈ closure S.U ∩ ball x₀ (3 * r), g x ≤ superKappa β (1 / (1 - δ₀)) * ε) →
      IsSemilinearSolution S.U S.Q β ε g u →
      ∀ x ∈ closure S.U ∩ closedBall x₀ r, ∀ t ∈ Icc 0 (trapTime d L b), u (x, t) < m * ε := by
  set θh := 1 / (1 - δ₀) with hθh_def
  have hθh : 1 < θh := by
    rw [hθh_def, one_lt_div (by linarith [hδ₀.2])]; linarith [hδ₀.1]
  set κ := superKappa β θh with hκ_def
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hQmin := S.Qmin_pos
  have h1δ : 0 < 1 - δ₀ := by linarith [hδ₀.2]
  set k := ((d : ℝ) + 1) / (2 * r ^ 2) with hk
  set Lη := b * k * Real.exp (d + 1) * (4 * r) with hLη
  set Dη := 2 * (b * k * Real.exp (d + 1)) * (d + 2 * k * (4 * r ^ 2)) with hDη
  obtain ⟨ε₀, hε₀, hWP⟩ := wellPrepared_super (Qmax := S.Qmax) (L := Lη) (D := Dη) hβ hb
    hδ₀.1 hδ₀.2 hQmin
  obtain ⟨C, c, hc0, -, hC1, htail⟩ := profileSuper_tail hβ hθh
  have hC0 : 0 < C := by linarith
  set σ := b / 8 with hσ
  set A := (L : ℝ) ^ 2 / (4 * σ) with hA_def
  have hA : 0 ≤ A := by positivity
  set τ := trapTime d L b with hτ_def
  have hτ : 0 < τ := trapTime_pos hb
  have hτA : 2 * d * A * τ ≤ b / 8 := by
    rw [hτ_def, trapTime, ← hσ, ← hA_def, mul_div_assoc', div_le_div_iff₀ (by positivity)
      (by norm_num)]
    linarith [mul_nonneg (mul_nonneg hd0 hA) hb.le]
  set ε₁ := min (min ε₀ (b / 8)) ((m - κ) * (c * (b / 2)) / C) with hε₁_def
  have hε₁ : 0 < ε₁ := lt_min (lt_min hε₀ (by positivity))
    (div_pos (mul_pos (by linarith) (by positivity)) hC0)
  refine ⟨ε₁, hε₁, ?_⟩
  intro ε hε g u x₀ hgL hg3 hu x hx t ht
  have hε0 : 0 < ε := hε.1
  have hεε₀ : ε ≤ ε₀ := hε.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεb : ε ≤ b / 8 := hε.2.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεC : ε < (m - κ) * (c * (b / 2)) / C := hε.2.trans_le (min_le_right _ _)
  -- the comparison domain `V = U ∩ B_{2r}(x₀)`
  set V := S.U ∩ ball x₀ (2 * r) with hV_def
  have hVo : IsOpen V := S.isOpen.inter isOpen_ball
  have hVU : V ⊆ S.U := inter_subset_left
  have hclV : closure V ⊆ closure S.U ∩ closedBall x₀ (2 * r) :=
    (closure_inter_subset_inter_closure _ _).trans
      (inter_subset_inter_right _ closure_ball_subset_closedBall)
  have hnorm : ∀ y ∈ closure V, ‖y - x₀‖ ≤ 2 * r := fun y hy ↦
    mem_closedBall_iff_norm.1 (hclV hy).2
  -- the barrier `v = Ψ_{ε,θ̂}(η̂)`
  set η := trapBarrier x₀ r b with hη
  set v := wellPreparedSuperData β δ₀ ε η with hv
  have hW : IsWellPreparedSuper V S.Q β ε S.Qmax η v κ := by
    refine hWP V S.Q η hVo (contDiff_trapBarrier x₀) (fun y _ hy ↦
      laplacian_trapBarrier_nonpos hr hb hy) (fun y hy hyb ↦ ?_)
      (fun y hy ↦ ⟨(S.Q_mem y (subset_closure hy.1)).1, S.abs_Q_le hy.1⟩)
      (fun y hy ↦ norm_gradient_trapBarrier_le_of_le hr hb (hnorm y (subset_closure hy)))
      (fun y hy ↦ abs_laplacian_trapBarrier_le hr hb (hnorm y (subset_closure hy))) ε ⟨hε0, hεε₀⟩
    have h1 := norm_gradient_trapBarrier_le hr hb hyb (hnorm y hy)
    replace h1 := h1.trans hbgrad
    have hQy := (S.Q_mem y (hclV hy).1).1
    have h2 : ‖∇ η y‖ ^ 2 ≤ ((1 - δ₀) * S.Qmin) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : ((1 - δ₀) * S.Qmin) ^ 2 ≤ (1 - δ₀) * S.Q y ^ 2 := by
      have h4 : S.Qmin ^ 2 ≤ S.Q y ^ 2 := pow_le_pow_left₀ hQmin.le hQy 2
      have h5 : (1 - δ₀) ^ 2 ≤ 1 - δ₀ :=
        pow_le_of_le_one (by linarith [hδ₀.2]) (by linarith [hδ₀.1]) two_ne_zero
      calc ((1 - δ₀) * S.Qmin) ^ 2 = (1 - δ₀) ^ 2 * S.Qmin ^ 2 := by ring
        _ ≤ (1 - δ₀) * S.Qmin ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
        _ ≤ (1 - δ₀) * S.Q y ^ 2 := mul_le_mul_of_nonneg_left h4 h1δ.le
    exact h2.trans h3
  have hvc : Continuous v :=
    (profileSuperEps_contDiff hβ hθh).continuous.comp (contDiff_trapBarrier x₀ (n := 0)).continuous
  -- comparison on `V × (0, τ]`
  have hsub : IsSemilinearViscSubOn V S.Q β ε (Ioc 0 τ) u :=
    Registry.isSemilinearViscSubOn_of_solOn hVo exists_Ioc_subset_Ioc
      ((hu.2.1.mono_left hVU).mono Ioc_subset_Ioi_self)
  have hsuper : IsSemilinearViscSuperOn V S.Q β ε (Ioc 0 τ) (fun p ↦ v p.1) :=
    IsSemilinearViscSuperStat.isSemilinearViscSuperOn ⟨hvc.continuousOn, hW.viscSuper⟩
      exists_Ioc_subset_Ioc
  have hQV : ∃ K, LipschitzOnWith K S.Q (closure V) := by
    obtain ⟨K, hK⟩ := S.lip; exact ⟨K, hK.mono (closure_mono hVU)⟩
  have hgε : ∀ y ∈ closure S.U, ‖y - x₀‖ ≤ 2 * r → g y < v y := fun y hy hyr ↦ by
    have h1 := hg3 y ⟨hy, by rw [mem_ball, dist_eq_norm]; linarith⟩
    exact h1.trans_lt (by rw [mul_comm]; exact hW.kappa_lt y)
  have hcomp := Registry.semilinear_comparison hVo (S.isBounded.subset hVU) hτ hQV hβ hε0
    ((hu.continuousOn_Icc τ).mono (prod_mono (closure_mono hVU) subset_rfl))
    (hvc.comp continuous_fst).continuousOn hsub hsuper ?_
  swap
  · rintro ⟨y, s⟩ hp
    rcases hp with ⟨hy, hs⟩ | ⟨hy, hs⟩
    · rw [mem_singleton_iff] at hs
      simp only at hs ⊢
      subst hs
      rw [hu.2.2.1 y (hclV hy).1]
      exact (hgε y (hclV hy).1 (hnorm y hy)).le
    · rcases frontier_inter_subset _ _ hy with ⟨hyU, hyB⟩ | ⟨hyU, hyB⟩
      · rw [hu.2.2.2 y hyU s hs.1]
        exact (hgε y (frontier_subset_closure hyU)
          (mem_closedBall_iff_norm.1 (closure_ball_subset_closedBall hyB))).le
      · have hys : ‖y - x₀‖ = 2 * r := by
          have := frontier_ball_subset_sphere hyB
          rwa [mem_sphere_iff_norm] at this
        have h1 : u (y, s) ≤ g y + σ + 2 * d * A * s :=
          hu.le_add_of_lipschitzOnWith hβ hε0 hgL (σ := b / 8) (by positivity) y hyU s hs.1
        have h2 := hg3 y ⟨hyU, by rw [mem_ball, dist_eq_norm, hys]; linarith⟩
        have h3 : b / 2 ≤ v y :=
          (le_trapBarrier hr hb hys.ge).trans ((le_max_left _ _).trans (hW.bounds y).1)
        have h4 : 2 * d * A * s ≤ b / 8 :=
          (mul_le_mul_of_nonneg_left hs.2 (by positivity)).trans hτA
        have h5 : κ * ε ≤ 1 * ε :=
          mul_le_mul_of_nonneg_right (superKappa_lt_one hβ hθh).le hε0.le
        change u (y, s) ≤ v y
        linarith only [h1, h2, h3, h4, h5, hεb, hσ, hb]
  -- evaluation at `(x, t)`
  have hxV : x ∈ closure V := by
    have hxb : x ∈ ball x₀ (2 * r) := by
      rw [mem_ball]; linarith [mem_closedBall.1 hx.2]
    have := isOpen_ball.inter_closure ⟨hxb, hx.1⟩
    rwa [inter_comm] at this
  have hle : u (x, t) ≤ v x := hcomp (x, t) ⟨hxV, ht⟩
  have hηx : η x ≤ -(b / 2) := trapBarrier_le hr hb (mem_closedBall_iff_norm.1 hx.2)
  have hs0 : η x / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε0.le
  obtain ⟨htl, -, -⟩ := htail (η x / ε) hs0
  have hexp : Real.exp (c * (η x / ε)) ≤ ε / (c * (b / 2)) := by
    refine (Real.exp_le_exp.2 ?_).trans (exp_neg_div_le hc0 (by positivity) hε0)
    have hce : c * η x ≤ -(c * (b / 2)) := by
      have := mul_le_mul_of_nonneg_left hηx hc0.le; linarith
    calc c * (η x / ε) = (c * η x) / ε := by ring
      _ ≤ (-(c * (b / 2))) / ε := div_le_div_of_nonneg_right hce hε0.le
      _ = -(c * (b / 2) / ε) := by ring
  have hCε : C * (ε / (c * (b / 2))) < m - κ := by
    rw [lt_div_iff₀ hC0] at hεC
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    linarith
  calc u (x, t) ≤ v x := hle
    _ = ε * profileSuper β θh (η x / ε) := rfl
    _ ≤ ε * (κ + C * (ε / (c * (b / 2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hε0.le
        have := mul_le_mul_of_nonneg_left hexp hC0.le
        linarith
    _ < ε * m := mul_lt_mul_of_pos_left (by linarith) hε0
    _ = m * ε := mul_comm ε m


/-- **Lemma A.11**, with explicit dependence on bounds `L`, `M`
of the data: for `r > 0` and `μ ∈ (0, 1)` there are `τ > 0` and `ε₁ > 0` such that for
`0 < ε < ε₁`, every solution `u` of (3.4) with nonnegative, `L`-Lipschitz data `g ≤ M` on `Ū`
and `g ≤ (1 - μ) ε` on `B_{3r}(x₀) ∩ Ū` (`x₀ ∈ Ū`) satisfies `u(x, t) < ε` on
`(B̄_r(x₀) ∩ Ū) × [0, τ]`.

Proof: `θ̂ = 1/(1 - δ₀)` with `κ_{θ̂} > 1 - μ`; then `exists_lt_of_le_superKappa` with
`b = r(1 - δ₀)Q_min/(4(d + 1))` and level `m = 1`. -/
theorem exists_lt_of_le_mul (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) (L : ℝ≥0)
    (M : ℝ) {r μ : ℝ} (hr : 0 < r) (hμ : μ ∈ Ioo (0 : ℝ) 1) :
    ∃ τ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ) (x₀ : E d),
      x₀ ∈ closure S.U → LipschitzOnWith L g (closure S.U) →
      (∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) →
      (∀ x ∈ closure S.U ∩ ball x₀ (3 * r), g x ≤ (1 - μ) * ε) →
      IsSemilinearSolution S.U S.Q β ε g u →
      ∀ x ∈ closure S.U ∩ closedBall x₀ r, ∀ t ∈ Icc 0 τ, u (x, t) < ε := by
  obtain ⟨δ₀, hδ₀, hκμ⟩ := exists_lt_superKappa hβ hμ
  have h1δ : 0 < 1 - δ₀ := by linarith [hδ₀.2]
  have hQmin := S.Qmin_pos
  set b := r * (1 - δ₀) * S.Qmin / (4 * (d + 1)) with hb_def
  have hb : 0 < b := by positivity
  have hbgrad : 4 * b * (d + 1) / r = (1 - δ₀) * S.Qmin := by
    rw [hb_def]; field_simp
  have hθh : 1 < 1 / (1 - δ₀) := by
    rw [one_lt_div h1δ]; linarith [hδ₀.1]
  obtain ⟨ε₁, hε₁, hA⟩ := exists_lt_of_le_superKappa S hβ L hr hb hδ₀ hbgrad.le
    (m := 1) (superKappa_lt_one hβ hθh)
  refine ⟨trapTime d L b, trapTime_pos hb, ε₁, hε₁, fun ε hε g u x₀ _ hgL _ hg3 hu x hx t ht ↦ ?_⟩
  have h := hA ε hε g u x₀ hgL (fun y hy ↦ (hg3 y hy).trans
    (mul_le_mul_of_nonneg_right hκμ.le hε.1.le)) hu x hx t ht
  linarith

/-- A positive function on a finite set has a positive lower bound. -/
theorem Finset.exists_pos_le {X : Type*} (t : Finset X) (f : X → ℝ) (hf : ∀ x ∈ t, 0 < f x) :
    ∃ m > 0, ∀ x ∈ t, m ≤ f x := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a t _ ih =>
    obtain ⟨m, hm, hm'⟩ := ih fun x hx ↦ hf x (Finset.mem_insert_of_mem hx)
    refine ⟨min m (f a), lt_min hm (hf a (Finset.mem_insert_self a t)), fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hm' x hx)

namespace IsWellPreparedData

variable {S : Setting d} {g : E d → ℝ} {β : ℝ → ℝ} {increasing : Bool} {ε₀ : ℝ}
  {gε : ℝ → E d → ℝ}

/-- **Proposition 3.8(vi)** for the well-prepared family (compare Corollary A.12): for compact
`K ⊆ Ū ∖ \overline{{g > 0}}` there is `τ > 0` with `u_ε < ε` on `K × [0, τ]` for all small `ε`.
Proof: Lemma A.11 around each point of `K` and a finite subcover. -/
theorem positivity_trace (hβ : IsReactionProfile β) (hg : ContDiff ℝ 1 g)
    (h : IsWellPreparedData S g β increasing ε₀ gε) {uε : ℝ → E d × ℝ → ℝ}
    (hu : ∀ ε ∈ Ioo 0 ε₀, IsSemilinearSolution S.U S.Q β ε (gε ε) (uε ε)) :
    ∀ K : Set (E d), IsCompact K → K ⊆ closure S.U \ closure (posSet g (closure S.U)) →
      ∃ τ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ → ∀ x ∈ K, ∀ t ∈ Icc 0 τ,
        uε ε (x, t) < ε := by
  intro K hK hKsub
  obtain ⟨μ, hμ, hμle⟩ := h.le_of_nonpos
  obtain ⟨L, hL⟩ := h.exists_lipschitzOnWith hg
  obtain ⟨Mg, hMg⟩ := S.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hg.continuous.continuousOn
  -- local statement around each point of `K`
  have hloc : ∀ x₀ ∈ K, ∃ r > 0, ∃ τ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ →
      ∀ x ∈ closure S.U ∩ closedBall x₀ r, ∀ t ∈ Icc 0 τ, uε ε (x, t) < ε := by
    intro x₀ hx₀
    obtain ⟨hx₀U, hx₀P⟩ := hKsub hx₀
    obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ y ∈ ball x₀ ρ, y ∉ posSet g (closure S.U) := by
      by_contra! hcon
      exact hx₀P (Metric.mem_closure_iff.2 fun ρ hρ ↦ by
        obtain ⟨y, hy, hyP⟩ := hcon ρ hρ
        exact ⟨y, hyP, by simpa [dist_comm] using hy⟩)
    obtain ⟨τ, hτ, ε₁, hε₁, hA⟩ := exists_lt_of_le_mul S hβ L (Mg + ε₀) (r := ρ / 3)
      (by positivity) hμ
    refine ⟨ρ / 3, by positivity, τ, hτ, min ε₁ ε₀, lt_min hε₁ h.pos, fun ε hε hεε₀ ↦ ?_⟩
    have hε' : ε ∈ Ioo 0 ε₀ := ⟨hε.1, hεε₀⟩
    refine hA ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ (gε ε) (uε ε) x₀ hx₀U (hL ε hε')
      (fun x hx ↦ ⟨h.nonneg hε' hx, ?_⟩) (fun x hx ↦ ?_) (hu ε hε')
    · have h1 := (h.bounds ε hε' x hx).2
      have h2 : max (g x) 0 ≤ Mg := max_le ((le_abs_self _).trans (by simpa using hMg x hx))
        ((abs_nonneg _).trans (by simpa using hMg x hx))
      linarith [hε'.2]
    · refine hμle ε hε' x hx.1 (not_lt.1 fun hgx ↦ hball x ?_ ⟨hx.1, hgx⟩)
      exact ball_subset_ball (show 3 * (ρ / 3) ≤ ρ by linarith) hx.2
  choose! r hr τ hτ ε₁ hε₁ hH using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ ball x (r x))
    fun x hx ↦ ball_mem_nhds x (hr x hx)
  obtain ⟨τ₀, hτ₀, hτle⟩ := Finset.exists_pos_le t τ fun x hx ↦ hτ x (htK x hx)
  obtain ⟨e₀, he₀, hele⟩ := Finset.exists_pos_le t ε₁ fun x hx ↦ hε₁ x (htK x hx)
  refine ⟨τ₀, hτ₀, e₀, he₀, fun ε hε hεε₀ x hx s hs ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcover hx)
  exact hH y (htK y hy) ε ⟨hε.1, hε.2.trans_le (hele y hy)⟩ hεε₀ x
    ⟨(hKsub hx).1, ball_subset_closedBall hxy⟩ s ⟨hs.1, hs.2.trans (hτle y hy)⟩

end IsWellPreparedData

/-! ### Proposition 3.8(vi*): below every level `κ ε` -/

/-- `κ_{θ̂} → 0` as `θ̂ → 1⁺` (from `2𝓑(κ_{θ̂}) = (θ̃ - 1)/θ̃`, `θ̃ = (1 + θ̂)/2`): for every
`κ > 0` there is `θ̂ ∈ (1, 2]` with `κ_{θ̂} < κ`. Used for Proposition 3.8(vi*) and
Proposition 5.3 with the set `E*`. -/
theorem exists_superKappa_lt_Ioc_two {β : ℝ → ℝ} (hβ : IsReactionProfile β) {κ : ℝ} (hκ : 0 < κ) :
    ∃ θh ∈ Ioc (1 : ℝ) 2, superKappa β θh < κ := by
  set κ' := min κ (1 / 2) with hκ'
  have hκ'0 : 0 < κ' := lt_min hκ (by norm_num)
  set q := 2 * bigBEps β 1 κ' with hq
  have hq0 : 0 < q := by have := hβ.bigB_pos hκ'0; positivity
  set θh := 1 + min 1 q with hθh_def
  have hm0 : 0 < min 1 q := lt_min one_pos hq0
  have hθh : 1 < θh := by linarith
  refine ⟨θh, ⟨hθh, by linarith [min_le_left 1 q]⟩, ?_⟩
  obtain ⟨-, hspec⟩ := superKappa_spec hβ hθh
  have hst : superTheta θh = 1 + min 1 q / 2 := by rw [superTheta, hθh_def]; ring
  have hlt : (superTheta θh - 1) / superTheta θh < q := by
    rw [hst, div_lt_iff₀ (by positivity)]
    nlinarith [min_le_right 1 q]
  refine lt_of_lt_of_le ?_ (min_le_left κ (1 / 2))
  by_contra hle
  push Not at hle
  have := hβ.bigB_monotone hle
  linarith

theorem mem_closure_posSet_of_gradient_ne_zero {g : E d → ℝ} {U : Set (E d)} (hU : IsOpen U)
    {x : E d} (hx : x ∈ U) (hg : DifferentiableAt ℝ g x) (hgx : g x = 0) (hne : ∇ g x ≠ 0) :
    x ∈ closure (posSet g (closure U)) := by
  set v := ∇ g x with hv
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf : HasDerivAt (fun t : ℝ ↦ g (x + t • v)) (inner ℝ v v) 0 := by
    have h2 : HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℝ) • v) := by simpa using hg.hasFDerivAt
    convert h2.comp_hasDerivAt (0 : ℝ) hline using 1
    rw [hv, gradient, InnerProductSpace.toDual_symm_apply]
  have hpos : 0 < inner ℝ v v := real_inner_self_pos.2 hne
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hcont : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝[>] 0) (𝓝 x) := by
    simpa using hline.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine mem_closure_of_tendsto hcont ?_
  filter_upwards [hslope.eventually (eventually_gt_nhds hpos), self_mem_nhdsWithin,
    hcont.eventually (hU.mem_nhds hx)] with t ht ht0 htU
  refine ⟨subset_closure htU, ?_⟩
  rw [slope_def_field] at ht
  simp only [zero_smul, add_zero, sub_zero, hgx] at ht
  exact (div_pos_iff_of_pos_right (mem_Ioi.1 ht0)).1 ht

/-- A strict subsolution is negative on `U ∖ \overline{{g > 0}}`: there `g ≤ 0`, and `g = 0`
would force `∇g ≠ 0` (Definition 2.2(ii), `Q ≥ Q_min > 0`), hence `g > 0` nearby. -/
theorem IsStrictSub.neg_of_not_mem_closure {S : Setting d} {g : E d → ℝ}
    (hg : IsStrictSub S.U S.Q g) {x : E d} (hx : x ∈ S.U)
    (hxP : x ∉ closure (posSet g (closure S.U))) : g x < 0 := by
  obtain ⟨hg2, a₀, ha₀, δ₀, hδ₀, -, hgrad⟩ := hg
  have hle : g x ≤ 0 := not_lt.1 fun h ↦ hxP (subset_closure ⟨subset_closure hx, h⟩)
  refine hle.lt_of_ne fun h0 ↦ hxP (mem_closure_posSet_of_gradient_ne_zero S.isOpen hx
    ((hg2.differentiable (by norm_num)) x) h0 fun hne ↦ ?_)
  have h := hgrad x (subset_closure hx) (by rw [h0, abs_zero]; exact ha₀.le)
  rw [hne, norm_zero] at h
  have hQ := (S.Q_mem x (subset_closure hx)).1
  have := S.Qmin_pos
  nlinarith

/-- **Lemma A.11 with data vanishing near `x₀`**, for every level: for `r > 0` there is `τ > 0`
(depending on `r`, `L`, `d`, `Q_min` only) such that for every `κ > 0`, for small `ε`, every
solution `u` of (3.4) with `L`-Lipschitz data `g ≤ 0` on `B_{3r}(x₀) ∩ Ū` satisfies `u < κ ε` on
`(B̄_r(x₀) ∩ Ū) × [0, τ]`. The barrier is that of Lemma A.11 with `θ̂ ∈ (1, 2]` chosen so that
`κ_{θ̂} < κ` (`exists_superKappa_lt_Ioc_two`); the trap height `b = r Q_min/(8(d + 1))` works for
all `θ̂ ∈ (1, 2]`, so `τ = trapTime d L b` is uniform in `κ`. -/
theorem exists_lt_mul_of_nonpos (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    (L : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    ∃ τ > 0, ∀ κ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ) (x₀ : E d),
      LipschitzOnWith L g (closure S.U) →
      (∀ x ∈ closure S.U ∩ ball x₀ (3 * r), g x ≤ 0) →
      IsSemilinearSolution S.U S.Q β ε g u →
      ∀ x ∈ closure S.U ∩ closedBall x₀ r, ∀ t ∈ Icc 0 τ, u (x, t) < κ * ε := by
  have hQmin := S.Qmin_pos
  set b := r * S.Qmin / (8 * (d + 1)) with hb_def
  have hb : 0 < b := by positivity
  refine ⟨trapTime d L b, trapTime_pos hb, fun κ hκ ↦ ?_⟩
  obtain ⟨θh, hθh, hθκ⟩ := exists_superKappa_lt_Ioc_two hβ hκ
  set δ₀ := 1 - 1 / θh with hδ₀_def
  have hθ0 : 0 < θh := by linarith [hθh.1]
  have hδ₀ : δ₀ ∈ Ioo (0 : ℝ) 1 := by
    have h1 : 1 / θh < 1 := by rw [div_lt_one hθ0]; exact hθh.1
    have h2 : 0 < 1 / θh := by positivity
    constructor <;> linarith
  have hδ₀2 : δ₀ ≤ 1 / 2 := by
    have : 1 / 2 ≤ 1 / θh := one_div_le_one_div_of_le hθ0 hθh.2
    linarith
  have he : 1 / (1 - δ₀) = θh := by rw [hδ₀_def, sub_sub_cancel, one_div_one_div]
  have hbgrad : 4 * b * (d + 1) / r ≤ (1 - δ₀) * S.Qmin := by
    have : 4 * b * (d + 1) / r = S.Qmin / 2 := by rw [hb_def]; field_simp; ring
    rw [this]; nlinarith
  obtain ⟨ε₁, hε₁, hA⟩ := exists_lt_of_le_superKappa S hβ L hr hb hδ₀ hbgrad (m := κ)
    (by rwa [he])
  refine ⟨ε₁, hε₁, fun ε hε g u x₀ hgL hg3 hu ↦ hA ε hε g u x₀ hgL (fun y hy ↦ ?_) hu⟩
  rw [he]
  exact (hg3 y hy).trans (mul_pos (superKappa_pos hβ hθh.1) hε.1).le

/-- **Proposition 3.8(vi\*)** (increasing case): for compact `K ⊆ U \ \overline{{g > 0}}` there
is `τ > 0` such that for every `κ > 0`, `u_ε < κ ε` on `K × [0, τ]` for all small `ε`.

This strengthening of Proposition 3.8(vi) is not in the paper. The paper's Proposition 5.3 uses
the set `limsup* {u_ε > ε}`, and with that set it is false (an `ε`-plateau `u ≡ ε` is a stationary
solution, and a vanishing perturbation lifts it over the threshold). Here Proposition 5.3 uses the
authors' corrected set `E* = \overline{⋃_{0<κ≤1} limsup* {u_ε > κ ε}}`, and Corollary 5.4 then
needs `u_ε < κ ε` near `t = 0` off `\overline{{g > 0}}` for every `κ`, not only for `κ = 1`.

Proof: `g < 0` on `K` (`IsStrictSub.neg_of_not_mem_closure`), so around each `x₀ ∈ K`,
`g ≤ g(x₀)/2 < 0` on a ball `B_{3r}(x₀)`, where `g_ε = 0` for small `ε`
(`IsWellPreparedData.eq_zero_of_le`); then `exists_lt_mul_of_nonpos` (whose time is uniform in
`κ`) and a finite subcover chosen before `κ`. -/
theorem IsWellPreparedData.positivity_trace_small (S : Setting d) {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {g : E d → ℝ} (hg : IsStrictSub S.U S.Q g) {ε₀ : ℝ}
    {gε : ℝ → E d → ℝ} (h : IsWellPreparedData S g β true ε₀ gε) {uε : ℝ → E d × ℝ → ℝ}
    (hu : ∀ ε ∈ Ioo 0 ε₀, IsSemilinearSolution S.U S.Q β ε (gε ε) (uε ε)) :
    ∀ K : Set (E d), IsCompact K → K ⊆ S.U \ closure (posSet g (closure S.U)) →
      ∃ τ > 0, ∀ κ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ → ∀ x ∈ K, ∀ t ∈ Icc 0 τ,
        uε ε (x, t) < κ * ε := by
  intro K hK hKsub
  have hg1 : ContDiff ℝ 1 g := hg.1.of_le (by norm_num)
  obtain ⟨c, hc, hc0⟩ := h.eq_zero_of_le rfl
  obtain ⟨L, hL⟩ := h.exists_lipschitzOnWith hg1
  -- local statement around each point of `K`
  have hloc : ∀ x₀ ∈ K, ∃ r > 0, ∃ τ > 0, ∀ κ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ →
      ∀ x ∈ closure S.U ∩ closedBall x₀ r, ∀ t ∈ Icc 0 τ, uε ε (x, t) < κ * ε := by
    intro x₀ hx₀
    have hneg := hg.neg_of_not_mem_closure (hKsub hx₀).1 (hKsub hx₀).2
    obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ y ∈ ball x₀ ρ, g y < g x₀ / 2 :=
      Metric.isOpen_iff.1 (isOpen_lt hg1.continuous continuous_const) x₀
        (show g x₀ < g x₀ / 2 by linarith)
    obtain ⟨τ, hτ, hA⟩ := exists_lt_mul_of_nonpos S hβ L (r := ρ / 3) (by positivity)
    refine ⟨ρ / 3, by positivity, τ, hτ, fun κ hκ ↦ ?_⟩
    obtain ⟨ε₁, hε₁, hA'⟩ := hA κ hκ
    have hε₂ : 0 < -g x₀ / 2 / c := by
      have : 0 < -g x₀ / 2 := by linarith
      positivity
    refine ⟨min ε₁ (-g x₀ / 2 / c), lt_min hε₁ hε₂, fun ε hε hεε₀ ↦ ?_⟩
    have hε' : ε ∈ Ioo 0 ε₀ := ⟨hε.1, hεε₀⟩
    refine hA' ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ (gε ε) (uε ε) x₀ (hL ε hε')
      (fun x hx ↦ (hc0 ε hε' x hx.1 ?_).le) (hu ε hε')
    have h1 := hball x (ball_subset_ball (show 3 * (ρ / 3) ≤ ρ by linarith) hx.2)
    have h2 : c * ε ≤ -g x₀ / 2 := by
      have := (lt_min_iff.1 hε.2).2
      rw [lt_div_iff₀ hc] at this
      linarith
    linarith
  choose! r hr τ hτ hH using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ ball x (r x))
    fun x hx ↦ ball_mem_nhds x (hr x hx)
  obtain ⟨τ₀, hτ₀, hτle⟩ := Finset.exists_pos_le t τ fun x hx ↦ hτ x (htK x hx)
  refine ⟨τ₀, hτ₀, fun κ hκ ↦ ?_⟩
  have hloc' : ∀ x ∈ t, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ →
      ∀ y ∈ closure S.U ∩ closedBall x (r x), ∀ s ∈ Icc 0 (τ x), uε ε (y, s) < κ * ε :=
    fun x hx ↦ hH x (htK x hx) κ hκ
  choose! ε₁ hε₁ hH' using hloc'
  obtain ⟨e₀, he₀, hele⟩ := Finset.exists_pos_le t ε₁ hε₁
  refine ⟨e₀, he₀, fun ε hε hεε₀ x hx s hs ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcover hx)
  exact hH' y hy ε ⟨hε.1, hε.2.trans_le (hele y hy)⟩ hεε₀ x
    ⟨subset_closure (hKsub hx).1, ball_subset_closedBall hxy⟩ s ⟨hs.1, hs.2.trans (hτle y hy)⟩

end PerronVariational

end
