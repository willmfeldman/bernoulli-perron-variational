/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.BernsteinCutoff
public import PerronVariational.Defs.Parabolic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Semilinear.Profiles

/-!
# The Bernstein estimates for smooth solutions (Propositions A.5–A.6, smooth case)

The joint proof of Propositions A.5 and A.6 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.4),
for smooth `Q`, so that the solution is smooth in the interior (interior smoothness of classical
solutions, `Registry.semilinear_contDiffOn_of_contDiff`, from parabolic-basic-theory v0.1.0).

* `bernstein_interior_smooth`: Proposition A.5 for solutions which are `C^∞`
  on `B_{2r} × (t₀ - 4r², ∞)`.
* `bernstein_initial_smooth`: Proposition A.6 for solutions which
  are `C^∞` on `B_{2r} × (a, ∞)` and whose spatial gradient is continuous up to `t = a`.

The constants depend only on `d`, `β`, `Q_max` and a bound `N` for `|∇(Q²)|`, not on `ε`, `r`,
the solution or the time interval.

We do not rescale to unit scale: the proof runs at scale `r` with the Bernstein function `φ`
built from `ε' = min(ε, r)`, which also covers Step 5 of the paper (the case `ε ≥ r`) without a
separate argument.

Proof structure: `z = η² |∇u|²/Φ'(Φ⁻¹(u))²` (`BernsteinMax.wGlob`, with the cutoff
`BernsteinMax.etaFun`) is continuous on the compact cylinder, so it attains its maximum; at a
positive maximum either `t = a` (Proposition A.6: `z ≤ L²`) or the derivative tests apply and
`BernsteinMax.zmax_bound` gives `z ≤ K₀ (1 + 4M/r)²`; on the inner cylinder `η = 1` and
`|∇u|² ≤ e² z`.
-/

open Set Filter Topology Metric
open scoped NNReal ContDiff Gradient

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

open BernsteinMax Bernstein

/-- `|y|² ≤ 3r²` implies `|y| < 2r`. -/
theorem norm_lt_two_mul_of_sq_lt {y r : ℝ} (hr : 0 < r) (hy0 : 0 ≤ y) (h : y ^ 2 ≤ 3 * r ^ 2) :
    y < 2 * r := by
  by_contra h'
  push Not at h'
  nlinarith

/-- `C = 4e√K₀` bounds the gradient from `z ≤ K₀(1 + 4M/r)²`. -/
theorem norm_le_of_sq_le {g K₀ M r : ℝ} (hg : 0 ≤ g) (hK₀ : 1 ≤ K₀) (hM : 0 ≤ M) (hr : 0 < r)
    (h : g ^ 2 ≤ Real.exp 1 ^ 2 * (K₀ * (1 + 4 * M / r) ^ 2)) :
    g ≤ 4 * Real.exp 1 * Real.sqrt K₀ * (M / r + 1) := by
  have hK0 : 0 ≤ K₀ := by linarith
  have hMr : 0 ≤ M / r := by positivity
  have e : Real.exp 1 ^ 2 * (K₀ * (1 + 4 * M / r) ^ 2) =
      (Real.exp 1 * Real.sqrt K₀ * (1 + 4 * M / r)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hK0]; ring
  rw [e] at h
  have h1 : g ≤ Real.exp 1 * Real.sqrt K₀ * (1 + 4 * M / r) :=
    (pow_le_pow_iff_left₀ hg (by positivity) two_ne_zero).1 h
  refine h1.trans ?_
  have : 1 + 4 * M / r ≤ 4 * (M / r + 1) := by
    have : 4 * M / r = 4 * (M / r) := by ring
    rw [this]; linarith
  have h2 : 0 ≤ Real.exp 1 * Real.sqrt K₀ := by positivity
  calc Real.exp 1 * Real.sqrt K₀ * (1 + 4 * M / r)
        ≤ Real.exp 1 * Real.sqrt K₀ * (4 * (M / r + 1)) :=
        mul_le_mul_of_nonneg_left this h2
    _ = 4 * Real.exp 1 * Real.sqrt K₀ * (M / r + 1) := by ring

/-- Final numeric step of Proposition A.6. -/
theorem norm_le_of_sq_le_max {g K₀ M r L : ℝ} (hg : 0 ≤ g) (hK₀ : 1 ≤ K₀) (hM : 0 ≤ M)
    (hr : 0 < r) (hL : 0 ≤ L)
    (h : g ^ 2 ≤ Real.exp 1 ^ 2 * max (L ^ 2) (K₀ * (1 + 4 * M / r) ^ 2)) :
    g ≤ 4 * Real.exp 1 * Real.sqrt K₀ * (L + M / r + 1) := by
  have hK0 : 0 ≤ K₀ := by linarith
  have hsK : 1 ≤ Real.sqrt K₀ := by rw [Real.one_le_sqrt]; exact hK₀
  have hMr : 0 ≤ M / r := by positivity
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  rcases le_total (L ^ 2) (K₀ * (1 + 4 * M / r) ^ 2) with hmax | hmax
  · rw [max_eq_right hmax] at h
    refine (norm_le_of_sq_le hg hK₀ hM hr h).trans ?_
    have : 0 ≤ 4 * Real.exp 1 * Real.sqrt K₀ := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  · rw [max_eq_left hmax] at h
    have h1 : g ≤ Real.exp 1 * L := by
      have e : Real.exp 1 ^ 2 * L ^ 2 = (Real.exp 1 * L) ^ 2 := by ring
      rw [e] at h
      exact (pow_le_pow_iff_left₀ hg (by positivity) two_ne_zero).1 h
    refine h1.trans ?_
    have h2 : Real.exp 1 * L ≤ Real.exp 1 * (4 * Real.sqrt K₀) * L := by
      have : 1 ≤ 4 * Real.sqrt K₀ := by linarith
      nlinarith [Real.exp_pos 1]
    have h3 : 0 ≤ 4 * Real.exp 1 * Real.sqrt K₀ * (M / r + 1) := by positivity
    linarith

/-- **Proposition A.5, smooth case**. There is `C = C(d, β, Q_max, N)` such that
for every `ε > 0`, every `C^∞` coefficient `Q` with `|Q| ≤ Q_max`, `|∇(Q²)| ≤ N`, and every
solution `u ≥ 0` of `∂ₜu = Δu - Q² β_ε(u)` which is `C^∞` on `B_{2r}(x₀) × (t₀ - 4r², ∞)`,
`0 < r ≤ 1`, with `u ≤ M` on `Q_{2r}(x₀, t₀)`: `|∇u| ≤ C (M/r + 1)` on `Q_r(x₀, t₀)`. -/
theorem bernstein_interior_smooth {β : ℝ → ℝ} (hβ : IsReactionProfile β) (Qmax N : ℝ) :
    ∃ C : ℝ, ∀ ε > 0, ∀ Q : E d → ℝ, ContDiff ℝ ∞ Q → (∀ x, |Q x| ≤ Qmax) →
      (∀ x, ‖∇ (fun y ↦ Q y ^ 2) x‖ ≤ N) →
      ∀ (u : E d × ℝ → ℝ) (x₀ : E d) (t₀ r : ℝ), 0 < r → r ≤ 1 →
      ContDiffOn ℝ ∞ u (ball x₀ (2 * r) ×ˢ Ioi (t₀ - (2 * r) ^ 2)) →
      (∀ p ∈ ball x₀ (2 * r) ×ˢ Ioi (t₀ - (2 * r) ^ 2),
        dₜ u p = lapₓ u p - Q p.1 ^ 2 * betaEps β ε (u p)) →
      ∀ M : ℝ, (∀ q ∈ parCyl x₀ t₀ (2 * r), 0 ≤ u q ∧ u q ≤ M) →
      ∀ p ∈ parCyl x₀ t₀ r, ‖gradₓ u p‖ ≤ C * (M / r + 1) := by
  obtain ⟨βmax, hβmax0, hβmax⟩ := hβ.exists_le
  obtain ⟨Lβ, hLβ0, hLβ⟩ := hβ.exists_abs_deriv_le
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := exists_chi_bounds
  set Cχ := cutoffChiConst d c₁ c₂ with hCχ
  set C₁ := Qmax ^ 2 * (Lβ + 2 * βmax) with hC₁
  set K₀ := 8 * (Cχ + 2 * C₁ + 2 * (βmax * N)) + 1 with hK₀
  refine ⟨4 * Real.exp 1 * Real.sqrt K₀, ?_⟩
  intro ε hε Q hQ hQmax hN u x₀ t₀ r hr hr1 hu heq M hM p hp
  have hQmax0 : 0 ≤ Qmax := (abs_nonneg _).trans (hQmax 0)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have hCχ0 : 0 ≤ Cχ := by rw [hCχ, cutoffChiConst]; positivity
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hK₀1 : 1 ≤ K₀ := by
    have : 0 ≤ Cχ + 2 * C₁ + 2 * (βmax * N) := by positivity
    linarith
  have hr2 : 0 < r ^ 2 := by positivity
  -- the cylinders
  have hsub : parCyl x₀ t₀ r ⊆ parCyl x₀ t₀ (2 * r) :=
    prod_mono (ball_subset_ball (by linarith)) (Ioc_subset_Ioc_left (by linarith))
  have hM0 : 0 ≤ M := (hM p (hsub hp)).1.trans (hM p (hsub hp)).2
  set O' := ball x₀ (2 * r) ×ˢ Ioi (t₀ - (2 * r) ^ 2) with hO'
  have hO'o : IsOpen O' := isOpen_ball.prod isOpen_Ioi
  set K := closedBall x₀ (2 * r) ×ˢ Icc (t₀ - (2 * r) ^ 2) t₀ with hK
  set η := etaFun x₀ t₀ r 1 with hη
  set Φ := bigPhi (min ε r) M with hΦ
  set Ψ := bigPsi (min ε r) M with hΨ
  set z : E d × ℝ → ℝ := fun q ↦ η q ^ 2 * wGlob Φ Ψ u q with hz
  have hηs : ContDiff ℝ ∞ η := contDiff_etaFun x₀ t₀ r 1
  have hσ : ∀ q : E d × ℝ, sigmaFun x₀ t₀ r 1 q = ‖q.1 - x₀‖ ^ 2 / r ^ 2 + (t₀ - q.2) / r ^ 2 :=
    fun q ↦ by simp [sigmaFun]
  -- `z` is continuous on `K`
  have hWO : ∀ q ∈ O', wGlob Φ Ψ u q = wOf (fun q ↦ Ψ (u q)) q := fun q hq ↦
    (wOf_eq_wGlob contDiff_bigPhi deriv_bigPhi_pos contDiff_bigPsi bigPhi_bigPsi
      (hu.differentiableAt' hO'o hq)).symm
  have hzO : ContinuousOn z O' := by
    have h1 : ContinuousOn (fun q ↦ η q ^ 2 * wOf (fun q ↦ Ψ (u q)) q) O' :=
      ((hηs.continuous.pow 2).continuousOn).mul
        (contDiffOn_wOf hO'o hu contDiff_bigPsi).continuousOn
    exact h1.congr fun q hq ↦ by simp only [hz, hWO q hq]
  have hz3 : ∀ q, 3 < sigmaFun x₀ t₀ r 1 q → z =ᶠ[𝓝 q] fun _ ↦ 0 := fun q hq ↦ by
    have hopen : IsOpen {q' | 3 < sigmaFun x₀ t₀ r 1 q'} :=
      isOpen_lt continuous_const (contDiff_sigmaFun x₀ t₀ r 1).continuous
    filter_upwards [hopen.mem_nhds hq] with q' hq'
    simp only [hz, hη, etaFun, chi_eq_zero (le_of_lt hq'), zero_pow two_ne_zero, zero_mul]
  have hzK : ContinuousOn z K := by
    intro q hq
    refine ContinuousAt.continuousWithinAt ?_
    by_cases h3 : 3 < sigmaFun x₀ t₀ r 1 q
    · exact (continuousAt_const.congr (hz3 q h3).symm)
    · push Not at h3
      have ht : 0 ≤ t₀ - q.2 := by linarith [hq.2.2]
      have hq1 : ‖q.1 - x₀‖ ^ 2 ≤ 3 * r ^ 2 := by
        rw [hσ] at h3
        have : ‖q.1 - x₀‖ ^ 2 / r ^ 2 ≤ 3 := by
          have : 0 ≤ (t₀ - q.2) / r ^ 2 := by positivity
          linarith
        rwa [div_le_iff₀ hr2] at this
      have hqO : q ∈ O' := by
        refine ⟨?_, ?_⟩
        · rw [mem_ball, dist_eq_norm]
          exact norm_lt_two_mul_of_sq_lt hr (norm_nonneg _) (by linarith)
        · rw [hσ] at h3
          have : (t₀ - q.2) / r ^ 2 ≤ 3 := by
            have : 0 ≤ ‖q.1 - x₀‖ ^ 2 / r ^ 2 := by positivity
            linarith
          rw [div_le_iff₀ hr2] at this
          simp only [mem_Ioi]; linarith
      exact hzO.continuousAt (hO'o.mem_nhds hqO)
  -- the maximum
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKne : K.Nonempty :=
    ⟨(x₀, t₀), mem_closedBall_self (by positivity), show t₀ - (2 * r) ^ 2 ≤ t₀ by linarith, le_rfl⟩
  obtain ⟨ph, hphK, hphmax⟩ := hKc.exists_isMaxOn hKne hzK
  -- the target point
  obtain ⟨y, s⟩ := p
  have hpK : (y, s) ∈ K := ⟨ball_subset_closedBall (ball_subset_ball (by linarith) hp.1),
    show t₀ - (2 * r) ^ 2 ≤ s by linarith [hp.2.1], hp.2.2⟩
  have hσp : sigmaFun x₀ t₀ r 1 (y, s) ≤ 2 := by
    rw [hσ]
    have h1 : ‖y - x₀‖ < r := by rw [← dist_eq_norm]; exact hp.1
    have h2 : ‖(y, s).1 - x₀‖ ^ 2 / r ^ 2 ≤ 1 := by
      rw [div_le_one hr2]; simp only; nlinarith [norm_nonneg (y - x₀)]
    have h3 : (t₀ - (y, s).2) / r ^ 2 ≤ 1 := by
      rw [div_le_one hr2]; simp only; linarith [hp.2.1]
    linarith
  have hηp : η (y, s) = 1 := chi_eq_one hσp
  have hup : 0 ≤ u (y, s) ∧ u (y, s) ≤ M := hM _ (hsub hp)
  have hgrad : ‖gradₓ u (y, s)‖ ^ 2 ≤ Real.exp 1 ^ 2 * z ph := by
    have h1 := norm_gradₓ_sq_le_wGlob (lt_min hε hr) hM0 hup.1 hup.2
    have h2 : z (y, s) ≤ z ph := hphmax hpK
    have h3 : z (y, s) = wGlob Φ Ψ u (y, s) := by simp only [hz, hηp, one_pow, one_mul]
    rw [h3] at h2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  refine norm_le_of_sq_le (norm_nonneg _) hK₀1 hM0 hr (hgrad.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- bound on `z` at the maximum
  by_cases hηph : η ph = 0
  · simp only [hz, hηph]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul]; positivity
  have hηph0 : 0 < η ph := lt_of_le_of_ne (chi_nonneg _) (Ne.symm hηph)
  have hσph : sigmaFun x₀ t₀ r 1 ph < 3 := by
    by_contra h; push Not at h; exact hηph (chi_eq_zero h)
  have htph : ph.2 ≤ t₀ := hphK.2.2
  have hq1 : ‖ph.1 - x₀‖ ^ 2 ≤ 3 * r ^ 2 := by
    rw [hσ] at hσph
    have : ‖ph.1 - x₀‖ ^ 2 / r ^ 2 ≤ 3 := by
      have : 0 ≤ (t₀ - ph.2) / r ^ 2 := div_nonneg (by linarith) hr2.le
      linarith
    rwa [div_le_iff₀ hr2] at this
  have htph' : t₀ - 3 * r ^ 2 < ph.2 := by
    rw [hσ] at hσph
    have : (t₀ - ph.2) / r ^ 2 < 3 := by
      have : 0 ≤ ‖ph.1 - x₀‖ ^ 2 / r ^ 2 := by positivity
      linarith
    rw [div_lt_iff₀ hr2] at this; linarith
  have hphO : ph ∈ O' := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      exact norm_lt_two_mul_of_sq_lt hr (norm_nonneg _) (by linarith)
    · simp only [mem_Ioi]; linarith
  have hmax : ∀ᶠ q in 𝓝 ph, q.2 ≤ ph.2 → z q ≤ z ph := by
    filter_upwards [hO'o.mem_nhds hphO] with q hq hle
    refine hphmax ⟨ball_subset_closedBall hq.1, (mem_Ioi.1 hq.2).le, hle.trans htph⟩
  have hbound := zmax_bound hβ hβmax hLβ hε hr hr1 hM0 hQ hQmax hN hO'o hu heq hηs hphO
    (hM ph ⟨hphO.1, (mem_Ioi.1 hphO.2), htph⟩) hηph0 (chi_le_one _) hmax
  have hCη := cutoffConstAt_etaFun_le x₀ t₀ r 1 hc hr zero_le_one le_rfl hq1
  rw [show 2 * βmax * N = 2 * (βmax * N) by ring] at hbound
  exact hbound.trans (zstar_le hε hr hr1 hM0 hCχ0 hC₁0 (mul_nonneg hβmax0.le hN0) hCη)

/-- **Proposition A.6, smooth case**. There is
`C = C(d, β, Q_max, N)` such that for every `ε > 0`, every `C^∞` coefficient `Q` with
`|Q| ≤ Q_max`, `|∇(Q²)| ≤ N`, and every solution `0 ≤ u ≤ M` of `∂ₜu = Δu - Q² β_ε(u)` which is
`C^∞` on `B_{2r}(x₀) × (a, ∞)`, `0 < r ≤ 1`, with `u`, `∇u` continuous on `B_{2r}(x₀) × [a, ∞)`
and `|∇u(·, a)| ≤ L` on `B_{2r}(x₀)`: `|∇u| ≤ C (L + M/r + 1)` on `B_r(x₀) × [a, ∞)`.

(The paper assumes `T ≤ 4r²`; the proof, which cuts off in space only, does not use it.) -/
theorem bernstein_initial_smooth {β : ℝ → ℝ} (hβ : IsReactionProfile β) (Qmax N : ℝ) :
    ∃ C : ℝ, ∀ ε > 0, ∀ Q : E d → ℝ, ContDiff ℝ ∞ Q → (∀ x, |Q x| ≤ Qmax) →
      (∀ x, ‖∇ (fun y ↦ Q y ^ 2) x‖ ≤ N) →
      ∀ (u : E d × ℝ → ℝ) (x₀ : E d) (r a : ℝ), 0 < r → r ≤ 1 →
      ContDiffOn ℝ ∞ u (ball x₀ (2 * r) ×ˢ Ioi a) →
      (∀ p ∈ ball x₀ (2 * r) ×ˢ Ioi a, dₜ u p = lapₓ u p - Q p.1 ^ 2 * betaEps β ε (u p)) →
      ContinuousOn u (ball x₀ (2 * r) ×ˢ Ici a) →
      ContinuousOn (gradₓ u) (ball x₀ (2 * r) ×ˢ Ici a) →
      ∀ M L : ℝ, (∀ p ∈ ball x₀ (2 * r) ×ˢ Ici a, 0 ≤ u p ∧ u p ≤ M) →
      (∀ x ∈ ball x₀ (2 * r), ‖gradₓ u (x, a)‖ ≤ L) →
      ∀ x ∈ ball x₀ r, ∀ t, a ≤ t → ‖gradₓ u (x, t)‖ ≤ C * (L + M / r + 1) := by
  obtain ⟨βmax, hβmax0, hβmax⟩ := hβ.exists_le
  obtain ⟨Lβ, hLβ0, hLβ⟩ := hβ.exists_abs_deriv_le
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := exists_chi_bounds
  set Cχ := cutoffChiConst d c₁ c₂ with hCχ
  set C₁ := Qmax ^ 2 * (Lβ + 2 * βmax) with hC₁
  set K₀ := 8 * (Cχ + 2 * C₁ + 2 * (βmax * N)) + 1 with hK₀
  refine ⟨4 * Real.exp 1 * Real.sqrt K₀, ?_⟩
  intro ε hε Q hQ hQmax hN u x₀ r a hr hr1 hu heq hcu hcg M L hM hL x hx t ht
  have hQmax0 : 0 ≤ Qmax := (abs_nonneg _).trans (hQmax 0)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have hCχ0 : 0 ≤ Cχ := by rw [hCχ, cutoffChiConst]; positivity
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hK₀1 : 1 ≤ K₀ := by
    have : 0 ≤ Cχ + 2 * C₁ + 2 * (βmax * N) := by positivity
    linarith
  have hr2 : 0 < r ^ 2 := by positivity
  have hx2 : x ∈ ball x₀ (2 * r) := ball_subset_ball (by linarith) hx
  have hxa : (x, a) ∈ ball x₀ (2 * r) ×ˢ Ici a := ⟨hx2, mem_Ici.2 le_rfl⟩
  have hM0 : 0 ≤ M := (hM (x, a) hxa).1.trans (hM (x, a) hxa).2
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL x hx2)
  set O' := ball x₀ (2 * r) ×ˢ Ioi a with hO'
  have hO'o : IsOpen O' := isOpen_ball.prod isOpen_Ioi
  set S := ball x₀ (2 * r) ×ˢ Ici a with hS
  set K := closedBall x₀ (2 * r) ×ˢ Icc a t with hK
  set η := etaFun x₀ 0 r 0 with hη
  set Φ := bigPhi (min ε r) M with hΦ
  set Ψ := bigPsi (min ε r) M with hΨ
  set z : E d × ℝ → ℝ := fun q ↦ η q ^ 2 * wGlob Φ Ψ u q with hz
  have hηs : ContDiff ℝ ∞ η := contDiff_etaFun x₀ 0 r 0
  have hσ : ∀ q : E d × ℝ, sigmaFun x₀ 0 r 0 q = ‖q.1 - x₀‖ ^ 2 / r ^ 2 :=
    fun q ↦ by simp [sigmaFun]
  -- `z` is continuous on `K`
  have hWS : ContinuousOn (wGlob Φ Ψ u) S := by
    have h1 : ContinuousOn (fun q ↦ deriv Φ (Ψ (u q)) ^ 2) S :=
      (((contDiff_deriv' contDiff_bigPhi).continuous.comp continuous_bigPsi).comp_continuousOn
        hcu).pow 2
    exact ((continuous_norm.comp_continuousOn hcg).pow 2).div h1
      fun q _ ↦ (pow_pos (deriv_bigPhi_pos _) 2).ne'
  have hzS : ContinuousOn z S := ((hηs.continuous.pow 2).continuousOn).mul hWS
  have hz3 : ∀ q, 3 < sigmaFun x₀ 0 r 0 q → z =ᶠ[𝓝 q] fun _ ↦ 0 := fun q hq ↦ by
    have hopen : IsOpen {q' | 3 < sigmaFun x₀ 0 r 0 q'} :=
      isOpen_lt continuous_const (contDiff_sigmaFun x₀ 0 r 0).continuous
    filter_upwards [hopen.mem_nhds hq] with q' hq'
    simp only [hz, hη, etaFun, chi_eq_zero (le_of_lt hq'), zero_pow two_ne_zero, zero_mul]
  have hball3 : ∀ q : E d × ℝ, sigmaFun x₀ 0 r 0 q ≤ 3 → q.1 ∈ ball x₀ (2 * r) := by
    intro q hq
    rw [hσ, div_le_iff₀ hr2] at hq
    rw [mem_ball, dist_eq_norm]
    exact norm_lt_two_mul_of_sq_lt hr (norm_nonneg _) hq
  have hzK : ContinuousOn z K := by
    intro q hq
    by_cases h3 : 3 < sigmaFun x₀ 0 r 0 q
    · exact (continuousAt_const.congr (hz3 q h3).symm).continuousWithinAt
    · push Not at h3
      have hqS : q ∈ S := ⟨hball3 q h3, hq.2.1⟩
      refine (hzS q hqS).mono_of_mem_nhdsWithin ?_
      refine mem_nhdsWithin.2 ⟨ball x₀ (2 * r) ×ˢ univ, isOpen_ball.prod isOpen_univ,
        ⟨hqS.1, mem_univ _⟩, fun q' hq' ↦ ⟨hq'.1.1, hq'.2.2.1⟩⟩
  -- the maximum
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKne : K.Nonempty := ⟨(x₀, a), mem_closedBall_self (by positivity), le_rfl, ht⟩
  obtain ⟨ph, hphK, hphmax⟩ := hKc.exists_isMaxOn hKne hzK
  -- the target point
  have hxK : (x, t) ∈ K := ⟨ball_subset_closedBall hx2, ht, le_rfl⟩
  have hσx : sigmaFun x₀ 0 r 0 (x, t) ≤ 2 := by
    rw [hσ, div_le_iff₀ hr2]
    have h1 : ‖x - x₀‖ < r := by rw [← dist_eq_norm]; exact hx
    simp only; nlinarith [norm_nonneg (x - x₀)]
  have hηx : η (x, t) = 1 := chi_eq_one hσx
  have hux : 0 ≤ u (x, t) ∧ u (x, t) ≤ M := hM _ ⟨hx2, ht⟩
  have hgrad : ‖gradₓ u (x, t)‖ ^ 2 ≤ Real.exp 1 ^ 2 * z ph := by
    have h1 := norm_gradₓ_sq_le_wGlob (lt_min hε hr) hM0 hux.1 hux.2
    have h2 : z (x, t) ≤ z ph := hphmax hxK
    have h3 : z (x, t) = wGlob Φ Ψ u (x, t) := by simp only [hz, hηx, one_pow, one_mul]
    rw [h3] at h2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  refine norm_le_of_sq_le_max (norm_nonneg _) hK₀1 hM0 hr hL0 (hgrad.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- bound on `z` at the maximum
  by_cases hηph : η ph = 0
  · simp only [hz, hηph]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul]; positivity
  have hηph0 : 0 < η ph := lt_of_le_of_ne (chi_nonneg _) (Ne.symm hηph)
  have hσph : sigmaFun x₀ 0 r 0 ph < 3 := by
    by_contra h; push Not at h; exact hηph (chi_eq_zero h)
  have hph1 : ph.1 ∈ ball x₀ (2 * r) := hball3 ph hσph.le
  have hphS : ph ∈ S := ⟨hph1, hphK.2.1⟩
  have hupS : 0 ≤ u ph ∧ u ph ≤ M := hM ph hphS
  have hη1 : η ph ^ 2 ≤ 1 := by
    change chi (sigmaFun x₀ 0 r 0 ph) ^ 2 ≤ 1
    have := chi_le_one (sigmaFun x₀ 0 r 0 ph)
    have := chi_nonneg (sigmaFun x₀ 0 r 0 ph)
    nlinarith
  rcases hphK.2.1.eq_or_lt with hta | hta
  · -- the maximum is at the initial time
    refine le_max_of_le_left ?_
    have h1 := wGlob_le_of_ge_one (lt_min hε hr) hM0 hupS.1 hupS.2
    have h2 : ‖gradₓ u ph‖ ≤ L := by
      obtain ⟨y, s⟩ := ph
      simp only at hta hph1
      rw [← hta]; exact hL y hph1
    have h3 : 0 ≤ wGlob Φ Ψ u ph := div_nonneg (sq_nonneg _) (sq_nonneg _)
    calc z ph = η ph ^ 2 * wGlob Φ Ψ u ph := rfl
      _ ≤ 1 * wGlob Φ Ψ u ph := mul_le_mul_of_nonneg_right hη1 h3
      _ ≤ ‖gradₓ u ph‖ ^ 2 := by rw [one_mul]; exact h1
      _ ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  · -- an interior (or final-time) maximum
    refine le_max_of_le_right ?_
    have hphO : ph ∈ O' := ⟨hph1, hta⟩
    have hmax : ∀ᶠ q in 𝓝 ph, q.2 ≤ ph.2 → z q ≤ z ph := by
      filter_upwards [hO'o.mem_nhds hphO] with q hq hle
      exact hphmax ⟨ball_subset_closedBall hq.1, (mem_Ioi.1 hq.2).le, hle.trans hphK.2.2⟩
    have hbound := zmax_bound hβ hβmax hLβ hε hr hr1 hM0 hQ hQmax hN hO'o hu heq hηs hphO
      hupS hηph0 (chi_le_one _) hmax
    have hq1 : ‖ph.1 - x₀‖ ^ 2 ≤ 3 * r ^ 2 := by
      have := hσph.le; rwa [hσ, div_le_iff₀ hr2] at this
    have hCη := cutoffConstAt_etaFun_le x₀ 0 r 0 hc hr le_rfl zero_le_one hq1
    rw [show 2 * βmax * N = 2 * (βmax * N) by ring] at hbound
    exact hbound.trans (zstar_le hε hr hr1 hM0 hCχ0 hC₁0 (mul_nonneg hβmax0.le hN0) hCη)

end PerronVariational

end
