/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.WellPosedData
import PerronVariational.Semilinear.Attainment
import PerronVariational.Semilinear.Dissipation
import PerronVariational.Semilinear.Lipschitz
import PerronVariational.Semilinear.Monotone
import PerronVariational.Semilinear.PositivityTrace

/-!
# Semilinear well-posedness (Proposition 3.8)

Assembly of **Proposition 3.8** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, from its
parts:

* data (i), (i'): `exists_isWellPreparedData` (Lemma A.4);
* existence of the solution: `Registry.semilinear_exists` (classical well-posedness, from
  parabolic-basic-theory v0.1.0);
* (ii) monotonicity and `L^∞` bounds: `IsSemilinearSolution.monotoneInTime`,
  `IsSemilinearSolution.antitoneInTime`, `IsSemilinearSolution.mem_Icc` (Lemma A.1, via the
  comparison principle);
* (iii) dissipation: `IsSemilinearSolution.dissipation` (the energy dissipation inequality,
  proved in `EnergyDissipation.lean`);
* (iv) interior Lipschitz bounds: `exists_interiorLipEst` (Proposition A.5),
  `exists_norm_gradₓ_le` (Lemma A.7), by smooth approximation of `Q` from the smooth Bernstein
  estimates `bernstein_interior_smooth`, `bernstein_initial_smooth` and, for Lemma A.7, the
  regularity of `∇u` at `t = 0` for smooth data (from parabolic-basic-theory v0.1.0);
* (v) modulus of continuity: `exists_modulus` (Proposition A.8; barriers and Lemma A.7);
* (vi) positivity trace: `IsWellPreparedData.positivity_trace` (from Lemma A.11);
* (vi*) (increasing case) below every level `κ ε`:
  `IsWellPreparedData.positivity_trace_small` (PositivityTrace.lean). This strengthening of (vi)
  is needed for Corollary 5.4 with the authors' corrected set `E*`.

The paper states (3.8) as an equality; here (iii) is the inequality `≤`, which is all that is
used. The paper asserts `u_ε ∈ C^∞(U_∞)`; here solutions are classical `C^{2,1}`, because with `Q`
only Lipschitz the appendix gives no more. The family is restricted to `0 < ε < min ε₀ 1`, since
Lemma A.7 and Proposition A.8 are stated for `ε ≤ 1`.
-/

open Set Filter Topology MeasureTheory
open scoped Gradient

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

theorem betaEps_eq_zero_of_nonpos {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε z : ℝ}
    (hε : 0 < ε) (hz : z ≤ 0) : betaEps β ε z = 0 := by
  rw [betaEps, hβ.eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hz hε.le), zero_div]

theorem betaEps_eq_zero_of_le {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε z : ℝ}
    (hε : 0 < ε) (hz : ε ≤ z) : betaEps β ε z = 0 := by
  rw [betaEps, hβ.eq_zero_of_one_le ((one_le_div hε).2 hz), zero_div]

/-- A bound `|g| ≤ M` on `U` extends to `Ū` for continuous `g`. -/
theorem abs_le_on_closure {U : Set (E d)} {g : E d → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x ∈ U, |g x| ≤ M) : ∀ x ∈ closure U, |g x| ≤ M := fun _ hx ↦
  closure_minimal hM (isClosed_le (continuous_abs.comp hg) continuous_const) hx

/-- **Proposition 3.8** for a well-prepared family of data and the corresponding solutions of
(3.4). -/
theorem isWellPreparedFamily_of_data (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {g : E d → ℝ} (hgC : ContDiff ℝ 2 g) {increasing : Bool} {ε₀ : ℝ} {gε : ℝ → E d → ℝ}
    (h : IsWellPreparedData S g β increasing ε₀ gε) (hε₀ : ε₀ ≤ 1)
    (hsub : increasing = true → IsStrictSub S.U S.Q g) {uε : ℝ → E d × ℝ → ℝ}
    (hu : ∀ ε ∈ Ioo 0 ε₀, IsSemilinearSolution S.U S.Q β ε (gε ε) (uε ε)) :
    IsWellPreparedFamily S g β increasing ε₀ gε uε := by
  have hg1 : ContDiff ℝ 1 g := hgC.of_le (by norm_num)
  obtain ⟨K, hK⟩ := h.exists_lipschitzOnWith hg1
  obtain ⟨Mg₀, hMg₀⟩ := S.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hgC.continuous.continuousOn
  set Mg := max Mg₀ 0
  have hMg : ∀ x ∈ closure S.U, |g x| ≤ Mg := fun x hx ↦
    (by simpa using hMg₀ x hx : |g x| ≤ Mg₀).trans (le_max_left _ _)
  have hMg0 : 0 ≤ Mg := le_max_right _ _
  have hcont : ∀ ε ∈ Ioo 0 ε₀, ContinuousOn (gε ε) (closure S.U) := fun ε hε ↦
    (hK ε hε).continuousOn
  -- `L^∞` bounds (3.7), by comparison with the constants `0` and `M + ε`
  have hbd : ∀ ε ∈ Ioo 0 ε₀, ∀ M : ℝ, (∀ x ∈ closure S.U, |g x| ≤ M) → 0 ≤ M →
      ∀ p ∈ closure S.U ×ˢ Ici 0, 0 ≤ uε ε p ∧ uε ε p ≤ M + ε := by
    intro ε hε M hM hM0
    refine (hu ε hε).mem_Icc hβ hε.1 (betaEps_eq_zero_of_nonpos hβ hε.1 le_rfl)
      (betaEps_eq_zero_of_le hβ hε.1 (by linarith)) fun x hx ↦ ⟨h.nonneg hε hx, ?_⟩
    have h1 := (h.bounds ε hε x hx).2
    have h2 : max (g x) 0 ≤ M := max_le ((le_abs_self _).trans (hM x hx)) hM0
    linarith
  have hgε_le : ∀ ε ∈ Ioo 0 ε₀, ∀ x ∈ closure S.U, 0 ≤ gε ε x ∧ gε ε x ≤ Mg + 1 := by
    intro ε hε x hx
    refine ⟨h.nonneg hε hx, ?_⟩
    have h1 := (h.bounds ε hε x hx).2
    have h2 : max (g x) 0 ≤ Mg := max_le ((le_abs_self _).trans (hMg x hx)) hMg0
    linarith [hε.2]
  have hε1 : ∀ ε ∈ Ioo 0 ε₀, ε ∈ Ioc (0 : ℝ) 1 := fun ε hε ↦ ⟨hε.1, hε.2.le.trans hε₀⟩
  refine ⟨h.pos, fun ε hε ↦ ⟨hu ε hε, ⟨K, hK ε hε⟩, h.bounds ε hε,
    fun M hM x hx ↦ (h.norm_gradient_le ε hε x hx).trans (hM x hx), h.memH1 ε hε, ?_, ?_, ?_,
    fun T hT ↦ (hu ε hε).dissipation S hβ hε.1 ⟨K, hK ε hε⟩ hT, h.lipschitz ε hε⟩, h.memH1_pos,
    h.tendsto_H1,
    ?_, ?_, ?_, h.positivity_trace hβ hg1 hu, ?_⟩
  · -- (i) energy of the data: `χ⁰_ε = 2 𝓑_ε(g_ε)` since `u_ε(·, 0) = g_ε`
    have heq : energyJχ S.U S.Q (∇ (gε ε)) (fun x ↦ chiEps β ε (uε ε) (x, 0)) =
        energyJχ S.U S.Q (∇ (gε ε)) (fun x ↦ 2 * bigBEps β ε (gε ε x)) := by
      refine setLIntegral_congr_fun S.isOpen.measurableSet fun x hx ↦ ?_
      simp only [chiEps, (hu ε hε).2.2.1 x (subset_closure hx)]
    rw [heq]
    exact h.energy_le ε hε
  · -- (ii) monotonicity (Lemma A.1)
    have hv := h.visc ε hε
    cases increasing with
    | true =>
      simp only [ite_true] at hv ⊢
      exact (hu ε hε).monotoneInTime hβ hε.1
        ((hu ε hε).le_of_viscSubStat hβ hε.1 hv (hcont ε hε))
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hv ⊢
      exact (hu ε hε).antitoneInTime hβ hε.1
        ((hu ε hε).le_of_viscSuperStat hβ hε.1 hv (hcont ε hε))
  · -- (ii) the bound (3.7)
    intro M hM
    obtain ⟨x₀, hx₀⟩ := S.isConnected.nonempty
    exact hbd ε hε M (abs_le_on_closure hgC.continuous hM) ((abs_nonneg _).trans (hM x₀ hx₀))
  · -- (iv) interior Lipschitz bound (3.9) (Proposition A.5)
    obtain ⟨C, hC⟩ := exists_interiorLipEst S hβ
    exact ⟨C, fun ε hε ↦ hC ε hε.1 (gε ε) (uε ε) ⟨K, hK ε hε⟩ (fun x hx ↦ h.nonneg hε hx)
      (hu ε hε)⟩
  · -- (iv) global-in-time interior gradient bound (Lemma A.7)
    intro V hV
    obtain ⟨CV, hCV⟩ := exists_norm_gradₓ_le S hβ hV K (Mg + 1)
    exact ⟨CV, fun ε hε ↦ hCV ε (hε1 ε hε) (gε ε) (uε ε) (hK ε hε) (hgε_le ε hε) (hu ε hε)⟩
  · -- (v) uniform modulus of continuity (Proposition A.8)
    obtain ⟨ϖ, hϖ, hmod⟩ := exists_modulus S hβ K (Mg + 1)
    exact ⟨ϖ, hϖ, fun ε hε ↦ hmod ε (hε1 ε hε) (gε ε) (uε ε) (hK ε hε) (hgε_le ε hε) (hu ε hε)⟩
  · -- (vi*) below every level `κ ε`
    intro hinc
    subst hinc
    exact h.positivity_trace_small S hβ (hsub rfl) hu

/-- **Proposition 3.8**: `SemilinearWellposedStatement`. The paper asserts `C^∞` solutions;
here they are classical `C^{2,1}` (joint continuity of `∇ₓu`, `D²ₓu`, `∂ₜu`), because `Q` is only
Lipschitz. -/
theorem semilinear_wellposed : SemilinearWellposedStatement := by
  intro d S g β hβ
  have key : ∀ increasing : Bool,
      (if increasing then IsStrictSub S.U S.Q g else IsStrictSuper S.U S.Q g) →
      ∃ (ε₀ : ℝ) (gε : ℝ → E d → ℝ) (uε : ℝ → E d × ℝ → ℝ),
        IsWellPreparedFamily S g β increasing ε₀ gε uε := by
    intro increasing hg
    have hgC : ContDiff ℝ 2 g := by
      cases increasing
      · simp only [Bool.false_eq_true, ite_false] at hg; exact hg.1
      · simp only [ite_true] at hg; exact hg.1
    obtain ⟨ε₀, gε, h⟩ := exists_isWellPreparedData S hβ increasing hg
    have h' := h.mono (lt_min h.pos one_pos) (min_le_left _ _)
    obtain ⟨K, hK⟩ := h'.exists_lipschitzOnWith (hgC.of_le (by norm_num))
    have hex : ∀ ε, ∃ u : E d × ℝ → ℝ, ε ∈ Ioo 0 (min ε₀ 1) →
        IsSemilinearSolution S.U S.Q β ε (gε ε) u := by
      intro ε
      by_cases hε : ε ∈ Ioo 0 (min ε₀ 1)
      · obtain ⟨u, hu⟩ := Registry.semilinear_exists S hβ hε.1 ⟨K, hK ε hε⟩
        exact ⟨u, fun _ ↦ hu⟩
      · exact ⟨0, fun h ↦ absurd h hε⟩
    choose uε huε using hex
    exact ⟨min ε₀ 1, gε, uε,
      isWellPreparedFamily_of_data S hβ hgC h' (min_le_right _ _)
        (fun hinc ↦ by subst hinc; simpa using hg) huε⟩
  exact ⟨fun hg ↦ key true (by simpa using hg), fun hg ↦ key false (by simpa using hg)⟩

end PerronVariational

end
