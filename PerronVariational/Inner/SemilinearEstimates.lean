/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
public import PerronVariational.Inner.Common
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.TietzeExtension
import PerronVariational.Registry.Comparison
import PerronVariational.Registry.SemilinearDissipation
import PerronVariational.Semilinear.Lipschitz
import PerronVariational.Semilinear.LipschitzApprox
import PerronVariational.Semilinear.Monotone
import PerronVariational.Semilinear.Profiles

/-!
# Uniform estimates for arbitrary solutions of the semilinear problem

F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
the Bernoulli one-phase problem*, arXiv:2609.14981, note at the start of Section 4 that
Proposition 3.8(iii), (iv) and the bound (4.1) "hold for any solution of the semilinear problem, as
can be seen from the proof". Proposition 4.1 (`EpsInnerLimitStatement`) quantifies over arbitrary
solutions, so these estimates are stated here for an arbitrary classical solution of (3.4) (with
data in `H¹`), as named lemmas.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-- Constants `c` with `β_ε(c) = 0` are classical solutions of `∂ₜu = Δu - Q² β_ε(u)`. -/
theorem isSemilinearSolOn_const {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε c : ℝ}
    {I : Set ℝ} (hc : betaEps β ε c = 0) : IsSemilinearSolOn U Q β ε I (fun _ ↦ c) := by
  refine ⟨continuousOn_const, fun t _ ↦ contDiffOn_const, ?_, ?_,
    fun p _ ↦ differentiableAt_const _, ?_, fun p _ ↦ ?_⟩
  · have : gradₓ (fun _ : E d × ℝ ↦ c) = fun _ ↦ 0 := funext fun p ↦ by simp [gradₓ]
    rw [this]
    exact continuousOn_const
  · have : (fun p : E d × ℝ ↦ iteratedFDeriv ℝ 2 (fun y : E d ↦ (fun _ : E d × ℝ ↦ c) (y, p.2))
        p.1) = fun _ ↦ 0 := funext fun p ↦ by simp [iteratedFDeriv_const_of_ne two_ne_zero]
    rw [this]
    exact continuousOn_const
  · have : dₜ (fun _ : E d × ℝ ↦ c) = fun _ ↦ 0 := funext fun p ↦ by simp [dₜ]
    rw [this]
    exact continuousOn_const
  · simp [dₜ, lapₓ, hc]

/-- Restricting the time interval of a classical solution. -/
theorem IsSemilinearSolOn.mono_time {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ}
    {I J : Set ℝ} {u : E d × ℝ → ℝ} (h : IsSemilinearSolOn U Q β ε I u) (hJ : J ⊆ I) :
    IsSemilinearSolOn U Q β ε J u :=
  ⟨h.1.mono (prod_mono le_rfl hJ), fun t ht ↦ h.2.1 t (hJ ht), h.2.2.1.mono (prod_mono le_rfl hJ),
    h.2.2.2.1.mono (prod_mono le_rfl hJ), fun p hp ↦ h.2.2.2.2.1 p ⟨hp.1, hJ hp.2⟩,
    h.2.2.2.2.2.1.mono (prod_mono le_rfl hJ), fun p hp ↦ h.2.2.2.2.2.2 p ⟨hp.1, hJ hp.2⟩⟩

/-- **Bounds (4.1)**, in the form `0 ≤ u ≤ max M ε`: for any solution `u` of (3.4) with data
`0 ≤ gε ≤ M` in `U`, `0 ≤ u ≤ max M ε` on `Ū × [0, ∞)`. Proof: comparison for the semilinear
equation (`Registry.semilinear_comparison`) with the constant classical solutions `0` and
`max M ε` (`β_ε` vanishes at both). The paper states `u ≤ ‖gε‖_∞`; here we prove `u ≤ max M ε`,
because the constant `M` need not be a supersolution when `M < ε`; the weaker bound suffices for
Proposition 4.1. -/
theorem semilinear_nonneg_le_max (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {ε : ℝ} (hε : 0 < ε) {gε : E d → ℝ} {u : E d × ℝ → ℝ} {M : ℝ}
    (hu : IsSemilinearSolution S.U S.Q β ε gε u) (hg : ∀ x ∈ S.U, 0 ≤ gε x ∧ gε x ≤ M) :
    ∀ p ∈ closure S.U ×ˢ Ici (0 : ℝ), 0 ≤ u p ∧ u p ≤ max M ε := by
  obtain ⟨hcont, hsol, h0, hlat⟩ := hu
  have hgcl : ∀ x ∈ closure S.U, 0 ≤ gε x ∧ gε x ≤ M := by
    have hc : ContinuousOn (fun x ↦ u (x, 0)) (closure S.U) :=
      hcont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx ↦ ⟨hx, mem_Ici.2 le_rfl⟩)
    have hcl := hc.preimage_isClosed_of_isClosed isClosed_closure (isClosed_Icc (a := (0 : ℝ))
      (b := M))
    have hsub : S.U ⊆ closure S.U ∩ (fun x ↦ u (x, 0)) ⁻¹' Icc 0 M := fun x hx ↦
      ⟨subset_closure hx, by
        simp only [mem_preimage]
        rw [h0 x (subset_closure hx)]
        exact hg x hx⟩
    intro x hx
    have := (closure_minimal hsub hcl) hx
    rw [← h0 x hx]
    exact this.2
  have hK0 : betaEps β ε (max M ε) = 0 := by
    simp only [betaEps]
    rw [hβ.eq_zero_of_one_le ((one_le_div hε).2 (le_max_right _ _))]
    simp
  have hz0 : betaEps β ε 0 = 0 := hβ.betaEps_zero ε
  intro p hp
  have hp2 : 0 ≤ p.2 := hp.2
  have hT : (0 : ℝ) < p.2 + 1 := by linarith
  have hpT : p ∈ closure S.U ×ˢ Icc 0 (p.2 + 1) := ⟨hp.1, hp2, by linarith⟩
  have hI : ∀ t ∈ Ioc (0 : ℝ) (p.2 + 1), ∃ δ > 0, Ioc (t - δ) t ⊆ Ioc 0 (p.2 + 1) :=
    fun t ht ↦ ⟨t, ht.1, fun s hs ↦ ⟨by linarith [hs.1], hs.2.trans ht.2⟩⟩
  have hsolT := IsSemilinearSolOn.mono_time hsol
    (Ioc_subset_Ioi_self : Ioc (0 : ℝ) (p.2 + 1) ⊆ Ioi 0)
  have hucT : ContinuousOn u (closure S.U ×ˢ Icc 0 (p.2 + 1)) :=
    hcont.mono (prod_mono le_rfl Icc_subset_Ici_self)
  have hbdry : ∀ q ∈ parBdry S.U 0 (p.2 + 1), q.1 ∈ closure S.U ∧ u q = gε q.1 := by
    rintro ⟨x, s⟩ (⟨hx, hs⟩ | ⟨hx, hs⟩)
    · simp only [mem_singleton_iff] at hs
      subst hs
      exact ⟨hx, h0 x hx⟩
    · exact ⟨frontier_subset_closure hx, hlat x hx s hs.1⟩
  have hlow := Registry.semilinear_comparison S.isOpen S.isBounded hT S.lip hβ hε
    continuousOn_const hucT
    (Registry.isSemilinearViscSubOn_of_solOn S.isOpen hI (isSemilinearSolOn_const hz0))
    (Registry.isSemilinearViscSuperOn_of_solOn S.isOpen hI hsolT)
    (fun q hq ↦ by
      obtain ⟨hq1, hq2⟩ := hbdry q hq
      rw [hq2]
      exact (hgcl q.1 hq1).1) p hpT
  have hup := Registry.semilinear_comparison S.isOpen S.isBounded hT S.lip hβ hε hucT
    continuousOn_const (Registry.isSemilinearViscSubOn_of_solOn S.isOpen hI hsolT)
    (Registry.isSemilinearViscSuperOn_of_solOn S.isOpen hI (isSemilinearSolOn_const hK0))
    (fun q hq ↦ by
      obtain ⟨hq1, hq2⟩ := hbdry q hq
      rw [hq2]
      exact (hgcl q.1 hq1).2.trans (le_max_left _ _)) p hpT
  exact ⟨hlow, hup⟩

/-- **Energy dissipation for an arbitrary solution** (Proposition 3.8(iii), (3.8); claimed for any
solution at the start of Section 4). If `u` solves (3.4) with data `gε ∈ H¹(U)` (the weak gradient
`Gε` is carried as explicit data), then for every `T > 0`
`½ J(u(T), χ_ε(T); U) + ∫₀ᵀ∫_U (∂ₜu)² ≤ ½ (∫_U |Gε|² + Q_max² |U|)`.
The paper's identity has right-hand side `½ J(gε, χ⁰_ε; U)`, which is at most the right-hand side
here since `χ⁰_ε ≤ 1`. The paper states (3.8) as an identity; here only the inequality is proved,
which is all that is used. From `Registry.semilinear_energy_dissipation`, proved in
`Semilinear/EnergyDissipation.lean`. -/
theorem semilinear_dissipation (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ}
    (hε : 0 < ε) {gε : E d → ℝ} {Gε : E d → E d} {u : E d × ℝ → ℝ} (hg : MemH1 S.U gε Gε)
    (hu : IsSemilinearSolution S.U S.Q β ε gε u) (T : ℝ) (hT : 0 < T) :
    energyJχ S.U S.Q (fun x ↦ gradₓ u (x, T)) (fun x ↦ chiEps β ε u (x, T)) / 2 +
        ∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ u p ^ 2) ≤ energyBound S Gε / 2 := by
  refine (Registry.semilinear_energy_dissipation S hβ hε hg hu hT).trans ?_
  refine ENNReal.div_le_div_right (setLIntegral_mono' S.isOpen.measurableSet fun x hx ↦ ?_) 2
  refine ENNReal.ofReal_le_ofReal (add_le_add le_rfl ?_)
  have h0 := hβ.bigBEps_nonneg hε.ne' (u (x, 0))
  have h1 := hβ.bigBEps_le_half hε.ne' (u (x, 0))
  obtain ⟨hQmin, hQmax⟩ := S.Q_mem x (subset_closure hx)
  have hQ0 : 0 ≤ S.Q x := S.Qmin_pos.le.trans hQmin
  have hχ0 : 0 ≤ chiEps β ε u (x, 0) := by simp only [chiEps]; linarith
  have hχ1 : chiEps β ε u (x, 0) ≤ 1 := by simp only [chiEps]; linarith
  calc S.Q x ^ 2 * chiEps β ε u (x, 0) ≤ S.Q x ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hχ1 (sq_nonneg _)
    _ ≤ S.Qmax ^ 2 := by rw [mul_one]; exact pow_le_pow_left₀ hQ0 hQmax 2

/-! ### Approximation of continuous data (for `semilinear_interiorLipEst`) -/

/-- Nonnegative data continuous on `Ū` are uniformly approximated on `Ū` by nonnegative data
Lipschitz on `Ū` (Tietze extension, mollification, truncation at `0`). -/
theorem Setting.exists_lipschitz_approx (S : Setting d) {g : E d → ℝ}
    (hg : ContinuousOn g (closure S.U)) (hg0 : ∀ x ∈ closure S.U, 0 ≤ g x) {η : ℝ}
    (hη : 0 < η) :
    ∃ g' : E d → ℝ, (∃ L : ℝ≥0, LipschitzOnWith L g' (closure S.U)) ∧ (∀ x, 0 ≤ g' x) ∧
      ∀ x ∈ closure S.U, |g' x - g x| ≤ η := by
  set K := closure S.U with hKdef
  have hK : IsCompact K := S.isBounded.isCompact_closure
  -- continuous extension
  obtain ⟨G, -, hGK⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed
    (⟨K.restrict g, hg.restrict⟩ : C(K, ℝ)) (t := univ) (fun _ ↦ mem_univ _) univ_nonempty
    isClosed_closure
  have hGg : ∀ x ∈ K, G x = g x := fun x hx ↦ by
    have := congrArg (fun F : C(K, ℝ) ↦ F ⟨x, hx⟩) hGK
    simpa using this
  -- smoothing
  have huc : UniformContinuousOn G (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous G.continuous.continuousOn
  obtain ⟨δ, hδ, hGδ⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨h, hh, hhG⟩ :=
    G.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (lt_min one_pos hδ)
  have hclose : ∀ x ∈ K, |h x - g x| ≤ η := fun x hx ↦ by
    rw [← hGg x hx, ← Real.dist_eq]
    refine hhG x η fun y hy ↦ ?_
    rw [mem_ball, lt_min_iff] at hy
    exact (hGδ y (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le) x
      (self_subset_cthickening _ hx) hy.2).le
  -- truncation
  refine ⟨fun x ↦ max (h x) 0, ?_, fun x ↦ le_max_right _ _, fun x hx ↦ ?_⟩
  · have hl : LocallyLipschitz fun x ↦ max (h x) 0 :=
      ((hh.of_le (by simp)).locallyLipschitz (𝕂 := ℝ)).max_const 0
    exact hl.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  · have e : g x = max (g x) 0 := (max_eq_left (hg0 x hx)).symm
    calc |max (h x) 0 - g x| = |max (h x) 0 - max (g x) 0| := by rw [← e]
      _ ≤ |h x - g x| := abs_max_sub_max_le_abs _ _ _
      _ ≤ η := hclose x hx

/-- **Continuous dependence on the data.** Two solutions of (3.4) (same setting) whose data
differ by at most `η` on `Ū` differ by at most `η e^{Λ t}` at time `t`, `Λ = Q_max² Lβ/ε²`
(`Lβ` a Lipschitz constant of `β`). Comparison (`Registry.semilinear_comparison`) with
`u' ± η e^{Λ t}`. -/
theorem IsSemilinearSolution.abs_sub_le_of_data (S : Setting d) {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {ε : ℝ} (hε : 0 < ε) {Lβ : ℝ} (hLβ0 : 0 ≤ Lβ)
    (hLβ : ∀ ε > 0, ∀ s s' : ℝ, |betaEps β ε s - betaEps β ε s'| ≤ Lβ / ε ^ 2 * |s - s'|)
    {g g' : E d → ℝ} {u u' : E d × ℝ → ℝ} (hu : IsSemilinearSolution S.U S.Q β ε g u)
    (hu' : IsSemilinearSolution S.U S.Q β ε g' u') {η : ℝ} (hη : 0 ≤ η)
    (hgg : ∀ x ∈ closure S.U, |g' x - g x| ≤ η) :
    ∀ x ∈ closure S.U, ∀ t : ℝ, 0 ≤ t →
      |u' (x, t) - u (x, t)| ≤ η * Real.exp (S.Qmax ^ 2 * (Lβ / ε ^ 2) * t) := by
  obtain ⟨βmax, -, hβmax⟩ := hβ.exists_le
  set Λ := S.Qmax ^ 2 * (Lβ / ε ^ 2) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set c : ℝ → ℝ := fun t ↦ η * Real.exp (Λ * t) with hc
  have hcs : ContDiff ℝ 2 c := by rw [hc]; fun_prop
  have hderiv : ∀ t, deriv c t = Λ * c t := fun t ↦ by
    have h2 : HasDerivAt (fun t ↦ Real.exp (Λ * t)) (Real.exp (Λ * t) * Λ) t := by
      simpa using ((hasDerivAt_id t).const_mul Λ).exp
    rw [(h2.const_mul η).deriv, hc]; ring
  have hc0 : ∀ t, 0 ≤ t → η ≤ c t := fun t ht ↦
    le_mul_of_one_le_right hη (Real.one_le_exp (by positivity))
  have hkey : ∀ x ∈ closure S.U, ∀ t, 0 ≤ t → ∀ s s' : ℝ, |s - s'| ≤ c t →
      S.Q x ^ 2 * betaEps β ε s - S.Q x ^ 2 * betaEps β ε s' ≤ deriv c t := by
    intro x hx t _ s s' hss
    have h := sq_mul_betaEps_sub_le hβ hβmax hLβ hLβ0 hε (q₁ := S.Q x)
      (S.Qmin_pos.le.trans (S.Q_mem x hx).1) (S.Q_mem x hx).2 (θ := 0) (by simp) hss
    rw [zero_mul, zero_add] at h
    rw [hderiv]
    exact h
  intro x hx t ht
  have hb : (0 : ℝ) < t + 1 := by linarith
  have hpt : (x, t) ∈ closure S.U ×ˢ Icc 0 (t + 1) := ⟨hx, ht, by linarith⟩
  have hcc : ContinuousOn (fun q : E d × ℝ ↦ c q.2) (closure S.U ×ˢ Icc 0 (t + 1)) :=
    (hcs.continuous.comp continuous_snd).continuousOn
  have ht0 : ∀ p ∈ parBdry S.U 0 (t + 1), 0 ≤ p.2 := by
    intro p hp
    rcases hp with ⟨-, h⟩ | ⟨-, h⟩
    · rw [mem_singleton_iff] at h; rw [h]
    · exact h.1
  have h1 : u (x, t) ≤ u' (x, t) + c t := by
    have hS : IsSemilinearViscSuperOn S.U S.Q β ε (Ioc 0 (t + 1)) (fun p ↦ u' p + c p.2) :=
      (hu'.viscSuperOn (t + 1)).add_time hcs fun p hp ↦ hkey p.1 (subset_closure hp.1) p.2
        hp.2.1.le _ _
        (by rw [sub_add_cancel_left, abs_neg, abs_of_nonneg (hη.trans (hc0 p.2 hp.2.1.le))])
    refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
      (hu.continuousOn_Icc _) ((hu'.continuousOn_Icc _).add hcc) (hu.viscSubOn (t + 1)) hS
      (fun p hp ↦ ?_) _ hpt
    rw [hu.eq_on_parBdry hp]
    change g p.1 ≤ u' p + c p.2
    rw [hu'.eq_on_parBdry hp]
    have h3 := hgg p.1 (parBdry_fst_mem hp)
    have h4 := hc0 p.2 (ht0 p hp)
    rw [abs_le] at h3
    linarith
  have h2 : u' (x, t) - c t ≤ u (x, t) := by
    have hS : IsSemilinearViscSubOn S.U S.Q β ε (Ioc 0 (t + 1)) (fun p ↦ u' p - c p.2) :=
      (hu'.viscSubOn (t + 1)).sub_time hcs fun p hp ↦ hkey p.1 (subset_closure hp.1) p.2
        hp.2.1.le _ _
        (by rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (hη.trans (hc0 p.2 hp.2.1.le))])
    refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
      ((hu'.continuousOn_Icc _).sub hcc) (hu.continuousOn_Icc _) hS (hu.viscSuperOn (t + 1))
      (fun p hp ↦ ?_) _ hpt
    rw [hu.eq_on_parBdry hp]
    rw [hu'.eq_on_parBdry hp]
    have h3 := hgg p.1 (parBdry_fst_mem hp)
    have h4 := hc0 p.2 (ht0 p hp)
    rw [abs_le] at h3
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Interior Lipschitz bound for an arbitrary solution** (Proposition 3.8(iv), (3.9); claimed
for any solution at the start of Section 4; Bernstein argument, Appendix A.4). There are a constant
`C` and `ε₁ > 0`, depending only on the setting and `β`, such that every solution `u` of (3.4)
with `0 < ε < ε₁` and bounded nonnegative data satisfies the interior Lipschitz estimate (3.12)
with constant `C`.

Proof: Proposition A.5 (`exists_interiorLipEst`) gives this, with `C` depending only on the setting
and `β`, for nonnegative data Lipschitz on `Ū`. The data `gε = u(·, 0)` are continuous and
nonnegative on `Ū`; approximate them uniformly on `Ū` by nonnegative Lipschitz data
(`Setting.exists_lipschitz_approx`), solve (well-posedness of the semilinear problem,
`Registry.semilinear_exists`), compare the solutions (`IsSemilinearSolution.abs_sub_le_of_data`,
comparison with shifts `η e^{Λ t}`), and pass the uniform interior gradient bound to the limit on
time slices (`norm_gradient_le_of_tendsto_pointwise`). The threshold `ε₁` plays no role (`ε₁ = 1`).
-/
theorem semilinear_interiorLipEst (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) :
    ∃ C ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo 0 ε₁, ∀ (M : ℝ) (gε : E d → ℝ) (u : E d × ℝ → ℝ),
      IsSemilinearSolution S.U S.Q β ε gε u → (∀ x ∈ S.U, 0 ≤ gε x ∧ gε x ≤ M) →
        InteriorLipEst S.U u C := by
  obtain ⟨C, hC⟩ := exists_interiorLipEst S hβ
  obtain ⟨Lβ, hLβ0, hLβ⟩ := hβ.exists_abs_betaEps_sub_le
  refine ⟨C, 1, one_pos, fun ε hε M g u hu hg ↦ ?_⟩
  have hε0 : 0 < ε := hε.1
  -- the data are continuous and nonnegative on `Ū`
  have hgc : ContinuousOn g (closure S.U) := by
    have hc : ContinuousOn (fun x ↦ u (x, 0)) (closure S.U) :=
      hu.1.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx ↦ ⟨hx, mem_Ici.2 le_rfl⟩)
    exact hc.congr fun x hx ↦ (hu.2.2.1 x hx).symm
  have hg0 : ∀ x ∈ closure S.U, 0 ≤ g x := fun x hx ↦ by
    have := (semilinear_nonneg_le_max S hβ hε0 hu hg (x, 0) ⟨hx, mem_Ici.2 le_rfl⟩).1
    rwa [hu.2.2.1 x hx] at this
  set Λ := S.Qmax ^ 2 * (Lβ / ε ^ 2) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  intro x t r hr hr1 hcyl Mc hMc p hp
  obtain ⟨hball, ht0⟩ := parCyl_subset_UInf (by positivity) hcyl
  have ht : 0 ≤ t := by nlinarith
  -- the approximate solutions
  have happrox : ∀ k : ℕ, ∃ (g' : E d → ℝ) (u' : E d × ℝ → ℝ),
      (∃ L : ℝ≥0, LipschitzOnWith L g' (closure S.U)) ∧ (∀ x, 0 ≤ g' x) ∧
      IsSemilinearSolution S.U S.Q β ε g' u' ∧
      ∀ z ∈ closure S.U, ∀ s ∈ Icc 0 t, |u' (z, s) - u (z, s)| ≤ 1 / (k + 1) := by
    intro k
    set η := Real.exp (-(Λ * t)) / (k + 1) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨g', hg'L, hg'0, hg'g⟩ := Setting.exists_lipschitz_approx S hgc hg0 hη0
    obtain ⟨u', hu'⟩ := Registry.semilinear_exists S hβ hε0 hg'L
    refine ⟨g', u', hg'L, hg'0, hu', fun z hz s hs ↦ ?_⟩
    refine (IsSemilinearSolution.abs_sub_le_of_data S hβ hε0 hLβ0 hLβ hu hu' hη0.le hg'g z hz s
      hs.1).trans ?_
    have h1 : Real.exp (Λ * s) ≤ Real.exp (Λ * t) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hΛ0)
    calc η * Real.exp (Λ * s) ≤ η * Real.exp (Λ * t) := mul_le_mul_of_nonneg_left h1 hη0.le
      _ = 1 / (k + 1) := by
        rw [hη, div_mul_eq_mul_div, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  choose gn un hgL hg'0 hun hclose using happrox
  -- the estimate for the approximate solutions
  have hest : ∀ k : ℕ, ∀ q ∈ parCyl x t r,
      ‖gradₓ (un k) q‖ ≤ C * ((Mc + 1 / (k + 1)) / r + 1) := by
    intro k
    refine hC ε hε0 (gn k) (un k) (hgL k) (fun y _ ↦ hg'0 k y) (hun k) x t r hr hr1 hcyl
      (Mc + 1 / (k + 1)) fun q hq ↦ ?_
    have hqU : q.1 ∈ closure S.U ∧ q.2 ∈ Icc 0 t :=
      ⟨subset_closure (hcyl hq).1, (mem_Ioi.1 (hcyl hq).2).le, hq.2.2⟩
    have h1 := hclose k q.1 hqU.1 q.2 hqU.2
    have h2 := hMc q hq
    calc |un k q| = |(un k q - u q) + u q| := by ring_nf
      _ ≤ |un k q - u q| + |u q| := abs_add_le _ _
      _ ≤ Mc + 1 / (k + 1) := by linarith
  -- pass to the limit on the time slice through `p`
  obtain ⟨y, s⟩ := p
  have hVp : ∀ z ∈ ball x r, (z, s) ∈ parCyl x t r := fun z hz ↦ ⟨hz, hp.2⟩
  have hlimC : Tendsto (fun k : ℕ ↦ C * ((Mc + 1 / ((k : ℝ) + 1)) / r + 1)) atTop
      (𝓝 (C * (Mc / r + 1))) := by
    have h0 : Tendsto (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (((h0.const_add Mc).div_const r).add_const 1).const_mul C
    rwa [add_zero] at h1
  have hsubcyl : parCyl x t r ⊆ parCyl x t (2 * r) :=
    prod_mono (ball_subset_ball (by linarith)) (Ioc_subset_Ioc_left (by nlinarith))
  have hcyl2 : parCyl x t r ⊆ UInf S.U := hsubcyl.trans hcyl
  refine norm_gradient_le_of_tendsto_pointwise (l := atTop) (F := fun k z ↦ un k (z, s))
    (C := fun k : ℕ ↦ C * ((Mc + 1 / ((k : ℝ) + 1)) / r + 1)) (f := fun z ↦ u (z, s))
    isOpen_ball (convex_ball x r) (fun k z hz ↦ ?_) (fun k z hz ↦ hest k (z, s) (hVp z hz))
    hlimC (fun z hz ↦ ?_) hp.1
  · have hzU : (z, s) ∈ S.U ×ˢ Ioi 0 := hcyl2 (hVp z hz)
    exact (((hun k).2.1.2.1 s hzU.2).contDiffAt (S.isOpen.mem_nhds hzU.1)).differentiableAt
      (by norm_num)
  · have hzU : (z, s) ∈ S.U ×ˢ Ioi 0 := hcyl2 (hVp z hz)
    have hs1 : s ∈ Icc 0 t := ⟨(mem_Ioi.1 hzU.2).le, hp.2.2⟩
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun k ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [Real.norm_eq_abs]
    exact hclose k z (subset_closure hzU.1) s hs1

-- The interior time-equicontinuity `semilinear_time_equicontinuous` is proved in
-- `Inner/Compactness.lean` (from (3.8), (3.9) and (4.1)).

-- The local bound on the reaction term `semilinear_betaEps_lintegral_le` is proved in
-- `Inner/ReactionBound.lean`.

-- The weighted perimeter bound `semilinear_weightedPerimeterEst` is proved in
-- `Inner/PerimeterEps.lean`.

-- The semilinear inner-variation identity (4.2) is proved in `Inner/InnerVarEps.lean`.

end Inner

end PerronVariational

end
