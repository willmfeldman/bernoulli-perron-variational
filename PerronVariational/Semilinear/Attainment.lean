/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Semilinear
import PerronVariational.Semilinear.AttainmentBarriers
import PerronVariational.Semilinear.AttainmentEstimates
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Lipschitz
import PerronVariational.Semilinear.Monotone

/-!
# Uniform attainment of the parabolic boundary data (Proposition 3.8(v))

Proposition A.8, with Lemmas A.9 and A.10, of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.5).

`exists_modulus` (Proposition A.8) is proved by barriers only. The route differs from the
paper's, which goes through the `L²`-in-time estimate of Lemma A.10 and hence the dissipation
identity:

1. `exists_boundary_estimate` (lateral estimate, uniform in `t`, AttainmentEstimates.lean);
2. `exists_spatial_modulus`: near `∂U` from 1., in the interior from the global gradient bound
   Lemma A.7 (`exists_norm_gradₓ_le`) and the mean value theorem;
3. `exists_time_modulus`: restart at time `s` (`IsSemilinearSolution.shift`) and apply the
   initial-time estimate `exists_initial_estimate` to the data `u(·, s)`, whose modulus comes
   from 2.;
4. the modulus `ϖ` is the supremum of the oscillations over the whole class.

So `exists_modulus` depends only on Lemma A.7, on the classical well-posedness of (3.4) and on the
comparison principle for (3.4) (both from parabolic-basic-theory v0.1.0).
-/

open Set Filter Topology Metric
open scoped NNReal Gradient

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- If `x ∈ Ū` has distance `≥ r` from `∂U`, then `B_r(x) ⊆ U`. -/
theorem Setting.ball_subset_of_forall_le (S : Setting d) {x : E d} (hx : x ∈ closure S.U)
    {r : ℝ} (hr : 0 < r) (h : ∀ w ∈ frontier S.U, r ≤ ‖w - x‖) : ball x r ⊆ S.U := by
  have hxU : x ∈ S.U := by
    rw [closure_eq_self_union_frontier] at hx
    rcases hx with hx | hx
    · exact hx
    · have := h x hx; rw [sub_self, norm_zero] at this; linarith
  have hdisj : Disjoint S.U (closure S.U)ᶜ :=
    disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)
  refine (convex_ball x r).isPreconnected.subset_left_of_subset_union S.isOpen
    isClosed_closure.isOpen_compl hdisj (fun w hw ↦ ?_) ⟨x, mem_ball_self hr, hxU⟩
  by_cases hwc : w ∈ closure S.U
  · left
    rw [closure_eq_self_union_frontier] at hwc
    rcases hwc with h' | h'
    · exact h'
    · exfalso
      have h1 := h w h'
      rw [mem_ball, dist_eq_norm] at hw
      linarith
  · right; exact hwc

/-- The data are `L`-Lipschitz, hence `|∇g| ≤ L` in `U`. -/
theorem norm_gradient_le_of_lipschitzOnWith (S : Setting d) {g : E d → ℝ} {L : ℝ≥0}
    (hg : LipschitzOnWith L g (closure S.U)) {x : E d} (hx : x ∈ S.U) : ‖∇ g x‖ ≤ L := by
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitzOn ℝ
    (mem_of_superset (S.isOpen.mem_nhds hx) subset_closure) hg

/-- **Spatial equicontinuity**, uniform in `t ≥ 0` and in the class of Proposition A.8. -/
theorem exists_spatial_modulus (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    (L : ℝ≥0) (M : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ > 0, ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ),
      LipschitzOnWith L g (closure S.U) → (∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) →
      IsSemilinearSolution S.U S.Q β ε g u →
      ∀ x ∈ closure S.U, ∀ y ∈ closure S.U, ‖x - y‖ < δ → ∀ t, 0 ≤ t →
        |u (x, t) - u (y, t)| ≤ σ := by
  obtain ⟨K, hK0, hK⟩ := exists_boundary_estimate S hβ L (σ := σ / 8) (by positivity)
  set r := σ / (8 * (K + 1)) with hr
  have hr0 : 0 < r := by positivity
  have hKr : K * r ≤ σ / 8 := by
    rw [hr, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- the interior set `V`
  set V := {z ∈ closure S.U | ∀ w ∈ frontier S.U, r / 2 ≤ ‖w - z‖} with hV
  have hVcl : IsClosed V := by
    have : V = closure S.U ∩ ⋂ w ∈ frontier S.U, {z | r / 2 ≤ ‖w - z‖} := by
      ext z; simp [hV]
    rw [this]
    exact isClosed_closure.inter (isClosed_biInter fun w _ ↦
      isClosed_le continuous_const (continuous_const.sub continuous_id).norm)
  have hVU : V ⊆ S.U := fun z hz ↦ by
    have hz1 := hz.1
    rw [closure_eq_self_union_frontier] at hz1
    rcases hz1 with h | h
    · exact h
    · have := hz.2 z h; rw [sub_self, norm_zero] at this; linarith
  have hVc : CompactlyContained V S.U := by
    refine ⟨?_, ?_⟩
    · rw [hVcl.closure_eq]
      exact S.isBounded.isCompact_closure.of_isClosed_subset hVcl fun z hz ↦ hz.1
    · rw [hVcl.closure_eq]; exact hVU
  obtain ⟨CV, hCV⟩ := exists_norm_gradₓ_le S hβ hVc L M
  set C' := max CV L with hC'
  have hC'0 : 0 ≤ C' := le_max_of_le_right L.2
  refine ⟨min (r / 2) (σ / (C' + 1)), lt_min (by positivity) (by positivity), ?_⟩
  intro ε hε g u hgL hgM hu x hx y hy hxy t ht
  have hδr : ‖x - y‖ < r / 2 := hxy.trans_le (min_le_left _ _)
  have hδσ : ‖x - y‖ < σ / (C' + 1) := hxy.trans_le (min_le_right _ _)
  have hg0 : ∀ z ∈ closure S.U, 0 ≤ g z := fun z hz ↦ (hgM z hz).1
  -- near the boundary
  have hnear : ∀ a ∈ closure S.U, ∀ b ∈ closure S.U, ‖a - b‖ < r / 2 →
      (∃ w ∈ frontier S.U, ‖w - a‖ < r) → |u (a, t) - u (b, t)| ≤ σ := by
    rintro a ha b hb hab ⟨w, hw, hwa⟩
    have h1 := hK ε hε g u hgL hg0 hu w hw a ha t ht
    have h2 := hK ε hε g u hgL hg0 hu w hw b hb t ht
    have hwa' : ‖a - w‖ < r := by rw [norm_sub_rev]; exact hwa
    have hwb : ‖b - w‖ < r + r / 2 := by
      calc ‖b - w‖ = ‖(b - a) + (a - w)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖b - a‖ + ‖a - w‖ := norm_add_le _ _
        _ < r / 2 + r := by rw [norm_sub_rev b a]; linarith
        _ = r + r / 2 := by ring
    have h3 : K * ‖a - w‖ ≤ K * r := mul_le_mul_of_nonneg_left hwa'.le hK0
    have h4 : K * ‖b - w‖ ≤ K * (r + r / 2) := mul_le_mul_of_nonneg_left hwb.le hK0
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith
  by_cases hxb : ∃ w ∈ frontier S.U, ‖w - x‖ < r
  · exact hnear x hx y hy hδr hxb
  by_cases hyb : ∃ w ∈ frontier S.U, ‖w - y‖ < r
  · rw [abs_sub_comm]
    exact hnear y hy x hx (by rw [norm_sub_rev]; exact hδr) hyb
  -- interior: gradient bound and the mean value theorem
  push Not at hxb
  have hball : ball x (r / 2) ⊆ V := by
    intro z hz
    have hzU : z ∈ S.U := S.ball_subset_of_forall_le hx hr0 hxb
      (ball_subset_ball (by linarith) hz)
    refine ⟨subset_closure hzU, fun w hw ↦ ?_⟩
    have h1 := hxb w hw
    rw [mem_ball, dist_eq_norm] at hz
    have h2 : ‖w - x‖ ≤ ‖w - z‖ + ‖z - x‖ := by
      calc ‖w - x‖ = ‖(w - z) + (z - x)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  have hyball : y ∈ ball x (r / 2) := by
    rw [mem_ball, dist_eq_norm]; exact (norm_sub_rev y x).trans_lt hδr
  have hlip : |u (x, t) - u (y, t)| ≤ C' * ‖x - y‖ := by
    rcases ht.eq_or_lt with ht0 | htpos
    · subst ht0
      rw [hu.2.2.1 x hx, hu.2.2.1 y hy]
      have := hgL.dist_le_mul x hx y hy
      rw [Real.dist_eq, dist_eq_norm] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    · have hdiff : ∀ z ∈ ball x (r / 2), DifferentiableAt ℝ (fun w ↦ u (w, t)) z := by
        intro z hz
        have hzU := hVU (hball hz)
        exact ((hu.2.1.2.1 t htpos).contDiffAt (S.isOpen.mem_nhds hzU)).differentiableAt
          (by norm_num)
      have hbound : ∀ z ∈ ball x (r / 2), ‖fderiv ℝ (fun w ↦ u (w, t)) z‖ ≤ C' := by
        intro z hz
        rw [← norm_gradient_eq_norm_fderiv]
        exact (hCV ε hε g u hgL hgM hu z (hball hz) t htpos).trans (le_max_left _ _)
      have := (convex_ball x (r / 2)).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
        (mem_ball_self (by positivity)) hyball
      rw [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev] at this
      exact this
  calc |u (x, t) - u (y, t)| ≤ C' * ‖x - y‖ := hlip
    _ ≤ C' * (σ / (C' + 1)) := mul_le_mul_of_nonneg_left hδσ.le hC'0
    _ ≤ σ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith

/-- **Equicontinuity in time**, uniform in `s ≥ 0` and in the class of Proposition A.8. -/
theorem exists_time_modulus (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    (L : ℝ≥0) (M : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ τ > 0, ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ),
      LipschitzOnWith L g (closure S.U) → (∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) →
      IsSemilinearSolution S.U S.Q β ε g u →
      ∀ x ∈ closure S.U, ∀ s, 0 ≤ s → ∀ t ∈ Icc s (s + τ), |u (x, t) - u (x, s)| ≤ σ := by
  obtain ⟨δ, hδ, hX⟩ := exists_spatial_modulus S hβ L M (σ := σ / 3) (by positivity)
  set M' := max M 1 with hM'
  have hM'0 : 0 ≤ M' := le_max_of_le_right zero_le_one
  set A := M' / δ ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨τ, hτ, hP⟩ := exists_initial_estimate S hβ (σ := σ / 3) (A := A) (by positivity) hA0
  refine ⟨τ, hτ, ?_⟩
  intro ε hε g u hgL hgM hu x hx s hs t ht
  have hbd := hu.nonneg_le_max hβ hε.1 hε.2 hgM
  have hv := hu.shift hs
  have hdata : ∀ y ∈ closure S.U, 0 ≤ u (y, s) ∧ u (y, s) ≤ M' := fun y hy ↦
    hbd (y, s) ⟨hy, hs⟩
  have hquad : ∀ y ∈ closure S.U, |u (y, s) - u (x, s)| ≤ σ / 3 + A * ‖y - x‖ ^ 2 := by
    intro y hy
    rcases lt_or_ge ‖y - x‖ δ with h | h
    · have := hX ε hε g u hgL hgM hu y hy x hx h s hs
      have : 0 ≤ A * ‖y - x‖ ^ 2 := by positivity
      linarith
    · have h1 : |u (y, s) - u (x, s)| ≤ M' := by
        have := hdata y hy; have := hdata x hx
        rw [abs_le]; constructor <;> linarith
      have h2 : M' ≤ A * ‖y - x‖ ^ 2 := by
        rw [hA, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le h 2) hM'0
      linarith
  have key := hP ε hε (fun y ↦ u (y, s)) (fun q ↦ u (q.1, q.2 + s)) M' hdata hv x hx hquad
    (t - s) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [sub_add_cancel] at key
  linarith

/-- **Equicontinuity** in space-time, uniform in the class of Proposition A.8. -/
theorem exists_modulus_aux (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    (L : ℝ≥0) (M : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ > 0, ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ),
      LipschitzOnWith L g (closure S.U) → (∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) →
      IsSemilinearSolution S.U S.Q β ε g u →
      ∀ p ∈ closure S.U ×ˢ Ici 0, ∀ q ∈ closure S.U ×ˢ Ici 0,
        ‖p.1 - q.1‖ + |p.2 - q.2| < δ → |u p - u q| ≤ σ := by
  obtain ⟨δ, hδ, hX⟩ := exists_spatial_modulus S hβ L M (σ := σ / 2) (by positivity)
  obtain ⟨τ, hτ, hT⟩ := exists_time_modulus S hβ L M (σ := σ / 2) (by positivity)
  refine ⟨min δ τ, lt_min hδ hτ, ?_⟩
  rintro ε hε g u hgL hgM hu ⟨x, t⟩ ⟨hx, ht⟩ ⟨y, s⟩ ⟨hy, hs⟩ hpq
  simp only [mem_Ici] at ht hs
  simp only at hpq ⊢
  have hxy : ‖x - y‖ < δ := by
    have := abs_nonneg (t - s); linarith [min_le_left δ τ]
  have hts : |t - s| < τ := by
    have := norm_nonneg (x - y); linarith [min_le_right δ τ]
  have h1 := hX ε hε g u hgL hgM hu x hx y hy hxy t ht
  have h2 : |u (y, t) - u (y, s)| ≤ σ / 2 := by
    rcases le_total s t with hst | hst
    · exact hT ε hε g u hgL hgM hu y hy s hs t ⟨hst, by linarith [(abs_lt.1 hts).2]⟩
    · rw [abs_sub_comm]
      exact hT ε hε g u hgL hgM hu y hy t ht s ⟨hst, by linarith [(abs_lt.1 hts).1]⟩
  calc |u (x, t) - u (y, s)| = |(u (x, t) - u (y, t)) + (u (y, t) - u (y, s))| := by ring_nf
    _ ≤ |u (x, t) - u (y, t)| + |u (y, t) - u (y, s)| := abs_add_le _ _
    _ ≤ σ := by linarith

/-- **Proposition A.8**, Proposition 3.8(v): given `L ≥ 0` and `M`, there is a
modulus of continuity `ϖ` such that for all `0 < ε ≤ 1`, every solution `u` of (3.4) with
nonnegative data `g ≤ M` that are `L`-Lipschitz on `Ū` satisfies
`|u(x, t) - u(y, s)| ≤ ϖ(|x - y| + |t - s|)` on `Ū × [0, ∞)`.

Proof: `ϖ(h)` is the supremum of `|u p - u q|` over the class and over `|p - q| ≤ h`; it tends
to `0` by `exists_modulus_aux`. -/
theorem exists_modulus (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) (L : ℝ≥0)
    (M : ℝ) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ), LipschitzOnWith L g (closure S.U) →
        (∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) → IsSemilinearSolution S.U S.Q β ε g u →
        ∀ p ∈ closure S.U ×ˢ Ici 0, ∀ q ∈ closure S.U ×ˢ Ici 0,
          |u p - u q| ≤ ϖ (‖p.1 - q.1‖ + |p.2 - q.2|) := by
  -- the oscillation set at scale `h`
  set O : ℝ → Set ℝ := fun h ↦ insert 0 {r | ∃ ε ∈ Ioc (0 : ℝ) 1, ∃ (g : E d → ℝ)
    (u : E d × ℝ → ℝ), LipschitzOnWith L g (closure S.U) ∧
    (∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) ∧ IsSemilinearSolution S.U S.Q β ε g u ∧
    ∃ p ∈ closure S.U ×ˢ Ici 0, ∃ q ∈ closure S.U ×ˢ Ici 0,
      ‖p.1 - q.1‖ + |p.2 - q.2| ≤ h ∧ r = |u p - u q|} with hO
  have hbdd : ∀ h, BddAbove (O h) := by
    intro h
    refine ⟨max M 1, fun r hr ↦ ?_⟩
    rcases hr with rfl | ⟨ε, hε, g, u, -, hgM, hu, p, hp, q, hq, -, rfl⟩
    · exact le_max_of_le_right zero_le_one
    · have h1 := hu.nonneg_le_max hβ hε.1 hε.2 hgM p hp
      have h2 := hu.nonneg_le_max hβ hε.1 hε.2 hgM q hq
      rw [abs_le]; constructor <;> linarith
  refine ⟨fun h ↦ sSup (O h), ?_, ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ, hδ, hE⟩ := exists_modulus_aux S hβ L M (σ := e / 2) (by positivity)
    refine ⟨δ, hδ, fun h _ hh ↦ ?_⟩
    rw [Real.dist_eq, sub_zero] at hh ⊢
    have hle : sSup (O h) ≤ e / 2 := by
      refine csSup_le ⟨0, mem_insert _ _⟩ fun r hr ↦ ?_
      rcases hr with rfl | ⟨ε, hε, g, u, hgL, hgM, hu, p, hp, q, hq, hpq, rfl⟩
      · positivity
      · exact hE ε hε g u hgL hgM hu p hp q hq (hpq.trans_lt ((le_abs_self h).trans_lt hh))
    have hge : 0 ≤ sSup (O h) := le_csSup (hbdd h) (mem_insert _ _)
    rw [abs_of_nonneg hge]
    linarith
  · intro ε hε g u hgL hgM hu p hp q hq
    exact le_csSup (hbdd _) (Or.inr ⟨ε, hε, g, u, hgL, hgM, hu, p, hp, q, hq, le_rfl, rfl⟩)

end PerronVariational

end
