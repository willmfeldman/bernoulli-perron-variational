/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import PerronVariational.Defs.Semilinear
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Semilinear.BernsteinSmooth
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.LipschitzApprox
import PerronVariational.Semilinear.Monotone
import PerronVariational.Semilinear.Profiles

/-!
# Interior Lipschitz bounds for the semilinear problem (Proposition 3.8(iv))

Appendix A.4 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: Propositions A.5 and
A.6 and Lemma A.7, proved by the Bernstein method.

* `exists_interiorLipEst` (Proposition A.5 for solutions of (3.4)): approximate `Q` by smooth
  coefficients (as in the appendix: `Q` is only Lipschitz, so solutions are only `C^{2,1}`), apply
  the smooth Bernstein estimate `bernstein_interior_smooth` to the approximate solutions (which
  are smooth), and pass to the limit by the comparison principle.
* `exists_norm_gradₓ_le` (Lemma A.7): the same with smooth data as well (the "mollification
  argument" of the proof of Lemma A.7) and the initial-data estimate `bernstein_initial_smooth`.
  The mollification argument also needs the regularity of the gradient up to `t = 0` for smooth
  data, `IsSemilinearSolution.continuousOn_gradₓ_of_contDiff`, which comes from
  parabolic-basic-theory v0.1.0.

Deviations from the paper's statements. Lemma A.7 assumes a bound on `‖∇g‖_{L^∞(U)}`; here we
assume a Lipschitz constant `L` of `g` on `Ū`, because for non-convex `U` the gradient bound does
not give an `ε`-independent Lipschitz constant on `Ū` (only the Lipschitz bound on balls
`B_{2r} ⊆ U` is used). Proposition A.6 assumes `T ≤ 4r²`; here it is not needed (the cutoff is
in space only), so Lemma A.7 follows from Proposition A.6 alone.

Note (paper typo): Propositions A.5 and A.6 write the equation as `(∂ₜ - Δ)u = -Q β_ε(u)`; the
equation (3.4) has `Q²`. The statements below use (3.4).
-/

open Set Filter Topology Metric
open scoped NNReal ContDiff Gradient

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- **Regularity of the gradient up to the initial time for smooth data** (the step of the
"mollification argument" in the proof of Lemma A.7 that the paper leaves implicit:
"it suffices to consider the case `g_ε` is smooth, so that `∇u_ε` is continuous at `t = 0` on
`V`"). If `Q` and the data `g` are `C^∞`, the spatial gradient of the solution of (3.4) is
continuous on `U × [0, ∞)`.

This is interior (in space) parabolic Schauder regularity up to the initial time
(O. A. Ladyzhenskaya, V. A. Solonnikov, N. N. Ural'ceva, *Linear and Quasilinear Equations of
Parabolic Type*, AMS Transl. Math. Monogr. 23, 1968, Ch. IV §10, local estimates near the lower
base; G. M. Lieberman, *Second Order Parabolic Differential Equations*, World Scientific, 1996,
doi:10.1142/3302, Ch. IV). It is a result from the literature, proved in parabolic-basic-theory
v0.1.0 and imported through `Registry.semilinear_continuousOn_gradₓ_of_contDiff`. -/
theorem IsSemilinearSolution.continuousOn_gradₓ_of_contDiff (S : Setting d) {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {ε : ℝ} (hε : 0 < ε) (hQ : ContDiff ℝ ∞ S.Q) {g : E d → ℝ}
    (hg : ContDiff ℝ ∞ g) {u : E d × ℝ → ℝ} (hu : IsSemilinearSolution S.U S.Q β ε g u) :
    ContinuousOn (gradₓ u) (S.U ×ˢ Ici 0) :=
  Registry.semilinear_continuousOn_gradₓ_of_contDiff S hβ hε hQ hg hu

/-! ### Auxiliary facts -/

/-- `|∇(Q²)| ≤ 2 Q_max K` for a differentiable `K`-Lipschitz `Q` with `|Q| ≤ Q_max`. -/
theorem norm_gradient_sq_le {Q : E d → ℝ} {K : ℝ≥0} (hQ : LipschitzWith K Q)
    (hQd : Differentiable ℝ Q) {Qmax : ℝ} (hQmax : ∀ x, |Q x| ≤ Qmax) (x : E d) :
    ‖∇ (fun y ↦ Q y ^ 2) x‖ ≤ 2 * Qmax * K := by
  rw [norm_gradient_eq_norm_fderiv]
  have h : HasFDerivAt (fun y ↦ Q y ^ 2) ((2 * Q x) • fderiv ℝ Q x) x := by
    have := (hQd x).hasFDerivAt.mul (hQd x).hasFDerivAt
    convert this using 1
    · funext y; simp [sq]
    · rw [two_mul, add_smul]
  rw [h.fderiv, norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
  have h1 : ‖fderiv ℝ Q x‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ hQ
  have h2 := hQmax x
  have h0 : 0 ≤ Qmax := (abs_nonneg _).trans h2
  exact mul_le_mul (by linarith) h1 (norm_nonneg _) (by positivity)

/-- If `Q_r(x, t) ⊆ U_∞` then `B_r(x) ⊆ U` and `t - r² ≥ 0`. -/
theorem parCyl_subset_UInf {U : Set (E d)} {x : E d} {t r : ℝ} (hr : 0 < r)
    (h : parCyl x t r ⊆ UInf U) : ball x r ⊆ U ∧ 0 ≤ t - r ^ 2 := by
  have hr2 : t - r ^ 2 < t := by nlinarith
  have hmem : ∀ y ∈ ball x r, ∀ s, t - r ^ 2 < s → s ≤ t → y ∈ U ∧ 0 < s := by
    intro y hy s hs1 hs2
    have := h (show (y, s) ∈ parCyl x t r from mk_mem_prod hy ⟨hs1, hs2⟩)
    exact this
  refine ⟨fun y hy ↦ (hmem y hy t hr2 le_rfl).1, ?_⟩
  by_contra hneg
  have hneg' : t - r ^ 2 < 0 := lt_of_not_ge hneg
  have := (hmem x (mem_ball_self hr) (min t 0) (lt_min hr2 hneg') (min_le_left _ _)).2
  linarith [min_le_right t 0]

/-- On `U`, the spatial gradient of a solution at `t = 0` is the gradient of the data. -/
theorem IsSemilinearSolution.gradₓ_zero {S : Setting d} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ}
    {u : E d × ℝ → ℝ} (hu : IsSemilinearSolution S.U S.Q β ε g u) {x : E d} (hx : x ∈ S.U) :
    gradₓ u (x, 0) = ∇ g x := by
  simp only [gradₓ]
  refine Filter.EventuallyEq.gradient_eq ?_
  filter_upwards [S.isOpen.mem_nhds hx] with y hy using hu.2.2.1 y (subset_closure hy)

/-- `u ≥ 0` for nonnegative bounded data (comparison with `0` and a large constant). -/
theorem IsSemilinearSolution.nonneg_of_nonneg {S : Setting d} {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {ε : ℝ} (hε : 0 < ε) {g : E d → ℝ} {u : E d × ℝ → ℝ}
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {M : ℝ}
    (hg : ∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) :
    ∀ p ∈ closure S.U ×ˢ Ici 0, 0 ≤ u p := by
  have hM : betaEps β ε (max M ε) = 0 := by
    rw [betaEps, hβ.eq_zero_of_one_le, zero_div]
    rw [le_div_iff₀ hε, one_mul]
    exact le_max_right _ _
  exact fun p hp ↦ (hu.mem_Icc hβ hε (hβ.betaEps_zero ε) hM (fun x hx ↦
    ⟨(hg x hx).1, (hg x hx).2.trans (le_max_left _ _)⟩) p hp).1

/-- Lipschitz data on the compact `Ū` are bounded. -/
theorem Setting.exists_bound_of_lipschitzOnWith (S : Setting d) {g : E d → ℝ} {L : ℝ≥0}
    (hg : LipschitzOnWith L g (closure S.U)) : ∃ M : ℝ, ∀ x ∈ closure S.U, g x ≤ M := by
  obtain ⟨M, hM⟩ := S.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hg.continuousOn
  exact ⟨M, fun x hx ↦ (le_abs_self _).trans (hM x hx)⟩

/-- `|Q'| ≤ Q_max` for a coefficient with values in `[Q_min, Q_max]`. -/
theorem Setting.abs_le_Qmax (S : Setting d) {Q' : E d → ℝ}
    (h : ∀ x, S.Qmin ≤ Q' x ∧ Q' x ≤ S.Qmax) (x : E d) : |Q' x| ≤ S.Qmax := by
  rw [abs_of_nonneg (S.Qmin_pos.le.trans (h x).1)]; exact (h x).2

/-! ### Proposition A.5 and Lemma A.7 -/

/-- **Proposition A.5**, i.e. the interior Lipschitz bound (3.9) of Proposition 3.8(iv), for
solutions of (3.4): there is a constant `C` (depending on the setting and on `β` only, in
particular not on `ε`) such that every solution `u` of (3.4) with nonnegative data
`g`, Lipschitz on `Ū`, satisfies `‖∇u‖_{L^∞(Q_r(x,t))} ≤ C (r⁻¹ ‖u‖_{L^∞(Q_{2r}(x,t))} + 1)`
whenever `Q_{2r}(x, t) ⊆ U_∞` and `0 < r ≤ 1`.

Proof: smooth approximation of `Q` (`IsSemilinearSolution.exists_smooth_approx`), the smooth
estimate `bernstein_interior_smooth` for the approximate solutions, and
`norm_gradient_le_of_tendsto_pointwise`. -/
theorem exists_interiorLipEst (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) :
    ∃ C : ℝ, ∀ ε > 0, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ),
      (∃ L : ℝ≥0, LipschitzOnWith L g (closure S.U)) → (∀ x ∈ closure S.U, 0 ≤ g x) →
      IsSemilinearSolution S.U S.Q β ε g u → InteriorLipEst S.U u C := by
  obtain ⟨K, hK⟩ := S.lip
  obtain ⟨C, hC⟩ := bernstein_interior_smooth (d := d) hβ S.Qmax (2 * S.Qmax * K)
  refine ⟨C, fun ε hε g u ⟨L, hgL⟩ hg0 hu ↦ ?_⟩
  obtain ⟨Mg, hMg⟩ := S.exists_bound_of_lipschitzOnWith hgL
  have hgM : ∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ max Mg 0 := fun x hx ↦
    ⟨hg0 x hx, (hMg x hx).trans (le_max_left _ _)⟩
  intro x t r hr hr1 hcyl M hM p hp
  obtain ⟨hball, ht0⟩ := parCyl_subset_UInf (by positivity) hcyl
  -- the approximate solutions
  have happrox := hu.exists_smooth_approx S hβ hε hgL (le_max_right Mg 0) hgM hK
  choose Sn gn un hSU _ _ hQs hQlip hQmem _ _ hgmem hun hclose using
    fun n : ℕ ↦ happrox (1 / (n + 1)) (by positivity) (t + 1)
  -- the estimate for the approximate solutions
  have hest : ∀ n : ℕ, ∀ q ∈ parCyl x t r,
      ‖gradₓ (un n) q‖ ≤ C * ((M + 1 / (n + 1)) / r + 1) := by
    intro n
    have hsmooth : ContDiffOn ℝ ∞ (un n) (S.U ×ˢ Ioi 0) :=
      Registry.semilinear_contDiffOn_of_contDiff S.isOpen isOpen_Ioi (hQs n) hβ hε (hun n).2.1
    have hsub : ball x (2 * r) ×ˢ Ioi (t - (2 * r) ^ 2) ⊆ S.U ×ˢ Ioi 0 :=
      prod_mono hball fun s hs ↦ by simp only [mem_Ioi] at hs ⊢; linarith
    refine hC ε hε (Sn n).Q (hQs n) (S.abs_le_Qmax (hQmem n))
      (norm_gradient_sq_le (hQlip n) ((hQs n).differentiable (by simp))
        (S.abs_le_Qmax (hQmem n))) (un n) x t r hr hr1 (hsmooth.mono hsub)
      (fun q hq ↦ (hun n).2.1.2.2.2.2.2.2 q (hsub hq)) (M + 1 / (n + 1)) (fun q hq ↦ ?_)
    have hqU : q ∈ closure S.U ×ˢ Icc 0 (t + 1) :=
      ⟨subset_closure (hcyl hq).1, (mem_Ioi.1 (hcyl hq).2).le, by linarith [hq.2.2]⟩
    have h1 := hclose n q.1 hqU.1 q.2 hqU.2
    have h2 := hM q hq
    have hun' : IsSemilinearSolution (Sn n).U (Sn n).Q β ε (gn n) (un n) := by
      rw [hSU n]; exact hun n
    have h3 := hun'.nonneg_of_nonneg hβ hε (fun y _ ↦ hgmem n y) q
      ⟨by rw [hSU n]; exact hqU.1, hqU.2.1⟩
    rw [abs_le] at h1 h2
    exact ⟨h3, by linarith⟩
  -- pass to the limit on the time slice through `p`
  obtain ⟨y, s⟩ := p
  have hVp : ∀ z ∈ ball x r, (z, s) ∈ parCyl x t r := fun z hz ↦ ⟨hz, hp.2⟩
  have hlimC : Tendsto (fun n : ℕ ↦ C * ((M + 1 / ((n : ℝ) + 1)) / r + 1)) atTop
      (𝓝 (C * (M / r + 1))) := by
    have h0 : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (((h0.const_add M).div_const r).add_const 1).const_mul C
    rwa [add_zero] at h1
  have hsubcyl : parCyl x t r ⊆ parCyl x t (2 * r) :=
    prod_mono (ball_subset_ball (by linarith)) (Ioc_subset_Ioc_left (by nlinarith))
  have hcyl2 : parCyl x t r ⊆ UInf S.U := hsubcyl.trans hcyl
  have hy : y ∈ ball x r := hp.1
  have key := norm_gradient_le_of_tendsto_pointwise (l := atTop) (F := fun n z ↦ un n (z, s))
    (C := fun n : ℕ ↦ C * ((M + 1 / ((n : ℝ) + 1)) / r + 1)) (f := fun z ↦ u (z, s))
    isOpen_ball (convex_ball x r) ?_ ?_ hlimC ?_ hy
  · exact key
  · intro n z hz
    have hzU : (z, s) ∈ S.U ×ˢ Ioi 0 := hcyl2 (hVp z hz)
    exact (((hun n).2.1.2.1 s hzU.2).contDiffAt (S.isOpen.mem_nhds hzU.1)).differentiableAt
      (by norm_num)
  · intro n z hz
    exact hest n (z, s) (hVp z hz)
  · intro z hz
    have hzU : (z, s) ∈ S.U ×ˢ Ioi 0 := hcyl2 (hVp z hz)
    have hs1 : s ∈ Icc 0 (t + 1) := ⟨(mem_Ioi.1 hzU.2).le, by linarith [hp.2.2]⟩
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [Real.norm_eq_abs]
    exact hclose n z (subset_closure hzU.1) s hs1

/-- **Lemma A.7**, second part of Proposition 3.8(iv): for `V ⊂⊂ U` and bounds `L`, `M` there
is `C_V` such that for `0 < ε ≤ 1`, every solution `u` of (3.4) with data `0 ≤ g ≤ M`,
`L`-Lipschitz on `Ū`, satisfies `sup_{t > 0} ‖∇u(·, t)‖_{L^∞(V)} ≤ C_V`.

Proof: smooth approximation of `Q` and `g` (`IsSemilinearSolution.exists_smooth_approx`), the
smooth initial-data estimate `bernstein_initial_smooth` (Proposition A.6) on
`B_{2r}(x) × [0, ∞)` with `2r ≤ dist(V, ∂U)`, the continuity of `∇u` at `t = 0` for smooth data
(`IsSemilinearSolution.continuousOn_gradₓ_of_contDiff`), and
`norm_gradient_le_of_tendsto_pointwise`. -/
theorem exists_norm_gradₓ_le (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {V : Set (E d)} (hV : CompactlyContained V S.U) (L : ℝ≥0) (M : ℝ) :
    ∃ CV : ℝ, ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ (g : E d → ℝ) (u : E d × ℝ → ℝ),
      LipschitzOnWith L g (closure S.U) → (∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) →
      IsSemilinearSolution S.U S.Q β ε g u →
      ∀ x ∈ V, ∀ t : ℝ, 0 < t → ‖gradₓ u (x, t)‖ ≤ CV := by
  obtain ⟨K, hK⟩ := S.lip
  obtain ⟨C, hC⟩ := bernstein_initial_smooth (d := d) hβ S.Qmax (2 * S.Qmax * K)
  obtain ⟨δ, hδ, hδU⟩ := hV.1.exists_cthickening_subset_open S.isOpen hV.2
  set r := min 1 (δ / 2) with hr
  have hr0 : 0 < r := lt_min one_pos (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  refine ⟨C * (L + max M 1 / r + 1), fun ε hε g u hgL hgM hu x hx t ht ↦ ?_⟩
  have hball : ball x (2 * r) ⊆ S.U := by
    refine (ball_subset_ball ?_).trans ((ball_subset_thickening (subset_closure hx) δ).trans
      ((thickening_subset_cthickening _ _).trans hδU))
    linarith [min_le_right 1 (δ / 2)]
  have hgM' : ∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ max M 0 := fun x hx ↦
    ⟨(hgM x hx).1, (hgM x hx).2.trans (le_max_left _ _)⟩
  -- the approximate solutions
  have happrox := hu.exists_smooth_approx S hβ hε.1 hgL (le_max_right M 0) hgM' hK
  choose Sn gn un hSU _ _ hQs hQlip hQmem hgs hglip hgmem hun hclose using
    fun n : ℕ ↦ happrox (1 / (n + 1)) (by positivity) (t + 1)
  -- the estimate for the approximate solutions
  have hest : ∀ n : ℕ, ∀ z ∈ ball x r, ‖gradₓ (un n) (z, t)‖ ≤ C * (L + max M 1 / r + 1) := by
    intro n z hz
    have hun' : IsSemilinearSolution (Sn n).U (Sn n).Q β ε (gn n) (un n) := by
      rw [hSU n]; exact hun n
    have hsmooth : ContDiffOn ℝ ∞ (un n) (S.U ×ˢ Ioi 0) :=
      Registry.semilinear_contDiffOn_of_contDiff S.isOpen isOpen_Ioi (hQs n) hβ hε.1 (hun n).2.1
    have hgrad : ContinuousOn (gradₓ (un n)) (S.U ×ˢ Ici 0) := by
      have := IsSemilinearSolution.continuousOn_gradₓ_of_contDiff (Sn n) hβ hε.1 (hQs n) (hgs n)
        hun'
      rwa [hSU n] at this
    have hbd := hun'.nonneg_le_max hβ hε.1 hε.2 (M := max M 0) (fun y _ ↦ hgmem n y)
    have hsub : ball x (2 * r) ×ˢ Ioi (0 : ℝ) ⊆ S.U ×ˢ Ioi 0 := prod_mono hball subset_rfl
    have hsubc : ball x (2 * r) ×ˢ Ici (0 : ℝ) ⊆ S.U ×ˢ Ici 0 := prod_mono hball subset_rfl
    refine hC ε hε.1 (Sn n).Q (hQs n) (S.abs_le_Qmax (hQmem n))
      (norm_gradient_sq_le (hQlip n) ((hQs n).differentiable (by simp)) (S.abs_le_Qmax (hQmem n)))
      (un n) x r 0 hr0 hr1 (hsmooth.mono hsub)
      (fun q hq ↦ (hun n).2.1.2.2.2.2.2.2 q (hsub hq))
      ((hun n).1.mono (prod_mono (hball.trans subset_closure) subset_rfl))
      (hgrad.mono hsubc) (max M 1) L (fun q hq ↦ ?_) (fun y hy ↦ ?_) z hz t ht.le
    · have := hbd q ⟨by rw [hSU n]; exact subset_closure (hball hq.1), hq.2⟩
      exact ⟨this.1, this.2.trans
        (max_le (max_le (le_max_left _ _) (le_max_of_le_right zero_le_one)) (le_max_right _ _))⟩
    · rw [hun'.gradₓ_zero (by rw [hSU n]; exact hball hy), norm_gradient_eq_norm_fderiv]
      exact norm_fderiv_le_of_lipschitz ℝ (hglip n)
  -- pass to the limit on the time slice
  refine norm_gradient_le_of_tendsto_pointwise (l := atTop) (F := fun n z ↦ un n (z, t))
    (C := fun _ : ℕ ↦ C * (L + max M 1 / r + 1)) (f := fun z ↦ u (z, t))
    isOpen_ball (convex_ball x r) (fun n z hz ↦ ?_) (fun n z hz ↦ hest n z hz) tendsto_const_nhds
    (fun z hz ↦ ?_) (mem_ball_self hr0)
  · have hzU : z ∈ S.U := hball (ball_subset_ball (by linarith) hz)
    exact (((hun n).2.1.2.1 t ht).contDiffAt (S.isOpen.mem_nhds hzU)).differentiableAt
      (by norm_num)
  · have hzU : z ∈ S.U := hball (ball_subset_ball (by linarith) hz)
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [Real.norm_eq_abs]
    exact hclose n z (subset_closure hzU) t ⟨ht.le, by linarith⟩

end PerronVariational

end
