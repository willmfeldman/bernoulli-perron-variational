/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.ViscosityLocal
import PerronVariational.Stationary.ViscosityJet

/-!
# Local extremality near the free boundary for uniformly strict data (the paper's proof)

Reference: F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

This file follows the paper's proof of [Lemma 2.8](#AFS:l.local-minimality) (`l.local-minimality`,
proved at the end of [§6](#AFS:s.conclusion)) for data `g` that are smooth strict sub/supersolutions
in the sense of [Definition 2.3](#AFS:d.strict-sub) (`IsUnifStrictSub`, `IsUnifStrictSuper`:
`Δg ≥ δ₀`, resp. `Δg ≤ -δ₀`, in `{g > -a₀}`). The general versions in
`PerronVariational.Stationary.ViscosityLocal` (for `Δg ≥ 0`, resp. `Δg ≤ 0`) need longer arguments;
the ones here are the paper's.

* The remark after [Definition 2.3](#AFS:d.strict-sub): constants (`IsUnifStrictSubWith`,
  `IsUnifStrictSuperWith`) and shifts `g + a`, `|a| ≤ a₀/2` (`IsUnifStrictSubWith.add_const`, …).
* `exists_smooth_le_of_contDiff_two`: a smooth minorant of a `C²` function with the same 1-jet and
  a Laplacian lowered by an arbitrarily small amount. This is the one step the paper leaves
  implicit: `g` is only `C²`, while [Definition 2.1](#AFS:d.stationary-viscosity) tests with `C^∞`
  functions. Because of the strict margin `δ₀`, the smooth minorant (resp. majorant) is still
  strictly sub- (resp. super-) harmonic at the touching point, so testing with it is the same as
  testing with `g`.
* Smallest case. "Since `u` is a viscosity supersolution it cannot touch `g` from above … So
  `u > g` in `U`": `IsViscSuper.lt_of_isUnifStrictSub`. Then [Lemma 2.8](#AFS:l.local-minimality):
  `perronSmallest_isLocalSmallestSuper_near_fb_unif`.
* Largest case. "`g` is a smooth strict supersolution so it cannot touch `u` from above at `x`,
  i.e. `g(x) > 0`": `IsViscSub.pos_of_isUnifStrictSuper`. "`v` is subharmonic in `B`":
  `IsViscSub.laplacian_nonneg_of_touch`. "By maximum principle `v ≤ g` in `B`":
  `IsViscSub.le_of_laplacian_neg`. Then [Lemma 2.8](#AFS:l.local-minimality):
  `perronLargest_isLocalLargestSub_near_fb_unif`.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Constants and shifts (the remark after [Definition 2.3](#AFS:d.strict-sub)) -/

/-- `g` is a smooth strict subsolution in the sense of [Definition 2.3](#AFS:d.strict-sub)
with the explicit constants `a₀, δ₀`. -/
def IsUnifStrictSubWith (U : Set (E d)) (Q g : E d → ℝ) (a₀ δ₀ : ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ 0 < a₀ ∧ 0 < δ₀ ∧ a₀ ≤ 1 / 2 ∧ δ₀ ≤ 1 / 2 ∧
    (∀ x ∈ closure U, -a₀ < g x → δ₀ ≤ Δ g x) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → (1 + δ₀) * Q x ^ 2 ≤ ‖∇ g x‖ ^ 2

/-- `g` is a smooth strict supersolution in the sense of [Definition 2.3](#AFS:d.strict-sub)
with the explicit constants `a₀, δ₀`. -/
def IsUnifStrictSuperWith (U : Set (E d)) (Q g : E d → ℝ) (a₀ δ₀ : ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ 0 < a₀ ∧ 0 < δ₀ ∧ a₀ ≤ 1 / 2 ∧ δ₀ ≤ 1 / 2 ∧
    (∀ x ∈ closure U, -a₀ < g x → Δ g x ≤ -δ₀) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → ‖∇ g x‖ ^ 2 ≤ (1 - δ₀) * Q x ^ 2

section Constants

variable {U : Set (E d)} {Q g : E d → ℝ}

theorem isUnifStrictSub_iff :
    IsUnifStrictSub U Q g ↔ ∃ a₀ δ₀, IsUnifStrictSubWith U Q g a₀ δ₀ := by
  constructor
  · rintro ⟨hg, a₀, ha₀, δ₀, hδ₀, h0, h1, h2, h3⟩; exact ⟨a₀, δ₀, hg, ha₀, hδ₀, h0, h1, h2, h3⟩
  · rintro ⟨a₀, δ₀, hg, ha₀, hδ₀, h0, h1, h2, h3⟩; exact ⟨hg, a₀, ha₀, δ₀, hδ₀, h0, h1, h2, h3⟩

theorem isUnifStrictSuper_iff :
    IsUnifStrictSuper U Q g ↔ ∃ a₀ δ₀, IsUnifStrictSuperWith U Q g a₀ δ₀ := by
  constructor
  · rintro ⟨hg, a₀, ha₀, δ₀, hδ₀, h0, h1, h2, h3⟩; exact ⟨a₀, δ₀, hg, ha₀, hδ₀, h0, h1, h2, h3⟩
  · rintro ⟨a₀, δ₀, hg, ha₀, hδ₀, h0, h1, h2, h3⟩; exact ⟨hg, a₀, ha₀, δ₀, hδ₀, h0, h1, h2, h3⟩

/-- The remark after [Definition 2.3](#AFS:d.strict-sub): for `|a| ≤ a₀/2`, the shift `g + a`
of a strict subsolution is a strict subsolution with `a₀` replaced by `a₀/2` and the same `δ₀`. -/
theorem IsUnifStrictSubWith.add_const {a₀ δ₀ : ℝ} (h : IsUnifStrictSubWith U Q g a₀ δ₀) {a : ℝ}
    (ha : |a| ≤ a₀ / 2) : IsUnifStrictSubWith U Q (fun x ↦ g x + a) (a₀ / 2) δ₀ := by
  obtain ⟨hg, ha₀, hδ₀, ha₁, hδ₁, h1, h2⟩ := h
  have hab := abs_le.1 ha
  refine ⟨hg.add contDiff_const, half_pos ha₀, hδ₀, by linarith, hδ₁, fun x hx hgx ↦ ?_,
    fun x hx hgx ↦ ?_⟩
  · rw [laplacian_add_const hg.contDiffAt]
    exact h1 x hx (by linarith)
  · rw [gradient_add_const]
    refine h2 x hx ?_
    have := abs_le.1 hgx
    rw [abs_le]; constructor <;> linarith

/-- The remark after [Definition 2.3](#AFS:d.strict-sub): for `|a| ≤ a₀/2`, the shift `g + a`
of a strict supersolution is a strict supersolution with `a₀` replaced by `a₀/2` and the same
`δ₀`. -/
theorem IsUnifStrictSuperWith.add_const {a₀ δ₀ : ℝ} (h : IsUnifStrictSuperWith U Q g a₀ δ₀)
    {a : ℝ} (ha : |a| ≤ a₀ / 2) :
    IsUnifStrictSuperWith U Q (fun x ↦ g x + a) (a₀ / 2) δ₀ := by
  obtain ⟨hg, ha₀, hδ₀, ha₁, hδ₁, h1, h2⟩ := h
  have hab := abs_le.1 ha
  refine ⟨hg.add contDiff_const, half_pos ha₀, hδ₀, by linarith, hδ₁, fun x hx hgx ↦ ?_,
    fun x hx hgx ↦ ?_⟩
  · rw [laplacian_add_const hg.contDiffAt]
    exact h1 x hx (by linarith)
  · rw [gradient_add_const]
    refine h2 x hx ?_
    have := abs_le.1 hgx
    rw [abs_le]; constructor <;> linarith

/-- Shifts of a strict subsolution ([Definition 2.3](#AFS:d.strict-sub)) by small constants are
strict subsolutions (the remark after [Definition 2.3](#AFS:d.strict-sub)). -/
theorem IsUnifStrictSub.exists_add_const (h : IsUnifStrictSub U Q g) :
    ∃ a₀ > 0, ∀ a : ℝ, |a| ≤ a₀ / 2 → IsUnifStrictSub U Q (fun x ↦ g x + a) := by
  obtain ⟨a₀, δ₀, hw⟩ := isUnifStrictSub_iff.1 h
  exact ⟨a₀, hw.2.1, fun a ha ↦ isUnifStrictSub_iff.2 ⟨_, _, hw.add_const ha⟩⟩

/-- Shifts of a strict supersolution ([Definition 2.3](#AFS:d.strict-sub)) by small constants are
strict supersolutions (the remark after [Definition 2.3](#AFS:d.strict-sub)). -/
theorem IsUnifStrictSuper.exists_add_const (h : IsUnifStrictSuper U Q g) :
    ∃ a₀ > 0, ∀ a : ℝ, |a| ≤ a₀ / 2 → IsUnifStrictSuper U Q (fun x ↦ g x + a) := by
  obtain ⟨a₀, δ₀, hw⟩ := isUnifStrictSuper_iff.1 h
  exact ⟨a₀, hw.2.1, fun a ha ↦ isUnifStrictSuper_iff.2 ⟨_, _, hw.add_const ha⟩⟩

end Constants

/-! ### Testing with `C²` functions -/

/-- **Smooth minorant with prescribed 1-jet.** For `H ∈ C²`, `z` and `η > 0` there is a smooth
`φ` with `φ(z) = H(z)`, `∇φ(z) = ∇H(z)`, `Δφ(z) = ΔH(z) - 2dη` and `φ ≤ H` near `z`. (The
negative of `exists_smooth_ge_of_contDiff_two` applied to `-H`.) -/
theorem exists_smooth_le_of_contDiff_two {H : E d → ℝ} (hH : ContDiff ℝ 2 H) (z : E d) {η : ℝ}
    (hη : 0 < η) :
    ∃ φ : E d → ℝ, ContDiff ℝ ∞ φ ∧ φ z = H z ∧ ∇ φ z = ∇ H z ∧
      Δ φ z = Δ H z - 2 * (Module.finrank ℝ (E d) : ℝ) * η ∧ ∀ᶠ y in 𝓝 z, φ y ≤ H y := by
  obtain ⟨ψ, hψs, hψz, hψg, hψl, hψle⟩ := exists_smooth_ge_of_contDiff_two hH.neg z hη
  have e : (fun x ↦ -H x) = -H := rfl
  rw [e] at hψg hψl
  have hng : ∀ f : E d → ℝ, ∇ (-f) z = -∇ f z := fun f ↦ by
    simp [gradient, fderiv_neg]
  refine ⟨-ψ, hψs.neg, ?_, ?_, ?_, ?_⟩
  · simp [hψz]
  · rw [hng, hψg, hng, neg_neg]
  · rw [InnerProductSpace.laplacian_neg, Pi.neg_apply, hψl, InnerProductSpace.laplacian_neg,
      Pi.neg_apply]
    ring
  · filter_upwards [hψle] with y hy
    simp only [Pi.neg_apply] at hy ⊢
    linarith

/-- The margin used below: `2 n (δ / (4 (n + 1))) ≤ δ / 2` for `n ≥ 0`, `δ ≥ 0`. -/
theorem two_mul_mul_div_le_half {n δ : ℝ} (hn : 0 ≤ n) (hδ : 0 ≤ δ) :
    2 * n * (δ / (4 * (n + 1))) ≤ δ / 2 := by
  rw [show 2 * n * (δ / (4 * (n + 1))) = δ / 2 * (n / (n + 1)) by field_simp; ring]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))

/-! ### [Lemma 2.8](#AFS:l.local-minimality), smallest supersolution case -/

/-- **[Lemma 2.8](#AFS:l.local-minimality), first step (paper route).** "Since `u` is a viscosity
supersolution it cannot touch `g` from above, that would contradict the definition of viscosity
solution. So `u > g` in `U`." Here `g ≤ u` in `U` and `g` is a smooth strict subsolution in the
sense of [Definition 2.3](#AFS:d.strict-sub); at a point `x ∈ U` with `Q(x) > 0` we get
`g(x) < u(x)`.

Proof: if `g(x) = u(x)` then `g` touches `u` from below at `x`, and `g(x) = u(x) ≥ 0 > -a₀`, so
`Δg(x) ≥ δ₀`; where moreover `g(x) = 0`, `|∇g(x)|² ≥ (1 + δ₀) Q(x)² > Q(x)²`. Both alternatives of
[Definition 2.1(i)](#AFS:d.stationary-viscosity) fail. Since `g` is only `C²`, the test function is
a smooth minorant of `g` with the same 1-jet and Laplacian `≥ Δg(x) - δ₀/2 ≥ δ₀/2`
(`exists_smooth_le_of_contDiff_two`). -/
theorem IsViscSuper.lt_of_isUnifStrictSub {U : Set (E d)} {Q u g : E d → ℝ}
    (hu : IsViscSuper U Q u) (hg : IsUnifStrictSub U Q g) (hgu : ∀ y ∈ U, g y ≤ u y) {x : E d}
    (hx : x ∈ U) (hQ : 0 < Q x) : g x < u x := by
  obtain ⟨hg2, a₀, ha₀, δ₀, hδ₀, -, -, h1, h2⟩ := hg
  refine lt_of_le_of_ne (hgu x hx) fun hgx ↦ ?_
  have hn0 : (0 : ℝ) ≤ Module.finrank ℝ (E d) := Nat.cast_nonneg _
  have hη : 0 < δ₀ / (4 * ((Module.finrank ℝ (E d) : ℝ) + 1)) := by positivity
  obtain ⟨φ, hφs, hφx, hφg, hφl, hφle⟩ := exists_smooth_le_of_contDiff_two hg2 x hη
  -- the smooth minorant touches `u` from below at `x`
  have htouch : TouchesBelow φ u U x := by
    refine ⟨hx, hφx.trans hgx, ?_⟩
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hφle] with y hyU hy
    exact hy.trans (hgu y hyU)
  have hxc : x ∈ closure U := subset_closure hx
  have hΔ : δ₀ ≤ Δ g x := h1 x hxc (by linarith [hu.2.1 x hx])
  have hm := two_mul_mul_div_le_half hn0 hδ₀.le
  rcases hu.2.2 φ hφs x hx htouch with h | ⟨h0, h3⟩
  · rw [hφl] at h
    linarith
  · rw [hφx] at h0
    rw [hφg] at h3
    have hq := h2 x hxc (by rw [h0, abs_zero]; exact ha₀.le)
    have h4 : ‖∇ g x‖ ^ 2 ≤ Q x ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [mul_pos hδ₀ (pow_pos hQ 2)]

open Classical in
/-- **[Lemma 2.8](#AFS:l.local-minimality)**, smallest supersolution case, following the paper's
proof, for a smooth strict subsolution `g` in the sense of
[Definition 2.3](#AFS:d.strict-sub). Assume (outputs of [Proposition 6.1](#AFS:p.inner-smallest))
that Perron's smallest supersolution `u` above `g` is a viscosity supersolution in `U` and
continuous on `Ū`. Then every free boundary point `x` has a ball `B_r(x) ⊂⊂ U` in which `u` is a
local smallest supersolution.

Proof (the paper's): `u > g` in `U` (`IsViscSuper.lt_of_isUnifStrictSub`), so `g(x) < u(x) = 0`
and `g < 0` on some `B̄_r(x) ⊆ U`. A competitor `v` in `B_r(x)`, equal to `u` off `B ⊂⊂ B_r(x)`
and extended by `u`, is a supersolution in `U` with `v = u ≥ g₊` off `B` and `v ≥ 0 ≥ g` in `B`;
so `v ∈ 𝒮_g` and `v ≥ u`. -/
theorem perronSmallest_isLocalSmallestSuper_near_fb_unif {U : Set (E d)} {Q g : E d → ℝ}
    (hU : IsOpen U) (hQ : ∀ y ∈ U, 0 < Q y) (hg : IsUnifStrictSub U Q g)
    (hne : (perronSuperClass U Q g).Nonempty)
    (hsuper : IsViscSuper U Q (perronSmallest U Q g))
    (hcont : ContinuousOn (perronSmallest U Q g) (closure U)) {x : E d}
    (hx : x ∈ freeBoundary (perronSmallest U Q g) U) :
    ∃ r > 0, closedBall x r ⊆ U ∧ IsLocalSmallestSuper (ball x r) Q (perronSmallest U Q g) := by
  set u := perronSmallest U Q g with hu_def
  have hxU : x ∈ U := hx.2
  have hux : u x = 0 := eq_zero_of_mem_freeBoundary hU hsuper.1 hsuper.2.1 hx
  have hgu : ∀ y ∈ U, g y ≤ u y := fun y hy ↦ le_perronSmallest' hne (subset_closure hy)
  -- `u > g` in `U`, hence `g(x) < 0`
  have hgx : g x < 0 := hux ▸ hsuper.lt_of_isUnifStrictSub hg hgu hxU (hQ x hxU)
  have hgc : Continuous g := hg.1.continuous
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.eventually_nhds_iff.1
    ((show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hxU).and
      (hgc.continuousAt.eventually (gt_mem_nhds hgx)))
  set r := r₁ / 2 with hr
  have hr0 : 0 < r := half_pos hr₁
  have hB : ∀ y ∈ closedBall x r, y ∈ U ∧ g y < 0 :=
    fun y hy ↦ hr₁' (lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hr₁))
  have hBU : closedBall x r ⊆ U := fun y hy ↦ (hB y hy).1
  have hbU : ball x r ⊆ U := ball_subset_closedBall.trans hBU
  refine ⟨r, hr0, hBU, hsuper.mono isOpen_ball hbU, ?_⟩
  intro y s hs hys v hv hvu z hz
  -- the competitor extended by `u`
  set w := (ball x r).piecewise v u with hw
  have hw_out : ∀ z ∉ closedBall y s, w z = u z := by
    intro z hz'
    by_cases hzb : z ∈ ball x r
    · rw [hw, piecewise_eq_of_mem _ _ _ hzb]
      exact hvu z ⟨hzb, fun h ↦ hz' (ball_subset_closedBall h)⟩
    · rw [hw, piecewise_eq_of_notMem _ _ _ hzb]
  have hwS : w ∈ perronSuperClass U Q g := by
    refine ⟨fun z hz ↦ ?_, ?_, fun z hz ↦ ?_⟩
    · by_cases hzb : z ∈ ball x r
      · have hc : ContinuousAt v z := hv.1.continuousAt (isOpen_ball.mem_nhds hzb)
        exact (hc.congr (Filter.mem_of_superset (isOpen_ball.mem_nhds hzb)
          fun y hy ↦ (piecewise_eq_of_mem _ _ _ hy).symm)).continuousWithinAt
      · have hzK : z ∉ closedBall y s := fun h ↦ hzb (hys h)
        refine (hcont z hz).congr_of_eventuallyEq ?_ (hw_out z hzK)
        exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset
          (isClosed_closedBall.isOpen_compl.mem_nhds hzK) fun y hy ↦ hw_out y hy)
    · exact isViscSuper_piecewise hU isOpen_ball hbU isClosed_closedBall hys hsuper hv
        fun z hz ↦ hvu z ⟨hz.1, fun h ↦ hz.2 (ball_subset_closedBall h)⟩
    · by_cases hzb : z ∈ ball x r
      · rw [hw, piecewise_eq_of_mem _ _ _ hzb]
        exact max_le (((hB z (ball_subset_closedBall hzb)).2).le.trans (hv.2.1 z hzb))
          (hv.2.1 z hzb)
      · rw [hw, piecewise_eq_of_notMem _ _ _ hzb]
        exact le_perronSmallest hne hz
  have := perronSmallest_le hwS (subset_closure (hbU hz))
  rwa [hw, piecewise_eq_of_mem _ _ _ hz] at this

/-- **[Lemma 2.8](#AFS:l.local-minimality)**, smallest supersolution case, paper route, in the
standing setting. -/
theorem Setting.perronSmallest_isLocalSmallestSuper_near_fb_unif (S : Setting d) {g : E d → ℝ}
    (hg : IsUnifStrictSub S.U S.Q g) (hsuper : IsViscSuper S.U S.Q (perronSmallest S.U S.Q g))
    (hcont : ContinuousOn (perronSmallest S.U S.Q g) (closure S.U)) {x : E d}
    (hx : x ∈ freeBoundary (perronSmallest S.U S.Q g) S.U) :
    ∃ r > 0, closedBall x r ⊆ S.U ∧
      IsLocalSmallestSuper (ball x r) S.Q (perronSmallest S.U S.Q g) :=
  PerronVariational.perronSmallest_isLocalSmallestSuper_near_fb_unif S.isOpen
    (fun y hy ↦ S.Qmin_pos.trans_le (S.Q_mem y (subset_closure hy)).1) hg
    (S.perronSuperClass_nonempty hg.1.continuous.continuousOn) hsuper hcont hx

/-! ### [Lemma 2.8](#AFS:l.local-minimality), largest subsolution case -/

/-- **[Lemma 2.8](#AFS:l.local-minimality), largest case, first step (paper route).** "`g` is a
smooth strict supersolution so it cannot touch `u` from above at `x`, i.e. `g(x) > 0`." Here `u` is
a viscosity subsolution in `U` with `u ≤ g₊`, `x` a free boundary point of `u` with `Q(x) > 0`, and
`g` a smooth strict supersolution in the sense of [Definition 2.3](#AFS:d.strict-sub).

Proof: `g(x) ≥ 0` since `x ∈ \overline{{u > 0}}` and `u ≤ g₊`. If `g(x) = 0 = u(x)`, then `g₊`
touches `u` from above at `x`; but `Δg(x) ≤ -δ₀ < 0` (as `g(x) = 0 > -a₀`) and
`|∇g(x)|² ≤ (1 - δ₀) Q(x)² < Q(x)²`, so both alternatives of
[Definition 2.1(ii)](#AFS:d.stationary-viscosity) fail. As in the smallest case, the test function
is a smooth majorant of `g` with the same 1-jet (`exists_smooth_ge_of_contDiff_two`), still strictly
superharmonic at `x` thanks to `δ₀`. -/
theorem IsViscSub.pos_of_isUnifStrictSuper {U : Set (E d)} {Q u g : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSub U Q u) (hg : IsUnifStrictSuper U Q g) (hug : ∀ y ∈ U, u y ≤ max (g y) 0)
    {x : E d} (hx : x ∈ freeBoundary u U) (hQ : 0 < Q x) : 0 < g x := by
  obtain ⟨hg2, a₀, ha₀, δ₀, hδ₀, -, -, h1, h2⟩ := hg
  have hux : u x = 0 := eq_zero_of_mem_freeBoundary hU hu.1 hu.2.1 hx
  have hxcl : x ∈ closure (posSet u U) := frontier_subset_closure hx.1
  -- `g(x) ≥ 0`
  have hgx : 0 ≤ g x := by
    have hsub' : posSet u U ⊆ {y | 0 ≤ g y} := by
      rintro y ⟨hyU, hy⟩
      by_contra hneg
      simp only [Set.mem_ofPred_eq, not_le] at hneg
      have := hug y hyU
      rw [max_eq_right hneg.le] at this
      linarith
    exact closure_minimal hsub' (isClosed_le continuous_const hg2.continuous) hxcl
  refine lt_of_le_of_ne hgx fun hgx0 ↦ ?_
  -- `g₊` touches `u` from above at `x`; test with a smooth majorant of `g`
  have hn0 : (0 : ℝ) ≤ Module.finrank ℝ (E d) := Nat.cast_nonneg _
  have hη : 0 < δ₀ / (4 * ((Module.finrank ℝ (E d) : ℝ) + 1)) := by positivity
  obtain ⟨φ, hφs, hφx, hφg, hφl, hφle⟩ := exists_smooth_ge_of_contDiff_two hg2 x hη
  have htouch : TouchesAbove (fun y ↦ max (φ y) 0) u (closure (posSet u U) ∩ U) x := by
    refine ⟨⟨hxcl, hx.2⟩, by
      change max (φ x) 0 = u x
      rw [hφx, ← hgx0, hux, max_self], ?_⟩
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hx.2), nhdsWithin_le_nhds hφle]
      with y hyU hy
    exact (hug y hyU).trans (max_le_max hy le_rfl)
  have hxc : x ∈ closure U := subset_closure hx.2
  have hΔ : Δ g x ≤ -δ₀ := h1 x hxc (by linarith)
  have hm := two_mul_mul_div_le_half hn0 hδ₀.le
  rcases hu.2.2 φ hφs x htouch with h | ⟨-, h3⟩
  · rw [hφl] at h
    linarith
  · rw [hφg] at h3
    have hq := h2 x hxc (by rw [← hgx0, abs_zero]; exact ha₀.le)
    have h4 : Q x ^ 2 ≤ ‖∇ g x‖ ^ 2 := pow_le_pow_left₀ hQ.le h3 2
    nlinarith [mul_pos hδ₀ (pow_pos hQ 2)]

/-- **A viscosity subsolution is subharmonic** (used in the proof of
[Lemma 2.8](#AFS:l.local-minimality): "`v` is subharmonic in `B`"). If `v` is a viscosity
subsolution in an open `W` and a smooth `φ` touches `v` from above at `z ∈ W` (in a neighbourhood of
`z`), then `Δφ(z) ≥ 0`.

Proof: if `v(z) > 0`, then `z ∈ \overline{{v > 0}}`, `φ₊` touches `v` from above there, and the
second alternative `φ(z) = 0` of [Definition 2.1(ii)](#AFS:d.stationary-viscosity) is excluded. If
`v(z) = 0`, then `φ ≥ v ≥ 0` near `z` and `φ(z) = 0`, so `z` is a local minimum of `φ`. -/
theorem IsViscSub.laplacian_nonneg_of_touch {W : Set (E d)} {Q v φ : E d → ℝ} (hW : IsOpen W)
    (hv : IsViscSub W Q v) (hφ : ContDiff ℝ ∞ φ) {z : E d} (hz : z ∈ W) (hφz : φ z = v z)
    (hle : ∀ᶠ y in 𝓝 z, v y ≤ φ y) : 0 ≤ Δ φ z := by
  rcases (hv.2.1 z hz).lt_or_eq with hpos | hzero
  · have htouch : TouchesAbove (fun y ↦ max (φ y) 0) v (closure (posSet v W) ∩ W) z := by
      refine ⟨⟨subset_closure ⟨hz, hpos⟩, hz⟩, by
        change max (φ z) 0 = v z
        rw [hφz]; exact max_eq_left hpos.le, ?_⟩
      filter_upwards [nhdsWithin_le_nhds hle] with y hy
      exact hy.trans (le_max_left _ _)
    rcases hv.2.2 φ hφ z htouch with h | ⟨h0, -⟩
    · exact h
    · rw [hφz] at h0; linarith
  · have hmin : ∀ᶠ y in 𝓝 z, φ z ≤ φ y := by
      filter_upwards [hle, hW.mem_nhds hz] with y hy hyW
      rw [hφz, ← hzero]
      exact (hv.2.1 y hyW).trans hy
    exact IsLocalMin.laplacian_nonneg (contDiff_two_of_smooth hφ) hmin

/-- **Maximum principle** against a classical strictly superharmonic function (used in the proof
of [Lemma 2.8](#AFS:l.local-minimality): "by maximum principle `v ≤ g` in `B`"). Let `v` be a
viscosity subsolution in an open `W`, `K ⊆ W` compact, and `H ∈ C²` with `ΔH < 0` in the interior of
`K`. If `v ≤ H` on the boundary of `K`, then `v ≤ H` on `K`.

Proof: otherwise `v - H` attains a positive maximum `t` over `K` at an interior point `z`; a smooth
majorant of `H + t` with the same 1-jet at `z` and still negative Laplacian touches `v` from
above at `z`, against `IsViscSub.laplacian_nonneg_of_touch`. -/
theorem IsViscSub.le_of_laplacian_neg {W K : Set (E d)} {Q v H : E d → ℝ} (hW : IsOpen W)
    (hv : IsViscSub W Q v) (hK : IsCompact K) (hKW : K ⊆ W) (hH : ContDiff ℝ 2 H)
    (hlap : ∀ z ∈ interior K, Δ H z < 0) (hbd : ∀ z ∈ frontier K, v z ≤ H z) :
    ∀ y ∈ K, v y ≤ H y := by
  intro y hy
  by_contra hcon
  push Not at hcon
  have hF : ContinuousOn (fun w ↦ v w - H w) K := (hv.1.mono hKW).sub hH.continuous.continuousOn
  obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn ⟨y, hy⟩ hF
  set t := v z - H z with ht
  have hty : v y - H y ≤ t := hzmax hy
  have ht0 : 0 < t := by linarith
  have hzint : z ∈ interior K := by
    by_contra hz
    linarith [hbd z ⟨subset_closure hzK, hz⟩]
  have hΔz := hlap z hzint
  have hn0 : (0 : ℝ) ≤ Module.finrank ℝ (E d) := Nat.cast_nonneg _
  have hη : 0 < -Δ H z / (4 * ((Module.finrank ℝ (E d) : ℝ) + 1)) :=
    div_pos (by linarith) (by positivity)
  obtain ⟨φ, hφs, hφz, -, hφl, hφle⟩ := exists_smooth_ge_of_contDiff_two
    (hH.add (contDiff_const (c := t))) z hη
  rw [laplacian_add_const hH.contDiffAt] at hφl
  have hle : ∀ᶠ w in 𝓝 z, v w ≤ φ w := by
    filter_upwards [mem_interior_iff_mem_nhds.1 hzint, hφle] with w hwK hw
    have : v w - H w ≤ t := hzmax hwK
    linarith
  have h := hv.laplacian_nonneg_of_touch hW hφs (hKW hzK) (by rw [hφz, ht]; ring) hle
  have hm := two_mul_mul_div_le_half hn0 (by linarith : 0 ≤ -Δ H z)
  rw [hφl] at h
  linarith

open Classical in
/-- **[Lemma 2.8](#AFS:l.local-minimality)**, largest subsolution case, following the paper's proof,
for a smooth strict supersolution `g` in the sense of [Definition 2.3](#AFS:d.strict-sub).
Assume (outputs of [Proposition 6.2](#AFS:p.inner-largest)) that Perron's largest subsolution `u`
below `g` is a viscosity subsolution in `U` and continuous on `Ū`. Then every free boundary point
`x` has a ball `B_r(x) ⊂⊂ U` in which `u` is a local largest subsolution.

Proof (the paper's): `g(x) > 0` (`IsViscSub.pos_of_isUnifStrictSuper`). Choose `B̄_r(x) ⊆ U` on
which `g > 0`, hence `Δg ≤ -δ₀ < 0` there. Let `v` be a viscosity subsolution in `B_r(x)` with
`v = u` off `B ⊂⊂ B_r(x)`. Then `v` is subharmonic in `B` and `v = u ≤ g` on `∂B`, so `v ≤ g` in `B`
by the maximum principle (`IsViscSub.le_of_laplacian_neg`). Thus `v`, extended by `u`, lies in
`𝒮^g` and `v ≤ u`. -/
theorem perronLargest_isLocalLargestSub_near_fb_unif {U : Set (E d)} {Q g : E d → ℝ}
    (hU : IsOpen U) (hQ : ∀ y ∈ U, 0 < Q y) (hg : IsUnifStrictSuper U Q g)
    (hsub : IsViscSub U Q (perronLargest U Q g))
    (hcont : ContinuousOn (perronLargest U Q g) (closure U)) {x : E d}
    (hx : x ∈ freeBoundary (perronLargest U Q g) U) :
    ∃ r > 0, closedBall x r ⊆ U ∧ IsLocalLargestSub (ball x r) Q (perronLargest U Q g) := by
  set u := perronLargest U Q g with hu_def
  have hxU : x ∈ U := hx.2
  have hug : ∀ y ∈ closure U, u y ≤ max (g y) 0 := fun y hy ↦ perronLargest_le hy
  -- `g(x) > 0`
  have hgx : 0 < g x :=
    hsub.pos_of_isUnifStrictSuper hU hg (fun y hy ↦ hug y (subset_closure hy)) hx (hQ x hxU)
  obtain ⟨hg2, a₀, ha₀, δ₀, hδ₀, -, -, h1, -⟩ := hg
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.eventually_nhds_iff.1
    ((show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hxU).and
      (hg2.continuous.continuousAt.eventually (lt_mem_nhds hgx)))
  set r := r₁ / 2 with hr
  have hr0 : 0 < r := half_pos hr₁
  have hB : ∀ y ∈ closedBall x r, y ∈ U ∧ 0 < g y :=
    fun y hy ↦ hr₁' (lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hr₁))
  have hBU : closedBall x r ⊆ U := fun y hy ↦ (hB y hy).1
  have hbU : ball x r ⊆ U := ball_subset_closedBall.trans hBU
  -- `g` is strictly superharmonic on `B̄_r(x)`
  have hΔ : ∀ y ∈ closedBall x r, Δ g y < 0 := fun y hy ↦
    (h1 y (subset_closure (hB y hy).1) (by linarith [(hB y hy).2])).trans_lt (neg_lt_zero.2 hδ₀)
  refine ⟨r, hr0, hBU, hsub.mono isOpen_ball hbU, ?_⟩
  intro y s hs hys v hv hvu z hz
  -- `v ≤ g` in `B = B_s(y)` by the maximum principle, hence `v ≤ g₊` in `B_r(x)`
  have hvB : ∀ w ∈ closedBall y s, v w ≤ g w := by
    refine hv.le_of_laplacian_neg isOpen_ball (isCompact_closedBall y s) hys hg2
      (fun w hw ↦ hΔ w (ball_subset_closedBall (hys (interior_subset hw)))) fun w hw ↦ ?_
    have hws : w ∈ sphere y s := frontier_closedBall_subset_sphere hw
    have hwB : w ∈ ball x r := hys (sphere_subset_closedBall hws)
    rw [hvu w ⟨hwB, fun h ↦ (ne_of_lt (mem_ball.1 h)) (mem_sphere.1 hws)⟩]
    exact (hug w (subset_closure (hbU hwB))).trans
      (max_eq_left (hB w (ball_subset_closedBall hwB)).2.le).le
  have hvg : ∀ w ∈ ball x r, v w ≤ max (g w) 0 := by
    intro w hw
    by_cases hwK : w ∈ closedBall y s
    · exact (hvB w hwK).trans (le_max_left _ _)
    · rw [hvu w ⟨hw, fun h ↦ hwK (ball_subset_closedBall h)⟩]
      exact hug w (subset_closure (hbU hw))
  -- the competitor extended by `u`
  set w := (ball x r).piecewise v u with hw
  have hw_out : ∀ z ∉ closedBall y s, w z = u z := by
    intro z hz'
    by_cases hzb : z ∈ ball x r
    · rw [hw, piecewise_eq_of_mem _ _ _ hzb]
      exact hvu z ⟨hzb, fun h ↦ hz' (ball_subset_closedBall h)⟩
    · rw [hw, piecewise_eq_of_notMem _ _ _ hzb]
  have hwS : w ∈ perronSubClass U Q g := by
    refine ⟨fun z hz ↦ ?_, ?_, fun z hz ↦ ?_⟩
    · by_cases hzb : z ∈ ball x r
      · have hc : ContinuousAt v z := hv.1.continuousAt (isOpen_ball.mem_nhds hzb)
        exact (hc.congr (Filter.mem_of_superset (isOpen_ball.mem_nhds hzb)
          fun y hy ↦ (piecewise_eq_of_mem _ _ _ hy).symm)).continuousWithinAt
      · have hzK : z ∉ closedBall y s := fun h ↦ hzb (hys h)
        refine (hcont z hz).congr_of_eventuallyEq ?_ (hw_out z hzK)
        exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset
          (isClosed_closedBall.isOpen_compl.mem_nhds hzK) fun y hy ↦ hw_out y hy)
    · exact isViscSub_piecewise hU isOpen_ball hbU isClosed_closedBall hys hsub hv
        fun z hz ↦ hvu z ⟨hz.1, fun h ↦ hz.2 (ball_subset_closedBall h)⟩
    · by_cases hzb : z ∈ ball x r
      · rw [hw, piecewise_eq_of_mem _ _ _ hzb]
        exact hvg z hzb
      · rw [hw, piecewise_eq_of_notMem _ _ _ hzb]
        exact hug z hz
  have := le_perronLargest hwS (subset_closure (hbU hz))
  rwa [hw, piecewise_eq_of_mem _ _ _ hz] at this

/-- **[Lemma 2.8](#AFS:l.local-minimality)**, largest subsolution case, paper route, in the standing
setting. -/
theorem Setting.perronLargest_isLocalLargestSub_near_fb_unif (S : Setting d) {g : E d → ℝ}
    (hg : IsUnifStrictSuper S.U S.Q g) (hsub : IsViscSub S.U S.Q (perronLargest S.U S.Q g))
    (hcont : ContinuousOn (perronLargest S.U S.Q g) (closure S.U)) {x : E d}
    (hx : x ∈ freeBoundary (perronLargest S.U S.Q g) S.U) :
    ∃ r > 0, closedBall x r ⊆ S.U ∧
      IsLocalLargestSub (ball x r) S.Q (perronLargest S.U S.Q g) :=
  PerronVariational.perronLargest_isLocalLargestSub_near_fb_unif S.isOpen
    (fun y hy ↦ S.Qmin_pos.trans_le (S.Q_mem y (subset_closure hy)).1) hg hsub hcont hx

end PerronVariational

end
