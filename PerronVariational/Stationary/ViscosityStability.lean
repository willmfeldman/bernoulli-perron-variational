/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.KLimit
public import PerronVariational.Defs.Stationary
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Order.CompletePartialOrder
import PerronVariational.Stationary.Perron
import PerronVariational.Stationary.ViscosityJet

/-!
# Stability of viscosity supersolutions and relaxed subsolutions (Lemma 2.4)

Lemma 2.4 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. The paper cites the proofs from
W. M. Feldman, N. Požár, *On convex comparison for exterior Bernoulli problems with discontinuous
anisotropy*, Interfaces Free Bound. 27 (2025), 459–468, doi:10.4171/ifb/525, Lemma 3.1, and from
W. M. Feldman, I. C. Kim, *The pinning effect of dilute defects*, arXiv:2512.11152, Lemma A.12;
here both parts are proved directly.

* `isViscSuper_of_tendstoLocallyUniformlyOn`: Lemma 2.4(i).
* `isRelaxedSub_of_tendstoLocallyUniformlyOn`: Lemma 2.4(ii), with `E* = upperKLimit E l`.

Both are stated along an arbitrary nontrivial filter `l` (the paper: `k → ∞`), and assume `Q`
continuous on `U` (true in the standing setting, where `Q` is Lipschitz).

Auxiliary exports: the quartic perturbation `φ ± |y - x|⁴` (`jet_add_quartic`,
`touchesBelow_strict_perturb`) and elementary facts on upper Kuratowski limits
(`isClosed_upperKLimit`, `upperKLimit_subset_closure`, `mem_upperKLimit_of_eventually_mem`,
`IsCompact.eventually_forall_not_mem_of_disjoint_upperKLimit`).
-/

open Set Filter Topology Metric Asymptotics
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Upper Kuratowski limits -/

section KLimit

variable {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} {l : Filter ι}

/-- The upper Kuratowski limit is closed. -/
theorem isClosed_upperKLimit : IsClosed (upperKLimit A l) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have : ∃ N ∈ 𝓝 x, ¬ ∃ᶠ i in l, (A i ∩ N).Nonempty := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hx hcon
  obtain ⟨N, hN, hfr⟩ := this
  obtain ⟨t, htN, ht, hxt⟩ := mem_nhds_iff.1 hN
  filter_upwards [ht.mem_nhds hxt] with y hy hyA
  exact hfr ((hyA t (ht.mem_nhds hy)).mono fun i hi ↦ hi.mono (inter_subset_inter_right _ htN))

/-- If eventually `A i ⊆ S`, then the upper Kuratowski limit lies in `closure S`. -/
theorem upperKLimit_subset_closure {S : Set X} (h : ∀ᶠ i in l, A i ⊆ S) :
    upperKLimit A l ⊆ closure S := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨i, ⟨y, hyA, hyt⟩, hi⟩ := ((hx t ht).and_eventually h).exists
  exact ⟨y, hyt, hi hyA⟩

/-- A point which eventually belongs to `A i` belongs to the upper Kuratowski limit. -/
theorem mem_upperKLimit_of_eventually_mem [l.NeBot] {x : X} (h : ∀ᶠ i in l, x ∈ A i) :
    x ∈ upperKLimit A l :=
  fun _ hN ↦ (h.mono fun _ hi ↦ ⟨x, hi, mem_of_mem_nhds hN⟩).frequently

/-- A compact set disjoint from the upper Kuratowski limit is eventually disjoint from `A i`. -/
theorem IsCompact.eventually_forall_not_mem_of_disjoint_upperKLimit {K : Set X}
    (hK : IsCompact K) (h : ∀ y ∈ K, y ∉ upperKLimit A l) :
    ∀ᶠ i in l, ∀ y ∈ K, y ∉ A i := by
  refine hK.induction_on (p := fun s ↦ ∀ᶠ i in l, ∀ y ∈ s, y ∉ A i) (by simp)
    (fun s t hst ht ↦ ht.mono fun i hi y hy ↦ hi y (hst hy))
    (fun s t hs ht ↦ (hs.and ht).mono fun i hi y hy ↦ hy.elim (hi.1 y) (hi.2 y)) ?_
  intro x hx
  have : ∃ N ∈ 𝓝 x, ¬ ∃ᶠ i in l, (A i ∩ N).Nonempty := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact h x hx hcon
  obtain ⟨N, hN, hfr⟩ := this
  refine ⟨N, mem_nhdsWithin_of_mem_nhds hN, ?_⟩
  rw [not_frequently] at hfr
  exact hfr.mono fun i hi y hy hyA ↦ hi ⟨y, hyA, hy⟩

end KLimit

/-! ### The quartic perturbation -/

theorem contDiff_quartic (x : E d) : ContDiff ℝ ∞ fun y : E d ↦ (‖y - x‖ ^ 2) ^ 2 :=
  ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).pow 2

theorem quartic_isLittleO (x : E d) :
    (fun y : E d ↦ (‖y - x‖ ^ 2) ^ 2) =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2 := by
  have ht : Tendsto (fun y : E d ↦ ‖y - x‖) (𝓝 x) (𝓝 0) := by
    have : Continuous fun y : E d ↦ ‖y - x‖ := by fun_prop
    simpa using this.tendsto x
  exact ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 4 by norm_num)).comp_tendsto ht).congr_left
    fun y ↦ by simp only [Function.comp_apply]; ring

/-- The perturbation `ψ = φ + s |y - x|⁴` of a smooth test function is smooth and has the same
value, gradient and Laplacian as `φ` at `x`. -/
theorem jet_add_quartic {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E d) (s : ℝ) :
    ContDiff ℝ ∞ (fun y ↦ φ y + s * (‖y - x‖ ^ 2) ^ 2) ∧
      (fun y ↦ φ y + s * (‖y - x‖ ^ 2) ^ 2) x = φ x ∧
      ∇ (fun y ↦ φ y + s * (‖y - x‖ ^ 2) ^ 2) x = ∇ φ x ∧
      Δ (fun y ↦ φ y + s * (‖y - x‖ ^ 2) ^ 2) x = Δ φ x := by
  have hψ : ContDiff ℝ ∞ (fun y ↦ φ y + s * (‖y - x‖ ^ 2) ^ 2) :=
    hφ.add (contDiff_const.mul (contDiff_quartic x))
  have h := laplacian_eq_of_sub_isLittleO (contDiff_two_of_smooth hψ) (contDiff_two_of_smooth hφ)
    (x := x) (((quartic_isLittleO x).const_mul_left s).congr_left fun y ↦ by ring)
  exact ⟨hψ, h.1, h.2.1, h.2.2⟩

/-- **Strict touching perturbation.** If `φ` touches `u` from below in `S` at `x`, then
`ψ = φ - |y - x|⁴` is smooth, has the same gradient and Laplacian as `φ` at `x`, still touches
`u` from below at `x`, and does so strictly: `ψ + |y - x|⁴ ≤ u` near `x` in `S`. -/
theorem touchesBelow_strict_perturb {φ u : E d → ℝ} {S : Set (E d)} {x : E d}
    (hφ : ContDiff ℝ ∞ φ) (h : TouchesBelow φ u S x) :
    ContDiff ℝ ∞ (fun y ↦ φ y - (‖y - x‖ ^ 2) ^ 2) ∧
      ∇ (fun y ↦ φ y - (‖y - x‖ ^ 2) ^ 2) x = ∇ φ x ∧
      Δ (fun y ↦ φ y - (‖y - x‖ ^ 2) ^ 2) x = Δ φ x ∧
      TouchesBelow (fun y ↦ φ y - (‖y - x‖ ^ 2) ^ 2) u S x ∧
      ∀ᶠ y in 𝓝[S] x, φ y - (‖y - x‖ ^ 2) ^ 2 + (‖y - x‖ ^ 2) ^ 2 ≤ u y := by
  have heq : (fun y ↦ φ y - (‖y - x‖ ^ 2) ^ 2) = fun y ↦ φ y + (-1) * (‖y - x‖ ^ 2) ^ 2 := by
    funext y; ring
  obtain ⟨h1, -, h3, h4⟩ := jet_add_quartic hφ x (-1)
  rw [heq]
  refine ⟨h1, h3, h4, ⟨h.1, by simpa using h.2.1, h.2.2.mono fun y hy ↦ ?_⟩, ?_⟩
  · have : 0 ≤ (‖y - x‖ ^ 2) ^ 2 := by positivity
    linarith
  · exact h.2.2.mono fun y hy ↦ by linarith

/-! ### Auxiliary lemmas -/

/-- An eventual property near `(x, 0)` holds on a product of balls. -/
theorem exists_ball_of_eventually_prod {x : E d} {P : E d → ℝ → Prop}
    (h : ∀ᶠ p : E d × ℝ in 𝓝 (x, 0), P p.1 p.2) :
    ∃ δ > 0, ∀ y ∈ ball x δ, ∀ m : ℝ, |m| < δ → P y m := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun y hy m hm ↦ h (y := (y, m)) ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨hy, by simpa [Real.dist_eq] using hm⟩

/-- A continuous function on `F ∩ B̄_ρ(x)` which is larger on `F ∩ ∂B_ρ(x)` than at some point of
`F ∩ B̄_ρ(x)` attains its minimum over `F ∩ B̄_ρ(x)` inside the open ball. -/
theorem exists_isMinOn_inter_ball {F : Set (E d)} (hF : IsClosed F) {x z₀ : E d} {ρ : ℝ}
    {h : E d → ℝ} (hc : ContinuousOn h (closedBall x ρ)) (hz₀ : z₀ ∈ F ∩ closedBall x ρ)
    (hbd : ∀ y ∈ F, dist y x = ρ → h z₀ < h y) :
    ∃ z ∈ F ∩ ball x ρ, IsMinOn h (F ∩ closedBall x ρ) z := by
  obtain ⟨z, hz, hmin⟩ := ((isCompact_closedBall x ρ).inter_left hF).exists_isMinOn ⟨z₀, hz₀⟩
    (hc.mono inter_subset_right)
  refine ⟨z, ⟨hz.1, ?_⟩, hmin⟩
  rcases (mem_closedBall.1 hz.2).lt_or_eq with hlt | heq
  · exact mem_ball.2 hlt
  · exact absurd (hmin hz₀) (not_le.2 (hbd z hz.1 heq))

theorem dist_eq_quartic {x y : E d} {ρ : ℝ} (h : dist y x = ρ) : (‖y - x‖ ^ 2) ^ 2 = ρ ^ 4 := by
  rw [← dist_eq_norm, h]; ring

/-! ### Lemma 2.4 -/

/-- **Lemma 2.4(i)**. Locally uniform limits of viscosity
supersolutions are viscosity supersolutions. -/
theorem isViscSuper_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ} (hQ : ContinuousOn Q U)
    {uk : ι → E d → ℝ} {u : E d → ℝ} (hk : ∀ᶠ k in l, IsViscSuper U Q (uk k))
    (hlim : TendstoLocallyUniformlyOn uk u l U) : IsViscSuper U Q u := by
  have hcont : ContinuousOn u U := hlim.continuousOn (hk.mono fun k h ↦ h.1).frequently
  refine ⟨hcont, fun x hx ↦ ge_of_tendsto (hlim.tendsto_at hx) (hk.mono fun k h ↦ h.2.1 x hx),
    ?_⟩
  intro φ hφ x hx htouch
  by_contra hcon
  simp only [not_or, not_le, not_and_or] at hcon
  obtain ⟨hlap, hbad⟩ := hcon
  obtain ⟨hψ, hψx, hψg, hψl⟩ := jet_add_quartic hφ x (-1)
  set ψ : E d → ℝ := fun y ↦ φ y + (-1) * (‖y - x‖ ^ 2) ^ 2 with hψ_def
  have hψ2 : ContDiff ℝ 2 ψ := contDiff_two_of_smooth hψ
  have hQx : ContinuousAt Q x := hQ.continuousAt (hU.mem_nhds hx)
  -- the "bad" neighbourhood where the test `ψ + m` would violate the supersolution property
  have hev : ∀ᶠ p : E d × ℝ in 𝓝 (x, 0),
      0 < Δ ψ p.1 ∧ (ψ p.1 + p.2 ≠ 0 ∨ Q p.1 < ‖∇ ψ p.1‖) := by
    have hfst : Tendsto Prod.fst (𝓝 (x, (0 : ℝ))) (𝓝 x) := continuous_fst.tendsto _
    refine Eventually.and (hfst.eventually
      (((continuous_laplacian hψ2).tendsto x).eventually_const_lt (by rwa [hψl]))) ?_
    rcases hbad with h0 | hg
    · have hc : ContinuousAt (fun p : E d × ℝ ↦ ψ p.1 + p.2) (x, 0) :=
        ((hψ.continuous.comp continuous_fst).add continuous_snd).continuousAt
      exact (hc.eventually_ne (by simpa [hψx] using h0)).mono fun p hp ↦ Or.inl hp
    · have ht : Tendsto (fun y ↦ ‖∇ ψ y‖ - Q y) (𝓝 x) (𝓝 (‖∇ ψ x‖ - Q x)) :=
        (((continuous_gradient (hψ2.of_le (by norm_num))).norm).tendsto x).sub hQx
      have := ht.eventually_const_lt (u := 0) (by rw [hψg]; linarith)
      exact (hfst.eventually this).mono fun p hp ↦ Or.inr (by linarith)
  obtain ⟨δ₀, hδ₀, hbadball⟩ := exists_ball_of_eventually_prod
    (P := fun y m ↦ 0 < Δ ψ y ∧ (ψ y + m ≠ 0 ∨ Q y < ‖∇ ψ y‖)) hev
  -- localization
  have hu0 : u x - ψ x = 0 := by rw [hψx, ← htouch.2.1]; ring
  have hsmall : ∀ᶠ y in 𝓝 x, |u y - ψ y| < δ₀ / 2 := by
    have hc : ContinuousAt (fun y ↦ u y - ψ y) x :=
      (hcont.continuousAt (hU.mem_nhds hx)).sub hψ.continuous.continuousAt
    have := Metric.tendsto_nhds.1 hc.tendsto (δ₀ / 2) (by positivity)
    simpa [hu0, Real.dist_eq] using this
  have hloc : ∀ᶠ y in 𝓝 x, y ∈ U ∧ φ y ≤ u y ∧ |u y - ψ y| < δ₀ / 2 ∧ y ∈ ball x δ₀ :=
    (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx).and ((htouch.eventually_le_of_isOpen hU).and
      (hsmall.and (ball_mem_nhds x hδ₀)))
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := Metric.eventually_nhds_iff.1 hloc
  set ρ := ρ₁ / 2 with hρ_def
  have hρ : 0 < ρ := half_pos hρ₁
  have hball : ∀ y ∈ closedBall x ρ,
      y ∈ U ∧ φ y ≤ u y ∧ |u y - ψ y| < δ₀ / 2 ∧ y ∈ ball x δ₀ :=
    fun y hy ↦ hρ₁' (lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hρ₁))
  have hBU : closedBall x ρ ⊆ U := fun y hy ↦ (hball y hy).1
  have hlow : ∀ y ∈ closedBall x ρ, (‖y - x‖ ^ 2) ^ 2 ≤ u y - ψ y := by
    intro y hy
    have := (hball y hy).2.1
    simp only [hψ_def]
    linarith
  -- uniform approximation on the closed ball
  set ε := min (ρ ^ 4 / 4) (δ₀ / 4) with hε_def
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ ρ ^ 4 / 4 := min_le_left _ _
  have hε2 : ε ≤ δ₀ / 4 := min_le_right _ _
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hlim _ hBU
    (isCompact_closedBall x ρ)
  obtain ⟨k, hsup, hclose⟩ := (hk.and (Metric.tendstoUniformlyOn_iff.1 hunif ε hε)).exists
  have hcl : ∀ y ∈ closedBall x ρ, |uk k y - u y| < ε := fun y hy ↦ by
    have := hclose y hy
    rwa [Real.dist_eq, abs_sub_comm] at this
  -- minimize `u_k - ψ` over the closed ball
  have hcont_k : ContinuousOn (fun y ↦ uk k y - ψ y) (closedBall x ρ) :=
    (hsup.1.mono hBU).sub hψ.continuous.continuousOn
  have hxB : x ∈ closedBall x ρ := mem_closedBall_self hρ.le
  obtain ⟨z, ⟨-, hzρ⟩, hzmin⟩ := exists_isMinOn_inter_ball isClosed_univ hcont_k
    ⟨mem_univ x, hxB⟩ (by
      intro y _ hy
      have hyB : y ∈ closedBall x ρ := mem_closedBall.2 hy.le
      have h1 := abs_lt.1 (hcl x hxB)
      have h2 := abs_lt.1 (hcl y hyB)
      have h3 := hlow y hyB
      rw [dist_eq_quartic hy] at h3
      try dsimp only
      linarith)
  have hzB : z ∈ closedBall x ρ := ball_subset_closedBall hzρ
  set c := uk k z - ψ z with hc_def
  have htouch' : TouchesBelow (fun y ↦ ψ y + c) (uk k) U z := by
    refine ⟨hBU hzB, by simp [hc_def], ?_⟩
    refine mem_nhdsWithin_of_mem_nhds ((isOpen_ball.mem_nhds hzρ)) |> fun h ↦
      Filter.mem_of_superset h fun y hy ↦ ?_
    have := hzmin ⟨mem_univ y, ball_subset_closedBall hy⟩
    simp only [Set.mem_ofPred_eq] at this
    change ψ y + c ≤ uk k y
    linarith
  have hres := hsup.2.2 _ (hψ.add contDiff_const) z (hBU hzB) htouch'
  rw [laplacian_add_const hψ2.contDiffAt, gradient_add_const] at hres
  -- the constant `c` is small
  have hcsmall : |c| < δ₀ := by
    have h1 := abs_lt.1 (hcl x hxB)
    have h2 := abs_lt.1 (hcl z hzB)
    have h3 := abs_lt.1 (hball z hzB).2.2.1
    have h4 : c ≤ uk k x - ψ x := hzmin ⟨mem_univ x, hxB⟩
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨hL, hB⟩ := hbadball z (hball z hzB).2.2.2 c hcsmall
  rcases hres with hres | ⟨hres1, hres2⟩
  · linarith
  · rcases hB with hB | hB
    · exact hB hres1
    · linarith

/-- **Lemma 2.4(ii)**. If `(u_k, E_k)` are relaxed subsolutions and
`u_k → u` locally uniformly in `U`, then `(u, E*)` is a relaxed subsolution, where
`E* = limsup* E_k` is the upper Kuratowski limit. -/
theorem isRelaxedSub_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ} (hQ : ContinuousOn Q U)
    {uk : ι → E d → ℝ} {u : E d → ℝ} {Es : ι → Set (E d)}
    (hk : ∀ᶠ k in l, IsRelaxedSub U Q (uk k) (Es k))
    (hlim : TendstoLocallyUniformlyOn uk u l U) : IsRelaxedSub U Q u (upperKLimit Es l) := by
  have hcont : ContinuousOn u U := hlim.continuousOn (hk.mono fun k h ↦ h.1).frequently
  have hnn : ∀ x ∈ U, 0 ≤ u x := fun x hx ↦
    ge_of_tendsto (hlim.tendsto_at hx) (hk.mono fun k h ↦ h.2.1 x hx)
  refine ⟨hcont, hnn, isClosed_upperKLimit,
    by simpa using upperKLimit_subset_closure (S := closure U) (hk.mono fun k h ↦ h.2.2.2.1),
    ?_, ?_⟩
  · rintro x ⟨hx, hpos⟩
    apply mem_upperKLimit_of_eventually_mem
    filter_upwards [hk, (hlim.tendsto_at hx).eventually_const_lt hpos] with k hk' hpk
    exact hk'.2.2.2.2.1 ⟨hx, hpk⟩
  intro φ hφ x htouch
  obtain ⟨⟨hxE, hx⟩, hφx, hle⟩ := htouch
  by_contra hcon
  simp only [not_or, not_le, not_and_or] at hcon
  obtain ⟨hlap, hbad⟩ := hcon
  obtain ⟨hψ, hψx, hψg, hψl⟩ := jet_add_quartic hφ x 1
  set ψ : E d → ℝ := fun y ↦ φ y + 1 * (‖y - x‖ ^ 2) ^ 2 with hψ_def
  have hψ2 : ContDiff ℝ 2 ψ := contDiff_two_of_smooth hψ
  have hQx : ContinuousAt Q x := hQ.continuousAt (hU.mem_nhds hx)
  have hev : ∀ᶠ p : E d × ℝ in 𝓝 (x, 0),
      Δ ψ p.1 < 0 ∧ (ψ p.1 + p.2 ≠ 0 ∨ ‖∇ ψ p.1‖ < Q p.1) := by
    have hfst : Tendsto Prod.fst (𝓝 (x, (0 : ℝ))) (𝓝 x) := continuous_fst.tendsto _
    refine Eventually.and (hfst.eventually
      (((continuous_laplacian hψ2).tendsto x).eventually_lt_const (by rwa [hψl]))) ?_
    rcases hbad with h0 | hg
    · have hc : ContinuousAt (fun p : E d × ℝ ↦ ψ p.1 + p.2) (x, 0) :=
        ((hψ.continuous.comp continuous_fst).add continuous_snd).continuousAt
      exact (hc.eventually_ne (by simpa [hψx] using h0)).mono fun p hp ↦ Or.inl hp
    · have ht : Tendsto (fun y ↦ Q y - ‖∇ ψ y‖) (𝓝 x) (𝓝 (Q x - ‖∇ ψ x‖)) :=
        hQx.tendsto.sub (((continuous_gradient (hψ2.of_le (by norm_num))).norm).tendsto x)
      have := ht.eventually_const_lt (u := 0) (by rw [hψg]; linarith)
      exact (hfst.eventually this).mono fun p hp ↦ Or.inr (by linarith)
  obtain ⟨δ₀, hδ₀, hbadball⟩ := exists_ball_of_eventually_prod
    (P := fun y m ↦ Δ ψ y < 0 ∧ (ψ y + m ≠ 0 ∨ ‖∇ ψ y‖ < Q y)) hev
  -- localization
  have hu0 : ψ x - u x = 0 := by rw [hψx, hφx]; ring
  have hcψ : ContinuousAt (fun y ↦ ψ y - u y) x :=
    hψ.continuous.continuousAt.sub (hcont.continuousAt (hU.mem_nhds hx))
  have hsmall : ∀ᶠ y in 𝓝 x, |ψ y - u y| < δ₀ / 2 := by
    have := Metric.tendsto_nhds.1 hcψ.tendsto (δ₀ / 2) (by positivity)
    simpa [hu0, Real.dist_eq] using this
  have hle' : ∀ᶠ y in 𝓝 x, y ∈ upperKLimit Es l ∩ U → u y ≤ φ y :=
    eventually_nhdsWithin_iff.1 hle
  have hloc : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (y ∈ upperKLimit Es l ∩ U → u y ≤ φ y) ∧
      |ψ y - u y| < δ₀ / 2 ∧ y ∈ ball x δ₀ :=
    (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx).and
      (hle'.and (hsmall.and (ball_mem_nhds x hδ₀)))
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := Metric.eventually_nhds_iff.1 hloc
  set ρ := ρ₁ / 2 with hρ_def
  have hρ : 0 < ρ := half_pos hρ₁
  have hball : ∀ y ∈ closedBall x ρ, y ∈ U ∧ (y ∈ upperKLimit Es l ∩ U → u y ≤ φ y) ∧
      |ψ y - u y| < δ₀ / 2 ∧ y ∈ ball x δ₀ :=
    fun y hy ↦ hρ₁' (lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hρ₁))
  have hBU : closedBall x ρ ⊆ U := fun y hy ↦ (hball y hy).1
  have hlow : ∀ y ∈ closedBall x ρ, y ∈ upperKLimit Es l →
      (‖y - x‖ ^ 2) ^ 2 ≤ ψ y - u y := by
    intro y hy hyE
    have := (hball y hy).2.1 ⟨hyE, hBU hy⟩
    simp only [hψ_def]
    linarith
  -- the compact part of the sphere where `ψ - u` is not large avoids `E*`
  have hcψB : ContinuousOn (fun y ↦ ψ y - u y) (closedBall x ρ) :=
    hψ.continuous.continuousOn.sub (hcont.mono hBU)
  set K' := sphere x ρ ∩ (fun y ↦ ψ y - u y) ⁻¹' Iic (ρ ^ 4 / 2) with hK'_def
  have hK'c : IsCompact K' :=
    (isCompact_sphere x ρ).of_isClosed_subset
      ((hcψB.mono sphere_subset_closedBall).preimage_isClosed_of_isClosed
        isClosed_sphere isClosed_Iic) inter_subset_left
  have hK'E : ∀ y ∈ K', y ∉ upperKLimit Es l := by
    rintro y ⟨hys, hyI⟩ hyE
    have h1 := hlow y (sphere_subset_closedBall hys) hyE
    rw [dist_eq_quartic (mem_sphere.1 hys)] at h1
    have h2 : ψ y - u y ≤ ρ ^ 4 / 2 := hyI
    have : 0 < ρ ^ 4 := by positivity
    linarith
  have hdisj := IsCompact.eventually_forall_not_mem_of_disjoint_upperKLimit hK'c hK'E
  -- points of `E_k` close to `x`
  set N := ball x ρ ∩ {y | |ψ y - u y| < ρ ^ 4 / 8} with hN_def
  have hN : N ∈ 𝓝 x := by
    refine inter_mem (ball_mem_nhds x hρ) ?_
    have := Metric.tendsto_nhds.1 hcψ.tendsto (ρ ^ 4 / 8) (by positivity)
    exact (by simpa [hu0, Real.dist_eq] using this :
      ∀ᶠ y in 𝓝 x, |ψ y - u y| < ρ ^ 4 / 8)
  -- uniform approximation
  set ε := min (ρ ^ 4 / 8) (δ₀ / 4) with hε_def
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ ρ ^ 4 / 8 := min_le_left _ _
  have hε2 : ε ≤ δ₀ / 4 := min_le_right _ _
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hlim _ hBU
    (isCompact_closedBall x ρ)
  obtain ⟨k, ⟨z₀, hz₀E, hz₀N⟩, hsub, hclose, hdk⟩ := ((hxE N hN).and_eventually
    (hk.and ((Metric.tendstoUniformlyOn_iff.1 hunif ε hε).and hdisj))).exists
  have hcl : ∀ y ∈ closedBall x ρ, |uk k y - u y| < ε := fun y hy ↦ by
    have := hclose y hy
    rwa [Real.dist_eq, abs_sub_comm] at this
  have hcont_k : ContinuousOn (fun y ↦ ψ y - uk k y) (closedBall x ρ) :=
    hψ.continuous.continuousOn.sub (hsub.1.mono hBU)
  have hz₀B : z₀ ∈ closedBall x ρ := ball_subset_closedBall hz₀N.1
  obtain ⟨z, ⟨hzE, hzρ⟩, hzmin⟩ := exists_isMinOn_inter_ball hsub.2.2.1 hcont_k
    ⟨hz₀E, hz₀B⟩ (by
      intro y hyE hy
      have hys : y ∈ sphere x ρ := mem_sphere.2 hy
      have hyB : y ∈ closedBall x ρ := sphere_subset_closedBall hys
      have hyK : y ∉ K' := fun hyK ↦ hdk y hyK hyE
      have hyI : ρ ^ 4 / 2 < ψ y - u y := by
        by_contra hcon
        exact hyK ⟨hys, not_lt.1 hcon⟩
      have h1 := abs_lt.1 (hcl z₀ hz₀B)
      have h2 := abs_lt.1 (hcl y hyB)
      have h3 := abs_lt.1 (show |ψ z₀ - u z₀| < ρ ^ 4 / 8 from hz₀N.2)
      try dsimp only
      linarith)
  have hzB : z ∈ closedBall x ρ := ball_subset_closedBall hzρ
  set c := ψ z - uk k z with hc_def
  have htouch' : TouchesAbove (fun y ↦ ψ y + -c) (uk k) (Es k ∩ U) z := by
    refine ⟨⟨hzE, hBU hzB⟩, by simp [hc_def], ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_ball.mem_nhds hzρ] with y hy hyEU
    have := hzmin ⟨hyEU.1, ball_subset_closedBall hy⟩
    simp only [Set.mem_ofPred_eq] at this
    linarith
  have hres := hsub.2.2.2.2.2 _ (hψ.add contDiff_const) z htouch'
  rw [laplacian_add_const hψ2.contDiffAt, gradient_add_const] at hres
  have hcsmall : |-c| < δ₀ := by
    have h1 := abs_lt.1 (hcl z₀ hz₀B)
    have h2 := abs_lt.1 (hcl z hzB)
    have h3 := abs_lt.1 (hball z hzB).2.2.1
    have h3' := abs_lt.1 (hball z₀ hz₀B).2.2.1
    have h4 : c ≤ ψ z₀ - uk k z₀ := hzmin ⟨hz₀E, hz₀B⟩
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨hL, hB⟩ := hbadball z (hball z hzB).2.2.2 (-c) hcsmall
  rcases hres with hres | ⟨hres1, hres2⟩
  · linarith
  · rcases hB with hB | hB
    · exact hB hres1
    · linarith

end PerronVariational

end
