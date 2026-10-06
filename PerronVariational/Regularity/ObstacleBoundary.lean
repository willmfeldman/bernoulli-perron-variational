/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.DeGiorgi.Caccioppoli
public import GMTFoundations.Sobolev.SobolevInequality
public import PerronVariational.Basic.Sobolev
import GMTFoundations.DeGiorgi.Oscillation
import GMTFoundations.Sobolev.SobolevOne
import PerronVariational.Regularity.ObstacleCaccioppoli

/-!
# Continuity of one-sided obstacle minimizers across `∂B`

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper").

The results are `obstacle_below_continuousOn` (Lemma 6.3 of the paper, Step 1, obstacle from above
`0 ≤ w ≤ u`) and `obstacle_above_continuousOn` (Step 2, obstacle from below `w ≥ u`), with the
statements used in `PerronVariational/Main/Directional.lean`.

**A step the paper does not argue.** In the proof of Lemma 6.3 the paper needs the obstacle
minimizer `w` on the ball `B`, extended by `u` outside `B`, to be continuous on `U`, since the
competitors of Def 2.6 must be continuous. It cites W. M. Feldman, I. C. Kim, N. Požár, *An obstacle
approach to rate-independent droplet evolution*, Forum Math. Sigma 14 (2026), e38,
doi:10.1017/fms.2026.10189, Section 3, for continuity in `B`, but that section treats domain
obstacles and does not give continuity across `∂B`. Here continuity up to `∂B` is proved by the De
Giorgi route for quasi-minima of M. Giaquinta, E. Giusti, *Quasi-minima*, Ann. Inst. H. Poincaré
Anal. Non Linéaire 1 (1984), no. 2, 79–107: Caccioppoli inequalities from truncation competitors
(`Regularity/ObstacleCaccioppoli.lean`), then De Giorgi's oscillation decay at the boundary.

Proof. At `z ∈ ∂B` put `f = w` (Step 2) or `f = -w` (Step 1), `c = ±u(z)`, and let `L` be a
Lipschitz constant of `u` near `z`. For every small `ρ`, `f ∈ DG⁺` on `B_ρ(z)` at levels
`≥ c + Lρ` (`isDeGiorgiAt_above`, `isDeGiorgiAt_below`) and `f = ±u ≤ c + Lρ` on `B_ρ(z) \ B`.
Iterating `oscillation_decay` on the radii `ρ_i = R₀ 16^{-i}` (`ae_le_of_boundary`) gives
`f ≤ c + ε` a.e. near `z`; since `w` is continuous in `B` and equals `u` outside, this becomes a
pointwise one-sided bound, and the other side is the obstacle constraint.
-/

open GMTFoundations
open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public section

namespace PerronVariational.Regularity

variable {d : ℕ}

/-- A linear recursion `e_{i+1} ≤ λ e_i + B qⁱ` with `λ < 1`, `q ≤ (1+λ)/2` decays like
`((1+λ)/2)ⁱ`. -/
theorem le_of_recursion {e : ℕ → ℝ} {lam q Bc : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hq0 : 0 ≤ q) (hq : q ≤ (1 + lam) / 2) (hB : 0 ≤ Bc)
    (h : ∀ i, e (i + 1) ≤ lam * e i + Bc * q ^ i) :
    ∀ i, e i ≤ ((1 + lam) / 2) ^ i * (|e 0| + 2 * Bc / (1 - lam)) := by
  set μ := (1 + lam) / 2 with hμ
  set E := |e 0| + 2 * Bc / (1 - lam) with hE
  have h1l : 0 < 1 - lam := by linarith
  have hBE : Bc ≤ (1 - lam) / 2 * E := by
    have : 2 * Bc / (1 - lam) ≤ E := by rw [hE]; linarith [abs_nonneg (e 0)]
    rw [div_le_iff₀ h1l] at this
    linarith
  have hμ0 : 0 ≤ μ := by rw [hμ]; linarith
  intro i
  induction i with
  | zero =>
    simp only [pow_zero, one_mul, hE]
    have : 0 ≤ 2 * Bc / (1 - lam) := by positivity
    linarith [le_abs_self (e 0)]
  | succ i ih =>
    have hqi : q ^ i ≤ μ ^ i := pow_le_pow_left₀ hq0 hq i
    have hμi : 0 ≤ μ ^ i := pow_nonneg hμ0 i
    calc e (i + 1) ≤ lam * e i + Bc * q ^ i := h i
      _ ≤ lam * (μ ^ i * E) + Bc * μ ^ i := by gcongr
      _ ≤ lam * (μ ^ i * E) + (1 - lam) / 2 * E * μ ^ i := by gcongr
      _ = μ ^ (i + 1) * E := by rw [pow_succ, hμ]; ring

/-- An a.e. upper bound near an interior point of `S` turns into a pointwise bound at points of
continuity. -/
theorem le_of_ae_le_of_continuousAt {f : E d → ℝ} {z y : E d} {δ c : ℝ}
    (hae : ∀ᵐ x ∂(volume.restrict (ball z δ)), f x ≤ c) (hy : y ∈ ball z δ)
    (hfy : ContinuousAt f y) : f y ≤ c := by
  by_contra hlt
  have h1 : ∀ᶠ x in 𝓝 y, c < f x := continuousAt_const.eventually_lt hfy (not_le.1 hlt)
  have h2 : ∀ᶠ x in 𝓝 y, x ∈ ball z δ := isOpen_ball.mem_nhds hy
  have hT : {x | x ∈ ball z δ ∧ c < f x} ∈ 𝓝 y := h2.and h1
  have hpos : 0 < volume {x | x ∈ ball z δ ∧ c < f x} := Measure.measure_pos_of_mem_nhds volume hT
  have hnull : volume {x | x ∈ ball z δ ∧ c < f x} = 0 := by
    rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hae
    refine measure_mono_null (fun x hx ↦ ?_) hae
    simp only [Set.mem_ofPred_eq, not_forall, not_le]
    exact ⟨hx.1, hx.2⟩
  exact hpos.ne' hnull

/-- **Boundary `L^∞` bound from the oscillation decay.** Let `z ∈ ∂B_r(x₀)`,
`B̄_{R₀}(z) ⊆ U`, and for every `0 < ρ ≤ R₀`: `f ∈ DG⁺` on `B_ρ(z)` at levels `≥ c + Lρ`, and
`f ≤ c + Lρ` on `B_ρ(z) \ B_r(x₀)`. If `f ≤ M₀` a.e. on `B_{R₀}(z)`, then for every `ε > 0`,
`f ≤ c + ε` a.e. on some ball `B_δ(z)`. -/
theorem ae_le_of_boundary (hd : 1 ≤ d) {CS : ℝ≥0} (hS : SobolevSupport d CS) {U : Set (E d)}
    (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d} (hf : MemH1Loc U f G) {x₀ z : E d}
    {r R₀ : ℝ} (hr : 0 < r) (hz : dist z x₀ = r) (hR₀ : 0 < R₀) (hzU : closedBall z R₀ ⊆ U)
    {c L C₀ C₁ M₀ : ℝ} (hL : 0 ≤ L) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hDG : ∀ ρ, 0 < ρ → ρ ≤ R₀ → IsDeGiorgiAt f G z ρ (c + L * ρ) C₀ C₁)
    (hout : ∀ ρ, 0 < ρ → ρ ≤ R₀ → ∀ x ∈ ball z ρ, x ∉ ball x₀ r → f x ≤ c + L * ρ)
    (hM₀ : ∀ᵐ x ∂(volume.restrict (ball z R₀)), f x ≤ M₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ᵐ x ∂(volume.restrict (ball z δ)), f x ≤ c + ε := by
  intro ε hε
  set n := oscN d CS C₀ with hn
  set lam : ℝ := 1 - 1 / 2 ^ (n + 1) with hlam
  set Λ : ℝ := 2 ^ n * √C₁ with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hp : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hlam1 : lam < 1 := by rw [hlam]; have : 0 < 1 / (2 : ℝ) ^ (n + 1) := by positivity
                             linarith
  have hlam0 : 0 ≤ lam := by
    rw [hlam, sub_nonneg, div_le_one hp]; exact one_le_pow₀ (by norm_num)
  set ρs : ℕ → ℝ := fun i ↦ R₀ / 16 ^ i with hρs
  have hρs0 : ∀ i, 0 < ρs i := fun i ↦ by simp only [hρs]; positivity
  have hρsle : ∀ i, ρs i ≤ R₀ := fun i ↦ div_le_self hR₀.le (one_le_pow₀ (by norm_num))
  have hρsucc : ∀ i, ρs (i + 1) = ρs i / 16 := fun i ↦ by simp only [hρs]; rw [pow_succ]; ring
  set Kk : ℕ → ℝ := fun i ↦ c + L * ρs i with hKk
  let Ms : ℕ → ℝ := fun i ↦ Nat.rec (motive := fun _ ↦ ℝ) M₀
    (fun j Mj ↦ Kk j + lam * (Mj - Kk j) + Λ * ρs j) i
  have hMs0 : Ms 0 = M₀ := rfl
  have hMsucc : ∀ i, Ms (i + 1) = Kk i + lam * (Ms i - Kk i) + Λ * ρs i := fun i ↦ rfl
  have hind : ∀ i, ∀ᵐ x ∂(volume.restrict (ball z (ρs i))), f x ≤ Ms i := by
    intro i
    induction i with
    | zero => simpa [hρs, hMs0] using hM₀
    | succ i ih =>
      have hzi : closedBall z (ρs i) ⊆ U := (closedBall_subset_closedBall (hρsle i)).trans hzU
      have h := oscillation_decay hd hS hU hf hr hz (hρs0 i) hzi (hDG _ (hρs0 i) (hρsle i))
        hC₀ hC₁ (hout _ (hρs0 i) (hρsle i)) ih
      rw [hρsucc, hMsucc]
      filter_upwards [h] with x hx
      have e : Kk i + lam * (Ms i - Kk i) + Λ * ρs i =
          c + L * ρs i + (1 - 1 / 2 ^ (n + 1)) * (Ms i - (c + L * ρs i)) +
            2 ^ n * √C₁ * ρs i := by rw [hlam, hΛ, hKk]
      rw [e]; exact hx
  -- the decay of `e_i = M_i - c`
  set e : ℕ → ℝ := fun i ↦ Ms i - c with he
  have hrec : ∀ i, e (i + 1) ≤ lam * e i + ((L + Λ) * R₀) * (1 / 16) ^ i := by
    intro i
    have hρi : ρs i = R₀ * (1 / 16) ^ i := by simp only [hρs]; rw [one_div_pow]; ring
    simp only [he, hMsucc, hKk]
    rw [hρi]
    have hq : 0 ≤ R₀ * (1 / 16 : ℝ) ^ i := by positivity
    have : 0 ≤ (1 - lam) * (L * (R₀ * (1 / 16) ^ i)) := by
      have := mul_nonneg hL hq; nlinarith
    nlinarith [mul_nonneg hlam0 hq]
  have hq : (1 / 16 : ℝ) ≤ (1 + lam) / 2 := by linarith
  have hbound := le_of_recursion hlam0 hlam1 (by norm_num) hq
    (by positivity : 0 ≤ (L + Λ) * R₀) hrec
  set E := |e 0| + 2 * ((L + Λ) * R₀) / (1 - lam) with hE
  have hE0 : 0 ≤ E := by
    have : 0 < 1 - lam := by linarith
    positivity
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (E + 1) by positivity)
    (show (1 + lam) / 2 < 1 by linarith)
  refine ⟨ρs i, hρs0 i, ?_⟩
  filter_upwards [hind i] with x hx
  have h1 := hbound i
  have h2 : ((1 + lam) / 2) ^ i * E ≤ ((1 + lam) / 2) ^ i * (E + 1) := by
    have : 0 ≤ ((1 + lam) / 2) ^ i := pow_nonneg (by linarith) _
    nlinarith
  have h3 : ((1 + lam) / 2) ^ i * (E + 1) < ε := by
    rwa [lt_div_iff₀ (by positivity)] at hi
  simp only [he] at h1
  linarith

/-- An a.e. bound from the De Giorgi `L^∞` lemma with a large level increment. -/
theorem exists_ae_le_of_isDeGiorgiAt (hd : 1 ≤ d) {CS : ℝ≥0} (hS : SobolevSupport d CS)
    {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d} (hf : MemH1Loc U f G)
    {z : E d} {R K C₀ C₁ : ℝ} (hR : 0 < R) (hzU : closedBall z R ⊆ U)
    (hDG : IsDeGiorgiAt f G z R K C₀ C₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) :
    ∃ M, ∀ᵐ x ∂(volume.restrict (ball z (R / 2))), f x ≤ M := by
  set ε := degiorgiEps d CS C₀ with hε
  have hε0 : 0 < ε := degiorgiEps_pos hC₀
  set I := ∫ x in ball z R, (max (f x - K) 0) ^ 2 with hI
  have hRd : 0 < R ^ d := by positivity
  set H2 : ℝ := C₁ * R ^ 2 + |I| / (ε * R ^ d) + 1 with hH2
  have hH20 : 0 < H2 := by
    have : 0 ≤ C₁ * R ^ 2 := by positivity
    have : 0 ≤ |I| / (ε * R ^ d) := by positivity
    linarith
  set H := √H2 with hH
  have hHsq : H ^ 2 = H2 := Real.sq_sqrt hH20.le
  have hH0 : 0 < H := Real.sqrt_pos.2 hH20
  have h1 : C₁ * R ^ 2 ≤ H ^ 2 := by
    rw [hHsq]; have : 0 ≤ |I| / (ε * R ^ d) := by positivity
    linarith
  have h2 : I ≤ ε * H ^ 2 * R ^ d := by
    have h3 : |I| / (ε * R ^ d) ≤ H ^ 2 := by
      rw [hHsq]; have : 0 ≤ C₁ * R ^ 2 := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)] at h3
    linarith [le_abs_self I]
  exact ⟨K + H, degiorgi_linfty hd hU hf hR hDG hC₀ hC₁ hzU hS le_rfl hH0 h1 h2⟩

/-! ### The targets -/

/-- Pointwise upper bound near `y` from an a.e. bound near `y`, for `w` continuous in `B`. -/
theorem eventually_lt_of_ae_le {w : E d → ℝ} {x₀ y : E d} {r δ c b : ℝ} (hδ : 0 < δ)
    (hae : ∀ᵐ x ∂(volume.restrict (ball y δ)), w x ≤ c) (hcb : c < b)
    (hwc : ContinuousOn w (ball x₀ r)) (hout : ∀ᶠ x in 𝓝 y, x ∉ ball x₀ r → w x < b) :
    ∀ᶠ x in 𝓝 y, w x < b := by
  filter_upwards [ball_mem_nhds y hδ, hout] with x hx1 hx2
  by_cases hxB : x ∈ ball x₀ r
  · exact (le_of_ae_le_of_continuousAt hae hx1
      (hwc.continuousAt (isOpen_ball.mem_nhds hxB))).trans_lt hcb
  · exact hx2 hxB

theorem one_le_of_dist_eq {x₀ y : E d} {r : ℝ} (hr : 0 < r) (h : dist y x₀ = r) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : y = x₀ := by ext i; exact Fin.elim0 i
    rw [this, dist_self] at h
    exact absurd h hr.ne
  · exact hd

theorem sq_le_of_bounds {U : Set (E d)} {Q : E d → ℝ} (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) : ∃ Cq, 0 ≤ Cq ∧ ∀ x ∈ U, Q x ^ 2 ≤ Cq := by
  obtain ⟨c, hc, hcQ⟩ := hQpos
  obtain ⟨C, hC⟩ := hQb
  refine ⟨(max C 0) ^ 2, by positivity, fun x hx ↦ ?_⟩
  have h0 : 0 ≤ Q x := hc.le.trans (hcQ x hx)
  exact pow_le_pow_left₀ h0 ((hC x hx).trans (le_max_left _ _)) 2

/-- The local Lipschitz bound of `u` near a point `y ∈ U`, on a ball `B̄_{R₀}(y) ⊆ U`. -/
theorem exists_lipschitz_ball {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hu : LocallyLipschitzOn U u) {y : E d} (hy : y ∈ U) :
    ∃ R₀ > 0, ∃ L : ℝ, 0 ≤ L ∧ closedBall y R₀ ⊆ U ∧
      ∀ ρ, ∀ x ∈ ball y ρ, x ∈ ball y R₀ → |u x - u y| ≤ L * ρ := by
  obtain ⟨L, t, ht, hLip⟩ := hu hy
  rw [hU.nhdsWithin_eq hy] at ht
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht (hU.mem_nhds hy))
  refine ⟨δ / 2, by positivity, L, L.2, ?_, fun ρ x hx hxR ↦ ?_⟩
  · exact (closedBall_subset_ball (by linarith)).trans (hball.trans inter_subset_right)
  · have hxt : x ∈ t := (hball (ball_subset_ball (by linarith) hxR)).1
    have hyt : y ∈ t := (hball (mem_ball_self hδ)).1
    have := hLip.dist_le_mul x hxt y hyt
    rw [Real.dist_eq] at this
    refine this.trans ?_
    gcongr
    exact (mem_ball.1 hx).le

/-- **Continuity across `∂B` of the obstacle-from-above minimizer** (paper Lemma 6.3, Step 1;
a step the paper does not argue, see the module docstring). -/
theorem obstacle_below_continuousOn {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (_hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (_hu0 : ∀ x ∈ U, 0 ≤ u x)
    {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U)
    (hGw : MemH1Loc U w Gw) (hwc : ContinuousOn w (ball x₀ r))
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv) :
    ContinuousOn w U := by
  obtain ⟨Cq, hCq, hQq⟩ := sq_le_of_bounds hQpos hQb
  have hucont : ContinuousOn u U := hu.continuousOn
  intro y hy
  refine ContinuousAt.continuousWithinAt ?_
  rcases lt_trichotomy (dist y x₀) r with h | h | h
  · exact hwc.continuousAt (isOpen_ball.mem_nhds h)
  swap
  · refine (hucont.continuousAt (hU.mem_nhds hy)).congr ?_
    filter_upwards [hU.mem_nhds hy, isClosed_closedBall.isOpen_compl.mem_nhds
      (show y ∉ closedBall x₀ r from fun h' ↦ by rw [mem_closedBall] at h'; linarith)]
      with x hx1 hx2
    exact (hwout x ⟨hx1, fun hb ↦ hx2 (ball_subset_closedBall hb)⟩).symm
  -- the boundary case
  have hd := one_le_of_dist_eq hr h
  obtain ⟨CS, hS⟩ := exists_sobolevSupport hd
  have hyB : y ∉ ball x₀ r := fun h' ↦ by rw [mem_ball] at h'; linarith
  have hwy : w y = u y := hwout y ⟨hy, hyB⟩
  obtain ⟨R₀, hR₀, L, hL, hyU, hLip⟩ := exists_lipschitz_ball hU hu hy
  have hballU : ∀ ρ, ρ ≤ R₀ → ball y ρ ⊆ U := fun ρ hρ ↦
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hρ).trans hyU)
  have hDG : ∀ ρ, 0 < ρ → ρ ≤ R₀ →
      IsDeGiorgiAt (fun x ↦ -w x) (fun x ↦ -Gw x) y ρ (-u y + L * ρ) caccConst (128 * Cq) :=
    fun ρ hρ hρR ↦ isDeGiorgiAt_below hU hCq hQq hB hGw hwout hwu hmin
      ((closedBall_subset_closedBall hρR).trans hyU) fun x hx ↦ by
        have := hLip ρ x hx (ball_subset_ball hρR hx)
        rw [abs_le] at this
        linarith [this.1]
  have hout : ∀ ρ, 0 < ρ → ρ ≤ R₀ → ∀ x ∈ ball y ρ, x ∉ ball x₀ r →
      -w x ≤ -u y + L * ρ := by
    intro ρ hρ hρR x hx hxB
    rw [hwout x ⟨hballU ρ hρR hx, hxB⟩]
    have := hLip ρ x hx (ball_subset_ball hρR hx)
    rw [abs_le] at this
    linarith [this.1]
  have hM₀ : ∀ᵐ x ∂(volume.restrict (ball y R₀)), -w x ≤ 0 :=
    (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx ↦ by
      linarith [(hwu x (hballU R₀ le_rfl hx)).1])
  have hmain := ae_le_of_boundary hd hS hU hGw.neg hr h hR₀ hyU hL caccConst_pos.le
    (by positivity) hDG hout hM₀
  rw [ContinuousAt, tendsto_order]
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- lower bound: from the oscillation decay of `-w`
    rw [hwy] at ha
    obtain ⟨δ, hδ, hae⟩ := hmain ((u y - a) / 2) (by linarith)
    have := eventually_lt_of_ae_le (w := fun x ↦ -w x) (b := -a) hδ hae (by linarith)
      hwc.neg (by
        filter_upwards [(hucont.continuousAt (hU.mem_nhds hy)).eventually
          (lt_mem_nhds ha), hU.mem_nhds hy] with x hx1 hx2 hxB
        rw [hwout x ⟨hx2, hxB⟩]; linarith)
    filter_upwards [this] with x hx
    linarith
  · -- upper bound: `w ≤ u`
    rw [hwy] at hb
    filter_upwards [(hucont.continuousAt (hU.mem_nhds hy)).eventually (gt_mem_nhds hb),
      hU.mem_nhds hy] with x hx1 hx2
    exact (hwu x hx2).2.trans_lt hx1

/-- **Continuity across `∂B` of the obstacle-from-below minimizer** (paper Lemma 6.3, Step 2;
a step the paper does not argue, see the module docstring). -/
theorem obstacle_above_continuousOn {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (_hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (_hu0 : ∀ x ∈ U, 0 ≤ u x)
    {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U)
    (hGw : MemH1Loc U w Gw) (hwc : ContinuousOn w (ball x₀ r))
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, u y ≤ w y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv) :
    ContinuousOn w U := by
  obtain ⟨Cq, hCq, hQq⟩ := sq_le_of_bounds hQpos hQb
  have hucont : ContinuousOn u U := hu.continuousOn
  intro y hy
  refine ContinuousAt.continuousWithinAt ?_
  rcases lt_trichotomy (dist y x₀) r with h | h | h
  · exact hwc.continuousAt (isOpen_ball.mem_nhds h)
  swap
  · refine (hucont.continuousAt (hU.mem_nhds hy)).congr ?_
    filter_upwards [hU.mem_nhds hy, isClosed_closedBall.isOpen_compl.mem_nhds
      (show y ∉ closedBall x₀ r from fun h' ↦ by rw [mem_closedBall] at h'; linarith)]
      with x hx1 hx2
    exact (hwout x ⟨hx1, fun hb ↦ hx2 (ball_subset_closedBall hb)⟩).symm
  -- the boundary case
  have hd := one_le_of_dist_eq hr h
  obtain ⟨CS, hS⟩ := exists_sobolevSupport hd
  have hyB : y ∉ ball x₀ r := fun h' ↦ by rw [mem_ball] at h'; linarith
  have hwy : w y = u y := hwout y ⟨hy, hyB⟩
  obtain ⟨R₀, hR₀, L, hL, hyU, hLip⟩ := exists_lipschitz_ball hU hu hy
  have hballU : ∀ ρ, ρ ≤ R₀ → ball y ρ ⊆ U := fun ρ hρ ↦
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hρ).trans hyU)
  have hDG : ∀ ρ, 0 < ρ → ρ ≤ R₀ → IsDeGiorgiAt w Gw y ρ (u y + L * ρ) caccConst 0 :=
    fun ρ hρ hρR ↦ isDeGiorgiAt_above hU hCq hQq hB hGw hwout hwu hmin
      ((closedBall_subset_closedBall hρR).trans hyU) fun x hx ↦ by
        have := hLip ρ x hx (ball_subset_ball hρR hx)
        rw [abs_le] at this
        linarith [this.2]
  have hout : ∀ ρ, 0 < ρ → ρ ≤ R₀ → ∀ x ∈ ball y ρ, x ∉ ball x₀ r → w x ≤ u y + L * ρ := by
    intro ρ hρ hρR x hx hxB
    rw [hwout x ⟨hballU ρ hρR hx, hxB⟩]
    have := hLip ρ x hx (ball_subset_ball hρR hx)
    rw [abs_le] at this
    linarith [this.2]
  obtain ⟨M₀, hM₀⟩ := exists_ae_le_of_isDeGiorgiAt hd hS hU hGw hR₀ hyU (hDG R₀ hR₀ le_rfl)
    caccConst_pos.le le_rfl
  have hmain := ae_le_of_boundary hd hS hU hGw hr h (by positivity : 0 < R₀ / 2)
    ((closedBall_subset_closedBall (by linarith)).trans hyU) hL caccConst_pos.le le_rfl
    (fun ρ hρ hρR ↦ hDG ρ hρ (by linarith)) (fun ρ hρ hρR ↦ hout ρ hρ (by linarith)) hM₀
  rw [ContinuousAt, tendsto_order]
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- lower bound: `u ≤ w`
    rw [hwy] at ha
    filter_upwards [(hucont.continuousAt (hU.mem_nhds hy)).eventually (lt_mem_nhds ha),
      hU.mem_nhds hy] with x hx1 hx2
    exact hx1.trans_le (hwu x hx2)
  · -- upper bound: from the oscillation decay
    rw [hwy] at hb
    obtain ⟨δ, hδ, hae⟩ := hmain ((b - u y) / 2) (by linarith)
    exact eventually_lt_of_ae_le hδ hae (by linarith) hwc (by
      filter_upwards [(hucont.continuousAt (hU.mem_nhds hy)).eventually (gt_mem_nhds hb),
        hU.mem_nhds hy] with x hx1 hx2 hxB
      rw [hwout x ⟨hx2, hxB⟩]; exact hx1)

end PerronVariational.Regularity

end
