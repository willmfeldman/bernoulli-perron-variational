/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.Lower
public import PerronVariational.Examples.TwoDisc.TwoPlane

/-!
# The two-plane points of the necklace example

For the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M. Feldman, K.
Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`), at each kissing point `m_k` (where the discs `B_a(z_k)` and
`B_a(z_{k-1})` touch, `z_k = m_k + a e_k`, `z_{k-1} = m_k - a e_k`):

* `perronSmallest_eq_near_kiss`: near `m_k`, `u_min = (w_k)₊ + (w_{k-1})₊`;
* `kiss_mem_freeBoundary`: `m_k` is a free boundary point of `u_min`;
* `tendstoLocallyUniformly_blowup`: the blow-ups `u_min(m_k + t y)/t` converge to `|⟪y, e_k⟫|`
  locally uniformly as `t → 0⁺` (the one-disc estimate `TwoDisc.blowup_est`, written in the
  coordinates `⟪y, e_k⟫` and `|y - ⟪y, e_k⟫ e_k|`), so every blow-up limit of `u_min` at `m_k` is
  `y ↦ |⟪y, e_k⟫|` (`isBlowupLimit_eq`), and this limit is attained (`isBlowupLimit_twoPlane`).
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational.Necklace

open TwoDisc (cst cst_pos wIn wIn_eq wIn_pos max_wIn_eq_zero max_wIn_eq blowup_est)

/-! ### Neighbouring centres -/

theorem cen_eq_of_dvd {j k : ℤ} (h : (numHoles : ℤ) ∣ j - k) : cen j = cen k := by
  rw [← cen_emod j, ← cen_emod k,
    Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd h)]

/-- Centres at distance `< 0.39` are equal or neighbours. -/
theorem cen_eq_of_norm_lt {j k : ℤ} (h : ‖cen j - cen k‖ ≤ 0.39) :
    cen j = cen k ∨ cen j = cen (k + 1) ∨ cen j = cen (k - 1) := by
  by_contra hne
  push Not at hne
  obtain ⟨h0, h1, h2⟩ := hne
  refine absurd h (not_le.2 (lt_norm_cen_sub_cen (fun hd ↦ h0 (cen_eq_of_dvd hd))
    (fun hd ↦ h1 (cen_eq_of_dvd (by rwa [show j - (k + 1) = j - k - 1 by ring])))
    (fun hd ↦ h2 (cen_eq_of_dvd (by rwa [show j - (k - 1) = j - k + 1 by ring])))))

theorem cen_ne_of_not_dvd {j k : ℤ} (h : ¬ (numHoles : ℤ) ∣ j - k) : cen j ≠ cen k := by
  intro he
  have := two_kissRad_le_norm_cen_sub_cen h
  rw [he, sub_self, norm_zero] at this
  norm_num [kissRad] at this

/-- Near `m_k`, only the discs around `z_k` and `z_{k-1}` are close. -/
theorem cen_eq_of_near_kiss {k c : ℤ} {x : E 2} (hx : ‖x - kiss k‖ ≤ 1 / 100)
    (hc : ‖x - cen c‖ < kissRad) : cen c = cen k ∨ cen c = cen (k - 1) := by
  have hk := norm_kiss_sub_cen k
  have hk1 := norm_kiss_sub_cen_sub_one k
  have t1 : ‖cen c - cen k‖ ≤ 0.39 := by
    have := norm_sub_le_norm_sub_add_norm_sub (cen c) x (cen k)
    have := norm_sub_le_norm_sub_add_norm_sub x (kiss k) (cen k)
    rw [norm_sub_rev (cen c) x] at *
    unfold kissRad at *; linarith
  have t2 : ‖cen c - cen (k - 1)‖ ≤ 0.39 := by
    have := norm_sub_le_norm_sub_add_norm_sub (cen c) x (cen (k - 1))
    have := norm_sub_le_norm_sub_add_norm_sub x (kiss k) (cen (k - 1))
    rw [norm_sub_rev (cen c) x] at *
    unfold kissRad at *; linarith
  rcases cen_eq_of_norm_lt t1 with h | h | h
  · exact Or.inl h
  · rcases cen_eq_of_norm_lt t2 with h' | h' | h'
    · exact Or.inr h'
    · rw [show k - 1 + 1 = k by ring] at h'; exact Or.inl h'
    · exfalso
      refine cen_ne_of_not_dvd (j := k + 1) (k := k - 1 - 1) ?_ (h.symm.trans h')
      rw [show k + 1 - (k - 1 - 1) = (3 : ℤ) by ring]; norm_num [numHoles]
  · exact Or.inr h

/-! ### `u_min` near a kissing point -/

/-- The unit tangent `e_k` at `m_k`. -/
theorem norm_kiss_add_sub_cen (k : ℤ) (y : E 2) :
    ‖kiss k + y - cen k‖ = ‖y - kissRad • tang k‖ := by
  rw [cen_eq_kiss_add]; congr 1; abel

theorem norm_kiss_add_sub_cen_sub_one (k : ℤ) (y : E 2) :
    ‖kiss k + y - cen (k - 1)‖ = ‖y + kissRad • tang k‖ := by
  rw [cen_sub_one_eq_kiss_sub]; congr 1; abel

theorem norm_sub_smul_tang_bounds (k : ℤ) {y : E 2} (hy : ‖y‖ ≤ 1 / 100) (s : ℝ) (hs : |s| = 1) :
    9 / 100 ≤ ‖y + (s * kissRad) • tang k‖ ∧ ‖y + (s * kissRad) • tang k‖ ≤ 11 / 100 := by
  have hn : ‖(s * kissRad) • tang k‖ = 1 / 10 := by
    rw [norm_smul, norm_tang, Real.norm_eq_abs, abs_mul, hs, abs_of_pos (by norm_num [kissRad])]
    norm_num [kissRad]
  constructor
  · have := norm_sub_norm_le ((s * kissRad) • tang k) (-y)
    rw [sub_neg_eq_add, add_comm, norm_neg, hn] at this
    linarith
  · have := norm_add_le y ((s * kissRad) • tang k)
    rw [hn] at this; linarith

theorem norm_kiss_add_sub_cen_bounds (k : ℤ) {y : E 2} (hy : ‖y‖ ≤ 1 / 100) :
    (9 / 100 ≤ ‖kiss k + y - cen k‖ ∧ ‖kiss k + y - cen k‖ ≤ 11 / 100) ∧
      (9 / 100 ≤ ‖kiss k + y - cen (k - 1)‖ ∧ ‖kiss k + y - cen (k - 1)‖ ≤ 11 / 100) := by
  have h1 := norm_sub_smul_tang_bounds k hy (-1) (by norm_num)
  have h2 := norm_sub_smul_tang_bounds k hy 1 (by norm_num)
  rw [norm_kiss_add_sub_cen, norm_kiss_add_sub_cen_sub_one]
  rw [neg_one_mul, neg_smul, ← sub_eq_add_neg] at h1
  rw [one_mul] at h2
  exact ⟨h1, h2⟩

theorem kiss_add_mem_domain (k : ℤ) {y : E 2} (hy : ‖y‖ ≤ 1 / 100) :
    kiss k + y ∈ domain ∧ ‖kiss k + y - 0‖ ^ 2 ≤ layerRad ^ 2 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := norm_kiss_add_sub_cen_bounds k hy
  have hd : 1 / 400 < ‖kiss k + y - cen k‖ ^ 2 := by nlinarith
  have hd' : ‖kiss k + y - cen k‖ ^ 2 ≤ 1 / 100 ∨ 1 / 100 < ‖kiss k + y - cen k‖ ^ 2 :=
    le_or_gt _ _
  have hn : ‖kiss k + y‖ ≤ 3.2 := by
    have := norm_add_le (kiss k) y
    rw [norm_kiss] at this; linarith [innerRad_bounds.2]
  refine ⟨?_, ?_⟩
  · rw [mem_domain_iff]
    refine ⟨by unfold outerRad; linarith, fun j ↦ ?_⟩
    by_contra hj
    push Not at hj
    have hj' : ‖kiss k + y - cen ((j : ℕ) : ℤ)‖ < kissRad := by
      unfold holeRad kissRad at *; linarith
    have hyk : ‖kiss k + y - kiss k‖ ≤ 1 / 100 := by rwa [add_sub_cancel_left]
    rcases cen_eq_of_near_kiss hyk hj' with he | he <;> rw [he] at hj
    · unfold holeRad at hj; linarith
    · obtain ⟨-, h3, -⟩ := norm_kiss_add_sub_cen_bounds k hy
      unfold holeRad at hj; linarith
  · rw [sub_zero]
    have := sq_le_sq_of_le (norm_nonneg _) hn
    linarith [layerRad_sq_bounds.1]

/-- **Near `m_k`, `u_min` is the sum of the two radial solutions** issuing from the neighbouring
holes `z_k`, `z_{k-1}`. -/
theorem perronSmallest_eq_near_kiss (k : ℤ) {y : E 2} (hy : ‖y‖ ≤ 1 / 100) :
    uMin (kiss k + y) = max (wIn (cen k) (kiss k + y)) 0 +
      max (wIn (cen (k - 1)) (kiss k + y)) 0 := by
  obtain ⟨hU, h0⟩ := kiss_add_mem_domain k hy
  rw [perronSmallest_eq_vSup_near hU h0, vSup_eq, max_hLayer_eq_zero h0, add_zero]
  obtain ⟨i, hi⟩ := exists_fin_cen_eq k
  obtain ⟨i', hi'⟩ := exists_fin_cen_eq (k - 1)
  have hii : i ≠ i' := by
    intro he
    rw [he, hi'] at hi
    exact cen_ne_of_not_dvd (j := k - 1) (k := k) (by norm_num [numHoles]) hi
  have hyk : ‖kiss k + y - kiss k‖ ≤ 1 / 100 := by rwa [add_sub_cancel_left]
  rw [wSum, Finset.sum_eq_add i i' hii (fun c _ hc ↦ ?_) (fun h ↦ absurd (Finset.mem_univ _) h)
    (fun h ↦ absurd (Finset.mem_univ _) h), hi, hi']
  refine max_wIn_eq_zero ?_
  by_contra hlt
  push Not at hlt
  have hlt' : ‖kiss k + y - cen ((c : ℕ) : ℤ)‖ < kissRad := by
    rw [← normSq_lt_iff (by norm_num [kissRad])]; unfold kissRad; linarith
  rcases cen_eq_of_near_kiss hyk hlt' with he | he
  · exact hc.1 (by
      by_contra hne
      exact cen_ne_of_not_dvd (not_dvd_of_ne hne) (he.trans hi.symm))
  · exact hc.2 (by
      by_contra hne
      exact cen_ne_of_not_dvd (not_dvd_of_ne hne) (he.trans hi'.symm))

/-! ### The blow-up estimate -/

theorem normSq_sub_smul_tang (k : ℤ) (y : E 2) (t s : ℝ) :
    ‖t • y - (s / 10) • tang k‖ ^ 2 =
      (t * ⟪y, tang k⟫ - s / 10) ^ 2 + t ^ 2 * (‖y‖ ^ 2 - ⟪y, tang k⟫ ^ 2) := by
  rw [norm_sub_sq_real, norm_smul, norm_smul, norm_tang, inner_smul_left, inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  simp only [conj_trivial]
  ring

theorem inner_tang_sq_le (k : ℤ) (y : E 2) : ⟪y, tang k⟫ ^ 2 ≤ ‖y‖ ^ 2 := by
  have := abs_real_inner_le_norm y (tang k)
  rw [norm_tang, mul_one] at this
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

/-- The one-disc estimate in the coordinates of `m_k`. -/
theorem blowup_est_tang (k : ℤ) {y : E 2} {t M s : ℝ} (hs : s = 1 ∨ s = -1) (ht : 0 < t)
    (hM : 0 ≤ M) (hy : ‖y‖ ≤ M) (htM : t * M ≤ 1 / 100) :
    |(Real.log (1 / 100) - Real.log (‖t • y - (s / 10) • tang k‖ ^ 2)) / 20 / t -
      s * ⟪y, tang k⟫| ≤ 50 * t * M ^ 2 := by
  set a := ⟪y, tang k⟫
  set b := Real.sqrt (‖y‖ ^ 2 - a ^ 2)
  have hb : b ^ 2 = ‖y‖ ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith [inner_tang_sq_le k y])
  have hab : a ^ 2 + b ^ 2 ≤ M ^ 2 := by
    rw [hb]; nlinarith [pow_le_pow_left₀ (norm_nonneg y) hy 2]
  have e : ‖t • y - (s / 10) • tang k‖ ^ 2 = (t * a - s / 10) ^ 2 + (t * b) ^ 2 := by
    rw [normSq_sub_smul_tang, mul_pow, hb]
  rw [e]
  exact blowup_est hs ht hM hab htM

/-- **The blow-up estimate at `m_k`.** For `|y| ≤ M` and `0 < t ≤ 1/(100 M)`,
`|u_min(m_k + t y)/t - |⟪y, e_k⟫|| ≤ 100 t M²`. -/
theorem blowup_sub_le (k : ℤ) {y : E 2} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hy : ‖y‖ ≤ M)
    (htM : t * M ≤ 1 / 100) :
    |blowup uMin (kiss k) t y - abs ⟪y, tang k⟫| ≤ 100 * t * M ^ 2 := by
  have hty : ‖t • y‖ ≤ 1 / 100 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith [norm_nonneg y]
  obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := norm_kiss_add_sub_cen_bounds k hty
  have e1 : ‖kiss k + t • y - cen k‖ = ‖t • y - (1 / 10 : ℝ) • tang k‖ := by
    rw [norm_kiss_add_sub_cen]; unfold kissRad; rfl
  have e2 : ‖kiss k + t • y - cen (k - 1)‖ = ‖t • y - (-1 / 10 : ℝ) • tang k‖ := by
    rw [norm_kiss_add_sub_cen_sub_one, show (-1 / 10 : ℝ) = -kissRad by norm_num [kissRad],
      neg_smul, sub_neg_eq_add]
  rw [blowup, perronSmallest_eq_near_kiss k hty, max_wIn_eq (by nlinarith),
    max_wIn_eq (by nlinarith), e1, e2]
  set A := (Real.log (1 / 100) - Real.log (‖t • y - (1 / 10 : ℝ) • tang k‖ ^ 2)) / 20
  set B := (Real.log (1 / 100) - Real.log (‖t • y - (-1 / 10 : ℝ) • tang k‖ ^ 2)) / 20
  set a := ⟪y, tang k⟫
  have hA : |A / t - a| ≤ 50 * t * M ^ 2 := by
    have := blowup_est_tang k (s := 1) (Or.inl rfl) ht hM hy htM
    rw [one_mul] at this; exact this
  have hB : |B / t - -a| ≤ 50 * t * M ^ 2 := by
    have := blowup_est_tang k (s := -1) (Or.inr rfl) ht hM hy htM
    rw [neg_one_mul] at this; exact this
  have habs : |a| = max a 0 + max (-a) 0 := by
    rcases le_total 0 a with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
  have hdiv : (max A 0 + max B 0) / t = max (A / t) 0 + max (B / t) 0 := by
    rw [add_div, ← max_div_div_right ht.le A 0, ← max_div_div_right ht.le B 0, zero_div]
  rw [hdiv, habs]
  have m1 := abs_max_sub_max_le_abs (A / t) a 0
  have m2 := abs_max_sub_max_le_abs (B / t) (-a) 0
  calc |max (A / t) 0 + max (B / t) 0 - (max a 0 + max (-a) 0)| ≤
      |max (A / t) 0 - max a 0| + |max (B / t) 0 - max (-a) 0| := by
        rw [show max (A / t) 0 + max (B / t) 0 - (max a 0 + max (-a) 0) =
          (max (A / t) 0 - max a 0) + (max (B / t) 0 - max (-a) 0) by ring]
        exact abs_add_le _ _
    _ ≤ 100 * t * M ^ 2 := by linarith

/-- **Blow-up at `m_k`.** `u_min(m_k + t y)/t → |⟪y, e_k⟫|` locally uniformly as `t → 0⁺`. -/
theorem tendstoLocallyUniformly_blowup (k : ℤ) :
    TendstoLocallyUniformly (fun t ↦ blowup uMin (kiss k) t) (fun y ↦ |⟪y, tang k⟫|)
      (𝓝[>] 0) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨M₀, hM₀⟩ := hK.isBounded.subset_closedBall 0
  set M := max M₀ 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hpos : 0 < min (1 / (100 * M)) (ε / (200 * M ^ 2)) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with t ht y hyK
  have hy : ‖y‖ ≤ M := by
    have := hM₀ hyK
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have htM : t * M ≤ 1 / 100 := by
    have := lt_of_lt_of_le ht.2 (min_le_left _ _)
    rw [lt_div_iff₀ (by positivity)] at this; nlinarith
  have hte : 100 * t * M ^ 2 < ε := by
    have := lt_of_lt_of_le ht.2 (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this; nlinarith
  rw [dist_comm, Real.dist_eq]
  exact lt_of_le_of_lt (blowup_sub_le k ht.1 hM.le hy htM) hte

/-- Every blow-up limit of `u_min` at `m_k` is the two-plane solution `|⟪y, e_k⟫|`. -/
theorem isBlowupLimit_eq (k : ℤ) {v : E 2 → ℝ} (hv : IsBlowupLimit uMin (kiss k) v) (y : E 2) :
    v y = |⟪y, tang k⟫| := by
  obtain ⟨r, hr, hr0, hconv⟩ := hv
  have hr' : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hr0, Eventually.of_forall hr⟩
  have h1 : Tendsto (fun n ↦ blowup uMin (kiss k) (r n) y) atTop (𝓝 (v y)) :=
    (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ y)
  have h2 : Tendsto (fun n ↦ blowup uMin (kiss k) (r n) y) atTop (𝓝 (|⟪y, tang k⟫|)) :=
    ((tendstoLocallyUniformlyOn_univ.2 (tendstoLocallyUniformly_blowup k)).tendsto_at
      (mem_univ y)).comp hr'
  exact tendsto_nhds_unique h1 h2

/-- The two-plane solution `|⟪y, e_k⟫|` is a blow-up limit of `u_min` at `m_k` (along
`t_n = 1/(n+1)`). -/
theorem isBlowupLimit_twoPlane (k : ℤ) :
    IsBlowupLimit uMin (kiss k) (fun y ↦ |⟪y, tang k⟫|) := by
  have hr : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n ↦ by simp only [mem_Ioi]; positivity⟩
  exact ⟨fun n ↦ 1 / ((n : ℝ) + 1), fun n ↦ by positivity, tendsto_one_div_add_atTop_nhds_zero_nat,
    fun u hu x ↦ by
      obtain ⟨t, ht, hev⟩ := tendstoLocallyUniformly_blowup k u hu x
      exact ⟨t, ht, hr.eventually hev⟩⟩

/-! ### `m_k` is a free boundary point -/

theorem kiss_mem_domain (k : ℤ) : kiss k ∈ domain := by
  simpa using (kiss_add_mem_domain k (y := 0) (by simp)).1

theorem perronSmallest_kiss (k : ℤ) : uMin (kiss k) = 0 := by
  have h := perronSmallest_eq_near_kiss k (y := 0) (by simp)
  rw [add_zero] at h
  rw [h, max_wIn_eq_zero, max_wIn_eq_zero, add_zero]
  · rw [norm_kiss_sub_cen_sub_one]; norm_num [kissRad]
  · rw [norm_kiss_sub_cen]; norm_num [kissRad]

theorem norm_kiss_add_smul_tang_sub_cen (k : ℤ) (s : ℝ) :
    ‖kiss k + s • tang k - cen k‖ = |s - kissRad| := by
  rw [norm_kiss_add_sub_cen, ← sub_smul, norm_smul, norm_tang, mul_one, Real.norm_eq_abs]

theorem norm_kiss_sub_smul_tang_sub_cen (k : ℤ) (s : ℝ) :
    ‖kiss k + (-s) • tang k - cen (k - 1)‖ = |s - kissRad| := by
  rw [norm_kiss_add_sub_cen_sub_one, ← add_smul, norm_smul, norm_tang, mul_one,
    Real.norm_eq_abs, show -s + kissRad = -(s - kissRad) by ring, abs_neg]

/-- On the segment from `m_k` into `B_a(z_k)`, `|x - z_k|² ∈ [r², a²)`. -/
theorem normSq_kiss_add_smul_tang (k : ℤ) {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 20) :
    1 / 400 ≤ ‖kiss k + s • tang k - cen k‖ ^ 2 ∧ ‖kiss k + s • tang k - cen k‖ ^ 2 < 1 / 100 := by
  rw [norm_kiss_add_smul_tang_sub_cen, sq_abs]
  unfold kissRad; constructor <;> nlinarith

theorem normSq_kiss_sub_smul_tang (k : ℤ) {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 20) :
    1 / 400 ≤ ‖kiss k + (-s) • tang k - cen (k - 1)‖ ^ 2 ∧
      ‖kiss k + (-s) • tang k - cen (k - 1)‖ ^ 2 < 1 / 100 := by
  rw [norm_kiss_sub_smul_tang_sub_cen, sq_abs]
  unfold kissRad; constructor <;> nlinarith

theorem perronSmallest_kiss_add_pos (k : ℤ) {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 20) :
    0 < uMin (kiss k + s • tang k) :=
  perronSmallest_pos k (normSq_kiss_add_smul_tang k hs hs').1
    (normSq_kiss_add_smul_tang k hs hs').2

theorem kiss_add_smul_mem_domain (k : ℤ) {s : ℝ} (hs : |s| ≤ 1 / 100) :
    kiss k + s • tang k ∈ domain :=
  (kiss_add_mem_domain k (by rw [norm_smul, norm_tang, mul_one, Real.norm_eq_abs]; exact hs)).1

/-- **`m_k` is a free boundary point of `u_min`.** -/
theorem kiss_mem_freeBoundary (k : ℤ) : kiss k ∈ freeBoundary uMin domain := by
  refine ⟨⟨?_, ?_⟩, kiss_mem_domain k⟩
  · have ht : Tendsto (fun s : ℝ ↦ kiss k + s • tang k) (𝓝[>] 0) (𝓝 (kiss k)) := by
      have : Continuous fun s : ℝ ↦ kiss k + s • tang k := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 100 by norm_num)] with s hs
    exact ⟨kiss_add_smul_mem_domain k (by rw [abs_of_pos hs.1]; exact hs.2.le),
      perronSmallest_kiss_add_pos k hs.1 (by linarith [hs.2])⟩
  · intro h
    have := interior_subset h
    simp [posSet, perronSmallest_kiss] at this

/-! ### Nontriviality of `u_min` -/

theorem perronSmallest_zero : uMin 0 = 0 := by
  have h0 : ‖(0 : E 2) - 0‖ ^ 2 ≤ layerRad ^ 2 := by
    rw [sub_zero, norm_zero, sq, zero_mul]; positivity
  rw [perronSmallest_eq_vSup_near zero_mem_domain h0, vSup_eq, max_hLayer_eq_zero h0, add_zero,
    wSum_eq_zero]
  intro j
  rw [zero_sub, norm_neg, norm_cen]
  nlinarith [ringRad_bounds.1]

theorem exists_perronSmallest_pos : ∃ x ∈ domain, 0 < uMin x :=
  ⟨_, kiss_add_smul_mem_domain 0 (s := 1 / 100) (by norm_num),
    perronSmallest_kiss_add_pos 0 (by norm_num) (by norm_num)⟩

end PerronVariational.Necklace

end
