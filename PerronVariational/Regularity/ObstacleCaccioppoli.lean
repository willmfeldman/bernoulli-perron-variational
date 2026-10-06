/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.DeGiorgi.Caccioppoli
public import PerronVariational.Basic.Sobolev
import PerronVariational.Regularity.Caccioppoli

/-!
# Caccioppoli inequalities for one-sided obstacle minimizers

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper");
used for the continuity of the obstacle minimizers in the proof of Lemma 6.3
(`Regularity/ObstacleBoundary.lean`). The De Giorgi class `IsDeGiorgiAt`, the cutoff constant and
the hole-filling lemma come from the dependency gmt-foundations v0.1.0
(`GMTFoundations.DeGiorgi.Caccioppoli`).

Let `B = B_r(x₀)`, `B̄ ⊆ U`, and let `w ∈ H¹_loc(U)` with `w = u` on `U \ B` minimize
`J_Q(·; B)` among competitors with the same values off `B` and a one-sided constraint.

* `step_above` (obstacle from below, `w ≥ u`; paper Lemma 6.3, Step 2): for `k ≥ sup_{B_t(z)} u`
  the competitor `v = w - η (w - k)₊` gives the one-step inequality for `F = (w - k)₊`, with no
  error term.
* `step_below` (obstacle from above, `0 ≤ w ≤ u`; paper Lemma 6.3, Step 1): for
  `k ≤ inf_{B_t(z)} u` the competitor `v = w + η (k - w)₊` gives the one-step inequality for
  `F = (k - w)₊` with the error term `sup Q² |{F > 0} ∩ B_t|`.

Combined with `caccioppoli_of_step` these are the Caccioppoli inequalities of the De Giorgi classes
`DG⁺` (for `w`) and `DG⁻` (for `-w`) of M. Giaquinta, E. Giusti, *Quasi-minima*, Ann. Inst. H.
Poincaré Anal. Non Linéaire 1 (1984), no. 2, 79–107.
-/

open GMTFoundations
open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public section

namespace PerronVariational.Regularity

variable {d : ℕ}

/-- Localization of the gradient comparison from the obstacle ball `B` to a ball `B_t(z)`. -/
theorem step_of_energy {U : Set (E d)} {B : Set (E d)} (hBm : MeasurableSet B) {z : E d}
    {t X : ℝ} (_hzt : ball z t ⊆ U) {Gw Gv GF : E d → E d} {F η : E d → ℝ}
    (hGw : IntegrableOn (fun x ↦ ‖Gw x‖ ^ 2) B) (hGv : IntegrableOn (fun x ↦ ‖Gv x‖ ^ 2) B)
    (hGwt : IntegrableOn (fun x ↦ ‖Gw x‖ ^ 2) (ball z t))
    (hGvt : IntegrableOn (fun x ↦ ‖Gv x‖ ^ 2) (ball z t))
    (hGFt : IntegrableOn (fun x ↦ ‖GF x‖ ^ 2) (ball z t))
    (hE : ∫ x in B, ‖Gw x‖ ^ 2 ≤ (∫ x in B, ‖Gv x‖ ^ 2) + X)
    (hout : ∀ y, y ∉ ball z t → Gv y = Gw y) (houtB : ∀ y ∈ ball z t, y ∉ B → Gv y = Gw y)
    (hin : ∀ y ∈ ball z t, ‖Gv y‖ ^ 2 - ‖Gw y‖ ^ 2 =
      ‖(1 - η y) • GF y - F y • ∇ η y‖ ^ 2 - ‖GF y‖ ^ 2) :
    ∫ x in ball z t, ‖GF x‖ ^ 2 ≤
      (∫ x in ball z t, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2) + X := by
  set h : E d → ℝ := fun y ↦ ‖Gv y‖ ^ 2 - ‖Gw y‖ ^ 2 with hh
  have h1 : ∫ x in B, h x = ∫ x in B ∩ ball z t, h x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hBm inter_subset_left fun y hy ↦ by
      have : y ∉ ball z t := fun h' ↦ hy.2 ⟨hy.1, h'⟩
      simp [hh, hout y this]
  have h2 : ∫ x in ball z t, h x = ∫ x in B ∩ ball z t, h x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball inter_subset_right
      fun y hy ↦ by
        have : y ∉ B := fun h' ↦ hy.2 ⟨h', hy.1⟩
        simp [hh, houtB y hy.1 this]
  have hBh : ∫ x in B, h x = (∫ x in B, ‖Gv x‖ ^ 2) - ∫ x in B, ‖Gw x‖ ^ 2 :=
    integral_sub hGv hGw
  have hint : IntegrableOn (fun x ↦ ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2) (ball z t) := by
    refine ((hGvt.sub hGwt).add hGFt).congr_fun (fun y hy ↦ ?_) measurableSet_ball
    have := hin y hy
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    linarith
  have h3 : ∫ x in ball z t, h x = (∫ x in ball z t, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2) -
      ∫ x in ball z t, ‖GF x‖ ^ 2 := by
    rw [← integral_sub hint hGFt]
    exact setIntegral_congr_fun measurableSet_ball fun y hy ↦ hin y hy
  linarith

section Above

variable {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ}

/-- **One-step inequality, obstacle from below** (`w ≥ u`, paper Lemma 6.3, Step 2). -/
theorem step_above (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq) (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq)
    (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, u y ≤ w y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {z : E d} {t k : ℝ} (hzt : closedBall z t ⊆ U) (hk : ∀ y ∈ ball z t, u y ≤ k)
    {η : E d → ℝ} (hη : ContDiff ℝ ∞ η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hη0 : ∀ x ∉ ball z t, η x = 0 ∧ ∇ η x = 0) :
    ∫ x in ball z t, ‖{y | k < w y}.indicator Gw x‖ ^ 2 ≤
      ∫ x in ball z t, ‖(1 - η x) • {y | k < w y}.indicator Gw x -
        max (w x - k) 0 • ∇ η x‖ ^ 2 := by
  set F : E d → ℝ := fun y ↦ max (w y - k) 0 with hFdef
  set GF : E d → E d := {y | k < w y}.indicator Gw with hGFdef
  have hF : MemH1Loc U F GF := hGw.posPart_sub hU k
  have hηF := hF.mul_smooth hU hη
  have hv := hGw.sub hηF
  set v : E d → ℝ := fun x ↦ w x - η x * F x with hvdef
  set Gv : E d → E d := fun x ↦ Gw x - (η x • GF x + F x • ∇ η x) with hGvdef
  have hF0 : ∀ y, 0 ≤ F y := fun y ↦ le_max_right _ _
  have hFk : ∀ y, w y ≤ k → F y = 0 := fun y hy ↦ max_eq_right (by linarith)
  have hGFk : ∀ y, w y ≤ k → GF y = 0 := fun y hy ↦
    indicator_of_notMem (show y ∉ {y | k < w y} from not_lt.2 hy) _
  have hzU : ball z t ⊆ U := ball_subset_closedBall.trans hzt
  have hBm : MeasurableSet (ball x₀ r) := measurableSet_ball
  -- admissibility
  have hP1 : ∀ y ∈ U \ ball x₀ r, v y = u y := by
    intro y hy
    change w y - η y * F y = u y
    by_cases hyt : y ∈ ball z t
    · have : w y ≤ k := (hwout y hy).symm ▸ hk y hyt
      simp only [hFk y this, mul_zero, sub_zero]; exact hwout y hy
    · simp only [(hη0 y hyt).1, zero_mul, sub_zero]; exact hwout y hy
  have hP2 : ∀ y ∈ U, u y ≤ v y := by
    intro y hy
    change u y ≤ w y - η y * F y
    by_cases hwk : w y ≤ k
    · simp only [hFk y hwk, mul_zero, sub_zero]; exact hwu y hy
    · by_cases hyt : y ∈ ball z t
      · have hFy : F y = w y - k := max_eq_left (by linarith)
        rw [hFy]
        have := hk y hyt
        have h01 := hη01 y
        nlinarith [hwu y hy]
      · simp only [(hη0 y hyt).1, zero_mul, sub_zero]; exact hwu y hy
  have hJ := hmin v Gv hv
    ((ae_restrict_iff' (hU.measurableSet.diff hBm)).2 (Eventually.of_forall hP1))
    ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall hP2))
  have hpos : posSet v (ball x₀ r) ⊆ posSet w (ball x₀ r) ∪ ∅ := by
    intro y hy
    refine Or.inl ⟨hy.1, ?_⟩
    have := hy.2
    have : 0 ≤ η y * F y := mul_nonneg (hη01 y).1 (hF0 y)
    simp only [hvdef] at *
    linarith [hy.2]
  have hcB : IsCompact (closedBall x₀ r) := isCompact_closedBall _ _
  have hGwB := (integrableOn_norm_sq_of_memH1Loc hGw hB hcB).mono_set ball_subset_closedBall
  have hGvB := (integrableOn_norm_sq_of_memH1Loc hv hB hcB).mono_set ball_subset_closedBall
  have hct : IsCompact (closedBall z t) := isCompact_closedBall _ _
  have hE := integral_norm_sq_le_of_energyJ_le hBm measure_ball_lt_top.ne
    (by simp) hCq (fun x hx ↦ hQ x (hB (ball_subset_closedBall hx))) hGwB hGvB hJ hpos
  simp only [measure_empty, ENNReal.toReal_zero, mul_zero, add_zero] at hE
  have := step_of_energy (X := 0) hBm hzU hGwB hGvB
    ((integrableOn_norm_sq_of_memH1Loc hGw hzt hct).mono_set ball_subset_closedBall)
    ((integrableOn_norm_sq_of_memH1Loc hv hzt hct).mono_set ball_subset_closedBall)
    ((integrableOn_norm_sq_of_memH1Loc hF hzt hct).mono_set ball_subset_closedBall)
    (by simpa using hE) (fun y hy ↦ ?_) (fun y hy hyB ↦ ?_) (fun y hy ↦ ?_) (η := η) (F := F)
  · simpa using this
  · simp [hGvdef, (hη0 y hy).1, (hη0 y hy).2]
  · have hwk : w y ≤ k := (hwout y ⟨hzU hy, hyB⟩).symm ▸ hk y hy
    simp [hGvdef, hFk y hwk, hGFk y hwk]
  · by_cases hwk : w y ≤ k
    · simp [hGvdef, hFk y hwk, hGFk y hwk]
    · have hGF : GF y = Gw y := indicator_of_mem (show y ∈ {y | k < w y} from not_le.1 hwk) _
      simp only [hGvdef, hGF]
      congr 2
      rw [sub_smul, one_smul]
      abel_nf

end Above

section Below

variable {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ}

/-- **One-step inequality, obstacle from above** (`0 ≤ w ≤ u`, paper Lemma 6.3, Step 1).
The error term comes from the growth of the positivity set. -/
theorem step_below (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq) (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq)
    (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {z : E d} {t k : ℝ} (hzt : closedBall z t ⊆ U) (hk : ∀ y ∈ ball z t, k ≤ u y)
    {η : E d → ℝ} (hη : ContDiff ℝ ∞ η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hη0 : ∀ x ∉ ball z t, η x = 0 ∧ ∇ η x = 0) :
    ∫ x in ball z t, ‖{y | w y < k}.indicator (fun y ↦ -Gw y) x‖ ^ 2 ≤
      (∫ x in ball z t, ‖(1 - η x) • {y | w y < k}.indicator (fun y ↦ -Gw y) x -
        max (k - w x) 0 • ∇ η x‖ ^ 2) +
      Cq * (volume ({x | 0 < max (k - w x) 0} ∩ ball z t)).toReal := by
  set F : E d → ℝ := fun y ↦ max (k - w y) 0 with hFdef
  set GF : E d → E d := {y | w y < k}.indicator (fun y ↦ -Gw y) with hGFdef
  have hF : MemH1Loc U F GF := hGw.posPart_const_sub hU k
  have hηF := hF.mul_smooth hU hη
  have hv := hGw.add hηF
  set v : E d → ℝ := fun x ↦ w x + η x * F x with hvdef
  set Gv : E d → E d := fun x ↦ Gw x + (η x • GF x + F x • ∇ η x) with hGvdef
  have hF0 : ∀ y, 0 ≤ F y := fun y ↦ le_max_right _ _
  have hFk : ∀ y, k ≤ w y → F y = 0 := fun y hy ↦ max_eq_right (by linarith)
  have hGFk : ∀ y, k ≤ w y → GF y = 0 := fun y hy ↦
    indicator_of_notMem (show y ∉ {y | w y < k} from not_lt.2 hy) _
  have hzU : ball z t ⊆ U := ball_subset_closedBall.trans hzt
  have hBm : MeasurableSet (ball x₀ r) := measurableSet_ball
  have hP1 : ∀ y ∈ U \ ball x₀ r, v y = u y := by
    intro y hy
    change w y + η y * F y = u y
    by_cases hyt : y ∈ ball z t
    · have : k ≤ w y := (hwout y hy).symm ▸ hk y hyt
      simp only [hFk y this, mul_zero, add_zero]; exact hwout y hy
    · simp only [(hη0 y hyt).1, zero_mul, add_zero]; exact hwout y hy
  have hP2 : ∀ y ∈ U, 0 ≤ v y ∧ v y ≤ u y := by
    intro y hy
    change 0 ≤ w y + η y * F y ∧ w y + η y * F y ≤ u y
    have hηF0 : 0 ≤ η y * F y := mul_nonneg (hη01 y).1 (hF0 y)
    refine ⟨by linarith [(hwu y hy).1], ?_⟩
    by_cases hwk : k ≤ w y
    · simp only [hFk y hwk, mul_zero, add_zero]; exact (hwu y hy).2
    · by_cases hyt : y ∈ ball z t
      · have hFy : F y = k - w y := max_eq_left (by linarith)
        rw [hFy]
        have := hk y hyt
        have h01 := hη01 y
        nlinarith
      · simp only [(hη0 y hyt).1, zero_mul, add_zero]; exact (hwu y hy).2
  have hJ := hmin v Gv hv
    ((ae_restrict_iff' (hU.measurableSet.diff hBm)).2 (Eventually.of_forall hP1))
    ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall hP2))
  have hpos : posSet v (ball x₀ r) ⊆ posSet w (ball x₀ r) ∪ ({x | 0 < F x} ∩ ball z t) := by
    intro y hy
    by_cases hwy : 0 < w y
    · exact Or.inl ⟨hy.1, hwy⟩
    · right
      have hvy : 0 < w y + η y * F y := hy.2
      have hηFy : 0 < η y * F y := by linarith
      have hFy : 0 < F y := by
        rcases (hF0 y).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hηFy; exact absurd hηFy (lt_irrefl 0)
      refine ⟨hFy, ?_⟩
      by_contra hyt
      rw [(hη0 y hyt).1, zero_mul] at hηFy
      exact lt_irrefl 0 hηFy
  have hcB : IsCompact (closedBall x₀ r) := isCompact_closedBall _ _
  have hGwB := (integrableOn_norm_sq_of_memH1Loc hGw hB hcB).mono_set ball_subset_closedBall
  have hGvB := (integrableOn_norm_sq_of_memH1Loc hv hB hcB).mono_set ball_subset_closedBall
  have hct : IsCompact (closedBall z t) := isCompact_closedBall _ _
  have hE := integral_norm_sq_le_of_energyJ_le hBm measure_ball_lt_top.ne
    (volume_inter_ball_ne_top _ z t) hCq (fun x hx ↦ hQ x (hB (ball_subset_closedBall hx)))
    hGwB hGvB hJ hpos
  refine step_of_energy hBm hzU hGwB hGvB
    ((integrableOn_norm_sq_of_memH1Loc hGw hzt hct).mono_set ball_subset_closedBall)
    ((integrableOn_norm_sq_of_memH1Loc hv hzt hct).mono_set ball_subset_closedBall)
    ((integrableOn_norm_sq_of_memH1Loc hF hzt hct).mono_set ball_subset_closedBall)
    hE (fun y hy ↦ ?_) (fun y hy hyB ↦ ?_) (fun y hy ↦ ?_)
  · simp [hGvdef, (hη0 y hy).1, (hη0 y hy).2]
  · have hwk : k ≤ w y := (hwout y ⟨hzU hy, hyB⟩).symm ▸ hk y hy
    simp [hGvdef, hFk y hwk, hGFk y hwk]
  · by_cases hwk : k ≤ w y
    · have hm : max (k - w y) 0 = 0 := max_eq_right (sub_nonpos.2 hwk)
      simp [hGvdef, hFk y hwk, hGFk y hwk, hm]
    · have hGF : GF y = -Gw y :=
        indicator_of_mem (show y ∈ {y | w y < k} from not_le.1 hwk) (fun y ↦ -Gw y)
      have e : (1 - η y) • GF y - F y • ∇ η y = -(Gw y + (η y • GF y + F y • ∇ η y)) := by
        rw [hGF, sub_smul, one_smul]
        simp only [smul_neg]
        abel
      simp only [hGvdef]
      rw [e, norm_neg, hGF, norm_neg]

end Below

/-! ### The De Giorgi classes of the obstacle minimizers -/

/-- The Caccioppoli constant `256 C²` (`C = cutoffConst`). -/
noncomputable def caccConst : ℝ := 256 * cutoffConst ^ 2

theorem caccConst_pos : 0 < caccConst := by
  have := cutoffConst_pos; unfold caccConst; positivity

theorem setOf_posPart_sub_pos (f : E d → ℝ) (k : ℝ) :
    {x | 0 < max (f x - k) 0} = {x | k < f x} := by
  ext x; simp

/-- **`w ∈ DG⁺`** for the obstacle-from-below minimizer (`w ≥ u`), at levels
`k ≥ K ≥ sup_{B_{R₀}(z)} u`, with no error term. -/
theorem isDeGiorgiAt_above {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d} {x₀ : E d}
    {r : ℝ} (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq) (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq)
    (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, u y ≤ w y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {z : E d} {R₀ K : ℝ} (hzR : closedBall z R₀ ⊆ U) (hK : ∀ y ∈ ball z R₀, u y ≤ K) :
    IsDeGiorgiAt w Gw z R₀ K caccConst 0 := by
  intro k hk ρ R hρ hρR hR
  have hc : IsCompact (closedBall z R₀) := isCompact_closedBall _ _
  have hF := hGw.posPart_sub hU k
  have h := caccioppoli_of_step (Er := 0) le_rfl
    ((integrableOn_norm_sq_of_memH1Loc hF hzR hc).mono_set ball_subset_closedBall)
    ((integrableOn_sq_of_memH1Loc hF hzR hc).mono_set ball_subset_closedBall)
    (fun t ht htR η hη hη01 hη0 ↦ by
      have := step_above hU hCq hQ hB hGw hwout hwu hmin
        ((closedBall_subset_closedBall htR).trans hzR)
        (fun y hy ↦ (hK y (ball_subset_ball htR hy)).trans hk) hη hη01 hη0
      simpa using this) hρ hρR hR
  simpa [caccConst] using h

/-- **`-w ∈ DG⁺`** (i.e. `w ∈ DG⁻`) for the obstacle-from-above minimizer (`0 ≤ w ≤ u`), at
levels `k ≥ K`, where `-K ≤ inf_{B_{R₀}(z)} u`, with error constant `128 Cq`, `Q² ≤ Cq`. -/
theorem isDeGiorgiAt_below {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d} {x₀ : E d}
    {r : ℝ} (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq) (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq)
    (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {z : E d} {R₀ K : ℝ} (hzR : closedBall z R₀ ⊆ U) (hK : ∀ y ∈ ball z R₀, -K ≤ u y) :
    IsDeGiorgiAt (fun x ↦ -w x) (fun x ↦ -Gw x) z R₀ K caccConst (128 * Cq) := by
  intro k hk ρ R hρ hρR hR
  have hc : IsCompact (closedBall z R₀) := isCompact_closedBall _ _
  have hF := hGw.neg.posPart_sub hU k
  have hset : {y | k < -w y} = {y | w y < -k} := by ext y; simp [lt_neg]
  have hmax : ∀ x, max (-k - w x) 0 = max (-w x - k) 0 := fun x ↦ by ring_nf
  have h := caccioppoli_of_step (Er := Cq) hCq
    ((integrableOn_norm_sq_of_memH1Loc hF hzR hc).mono_set ball_subset_closedBall)
    ((integrableOn_sq_of_memH1Loc hF hzR hc).mono_set ball_subset_closedBall)
    (fun t ht htR η hη hη01 hη0 ↦ by
      have := step_below (k := -k) hU hCq hQ hB hGw hwout hwu hmin
        ((closedBall_subset_closedBall htR).trans hzR)
        (fun y hy ↦ (neg_le_neg hk).trans (hK y (ball_subset_ball htR hy))) hη hη01 hη0
      simp only [hmax] at this
      rw [hset]
      exact this) hρ hρR hR
  rw [setOf_posPart_sub_pos] at h
  convert h using 2
  rw [caccConst, mul_div_assoc]

end PerronVariational.Regularity

end
