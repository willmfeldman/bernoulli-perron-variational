/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.TwoDisc.Lower
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The two-plane point of the two-disc model example

For the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 (`[AFS]`):

* `perronSmallest_eq_vSup`: `u_min = v` on `U ∩ {|x| ≤ ρ}`; in particular near the two discs,
  `u_min = (a log (a/|x - p|))₊ + (a log (a/|x + p|))₊`;
* `zero_mem_freeBoundary`: `0` is a free boundary point of `u_min`;
* `tendstoLocallyUniformly_blowup`: the blow-ups `u_min(t y)/t` converge to `|y₁|` locally
  uniformly as `t → 0⁺` (from `|log (1 + u) - u| ≤ 2u²`), so every blow-up limit of `u_min` at
  `0` is `y ↦ |y₁|` (`isBlowupLimit_eq`).
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian ContDiff

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

/-- The smallest supersolution of the example. -/
abbrev uMin : E 2 → ℝ := perronSmallest domain (fun _ ↦ 1) gSub

theorem perronSuperClass_nonempty' : (perronSuperClass domain (fun _ ↦ (1 : ℝ)) gSub).Nonempty :=
  ⟨vSup, vSup_mem_perronSuperClass⟩

theorem max_wIn_eq {z x : E 2} (hτ : 1 / 400 ≤ ‖x - z‖ ^ 2) :
    max (wIn z x) 0 = max ((Real.log (1 / 100) - Real.log (‖x - z‖ ^ 2)) / 20) 0 := by
  rw [wIn_val hτ, pV, max_floorCap_eq cst_pos (by linarith [cst_pos]) (aw_le_cst hτ)]

/-- `u_min = v` on `U ∩ {|x| ≤ ρ}`. -/
theorem perronSmallest_eq_vSup {y : E 2} (hy : y ∈ domain) (h0 : ‖y - 0‖ ^ 2 ≤ rho ^ 2) :
    uMin y = vSup y := by
  refine le_antisymm (perronSmallest_le_vSup (subset_closure hy)) ?_
  obtain ⟨-, hp, hm⟩ := mem_domain_norm hy
  have hnn := perronSmallest_nonneg perronSuperClass_nonempty' (subset_closure hy)
  by_cases A : ‖y - hole‖ ^ 2 < 1 / 100
  · rw [vSup_eq_plus A.le, max_eq_left (wIn_pos hp.le A).le]
    exact wIn_le_perronSmallest (Or.inl rfl) hp.le A
  by_cases B : ‖y + hole‖ ^ 2 < 1 / 100
  · have hB : ‖y - -hole‖ ^ 2 < 1 / 100 := by rw [sq_sub_neg_hole]; exact B
    have hm' : 1 / 400 ≤ ‖y - -hole‖ ^ 2 := by rw [sq_sub_neg_hole]; exact hm.le
    rw [vSup_eq_minus B.le, max_eq_left (wIn_pos hm' hB).le]
    exact wIn_le_perronSmallest (Or.inr rfl) hm' hB
  push Not at A B
  rw [vSup, max_wIn_eq_zero A, max_wIn_eq_zero (z := -hole) (by rw [sq_sub_neg_hole]; exact B),
    max_hOut_eq_zero h0]
  simpa using hnn

/-! ### Near `0` -/

theorem mem_domain_of_small {y : E 2} (h : ‖y‖ ≤ 1 / 100) : y ∈ domain ∧ ‖y - 0‖ ^ 2 ≤ rho ^ 2 := by
  have h2 : ‖y‖ ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [norm_sq_eq] at h2
  refine ⟨?_, ?_⟩
  · rw [mem_domain_iff]
    refine ⟨by nlinarith, ?_, ?_⟩ <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  · rw [sub_zero, norm_sq_eq]; nlinarith [rho_sq_bounds.1]

/-- Near `0`, `u_min` is the sum of the two radial solutions. -/
theorem uMin_eq_small {y : E 2} (h : ‖y‖ ≤ 1 / 100) :
    uMin y = max ((Real.log (1 / 100) - Real.log (‖y - hole‖ ^ 2)) / 20) 0 +
      max ((Real.log (1 / 100) - Real.log (‖y + hole‖ ^ 2)) / 20) 0 := by
  obtain ⟨hy, h0⟩ := mem_domain_of_small h
  obtain ⟨-, hp, hm⟩ := mem_domain_norm hy
  rw [perronSmallest_eq_vSup hy h0, vSup, max_wIn_eq hp.le,
    max_wIn_eq (z := -hole) (by rw [sq_sub_neg_hole]; exact hm.le),
    max_hOut_eq_zero h0, sq_sub_neg_hole]
  ring

/-! ### The logarithmic estimate -/

theorem abs_log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) : |Real.log (1 + u) - u| ≤ 2 * u ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one,
    sub_neg_eq_add, abs_neg] at h
  rw [show Real.log (1 + u) - u = -u + Real.log (1 + u) by ring]
  calc _ ≤ |u| ^ 2 / (1 - |u|) := by rw [add_comm (1 : ℝ) u] at *; simpa [add_comm] using h
    _ ≤ 2 * u ^ 2 := by
      rw [div_le_iff₀ (by linarith), sq_abs]
      nlinarith [sq_nonneg u, abs_nonneg u]

/-- The one-disc blow-up estimate: with `τ = (t a - s/10)² + (t b)²`, `s = ±1`,
`|(log (1/100) - log τ)/(20 t) - s a| ≤ 50 t M²` for `a² + b² ≤ M²`, `t M ≤ 1/100`. -/
theorem blowup_est {a b t M s : ℝ} (hs : s = 1 ∨ s = -1) (ht : 0 < t) (hM : 0 ≤ M)
    (hab : a ^ 2 + b ^ 2 ≤ M ^ 2) (htM : t * M ≤ 1 / 100) :
    |(Real.log (1 / 100) - Real.log ((t * a - s / 10) ^ 2 + (t * b) ^ 2)) / 20 / t - s * a| ≤
      50 * t * M ^ 2 := by
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have haM : |a| ≤ M := by
    rw [← abs_of_nonneg hM]; exact sq_le_sq.1 (by nlinarith [sq_nonneg b])
  set u := 100 * t ^ 2 * (a ^ 2 + b ^ 2) - 20 * t * (s * a) with hu
  have hτ : (t * a - s / 10) ^ 2 + (t * b) ^ 2 = (1 + u) / 100 := by
    rw [hu]; linear_combination (1 / 100) * hs2
  have hsa : |s * a| ≤ M := by rw [abs_mul]; rcases hs with rfl | rfl <;> simpa using haM
  have hu1 : |u| ≤ 21 * (t * M) := by
    have h1 : 100 * t ^ 2 * (a ^ 2 + b ^ 2) ≤ t * M := by
      have hsq : 100 * t ^ 2 * (a ^ 2 + b ^ 2) ≤ 100 * (t * M) ^ 2 := by nlinarith [sq_nonneg t]
      have : 100 * (t * M) ^ 2 ≤ t * M := by nlinarith [mul_nonneg ht.le hM]
      linarith
    have h2 : 0 ≤ 100 * t ^ 2 * (a ^ 2 + b ^ 2) := by positivity
    have h3 : |20 * t * (s * a)| ≤ 20 * (t * M) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 20 * t)]; nlinarith
    rw [hu]
    calc |100 * t ^ 2 * (a ^ 2 + b ^ 2) - 20 * t * (s * a)| ≤
        |100 * t ^ 2 * (a ^ 2 + b ^ 2)| + |20 * t * (s * a)| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg h2]; linarith
  have hu2 : |u| ≤ 1 / 2 := by linarith
  have hlog := abs_log_one_add_sub_le hu2
  have e : (Real.log (1 / 100) - Real.log ((t * a - s / 10) ^ 2 + (t * b) ^ 2)) / 20 / t - s * a =
      -(Real.log (1 + u) - u) / (20 * t) - 5 * t * (a ^ 2 + b ^ 2) := by
    have h1u : 0 < 1 + u := by linarith [abs_le.1 hu2]
    rw [hτ, Real.log_div h1u.ne' (by norm_num), one_div, Real.log_inv]
    field_simp
    rw [hu]; ring
  rw [e]
  have hu3 : u ^ 2 ≤ 441 * t ^ 2 * M ^ 2 := by
    have := sq_le_sq' (abs_le.1 hu1).1 (abs_le.1 hu1).2
    nlinarith
  calc |-(Real.log (1 + u) - u) / (20 * t) - 5 * t * (a ^ 2 + b ^ 2)| ≤
      |-(Real.log (1 + u) - u) / (20 * t)| + |5 * t * (a ^ 2 + b ^ 2)| := abs_sub _ _
    _ ≤ 2 * u ^ 2 / (20 * t) + 5 * t * M ^ 2 := by
      gcongr
      · rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 20 * t)]
        exact div_le_div_of_nonneg_right hlog (by positivity)
      · rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hab (by positivity)
    _ ≤ 50 * t * M ^ 2 := by
      have : 2 * u ^ 2 / (20 * t) ≤ 45 * t * M ^ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith

/-- `|y₁|`, the two-plane solution. -/
def twoPlane (y : E 2) : ℝ := |inner ℝ y (EuclideanSpace.single 0 1)|

theorem twoPlane_eq (y : E 2) : twoPlane y = |y 0| := by
  simp [twoPlane, EuclideanSpace.inner_single_right]

/-- **The blow-up estimate.** For `|y| ≤ M` and `0 < t ≤ 1/(100 M)`,
`|u_min(t y)/t - |y₁|| ≤ 100 t M²`. -/
theorem blowup_sub_twoPlane_le {y : E 2} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hy : ‖y‖ ≤ M)
    (htM : t * M ≤ 1 / 100) : |blowup uMin 0 t y - twoPlane y| ≤ 100 * t * M ^ 2 := by
  have hty : ‖t • y‖ ≤ 1 / 100 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith [norm_nonneg y]
  have hab : y 0 ^ 2 + y 1 ^ 2 ≤ M ^ 2 := by
    rw [← norm_sq_eq]; exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  rw [blowup, zero_add, uMin_eq_small hty, twoPlane_eq, norm_sub_hole_sq, norm_add_hole_sq]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have e1 := blowup_est (s := 1) (a := y 0) (b := y 1) (Or.inl rfl) ht hM hab htM
  have e2 := blowup_est (s := -1) (a := y 0) (b := y 1) (Or.inr rfl) ht hM hab htM
  simp only [one_div, one_mul, neg_mul, one_mul] at e1 e2
  have r1 : (t * y 0 - 10⁻¹) ^ 2 = (t * y 0 - 1 / 10) ^ 2 := by norm_num
  have r2 : (t * y 0 - -1 / 10) ^ 2 = (t * y 0 + 1 / 10) ^ 2 := by ring
  set A := (Real.log (1 / 100) - Real.log ((t * y 0 - 1 / 10) ^ 2 + (t * y 1) ^ 2)) / 20
  set B := (Real.log (1 / 100) - Real.log ((t * y 0 + 1 / 10) ^ 2 + (t * y 1) ^ 2)) / 20
  have hA : |A / t - y 0| ≤ 50 * t * M ^ 2 := by
    have := blowup_est (s := 1) (a := y 0) (b := y 1) (Or.inl rfl) ht hM hab htM
    simpa [A] using this
  have hB : |B / t - -y 0| ≤ 50 * t * M ^ 2 := by
    have := blowup_est (s := -1) (a := y 0) (b := y 1) (Or.inr rfl) ht hM hab htM
    have r : (t * y 0 - -1 / 10) = (t * y 0 + 1 / 10) := by ring
    rw [r] at this
    simpa [B] using this
  have habs : |y 0| = max (y 0) 0 + max (-y 0) 0 := by
    rcases le_total 0 (y 0) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
  have hdiv : (max A 0 + max B 0) / t = max (A / t) 0 + max (B / t) 0 := by
    rw [add_div, ← max_div_div_right ht.le A 0, ← max_div_div_right ht.le B 0, zero_div]
  rw [hdiv, habs]
  have m1 := abs_max_sub_max_le_abs (A / t) (y 0) 0
  have m2 := abs_max_sub_max_le_abs (B / t) (-y 0) 0
  calc |max (A / t) 0 + max (B / t) 0 - (max (y 0) 0 + max (-y 0) 0)| ≤
      |max (A / t) 0 - max (y 0) 0| + |max (B / t) 0 - max (-y 0) 0| := by
        rw [show max (A / t) 0 + max (B / t) 0 - (max (y 0) 0 + max (-y 0) 0) =
          (max (A / t) 0 - max (y 0) 0) + (max (B / t) 0 - max (-y 0) 0) by ring]
        exact abs_add_le _ _
    _ ≤ 100 * t * M ^ 2 := by linarith

/-- **Blow-up at `0`.** `u_min(t y)/t → |y₁|` locally uniformly as `t → 0⁺`. -/
theorem tendstoLocallyUniformly_blowup :
    TendstoLocallyUniformly (fun t ↦ blowup uMin 0 t) twoPlane (𝓝[>] 0) := by
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
  exact lt_of_le_of_lt (blowup_sub_twoPlane_le ht.1 hM.le hy htM) hte

/-- Every blow-up limit of `u_min` at `0` is the two-plane solution `|y₁|`. -/
theorem isBlowupLimit_eq {v : E 2 → ℝ} (hv : IsBlowupLimit uMin 0 v) (y : E 2) :
    v y = twoPlane y := by
  obtain ⟨r, hr, hr0, hconv⟩ := hv
  have hr' : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hr0, Eventually.of_forall hr⟩
  have h1 : Tendsto (fun n ↦ blowup uMin 0 (r n) y) atTop (𝓝 (v y)) :=
    (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ y)
  have h2 : Tendsto (fun n ↦ blowup uMin 0 (r n) y) atTop (𝓝 (twoPlane y)) :=
    ((tendstoLocallyUniformlyOn_univ.2 tendstoLocallyUniformly_blowup).tendsto_at
      (mem_univ y)).comp hr'
  exact tendsto_nhds_unique h1 h2

/-! ### `0` is a free boundary point -/

theorem uMin_zero : uMin 0 = 0 := by
  have h1 : ‖(0 : E 2) - hole‖ ^ 2 = 1 / 100 := by simp [norm_hole]; norm_num
  have h2 : ‖(0 : E 2) + hole‖ ^ 2 = 1 / 100 := by simp [norm_hole]; norm_num
  rw [uMin_eq_small (by simp), h1, h2, sub_self]
  simp

/-- The unit vector `e₁`. -/
def eOne : E 2 := EuclideanSpace.single 0 1

@[simp] theorem eOne_zero : eOne 0 = 1 := by simp [eOne]
@[simp] theorem eOne_one : eOne 1 = 0 := by simp [eOne]

theorem norm_smul_eOne (t : ℝ) : ‖t • eOne‖ = |t| := by simp [eOne, norm_smul]

theorem uMin_pos_e₁ {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 100) : 0 < uMin (t • eOne) := by
  rw [uMin_eq_small (by rw [norm_smul_eOne, abs_of_pos ht]; exact ht')]
  have hτ : ‖t • eOne - hole‖ ^ 2 = (t - 1 / 10) ^ 2 := by
    rw [norm_sub_hole_sq]; simp
  rw [hτ]
  have : Real.log ((t - 1 / 10) ^ 2) < Real.log (1 / 100) :=
    Real.log_lt_log (by nlinarith) (by nlinarith)
  have h1 : 0 < (Real.log (1 / 100) - Real.log ((t - 1 / 10) ^ 2)) / 20 := by linarith
  rw [max_eq_left h1.le]
  have := le_max_right ((Real.log (1 / 100) - Real.log (‖t • eOne + hole‖ ^ 2)) / 20) 0
  linarith

theorem tendsto_smul_eOne : Tendsto (fun t : ℝ ↦ t • eOne) (𝓝[>] 0) (𝓝 0) := by
  have : Continuous fun t : ℝ ↦ t • eOne := by fun_prop
  have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa using h

theorem zero_mem_freeBoundary : (0 : E 2) ∈ freeBoundary uMin domain := by
  obtain ⟨h0U, -⟩ := mem_domain_of_small (y := 0) (by simp)
  refine ⟨⟨?_, ?_⟩, h0U⟩
  · -- `0` is a limit of the positive points `t e₁`
    refine mem_closure_of_tendsto tendsto_smul_eOne ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 100 by norm_num)] with t ht
    exact ⟨(mem_domain_of_small (by rw [norm_smul_eOne, abs_of_pos ht.1]; exact ht.2.le)).1,
      uMin_pos_e₁ ht.1 ht.2.le⟩
  · intro h
    have := interior_subset h
    simp [posSet, uMin_zero] at this

end PerronVariational.TwoDisc

end
