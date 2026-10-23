/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.TwoDisc.Domain
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The necklace example: geometry

Plane geometry for the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M.
Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981 (`[AFS]`).

`N = 100` holes of radius `r = 1/20` are centred at `z_k = R (cos (2k+1)θ, sin (2k+1)θ)`, with
`θ = π/N` and `R = a / sin θ`, `a = 1/10`. Neighbouring centres are at distance `2a`, so the discs
`B_a(z_k)` touch at the kissing points `m_k = ρ_in (cos 2kθ, sin 2kθ)`, `ρ_in = R cos θ`.

* `norm_pol_sub_pol_sq`: the law of cosines in polar form.
* `sin_sq_le_sin_sq_int_mul`: `sin² (iπ/M) ≤ sin² (mπ/M)` when `m mod M ∈ [i, M - i]`.
* `norm_cen_sub_cen_sq`, `two_kissRad_le_norm_cen_sub_cen`: distances between centres.
* `cen_eq_kiss_add`, `cen_sub_one_eq_kiss_sub`: the kissing points.
* `eq_of_mem_hole_of_mem_hole`: a ray from `0` meets at most one hole.
* `exists_norm_sub_cen_sq_le`: the inscribed circle `∂B_{ρ_in}` is covered by the closed discs
  `B̄_a(z_k)`, and it meets their boundaries only at the kissing points.
-/

open Set Filter Topology Metric Real
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational.Necklace

open TwoDisc (norm_sq_eq)

/-! ### Constants -/

/-- The number of holes, `N = 100`. -/
def numHoles : ℕ := 100

/-- Half the angle between neighbouring centres, `θ = π / N`. -/
def ang : ℝ := π / numHoles

/-- The hole radius `r = 1/20`. -/
def holeRad : ℝ := 1 / 20

/-- The kissing radius `a = 1/10`: the free boundary radius of each radial solution. -/
def kissRad : ℝ := 1 / 10

/-- The radius of the circle of centres, `R = a / sin θ`. -/
def ringRad : ℝ := kissRad / Real.sin ang

/-- The radius of the circle of kissing points, `ρ_in = R cos θ`. -/
def innerRad : ℝ := ringRad * Real.cos ang

/-- The outer radius `4`. -/
def outerRad : ℝ := 4

/-- The point with polar coordinates `(s, φ)`. -/
def pol (s φ : ℝ) : E 2 := !₂[s * Real.cos φ, s * Real.sin φ]

/-- The centre `z_k = R (cos (2k+1)θ, sin (2k+1)θ)` of the `k`-th hole (`k ∈ ℤ`, periodic). -/
def cen (k : ℤ) : E 2 := pol ringRad ((2 * k + 1) * ang)

/-- The kissing point `m_k = ρ_in (cos 2kθ, sin 2kθ)` between the holes `k - 1` and `k`. -/
def kiss (k : ℤ) : E 2 := pol innerRad (2 * k * ang)

/-- The unit tangent `e_k = (-sin 2kθ, cos 2kθ)` at the kissing point `m_k`. -/
def tang (k : ℤ) : E 2 := !₂[-Real.sin (2 * k * ang), Real.cos (2 * k * ang)]

/-! ### Numerics -/

theorem numHoles_pos : (0 : ℝ) < numHoles := by norm_num [numHoles]

theorem ang_bounds : 0.0314 < ang ∧ ang < 0.0315 := by
  have h1 := pi_gt_d2; have h2 := pi_lt_d2
  unfold ang numHoles
  constructor <;> rw [Nat.cast_ofNat] <;> [rw [lt_div_iff₀ (by norm_num)];
    rw [div_lt_iff₀ (by norm_num)]] <;> linarith

theorem ang_pos : 0 < ang := by linarith [ang_bounds.1]

theorem sin_ang_bounds : 0.03139 < Real.sin ang ∧ Real.sin ang < 0.0315 := by
  obtain ⟨h1, h2⟩ := ang_bounds
  refine ⟨?_, (sin_lt ang_pos).trans h2⟩
  have := sin_gt_sub_cube ang_pos
  have h3 : ang ^ 3 ≤ 0.0315 ^ 3 := pow_le_pow_left₀ ang_pos.le h2.le 3
  nlinarith

theorem sin_ang_pos : 0 < Real.sin ang := by linarith [sin_ang_bounds.1]

theorem cos_ang_bounds : 0.9995 < Real.cos ang ∧ Real.cos ang ≤ 1 := by
  refine ⟨?_, cos_le_one _⟩
  have := one_sub_sq_div_two_le_cos (x := ang)
  have h : ang ^ 2 < 0.0315 ^ 2 := pow_lt_pow_left₀ ang_bounds.2 ang_pos.le (by norm_num)
  nlinarith

theorem ringRad_bounds : 3.17 < ringRad ∧ ringRad < 3.19 := by
  obtain ⟨h1, h2⟩ := sin_ang_bounds
  unfold ringRad kissRad
  constructor
  · rw [lt_div_iff₀ sin_ang_pos]; linarith
  · rw [div_lt_iff₀ sin_ang_pos]; linarith

theorem ringRad_pos : 0 < ringRad := by linarith [ringRad_bounds.1]

theorem ringRad_mul_sin : ringRad * Real.sin ang = kissRad := by
  unfold ringRad; field_simp [sin_ang_pos.ne']

theorem innerRad_bounds : 3.16 < innerRad ∧ innerRad < 3.19 := by
  obtain ⟨h1, h2⟩ := ringRad_bounds
  obtain ⟨h3, h4⟩ := cos_ang_bounds
  unfold innerRad
  constructor <;> nlinarith

theorem innerRad_pos : 0 < innerRad := by linarith [innerRad_bounds.1]

/-! ### Polar coordinates -/

@[simp] theorem pol_zero (s φ : ℝ) : pol s φ 0 = s * Real.cos φ := rfl
@[simp] theorem pol_one (s φ : ℝ) : pol s φ 1 = s * Real.sin φ := rfl

/-- The law of cosines: `|pol s φ - pol t ψ|² = s² + t² - 2 s t cos (φ - ψ)`. -/
theorem norm_pol_sub_pol_sq (s t φ ψ : ℝ) :
    ‖pol s φ - pol t ψ‖ ^ 2 = s ^ 2 + t ^ 2 - 2 * s * t * Real.cos (φ - ψ) := by
  rw [norm_sq_eq, cos_sub]
  simp only [PiLp.sub_apply, pol_zero, pol_one]
  linear_combination s ^ 2 * sin_sq_add_cos_sq φ + t ^ 2 * sin_sq_add_cos_sq ψ

theorem norm_pol_sq (s φ : ℝ) : ‖pol s φ‖ ^ 2 = s ^ 2 := by
  rw [norm_sq_eq]
  simp only [pol_zero, pol_one]
  linear_combination s ^ 2 * sin_sq_add_cos_sq φ

theorem norm_pol {s : ℝ} (hs : 0 ≤ s) (φ : ℝ) : ‖pol s φ‖ = s := by
  rw [← sq_eq_sq₀ (norm_nonneg _) hs, norm_pol_sq]

/-- Chords: `|pol s φ - pol s ψ|² = 4 s² sin² ((φ - ψ)/2)`. -/
theorem norm_pol_sub_pol_sq_same (s φ ψ : ℝ) :
    ‖pol s φ - pol s ψ‖ ^ 2 = 4 * s ^ 2 * Real.sin ((φ - ψ) / 2) ^ 2 := by
  rw [norm_pol_sub_pol_sq]
  have h2 : Real.cos (φ - ψ) = 1 - 2 * Real.sin ((φ - ψ) / 2) ^ 2 := by
    have := cos_two_mul ((φ - ψ) / 2)
    rw [mul_div_cancel₀ _ two_ne_zero] at this
    rw [this]; linear_combination 2 * sin_sq_add_cos_sq ((φ - ψ) / 2)
  rw [h2]; ring

theorem pol_add_two_pi_mul (s φ : ℝ) (n : ℤ) : pol s (φ + n * (2 * π)) = pol s φ := by
  ext i; fin_cases i
  · simp [pol, cos_add_int_mul_two_pi]
  · simp [pol, sin_add_int_mul_two_pi]

/-! ### Sines of rational multiples of `π` -/

theorem sin_sq_le_sin_sq {α t : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ π / 2) (hαt : α ≤ t)
    (htα : t ≤ π - α) : Real.sin α ^ 2 ≤ Real.sin t ^ 2 := by
  have h0 : 0 ≤ Real.sin α := sin_nonneg_of_nonneg_of_le_pi hα (by linarith [pi_pos])
  have : Real.sin α ≤ Real.sin t := by
    rcases le_total t (π / 2) with h | h
    · exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) h hαt
    · rw [← sin_pi_sub t]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) (by linarith)
  exact pow_le_pow_left₀ h0 this 2

theorem sin_sq_int_mul_pi_div (M : ℕ) (hM : 0 < M) (m : ℤ) :
    Real.sin (m * π / M) ^ 2 = Real.sin ((m % (M : ℤ) : ℤ) * π / M) ^ 2 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have e : (m : ℝ) * π / M = ((m % (M : ℤ) : ℤ) : ℝ) * π / M + ((m / (M : ℤ) : ℤ) : ℝ) * π := by
    have := Int.emod_add_mul_ediv m M
    have hc : (m : ℝ) = ((m % (M : ℤ) : ℤ) : ℝ) + (M : ℝ) * ((m / (M : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast this.symm
    rw [hc]; field_simp
  rw [e, sin_add_int_mul_pi, mul_pow, ← sq_abs ((-1 : ℝ) ^ _), abs_neg_one_zpow, one_pow,
    one_mul]

/-- `sin² (iπ/M) ≤ sin² (mπ/M)` when `m mod M ∈ [i, M - i]`. -/
theorem sin_sq_le_sin_sq_int_mul (M : ℕ) (hM : 0 < M) (i : ℕ) (hi : 2 * i ≤ M) (m : ℤ)
    (h1 : (i : ℤ) ≤ m % (M : ℤ)) (h2 : m % (M : ℤ) ≤ M - i) :
    Real.sin (i * π / M) ^ 2 ≤ Real.sin (m * π / M) ^ 2 := by
  rw [sin_sq_int_mul_pi_div M hM]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h1' : (i : ℝ) ≤ ((m % (M : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1
  have h2' : ((m % (M : ℤ) : ℤ) : ℝ) ≤ (M : ℝ) - i := by exact_mod_cast h2
  have hi' : 2 * (i : ℝ) ≤ M := by exact_mod_cast hi
  have hp := pi_pos
  apply sin_sq_le_sin_sq (by positivity)
  · rw [div_le_iff₀ hMr]; nlinarith
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1' hp.le) hMr.le
  · calc _ ≤ ((M : ℝ) - i) * π / M :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2' hp.le) hMr.le
      _ = π - i * π / M := by field_simp

/-- If `M ∤ m` then `sin² (π/M) ≤ sin² (mπ/M)`. -/
theorem sin_sq_le_sin_sq_of_not_dvd (M : ℕ) (hM : 2 ≤ M) (m : ℤ) (h : ¬ (M : ℤ) ∣ m) :
    Real.sin (π / M) ^ 2 ≤ Real.sin (m * π / M) ^ 2 := by
  have hM0 : (0 : ℤ) < M := by omega
  have h0 : m % (M : ℤ) ≠ 0 := fun h0 ↦ h (Int.dvd_of_emod_eq_zero h0)
  have := Int.emod_nonneg m hM0.ne'
  have := Int.emod_lt_of_pos m hM0
  have := sin_sq_le_sin_sq_int_mul M (by omega) 1 (by omega) m (by push_cast; omega)
    (by push_cast; omega)
  simpa using this

/-! ### Centres and kissing points -/

theorem cen_add_numHoles (k : ℤ) : cen (k + numHoles) = cen k := by
  unfold cen
  have : (2 * ((k + numHoles : ℤ) : ℝ) + 1) * ang = (2 * k + 1) * ang + (1 : ℤ) * (2 * π) := by
    unfold ang numHoles; push_cast; field_simp; ring
  rw [this, pol_add_two_pi_mul]

theorem cen_emod (k : ℤ) : cen (k % numHoles) = cen k := by
  unfold cen
  have : (2 * ((k % numHoles : ℤ) : ℝ) + 1) * ang =
      (2 * k + 1) * ang + ((-(k / numHoles) : ℤ) : ℝ) * (2 * π) := by
    have hc : (k : ℝ) =
        ((k % (numHoles : ℤ) : ℤ) : ℝ) + (numHoles : ℝ) * ((k / numHoles : ℤ) : ℝ) := by
      exact_mod_cast (Int.emod_add_mul_ediv k numHoles).symm
    rw [hc]; unfold ang numHoles; push_cast; field_simp; ring
  rw [this, pol_add_two_pi_mul]

/-- Every centre is one of `z_0, …, z_{N-1}`. -/
theorem exists_fin_cen_eq (k : ℤ) : ∃ j : Fin numHoles, cen (j : ℕ) = cen k := by
  have h0 := Int.emod_nonneg k (show (numHoles : ℤ) ≠ 0 by norm_num [numHoles])
  have h1 := Int.emod_lt_of_pos k (show (0 : ℤ) < numHoles by norm_num [numHoles])
  refine ⟨⟨(k % numHoles).toNat, by omega⟩, ?_⟩
  rw [← cen_emod k]
  congr 1
  simp only
  omega

theorem norm_cen (k : ℤ) : ‖cen k‖ = ringRad := norm_pol ringRad_pos.le _

theorem norm_cen_sub_cen_sq (j k : ℤ) :
    ‖cen j - cen k‖ ^ 2 = 4 * ringRad ^ 2 * Real.sin ((j - k : ℤ) * π / numHoles) ^ 2 := by
  rw [cen, cen, norm_pol_sub_pol_sq_same]
  congr 3
  unfold ang; push_cast; ring

/-- Distinct centres are at distance at least `2a`. -/
theorem two_kissRad_le_norm_cen_sub_cen {j k : ℤ} (h : ¬ (numHoles : ℤ) ∣ j - k) :
    2 * kissRad ≤ ‖cen j - cen k‖ := by
  have hs := sin_sq_le_sin_sq_of_not_dvd numHoles (by norm_num [numHoles]) (j - k) h
  have hsq : (2 * kissRad) ^ 2 ≤ ‖cen j - cen k‖ ^ 2 := by
    rw [norm_cen_sub_cen_sq, ← ringRad_mul_sin]
    have : Real.sin ang = Real.sin (π / numHoles) := rfl
    rw [this]; nlinarith [sq_nonneg ringRad]
  exact (pow_le_pow_iff_left₀ (by norm_num [kissRad]) (norm_nonneg _) two_ne_zero).1 hsq

/-- Non-neighbouring centres are at distance `> 0.39`. -/
theorem lt_norm_cen_sub_cen {j k : ℤ} (h0 : ¬ (numHoles : ℤ) ∣ j - k)
    (h1 : ¬ (numHoles : ℤ) ∣ j - k - 1) (h2 : ¬ (numHoles : ℤ) ∣ j - k + 1) :
    0.39 < ‖cen j - cen k‖ := by
  have hN : (numHoles : ℤ) = 100 := rfl
  rw [hN] at h0 h1 h2
  have hm0 := Int.emod_nonneg (j - k) (show (100 : ℤ) ≠ 0 by norm_num)
  have hm1 := Int.emod_lt_of_pos (j - k) (show (0 : ℤ) < 100 by norm_num)
  have hs := sin_sq_le_sin_sq_int_mul numHoles (by norm_num [numHoles]) 2 (by norm_num [numHoles])
    (j - k) (by rw [hN]; push_cast; omega) (by rw [hN]; push_cast; omega)
  have e2 : Real.sin ((2 : ℕ) * π / numHoles) = 2 * Real.sin ang * Real.cos ang := by
    rw [← sin_two_mul]; unfold ang; congr 1; push_cast; ring
  rw [e2] at hs
  have hsq : 0.39 ^ 2 < ‖cen j - cen k‖ ^ 2 := by
    rw [norm_cen_sub_cen_sq]
    have hRs := ringRad_mul_sin
    have hc := cos_ang_bounds.1
    have : (2 * Real.sin ang * Real.cos ang) ^ 2 * ringRad ^ 2 =
        4 * kissRad ^ 2 * Real.cos ang ^ 2 := by rw [← hRs]; ring
    have hc2 : (0.9995 : ℝ) ^ 2 < Real.cos ang ^ 2 := pow_lt_pow_left₀ hc (by norm_num) two_ne_zero
    unfold kissRad at this
    nlinarith
  exact (pow_lt_pow_iff_left₀ (by norm_num) (norm_nonneg _) two_ne_zero).1 hsq

theorem cen_eq_kiss_add (k : ℤ) : cen k = kiss k + kissRad • tang k := by
  rw [← ringRad_mul_sin]
  ext i; fin_cases i
  · simp only [cen, kiss, tang, pol, innerRad, Fin.zero_eta, Fin.isValue, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    simp only [Fin.isValue, Matrix.cons_val_zero]
    rw [show (2 * (k : ℝ) + 1) * ang = 2 * k * ang + ang by ring, cos_add]; ring
  · simp only [cen, kiss, tang, pol, innerRad, Fin.mk_one, Fin.isValue, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    simp only [Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    rw [show (2 * (k : ℝ) + 1) * ang = 2 * k * ang + ang by ring, sin_add]; ring

theorem cen_sub_one_eq_kiss_sub (k : ℤ) : cen (k - 1) = kiss k - kissRad • tang k := by
  rw [← ringRad_mul_sin]
  ext i; fin_cases i
  · simp only [cen, kiss, tang, pol, innerRad, Fin.zero_eta, Fin.isValue, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    simp only [Fin.isValue, Matrix.cons_val_zero]
    rw [show (2 * ((k - 1 : ℤ) : ℝ) + 1) * ang = 2 * k * ang - ang by push_cast; ring, cos_sub]
    ring
  · simp only [cen, kiss, tang, pol, innerRad, Fin.mk_one, Fin.isValue, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    simp only [Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    rw [show (2 * ((k - 1 : ℤ) : ℝ) + 1) * ang = 2 * k * ang - ang by push_cast; ring, sin_sub]
    ring

theorem norm_tang (k : ℤ) : ‖tang k‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, norm_sq_eq]
  simp only [tang]
  simp only [Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination sin_sq_add_cos_sq (2 * k * ang)

theorem norm_kiss_sub_cen (k : ℤ) : ‖kiss k - cen k‖ = kissRad := by
  rw [cen_eq_kiss_add, sub_add_cancel_left, norm_neg, norm_smul, norm_tang, mul_one,
    Real.norm_of_nonneg (by norm_num [kissRad])]

theorem norm_kiss_sub_cen_sub_one (k : ℤ) : ‖kiss k - cen (k - 1)‖ = kissRad := by
  rw [cen_sub_one_eq_kiss_sub, sub_sub_cancel, norm_smul, norm_tang, mul_one,
    Real.norm_of_nonneg (by norm_num [kissRad])]

theorem norm_kiss (k : ℤ) : ‖kiss k‖ = innerRad := norm_pol innerRad_pos.le _

/-! ### Rays from the origin -/

theorem holeRad_lt_ringRad : holeRad < ringRad := by
  unfold holeRad; linarith [ringRad_bounds.1]

/-- The radial projection onto the circle of centres moves a point of the `k`-th hole to within
`√0.0026` of `z_k`. -/
theorem norm_proj_sub_cen_sq_lt {y : E 2} {k : ℤ} (hy : ‖y - cen k‖ ≤ holeRad) :
    0 < ‖y‖ ∧ ‖(ringRad / ‖y‖) • y - cen k‖ ^ 2 < 0.0026 := by
  have hR := ringRad_bounds
  have hz := norm_cen k
  have hs : ringRad - holeRad ≤ ‖y‖ := by
    have := norm_sub_norm_le (cen k) y
    rw [norm_sub_rev] at this; linarith
  have hr : holeRad = 1 / 20 := rfl
  set s := ‖y‖ with hsdef
  have hs0 : 0 < s := by rw [hr] at hs; linarith
  refine ⟨hs0, ?_⟩
  set I := ⟪y, cen k⟫ with hIdef
  have hI : s ^ 2 - 2 * I + ringRad ^ 2 ≤ holeRad ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hy 2
    rw [norm_sub_sq_real, hz] at h; exact h
  have hL : ‖(ringRad / s) • y - cen k‖ ^ 2 * s = 2 * ringRad ^ 2 * s - 2 * ringRad * I := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, hz,
      Real.norm_of_nonneg (div_nonneg ringRad_pos.le hs0.le)]
    field_simp
    ring
  have key : ‖(ringRad / s) • y - cen k‖ ^ 2 * s ≤ ringRad * holeRad ^ 2 := by
    rw [hL]; nlinarith [sq_nonneg (s - ringRad)]
  have : ringRad * holeRad ^ 2 < 0.0026 * s := by rw [hr] at hs ⊢; nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith

/-- A ray from the origin meets at most one hole. -/
theorem dvd_of_mem_hole_of_mem_hole {y : E 2} {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {j k : ℤ}
    (hj : ‖s • y - cen j‖ ≤ holeRad) (hk : ‖t • y - cen k‖ ≤ holeRad) :
    (numHoles : ℤ) ∣ j - k := by
  obtain ⟨hy1, h1⟩ := norm_proj_sub_cen_sq_lt hj
  obtain ⟨hy2, h2⟩ := norm_proj_sub_cen_sq_lt hk
  have hy : 0 < ‖y‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs.le] at hy1; exact pos_of_mul_pos_right hy1 hs.le
  have proj : ∀ {u : ℝ}, 0 < u → (ringRad / ‖u • y‖) • (u • y) = (ringRad / ‖y‖) • y := by
    intro u hu
    rw [smul_smul, norm_smul, Real.norm_of_nonneg hu.le]
    congr 1; field_simp
  rw [proj hs] at h1
  rw [proj ht] at h2
  by_contra hd
  have h := two_kissRad_le_norm_cen_sub_cen hd
  have htri : ‖cen j - cen k‖ ≤ ‖(ringRad / ‖y‖) • y - cen j‖ + ‖(ringRad / ‖y‖) • y - cen k‖ := by
    calc _ = ‖((ringRad / ‖y‖) • y - cen k) - ((ringRad / ‖y‖) • y - cen j)‖ := by
            congr 1; abel
      _ ≤ _ := by rw [add_comm]; exact norm_sub_le _ _
  unfold kissRad at h
  have hsq := mul_self_le_mul_self (by norm_num) (h.trans htri)
  nlinarith [sq_nonneg (‖(ringRad / ‖y‖) • y - cen j‖ - ‖(ringRad / ‖y‖) • y - cen k‖)]

/-- The ray through `e₁` (the direction of the kissing point `m_0`) misses all holes. -/
theorem holeRad_lt_norm_pol_zero_sub_cen {t : ℝ} (ht : 0 < t) (k : ℤ) :
    holeRad < ‖pol t 0 - cen k‖ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, h⟩ := norm_proj_sub_cen_sq_lt hcon
  have hp : (ringRad / ‖pol t 0‖) • pol t 0 = pol ringRad 0 := by
    rw [norm_pol ht.le]
    ext i; fin_cases i
    · simp [pol]; field_simp
    · simp [pol]
  rw [hp, cen, norm_pol_sub_pol_sq_same] at h
  have hs := sin_sq_le_sin_sq_of_not_dvd 200 (by norm_num) (-(2 * k + 1)) (by omega)
  have e : (0 - (2 * (k : ℝ) + 1) * ang) / 2 = ((-(2 * k + 1) : ℤ) : ℝ) * π / (200 : ℕ) := by
    unfold ang numHoles; push_cast; ring
  rw [e] at h
  have hsin : 0.0156 < Real.sin (π / (200 : ℕ)) := by
    have hp0 : 0 < π / (200 : ℕ) := by positivity
    have := sin_gt_sub_cube hp0
    have h1 := pi_gt_d2; have h2 := pi_lt_d2
    have hb : π / (200 : ℕ) < 0.0158 := by rw [div_lt_iff₀ (by norm_num)]; push_cast; linarith
    have hb' : 0.0157 < π / (200 : ℕ) := by rw [lt_div_iff₀ (by norm_num)]; push_cast; linarith
    have h3 : (π / (200 : ℕ)) ^ 3 ≤ 0.0158 ^ 3 := pow_le_pow_left₀ hp0.le hb.le 3
    linarith
  have hsin2 : (0.0156 : ℝ) ^ 2 < Real.sin (π / (200 : ℕ)) ^ 2 :=
    pow_lt_pow_left₀ hsin (by norm_num) two_ne_zero
  have hR := ringRad_bounds
  nlinarith

/-! ### The inscribed circle -/

/-- Every point of the plane is `pol |x| φ` for some angle `φ`. -/
theorem exists_eq_pol (x : E 2) : ∃ φ : ℝ, x = pol ‖x‖ φ := by
  set w : ℂ := ⟨x 0, x 1⟩
  have hw : ‖w‖ = ‖x‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.normSq_mk,
      norm_sq_eq]
    ring
  refine ⟨Complex.arg w, ?_⟩
  ext i; fin_cases i
  · simp only [pol, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero]
    rw [← hw, Complex.norm_mul_cos_arg]
  · simp only [pol, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← hw, Complex.norm_mul_sin_arg]

/-- **The inscribed circle is covered by the closed discs `B̄_a(z_k)`**, and it meets the circles
`∂B_a(z_k)` only at kissing points: every `x` with `|x| = ρ_in` is a kissing point or lies in an
open disc `B_a(z_k)`. -/
theorem exists_norm_sub_cen_lt_or_eq_kiss {x : E 2} (hx : ‖x‖ = innerRad) :
    ∃ k : ℤ, ‖x - cen k‖ < kissRad ∨ x = kiss k := by
  obtain ⟨φ, hφ⟩ := exists_eq_pol x
  rw [hx] at hφ
  have ha := ang_pos
  set k : ℤ := ⌊φ / (2 * ang)⌋ with hk
  have h1 : (k : ℝ) ≤ φ / (2 * ang) := Int.floor_le _
  have h2 : φ / (2 * ang) < k + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ (by positivity)] at h1
  rw [div_lt_iff₀ (by positivity)] at h2
  refine ⟨k, ?_⟩
  rcases eq_or_lt_of_le h1 with he | hlt
  · right; rw [hφ, kiss, ← he]; ring_nf
  left
  set δ := φ - (2 * k + 1) * ang with hδ
  have hδ1 : |δ| < ang := by rw [abs_lt]; constructor <;> linarith
  have hcos : Real.cos ang < Real.cos δ := by
    rw [← cos_abs δ]
    exact cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [ang_bounds.2, pi_gt_d2])
      hδ1
  have hsq : ‖x - cen k‖ ^ 2 < kissRad ^ 2 := by
    rw [hφ, cen, norm_pol_sub_pol_sq, ← hδ, ← ringRad_mul_sin, innerRad]
    have hR := ringRad_pos
    have hc := cos_ang_bounds.1
    have := sin_sq_add_cos_sq ang
    nlinarith [mul_pos (mul_pos hR hR) (by linarith : (0 : ℝ) < Real.cos ang)]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by norm_num [kissRad]) two_ne_zero).1 hsq

end PerronVariational.Necklace

end
