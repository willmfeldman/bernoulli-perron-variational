/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A `C²` ramp, and floor-and-cap profiles

A tool for the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`).

* `ramp u` is `0` for `u ≤ 0`, `u³ - u⁴/2` on `[0, 1]` and `u - 1/2` for `u ≥ 1`. It is `C²`
  and convex, with `ramp' ∈ [0, 1]`.
* `floorCap tf Lf tc Lc t = t + Lf ramp ((tf - t)/Lf) - Lc ramp ((t - tc)/Lc)` is the identity on
  `[tf, tc]`, constant `tf - Lf/2` below `tf - Lf`, constant `tc + Lc/2` above `tc + Lc`, and
  concave on `[tf, ∞)`.
-/

open Set Filter Topology

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

/-! ### The ramp -/

/-- The `C²` ramp: `0` for `u ≤ 0`, `u³ - u⁴/2` on `[0, 1]`, `u - 1/2` for `u ≥ 1`. -/
def ramp (u : ℝ) : ℝ := if u ≤ 0 then 0 else if u ≤ 1 then u ^ 3 - u ^ 4 / 2 else u - 1 / 2

/-- The derivative of `ramp`. -/
def rampD (u : ℝ) : ℝ := if u ≤ 0 then 0 else if u ≤ 1 then 3 * u ^ 2 - 2 * u ^ 3 else 1

/-- The second derivative of `ramp`: `6 u (1 - u)` on `[0, 1]` and `0` elsewhere. -/
def rampDD (u : ℝ) : ℝ := 6 * max (u * (1 - u)) 0

theorem ramp_of_nonpos {u : ℝ} (hu : u ≤ 0) : ramp u = 0 := by simp [ramp, hu]

theorem ramp_of_mem_Icc {u : ℝ} (hu : u ∈ Icc 0 1) : ramp u = u ^ 3 - u ^ 4 / 2 := by
  rcases eq_or_lt_of_le hu.1 with h | h
  · subst h; simp [ramp]
  · simp [ramp, not_le.2 h, hu.2]

theorem ramp_of_one_le {u : ℝ} (hu : 1 ≤ u) : ramp u = u - 1 / 2 := by
  rcases eq_or_lt_of_le hu with h | h
  · subst h; norm_num [ramp]
  · simp [ramp, not_le.2 (zero_lt_one.trans h), not_le.2 h]

theorem rampD_of_nonpos {u : ℝ} (hu : u ≤ 0) : rampD u = 0 := by simp [rampD, hu]

theorem rampD_of_mem_Icc {u : ℝ} (hu : u ∈ Icc 0 1) : rampD u = 3 * u ^ 2 - 2 * u ^ 3 := by
  rcases eq_or_lt_of_le hu.1 with h | h
  · subst h; simp [rampD]
  · simp [rampD, not_le.2 h, hu.2]

theorem rampD_of_one_le {u : ℝ} (hu : 1 ≤ u) : rampD u = 1 := by
  rcases eq_or_lt_of_le hu with h | h
  · subst h; norm_num [rampD]
  · simp [rampD, not_le.2 (zero_lt_one.trans h), not_le.2 h]

theorem rampDD_of_nonpos {u : ℝ} (hu : u ≤ 0) : rampDD u = 0 := by
  have : u * (1 - u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu (by linarith)
  simp [rampDD, max_eq_right this]

theorem rampDD_of_mem_Icc {u : ℝ} (hu : u ∈ Icc 0 1) : rampDD u = 6 * u - 6 * u ^ 2 := by
  have : 0 ≤ u * (1 - u) := mul_nonneg hu.1 (by linarith [hu.2])
  rw [rampDD, max_eq_left this]; ring

theorem rampDD_of_one_le {u : ℝ} (hu : 1 ≤ u) : rampDD u = 0 := by
  have : u * (1 - u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  simp [rampDD, max_eq_right this]

theorem continuous_rampDD : Continuous rampDD := by unfold rampDD; fun_prop

theorem rampDD_nonneg (u : ℝ) : 0 ≤ rampDD u := by unfold rampDD; positivity

/-- Gluing one-sided derivatives at a point. -/
theorem hasDerivAt_of_Iic_Ici {f g h : ℝ → ℝ} {x₀ D : ℝ} (hg : HasDerivAt g D x₀)
    (hh : HasDerivAt h D x₀) (hfg : ∀ᶠ x in 𝓝[≤] x₀, f x = g x)
    (hfh : ∀ᶠ x in 𝓝[≥] x₀, f x = h x) (hg₀ : f x₀ = g x₀) (hh₀ : f x₀ = h x₀) :
    HasDerivAt f D x₀ := by
  have h1 : HasDerivWithinAt f D (Iic x₀) x₀ := hg.hasDerivWithinAt.congr_of_eventuallyEq hfg hg₀
  have h2 : HasDerivWithinAt f D (Ici x₀) x₀ := hh.hasDerivWithinAt.congr_of_eventuallyEq hfh hh₀
  have := h1.union h2
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- A three-piece function with breakpoints `0` and `1` has derivative `D` wherever its pieces
do, provided the pieces' derivatives agree at the breakpoints. -/
theorem hasDerivAt_three_pieces {f f₁ f₂ f₃ : ℝ → ℝ} {D D₁ D₂ D₃ : ℝ → ℝ}
    (h₁ : ∀ u ≤ 0, f u = f₁ u) (h₂ : ∀ u ∈ Icc (0 : ℝ) 1, f u = f₂ u) (h₃ : ∀ u, 1 ≤ u → f u = f₃ u)
    (hD₁ : ∀ u ≤ 0, D u = D₁ u) (hD₂ : ∀ u ∈ Icc (0 : ℝ) 1, D u = D₂ u)
    (hD₃ : ∀ u, 1 ≤ u → D u = D₃ u)
    (d₁ : ∀ u, HasDerivAt f₁ (D₁ u) u) (d₂ : ∀ u, HasDerivAt f₂ (D₂ u) u)
    (d₃ : ∀ u, HasDerivAt f₃ (D₃ u) u) (u : ℝ) : HasDerivAt f (D u) u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · rw [hD₁ u hu.le]
    refine (d₁ u).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hu] with x hx using h₁ x (le_of_lt hx)
  · have e₁ : D 0 = D₁ 0 := hD₁ 0 le_rfl
    have e₂ : D 0 = D₂ 0 := hD₂ 0 ⟨le_rfl, zero_le_one⟩
    refine hasDerivAt_of_Iic_Ici (g := f₁) (h := f₂) (e₁ ▸ d₁ 0) (e₂ ▸ d₂ 0) ?_ ?_
      (h₁ 0 le_rfl) (h₂ 0 ⟨le_rfl, zero_le_one⟩)
    · filter_upwards [self_mem_nhdsWithin] with x hx using h₁ x hx
    · filter_upwards [Ico_mem_nhdsGE (zero_lt_one' ℝ)] with x hx using h₂ x ⟨hx.1, hx.2.le⟩
  · rcases lt_trichotomy u 1 with hu1 | rfl | hu1
    · rw [hD₂ u ⟨hu.le, hu1.le⟩]
      refine (d₂ u).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hu hu1] with x hx using h₂ x ⟨hx.1.le, hx.2.le⟩
    · have e₂ : D 1 = D₂ 1 := hD₂ 1 ⟨zero_le_one, le_rfl⟩
      have e₃ : D 1 = D₃ 1 := hD₃ 1 le_rfl
      refine hasDerivAt_of_Iic_Ici (g := f₂) (h := f₃) (e₂ ▸ d₂ 1) (e₃ ▸ d₃ 1) ?_ ?_
        (h₂ 1 ⟨zero_le_one, le_rfl⟩) (h₃ 1 le_rfl)
      · filter_upwards [Ioc_mem_nhdsLE (zero_lt_one' ℝ)] with x hx using h₂ x ⟨hx.1.le, hx.2⟩
      · filter_upwards [self_mem_nhdsWithin] with x hx using h₃ x hx
    · rw [hD₃ u hu1.le]
      refine (d₃ u).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hu1] with x hx using h₃ x (le_of_lt hx)

theorem hasDerivAt_ramp (u : ℝ) : HasDerivAt ramp (rampD u) u := by
  refine hasDerivAt_three_pieces (f₁ := fun _ ↦ 0) (f₂ := fun u ↦ u ^ 3 - u ^ 4 / 2)
    (f₃ := fun u ↦ u - 1 / 2) (D₁ := fun _ ↦ 0) (D₂ := fun u ↦ 3 * u ^ 2 - 2 * u ^ 3)
    (D₃ := fun _ ↦ 1) (fun u hu ↦ ramp_of_nonpos hu) (fun u hu ↦ ramp_of_mem_Icc hu)
    (fun u hu ↦ ramp_of_one_le hu) (fun u hu ↦ rampD_of_nonpos hu)
    (fun u hu ↦ rampD_of_mem_Icc hu) (fun u hu ↦ rampD_of_one_le hu)
    (fun u ↦ hasDerivAt_const u 0) (fun u ↦ ?_) (fun u ↦ ?_) u
  · convert ((hasDerivAt_pow 3 u).sub ((hasDerivAt_pow 4 u).div_const 2)) using 1
    push_cast; ring
  · simpa using (hasDerivAt_id u).sub_const (1 / 2 : ℝ)

theorem hasDerivAt_rampD (u : ℝ) : HasDerivAt rampD (rampDD u) u := by
  refine hasDerivAt_three_pieces (f₁ := fun _ ↦ 0) (f₂ := fun u ↦ 3 * u ^ 2 - 2 * u ^ 3)
    (f₃ := fun _ ↦ 1) (D₁ := fun _ ↦ 0) (D₂ := fun u ↦ 6 * u - 6 * u ^ 2)
    (D₃ := fun _ ↦ 0) (fun u hu ↦ rampD_of_nonpos hu) (fun u hu ↦ rampD_of_mem_Icc hu)
    (fun u hu ↦ rampD_of_one_le hu) (fun u hu ↦ rampDD_of_nonpos hu)
    (fun u hu ↦ rampDD_of_mem_Icc hu) (fun u hu ↦ rampDD_of_one_le hu)
    (fun u ↦ hasDerivAt_const u 0) (fun u ↦ ?_) (fun u ↦ hasDerivAt_const u 1) u
  convert (((hasDerivAt_pow 2 u).const_mul 3).sub ((hasDerivAt_pow 3 u).const_mul 2)) using 1
  push_cast; ring

theorem deriv_ramp : deriv ramp = rampD := funext fun u ↦ (hasDerivAt_ramp u).deriv

theorem deriv_rampD : deriv rampD = rampDD := funext fun u ↦ (hasDerivAt_rampD u).deriv

theorem contDiff_ramp : ContDiff ℝ 2 ramp := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv, deriv_ramp,
    contDiff_one_iff_deriv, deriv_rampD]
  exact ⟨fun u ↦ (hasDerivAt_ramp u).differentiableAt, by simp,
    fun u ↦ (hasDerivAt_rampD u).differentiableAt, continuous_rampDD⟩

theorem rampD_nonneg (u : ℝ) : 0 ≤ rampD u := by
  rcases le_or_gt u 0 with h | h
  · rw [rampD_of_nonpos h]
  rcases le_or_gt u 1 with h1 | h1
  · rw [rampD_of_mem_Icc ⟨h.le, h1⟩]; nlinarith [sq_nonneg u]
  · rw [rampD_of_one_le h1.le]; norm_num

theorem rampD_le_one (u : ℝ) : rampD u ≤ 1 := by
  rcases le_or_gt u 0 with h | h
  · rw [rampD_of_nonpos h]; norm_num
  rcases le_or_gt u 1 with h1 | h1
  · rw [rampD_of_mem_Icc ⟨h.le, h1⟩]
    nlinarith [sq_nonneg (u - 1), mul_nonneg h.le (sq_nonneg (u - 1))]
  · rw [rampD_of_one_le h1.le]

theorem ramp_nonneg (u : ℝ) : 0 ≤ ramp u := by
  rcases le_or_gt u 0 with h | h
  · rw [ramp_of_nonpos h]
  rcases le_or_gt u 1 with h1 | h1
  · rw [ramp_of_mem_Icc ⟨h.le, h1⟩]
    have : u ^ 4 ≤ u ^ 3 := by
      have := pow_le_pow_of_le_one h.le h1 (show 3 ≤ 4 by norm_num); linarith
    nlinarith [pow_pos h 3]
  · rw [ramp_of_one_le h1.le]; linarith

theorem ramp_le_self {u : ℝ} (hu : 0 ≤ u) : ramp u ≤ u := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h, ramp_of_nonpos le_rfl]
  rcases le_or_gt u 1 with h1 | h1
  · rw [ramp_of_mem_Icc ⟨h.le, h1⟩]
    have : u ^ 3 ≤ u := by
      have := pow_le_pow_of_le_one h.le h1 (show 1 ≤ 3 by norm_num); simpa using this
    nlinarith [pow_pos h 4]
  · rw [ramp_of_one_le h1.le]; linarith

/-! ### Floor-and-cap profiles -/

/-- The floor-and-cap profile `t + Lf ramp ((tf - t)/Lf) - Lc ramp ((t - tc)/Lc)`. -/
def floorCap (tf Lf tc Lc t : ℝ) : ℝ :=
  t + Lf * ramp ((tf - t) / Lf) - Lc * ramp ((t - tc) / Lc)

/-- The derivative of `floorCap`. -/
def floorCapD (tf Lf tc Lc t : ℝ) : ℝ :=
  1 - rampD ((tf - t) / Lf) - rampD ((t - tc) / Lc)

/-- The second derivative of `floorCap`. -/
def floorCapDD (tf Lf tc Lc t : ℝ) : ℝ :=
  rampDD ((tf - t) / Lf) / Lf - rampDD ((t - tc) / Lc) / Lc

variable {tf Lf tc Lc : ℝ}

theorem hasDerivAt_floorCap (hLf : Lf ≠ 0) (hLc : Lc ≠ 0) (t : ℝ) :
    HasDerivAt (floorCap tf Lf tc Lc) (floorCapD tf Lf tc Lc t) t := by
  have h1 : HasDerivAt (fun t ↦ (tf - t) / Lf) (-1 / Lf) t := by
    simpa using ((hasDerivAt_id t).const_sub tf).div_const Lf
  have h2 : HasDerivAt (fun t ↦ (t - tc) / Lc) (1 / Lc) t := by
    simpa using ((hasDerivAt_id t).sub_const tc).div_const Lc
  have := ((hasDerivAt_id t).add (((hasDerivAt_ramp _).comp t h1).const_mul Lf)).sub
    (((hasDerivAt_ramp _).comp t h2).const_mul Lc)
  convert this using 1
  · rfl
  simp only [floorCapD]
  field_simp
  ring

theorem hasDerivAt_floorCapD (hLf : Lf ≠ 0) (hLc : Lc ≠ 0) (t : ℝ) :
    HasDerivAt (floorCapD tf Lf tc Lc) (floorCapDD tf Lf tc Lc t) t := by
  have h1 : HasDerivAt (fun t ↦ (tf - t) / Lf) (-1 / Lf) t := by
    simpa using ((hasDerivAt_id t).const_sub tf).div_const Lf
  have h2 : HasDerivAt (fun t ↦ (t - tc) / Lc) (1 / Lc) t := by
    simpa using ((hasDerivAt_id t).sub_const tc).div_const Lc
  have := ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_rampD _).comp t h1)).sub
    ((hasDerivAt_rampD _).comp t h2)
  convert this using 1
  · rfl
  simp only [floorCapDD]
  field_simp
  ring

theorem deriv_floorCap (hLf : Lf ≠ 0) (hLc : Lc ≠ 0) :
    deriv (floorCap tf Lf tc Lc) = floorCapD tf Lf tc Lc :=
  funext fun t ↦ (hasDerivAt_floorCap hLf hLc t).deriv

theorem deriv_floorCapD (hLf : Lf ≠ 0) (hLc : Lc ≠ 0) :
    deriv (floorCapD tf Lf tc Lc) = floorCapDD tf Lf tc Lc :=
  funext fun t ↦ (hasDerivAt_floorCapD hLf hLc t).deriv

theorem contDiff_floorCap : ContDiff ℝ 2 (floorCap tf Lf tc Lc) := by
  unfold floorCap
  have hr := contDiff_ramp
  fun_prop

theorem floorCap_of_mem_Icc (hLf : 0 < Lf) (hLc : 0 < Lc) {t : ℝ} (ht : t ∈ Icc tf tc) :
    floorCap tf Lf tc Lc t = t := by
  rw [floorCap, ramp_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) hLf.le),
    ramp_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) hLc.le)]
  ring

theorem floorCap_of_le_floor (hLf : 0 < Lf) (hLc : 0 < Lc) (htfc : tf ≤ tc) {t : ℝ}
    (ht : t ≤ tf - Lf) : floorCap tf Lf tc Lc t = tf - Lf / 2 := by
  rw [floorCap, ramp_of_one_le (by rw [le_div_iff₀ hLf]; linarith),
    ramp_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hLc.le)]
  field_simp
  ring

theorem floorCap_of_cap_le (hLf : 0 < Lf) (hLc : 0 < Lc) (htfc : tf ≤ tc) {t : ℝ}
    (ht : tc + Lc ≤ t) : floorCap tf Lf tc Lc t = tc + Lc / 2 := by
  rw [floorCap, ramp_of_one_le (u := (t - tc) / Lc) (by rw [le_div_iff₀ hLc]; linarith),
    ramp_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hLf.le)]
  field_simp
  ring

theorem floorCap_le_floor (hLf : 0 < Lf) (hLc : 0 < Lc) (htfc : tf ≤ tc) {t : ℝ}
    (ht : t ≤ tf) : floorCap tf Lf tc Lc t ≤ tf := by
  rw [floorCap, ramp_of_nonpos (u := (t - tc) / Lc)
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hLc.le)]
  have h := ramp_le_self (u := (tf - t) / Lf) (div_nonneg (by linarith) hLf.le)
  have : Lf * ramp ((tf - t) / Lf) ≤ tf - t := by
    calc _ ≤ Lf * ((tf - t) / Lf) := mul_le_mul_of_nonneg_left h hLf.le
      _ = tf - t := by field_simp
  linarith

theorem floorCapD_of_mem_Icc (hLf : 0 < Lf) (hLc : 0 < Lc) {t : ℝ} (ht : t ∈ Icc tf tc) :
    floorCapD tf Lf tc Lc t = 1 := by
  rw [floorCapD, rampD_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) hLf.le),
    rampD_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) hLc.le)]
  ring

theorem floorCapDD_of_mem_Icc (hLf : 0 < Lf) (hLc : 0 < Lc) {t : ℝ} (ht : t ∈ Icc tf tc) :
    floorCapDD tf Lf tc Lc t = 0 := by
  rw [floorCapDD, rampDD_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) hLf.le),
    rampDD_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) hLc.le)]
  ring

/-- `floorCap` is concave above the floor. -/
theorem floorCapDD_nonpos (hLf : 0 < Lf) (hLc : 0 < Lc) {t : ℝ} (ht : tf ≤ t) :
    floorCapDD tf Lf tc Lc t ≤ 0 := by
  rw [floorCapDD, rampDD_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hLf.le)]
  have := div_nonneg (rampDD_nonneg ((t - tc) / Lc)) hLc.le
  rw [zero_div]
  linarith

/-- On the floor, `floorCapD` vanishes. -/
theorem floorCapD_of_le_floor (hLf : 0 < Lf) (hLc : 0 < Lc) (htfc : tf ≤ tc) {t : ℝ}
    (ht : t ≤ tf - Lf) : floorCapD tf Lf tc Lc t = 0 := by
  rw [floorCapD, rampD_of_one_le (by rw [le_div_iff₀ hLf]; linarith),
    rampD_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hLc.le)]
  ring

end PerronVariational.TwoDisc

end
