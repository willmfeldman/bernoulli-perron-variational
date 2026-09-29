/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.TwoDisc.LogRadial

/-!
# Floor-and-cap profiles of logarithms of the distance

A tool for the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`).

The data of the example are sums of pieces `logRad (floorCap tf lf tc lc) z α k δ`. This file
records, for one piece at a point `x` with argument `t = α log |x - z|² + k`:
* on the floor (`t ≤ tf - lf`), the piece is the constant `tf - lf/2` with zero gradient and
  Laplacian;
* in the middle (`t ∈ [tf, tc]`), it is `t`, with `|∇| = 2|α|/|x - z|`;
* it is superharmonic where `t ≥ tf` and subharmonic where `t ≤ tc`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped Gradient Laplacian

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

variable {tf lf tc lc : ℝ}

theorem floorCapDD_of_le_floor (hlf : 0 < lf) (hlc : 0 < lc) (htfc : tf ≤ tc) {t : ℝ}
    (ht : t ≤ tf - lf) : floorCapDD tf lf tc lc t = 0 := by
  rw [floorCapDD, rampDD_of_one_le (by rw [le_div_iff₀ hlf]; linarith),
    rampDD_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hlc.le)]
  ring

/-- `floorCap` is convex below the cap. -/
theorem floorCapDD_nonneg (hlf : 0 < lf) (hlc : 0 < lc) {t : ℝ} (ht : t ≤ tc) :
    0 ≤ floorCapDD tf lf tc lc t := by
  rw [floorCapDD, rampDD_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hlc.le), zero_div,
    sub_zero]
  exact div_nonneg (rampDD_nonneg _) hlf.le

/-- Above the cap threshold, `floorCap ≥ tc`. -/
theorem cap_le_floorCap (hlc : 0 < lc) (hlf : 0 < lf) (htfc : tf ≤ tc) {t : ℝ} (ht : tc ≤ t) :
    tc ≤ floorCap tf lf tc lc t := by
  rw [floorCap, ramp_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hlf.le)]
  have h := ramp_le_self (u := (t - tc) / lc) (div_nonneg (by linarith) hlc.le)
  have : lc * ramp ((t - tc) / lc) ≤ t - tc := by
    calc _ ≤ lc * ((t - tc) / lc) := mul_le_mul_of_nonneg_left h hlc.le
      _ = t - tc := by field_simp
  linarith

variable {α k δ δ' : ℝ} {z x : E 2}

theorem logRad_apply (P : ℝ → ℝ) :
    logRad P z α k δ x = P (α * Real.log (max (‖x - z‖ ^ 2) δ) + k) := rfl

variable (hlf : 0 < lf) (hlc : 0 < lc) (htfc : tf ≤ tc) (hδ : 0 < δ) (hδδ' : δ < δ')
  (hc : ClampConst (floorCap tf lf tc lc) α k δ δ')
include hlf hlc hδ hδδ' hc

omit hlf hlc in
theorem contDiff_logRad_floorCap : ContDiff ℝ 2 (logRad (floorCap tf lf tc lc) z α k δ) :=
  contDiff_logRad contDiff_floorCap hδ hδδ' hc z

include htfc

omit hδ hδδ' hc in
/-- On the floor, a piece is the constant `tf - lf/2`. -/
theorem logRad_eq_floor (h : α * Real.log (max (‖x - z‖ ^ 2) δ) + k ≤ tf - lf) :
    logRad (floorCap tf lf tc lc) z α k δ x = tf - lf / 2 := by
  rw [logRad_apply, floorCap_of_le_floor hlf hlc htfc h]

/-- On the floor, a piece has zero gradient. -/
theorem hasGradientAt_logRad_floor (h : α * Real.log (max (‖x - z‖ ^ 2) δ) + k ≤ tf - lf) :
    HasGradientAt (logRad (floorCap tf lf tc lc) z α k δ) 0 x := by
  rcases lt_or_ge (‖x - z‖ ^ 2) δ' with h' | h'
  · exact hasGradientAt_logRad_of_lt_clamp contDiff_floorCap hδ hδδ' hc h'
  · have hτ : δ < ‖x - z‖ ^ 2 := hδδ'.trans_le h'
    rw [max_eq_left hτ.le] at h
    have := hasGradientAt_logRad contDiff_floorCap
      (hasDerivAt_floorCap hlf.ne' hlc.ne') hδ hδδ' hc hτ
    rwa [floorCapD_of_le_floor hlf hlc htfc h, zero_mul, mul_zero, zero_smul] at this

/-- On the floor, a piece has zero Laplacian. -/
theorem laplacian_logRad_floor (h : α * Real.log (max (‖x - z‖ ^ 2) δ) + k ≤ tf - lf) :
    Δ (logRad (floorCap tf lf tc lc) z α k δ) x = 0 := by
  rcases lt_or_ge (‖x - z‖ ^ 2) δ' with h' | h'
  · exact laplacian_logRad_of_lt_clamp contDiff_floorCap hδ hδδ' hc h'
  · have hτ : δ < ‖x - z‖ ^ 2 := hδδ'.trans_le h'
    rw [max_eq_left hτ.le] at h
    rw [laplacian_logRad contDiff_floorCap (hasDerivAt_floorCap hlf.ne' hlc.ne')
      (hasDerivAt_floorCapD hlf.ne' hlc.ne') hδ hδδ' hc hτ, floorCapDD_of_le_floor hlf hlc htfc h]
    simp

omit htfc hδ hδδ' hc in
/-- In the middle, a piece is its argument. -/
theorem logRad_eq_mid (hτ : δ ≤ ‖x - z‖ ^ 2)
    (h : α * Real.log (‖x - z‖ ^ 2) + k ∈ Icc tf tc) :
    logRad (floorCap tf lf tc lc) z α k δ x = α * Real.log (‖x - z‖ ^ 2) + k := by
  rw [logRad_apply, max_eq_left hτ, floorCap_of_mem_Icc hlf hlc h]

omit htfc in
/-- In the middle, `|∇ piece| = 2|α|/|x - z|`. -/
theorem norm_gradient_logRad_mid (hτ : δ < ‖x - z‖ ^ 2)
    (h : α * Real.log (‖x - z‖ ^ 2) + k ∈ Icc tf tc) :
    ‖∇ (logRad (floorCap tf lf tc lc) z α k δ) x‖ = 2 * |α| / ‖x - z‖ := by
  rw [norm_gradient_logRad contDiff_floorCap (hasDerivAt_floorCap hlf.ne' hlc.ne') hδ hδδ' hc hτ,
    floorCapD_of_mem_Icc hlf hlc h]
  simp

omit htfc in
/-- In the middle, a piece is harmonic. -/
theorem laplacian_logRad_mid (hτ : δ < ‖x - z‖ ^ 2)
    (h : α * Real.log (‖x - z‖ ^ 2) + k ∈ Icc tf tc) :
    Δ (logRad (floorCap tf lf tc lc) z α k δ) x = 0 := by
  rw [laplacian_logRad contDiff_floorCap (hasDerivAt_floorCap hlf.ne' hlc.ne')
    (hasDerivAt_floorCapD hlf.ne' hlc.ne') hδ hδδ' hc hτ, floorCapDD_of_mem_Icc hlf hlc h]
  simp

omit htfc in
/-- A piece is superharmonic where its argument is at least `tf`. -/
theorem laplacian_logRad_nonpos (hτ : δ < ‖x - z‖ ^ 2) (h : tf ≤ α * Real.log (‖x - z‖ ^ 2) + k) :
    Δ (logRad (floorCap tf lf tc lc) z α k δ) x ≤ 0 := by
  rw [laplacian_logRad contDiff_floorCap (hasDerivAt_floorCap hlf.ne' hlc.ne')
    (hasDerivAt_floorCapD hlf.ne' hlc.ne') hδ hδδ' hc hτ]
  have := floorCapDD_nonpos (tc := tc) (Lc := lc) hlf hlc h
  have hτ0 : 0 < ‖x - z‖ ^ 2 := hδ.trans hτ
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) this)
    hτ0.le

omit htfc in
/-- A piece is subharmonic where its argument is at most `tc`. -/
theorem laplacian_logRad_nonneg (hτ : δ < ‖x - z‖ ^ 2) (h : α * Real.log (‖x - z‖ ^ 2) + k ≤ tc) :
    0 ≤ Δ (logRad (floorCap tf lf tc lc) z α k δ) x := by
  rw [laplacian_logRad contDiff_floorCap (hasDerivAt_floorCap hlf.ne' hlc.ne')
    (hasDerivAt_floorCapD hlf.ne' hlc.ne') hδ hδδ' hc hτ]
  have := floorCapDD_nonneg (tf := tf) (lf := lf) hlf hlc h
  have hτ0 : 0 < ‖x - z‖ ^ 2 := hδ.trans hτ
  positivity

end PerronVariational.TwoDisc

end
