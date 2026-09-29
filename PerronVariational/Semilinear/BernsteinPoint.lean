/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.MeanInequalities

/-!
# The Bernstein inequality at a maximum point (Step 3, algebraic part)

Step 3 of the joint proof of Propositions A.5 and A.6 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.4),
inequality (A.10).

At a positive maximum `(x̂, t̂)` of `z = η² w`, `w = |∇v|²`, relative to the parabolic past, the
derivative tests (`∂ₜz ≥ 0`, `∇z = 0`, `Δz ≤ 0`) and the equation (A.8) for `w` give

  `|ℓ'| η² w ≤ C_η + 2 η² (|k_v| + |∇ₓk|)`   when `w ≥ 1`,

with `C_η = 16|∇η|² + 2|∂ₜη| + 2|Δη|`. This file contains the purely algebraic deduction, with all
derivatives at the point replaced by real numbers.

Compared with the paper we use the first-order test `∇z = 0` also in the cross term
`-2∇η²·∇w = 8w|∇η|²`, so that the Hessian term `-2|D²v|²` of (A.8) is simply dropped and no
Young inequality with `|D²v|` is needed.
-/

open Finset

@[expose] public section

namespace PerronVariational

/-- **The Bernstein inequality at a maximum point** (algebraic core of (A.10)).
Notation (all at the maximum point): `G i = ∂ᵢv`, `W = ∑ Gᵢ²` (`= w`), `h i = ∂ᵢη`,
`ηxx i = ∂ᵢ²η`, `ηt = ∂ₜη`, `wx i = ∂ᵢw`, `wxx i = ∂ᵢ²w`, `wt = ∂ₜw`, `ℓ = ℓ(v)`, `a = -ℓ'(v)`,
`kv = ∂ᵥk`, `kx i = ∂ᵢk`. Hypotheses: (A.8) with the Hessian term dropped (`hB`), the
first-order spatial test for `z` (`hC`), the second-order spatial test (`hD`), the time test
(`hE`), and (e) `ℓ² ≤ 2|ℓ'|`. -/
theorem bernstein_point_algebra {ι : Type*} [Fintype ι] (G h ηxx wx wxx kx : ι → ℝ)
    {η ηt wt ℓ a kv Kx : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (ha : 0 < a) (hℓ : ℓ ^ 2 ≤ 2 * a)
    (hKx : 0 ≤ Kx) (hkx : ∑ i, kx i ^ 2 ≤ Kx ^ 2) (hW1 : 1 ≤ ∑ i, G i ^ 2)
    (hB : wt - ∑ i, wxx i - 2 * ℓ * ∑ i, G i * wx i ≤
      -2 * a * (∑ i, G i ^ 2) ^ 2 - 2 * ∑ i, G i * kx i - 2 * kv * ∑ i, G i ^ 2)
    (hC : ∀ i, 2 * η * h i * (∑ j, G j ^ 2) + η ^ 2 * wx i = 0)
    (hD : ∑ i, ((2 * h i ^ 2 + 2 * η * ηxx i) * (∑ j, G j ^ 2) + 4 * η * h i * wx i +
      η ^ 2 * wxx i) ≤ 0)
    (hE : 0 ≤ 2 * η * ηt * (∑ j, G j ^ 2) + η ^ 2 * wt) :
    a * (η ^ 2 * ∑ i, G i ^ 2) ≤
      16 * ∑ i, h i ^ 2 + 2 * |ηt| + 2 * |∑ i, ηxx i| + 2 * η ^ 2 * (|kv| + Kx) := by
  set W := ∑ i, G i ^ 2 with hW
  set Hh := ∑ i, h i ^ 2 with hHh
  set Y := ∑ i, G i * h i with hY
  set Z := ∑ i, G i * kx i with hZ
  set S := ∑ i, ηxx i with hS
  have hW0 : 0 < W := by linarith
  have hHh0 : 0 ≤ Hh := sum_nonneg fun i _ ↦ sq_nonneg _
  -- `η ∂ᵢw = -2 W ∂ᵢη`
  have hwx : ∀ i, η * wx i = -2 * W * h i := fun i ↦ by
    have := hC i
    have h2 : η * (2 * W * h i + η * wx i) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · linarith
  have hGwx : η * ∑ i, G i * wx i = -2 * W * Y := by
    rw [mul_sum, hY, mul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [← mul_assoc, mul_comm η, mul_assoc, hwx i]; ring
  have hhwx : η * ∑ i, h i * wx i = -2 * W * Hh := by
    rw [mul_sum, hHh, mul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [← mul_assoc, mul_comm η, mul_assoc, hwx i]; ring
  -- the second-order test, rewritten
  have hD' : (2 * Hh + 2 * η * S) * W - 8 * W * Hh + η ^ 2 * ∑ i, wxx i ≤ 0 := by
    have e1 : ∑ i, (2 * h i ^ 2 + 2 * η * ηxx i) * W = (2 * Hh + 2 * η * S) * W := by
      rw [← sum_mul, sum_add_distrib, ← mul_sum, ← mul_sum]
    have e2 : ∑ i, 4 * η * h i * wx i = 4 * (η * ∑ i, h i * wx i) := by
      rw [mul_sum, mul_sum]; exact sum_congr rfl fun i _ ↦ by ring
    have e3 : ∑ i, η ^ 2 * wxx i = η ^ 2 * ∑ i, wxx i := by rw [mul_sum]
    rw [sum_add_distrib, sum_add_distrib, e1, e2, e3, hhwx] at hD
    linarith
  -- Cauchy–Schwarz
  have hY2 : Y ^ 2 ≤ W * Hh := sum_mul_sq_le_sq_mul_sq _ _ _
  have hZ2 : Z ^ 2 ≤ W * Kx ^ 2 := (sum_mul_sq_le_sq_mul_sq _ _ _).trans
    (mul_le_mul_of_nonneg_left hkx hW0.le)
  have hZ : -Z ≤ W * Kx := by
    have h1 : Z ^ 2 ≤ (W * Kx) ^ 2 := by
      have : W * Kx ^ 2 ≤ W ^ 2 * Kx ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      linarith
    linarith [(abs_le_of_sq_le_sq' h1 (by positivity)).1]
  -- Young: `-4 ℓ η W Y ≤ a η² W² + 8 W |∇η|²`
  have hYoung : -4 * ℓ * η * W * Y ≤ a * η ^ 2 * W ^ 2 + 8 * W * Hh := by
    have h1 : a * (-4 * ℓ * η * W * Y) ≤ a * (a * η ^ 2 * W ^ 2 + 8 * Y ^ 2) := by
      linarith [sq_nonneg (a * η * W + 2 * ℓ * Y), mul_le_mul_of_nonneg_right hℓ (sq_nonneg Y)]
    have h2 := le_of_mul_le_mul_left h1 ha
    linarith
  -- combine
  have hB' : η ^ 2 * wt - η ^ 2 * ∑ i, wxx i - 2 * ℓ * η * (η * ∑ i, G i * wx i) ≤
      η ^ 2 * (-2 * a * W ^ 2 - 2 * Z - 2 * kv * W) := by
    have := mul_le_mul_of_nonneg_left hB (sq_nonneg η)
    linarith
  rw [hGwx] at hB'
  have hkv : -kv * W ≤ |kv| * W := mul_le_mul_of_nonneg_right (neg_le_abs kv) hW0.le
  have hηt : η * ηt * W ≤ |ηt| * W := by
    refine mul_le_mul_of_nonneg_right ?_ hW0.le
    calc η * ηt ≤ |η * ηt| := le_abs_self _
      _ = η * |ηt| := by rw [abs_mul, abs_of_pos hη]
      _ ≤ |ηt| := mul_le_of_le_one_left (abs_nonneg _) hη1
  have hSb : -(η * S) * W ≤ |S| * W := by
    refine mul_le_mul_of_nonneg_right ?_ hW0.le
    calc -(η * S) ≤ |η * S| := neg_le_abs _
      _ = η * |S| := by rw [abs_mul, abs_of_pos hη]
      _ ≤ |S| := mul_le_of_le_one_left (abs_nonneg _) hη1
  have hmain : a * η ^ 2 * W ^ 2 ≤
      W * (2 * η ^ 2 * Kx + 2 * η ^ 2 * |kv| + 2 * |ηt| + 2 * |S| + 14 * Hh) := by
    have h1 := mul_le_mul_of_nonneg_left hZ (sq_nonneg η)
    have h2 := mul_le_mul_of_nonneg_left hkv (sq_nonneg η)
    linarith
  have hfin : a * (η ^ 2 * W) ≤
      2 * η ^ 2 * Kx + 2 * η ^ 2 * |kv| + 2 * |ηt| + 2 * |S| + 14 * Hh := by
    have e : a * η ^ 2 * W ^ 2 = W * (a * (η ^ 2 * W)) := by ring
    rw [e] at hmain
    exact le_of_mul_le_mul_left hmain hW0
  linarith

end PerronVariational

end
