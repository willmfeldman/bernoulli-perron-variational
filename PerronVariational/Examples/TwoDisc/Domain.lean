/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Setting
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.PathConnected

/-!
# The two-disc domain

The domain of the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`):
`U = B₁(0) \ (B̄_{1/20}(p) ∪ B̄_{1/20}(-p))` in `ℝ²`, with `p = (1/10, 0)`.

* `U` is open, bounded and connected (`isConnected_domain`): every point either lies in one of
  four convex caps of `B₁(0)` that miss the holes, or moves vertically, away from the
  `x₁`-axis, into the upper or lower cap.
* `ρ(x) = (|x|² - 1)(1/400 - |x - p|²)(1/400 - |x + p|²)` is a `C²` defining function
  (`hasC2Boundary_domain`).
* `setting` packages `U` with `Q ≡ 1`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped Gradient RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

/-- The centre `p = (1/10, 0)` of the right hole. -/
def hole : E 2 := EuclideanSpace.single 0 (1 / 10)

/-- The two-disc domain `B₁(0) \ (B̄_{1/20}(p) ∪ B̄_{1/20}(-p))`. -/
def domain : Set (E 2) := ball 0 1 \ (closedBall hole (1 / 20) ∪ closedBall (-hole) (1 / 20))

/-! ### Coordinates -/

theorem norm_sq_eq (x : E 2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

@[simp] theorem hole_zero : hole 0 = 1 / 10 := by simp [hole]

@[simp] theorem hole_one : hole 1 = 0 := by simp [hole]

theorem norm_sub_hole_sq (x : E 2) : ‖x - hole‖ ^ 2 = (x 0 - 1 / 10) ^ 2 + x 1 ^ 2 := by
  rw [norm_sq_eq]; simp

theorem norm_add_hole_sq (x : E 2) : ‖x + hole‖ ^ 2 = (x 0 + 1 / 10) ^ 2 + x 1 ^ 2 := by
  rw [norm_sq_eq]; simp

theorem norm_hole : ‖hole‖ = 1 / 10 := by
  simp [hole]

theorem lt_norm_iff_sq {v : E 2} {r : ℝ} (hr : 0 ≤ r) : r < ‖v‖ ↔ r ^ 2 < ‖v‖ ^ 2 :=
  (sq_lt_sq₀ hr (norm_nonneg _)).symm

theorem norm_lt_iff_sq {v : E 2} {r : ℝ} (hr : 0 ≤ r) : ‖v‖ < r ↔ ‖v‖ ^ 2 < r ^ 2 :=
  (sq_lt_sq₀ (norm_nonneg _) hr).symm

/-- Membership in `U` in coordinates. -/
theorem mem_domain_iff (x : E 2) :
    x ∈ domain ↔ x 0 ^ 2 + x 1 ^ 2 < 1 ∧ 1 / 400 < (x 0 - 1 / 10) ^ 2 + x 1 ^ 2 ∧
      1 / 400 < (x 0 + 1 / 10) ^ 2 + x 1 ^ 2 := by
  simp only [domain, mem_diff, mem_ball, mem_union, mem_closedBall, dist_eq_norm, sub_zero,
    sub_neg_eq_add, not_or, not_le]
  rw [norm_lt_iff_sq zero_le_one, lt_norm_iff_sq (by norm_num), lt_norm_iff_sq (by norm_num),
    norm_sq_eq, norm_sub_hole_sq, norm_add_hole_sq]
  norm_num

theorem isOpen_domain : IsOpen domain :=
  isOpen_ball.sdiff (isClosed_closedBall.union isClosed_closedBall)

theorem isBounded_domain : Bornology.IsBounded domain :=
  isBounded_ball.subset diff_subset

theorem domain_subset_ball : domain ⊆ ball 0 1 := diff_subset

/-! ### Connectedness -/

/-- The coordinate functionals are linear. -/
theorem isLinearMap_coord (i : Fin 2) : IsLinearMap ℝ fun y : E 2 ↦ y i :=
  (EuclideanSpace.projₗ (𝕜 := ℝ) i).isLinear

theorem convex_cap_gt (i : Fin 2) (c : ℝ) : Convex ℝ (ball (0 : E 2) 1 ∩ {y | c < y i}) :=
  (convex_ball _ _).inter (convex_halfSpace_gt (isLinearMap_coord i) c)

theorem convex_cap_lt (i : Fin 2) (c : ℝ) : Convex ℝ (ball (0 : E 2) 1 ∩ {y | y i < c}) :=
  (convex_ball _ _).inter (convex_halfSpace_lt (isLinearMap_coord i) c)

theorem mem_ball_iff_coord (y : E 2) : y ∈ ball (0 : E 2) 1 ↔ y 0 ^ 2 + y 1 ^ 2 < 1 := by
  rw [mem_ball, dist_eq_norm, sub_zero, norm_lt_iff_sq zero_le_one, norm_sq_eq]; norm_num

/-- The point `(s, t)`. -/
def pt (s t : ℝ) : E 2 := !₂[s, t]

@[simp] theorem pt_zero (s t : ℝ) : pt s t 0 = s := rfl
@[simp] theorem pt_one (s t : ℝ) : pt s t 1 = t := rfl

/-- The union of the four caps `{y₂ > 1/20}`, `{y₁ > 1/2}`, `{y₂ < -1/20}`, `{y₁ < -1/2}` of the
unit disc is preconnected. -/
theorem isPreconnected_caps :
    IsPreconnected ((ball (0 : E 2) 1 ∩ {y | 1 / 20 < y 1}) ∪
      (ball (0 : E 2) 1 ∩ {y | 1 / 2 < y 0}) ∪ (ball (0 : E 2) 1 ∩ {y | y 1 < -1 / 20}) ∪
      (ball (0 : E 2) 1 ∩ {y | y 0 < -1 / 2})) := by
  have hmem : ∀ s t : ℝ, s ^ 2 + t ^ 2 < 1 → pt s t ∈ ball (0 : E 2) 1 := fun s t h ↦ by
    rw [mem_ball_iff_coord]; simpa using h
  refine (((convex_cap_gt 1 _).isPreconnected.union (pt (3 / 5) (1 / 10)) ?_ ?_
    (convex_cap_gt 0 _).isPreconnected).union (pt (3 / 5) (-1 / 10)) ?_ ?_
    (convex_cap_lt 1 _).isPreconnected).union (pt (-3 / 5) (-1 / 10)) ?_ ?_
    (convex_cap_lt 0 _).isPreconnected
  · exact ⟨hmem _ _ (by norm_num), by simp; norm_num⟩
  · exact ⟨hmem _ _ (by norm_num), by simp; norm_num⟩
  · exact Or.inr ⟨hmem _ _ (by norm_num), by simp; norm_num⟩
  · exact ⟨hmem _ _ (by norm_num), by simp; norm_num⟩
  · exact Or.inr ⟨hmem _ _ (by norm_num), by simp; norm_num⟩
  · exact ⟨hmem _ _ (by norm_num), by simp; norm_num⟩

theorem caps_subset_domain :
    (ball (0 : E 2) 1 ∩ {y | 1 / 20 < y 1}) ∪ (ball (0 : E 2) 1 ∩ {y | 1 / 2 < y 0}) ∪
      (ball (0 : E 2) 1 ∩ {y | y 1 < -1 / 20}) ∪ (ball (0 : E 2) 1 ∩ {y | y 0 < -1 / 2}) ⊆
      domain := by
  rintro y (((⟨hb, hy⟩ | ⟨hb, hy⟩) | ⟨hb, hy⟩) | ⟨hb, hy⟩) <;>
  · rw [mem_ball_iff_coord] at hb
    simp only [mem_setOf_eq] at hy
    rw [mem_domain_iff]
    refine ⟨hb, ?_, ?_⟩ <;> nlinarith [sq_nonneg (y 0 - 1 / 10), sq_nonneg (y 0 + 1 / 10),
      sq_nonneg (y 1)]

/-- The vertical segment from a point of `U` with `|x₁| ≤ 1/2` away from the axis stays in `U`. -/
theorem segment_vertical_subset {x : E 2} (hx : x ∈ domain) (h0 : |x 0| ≤ 1 / 2) {t : ℝ}
    (hxt : 0 ≤ x 1 * (t - x 1)) (ht : t ^ 2 ≤ max (x 1 ^ 2) (1 / 100)) :
    segment ℝ x (pt (x 0) t) ⊆ domain := by
  rintro y ⟨α, β, hα, hβ, hαβ, rfl⟩
  rw [mem_domain_iff] at hx ⊢
  have e0 : (α • x + β • pt (x 0) t) 0 = x 0 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero]
    rw [← add_mul, hαβ, one_mul]
  have e1 : (α • x + β • pt (x 0) t) 1 = α * x 1 + β * t := by simp
  rw [e0, e1]
  -- the new second coordinate is at least as far from the axis
  have hge : x 1 ^ 2 ≤ (α * x 1 + β * t) ^ 2 := by
    have : α * x 1 + β * t = x 1 + β * (t - x 1) := by
      rw [show α = 1 - β by linarith]; ring
    rw [this]
    nlinarith [mul_nonneg hβ hxt, sq_nonneg (β * (t - x 1))]
  have hle : (α * x 1 + β * t) ^ 2 ≤ max (x 1 ^ 2) (1 / 100) := by
    have hconv : (α * x 1 + β * t) ^ 2 ≤ α * x 1 ^ 2 + β * t ^ 2 := by
      have : α * x 1 ^ 2 + β * t ^ 2 - (α * x 1 + β * t) ^ 2 = α * β * (x 1 - t) ^ 2 := by
        rw [show α = 1 - β by linarith]; ring
      nlinarith [mul_nonneg (mul_nonneg hα hβ) (sq_nonneg (x 1 - t))]
    calc _ ≤ α * x 1 ^ 2 + β * t ^ 2 := hconv
      _ ≤ α * max (x 1 ^ 2) (1 / 100) + β * max (x 1 ^ 2) (1 / 100) := by
          gcongr
          exact le_max_left _ _
      _ = _ := by rw [← add_mul, hαβ, one_mul]
  have h0' : x 0 ^ 2 ≤ 1 / 4 := by
    have := sq_abs (x 0) ▸ pow_le_pow_left₀ (abs_nonneg _) h0 2
    norm_num at this ⊢; linarith
  refine ⟨?_, by linarith [hx.2.1], by linarith [hx.2.2]⟩
  rcases le_total (x 1 ^ 2) (1 / 100) with hm | hm
  · rw [max_eq_right hm] at hle; linarith
  · rw [max_eq_left hm] at hle; linarith [hx.1]

theorem isConnected_domain : IsConnected domain := by
  set W := (ball (0 : E 2) 1 ∩ {y | 1 / 20 < y 1}) ∪ (ball (0 : E 2) 1 ∩ {y | 1 / 2 < y 0}) ∪
      (ball (0 : E 2) 1 ∩ {y | y 1 < -1 / 20}) ∪ (ball (0 : E 2) 1 ∩ {y | y 0 < -1 / 2}) with hW
  have hb : pt 0 (1 / 2) ∈ W := by
    refine Or.inl (Or.inl (Or.inl ⟨?_, ?_⟩))
    · rw [mem_ball_iff_coord]; norm_num
    · simp only [mem_setOf_eq, pt_one]; norm_num
  refine ⟨⟨pt 0 (1 / 2), caps_subset_domain hb⟩,
    isPreconnected_of_forall (pt 0 (1 / 2)) fun y hy ↦ ?_⟩
  by_cases hyW : y ∈ W
  · exact ⟨W, caps_subset_domain, hb, hyW, isPreconnected_caps⟩
  -- otherwise `|y₁| ≤ 1/2`; move vertically to `|y₂| = max |y₂| (1/10)`
  have hy0 : |y 0| ≤ 1 / 2 := by
    rw [abs_le]
    have hyb : y ∈ ball (0 : E 2) 1 := domain_subset_ball hy
    constructor <;> by_contra h <;> push Not at h <;> apply hyW
    · exact Or.inr ⟨hyb, by simp only [mem_setOf_eq]; linarith⟩
    · exact Or.inl (Or.inl (Or.inr ⟨hyb, by simp only [mem_setOf_eq]; linarith⟩))
  have hyb := (mem_domain_iff y).1 hy
  set t := if 0 ≤ y 1 then max (y 1) (1 / 10) else min (y 1) (-1 / 10) with ht
  have hxt : 0 ≤ y 1 * (t - y 1) := by
    rw [ht]; split_ifs with h
    · exact mul_nonneg h (by linarith [le_max_left (y 1) (1 / 10)])
    · push Not at h
      exact mul_nonneg_of_nonpos_of_nonpos h.le (by linarith [min_le_left (y 1) (-1 / 10)])
  have htsq : t ^ 2 ≤ max (y 1 ^ 2) (1 / 100) := by
    rw [ht]; split_ifs with h
    · rcases le_total (y 1) (1 / 10) with h' | h'
      · rw [max_eq_right h']; norm_num
      · rw [max_eq_left h']; exact le_max_left _ _
    · push Not at h
      rcases le_total (y 1) (-1 / 10) with h' | h'
      · rw [min_eq_left h']; exact le_max_left _ _
      · rw [min_eq_right h']; norm_num
  have htW : pt (y 0) t ∈ W := by
    have hball : pt (y 0) t ∈ ball (0 : E 2) 1 := by
      rw [mem_ball_iff_coord, pt_zero, pt_one]
      have h0' : y 0 ^ 2 ≤ 1 / 4 := by
        have := sq_abs (y 0) ▸ pow_le_pow_left₀ (abs_nonneg _) hy0 2
        norm_num at this ⊢; linarith
      rcases le_total (y 1 ^ 2) (1 / 100) with hm | hm
      · rw [max_eq_right hm] at htsq; linarith
      · rw [max_eq_left hm] at htsq; linarith [hyb.1]
    by_cases h : 0 ≤ y 1
    · have htv : t = max (y 1) (1 / 10) := by rw [ht, if_pos h]
      exact Or.inl (Or.inl (Or.inl ⟨hball, by
        simp only [mem_setOf_eq, pt_one]; rw [htv]; linarith [le_max_right (y 1) (1 / 10)]⟩))
    · have htv : t = min (y 1) (-1 / 10) := by rw [ht, if_neg h]
      exact Or.inl (Or.inr ⟨hball, by
        simp only [mem_setOf_eq, pt_one]; rw [htv]; linarith [min_le_right (y 1) (-1 / 10)]⟩)
  refine ⟨segment ℝ y (pt (y 0) t) ∪ W,
    union_subset (segment_vertical_subset hy hy0 hxt htsq) caps_subset_domain, Or.inr hb,
    Or.inl (left_mem_segment _ _ _), ?_⟩
  exact (convex_segment _ _).isPreconnected.union (pt (y 0) t) (right_mem_segment _ _ _) htW
    isPreconnected_caps

/-! ### The `C²` boundary -/

/-- The defining function `ρ(x) = (|x|² - 1)(1/400 - |x - p|²)(1/400 - |x + p|²)`. -/
def rhoU (x : E 2) : ℝ := (‖x‖ ^ 2 - 1) * ((1 / 400 - ‖x - hole‖ ^ 2) * (1 / 400 - ‖x + hole‖ ^ 2))

theorem contDiff_rhoU : ContDiff ℝ 2 rhoU := by
  unfold rhoU
  have := contDiff_norm_sq ℝ (E := E 2) (n := 2)
  have h1 : ContDiff ℝ 2 fun x : E 2 ↦ ‖x - hole‖ ^ 2 := this.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ 2 fun x : E 2 ↦ ‖x + hole‖ ^ 2 := this.comp (contDiff_id.add contDiff_const)
  exact (this.sub contDiff_const).mul ((contDiff_const.sub h1).mul (contDiff_const.sub h2))

/-- Sign facts: the holes are disjoint and lie inside the unit disc. -/
theorem hole_facts (x : E 2) :
    (‖x - hole‖ ^ 2 ≤ 1 / 400 → 1 / 400 < ‖x + hole‖ ^ 2 ∧ ‖x‖ ^ 2 < 1) ∧
    (‖x + hole‖ ^ 2 ≤ 1 / 400 → 1 / 400 < ‖x - hole‖ ^ 2 ∧ ‖x‖ ^ 2 < 1) := by
  rw [norm_sub_hole_sq, norm_add_hole_sq, norm_sq_eq]
  constructor <;> intro h <;> constructor <;>
    nlinarith [sq_nonneg (x 0 - 1 / 10), sq_nonneg (x 0 + 1 / 10), sq_nonneg (x 1)]

theorem domain_eq : domain = {x | rhoU x < 0} := by
  ext x
  have hd : x ∈ domain ↔ ‖x‖ ^ 2 < 1 ∧ 1 / 400 < ‖x - hole‖ ^ 2 ∧ 1 / 400 < ‖x + hole‖ ^ 2 := by
    rw [mem_domain_iff, norm_sq_eq, norm_sub_hole_sq, norm_add_hole_sq]
  rw [hd, mem_setOf_eq, rhoU]
  obtain ⟨h1, h2⟩ := hole_facts x
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact mul_neg_of_neg_of_pos (by linarith) (mul_pos_of_neg_of_neg (by linarith) (by linarith))
  · intro h
    by_cases hb : ‖x - hole‖ ^ 2 ≤ 1 / 400
    · obtain ⟨hc, ha⟩ := h1 hb
      have : 0 ≤ (‖x‖ ^ 2 - 1) * ((1 / 400 - ‖x - hole‖ ^ 2) * (1 / 400 - ‖x + hole‖ ^ 2)) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith)
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
      linarith
    by_cases hc : ‖x + hole‖ ^ 2 ≤ 1 / 400
    · obtain ⟨hb', ha⟩ := h2 hc
      have : 0 ≤ (‖x‖ ^ 2 - 1) * ((1 / 400 - ‖x - hole‖ ^ 2) * (1 / 400 - ‖x + hole‖ ^ 2)) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith)
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
      linarith
    push Not at hb hc
    refine ⟨?_, hb, hc⟩
    by_contra ha
    push Not at ha
    have : 0 ≤ (‖x‖ ^ 2 - 1) * ((1 / 400 - ‖x - hole‖ ^ 2) * (1 / 400 - ‖x + hole‖ ^ 2)) :=
      mul_nonneg (by linarith) (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
    linarith

theorem rhoU_eq_zero_of_mem_frontier {x : E 2} (hx : x ∈ frontier domain) : rhoU x = 0 := by
  have hc : Continuous rhoU := contDiff_rhoU.continuous
  have hcl : closure domain ⊆ {x | rhoU x ≤ 0} := by
    rw [domain_eq]
    exact closure_minimal (fun y (hy : rhoU y < 0) ↦ hy.le) (isClosed_le hc continuous_const)
  have h1 : rhoU x ≤ 0 := hcl hx.1
  have h2 : ¬ rhoU x < 0 := by
    have := hx.2
    rw [isOpen_domain.interior_eq, domain_eq] at this
    exact this
  linarith [not_lt.1 h2]

/-- If `f x = 0`, `g x ≠ 0` and `Df(x) v ≠ 0`, then `∇(f g)(x) ≠ 0`. -/
theorem gradient_mul_ne_zero {f g : E 2 → ℝ} {x v : E 2} {Df Dg : E 2 →L[ℝ] ℝ}
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x) (hfx : f x = 0) (hgx : g x ≠ 0)
    (hv : Df v ≠ 0) : ∇ (fun y ↦ f y * g y) x ≠ 0 := by
  intro h0
  have hd : HasFDerivAt (fun y ↦ f y * g y) (f x • Dg + g x • Df) x := hf.mul hg
  have : fderiv ℝ (fun y ↦ f y * g y) x = 0 := by
    have := congrArg (toDual ℝ (E 2)) h0
    simpa [gradient] using this
  rw [hd.fderiv] at this
  have := congrArg (fun L : E 2 →L[ℝ] ℝ ↦ L v) this
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    hfx, zero_mul, zero_add, ContinuousLinearMap.zero_apply] at this
  exact mul_ne_zero hgx hv this

theorem hasFDerivAt_norm_sub_sq (c x : E 2) :
    HasFDerivAt (fun y : E 2 ↦ ‖y - c‖ ^ 2)
      (2 • (innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ (E 2))) x :=
  ((hasFDerivAt_id x).sub_const c).norm_sq

theorem hasC2Boundary_domain : HasC2Boundary domain := by
  refine ⟨rhoU, contDiff_rhoU, domain_eq, fun x hx ↦ ?_⟩
  have h0 := rhoU_eq_zero_of_mem_frontier hx
  obtain ⟨h1, h2⟩ := hole_facts x
  -- derivative data of the three factors
  have dA := (hasFDerivAt_norm_sub_sq 0 x).sub_const (1 : ℝ)
  have dB := (hasFDerivAt_norm_sub_sq hole x).const_sub (1 / 400 : ℝ)
  have dC := (hasFDerivAt_norm_sub_sq (-hole) x).const_sub (1 / 400 : ℝ)
  simp only [sub_zero, sub_neg_eq_add] at dA dB dC
  have hdir : ∀ c : E 2, x - c ≠ 0 →
      (2 • (innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ (E 2))) (x - c) ≠ 0 := by
    intro c hc
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.coe_id', id_eq, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat]
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.2 hc))
  have hne : ∀ c : E 2, ‖x - c‖ ^ 2 ≠ 0 → x - c ≠ 0 := fun c h hc ↦ h (by simp [hc])
  rw [rhoU] at h0
  rcases mul_eq_zero.1 h0 with hA | hBC
  · -- on the outer circle
    have hb : ¬ ‖x - hole‖ ^ 2 ≤ 1 / 400 := fun hb ↦ by linarith [(h1 hb).2]
    have hc : ¬ ‖x + hole‖ ^ 2 ≤ 1 / 400 := fun hc ↦ by linarith [(h2 hc).2]
    have : ∇ (fun y ↦ (‖y‖ ^ 2 - 1) * ((1 / 400 - ‖y - hole‖ ^ 2) * (1 / 400 - ‖y + hole‖ ^ 2)))
        x ≠ 0 := gradient_mul_ne_zero (v := x - 0) dA (dB.mul dC) hA
      (mul_ne_zero (by linarith [not_le.1 hb]) (by linarith [not_le.1 hc]))
      (by
        have := hdir 0 (hne 0 (by rw [sub_zero]; linarith))
        simpa using this)
    exact this
  rcases mul_eq_zero.1 hBC with hB | hC
  · have hB' : ‖x - hole‖ ^ 2 ≤ 1 / 400 := by linarith
    obtain ⟨hc, ha⟩ := h1 hB'
    have e : rhoU = fun y ↦ (1 / 400 - ‖y - hole‖ ^ 2) *
        ((‖y‖ ^ 2 - 1) * (1 / 400 - ‖y + hole‖ ^ 2)) := by
      funext y; rw [rhoU]; ring
    have : ∇ (fun y ↦ (1 / 400 - ‖y - hole‖ ^ 2) * ((‖y‖ ^ 2 - 1) * (1 / 400 - ‖y + hole‖ ^ 2)))
        x ≠ 0 := gradient_mul_ne_zero (v := x - hole) dB (dA.mul dC) (by linarith)
      (mul_ne_zero (by linarith) (by linarith))
      (by
        have := hdir hole (hne hole (by linarith))
        simpa using this)
    rwa [← e] at this
  · have hC' : ‖x + hole‖ ^ 2 ≤ 1 / 400 := by linarith
    obtain ⟨hb, ha⟩ := h2 hC'
    have e : rhoU = fun y ↦ (1 / 400 - ‖y + hole‖ ^ 2) *
        ((‖y‖ ^ 2 - 1) * (1 / 400 - ‖y - hole‖ ^ 2)) := by
      funext y; rw [rhoU]; ring
    have : ∇ (fun y ↦ (1 / 400 - ‖y + hole‖ ^ 2) * ((‖y‖ ^ 2 - 1) * (1 / 400 - ‖y - hole‖ ^ 2)))
        x ≠ 0 := gradient_mul_ne_zero (v := x + hole) dC (dA.mul dB) (by linarith)
      (mul_ne_zero (by linarith) (by linarith))
      (by
        have hn : ‖x + hole‖ ^ 2 ≠ 0 := by
          rw [show ‖x + hole‖ ^ 2 = 1 / 400 by linarith]; norm_num
        simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_id', id_eq,
          innerSL_apply_apply, real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat,
          neg_ne_zero]
        exact mul_ne_zero two_ne_zero hn)
    rwa [← e] at this

/-! ### The setting -/

/-- The setting of the example: the two-disc domain with `Q ≡ 1`. -/
def setting : Setting 2 where
  U := domain
  Q := fun _ ↦ 1
  Qmin := 1
  Qmax := 1
  two_le := le_rfl
  isOpen := isOpen_domain
  isBounded := isBounded_domain
  isConnected := isConnected_domain
  c2 := hasC2Boundary_domain
  lip := ⟨0, (LipschitzWith.const (1 : ℝ)).lipschitzOnWith⟩
  Qmin_pos := one_pos
  Qmin_le_Qmax := le_rfl
  Q_mem := fun _ _ ↦ ⟨le_rfl, le_rfl⟩

end PerronVariational.TwoDisc

end
