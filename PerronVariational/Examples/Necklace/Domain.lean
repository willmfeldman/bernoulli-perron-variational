/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.Geometry
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The necklace domain

The domain of the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M.
Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`): `U = B₄(0) \ ⋃_{k < N} B̄_r(z_k)` in `ℝ²` (`N = 100`, `r = 1/20`).

* The holes are pairwise disjoint and lie in the annulus `R - r ≤ |x| ≤ R + r`
  (`lt_norm_sub_cen_of_mem_hole`, `norm_le_of_mem_holes`).
* `U` is open, bounded and connected (`isConnected_domain`): every point is joined inside `U`
  either to `0` along the segment `[0, x]`, or radially to the circle `∂B_{39/10}(0)`, since a ray
  from `0` meets at most one hole; the circle is joined to `0` along the ray through the kissing
  point `m_0`, which misses all holes.
* `ρ(x) = (|x|² - 16) ∏_k (|x - z_k|² - r²)` is a `C²` defining function (`hasC2Boundary_domain`).
* `setting` packages `U` with `Q ≡ 1`.
-/

open Set Filter Topology Metric Real InnerProductSpace
open scoped Gradient RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational.Necklace

open TwoDisc (norm_sq_eq gradient_mul_ne_zero hasFDerivAt_norm_sub_sq)

/-- The union of the closed holes `B̄_r(z_k)`, `k < N`. -/
def holes : Set (E 2) := ⋃ k : Fin numHoles, closedBall (cen ((k : ℕ) : ℤ)) holeRad

/-- The necklace domain `B₄(0) \ ⋃_{k < N} B̄_r(z_k)`. -/
def domain : Set (E 2) := ball 0 outerRad \ holes

theorem mem_holes_iff {x : E 2} :
    x ∈ holes ↔ ∃ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ≤ holeRad := by
  simp [holes, mem_closedBall, dist_eq_norm]

theorem mem_domain_iff {x : E 2} :
    x ∈ domain ↔ ‖x‖ < outerRad ∧ ∀ k : Fin numHoles, holeRad < ‖x - cen ((k : ℕ) : ℤ)‖ := by
  simp [domain, mem_holes_iff, mem_ball, dist_eq_norm]

theorem isOpen_domain : IsOpen domain :=
  isOpen_ball.sdiff (isClosed_iUnion_of_finite fun _ ↦ isClosed_closedBall)

theorem isBounded_domain : Bornology.IsBounded domain :=
  isBounded_ball.subset sdiff_subset

/-! ### The holes -/

theorem not_dvd_of_ne {j k : Fin numHoles} (h : j ≠ k) :
    ¬ (numHoles : ℤ) ∣ ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) := by
  have hj := j.isLt; have hk := k.isLt
  have hjk : (j : ℕ) ≠ k := Fin.val_ne_of_ne h
  simp only [numHoles] at hj hk ⊢
  omega

theorem eq_of_dvd {j k : Fin numHoles} (h : (numHoles : ℤ) ∣ ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) :
    j = k := by
  by_contra hne; exact not_dvd_of_ne hne h

/-- The holes are pairwise disjoint (with room to spare: `2r < 2a ≤ |z_j - z_k|`). -/
theorem lt_norm_sub_cen_of_mem_hole {x : E 2} {j k : Fin numHoles} (h : j ≠ k)
    (hx : ‖x - cen ((j : ℕ) : ℤ)‖ ≤ holeRad) : holeRad < ‖x - cen ((k : ℕ) : ℤ)‖ := by
  have hd := two_kissRad_le_norm_cen_sub_cen (not_dvd_of_ne h)
  have := norm_sub_le_norm_sub_add_norm_sub (cen ((j : ℕ) : ℤ)) x (cen ((k : ℕ) : ℤ))
  have e := norm_sub_rev x (cen ((j : ℕ) : ℤ))
  unfold kissRad holeRad at *
  linarith

theorem norm_le_of_mem_hole {x : E 2} {k : ℤ} (hx : ‖x - cen k‖ ≤ holeRad) :
    ‖x‖ ≤ ringRad + holeRad := by
  have := norm_le_norm_add_norm_sub' x (cen k)
  rw [norm_cen] at this; linarith

theorem le_norm_of_mem_hole {x : E 2} {k : ℤ} (hx : ‖x - cen k‖ ≤ holeRad) :
    ringRad - holeRad ≤ ‖x‖ := by
  have := norm_sub_norm_le (cen k) x
  rw [norm_cen, norm_sub_rev] at this; linarith

theorem ringRad_add_holeRad_lt : ringRad + holeRad < 39 / 10 := by
  unfold holeRad; linarith [ringRad_bounds.2]

theorem holeRad_lt_norm_sub_cen_of_lt {x : E 2} (k : ℤ) (hx : ringRad + holeRad < ‖x‖) :
    holeRad < ‖x - cen k‖ := by
  by_contra h; push Not at h; linarith [norm_le_of_mem_hole h]

theorem holeRad_lt_norm_sub_cen_of_lt' {x : E 2} (k : ℤ) (hx : ‖x‖ < ringRad - holeRad) :
    holeRad < ‖x - cen k‖ := by
  by_contra h; push Not at h; linarith [le_norm_of_mem_hole h]

theorem zero_mem_domain : (0 : E 2) ∈ domain := by
  rw [mem_domain_iff]
  refine ⟨by norm_num [outerRad], fun k ↦ holeRad_lt_norm_sub_cen_of_lt' _ ?_⟩
  rw [norm_zero]; unfold holeRad; linarith [ringRad_bounds.1]

/-! ### Connectedness -/

theorem smul_pol (c s φ : ℝ) : c • pol s φ = pol (c * s) φ := by
  ext i; fin_cases i <;> simp [pol, mul_assoc]

theorem one_lt_rank : 1 < Module.rank ℝ (E 2) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num

/-- The point `(39/10) e₁`, on the ray through the kissing point `m_0`. -/
def outPt : E 2 := pol (39 / 10) 0

/-- The connector: the segment `[0, (39/10) e₁]` together with the circle `∂B_{39/10}(0)`. -/
def connector : Set (E 2) := segment ℝ 0 outPt ∪ sphere 0 (39 / 10)

theorem norm_outPt : ‖outPt‖ = 39 / 10 := norm_pol (by norm_num) _

theorem isPreconnected_connector : IsPreconnected connector :=
  (convex_segment _ _).isPreconnected.union outPt (right_mem_segment _ _ _)
    (by rw [mem_sphere_zero_iff_norm, norm_outPt]) (isPreconnected_sphere one_lt_rank _ _)

theorem sphere_subset_domain : sphere (0 : E 2) (39 / 10) ⊆ domain := by
  intro y hy
  rw [mem_sphere_zero_iff_norm] at hy
  rw [mem_domain_iff, hy]
  refine ⟨by norm_num [outerRad], fun k ↦ holeRad_lt_norm_sub_cen_of_lt _ ?_⟩
  rw [hy]; exact ringRad_add_holeRad_lt

theorem connector_subset_domain : connector ⊆ domain := by
  refine union_subset ?_ sphere_subset_domain
  rw [segment_eq_image]
  rintro _ ⟨c, ⟨hc0, hc1⟩, rfl⟩
  simp only [smul_zero, zero_add, outPt, smul_pol]
  rw [mem_domain_iff, norm_pol (by positivity)]
  refine ⟨by unfold outerRad; nlinarith, fun k ↦ ?_⟩
  rcases hc0.eq_or_lt with rfl | hc
  · rw [zero_mul]
    have := holeRad_lt_norm_sub_cen_of_lt' (x := 0) ((k : ℕ) : ℤ)
      (by rw [norm_zero]; unfold holeRad; linarith [ringRad_bounds.1])
    convert this using 2
    ext i; fin_cases i <;> simp [pol]
  · exact holeRad_lt_norm_pol_zero_sub_cen (by positivity) _

theorem zero_mem_connector : (0 : E 2) ∈ connector := Or.inl (left_mem_segment _ _ _)

/-- A point of `U` is joined to the connector inside `U`. -/
theorem exists_preconnected_join {x : E 2} (hx : x ∈ domain) :
    ∃ t ⊆ domain, (0 : E 2) ∈ t ∧ x ∈ t ∧ IsPreconnected t := by
  have hx' := mem_domain_iff.1 hx
  by_cases hA : ∀ c ∈ Icc (0 : ℝ) 1, ∀ k : Fin numHoles, holeRad < ‖c • x - cen ((k : ℕ) : ℤ)‖
  · -- the segment `[0, x]` misses the holes
    refine ⟨segment ℝ 0 x, ?_, left_mem_segment _ _ _, right_mem_segment _ _ _,
      (convex_segment _ _).isPreconnected⟩
    rw [segment_eq_image]
    rintro _ ⟨c, hc, rfl⟩
    simp only [smul_zero, zero_add]
    rw [mem_domain_iff, norm_smul, Real.norm_of_nonneg hc.1]
    exact ⟨by nlinarith [hc.2, norm_nonneg x, hx'.1], hA c hc⟩
  -- otherwise some `c x`, `0 ≤ c ≤ 1`, lies in a hole; go outwards
  push Not at hA
  obtain ⟨c, ⟨hc0, hc1⟩, k, hck⟩ := hA
  have hcpos : 0 < c := by
    rcases hc0.eq_or_lt with rfl | h
    · rw [zero_smul, zero_sub, norm_neg, norm_cen] at hck
      exact absurd hck (not_le.2 holeRad_lt_ringRad)
    · exact h
  have hxpos : 0 < ‖x‖ := by
    have := le_norm_of_mem_hole hck
    rw [norm_smul, Real.norm_of_nonneg hc0] at this
    have : 0 < c * ‖x‖ := by unfold holeRad at this; linarith [ringRad_bounds.1]
    exact pos_of_mul_pos_right this hc0
  set q : E 2 := ((39 / 10) / ‖x‖) • x with hq
  have hqn : ‖q‖ = 39 / 10 := by
    rw [hq, norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp
  refine ⟨segment ℝ x q ∪ connector, union_subset ?_ connector_subset_domain,
    Or.inr zero_mem_connector, Or.inl (left_mem_segment _ _ _),
    (convex_segment _ _).isPreconnected.union q (right_mem_segment _ _ _)
      (Or.inr (by rw [mem_sphere_zero_iff_norm, hqn])) isPreconnected_connector⟩
  rw [segment_eq_image]
  rintro _ ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
  set μ := 1 - θ + θ * ((39 / 10) / ‖x‖) with hμ
  have heq : (1 - θ) • x + θ • q = μ • x := by
    rw [hq, smul_smul, ← add_smul]
  have hμx : μ * ‖x‖ = (1 - θ) * ‖x‖ + θ * (39 / 10) := by
    rw [hμ]; field_simp
  have hμpos : 0 < μ := by
    have : 0 < μ * ‖x‖ := by
      rw [hμx]
      rcases hθ0.eq_or_lt with rfl | hθ
      · simpa using hxpos
      · nlinarith
    exact pos_of_mul_pos_left this hxpos.le
  change (1 - θ) • x + θ • q ∈ domain
  rw [heq, mem_domain_iff, norm_smul, Real.norm_of_nonneg hμpos.le, hμx]
  have hx4 : ‖x‖ < 4 := hx'.1
  refine ⟨by unfold outerRad; nlinarith, fun j ↦ ?_⟩
  rcases le_or_gt 1 μ with h1 | h1
  · -- beyond `x` on the ray: at most one hole, and it is the hole of `c x`
    by_contra hj
    push Not at hj
    have hjk := eq_of_dvd (dvd_of_mem_hole_of_mem_hole hμpos hcpos hj hck)
    subst hjk
    -- `x` lies between `c x` and `μ x`
    have hmem : x ∈ closedBall (cen ((j : ℕ) : ℤ)) holeRad := by
      rcases hc1.eq_or_lt with rfl | hc1'
      · rw [one_smul] at hck; rwa [mem_closedBall, dist_eq_norm]
      have hne : μ - c ≠ 0 := by linarith
      have hseg : x ∈ segment ℝ (c • x) (μ • x) := by
        refine ⟨(μ - 1) / (μ - c), (1 - c) / (μ - c), div_nonneg (by linarith) (by linarith),
          div_nonneg (by linarith) (by linarith), by field_simp; ring, ?_⟩
        rw [smul_smul, smul_smul, ← add_smul]
        have : (μ - 1) / (μ - c) * c + (1 - c) / (μ - c) * μ = 1 := by field_simp; ring
        rw [this, one_smul]
      exact (convex_closedBall _ _).segment_subset
        (by rwa [mem_closedBall, dist_eq_norm]) (by rwa [mem_closedBall, dist_eq_norm]) hseg
    rw [mem_closedBall, dist_eq_norm] at hmem
    exact absurd hmem (not_le.2 (hx'.2 j))
  · -- `|x| > 39/10`: the whole segment stays outside `B_{R + r}`
    refine holeRad_lt_norm_sub_cen_of_lt _ ?_
    rw [norm_smul, Real.norm_of_nonneg hμpos.le, hμx]
    have hθ : θ * (39 / 10 / ‖x‖) < θ := by linarith
    have hx39 : 39 / 10 < ‖x‖ := by
      rcases hθ0.eq_or_lt with rfl | hθpos
      · simp at hθ
      · have := (mul_lt_iff_lt_one_right hθpos).1 hθ
        rwa [div_lt_one hxpos] at this
    nlinarith [ringRad_add_holeRad_lt]

theorem isConnected_domain : IsConnected domain :=
  ⟨⟨0, zero_mem_domain⟩, isPreconnected_of_forall 0 fun _ hx ↦ exists_preconnected_join hx⟩

/-! ### The `C²` boundary -/

/-- The product of the hole factors `∏_k (|x - z_k|² - r²)`. -/
def holeProd (x : E 2) : ℝ := ∏ k : Fin numHoles, (‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 - holeRad ^ 2)

/-- The defining function `ρ(x) = (|x|² - 16) ∏_k (|x - z_k|² - r²)`. -/
def rhoU (x : E 2) : ℝ := (‖x‖ ^ 2 - outerRad ^ 2) * holeProd x

theorem contDiff_holeFactor (k : ℤ) :
    ContDiff ℝ 2 fun x : E 2 ↦ ‖x - cen k‖ ^ 2 - holeRad ^ 2 :=
  ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const

theorem contDiff_holeProd : ContDiff ℝ 2 holeProd :=
  contDiff_prod fun _ _ ↦ contDiff_holeFactor _

theorem contDiff_rhoU : ContDiff ℝ 2 rhoU :=
  ((contDiff_norm_sq ℝ).sub contDiff_const).mul contDiff_holeProd

theorem holeFactor_pos {x : E 2} {k : ℤ} (h : holeRad < ‖x - cen k‖) :
    0 < ‖x - cen k‖ ^ 2 - holeRad ^ 2 := by
  have : holeRad ^ 2 < ‖x - cen k‖ ^ 2 :=
    pow_lt_pow_left₀ h (by norm_num [holeRad]) two_ne_zero
  linarith

theorem holeProd_pos {x : E 2} (hx : x ∉ holes) : 0 < holeProd x := by
  rw [mem_holes_iff] at hx
  push Not at hx
  exact Finset.prod_pos fun k _ ↦ holeFactor_pos (hx k)

/-- Split off the `k`-th factor of `holeProd`. -/
theorem holeProd_eq (k : Fin numHoles) (x : E 2) :
    holeProd x = (‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 - holeRad ^ 2) *
      ∏ j ∈ Finset.univ.erase k, (‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 - holeRad ^ 2) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm

theorem prod_erase_pos {x : E 2} {k : Fin numHoles} (hx : ‖x - cen ((k : ℕ) : ℤ)‖ ≤ holeRad) :
    0 < ∏ j ∈ Finset.univ.erase k, (‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 - holeRad ^ 2) :=
  Finset.prod_pos fun _ hj ↦
    holeFactor_pos (lt_norm_sub_cen_of_mem_hole (Finset.ne_of_mem_erase hj).symm hx)

theorem holeProd_nonpos {x : E 2} {k : Fin numHoles} (hx : ‖x - cen ((k : ℕ) : ℤ)‖ ≤ holeRad) :
    holeProd x ≤ 0 := by
  rw [holeProd_eq k]
  have h1 : ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 ≤ holeRad ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hx 2
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (prod_erase_pos hx).le

theorem norm_sq_lt_of_mem_hole {x : E 2} {k : ℤ} (hx : ‖x - cen k‖ ≤ holeRad) :
    ‖x‖ ^ 2 < outerRad ^ 2 := by
  have h := norm_le_of_mem_hole hx
  have := ringRad_add_holeRad_lt
  have h0 := norm_nonneg x
  unfold outerRad; nlinarith

theorem domain_eq : domain = {x | rhoU x < 0} := by
  ext x
  simp only [Set.mem_ofPred_eq, rhoU]
  constructor
  · intro hx
    have hx' := mem_domain_iff.1 hx
    have h1 : ‖x‖ ^ 2 < outerRad ^ 2 := pow_lt_pow_left₀ hx'.1 (norm_nonneg _) two_ne_zero
    have h2 : x ∉ holes := hx.2
    exact mul_neg_of_neg_of_pos (by linarith) (holeProd_pos h2)
  · intro h
    by_cases hh : x ∈ holes
    · obtain ⟨k, hk⟩ := mem_holes_iff.1 hh
      have := norm_sq_lt_of_mem_hole hk
      have := mul_nonneg_of_nonpos_of_nonpos (by linarith : ‖x‖ ^ 2 - outerRad ^ 2 ≤ 0)
        (holeProd_nonpos hk)
      linarith
    · have hp := holeProd_pos hh
      have h1 : ‖x‖ ^ 2 - outerRad ^ 2 < 0 := by
        by_contra hc; push Not at hc; nlinarith
      refine ⟨?_, hh⟩
      rw [mem_ball, dist_zero_right]
      have : ‖x‖ ^ 2 < outerRad ^ 2 := by linarith
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by norm_num [outerRad]) two_ne_zero).1 this

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

theorem hasFDerivAt_norm_sub_sq_ne_zero {c x : E 2} (hc : x - c ≠ 0) :
    (2 • (innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ (E 2))) (x - c) ≠ 0 := by
  simp only [smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.coe_id', id_eq, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat]
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.2 hc))

theorem hasC2Boundary_domain : HasC2Boundary domain := by
  refine ⟨rhoU, contDiff_rhoU, domain_eq, fun x hx ↦ ?_⟩
  have h0 := rhoU_eq_zero_of_mem_frontier hx
  rw [rhoU] at h0
  rcases mul_eq_zero.1 h0 with hA | hB
  · -- on the outer circle
    have hn : ‖x‖ = outerRad := by
      have : ‖x‖ ^ 2 = outerRad ^ 2 := by linarith
      exact (pow_left_inj₀ (norm_nonneg _) (by norm_num [outerRad]) two_ne_zero).1 this
    have hh : x ∉ holes := by
      rw [mem_holes_iff]; rintro ⟨k, hk⟩
      have := norm_sq_lt_of_mem_hole hk; rw [hn] at this; exact lt_irrefl _ this
    have dA := ((hasFDerivAt_norm_sub_sq 0 x).sub_const (outerRad ^ 2))
    simp only [sub_zero] at dA
    have dB := (contDiff_holeProd.differentiable (by norm_num) x).hasFDerivAt
    exact gradient_mul_ne_zero (v := x) dA dB hA (holeProd_pos hh).ne'
      (by
        have := hasFDerivAt_norm_sub_sq_ne_zero (c := 0) (x := x)
          (by rw [sub_zero]; intro h; rw [h, norm_zero] at hn; norm_num [outerRad] at hn)
        simpa using this)
  · -- on a hole circle
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hB
    have hk' : ‖x - cen ((k : ℕ) : ℤ)‖ = holeRad := by
      have : ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 = holeRad ^ 2 := by linarith
      exact (pow_left_inj₀ (norm_nonneg _) (by norm_num [holeRad]) two_ne_zero).1 this
    have e : rhoU = fun y ↦ (‖y - cen ((k : ℕ) : ℤ)‖ ^ 2 - holeRad ^ 2) *
        ((‖y‖ ^ 2 - outerRad ^ 2) *
          ∏ j ∈ Finset.univ.erase k, (‖y - cen ((j : ℕ) : ℤ)‖ ^ 2 - holeRad ^ 2)) := by
      funext y; rw [rhoU, holeProd_eq k]; ring
    have dA := (hasFDerivAt_norm_sub_sq (cen ((k : ℕ) : ℤ)) x).sub_const (holeRad ^ 2)
    have hdiff : ContDiff ℝ 2 fun y : E 2 ↦ (‖y‖ ^ 2 - outerRad ^ 2) *
        ∏ j ∈ Finset.univ.erase k, (‖y - cen ((j : ℕ) : ℤ)‖ ^ 2 - holeRad ^ 2) :=
      ((contDiff_norm_sq ℝ).sub contDiff_const).mul
        (contDiff_prod fun _ _ ↦ contDiff_holeFactor _)
    have dB := (hdiff.differentiable (by norm_num) x).hasFDerivAt
    have hg : (‖x‖ ^ 2 - outerRad ^ 2) *
        ∏ j ∈ Finset.univ.erase k, (‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 - holeRad ^ 2) ≠ 0 :=
      mul_ne_zero (by linarith [norm_sq_lt_of_mem_hole hk'.le]) (prod_erase_pos hk'.le).ne'
    rw [e]
    exact gradient_mul_ne_zero (v := x - cen ((k : ℕ) : ℤ)) dA dB (by rw [hk']; ring) hg
      (hasFDerivAt_norm_sub_sq_ne_zero (by
        intro h; rw [h, norm_zero] at hk'; norm_num [holeRad] at hk'))

/-! ### The setting -/

/-- The setting of the necklace example: the necklace domain with `Q ≡ 1`. -/
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

theorem setting_U : setting.U = domain := rfl

theorem setting_Q : setting.Q = fun _ ↦ 1 := rfl

end PerronVariational.Necklace

end
