/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.Perron
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Order.CompletePartialOrder
import PerronVariational.Semilinear.Calculus
import PerronVariational.Stationary.ViscosityJet

/-!
# Locality of viscosity solutions and Lemma 2.7

Lemma 2.7 and its dual, from F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

* Locality: the viscosity super/subsolution properties are local (`IsViscSuper.mono`,
  `isViscSuper_of_locally`, `IsViscSub.mono`, `isViscSub_of_locally`), and supersolutions can be
  glued along a closed set (`isViscSuper_piecewise`, `isViscSub_piecewise`).
* At a zero of a viscosity supersolution lying above a smooth strict subsolution `g`, one
  has `g < 0` (`IsViscSuper.strictSub_lt_zero`), proved with an explicit polynomial test function
  (`IsViscSuper.false_of_touch_strictSub`). The proof of Lemma 2.7 in the paper claims "`u > g` in
  `U`", which does not follow: Definition 2.2 only gives `Δg ≥ 0`, which is not strict, and `g` is
  only `C²`. Only `g < 0` at free boundary points is needed.
* **Lemma 2.7**: `perronSmallest_isLocalSmallestSuper_near_fb`.
* Comparison with strict `C²` barriers (`IsViscSub.le_max_of_barrier`,
  `IsViscSub.le_max_of_isStrictSuperWith`) and the **dual of Lemma 2.7**, which the paper uses
  but does not prove: `perronLargest_isLocalLargestSub_near_fb`.
-/

open Set Filter Topology Metric Asymptotics
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### A second-order Taylor bound -/

/-- A `C²` function agrees with its first-order Taylor polynomial up to `O(|y - x|²)`. -/
theorem exists_taylor_two_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : F → ℝ} (hg : ContDiff ℝ 2 g) (x : F) :
    ∃ C, ∀ᶠ y in 𝓝 x, |g y - g x - fderiv ℝ g x (y - x)| ≤ C * ‖y - x‖ ^ 2 := by
  have hd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  obtain ⟨C, hC0, hC⟩ := hd.isBigO_sub.exists_pos
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.1 hC.bound
  refine ⟨C, Metric.eventually_nhds_iff.2 ⟨ρ, hρ, fun y hy ↦ ?_⟩⟩
  set r := ‖y - x‖ with hr
  have hs : closedBall x r ⊆ ball x ρ := closedBall_subset_ball (by rwa [hr, ← dist_eq_norm])
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := g)
    (f' := fderiv ℝ g) (φ := fderiv ℝ g x) (s := closedBall x r) (C := C * r)
    (x := x) (y := y) (fun z _ ↦ (hg1 z).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz ↦ (hρ' (hs hz)).trans (mul_le_mul_of_nonneg_left
      (by rw [← dist_eq_norm]; exact mem_closedBall.1 hz) hC0.le))
    (convex_closedBall x r) (mem_closedBall_self (norm_nonneg _))
    (by simp [hr, dist_eq_norm])
  rw [Real.norm_eq_abs] at key
  calc _ ≤ C * r * ‖y - x‖ := key
    _ = C * ‖y - x‖ ^ 2 := by rw [hr]; ring

/-! ### Locality -/

section Locality

variable {U W : Set (E d)} {Q u v : E d → ℝ}

/-- Restriction of a viscosity supersolution to an open subset. -/
theorem IsViscSuper.mono (hu : IsViscSuper U Q u) (hW : IsOpen W) (hWU : W ⊆ U) :
    IsViscSuper W Q u := by
  refine ⟨hu.1.mono hWU, fun x hx ↦ hu.2.1 x (hWU hx), fun φ hφ x hx h ↦ ?_⟩
  refine hu.2.2 φ hφ x (hWU hx) ⟨hWU hx, h.2.1, ?_⟩
  have := h.2.2
  rw [hW.nhdsWithin_eq hx] at this
  exact nhdsWithin_le_nhds this

/-- The viscosity supersolution property is local. -/
theorem isViscSuper_of_locally (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ v, IsViscSuper W Q v ∧ EqOn u v W) :
    IsViscSuper U Q u := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun φ hφ x hx htouch ↦ ?_⟩
  · obtain ⟨W, hW, hxW, -, v, hv, heq⟩ := h x hx
    have hc : ContinuousAt v x := hv.1.continuousAt (hW.mem_nhds hxW)
    exact (hc.congr (Filter.mem_of_superset (hW.mem_nhds hxW)
      fun y hy ↦ (heq hy).symm)).continuousWithinAt
  · obtain ⟨W, -, hxW, -, v, hv, heq⟩ := h x hx
    rw [heq hxW]; exact hv.2.1 x hxW
  · obtain ⟨W, hW, hxW, -, v, hv, heq⟩ := h x hx
    have h2 := htouch.2.2
    rw [hU.nhdsWithin_eq hx] at h2
    refine hv.2.2 φ hφ x hxW ⟨hxW, by rw [htouch.2.1, heq hxW], ?_⟩
    rw [hW.nhdsWithin_eq hxW]
    filter_upwards [h2, hW.mem_nhds hxW] with y hy hyW
    rw [← heq hyW]; exact hy

theorem posSet_inter_eq (hWU : W ⊆ U) (heq : EqOn u v W) :
    posSet u U ∩ W = posSet v W := by
  ext y
  simp only [posSet, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨⟨-, hy⟩, hyW⟩; exact ⟨hyW, by rwa [← heq hyW]⟩
  · rintro ⟨hyW, hy⟩; exact ⟨⟨hWU hyW, by rwa [heq hyW]⟩, hyW⟩

/-- Near a point of an open `W ⊆ U` on which `u = v`, the touching sets
`\overline{{u > 0}} ∩ U` and `\overline{{v > 0}} ∩ W` agree. -/
theorem closure_posSet_inter_eq (hW : IsOpen W) (hWU : W ⊆ U) (heq : EqOn u v W) :
    closure (posSet u U) ∩ U ∩ W = closure (posSet v W) ∩ W := by
  apply Subset.antisymm
  · rintro y ⟨⟨hy, -⟩, hyW⟩
    refine ⟨?_, hyW⟩
    have := hW.inter_closure ⟨hyW, hy⟩
    rwa [inter_comm, posSet_inter_eq hWU heq] at this
  · rintro y ⟨hy, hyW⟩
    refine ⟨⟨closure_mono ?_ hy, hWU hyW⟩, hyW⟩
    rw [← posSet_inter_eq hWU heq]; exact inter_subset_left

/-- Restriction of a viscosity subsolution to an open subset. -/
theorem IsViscSub.mono (hu : IsViscSub U Q u) (hW : IsOpen W) (hWU : W ⊆ U) :
    IsViscSub W Q u := by
  refine ⟨hu.1.mono hWU, fun x hx ↦ hu.2.1 x (hWU hx), fun φ hφ x h ↦ ?_⟩
  have hxW : x ∈ W := h.1.2
  have hS := closure_posSet_inter_eq (u := u) (v := u) hW hWU (fun _ _ ↦ rfl)
  refine hu.2.2 φ hφ x ⟨⟨closure_mono (posSet_inter_eq (u := u) hWU (fun _ _ ↦ rfl) ▸
    inter_subset_left) h.1.1, hWU hxW⟩, h.2.1, ?_⟩
  rw [nhdsWithin_restrict _ hxW hW, hS]
  exact h.2.2

/-- The viscosity subsolution property is local. -/
theorem isViscSub_of_locally
    (h : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ v, IsViscSub W Q v ∧ EqOn u v W) :
    IsViscSub U Q u := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun φ hφ x htouch ↦ ?_⟩
  · obtain ⟨W, hW, hxW, -, v, hv, heq⟩ := h x hx
    have hc : ContinuousAt v x := hv.1.continuousAt (hW.mem_nhds hxW)
    exact (hc.congr (Filter.mem_of_superset (hW.mem_nhds hxW)
      fun y hy ↦ (heq hy).symm)).continuousWithinAt
  · obtain ⟨W, -, hxW, -, v, hv, heq⟩ := h x hx
    rw [heq hxW]; exact hv.2.1 x hxW
  · obtain ⟨W, hW, hxW, hWU, v, hv, heq⟩ := h x htouch.1.2
    have hS := closure_posSet_inter_eq hW hWU heq
    have hxS : x ∈ closure (posSet v W) ∩ W := by rw [← hS]; exact ⟨htouch.1, hxW⟩
    refine hv.2.2 φ hφ x ⟨hxS, by rw [htouch.2.1, heq hxW], ?_⟩
    have h2 := htouch.2.2
    rw [nhdsWithin_restrict _ hxW hW, hS] at h2
    filter_upwards [h2, self_mem_nhdsWithin] with y hy hyS
    rw [← heq hyS.2]; exact hy

open Classical in
/-- **Gluing.** If `u` is a viscosity supersolution in `U`, `v` one in an open `W ⊆ U`, and
`v = u` on `W \ K` for a closed `K ⊆ W`, then the function equal to `v` on `W` and to `u`
elsewhere is a viscosity supersolution in `U`. -/
theorem isViscSuper_piecewise (hU : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U) {K : Set (E d)}
    (hK : IsClosed K) (hKW : K ⊆ W) (hu : IsViscSuper U Q u) (hv : IsViscSuper W Q v)
    (heq : ∀ y ∈ W \ K, v y = u y) : IsViscSuper U Q (W.piecewise v u) := by
  refine isViscSuper_of_locally hU fun x hx ↦ ?_
  by_cases hxW : x ∈ W
  · exact ⟨W, hW, hxW, hWU, v, hv, fun y hy ↦ piecewise_eq_of_mem _ _ _ hy⟩
  · refine ⟨U \ K, hU.sdiff hK, ⟨hx, fun h ↦ hxW (hKW h)⟩, diff_subset, u,
      hu.mono (hU.sdiff hK) diff_subset, fun y hy ↦ ?_⟩
    by_cases hyW : y ∈ W
    · rw [piecewise_eq_of_mem _ _ _ hyW]; exact heq y ⟨hyW, hy.2⟩
    · exact piecewise_eq_of_notMem _ _ _ hyW

open Classical in
/-- **Gluing** for viscosity subsolutions (same hypotheses as `isViscSuper_piecewise`). -/
theorem isViscSub_piecewise (hU : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U) {K : Set (E d)}
    (hK : IsClosed K) (hKW : K ⊆ W) (hu : IsViscSub U Q u) (hv : IsViscSub W Q v)
    (heq : ∀ y ∈ W \ K, v y = u y) : IsViscSub U Q (W.piecewise v u) := by
  refine isViscSub_of_locally fun x hx ↦ ?_
  by_cases hxW : x ∈ W
  · exact ⟨W, hW, hxW, hWU, v, hv, fun y hy ↦ piecewise_eq_of_mem _ _ _ hy⟩
  · refine ⟨U \ K, hU.sdiff hK, ⟨hx, fun h ↦ hxW (hKW h)⟩, diff_subset, u,
      hu.mono (hU.sdiff hK) diff_subset, fun y hy ↦ ?_⟩
    by_cases hyW : y ∈ W
    · rw [piecewise_eq_of_mem _ _ _ hyW]; exact heq y ⟨hyW, hy.2⟩
    · exact piecewise_eq_of_notMem _ _ _ hyW

end Locality

/-! ### Supersolutions above a strict subsolution are negative at their zeros -/

/-- At a free boundary point, a continuous nonnegative function vanishes. -/
theorem eq_zero_of_mem_freeBoundary {U : Set (E d)} {u : E d → ℝ} (hU : IsOpen U)
    (hc : ContinuousOn u U) (hnn : ∀ y ∈ U, 0 ≤ u y) {x : E d} (hx : x ∈ freeBoundary u U) :
    u x = 0 := by
  refine le_antisymm (not_lt.1 fun hpos ↦ ?_) (hnn x hx.2)
  apply hx.1.2
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [hU.mem_nhds hx.2,
    (hc.continuousAt (hU.mem_nhds hx.2)).eventually (lt_mem_nhds hpos)] with y hyU hy
  exact ⟨hyU, hy⟩

/-- **Test-function step.** Let `u` be a viscosity supersolution in `U`, `x ∈ U` with
`u(x) = 0`, and `g ∈ C²` with `g ≤ u` in `U`, `g(x) = 0` and `|∇g(x)| > Q(x) > 0`. This is
impossible: with `ν = ∇g(x)/|∇g(x)|`, `s = (y - x)·ν` and `Q(x) < λ < |∇g(x)|`, the polynomial
`φ(y) = λ s + B s² - K |y - x|²` (with `K` a second-order Taylor constant of `g` and
`B = dK + 1`) touches `u` from below at `x` and has `Δφ = 2 > 0`, `|∇φ(x)| = λ > Q(x)`. -/
theorem IsViscSuper.false_of_touch_strictSub {U : Set (E d)} {Q u g : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSuper U Q u) {x : E d} (hx : x ∈ U) (hux : u x = 0)
    (hgu : ∀ y ∈ U, g y ≤ u y) (hg : ContDiff ℝ 2 g) (hgx : g x = 0) (hQ : 0 < Q x)
    (hgrad : Q x < ‖∇ g x‖) : False := by
  set a := ‖∇ g x‖ with ha_def
  have ha : 0 < a := hQ.trans hgrad
  set ν : E d := a⁻¹ • ∇ g x with hν_def
  have hν : ‖ν‖ = 1 := by
    rw [hν_def, norm_smul, norm_inv, norm_norm, ← ha_def, inv_mul_cancel₀ ha.ne']
  have hgν : ∇ g x = a • ν := by rw [hν_def, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hfd : ∀ w, fderiv ℝ g x w = a * ⟪w, ν⟫ := by
    intro w
    have : fderiv ℝ g x w = ⟪∇ g x, w⟫ := (InnerProductSpace.toDual_symm_apply).symm
    rw [this, hgν, real_inner_smul_left, real_inner_comm]
  set lam := (Q x + a) / 2 with hlam
  have hlam1 : Q x < lam := by rw [hlam]; linarith
  have hlam2 : lam < a := by rw [hlam]; linarith
  have hlam0 : 0 < lam := hQ.trans hlam1
  obtain ⟨C, hC⟩ := exists_taylor_two_bound hg x
  set K := max C 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hCK : C ≤ K := le_max_left _ _
  set B : ℝ := (d : ℝ) * K + 1 with hB
  have hB0 : 0 < B := by positivity
  set φ : E d → ℝ := fun y ↦ lam * ⟪y - x, ν⟫ + B * ⟪y - x, ν⟫ ^ 2 - K * ‖y - x‖ ^ 2
    with hφ_def
  have hφ : ContDiff ℝ ∞ φ := by
    have h1 : ContDiff ℝ ∞ fun y : E d ↦ ⟪y - x, ν⟫ :=
      (contDiff_id.sub contDiff_const).inner ℝ contDiff_const
    have h2 : ContDiff ℝ ∞ fun y : E d ↦ ‖y - x‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    exact ((contDiff_const.mul h1).add (contDiff_const.mul (h1.pow 2))).sub
      (contDiff_const.mul h2)
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_of_smooth hφ
  -- the 2-jet of `φ` at `x`
  have hjet : ∀ w : E d, φ x = 0 ∧ fderiv ℝ φ x w = lam * ⟪w, ν⟫ ∧
      iteratedFDeriv ℝ 2 φ x ![w, w] = 2 * (B * ⟪w, ν⟫ ^ 2 - K * ‖w‖ ^ 2) := by
    intro w
    refine iteratedFDeriv_two_eq_of_isLittleO hφ2 ((isLittleO_zero _ _).congr_left fun t ↦ ?_)
    simp only [hφ_def, add_sub_cancel_left, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hφx : φ x = 0 := (hjet 0).1
  have hlap : Δ φ x = 2 := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    simp_rw [fun i ↦ (hjet ((EuclideanSpace.basisFun (Fin d) ℝ) i)).2.2]
    have hn : ∀ i, ‖(EuclideanSpace.basisFun (Fin d) ℝ) i‖ = 1 :=
      fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.1 i
    have hs : ∑ i, ⟪(EuclideanSpace.basisFun (Fin d) ℝ) i, ν⟫ ^ 2 = 1 := by
      have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner ν ν
      rw [real_inner_self_eq_norm_sq, hν, one_pow] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [real_inner_comm ν, sq]
    simp_rw [hn, one_pow, mul_one, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs, hB]
    ring
  have hgradφ : lam ≤ ‖∇ φ x‖ := by
    have h1 : ⟪∇ φ x, ν⟫ = lam := by
      have : ⟪∇ φ x, ν⟫ = fderiv ℝ φ x ν := InnerProductSpace.toDual_symm_apply
      rw [this, (hjet ν).2.1, real_inner_self_eq_norm_sq, hν]; ring
    have h2 := real_inner_le_norm (∇ φ x) ν
    rw [hν, mul_one, h1] at h2
    exact h2
  -- `φ` touches `u` from below at `x`
  set ρ := min ((a - lam) / B) (lam / B) with hρ
  have hρ0 : 0 < ρ := lt_min (div_pos (by linarith) hB0) (div_pos hlam0 hB0)
  have htouch : TouchesBelow φ u U x := by
    refine ⟨hx, by rw [hφx, hux], mem_nhdsWithin_of_mem_nhds ?_⟩
    filter_upwards [hU.mem_nhds hx, hC, ball_mem_nhds x hρ0] with y hyU hyC hyρ
    have hu0 := hu.2.1 y hyU
    have hgy := hgu y hyU
    rw [hgx, sub_zero, hfd] at hyC
    set s := ⟪y - x, ν⟫ with hs
    set r := ‖y - x‖ with hr
    have hsr : |s| ≤ r := by
      have := abs_real_inner_le_norm (y - x) ν
      rwa [hν, mul_one] at this
    have hrρ : r < ρ := by rw [hr, ← dist_eq_norm]; exact hyρ
    have hBr1 : B * r < a - lam := by
      have := (lt_of_lt_of_le hrρ (min_le_left _ _))
      rwa [lt_div_iff₀ hB0, mul_comm] at this
    have hBr2 : B * r < lam := by
      have := (lt_of_lt_of_le hrρ (min_le_right _ _))
      rwa [lt_div_iff₀ hB0, mul_comm] at this
    have hBs : B * |s| ≤ B * r := mul_le_mul_of_nonneg_left hsr hB0.le
    have hr0 : 0 ≤ r ^ 2 := sq_nonneg _
    have hKC : C * r ^ 2 ≤ K * r ^ 2 := mul_le_mul_of_nonneg_right hCK hr0
    have hKr : 0 ≤ K * r ^ 2 := mul_nonneg hK0 hr0
    change lam * s + B * s ^ 2 - K * r ^ 2 ≤ u y
    rcases le_or_gt s 0 with hs0 | hs0
    · rw [abs_of_nonpos hs0] at hBs
      have : 0 ≤ lam + B * s := by linarith
      have : s * (lam + B * s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs0 this
      linarith
    · rw [abs_of_pos hs0] at hBs
      have hgl := (abs_le.1 hyC).1
      have : 0 ≤ s * (a - lam - B * s) := mul_nonneg hs0.le (by linarith)
      linarith
  rcases hu.2.2 φ hφ x hx htouch with h | ⟨-, h⟩
  · rw [hlap] at h; norm_num at h
  · linarith

/-- If `u` is a viscosity supersolution in `U` with `u ≥ g` in `U`, where `g` is a smooth
strict subsolution and `Q > 0`, then `g(x) < 0` at every zero `x ∈ U` of `u`. (This replaces the
claim "`u > g` in `U`" in the proof of Lemma 2.7, which does not follow: `Δg ≥ 0` is not strict.) -/
theorem IsViscSuper.strictSub_lt_zero {U : Set (E d)} {Q u g : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSuper U Q u) (hg : IsStrictSub U Q g) (hgu : ∀ y ∈ U, g y ≤ u y) {x : E d}
    (hx : x ∈ U) (hux : u x = 0) (hQ : 0 < Q x) : g x < 0 := by
  obtain ⟨hg2, a₀, ha₀, δ₀, hδ₀, -, h2⟩ := hg
  refine lt_of_le_of_ne (hux ▸ hgu x hx) fun hgx ↦ ?_
  have hq := h2 x (subset_closure hx) (by rw [hgx, abs_zero]; exact ha₀.le)
  have hlt : Q x ^ 2 < ‖∇ g x‖ ^ 2 := by
    have : 0 < δ₀ * Q x ^ 2 := by positivity
    linarith
  exact hu.false_of_touch_strictSub hU hx hux hgu hg2 hgx hQ
    (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt)

/-! ### Lemma 2.7 -/

open Classical in
/-- **Lemma 2.7**. Let `u` be Perron's smallest supersolution above a
smooth strict subsolution `g`. Assume (outputs of Proposition 6.1) that `u` is a viscosity
supersolution in `U` and continuous on `Ū`. Then every free boundary point `x` has a ball
`B_r(x) ⊂⊂ U` in which `u` is a local smallest supersolution.

Proof: `g(x) < 0` by `IsViscSuper.strictSub_lt_zero`, so `g < 0` on some `B̄_r(x) ⊆ U`;
a competitor `v` on `B_r(x)` extended by `u` lies in `𝒮_g`, hence `v ≥ u`. -/
theorem perronSmallest_isLocalSmallestSuper_near_fb {U : Set (E d)} {Q g : E d → ℝ}
    (hU : IsOpen U) (hQ : ∀ y ∈ U, 0 < Q y) (hg : IsStrictSub U Q g)
    (hne : (perronSuperClass U Q g).Nonempty)
    (hsuper : IsViscSuper U Q (perronSmallest U Q g))
    (hcont : ContinuousOn (perronSmallest U Q g) (closure U)) {x : E d}
    (hx : x ∈ freeBoundary (perronSmallest U Q g) U) :
    ∃ r > 0, closedBall x r ⊆ U ∧ IsLocalSmallestSuper (ball x r) Q (perronSmallest U Q g) := by
  set u := perronSmallest U Q g with hu_def
  have hxU : x ∈ U := hx.2
  have hux : u x = 0 := eq_zero_of_mem_freeBoundary hU hsuper.1 hsuper.2.1 hx
  have hgu : ∀ y ∈ U, g y ≤ u y := fun y hy ↦ le_perronSmallest' hne (subset_closure hy)
  have hgx : g x < 0 := hsuper.strictSub_lt_zero hU hg hgu hxU hux (hQ x hxU)
  have hgc : Continuous g := hg.1.continuous
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.eventually_nhds_iff.1
    ((show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hxU).and
      (hgc.continuousAt.eventually (gt_mem_nhds hgx)))
  set r := r₁ / 2 with hr
  have hr0 : 0 < r := half_pos hr₁
  have hB : ∀ y ∈ closedBall x r, y ∈ U ∧ g y < 0 :=
    fun y hy ↦ hr₁' (lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hr₁))
  have hBU : closedBall x r ⊆ U := fun y hy ↦ (hB y hy).1
  have hbU : ball x r ⊆ U := ball_subset_closedBall.trans hBU
  refine ⟨r, hr0, hBU, hsuper.mono isOpen_ball hbU, ?_⟩
  intro y s hs hys v hv hvu z hz
  -- the glued competitor
  set w := (ball x r).piecewise v u with hw
  have hw_out : ∀ z ∉ closedBall y s, w z = u z := by
    intro z hz'
    by_cases hzb : z ∈ ball x r
    · rw [hw, piecewise_eq_of_mem _ _ _ hzb]
      exact hvu z ⟨hzb, fun h ↦ hz' (ball_subset_closedBall h)⟩
    · rw [hw, piecewise_eq_of_notMem _ _ _ hzb]
  have hwS : w ∈ perronSuperClass U Q g := by
    refine ⟨fun z hz ↦ ?_, ?_, fun z hz ↦ ?_⟩
    · by_cases hzb : z ∈ ball x r
      · have hc : ContinuousAt v z := hv.1.continuousAt (isOpen_ball.mem_nhds hzb)
        exact (hc.congr (Filter.mem_of_superset (isOpen_ball.mem_nhds hzb)
          fun y hy ↦ (piecewise_eq_of_mem _ _ _ hy).symm)).continuousWithinAt
      · have hzK : z ∉ closedBall y s := fun h ↦ hzb (hys h)
        refine (hcont z hz).congr_of_eventuallyEq ?_ (hw_out z hzK)
        exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset
          (isClosed_closedBall.isOpen_compl.mem_nhds hzK) fun y hy ↦ hw_out y hy)
    · exact isViscSuper_piecewise hU isOpen_ball hbU isClosed_closedBall hys hsuper hv
        fun z hz ↦ hvu z ⟨hz.1, fun h ↦ hz.2 (ball_subset_closedBall h)⟩
    · by_cases hzb : z ∈ ball x r
      · rw [hw, piecewise_eq_of_mem _ _ _ hzb]
        exact max_le (((hB z (ball_subset_closedBall hzb)).2).le.trans (hv.2.1 z hzb))
          (hv.2.1 z hzb)
      · rw [hw, piecewise_eq_of_notMem _ _ _ hzb]
        exact le_perronSmallest hne hz
  have := perronSmallest_le hwS (subset_closure (hbU hz))
  rwa [hw, piecewise_eq_of_mem _ _ _ hz] at this

/-- **Lemma 2.7** in the standing setting: the positivity of `Q` and the nonemptiness of `𝒮_g`
are automatic. -/
theorem Setting.perronSmallest_isLocalSmallestSuper_near_fb (S : Setting d) {g : E d → ℝ}
    (hg : IsStrictSub S.U S.Q g) (hsuper : IsViscSuper S.U S.Q (perronSmallest S.U S.Q g))
    (hcont : ContinuousOn (perronSmallest S.U S.Q g) (closure S.U)) {x : E d}
    (hx : x ∈ freeBoundary (perronSmallest S.U S.Q g) S.U) :
    ∃ r > 0, closedBall x r ⊆ S.U ∧
      IsLocalSmallestSuper (ball x r) S.Q (perronSmallest S.U S.Q g) :=
  PerronVariational.perronSmallest_isLocalSmallestSuper_near_fb S.isOpen
    (fun y hy ↦ S.Qmin_pos.trans_le (S.Q_mem y (subset_closure hy)).1) hg
    (S.perronSuperClass_nonempty hg.1.continuous.continuousOn) hsuper hcont hx

/-! ### Comparison with strict `C²` barriers and the dual of Lemma 2.7 -/


/-- **Comparison with a strict barrier.** Let `v` be a viscosity subsolution in an open `W`,
`K ⊆ W` compact and `H ∈ C²` with `ΔH < 0` on `K` and `|∇H| < Q` at the points of `K` where
`H < 0`. If `v ≤ H₊` on `W \ K`, then `v ≤ H₊` on `K`.

Proof: otherwise let `t > 0` be the maximum of `v - H` over `\overline{{v > 0} ∩ K}`, attained at
`z`; then `v ≤ (H + t)₊` on `W` with equality at `z`, and a smooth quadratic majorant of `H + t`
at `z` (`exists_smooth_ge_of_contDiff_two`) contradicts the subsolution property at `z`. -/
theorem IsViscSub.le_max_of_barrier {W K : Set (E d)} {Q v H : E d → ℝ} (hd : 0 < d)
    (hW : IsOpen W) (hv : IsViscSub W Q v) (hK : IsCompact K) (hKW : K ⊆ W)
    (hH : ContDiff ℝ 2 H) (hlap : ∀ z ∈ K, Δ H z < 0)
    (hgrad : ∀ z ∈ K, H z < 0 → ‖∇ H z‖ < Q z)
    (hout : ∀ y ∈ W \ K, v y ≤ max (H y) 0) : ∀ y ∈ K, v y ≤ max (H y) 0 := by
  intro y hy
  by_contra hcon
  push Not at hcon
  have hvy : 0 < v y := lt_of_le_of_lt (le_max_right _ _) hcon
  have hHy : H y < v y := lt_of_le_of_lt (le_max_left _ _) hcon
  set A := posSet v W ∩ K with hA
  have hAK : closure A ⊆ K := hK.isClosed.closure_subset_iff.2 inter_subset_right
  have hAc : IsCompact (closure A) := hK.of_isClosed_subset isClosed_closure hAK
  have hF : ContinuousOn (fun w ↦ v w - H w) (closure A) :=
    ((hv.1.mono (hAK.trans hKW)).sub hH.continuous.continuousOn)
  have hyA : y ∈ A := ⟨⟨hKW hy, hvy⟩, hy⟩
  obtain ⟨z, hzA, hzmax⟩ := hAc.exists_isMaxOn ⟨y, subset_closure hyA⟩ hF
  set t := v z - H z with ht
  have hty : v y - H y ≤ t := hzmax (subset_closure hyA)
  have ht0 : 0 < t := by linarith
  have hzK : z ∈ K := hAK hzA
  have hzW : z ∈ W := hKW hzK
  have hle : ∀ w ∈ W, v w ≤ max (H w + t) 0 := by
    intro w hw
    by_cases hwK : w ∈ K
    · by_cases hvw : 0 < v w
      · have := hzmax (subset_closure (⟨⟨hw, hvw⟩, hwK⟩ : w ∈ A))
        simp only [mem_setOf_eq] at this
        exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (not_lt.1 hvw)
    · exact (hout w ⟨hw, hwK⟩).trans (max_le_max (by linarith) le_rfl)
  set η : ℝ := -Δ H z / (4 * d) with hη
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hη0 : 0 < η := div_pos (by linarith [hlap z hzK]) (by positivity)
  obtain ⟨φ, hφs, hφz, hφg, hφl, hφle⟩ := exists_smooth_ge_of_contDiff_two
    (hH.add (contDiff_const (c := t))) z hη0
  rw [laplacian_add_const hH.contDiffAt, finrank_euclideanSpace_fin] at hφl
  rw [gradient_add_const] at hφg
  have hvz : v z = H z + t := by rw [ht]; ring
  have htouch : TouchesAbove (fun w ↦ max (φ w) 0) v (closure (posSet v W) ∩ W) z := by
    refine ⟨⟨closure_mono inter_subset_left hzA, hzW⟩, ?_, ?_⟩
    · have hφv : φ z = v z := by rw [hφz]; exact hvz.symm
      simp only [hφv]; exact max_eq_left (hv.2.1 z hzW)
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hzW),
        mem_nhdsWithin_of_mem_nhds hφle] with w hw hw'
      exact (hle w hw).trans (max_le_max hw' le_rfl)
  rcases hv.2.2 φ hφs z htouch with h | ⟨h1, h2⟩
  · have : Δ φ z = Δ H z / 2 := by
      rw [hφl, hη]; field_simp; ring
    linarith [hlap z hzK]
  · have hHz : H z < 0 := by rw [hφz] at h1; linarith
    have := hgrad z hzK hHz
    rw [hφg] at h2
    linarith

/-- **Barrier step of the dual of Lemma 2.7.** Let `g` be a strict supersolution with constants
`a₀, δ₀`, and `B̄_r(x) ⊆ U` a ball on which `g > -a₀/2` and `Q ≥ q₀ > 0`. If `v` is a viscosity
subsolution in `B_r(x)`, `K ⊆ B_r(x)` is compact and `v ≤ g₊` on `B_r(x) \ K`, then `v ≤ g₊` on
`K`. (Comparison with the barriers `g + ε(r² - |y - x|²)`, `ε → 0`.) -/
theorem IsViscSub.le_max_of_isStrictSuperWith {U : Set (E d)} {Q g v : E d → ℝ} (hd : 0 < d)
    {a₀ δ₀ : ℝ} (hg : IsStrictSuperWith U Q g a₀ δ₀) {x : E d} {r : ℝ}
    (hBU : closedBall x r ⊆ U) (hga : ∀ y ∈ closedBall x r, -a₀ / 2 < g y) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hQ : ∀ y ∈ closedBall x r, q₀ ≤ Q y) (hv : IsViscSub (ball x r) Q v)
    {K : Set (E d)} (hK : IsCompact K) (hKB : K ⊆ ball x r)
    (hout : ∀ y ∈ ball x r \ K, v y ≤ max (g y) 0) : ∀ y ∈ K, v y ≤ max (g y) 0 := by
  obtain ⟨hg2, ha₀, hδ₀, hg1, hg2'⟩ := hg
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- the paraboloid `ψ(y) = r² - |y - x|²`
  set ψ : E d → ℝ := fun y ↦ r ^ 2 - ‖y - x‖ ^ 2 with hψ
  have hψs : ContDiff ℝ 2 ψ :=
    contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hψjet : ∀ z w : E d, ψ z = r ^ 2 - ‖z - x‖ ^ 2 ∧
      fderiv ℝ ψ z w = -2 * ⟪z - x, w⟫ ∧ iteratedFDeriv ℝ 2 ψ z ![w, w] = 2 * (-‖w‖ ^ 2) := by
    intro z w
    refine iteratedFDeriv_two_eq_of_isLittleO hψs ((isLittleO_zero _ _).congr_left fun t ↦ ?_)
    have : z + t • w - x = (z - x) + t • w := by abel
    simp only [hψ, this, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hψlap : ∀ z, Δ ψ z = -2 * d := by
    intro z
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ψ
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    simp_rw [fun i ↦ (hψjet z ((EuclideanSpace.basisFun (Fin d) ℝ) i)).2.2]
    simp
    ring
  have hψgrad : ∀ z, ‖fderiv ℝ ψ z‖ ≤ 2 * ‖z - x‖ := by
    intro z
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
    rw [(hψjet z w).2.1, Real.norm_eq_abs, abs_mul, abs_neg, abs_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) zero_le_two
  have hψnn : ∀ y ∈ ball x r, 0 ≤ ψ y := by
    intro y hy
    have h1 : ‖y - x‖ < r := by rw [← dist_eq_norm]; exact hy
    simp only [hψ]
    nlinarith [norm_nonneg (y - x)]
  have hψle : ∀ y ∈ ball x r, ψ y ≤ r ^ 2 := fun y _ ↦ by
    simp only [hψ]; nlinarith [norm_nonneg (y - x)]
  intro y hy
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (hKB hy)
  set ε₀ := min (δ₀ * q₀ / (8 * r)) (q₀ / (2 * r)) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hmain : ∀ ε, 0 < ε → ε ≤ ε₀ → v y ≤ max (g y + ε * ψ y) 0 := by
    intro ε hε hεle
    have hc1 : 2 * ε * r ≤ δ₀ * q₀ / 4 := by
      have := (hεle.trans (min_le_left _ _))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hc2 : 2 * ε * r ≤ q₀ := by
      have := (hεle.trans (min_le_right _ _))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hψε : ContDiff ℝ 2 (ε • ψ) := hψs.const_smul ε
    have hHs : ContDiff ℝ 2 (g + ε • ψ) := hg2.add hψε
    have hHapp : ∀ w, (g + ε • ψ) w = g w + ε * ψ w := fun w ↦ rfl
    have key := hv.le_max_of_barrier hd isOpen_ball hK hKB hHs ?_ ?_ ?_ y hy
    · simpa [hHapp] using key
    · -- the barrier is strictly superharmonic
      intro z hz
      have hzB : z ∈ closedBall x r := ball_subset_closedBall (hKB hz)
      have hΔg : Δ g z ≤ 0 := hg1 z (subset_closure (hBU hzB)) (by linarith [hga z hzB])
      rw [hg2.contDiffAt.laplacian_add hψε.contDiffAt,
        InnerProductSpace.laplacian_smul ε hψs.contDiffAt, hψlap z, smul_eq_mul]
      nlinarith
    · -- gradient condition on the zero level set
      intro z hz hHz
      have hzb : z ∈ ball x r := hKB hz
      have hzB : z ∈ closedBall x r := ball_subset_closedBall hzb
      rw [hHapp] at hHz
      have hgz : g z < 0 := by nlinarith [hψnn z hzb]
      have hgabs : |g z| ≤ a₀ := by
        rw [abs_le]; constructor <;> linarith [hga z hzB]
      have hG := hg2' z (subset_closure (hBU hzB)) hgabs
      have hq := hQ z hzB
      have hfd : fderiv ℝ (g + ε • ψ) z = fderiv ℝ g z + ε • fderiv ℝ ψ z := by
        rw [fderiv_add (hg2.differentiable (by norm_num) z)
          (hψε.differentiable (by norm_num) z),
          fderiv_const_smul (hψs.differentiable (by norm_num) z)]
      have hbound : ‖∇ (g + ε • ψ) z‖ ≤ ‖∇ g z‖ + 2 * ε * r := by
        rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv, hfd]
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        have h1 := hψgrad z
        have h2 : ‖z - x‖ ≤ r := by rw [← dist_eq_norm]; exact hzB
        linarith [mul_le_mul_of_nonneg_left h1 hε.le, mul_le_mul_of_nonneg_left h2 hε.le]
      set G := ‖∇ g z‖
      have hG0 : 0 ≤ G := norm_nonneg _
      have hQ0 : 0 < Q z := hq₀.trans_le hq
      have hδQ : 0 < δ₀ * Q z ^ 2 := by positivity
      have hG2 : G ^ 2 ≤ Q z ^ 2 := by linarith [mul_nonneg hδ₀.le (sq_nonneg (Q z))]
      have hGq : G ≤ Q z := (pow_le_pow_iff_left₀ hG0 hQ0.le two_ne_zero).1 hG2
      set c := 2 * ε * r with hc
      have hc0 : 0 ≤ c := by positivity
      have e1 : c * G ≤ c * Q z := mul_le_mul_of_nonneg_left hGq hc0
      have e2 : c * Q z ≤ δ₀ * q₀ / 4 * Q z := mul_le_mul_of_nonneg_right hc1 hQ0.le
      have e3 : δ₀ * q₀ * Q z ≤ δ₀ * (Q z * Q z) := by
        have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ δ₀ * Q z)
        linarith
      have e4 : c * c ≤ δ₀ * q₀ / 4 * q₀ := mul_le_mul hc1 hc2 hc0 (by positivity)
      have e5 : δ₀ * q₀ * q₀ ≤ δ₀ * (Q z * Q z) := by
        have h1 := mul_le_mul hq hq hq₀.le hQ0.le
        linarith [mul_le_mul_of_nonneg_left h1 hδ₀.le]
      have hlt : (G + c) ^ 2 < Q z ^ 2 := by linarith
      have : G + c < Q z := lt_of_pow_lt_pow_left₀ 2 hQ0.le hlt
      linarith
    · -- outside `K`
      intro w hw
      exact (hout w hw).trans (max_le_max (by
        rw [hHapp]; nlinarith [hψnn w hw.1, hε.le]) le_rfl)
  -- let `ε → 0`
  by_contra hcon
  push Not at hcon
  set δ := v y - max (g y) 0 with hδ
  have hδ0 : 0 < δ := by linarith
  set ε := min ε₀ (δ / (2 * (r ^ 2 + 1))) with hε
  have hε0 : 0 < ε := lt_min hε₀pos (by positivity)
  have h1 := hmain ε hε0 (min_le_left _ _)
  have hεr : ε * r ^ 2 < δ := by
    have h2 : ε ≤ δ / (2 * (r ^ 2 + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith
  have hψy := hψle y (hKB hy)
  have h3 : max (g y + ε * ψ y) 0 ≤ max (g y) 0 + ε * r ^ 2 := by
    refine max_le ?_ (by nlinarith [le_max_right (g y) 0])
    nlinarith [le_max_left (g y) 0]
  linarith

open Classical in
/-- **Dual of Lemma 2.7** (not proved in the paper; needed for Theorem 1.1(iii), largest case,
where Lemma 6.3 needs a local largest subsolution). The dual argument needs the glued competitor
to satisfy `v ≤ g₊` in the ball; a test function at `x` alone fails when `g(x) = 0 = |∇g(x)|`, so
we compare with strict barriers. Let `u` be Perron's largest subsolution below a smooth strict
supersolution `g`, and assume (outputs of Proposition 6.2) that `u` is a viscosity subsolution
in `U` and continuous on `Ū`. Then every free boundary point `x` has a ball `B_r(x) ⊂⊂ U` in
which `u` is a local largest subsolution.

Proof: `g(x) ≥ 0` since `x ∈ \overline{{u > 0}}` and `u ≤ g₊`. Choose `B̄_r(x) ⊆ U` with
`g > -a₀/2` there. For a competitor `v` in `B_r(x)`, equal to `u` off `B ⊂⊂ B_r(x)`, comparison
with the strict barriers `g + ε(r² - |y - x|²)` gives `v ≤ g₊`
(`IsViscSub.le_max_of_isStrictSuperWith`); hence `v` extended by `u` lies in `𝒮^g` and `v ≤ u`. -/
theorem perronLargest_isLocalLargestSub_near_fb {U : Set (E d)} {Q g : E d → ℝ} (hd : 0 < d)
    (hU : IsOpen U) {q₀ : ℝ} (hq₀ : 0 < q₀) (hQ : ∀ y ∈ U, q₀ ≤ Q y)
    (hg : IsStrictSuper U Q g) (hsub : IsViscSub U Q (perronLargest U Q g))
    (hcont : ContinuousOn (perronLargest U Q g) (closure U)) {x : E d}
    (hx : x ∈ freeBoundary (perronLargest U Q g) U) :
    ∃ r > 0, closedBall x r ⊆ U ∧ IsLocalLargestSub (ball x r) Q (perronLargest U Q g) := by
  set u := perronLargest U Q g with hu_def
  obtain ⟨a₀, δ₀, hgw⟩ := isStrictSuper_iff.1 hg
  have hxU : x ∈ U := hx.2
  have hgc : Continuous g := hg.1.continuous
  have hug : ∀ y ∈ closure U, u y ≤ max (g y) 0 := fun y hy ↦ perronLargest_le hy
  -- `g(x) ≥ 0`
  have hgx : 0 ≤ g x := by
    have hsub' : posSet u U ⊆ {y | 0 ≤ g y} := by
      rintro y ⟨hyU, hy⟩
      by_contra hneg
      simp only [mem_setOf_eq, not_le] at hneg
      have := hug y (subset_closure hyU)
      rw [max_eq_right hneg.le] at this
      linarith
    exact closure_minimal hsub' (isClosed_le continuous_const hgc)
      (frontier_subset_closure hx.1)
  have ha₀ : 0 < a₀ := hgw.2.1
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.eventually_nhds_iff.1
    ((show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hxU).and
      (hgc.continuousAt.eventually (lt_mem_nhds (show -a₀ / 2 < g x by linarith))))
  set r := r₁ / 2 with hr
  have hr0 : 0 < r := half_pos hr₁
  have hB : ∀ y ∈ closedBall x r, y ∈ U ∧ -a₀ / 2 < g y :=
    fun y hy ↦ hr₁' (lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hr₁))
  have hBU : closedBall x r ⊆ U := fun y hy ↦ (hB y hy).1
  have hbU : ball x r ⊆ U := ball_subset_closedBall.trans hBU
  refine ⟨r, hr0, hBU, hsub.mono isOpen_ball hbU, ?_⟩
  intro y s hs hys v hv hvu z hz
  -- `v ≤ g₊` in `B_r(x)`
  have hvg : ∀ w ∈ ball x r, v w ≤ max (g w) 0 := by
    have hK := hv.le_max_of_isStrictSuperWith hd hgw hBU (fun w hw ↦ (hB w hw).2) hq₀
      (fun w hw ↦ hQ w (hBU hw)) (isCompact_closedBall y s) hys (by
        intro w hw
        rw [hvu w ⟨hw.1, fun h ↦ hw.2 (ball_subset_closedBall h)⟩]
        exact hug w (subset_closure (hbU hw.1)))
    intro w hw
    by_cases hwK : w ∈ closedBall y s
    · exact hK w hwK
    · rw [hvu w ⟨hw, fun h ↦ hwK (ball_subset_closedBall h)⟩]
      exact hug w (subset_closure (hbU hw))
  -- the glued competitor
  set w := (ball x r).piecewise v u with hw
  have hw_out : ∀ z ∉ closedBall y s, w z = u z := by
    intro z hz'
    by_cases hzb : z ∈ ball x r
    · rw [hw, piecewise_eq_of_mem _ _ _ hzb]
      exact hvu z ⟨hzb, fun h ↦ hz' (ball_subset_closedBall h)⟩
    · rw [hw, piecewise_eq_of_notMem _ _ _ hzb]
  have hwS : w ∈ perronSubClass U Q g := by
    refine ⟨fun z hz ↦ ?_, ?_, fun z hz ↦ ?_⟩
    · by_cases hzb : z ∈ ball x r
      · have hc : ContinuousAt v z := hv.1.continuousAt (isOpen_ball.mem_nhds hzb)
        exact (hc.congr (Filter.mem_of_superset (isOpen_ball.mem_nhds hzb)
          fun y hy ↦ (piecewise_eq_of_mem _ _ _ hy).symm)).continuousWithinAt
      · have hzK : z ∉ closedBall y s := fun h ↦ hzb (hys h)
        refine (hcont z hz).congr_of_eventuallyEq ?_ (hw_out z hzK)
        exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset
          (isClosed_closedBall.isOpen_compl.mem_nhds hzK) fun y hy ↦ hw_out y hy)
    · exact isViscSub_piecewise hU isOpen_ball hbU isClosed_closedBall hys hsub hv
        fun z hz ↦ hvu z ⟨hz.1, fun h ↦ hz.2 (ball_subset_closedBall h)⟩
    · by_cases hzb : z ∈ ball x r
      · rw [hw, piecewise_eq_of_mem _ _ _ hzb]
        exact hvg z hzb
      · rw [hw, piecewise_eq_of_notMem _ _ _ hzb]
        exact hug z hz
  have := le_perronLargest hwS (subset_closure (hbU hz))
  rwa [hw, piecewise_eq_of_mem _ _ _ hz] at this

/-- **Dual of Lemma 2.7** in the standing setting. -/
theorem Setting.perronLargest_isLocalLargestSub_near_fb (S : Setting d) {g : E d → ℝ}
    (hg : IsStrictSuper S.U S.Q g) (hsub : IsViscSub S.U S.Q (perronLargest S.U S.Q g))
    (hcont : ContinuousOn (perronLargest S.U S.Q g) (closure S.U)) {x : E d}
    (hx : x ∈ freeBoundary (perronLargest S.U S.Q g) S.U) :
    ∃ r > 0, closedBall x r ⊆ S.U ∧
      IsLocalLargestSub (ball x r) S.Q (perronLargest S.U S.Q g) :=
  PerronVariational.perronLargest_isLocalLargestSub_near_fb (by linarith [S.two_le]) S.isOpen
    S.Qmin_pos (fun y hy ↦ (S.Q_mem y (subset_closure hy)).1) hg hsub hcont hx

end PerronVariational

end
