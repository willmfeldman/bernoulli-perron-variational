/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import PerronVariational.Defs.Semilinear
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import PerronVariational.Inner.EpsIdentity
import PerronVariational.Inner.WeakGrad
import PerronVariational.Semilinear.Calculus

/-!
# The weak heat equation in `{u > 0}` in the limit ((4.5))

The weak heat equation (4.5), proved in Section 4.2 of F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981, for the `ε → 0` limit of the semilinear approximations.

* `Inner.integral_laplacian_mul_eq_neg`: `∫ Δf g = -∫ ∇f · ∇g` for `f ∈ C²(U)` and `g` Lipschitz
  with compact support in `U` (Rademacher integration by parts, after a Lipschitz extension of the
  first derivatives of `f` near `spt g`);
* `Inner.integral_lapₓ_mul_eq_neg`: its space-time version on `U_∞` (Fubini);
* `Inner.weakHeat_of_tendsto`: (4.5) for the limit of the semilinear approximations. The paper's
  Definition 3.7 does not contain (4.5), but the proof of Theorem 3.10 uses it; here it is a
  conclusion of Proposition 4.1 and Theorem 3.9 and a hypothesis of Theorem 3.10.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-- A `C¹` function on an open set agrees near a compact subset with a globally Lipschitz
function. -/
theorem exists_lipschitzWith_eqOn_thickening {U : Set (E d)} (hU : IsOpen U) {h : E d → ℝ}
    (hh : ContDiffOn ℝ 1 h U) {K : Set (E d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ H : E d → ℝ, ∃ C : ℝ≥0, LipschitzWith C H ∧ ∃ δ > 0, EqOn h H (thickening δ K) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hS : IsCompact (cthickening δ K) := hK.cthickening
  obtain ⟨L, hL⟩ := hS.exists_bound_of_continuousOn
    ((hh.continuousOn_fderiv_of_isOpen hU le_rfl).mono hδU)
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (hh.continuousOn.mono hδU)
  set C : ℝ := max (max L (4 * M / δ)) 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hlip : LipschitzOnWith (Real.toNNReal C) h (thickening (δ / 2) K) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
    rw [Real.coe_toNNReal _ hC0]
    have hyS : y ∈ cthickening δ K :=
      thickening_subset_cthickening _ _ (thickening_mono (by linarith) _ hy)
    have hzS : z ∈ cthickening δ K :=
      thickening_subset_cthickening _ _ (thickening_mono (by linarith) _ hz)
    by_cases hyz : dist z y < δ / 2
    · have hball : ball y (δ / 2) ⊆ thickening δ K := by
        intro w hw
        obtain ⟨k, hk, hyk⟩ := mem_thickening_iff.1 hy
        refine mem_thickening_iff.2 ⟨k, hk, ?_⟩
        calc dist w k ≤ dist w y + dist y k := dist_triangle _ _ _
          _ < δ / 2 + δ / 2 := add_lt_add (mem_ball.1 hw) hyk
          _ = δ := add_halves δ
      have hdiff : ∀ w ∈ ball y (δ / 2), DifferentiableAt ℝ h w := fun w hw ↦
        (hh.differentiableOn (by norm_num)).differentiableAt
          (hU.mem_nhds (hδU (thickening_subset_cthickening _ _ (hball hw))))
      have hbd : ∀ w ∈ ball y (δ / 2), ‖fderiv ℝ h w‖ ≤ L := fun w hw ↦
        hL w (thickening_subset_cthickening _ _ (hball hw))
      have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbd (convex_ball _ _)
        (mem_ball_self (half_pos hδ)) (mem_ball.2 hyz)
      rw [dist_comm (h y), dist_comm y, Real.dist_eq, dist_eq_norm, ← Real.norm_eq_abs]
      exact this.trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_left _ _)) (norm_nonneg _))
    · push Not at hyz
      have hMy := hM y hyS
      have hMz := hM z hzS
      rw [Real.norm_eq_abs] at hMy hMz
      have hM0 : 0 ≤ M := (abs_nonneg _).trans hMy
      rw [Real.dist_eq]
      calc |h y - h z| ≤ |h y| + |h z| := abs_sub _ _
        _ ≤ 2 * M := by linarith
        _ = 4 * M / δ * (δ / 2) := by field_simp; ring
        _ ≤ 4 * M / δ * dist y z := by
            rw [dist_comm]
            exact mul_le_mul_of_nonneg_left hyz (by positivity)
        _ ≤ C * dist y z :=
            mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _))
              dist_nonneg
  obtain ⟨H, hH, heq⟩ := hlip.extend_real
  exact ⟨H, _, hH, δ / 2, half_pos hδ, heq⟩

/-- `⟪∇f(x), v⟫ = Df(x) v`. -/
theorem inner_gradient_eq_fderiv (f : E d → ℝ) (x v : E d) : ⟪∇ f x, v⟫ = fderiv ℝ f x v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

/-- **Integration by parts against a Lipschitz function.** For `f ∈ C²(U)` and `g` Lipschitz
with compact support in `U`, `∫ Δf g = -∫ ∇f · ∇g`. -/
theorem integral_laplacian_mul_eq_neg {U : Set (E d)} (hU : IsOpen U) {f g : E d → ℝ}
    (hf : ContDiffOn ℝ 2 f U) {Cg : ℝ≥0} (hg : LipschitzWith Cg g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) :
    ∫ x, Δ f x * g x = -∫ x, ⟪∇ f x, ∇ g x⟫ := by
  set K := tsupport g with hKdef
  have hK : IsCompact K := hgc
  have hKm : MeasurableSet K := (isClosed_tsupport g).measurableSet
  set e := stdOrthonormalBasis ℝ (E d) with hedef
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  set D : Fin (Module.finrank ℝ (E d)) → E d → ℝ := fun i x ↦ fderiv ℝ f x (e i) with hDdef
  have hD : ∀ i, ContDiffOn ℝ 1 (D i) U := fun i ↦ hf1.clm_apply contDiffOn_const
  have hdiffD : ∀ i, ∀ x ∈ U, DifferentiableAt ℝ (D i) x := fun i x hx ↦
    ((hD i).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  choose H CH hH δ hδ hHeq using fun i ↦ exists_lipschitzWith_eqOn_thickening hU (hD i) hK hgU
  have hg0 : ∀ x, x ∉ K → g x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hdg0 : ∀ x, x ∉ K → fderiv ℝ g x = 0 := fun x hx ↦ fderiv_of_notMem_tsupport ℝ hx
  -- pointwise identities
  have hlap : ∀ x ∈ U, Δ f x = ∑ i, fderiv ℝ (D i) x (e i) := by
    intro x hx
    rw [laplacian_eq_sum_fderiv_fderiv]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hf1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
    simp only [D]
    rw [fderiv_clm_apply hdf (differentiableAt_const _)]
    simp [hedef]
  have hinner : ∀ x, ⟪∇ f x, ∇ g x⟫ = ∑ i, fderiv ℝ g x (e i) * D i x := by
    intro x
    rw [← e.sum_inner_mul_inner (∇ f x) (∇ g x)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_gradient_eq_fderiv, real_inner_comm, inner_gradient_eq_fderiv, mul_comm]
  -- integrability
  have hA : ∀ i, Integrable (fun x ↦ fderiv ℝ (D i) x (e i) * g x) := by
    intro i
    have hc : ContinuousOn (fun x ↦ fderiv ℝ (D i) x (e i) * g x) K :=
      ((((hD i).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).mono
        hgU).mul hg.continuous.continuousOn
    refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).1
      (hc.integrableOn_compact hK)
    by_contra h
    exact hx (by simp [hg0 x h])
  have hB : ∀ i, Integrable (fun x ↦ fderiv ℝ g x (e i) * D i x) := by
    intro i
    have hDi : IntegrableOn (D i) K := ((hD i).continuousOn.mono hgU).integrableOn_compact hK
    have hmeas : AEStronglyMeasurable (fun x ↦ fderiv ℝ g x (e i)) (volume.restrict K) :=
      (measurable_fderiv_apply_const ℝ g (e i)).aestronglyMeasurable
    have hbd : ∀ᵐ x ∂(volume.restrict K), ‖fderiv ℝ g x (e i)‖ ≤ Cg := by
      refine Eventually.of_forall fun x ↦ ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [e.orthonormal.1 i, mul_one]
      exact norm_fderiv_le_of_lipschitz ℝ hg
    refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).1
      (hDi.bdd_mul hmeas hbd)
    by_contra h
    exact hx (by simp [hdg0 x h])
  -- integration by parts in each direction
  have hibp : ∀ i, ∫ x, fderiv ℝ (D i) x (e i) * g x = -∫ x, fderiv ℝ g x (e i) * D i x := by
    intro i
    have h1 := (hH i).integral_lineDeriv_mul_eq (μ := volume) hg hgc (e i)
    have hL : ∀ x, lineDeriv ℝ (H i) x (e i) * g x = fderiv ℝ (D i) x (e i) * g x := by
      intro x
      by_cases hx : x ∈ K
      · have hev : H i =ᶠ[𝓝 x] D i :=
          Filter.mem_of_superset (isOpen_thickening.mem_nhds (self_subset_thickening (hδ i) K hx))
            fun y hy ↦ (hHeq i hy).symm
        have hd : HasFDerivAt (H i) (fderiv ℝ (D i) x) x :=
          (hdiffD i x (hgU hx)).hasFDerivAt.congr_of_eventuallyEq hev
        rw [(hd.hasLineDerivAt (e i)).lineDeriv]
      · simp [hg0 x hx]
    have hR : (fun x ↦ lineDeriv ℝ g x (-(e i)) * H i x) =ᵐ[volume]
        fun x ↦ -(fderiv ℝ g x (e i) * D i x) := by
      filter_upwards [hg.ae_differentiableAt] with x hx
      rw [hx.lineDeriv_eq_fderiv, map_neg]
      by_cases hxK : x ∈ K
      · rw [← hHeq i (self_subset_thickening (hδ i) K hxK)]
        ring
      · simp [hdg0 x hxK]
    rw [← integral_neg, ← integral_congr_ae hR, ← h1]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ (hL x).symm)
  calc ∫ x, Δ f x * g x = ∫ x, ∑ i, fderiv ℝ (D i) x (e i) * g x := by
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only
        by_cases hx : x ∈ U
        · rw [hlap x hx, Finset.sum_mul]
        · have hxK : x ∉ K := fun h ↦ hx (hgU h)
          simp [hg0 x hxK]
    _ = ∑ i, ∫ x, fderiv ℝ (D i) x (e i) * g x := integral_finsetSum _ fun i _ ↦ hA i
    _ = ∑ i, -∫ x, fderiv ℝ g x (e i) * D i x := Finset.sum_congr rfl fun i _ ↦ hibp i
    _ = -∫ x, ∑ i, fderiv ℝ g x (e i) * D i x := by
        rw [integral_finsetSum _ fun i _ ↦ hB i, Finset.sum_neg_distrib]
    _ = -∫ x, ⟪∇ f x, ∇ g x⟫ := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun x ↦ (hinner x).symm)

/-! ### Space-time version -/

theorem tsupport_slice_subset (φ : E d × ℝ → ℝ) (t : ℝ) :
    tsupport (fun x ↦ φ (x, t)) ⊆ {x | (x, t) ∈ tsupport φ} :=
  closure_minimal (fun _ hx ↦ subset_tsupport φ hx)
    ((isClosed_tsupport φ).preimage (continuous_id.prodMk continuous_const))

theorem hasCompactSupport_slice {φ : E d × ℝ → ℝ} (hφ : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun x ↦ φ (x, t)) :=
  IsCompact.of_isClosed_subset (hφ.image continuous_fst) (isClosed_tsupport _)
    fun x hx ↦ ⟨(x, t), tsupport_slice_subset φ t hx, rfl⟩

/-- A locally Lipschitz function with compact support on `ℝᵈ` is Lipschitz. -/
theorem LocallyLipschitz.exists_lipschitzWith_of_hasCompactSupport {g : E d → ℝ}
    (hg : LocallyLipschitz g) (hgc : HasCompactSupport g) : ∃ K, LipschitzWith K g := by
  set s := cthickening 1 (tsupport g) with hsdef
  have hs : IsCompact s := hgc.cthickening
  obtain ⟨K, hK⟩ := (hg.locallyLipschitzOn (s := s)).exists_lipschitzOnWith_of_compact hs
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hts : tsupport g ⊆ s := self_subset_cthickening _
  have h0 : ∀ x, x ∉ tsupport g → g x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hfar : ∀ x y, x ∈ tsupport g → y ∉ s → 1 < dist x y := fun x y hx hy ↦ by
    by_contra h
    exact hy (mem_cthickening_of_dist_le y x 1 _ hx (by rw [dist_comm]; linarith))
  have hMn : M ≤ Real.toNNReal M := Real.le_coe_toNNReal M
  have key : ∀ x y, y ∉ s → |g x - g y| ≤ (K + Real.toNNReal M : ℝ≥0) * dist x y := by
    intro x y hy
    rw [h0 y fun h ↦ hy (hts h), sub_zero]
    by_cases hx : x ∈ tsupport g
    · have h1 := hfar x y hx hy
      have h2 : |g x| ≤ M := by simpa [Real.norm_eq_abs] using hM x
      push_cast
      nlinarith [K.coe_nonneg, (Real.toNNReal M).coe_nonneg, abs_nonneg (g x)]
    · rw [h0 x hx, abs_zero]
      positivity
  refine ⟨K + Real.toNNReal M, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  rw [Real.dist_eq]
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · have := hK.dist_le_mul x hx y hy
      rw [Real.dist_eq] at this
      exact this.trans (mul_le_mul_of_nonneg_right (by push_cast; linarith [
        (Real.toNNReal M).coe_nonneg]) dist_nonneg)
    · exact key x y hy
  · rw [abs_sub_comm, dist_comm]
    exact key y x hx

/-- Test functions for the space-time integration by parts: continuous, with locally Lipschitz
time slices and bounded spatial gradient. (No regularity in time is required.) -/
def IsSliceLipTest (φ : E d × ℝ → ℝ) : Prop :=
  Continuous φ ∧ (∀ t : ℝ, LocallyLipschitz fun x ↦ φ (x, t)) ∧ ∃ C : ℝ, ∀ p, ‖gradₓ φ p‖ ≤ C

theorem LipschitzWith.isSliceLipTest {φ : E d × ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    IsSliceLipTest φ :=
  ⟨hφ.continuous, fun t ↦ (hφ.comp (LipschitzWith.prodMk_right t)).locallyLipschitz,
    K, norm_gradₓ_le hφ⟩

/-- **Space-time integration by parts.** If every time slice of `f` is `C²` in `U`, and `φ` is
Lipschitz with compact support in `U_∞`, then `∫_{U_∞} Δₓf φ = -∫_{U_∞} ∇ₓf · ∇ₓφ`
(Fubini and `integral_laplacian_mul_eq_neg` on each slice). -/
theorem integral_lapₓ_mul_eq_neg {U : Set (E d)} (hU : IsOpen U) {f φ : E d × ℝ → ℝ}
    (hf : ∀ t > 0, ContDiffOn ℝ 2 (fun x ↦ f (x, t)) U)
    (hlap : ContinuousOn (lapₓ f) (tsupport φ)) (hgrad : ContinuousOn (gradₓ f) (tsupport φ))
    (hφ : IsSliceLipTest φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ UInf U) :
    ∫ p in UInf U, lapₓ f p * φ p = -∫ p in UInf U, ⟪gradₓ f p, gradₓ φ p⟫ := by
  obtain ⟨hφcont, hφsl, Cφ, hCφ⟩ := hφ
  set K := tsupport φ with hKdef
  have hK : IsCompact K := hφc
  have hKm : MeasurableSet K := (isClosed_tsupport φ).measurableSet
  have h0 : ∀ p, p ∉ K → φ p = 0 := fun p hp ↦ image_eq_zero_of_notMem_tsupport hp
  have hA0 : ∀ p, p ∉ K → lapₓ f p * φ p = 0 := fun p hp ↦ by simp [h0 p hp]
  have hB0 : ∀ p, p ∉ K → ⟪gradₓ f p, gradₓ φ p⟫ = 0 := fun p hp ↦ by
    simp [gradₓ_eq_zero_of_notMem hp]
  have hAint : Integrable (fun p ↦ lapₓ f p * φ p) := by
    refine (integrableOn_iff_integrable_of_support_subset fun p hp ↦ ?_).1
      ((hlap.mul hφcont.continuousOn).integrableOn_compact hK)
    by_contra h
    exact hp (hA0 p h)
  have hBint : Integrable (fun p ↦ ⟪gradₓ f p, gradₓ φ p⟫) := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgrad
    have hon : IntegrableOn (fun p ↦ ⟪gradₓ f p, gradₓ φ p⟫) K := by
      refine IntegrableOn.of_bound hK.measure_lt_top
        ((hgrad.aestronglyMeasurable hKm).inner
          (measurable_gradₓ hφcont).aestronglyMeasurable)
        (C * Cφ) (ae_restrict_of_forall_mem hKm fun p hp ↦ ?_)
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      exact mul_le_mul (hC p hp) (hCφ p) (norm_nonneg _)
        ((norm_nonneg _).trans (hC p hp))
    refine (integrableOn_iff_integrable_of_support_subset fun p hp ↦ ?_).1 hon
    by_contra h
    exact hp (hB0 p h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ hA0 p fun h ↦ hp (hφs h),
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ hB0 p fun h ↦ hp (hφs h)]
  rw [Measure.volume_eq_prod] at hAint hBint ⊢
  rw [integral_prod_symm _ hAint, integral_prod_symm _ hBint, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  by_cases ht : 0 < t
  · obtain ⟨Kt, hlip⟩ :=
      LocallyLipschitz.exists_lipschitzWith_of_hasCompactSupport (hφsl t)
        (hasCompactSupport_slice hφc t)
    have h := integral_laplacian_mul_eq_neg (f := fun x ↦ f (x, t)) (g := fun x ↦ φ (x, t)) hU
      (hf t ht) hlip (hasCompactSupport_slice hφc t)
      fun x hx ↦ (hφs (tsupport_slice_subset φ t hx)).1
    simp only [lapₓ, gradₓ]
    exact h
  · have hK' : ∀ x, (x, t) ∉ K := fun x h ↦ ht (hφs h).2
    simp [h0 _ (hK' _), gradₓ_eq_zero_of_notMem (hK' _)]

/-- **(4.5) in the limit**: if classical solutions `v n` of (3.4)
with `e n → 0` converge locally uniformly to `u` on `U_∞`, with
`∫ ∇ₓv n · ∇ₓφ → ∫ ∇ₓu · ∇ₓφ` for all test functions `φ` (e.g. weak convergence of the
gradients) and `∂ₜv n ⇀ w` weakly in `L²(U_∞)`, then `u` satisfies the weak heat
equation in `{u > 0}`. On `spt φ ⊆ {u > 0}` one has `v n > e n` for large `n`,
so the reaction term vanishes there; multiply (3.4) by `φ`, integrate by parts in `x`
(`integral_lapₓ_mul_eq_neg`) and pass to the limit. -/
theorem weakHeat_of_tendsto_of_grad {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ}
    {β : ℝ → ℝ} (hβ : IsReactionProfile β) {e : ℕ → ℝ} {v : ℕ → E d × ℝ → ℝ} {u w : E d × ℝ → ℝ}
    (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0))
    (hsol : ∀ n, IsSemilinearSolOn U Q β (e n) (Ioi 0) (v n))
    (hconv : TendstoLocallyUniformlyOn v u atTop (UInf U))
    (hR : ∀ φ : E d × ℝ → ℝ, IsSliceLipTest φ → HasCompactSupport φ → tsupport φ ⊆ UInf U →
      Tendsto (fun n ↦ ∫ p in UInf U, ⟪gradₓ (v n) p, gradₓ φ p⟫) atTop
        (𝓝 (∫ p in UInf U, ⟪gradₓ u p, gradₓ φ p⟫)))
    (hw : TendstoWeakL2 volume (UInf U) (fun n ↦ dₜ (v n)) w atTop) :
    ∀ φ : E d × ℝ → ℝ, IsSliceLipTest φ → HasCompactSupport φ →
      tsupport φ ⊆ posSetP u (UInf U) →
      ∫ p in UInf U, w p * φ p = -∫ p in UInf U, ⟪gradₓ u p, gradₓ φ p⟫ := by
  intro φ hφ hφc hφs
  obtain ⟨hφcont, -, Kφ, hKφ⟩ := id hφ
  set K := tsupport φ with hKdef
  have hK : IsCompact K := hφc
  have hKm : MeasurableSet K := (isClosed_tsupport φ).measurableSet
  have hKU : K ⊆ UInf U := fun p hp ↦ (hφs hp).1
  have hUo : IsOpen (UInf U) := hU.prod isOpen_Ioi
  have hUm : MeasurableSet (UInf U) := hUo.measurableSet
  have hucont : ContinuousOn u (UInf U) :=
    hconv.continuousOn (Frequently.of_forall fun n ↦ (hsol n).1)
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' (hucont.mono hKU) fun p hp ↦ (hφs hp).2
  have hunif : TendstoUniformlyOn v u atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hUo).1 hconv K hKU hK
  -- the reaction term vanishes on `K` for large `n`
  have hev : ∀ᶠ n in atTop, ∀ p ∈ K, dₜ (v n) p = lapₓ (v n) p := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif (m / 2) (half_pos hm),
      he0.eventually (gt_mem_nhds (half_pos hm))] with n hn hen p hp
    rw [(hsol n).2.2.2.2.2.2 p (hKU hp)]
    have hvp : m / 2 < v n p := by
      have h1 := hn p hp
      have h2 := hmK p hp
      rw [Real.dist_eq] at h1
      linarith [(abs_lt.1 h1).2]
    have hβ0 : betaEps β (e n) (v n p) = 0 := by
      rw [betaEps, hβ.2.1 _ fun hmem ↦ ?_, zero_div]
      have : 1 < v n p / e n := (one_lt_div (he n)).2 (by linarith)
      exact absurd hmem.2 (not_lt.2 this.le)
    rw [hβ0, mul_zero, sub_zero]
  -- the identity at level `n`
  have hidn : ∀ᶠ n in atTop, ∫ p in UInf U, dₜ (v n) p * φ p =
      -∫ p in UInf U, ⟪gradₓ (v n) p, gradₓ φ p⟫ := by
    filter_upwards [hev] with n hn
    have heq : ∫ p in UInf U, dₜ (v n) p * φ p = ∫ p in UInf U, lapₓ (v n) p * φ p := by
      refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
      by_cases hp : p ∈ K
      · simp only [hn p hp]
      · simp [image_eq_zero_of_notMem_tsupport hp]
    rw [heq]
    exact integral_lapₓ_mul_eq_neg hU (fun t ht ↦ (hsol n).2.1 t ht)
      (((hsol n).2.2.2.2.2.1.mono hKU).congr fun p hp ↦ (hn p hp).symm)
      ((hsol n).2.2.1.mono hKU) hφ hφc hKU
  -- the time-derivative term
  have hφL2 : MemLp φ 2 (volume.restrict (UInf U)) :=
    (hφcont.memLp_of_hasCompactSupport hφc).restrict _
  have hL : Tendsto (fun n ↦ ∫ p in UInf U, dₜ (v n) p * φ p) atTop
      (𝓝 (∫ p in UInf U, w p * φ p)) := by
    have := hw.2.2 φ hφL2
    simp only [RCLike.inner_apply, conj_trivial] at this
    simpa only [mul_comm] using this
  exact tendsto_nhds_unique (hL.congr' hidn) (hR φ hφ hφc hKU).neg

/-- **(4.5) in the limit**: if classical solutions `v n` of (3.4)
with `e n → 0` converge locally uniformly to `u` on `U_∞`, with `∇ₓv n → ∇ₓu` in `L²_loc`
(`∇ₓu ∈ L²_loc`) and `∂ₜv n ⇀ w` weakly in `L²(U_∞)`, then `u` satisfies the weak heat
equation in `{u > 0}` for test functions that are only Lipschitz in space
(see `weakHeat_of_tendsto_of_grad`). -/
theorem weakHeat_of_tendsto' {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ} {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {e : ℕ → ℝ} {v : ℕ → E d × ℝ → ℝ} {u w : E d × ℝ → ℝ}
    (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0))
    (hsol : ∀ n, IsSemilinearSolOn U Q β (e n) (Ioi 0) (v n))
    (hconv : TendstoLocallyUniformlyOn v u atTop (UInf U))
    (hstrong : TendstoLpLoc 2 volume (UInf U) (fun n ↦ gradₓ (v n)) (gradₓ u) atTop)
    (hg₀ : ∀ K ⊆ UInf U, IsCompact K → MemLp (gradₓ u) 2 (volume.restrict K))
    (hw : TendstoWeakL2 volume (UInf U) (fun n ↦ dₜ (v n)) w atTop) :
    ∀ φ : E d × ℝ → ℝ, IsSliceLipTest φ → HasCompactSupport φ →
      tsupport φ ⊆ posSetP u (UInf U) →
      ∫ p in UInf U, w p * φ p = -∫ p in UInf U, ⟪gradₓ u p, gradₓ φ p⟫ := by
  refine weakHeat_of_tendsto_of_grad hU hβ he he0 hsol hconv ?_ hw
  intro φ hφ hφc hKU
  obtain ⟨hφcont, -, Kφ, hKφ⟩ := id hφ
  set K := tsupport φ with hKdef
  have hK : IsCompact K := hφc
  have hKm : MeasurableSet K := (isClosed_tsupport φ).measurableSet
  have hUm : MeasurableSet (UInf U) := (hU.prod isOpen_Ioi).measurableSet
  have hred : ∀ G : E d × ℝ → E d,
      ∫ p in UInf U, ⟪G p, gradₓ φ p⟫ = ∫ p in K, ⟪G p, gradₓ φ p⟫ := fun G ↦
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hUm hKU fun p hp ↦ by
      simp [gradₓ_eq_zero_of_notMem hp.2]
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hgφ : MemLp (gradₓ φ) 2 (volume.restrict K) :=
    MemLp.of_bound (measurable_gradₓ hφcont).aestronglyMeasurable Kφ
      (Eventually.of_forall hKφ)
  have hgn : ∀ n, MemLp (gradₓ (v n)) 2 (volume.restrict K) := fun n ↦ by
    have hc := (hsol n).2.2.1.mono hKU
    obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn hc
    exact MemLp.of_bound (hc.aestronglyMeasurable hKm) Cg (ae_restrict_of_forall_mem hKm hCg)
  simp only [hred]
  exact tendsto_integral_inner_of_tendsto hgn (hg₀ K hKU hK) (fun _ ↦ hgφ) hgφ
    (hstrong K hKU hK) (by simp)

/-- **(4.5) in the limit**, in the form of Def `WeakHeatInPos`
(Lipschitz test functions); see `weakHeat_of_tendsto'` for the version with test functions that
are only Lipschitz in space. -/
theorem weakHeat_of_tendsto {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ} {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {e : ℕ → ℝ} {v : ℕ → E d × ℝ → ℝ} {u w : E d × ℝ → ℝ}
    (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0))
    (hsol : ∀ n, IsSemilinearSolOn U Q β (e n) (Ioi 0) (v n))
    (hconv : TendstoLocallyUniformlyOn v u atTop (UInf U))
    (hstrong : TendstoLpLoc 2 volume (UInf U) (fun n ↦ gradₓ (v n)) (gradₓ u) atTop)
    (hg₀ : ∀ K ⊆ UInf U, IsCompact K → MemLp (gradₓ u) 2 (volume.restrict K))
    (hw : TendstoWeakL2 volume (UInf U) (fun n ↦ dₜ (v n)) w atTop) :
    WeakHeatInPos U u w := by
  rintro φ ⟨Kφ, hφ⟩ hφc hφs
  exact weakHeat_of_tendsto' hU hβ he he0 hsol hconv hstrong hg₀ hw φ
    (LipschitzWith.isSliceLipTest hφ) hφc hφs

end Inner

end PerronVariational

end
