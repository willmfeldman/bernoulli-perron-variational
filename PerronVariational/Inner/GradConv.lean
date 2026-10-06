/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.InnerVarLinear
import GMTFoundations.Sobolev.Cutoff
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import PerronVariational.Inner.SliceInnerVar
import PerronVariational.Inner.WeakHarmonic

/-!
# Weak convergence of gradients from locally uniform convergence

Tool for Step 2 of the proof of **Theorem 3.10** of F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 ("we have used that `u(·, t)` converges to `u_∞` weakly in `H¹(U)`"): if `Fₙ → f`
locally uniformly in the open set `U` and `∇Fₙ` is locally bounded, uniformly in `n`, then
`∫_U ∇Fₙ · G → ∫_U ∇f · G` for every bounded measurable `G` vanishing outside a compact subset of
`U`.

Proof: for `G = Φ` smooth with compact support in `U` integrate by parts,
`∫_U ∇Fₙ · Φ = -∫_U Fₙ div Φ`, and use the uniform convergence on `spt Φ`. For general `G`,
approximate `G` in `L¹` by `Φ_j = θ (ρ_j ⋆ G)` (a cutoff `θ` times the mollification of `G`) and
use the uniform bounds on the gradients.

## Main results

* `PerronVariational.LongTime.integral_inner_gradient_eq_neg_div`
* `PerronVariational.LongTime.tendsto_integral_inner_gradient`
-/

open Set Function Filter Topology MeasureTheory Metric InnerProductSpace ContinuousLinearMap
open scoped Gradient ContDiff NNReal ENNReal Convolution

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-- `⟨∇F(x), v⟩ = ∑ᵢ ∂ᵢF(x) vᵢ`. -/
theorem inner_gradient_eq_sum (F : E d → ℝ) (x v : E d) :
    inner ℝ (∇ F x) v = ∑ i, fderiv ℝ F x (coordVec i) * v i := by
  have hF : ∀ i, fderiv ℝ F x (coordVec i) = (∇ F x) i := fun i ↦ by
    rw [← inner_gradient_eq_fderiv, real_inner_comm, coordVec, EuclideanSpace.inner_single_right]
    simp
  simp only [hF, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- The divergence `div Φ = ∑ᵢ ∂ᵢΦᵢ`, written with the coordinates. -/
noncomputable def coordDiv (Φ : E d → E d) (x : E d) : ℝ :=
  ∑ i, fderiv ℝ (fun y ↦ Φ y i) x (coordVec i)

theorem contDiff_coord {Φ : E d → E d} {n : WithTop ℕ∞} (hΦ : ContDiff ℝ n Φ) (i : Fin d) :
    ContDiff ℝ n fun y ↦ Φ y i :=
  (EuclideanSpace.proj i : E d →L[ℝ] ℝ).contDiff.comp hΦ

theorem tsupport_coordDiv_subset (Φ : E d → E d) : tsupport (coordDiv Φ) ⊆ tsupport Φ :=
  closure_minimal (fun y hy ↦ by
    by_contra h'
    refine hy (Finset.sum_eq_zero fun i _ ↦ ?_)
    simp [fderiv_of_notMem_tsupport ℝ fun h ↦ h' (tsupport_coord_subset Φ i h)])
    (isClosed_tsupport _)

theorem continuous_coordDiv {Φ : E d → E d} (hΦ : ContDiff ℝ 1 Φ) : Continuous (coordDiv Φ) :=
  continuous_finsetSum _ fun i _ ↦
    ((contDiff_coord hΦ i).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- **Integration by parts**, `∫_U ∇F · Φ = -∫_U F div Φ` for `F` locally Lipschitz on the open
set `U` and `Φ ∈ C¹_c(U; ℝᵈ)`. -/
theorem integral_inner_gradient_eq_neg_div {U : Set (E d)} (hU : IsOpen U) {F : E d → ℝ}
    (hF : LocallyLipschitzOn U F) {Φ : E d → E d} (hΦ : ContDiff ℝ 1 Φ)
    (hΦc : HasCompactSupport Φ) (hΦU : tsupport Φ ⊆ U) :
    ∫ x in U, inner ℝ (∇ F x) (Φ x) = -∫ x in U, F x * coordDiv Φ x := by
  have hK := hΦc.isCompact
  obtain ⟨B, hB⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hF hK hΦU
  have hΦic : ∀ i : Fin d, HasCompactSupport (fun y ↦ Φ y i) := fun i ↦
    hΦc.comp_left (g := fun v : E d ↦ v i) (by simp)
  have hint : ∀ i : Fin d, IntegrableOn (fun x ↦ fderiv ℝ F x (coordVec i) * Φ x i) U := by
    intro i
    obtain ⟨C, hC⟩ := (hΦic i).exists_bound_of_continuous (contDiff_coord hΦ i).continuous
    refine IntegrableOn.of_forall_sdiff_eq_zero (s := tsupport Φ) ?_ hU.measurableSet
      fun x hx ↦ ?_
    · refine IntegrableOn.of_bound hK.measure_lt_top
        ((measurable_fderiv_apply_const ℝ F _).mul
          (contDiff_coord hΦ i).continuous.measurable).aestronglyMeasurable (B * ‖coordVec i‖ * C)
        ((ae_restrict_mem hK.measurableSet).mono fun x hx ↦ ?_)
      rw [norm_mul]
      exact mul_le_mul ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg _))) (hC x) (norm_nonneg _)
        (mul_nonneg ((norm_nonneg _).trans (hB x hx)) (norm_nonneg _))
    · simp [image_eq_zero_of_notMem_tsupport hx.2]
  simp_rw [inner_gradient_eq_sum]
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  simp_rw [coordDiv, Finset.mul_sum]
  rw [integral_finsetSum, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact GMTFoundations.integral_fderiv_mul_eq_neg hU hF (contDiff_coord hΦ i) (hΦic i)
      ((tsupport_coord_subset Φ i).trans hΦU) _
  · intro i _
    have hc : Continuous fun x ↦ fderiv ℝ (fun y ↦ Φ y i) x (coordVec i) :=
      ((contDiff_coord hΦ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs : tsupport (fun x ↦ fderiv ℝ (fun y ↦ Φ y i) x (coordVec i)) ⊆ tsupport Φ :=
      (tsupport_fderiv_apply_subset _ _).trans (tsupport_coord_subset Φ i)
    refine IntegrableOn.of_forall_sdiff_eq_zero (s := tsupport Φ) ?_ hU.measurableSet
      fun x hx ↦ ?_
    · exact ((hF.continuousOn.mono hΦU).mul hc.continuousOn).integrableOn_compact hK
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx.2 (hcs h)]

/-- Weak convergence against a smooth compactly supported field. -/
theorem tendsto_integral_inner_gradient_of_smooth {U : Set (E d)} (hU : IsOpen U)
    {F : ℕ → E d → ℝ} {f : E d → ℝ} (hF : ∀ n, LocallyLipschitzOn U (F n))
    (hf : LocallyLipschitzOn U f) {Φ : E d → E d} (hΦ : ContDiff ℝ 1 Φ)
    (hΦc : HasCompactSupport Φ) (hΦU : tsupport Φ ⊆ U)
    (hconv : TendstoUniformlyOn F f atTop (tsupport Φ)) :
    Tendsto (fun n ↦ ∫ x in U, inner ℝ (∇ (F n) x) (Φ x)) atTop
      (𝓝 (∫ x in U, inner ℝ (∇ f x) (Φ x))) := by
  simp_rw [integral_inner_gradient_eq_neg_div hU (hF _) hΦ hΦc hΦU,
    integral_inner_gradient_eq_neg_div hU hf hΦ hΦc hΦU]
  have hs := tsupport_coordDiv_subset Φ
  refine (tendsto_setIntegral_mul_of_tendstoUniformlyOn hU.measurableSet (continuous_coordDiv hΦ)
    (hΦc.isCompact.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans hΦU)
    (Eventually.of_forall fun n ↦ (hF n).continuousOn.mono (hs.trans hΦU))
    (hf.continuousOn.mono (hs.trans hΦU)) (hconv.mono hs)).neg

/-- Integrability of `∇F · H` over `U` for `F` locally Lipschitz on `U` and `H` bounded and
vanishing outside a compact subset of `U`. -/
theorem integrableOn_inner_gradient {U : Set (E d)} (hU : IsOpen U) {F : E d → ℝ}
    (hF : LocallyLipschitzOn U F) {K : Set (E d)} (hK : IsCompact K) (hKU : K ⊆ U)
    {H : E d → E d} (hHm : AEStronglyMeasurable H volume) {M : ℝ} (hHb : ∀ x, ‖H x‖ ≤ M)
    (hH0 : ∀ x ∉ K, H x = 0) : IntegrableOn (fun x ↦ inner ℝ (∇ F x) (H x)) U := by
  obtain ⟨B, hB⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hF hK hKU
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := K) ?_ hU.measurableSet fun x hx ↦ by
    simp [hH0 x hx.2]
  refine IntegrableOn.of_bound hK.measure_lt_top
    ((GMTFoundations.measurable_gradient F).aestronglyMeasurable.inner hHm.restrict) (B * M)
    ((ae_restrict_mem hK.measurableSet).mono fun x hx ↦ ?_)
  refine (norm_inner_le_norm _ _).trans (mul_le_mul ?_ (hHb x) (norm_nonneg _)
    ((norm_nonneg _).trans (hB x hx)))
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact hB x hx

/-- `|∫_U ∇F · H| ≤ b ∫_K |H|` if `|∇F| ≤ b` on `K` and `H` vanishes outside `K ⊆ U`. -/
theorem norm_setIntegral_inner_gradient_le {U : Set (E d)} (hU : MeasurableSet U) {F : E d → ℝ}
    {K : Set (E d)} (hKm : MeasurableSet K) (hKU : K ⊆ U) {H : E d → E d} (hHi : IntegrableOn H K)
    (hH0 : ∀ x ∉ K, H x = 0) {b : ℝ} (hb : ∀ x ∈ K, ‖∇ F x‖ ≤ b) :
    ‖∫ x in U, inner ℝ (∇ F x) (H x)‖ ≤ b * ∫ x in K, ‖H x‖ := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hKU fun x hx ↦ by simp [hH0 x hx.2],
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hHi.norm.const_mul b)
    ((ae_restrict_mem hKm).mono fun x hx ↦ ?_)
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg _))

/-- **Weak convergence of gradients.** If `Fₙ → f` locally uniformly in the open set `U`, `Fₙ`, `f`
are locally Lipschitz on `U` and the gradients `∇Fₙ` are bounded on compact subsets of `U`
uniformly for large `n`, then `∫_U ∇Fₙ · G → ∫_U ∇f · G` for every bounded measurable `G`
vanishing outside a compact subset of `U`. -/
theorem tendsto_integral_inner_gradient {U : Set (E d)} (hU : IsOpen U) {F : ℕ → E d → ℝ}
    {f : E d → ℝ} (hF : ∀ n, LocallyLipschitzOn U (F n)) (hf : LocallyLipschitzOn U f)
    (hconv : ∀ K', IsCompact K' → K' ⊆ U → TendstoUniformlyOn F f atTop K')
    (hBF : ∀ K', IsCompact K' → K' ⊆ U → ∃ B, ∀ᶠ n in atTop, ∀ x ∈ K', ‖∇ (F n) x‖ ≤ B)
    {K : Set (E d)} (hK : IsCompact K) (hKU : K ⊆ U) {G : E d → E d}
    (hGm : AEStronglyMeasurable G volume) {M : ℝ} (hGb : ∀ x, ‖G x‖ ≤ M)
    (hG0 : ∀ x ∉ K, G x = 0) :
    Tendsto (fun n ↦ ∫ x in U, inner ℝ (∇ (F n) x) (G x)) atTop
      (𝓝 (∫ x in U, inner ℝ (∇ f x) (G x))) := by
  obtain ⟨θ, hθs, hθc, hθU, hθ01, hθ1⟩ := GMTFoundations.exists_smooth_cutoff hK hU hKU
  set K'' := tsupport θ
  have hK'' : IsCompact K'' := hθc.isCompact
  have hK''m : MeasurableSet K'' := hK''.measurableSet
  have hUm : MeasurableSet U := hU.measurableSet
  have : IsFiniteMeasure (volume.restrict K'') :=
    isFiniteMeasure_restrict.2 hK''.measure_lt_top.ne
  obtain ⟨B, hB⟩ := hBF K'' hK'' hθU
  obtain ⟨B', hB'⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hf hK'' hθU
  have hB'g : ∀ x ∈ K'', ‖∇ f x‖ ≤ max B' 0 := fun x hx ↦ by
    rw [gradient, LinearIsometryEquiv.norm_map]; exact (hB' x hx).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hGb 0)
  have hGloc : LocallyIntegrable G volume :=
    (locallyIntegrable_const M).mono hGm (Eventually.of_forall fun x ↦
      (hGb x).trans (le_abs_self M |>.trans_eq (Real.norm_eq_abs M).symm))
  have hθG : ∀ x, θ x • G x = G x := fun x ↦ by
    by_cases hx : x ∈ K
    · rw [hθ1 x hx, one_smul]
    · rw [hG0 x hx, smul_zero]
  have hG0'' : ∀ x ∉ K'', G x = 0 := fun x hx ↦ by
    rw [← hθG x, image_eq_zero_of_notMem_tsupport hx, zero_smul]
  -- the approximations `Φ_j = θ (ρ_j ⋆ G)`
  set C : ℕ → E d → E d := fun j ↦ (moll d j ⋆[lsmul ℝ ℝ, volume] G)
  set Φ : ℕ → E d → E d := fun j x ↦ θ x • C j x
  have hCs : ∀ j, ContDiff ℝ ∞ (C j) := fun j ↦
    (hasCompactSupport_moll j).contDiff_convolution_left (lsmul ℝ ℝ) (contDiff_moll j) hGloc
  have hΦs : ∀ j, ContDiff ℝ 1 (Φ j) := fun j ↦ (hθs.smul (hCs j)).of_le (by simp)
  have hΦsupp : ∀ j, tsupport (Φ j) ⊆ K'' := fun j ↦
    closure_minimal (fun x hx ↦ subset_tsupport θ fun h ↦ hx (by simp [Φ, h]))
      (isClosed_tsupport _)
  have hΦc : ∀ j, HasCompactSupport (Φ j) := fun j ↦
    hK''.of_isClosed_subset (isClosed_tsupport _) (hΦsupp j)
  have hΦ0 : ∀ j, ∀ x ∉ K'', Φ j x = 0 := fun j x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hΦsupp j h)
  have hCb : ∀ j x, ‖C j x‖ ≤ M := fun j x ↦ norm_moll_convolution_le hGb j x
  have hΦb : ∀ j x, ‖Φ j x‖ ≤ M := fun j x ↦ by
    rw [norm_smul, Real.norm_of_nonneg (hθ01 x).1]
    calc θ x * ‖C j x‖ ≤ 1 * M :=
          mul_le_mul (hθ01 x).2 (hCb j x) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  have hae : ∀ᵐ x, Tendsto (fun j ↦ C j x) atTop (𝓝 (G x)) := by
    have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
      (φ := bumpN d) (l := atTop) (K := 2) tendsto_bumpRad
      (Eventually.of_forall fun n ↦ by simp [bumpN]; linarith) hGloc
    exact h
  -- `Φ_j → G` in `L¹(K'')`
  have hL1 : Tendsto (fun j ↦ ∫ x in K'', ‖G x - Φ j x‖) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict K'')
      (F := fun j x ↦ ‖G x - Φ j x‖) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ M + M)
      (Eventually.of_forall fun j ↦
        (hGm.restrict.sub (hΦs j).continuous.aestronglyMeasurable).norm)
      (Eventually.of_forall fun j ↦ Eventually.of_forall fun x ↦ by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hGb x) (hΦb j x)))
      (integrable_const _) ((ae_restrict_of_ae hae).mono fun x hx ↦ by
        have : Tendsto (fun j ↦ ‖G x - θ x • C j x‖) atTop (𝓝 ‖G x - θ x • G x‖) :=
          (tendsto_const_nhds.sub (tendsto_const_nhds.smul hx)).norm
        rwa [hθG, sub_self, norm_zero] at this)
    simpa using h
  -- the `ε`-argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  set c := max B 0 + max B' 0 + 1
  have hc : 0 < c := by positivity
  obtain ⟨j, hj⟩ : ∃ j, ∫ x in K'', ‖G x - Φ j x‖ < ε / (3 * c) := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hL1 _ (div_pos hε (mul_pos three_pos hc))
    refine ⟨N, ?_⟩
    have := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hsm := tendsto_integral_inner_gradient_of_smooth hU hF hf (hΦs j) (hΦc j)
    ((hΦsupp j).trans hθU) ((hconv K'' hK'' hθU).mono (hΦsupp j))
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hsm (ε / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hB
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  have hDm : AEStronglyMeasurable (fun x ↦ G x - Φ j x) volume :=
    hGm.sub (hΦs j).continuous.aestronglyMeasurable
  have hDb : ∀ x, ‖G x - Φ j x‖ ≤ M + M := fun x ↦
    (norm_sub_le _ _).trans (add_le_add (hGb x) (hΦb j x))
  have hD0 : ∀ x ∉ K'', G x - Φ j x = 0 := fun x hx ↦ by rw [hG0'' x hx, hΦ0 j x hx, sub_zero]
  have hDi : IntegrableOn (fun x ↦ G x - Φ j x) K'' :=
    IntegrableOn.of_bound hK''.measure_lt_top hDm.restrict (M + M)
      (Eventually.of_forall hDb)
  have hsplit : ∀ g : E d → ℝ, LocallyLipschitzOn U g → ∫ x in U, inner ℝ (∇ g x) (G x) =
      (∫ x in U, inner ℝ (∇ g x) (Φ j x)) + ∫ x in U, inner ℝ (∇ g x) (G x - Φ j x) := by
    intro g hg
    have hi1 : IntegrableOn (fun x ↦ inner ℝ (∇ g x) (Φ j x)) U :=
      integrableOn_inner_gradient hU hg hK'' hθU (hΦs j).continuous.aestronglyMeasurable
        (hΦb j) (hΦ0 j)
    have hi2 : IntegrableOn (fun x ↦ inner ℝ (∇ g x) (G x - Φ j x)) U :=
      integrableOn_inner_gradient hU hg hK'' hθU hDm hDb hD0
    rw [← integral_add hi1 hi2]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp only [inner_sub_right]; ring)
  have e1 : ‖∫ x in U, inner ℝ (∇ (F n) x) (G x - Φ j x)‖ ≤
      max B 0 * ∫ x in K'', ‖G x - Φ j x‖ :=
    norm_setIntegral_inner_gradient_le hUm hK''m hθU hDi hD0
      fun x hx ↦ (h2 x hx).trans (le_max_left _ _)
  have e2 : ‖∫ x in U, inner ℝ (∇ f x) (G x - Φ j x)‖ ≤
      max B' 0 * ∫ x in K'', ‖G x - Φ j x‖ :=
    norm_setIntegral_inner_gradient_le hUm hK''m hθU hDi hD0 hB'g
  rw [hsplit _ (hF n), hsplit _ hf, Real.dist_eq]
  rw [Real.dist_eq] at h1
  have hI0 : 0 ≤ ∫ x in K'', ‖G x - Φ j x‖ := setIntegral_nonneg hK''m fun _ _ ↦ norm_nonneg _
  have hcε : c * (ε / (3 * c)) = ε / 3 := by field_simp
  calc |((∫ x in U, inner ℝ (∇ (F n) x) (Φ j x)) +
          ∫ x in U, inner ℝ (∇ (F n) x) (G x - Φ j x)) -
        ((∫ x in U, inner ℝ (∇ f x) (Φ j x)) + ∫ x in U, inner ℝ (∇ f x) (G x - Φ j x))|
      ≤ |(∫ x in U, inner ℝ (∇ (F n) x) (Φ j x)) - ∫ x in U, inner ℝ (∇ f x) (Φ j x)| +
        ‖∫ x in U, inner ℝ (∇ (F n) x) (G x - Φ j x)‖ +
        ‖∫ x in U, inner ℝ (∇ f x) (G x - Φ j x)‖ := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        set A1 := ∫ x in U, inner ℝ (∇ (F n) x) (Φ j x)
        set A2 := ∫ x in U, inner ℝ (∇ (F n) x) (G x - Φ j x)
        set A3 := ∫ x in U, inner ℝ (∇ f x) (Φ j x)
        set A4 := ∫ x in U, inner ℝ (∇ f x) (G x - Φ j x)
        have key : A1 + A2 - (A3 + A4) = (A1 - A3) + A2 + -A4 := by ring
        rw [key]
        exact (abs_add_three _ _ _).trans (le_of_eq (by rw [abs_neg]))
    _ < ε / 3 + max B 0 * (ε / (3 * c)) + max B' 0 * (ε / (3 * c)) := by
        have hb1 : max B 0 * ∫ x in K'', ‖G x - Φ j x‖ ≤ max B 0 * (ε / (3 * c)) :=
          mul_le_mul_of_nonneg_left hj.le (le_max_right _ _)
        have hb2 : max B' 0 * ∫ x in K'', ‖G x - Φ j x‖ ≤ max B' 0 * (ε / (3 * c)) :=
          mul_le_mul_of_nonneg_left hj.le (le_max_right _ _)
        linarith
    _ ≤ ε := by
        have : (max B 0 + max B' 0) * (ε / (3 * c)) ≤ c * (ε / (3 * c)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        nlinarith

/-- **From smooth to Lipschitz test functions**: if `∫_W g · ∇φ = 0` for all `φ ∈ C_c^∞(W)`
(`g` measurable and bounded on compact subsets of the open set `W`), then the same holds for all
Lipschitz `ζ` with compact support in `W` (density of translated bumps). -/
theorem setIntegral_inner_gradient_eq_zero_of_lipschitz {W : Set (E d)} (hW : IsOpen W)
    {g : E d → E d} (hgm : Measurable g)
    (hgb : ∀ K, IsCompact K → K ⊆ W → ∃ B, ∀ x ∈ K, ‖g x‖ ≤ B)
    (h : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ∫ x in W, inner ℝ (g x) (∇ φ x) = 0)
    {ζ : E d → ℝ} (hζ : ∃ K, LipschitzWith K ζ) (hζc : HasCompactSupport ζ)
    (hζW : tsupport ζ ⊆ W) :
    ∫ x in W, inner ℝ (g x) (∇ ζ x) = 0 := by
  obtain ⟨δ, hδ, hδW⟩ := hζc.isCompact.exists_cthickening_subset_open hW hζW
  set V := cthickening (δ / 2) (tsupport ζ)
  have hVc : IsCompact V := hζc.isCompact.cthickening
  have hVW : V ⊆ W := (cthickening_mono (by linarith) _).trans hδW
  have hVm : MeasurableSet V := hVc.measurableSet
  set W' := thickening (δ / 2) (tsupport ζ)
  have hW'V : W' ⊆ V := thickening_subset_cthickening _ _
  have hζW' : tsupport ζ ⊆ W' := self_subset_thickening (half_pos hδ) _
  obtain ⟨B, hB⟩ := hgb V hVc hVW
  have hg : Integrable g (volume.restrict V) :=
    IntegrableOn.of_bound hVc.measure_lt_top hgm.aestronglyMeasurable B
      ((ae_restrict_mem hVm).mono fun x hx ↦ hB x hx)
  have hμ : volume.restrict V ≪ volume :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hH : ∀ n, ∀ q ∈ (univ : Set (E d)), closedBall q (bumpRad n) ⊆ W' →
      firstOrderFunctional (volume.restrict V) (fun _ ↦ 0) g (fun x ↦ moll d n (x - q)) = 0 := by
    intro n q _ hball
    have hc : HasCompactSupport (mollAt n q) :=
      HasCompactSupport.intro (isCompact_closedBall q (bumpRad n)) fun x hx ↦ mollAt_eq_zero hx
    have h0 := h (mollAt n q) (contDiff_mollAt n q) hc
      ((tsupport_mollAt_subset n q).trans ((hball.trans hW'V).trans hVW))
    refine Eq.trans ?_ h0
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hW.measurableSet hVW ?_,
      firstOrderFunctional]
    · refine setIntegral_congr_fun hVm fun x _ ↦ ?_
      rw [inner_gradient_eq_fderiv]
      simp only [zero_mul, zero_add]
      rfl
    · intro x hx
      have hxB : x ∉ closedBall q (bumpRad n) := fun h' ↦ hx.2 (hW'V (hball h'))
      simp [gradient_mollAt_eq_zero hxB]
  have hΨ := firstOrderFunctional_eq_zero_of_bumps hμ (integrable_zero _ _ _) hg
    isOpen_thickening dense_univ hH hζ hζc hζW'
  have hvan : ∀ x ∉ V, fderiv ℝ ζ x = 0 := fun x hx ↦
    fderiv_of_notMem_tsupport ℝ fun h' ↦ hx (self_subset_cthickening _ h')
  unfold firstOrderFunctional at hΨ
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hW.measurableSet hVW fun x hx ↦ by
    simp [gradient, hvan x hx.2]]
  rw [← hΨ]
  exact setIntegral_congr_fun hVm fun x _ ↦ by
    rw [inner_gradient_eq_fderiv, Pi.zero_apply, zero_mul, zero_add]

/-- `‖D‖_{L²(K)} ≤ (∫_U η |D|²)^{1/2}` for a weight `η ≥ 0` equal to `1` on `K ⊆ U`. -/
theorem eLpNorm_two_le_of_weight {U K : Set (E d)} (hKU : K ⊆ U) {D : E d → E d}
    {η : E d → ℝ} (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x ∈ K, η x = 1) (hKm : MeasurableSet K)
    (hDm : AEStronglyMeasurable D (volume.restrict K))
    (hi : IntegrableOn (fun x ↦ η x * ‖D x‖ ^ 2) U) :
    eLpNorm D 2 (volume.restrict K) ≤
      ENNReal.ofReal (∫ x in U, η x * ‖D x‖ ^ 2) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hDm]
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x ↦ mul_nonneg (hη0 x) (sq_nonneg _))]
  calc ∫⁻ x in K, ‖D x‖ₑ ^ (2 : ℝ) = ∫⁻ x in K, ENNReal.ofReal (η x * ‖D x‖ ^ 2) := by
        refine setLIntegral_congr_fun hKm fun x hx ↦ ?_
        rw [hη1 x hx, one_mul, ← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
        norm_cast
    _ ≤ ∫⁻ x in U, ENNReal.ofReal (η x * ‖D x‖ ^ 2) := lintegral_mono_set hKU

/-- A function bounded and a.e.-strongly measurable on a compact `K` and vanishing outside `K` is
integrable on any measurable `U`. -/
theorem integrableOn_of_bound_of_vanish {U K : Set (E d)} (hUm : MeasurableSet U)
    (hK : IsCompact K) {φ : E d → ℝ} (hm : AEStronglyMeasurable φ (volume.restrict K)) {c : ℝ}
    (hb : ∀ x ∈ K, ‖φ x‖ ≤ c) (h0 : ∀ x ∉ K, φ x = 0) : IntegrableOn φ U :=
  (IntegrableOn.of_bound hK.measure_lt_top hm c
    ((ae_restrict_mem hK.measurableSet).mono hb)).of_forall_sdiff_eq_zero hUm
    fun x hx ↦ h0 x hx.2

end LongTime

end PerronVariational

end
