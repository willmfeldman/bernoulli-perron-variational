/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Setting
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Topology.Algebra.Module.Cardinality
import PerronVariational.Inner.SliceHeat

/-!
# The truncation argument: from the equation in `{f > 0}` to an energy identity

Tool for **Theorem 3.10**, Step 2, of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981,
where this identity is used without the truncation argument being spelled out. Let `f ≥ 0` be
locally Lipschitz on the open set `U` and satisfy `∫_U a ζ = -∫_U ∇f · ∇ζ` for all Lipschitz `ζ`
with compact support in `{f > 0}`. Then for all `η ∈ C¹_c(U)`,
`∫_U a f η = -∫_U (|∇f|² η + f ∇f · ∇η)`.

Proof: test with `ζ_δ = (f - δ)₊ η` for levels `δ ↓ 0` with `|{f = δ}| = 0` (all but countably many
`δ`), so that `∇ζ_δ = 1_{f > δ} η ∇f + (f - δ)₊ ∇η` a.e.; then let `δ ↓ 0` by dominated
convergence, using `∇f = 0` on `{f = 0} ∩ U` (minimum points).

## Main results

* `PerronVariational.LongTime.lipschitzWith_of_locallyLipschitz_of_hasCompactSupport`
* `PerronVariational.LongTime.integral_truncation_identity`
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient ContDiff NNReal ENNReal

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-- A locally Lipschitz function with compact support is Lipschitz. -/
theorem lipschitzWith_of_locallyLipschitz_of_hasCompactSupport {f : E d → ℝ}
    (hf : LocallyLipschitz f) (hfc : HasCompactSupport f) : ∃ K, LipschitzWith K f := by
  set S := tsupport f
  set K' := cthickening 1 S
  have hK' : IsCompact K' := hfc.isCompact.cthickening
  obtain ⟨L, hL⟩ := (hf.locallyLipschitzOn (s := K')).exists_lipschitzOnWith_of_compact hK'
  obtain ⟨M, hM⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set C : ℝ≥0 := max L M.toNNReal
  have hLC : (L : ℝ) ≤ C := by simp [C]
  have hMC : M ≤ C := by simp [C, Real.coe_toNNReal _ hM0]
  have hzero : ∀ y ∉ S, f y = 0 := fun y hy ↦ image_eq_zero_of_notMem_tsupport hy
  have key : ∀ x y, x ∈ S → dist (f x) (f y) ≤ C * dist x y := by
    intro x y hx
    by_cases hy : y ∈ K'
    · exact (hL.dist_le_mul x (self_subset_cthickening _ hx) y hy).trans
        (mul_le_mul_of_nonneg_right hLC dist_nonneg)
    · have hd : 1 < dist x y := by
        by_contra h'
        exact hy (mem_cthickening_of_dist_le y x 1 S hx (by rw [dist_comm]; linarith))
      have hfy : f y = 0 := hzero y fun h ↦ hy (self_subset_cthickening _ h)
      rw [hfy, dist_zero_right]
      calc ‖f x‖ ≤ M := hM x
        _ ≤ C := hMC
        _ = C * 1 := (mul_one _).symm
        _ ≤ C * dist x y := mul_le_mul_of_nonneg_left hd.le (NNReal.coe_nonneg _)
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  by_cases hx : x ∈ S
  · exact key x y hx
  by_cases hy : y ∈ S
  · rw [dist_comm, dist_comm x]; exact key y x hy
  rw [hzero x hx, hzero y hy, dist_self]
  positivity

/-- The derivative of `(g - δ)₊ η` at a differentiability point `x` of `g` with `g x ≠ δ`. -/
theorem fderiv_trunc_mul {g η : E d → ℝ} {x : E d} {δ : ℝ} (hg : DifferentiableAt ℝ g x)
    (hη : DifferentiableAt ℝ η x) (hx : g x ≠ δ) :
    fderiv ℝ (fun y ↦ max (g y - δ) 0 * η y) x =
      (if δ < g x then (1 : ℝ) else 0) • (η x • fderiv ℝ g x) + max (g x - δ) 0 • fderiv ℝ η x := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hev : (fun y ↦ max (g y - δ) 0 * η y) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hg.continuousAt.eventually (gt_mem_nhds hlt)] with y hy
      simp [max_eq_right (by linarith : g y - δ ≤ 0)]
    rw [hev.fderiv_eq, fderiv_fun_const, if_neg (not_lt.2 hlt.le),
      max_eq_right (by linarith : g x - δ ≤ 0)]
    simp
  · have hev : (fun y ↦ max (g y - δ) 0 * η y) =ᶠ[𝓝 x] fun y ↦ (g y - δ) * η y := by
      filter_upwards [hg.continuousAt.eventually (lt_mem_nhds hgt)] with y hy
      rw [max_eq_left (by linarith : 0 ≤ g y - δ)]
    rw [hev.fderiv_eq, fderiv_fun_mul (hg.sub_const δ) hη, fderiv_sub_const, if_pos hgt,
      max_eq_left (by linarith : 0 ≤ g x - δ), one_smul, add_comm]

/-- The product of two bounded Lipschitz functions is Lipschitz. -/
theorem lipschitzWith_mul_of_bounded {f g : E d → ℝ} {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) {Mf Mg : ℝ} (hfb : ∀ x, |f x| ≤ Mf) (hgb : ∀ x, |g x| ≤ Mg) :
    ∃ K, LipschitzWith K fun x ↦ f x * g x := by
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb 0)
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgb 0)
  refine ⟨Mf.toNNReal * Kg + Mg.toNNReal * Kf, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have h1 := hf.dist_le_mul x y
  have h2 := hg.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2 ⊢
  have heq : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [heq, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul, Real.coe_toNNReal _ hMf,
    Real.coe_toNNReal _ hMg]
  calc |f x * (g x - g y) + g y * (f x - f y)|
      ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ ≤ Mf * (Kg * dist x y) + Mg * (Kf * dist x y) := by
        gcongr
        · exact hfb x
        · exact hgb y
    _ = (Mf * Kg + Mg * Kf) * dist x y := by ring

/-- **The truncation identity.** Let `f ≥ 0` be locally Lipschitz on the open set `U`, `a`
integrable on compact subsets of `U`, and suppose `∫_U a ζ = -∫_U ∇f · ∇ζ` for all Lipschitz `ζ`
with compact support in `{f > 0} ∩ U`. Then `∫_U a f η = -∫_U (|∇f|² η + f ∇f · ∇η)` for every
`η ∈ C¹_c(U)`. -/
theorem integral_truncation_identity {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : LocallyLipschitzOn U f) (hf0 : ∀ x ∈ U, 0 ≤ f x) {a : E d → ℝ}
    (ha : ∀ K, IsCompact K → K ⊆ U → IntegrableOn a K)
    (hid : ∀ ζ : E d → ℝ, (∃ K, LipschitzWith K ζ) → HasCompactSupport ζ →
      tsupport ζ ⊆ posSet f U → ∫ x in U, a x * ζ x = -∫ x in U, inner ℝ (∇ f x) (∇ ζ x))
    {η : E d → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, a x * (f x * η x) =
      -∫ x in U, (‖∇ f x‖ ^ 2 * η x + f x * inner ℝ (∇ f x) (∇ η x)) := by
  set K := tsupport η
  have hK : IsCompact K := hηc.isCompact
  have hKm : MeasurableSet K := hK.measurableSet
  have hUm : MeasurableSet U := hU.measurableSet
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hηU
  obtain ⟨L, hL⟩ := (hf.mono hδ₀U).exists_lipschitzOnWith_of_compact hK.cthickening
  obtain ⟨g, hg, hfg⟩ := hL.extend_real
  have hKW : K ⊆ thickening δ₀ K := self_subset_thickening hδ₀ _
  have hfgK : ∀ x ∈ K, f x = g x := fun x hx ↦ hfg (self_subset_cthickening _ hx)
  have hDfg : ∀ x ∈ K, fderiv ℝ f x = fderiv ℝ g x := fun x hx ↦
    Filter.EventuallyEq.fderiv_eq (eventuallyEq_of_mem (isOpen_thickening.mem_nhds (hKW hx))
      (hfg.mono (thickening_subset_cthickening _ _)))
  have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
  have hη0 : ∀ x ∉ K, η x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hDη0 : ∀ x ∉ K, fderiv ℝ η x = 0 := fun x hx ↦ fderiv_of_notMem_tsupport ℝ hx
  have hgη0 : ∀ x ∉ K, ∇ η x = 0 := fun x hx ↦ by simp [gradient, hDη0 x hx]
  -- `∇f = 0` on `{f = 0} ∩ U`
  have hcrit : ∀ x ∈ U, f x = 0 → ∇ f x = 0 := by
    intro x hx hfx
    have : fderiv ℝ f x = 0 := by
      by_cases hd : DifferentiableAt ℝ f x
      · refine IsLocalMin.fderiv_eq_zero ?_
        filter_upwards [hU.mem_nhds hx] with y hy
        rw [hfx]; exact hf0 y hy
      · exact fderiv_zero_of_not_differentiableAt hd
    simp [gradient, this]
  -- bounds on `K`
  obtain ⟨B, hB⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hf hK hηU
  have hBg : ∀ x ∈ K, ‖∇ f x‖ ≤ B := fun x hx ↦ by
    rw [gradient, LinearIsometryEquiv.norm_map]; exact hB x hx
  obtain ⟨Mf, hMf⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hηU)
  obtain ⟨Mη, hMη⟩ := hηc.exists_bound_of_continuous hη.continuous
  have hgηc : Continuous (∇ η) :=
    (toDual ℝ (E d)).symm.continuous.comp (hη.continuous_fderiv one_ne_zero)
  obtain ⟨MD, hMD⟩ := (hηc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hη.continuous_fderiv one_ne_zero)
  have hMDg : ∀ x, ‖∇ η x‖ ≤ MD := fun x ↦ by
    rw [gradient, LinearIsometryEquiv.norm_map]; exact hMD x
  -- the integrands
  set A : ℝ → E d → ℝ := fun δ x ↦ a x * (max (f x - δ) 0 * η x)
  set F : ℝ → E d → ℝ := fun δ x ↦ (if δ < g x then (1 : ℝ) else 0) * (η x * ‖∇ f x‖ ^ 2) +
    max (f x - δ) 0 * inner ℝ (∇ f x) (∇ η x)
  have hA0 : ∀ δ, ∀ x ∉ K, A δ x = 0 := fun δ x hx ↦ by simp [A, hη0 x hx]
  have hF0 : ∀ δ, ∀ x ∉ K, F δ x = 0 := fun δ x hx ↦ by simp [F, hη0 x hx, hgη0 x hx]
  -- Step 1: the identity for `ζ_δ = (f - δ)₊ η`, `|{g = δ}| = 0`
  have hstep : ∀ δ, 0 < δ → volume {x | g x = δ} = 0 →
      ∫ x in U, A δ x = -∫ x in U, F δ x := by
    intro δ hδ hnull
    set ζ : E d → ℝ := fun y ↦ max (g y - δ) 0 * η y
    have hζeq : ∀ y, max (f y - δ) 0 * η y = ζ y := fun y ↦ by
      by_cases hy : y ∈ K
      · simp [ζ, hfgK y hy]
      · simp [ζ, hη0 y hy]
    have hζsupp : tsupport ζ ⊆ K ∩ {y | δ ≤ g y} := by
      refine closure_minimal (fun y hy ↦ ⟨?_, ?_⟩)
        (hK.isClosed.inter (isClosed_le continuous_const hg.continuous))
      · by_contra h'
        exact hy (by simp [ζ, hη0 y h'])
      · by_contra h'
        exact hy (by simp [ζ, max_eq_right (by simp at h'; linarith : g y - δ ≤ 0)])
    have hζpos : tsupport ζ ⊆ posSet f U := fun y hy ↦ by
      have h2 : δ ≤ g y := (hζsupp hy).2
      exact ⟨hηU (hζsupp hy).1, by rw [hfgK y (hζsupp hy).1]; linarith⟩
    have hζc : HasCompactSupport ζ :=
      hK.of_isClosed_subset (isClosed_tsupport _) (hζsupp.trans inter_subset_left)
    -- `ζ` is Lipschitz: it agrees with the product of two bounded Lipschitz functions
    have hζL : ∃ K, LipschitzWith K ζ := by
      obtain ⟨Kη, hKη⟩ := hη.lipschitzWith_of_hasCompactSupport hηc one_ne_zero
      set M := max Mf 0
      have hgδ : LipschitzWith L fun x ↦ g x - δ := LipschitzWith.of_dist_le_mul fun x y ↦ by
        simpa [Real.dist_eq] using hg.dist_le_mul x y
      obtain ⟨K₁, hK₁⟩ := lipschitzWith_mul_of_bounded
        ((hgδ.max_const 0).min_const M) hKη
        (Mf := M) (Mg := Mη) (fun x ↦ by
          rw [abs_le]
          constructor
          · have : 0 ≤ min (max (g x - δ) 0) M :=
              le_min (le_max_right _ _) (le_max_right _ _)
            linarith [le_max_right Mf 0]
          · exact min_le_right _ _) (fun x ↦ (Real.norm_eq_abs _).symm.trans_le (hMη x))
      refine ⟨K₁, ?_⟩
      convert hK₁ using 1
      funext y
      simp only [ζ]
      by_cases hy : y ∈ K
      · congr 1
        refine (min_eq_left ?_).symm
        refine max_le ?_ (le_max_right _ _)
        have := hMf y hy
        rw [← hfgK y hy]
        linarith [le_abs_self (f y), le_max_left Mf 0, (Real.norm_eq_abs (f y)).symm.trans_le this]
      · simp [hη0 y hy]
    have h := hid ζ hζL hζc hζpos
    have hl : ∫ x in U, A δ x = ∫ x in U, a x * ζ x :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [A, hζeq])
    rw [hl, h]
    congr 1
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hg.ae_differentiableAt, measure_eq_zero_iff_ae_notMem.1 hnull]
      with x hxd hxδ
    by_cases hxK : x ∈ K
    · rw [inner_gradient_eq_fderiv, fderiv_trunc_mul hxd (hηd x) hxδ]
      simp only [F, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ← hDfg x hxK, ← inner_gradient_eq_fderiv, real_inner_self_eq_norm_sq, hfgK x hxK]
    · have hx' : x ∉ tsupport ζ := fun h' ↦ hxK (hζsupp h').1
      rw [hF0 δ x hxK]
      simp [gradient, fderiv_of_notMem_tsupport ℝ hx']
  -- Step 2: `δ ↓ 0` along levels with `|{g = δ}| = 0`
  have hbad := Measure.countable_meas_level_set_pos (μ := volume) hg.continuous.measurable
  have hdense := hbad.dense_compl ℝ
  have hδj : ∀ j : ℕ, ∃ δ ∈ {t : ℝ | 0 < volume {x | g x = t}}ᶜ,
      δ ∈ Ioo 0 (1 / ((j : ℝ) + 1)) := fun j ↦ hdense.exists_between (by positivity)
  choose δ hδbad hδI using hδj
  have hδpos : ∀ j, 0 < δ j := fun j ↦ (hδI j).1
  have hδnull : ∀ j, volume {x | g x = δ j} = 0 := fun j ↦ by
    have := hδbad j
    simp only [mem_compl_iff, mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at this
    exact this
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun j ↦ (hδpos j).le) fun j ↦ (hδI j).2.le
  -- reduce to integrals over `K`
  have hredU : ∀ φ : E d → ℝ, (∀ x ∉ K, φ x = 0) → ∫ x in U, φ x = ∫ x in K, φ x :=
    fun φ hφ ↦ setIntegral_eq_of_subset_of_forall_diff_eq_zero hUm hηU fun x hx ↦ hφ x hx.2
  have hmeasf : AEStronglyMeasurable f (volume.restrict K) :=
    (hf.continuousOn.mono hηU).aestronglyMeasurable hKm
  have hmeasDf : Measurable fun x ↦ ∇ f x :=
    (toDual ℝ (E d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
  -- limit of the left side
  have hlimA : Tendsto (fun j ↦ ∫ x in K, A (δ j) x) atTop
      (𝓝 (∫ x in K, a x * (f x * η x))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖a x‖ * (Mf * Mη))
      (Eventually.of_forall fun j ↦ ?_) (Eventually.of_forall fun j ↦ ?_)
      ((ha K hK hηU).norm.mul_const _) ?_
    · exact (ha K hK hηU).aestronglyMeasurable.mul
        (((hmeasf.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const).mul
          hη.continuous.aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem hKm] with x hx
      have hfx := hf0 x (hηU hx)
      rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine mul_le_mul ?_ (hMη x) (norm_nonneg _) ((norm_nonneg _).trans (hMf x hx))
      refine (Real.norm_of_nonneg (le_max_right _ _)).trans_le ?_
      refine (max_le (by linarith [hδpos j]) hfx).trans ?_
      exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hMf x hx))
    · filter_upwards [ae_restrict_mem hKm] with x hx
      have hfx := hf0 x (hηU hx)
      have : Tendsto (fun j ↦ max (f x - δ j) 0) atTop (𝓝 (max (f x - 0) 0)) :=
        ((tendsto_const_nhds.sub hδlim).max tendsto_const_nhds)
      rw [sub_zero, max_eq_left hfx] at this
      exact tendsto_const_nhds.mul (this.mul tendsto_const_nhds)
  -- limit of the right side
  have hlimF : Tendsto (fun j ↦ ∫ x in K, F (δ j) x) atTop
      (𝓝 (∫ x in K, (‖∇ f x‖ ^ 2 * η x + f x * inner ℝ (∇ f x) (∇ η x)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ Mη * B ^ 2 + Mf * (B * MD))
      (Eventually.of_forall fun j ↦ ?_) (Eventually.of_forall fun j ↦ ?_)
      (integrable_const _) ?_
    · refine AEStronglyMeasurable.add ?_ ?_
      · refine AEStronglyMeasurable.mul ?_ ?_
        · exact (Measurable.ite (measurableSet_lt measurable_const hg.continuous.measurable)
            measurable_const measurable_const).aestronglyMeasurable
        · exact hη.continuous.aestronglyMeasurable.mul
            (hmeasDf.norm.pow_const 2).aestronglyMeasurable
      · exact ((hmeasf.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const).mul
          (hmeasDf.inner hgηc.measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hKm] with x hx
      have hfx := hf0 x (hηU hx)
      have hMf' : f x ≤ Mf := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hMf x hx))
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hBg x hx)
      have hm : max (f x - δ j) 0 ≤ Mf := max_le (by linarith [hδpos j]) (hfx.trans hMf')
      have hi : ‖(if δ j < g x then (1 : ℝ) else 0)‖ ≤ 1 := by split_ifs <;> simp
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]
        calc ‖(if δ j < g x then (1 : ℝ) else 0)‖ * ‖η x * ‖∇ f x‖ ^ 2‖ ≤ 1 * (Mη * B ^ 2) := by
              refine mul_le_mul hi ?_ (norm_nonneg _) zero_le_one
              rw [norm_mul, norm_pow, norm_norm]
              exact mul_le_mul (hMη x) (pow_le_pow_left₀ (norm_nonneg _) (hBg x hx) 2)
                (by positivity) ((norm_nonneg _).trans (hMη x))
          _ = Mη * B ^ 2 := one_mul _
      · rw [norm_mul, Real.norm_of_nonneg (le_max_right _ _)]
        exact mul_le_mul hm ((norm_inner_le_norm _ _).trans (mul_le_mul (hBg x hx) (hMDg x)
          (norm_nonneg _) hB0)) (norm_nonneg _) (hfx.trans hMf')
    · filter_upwards [ae_restrict_mem hKm] with x hx
      have hfx := hf0 x (hηU hx)
      rcases hfx.lt_or_eq with hpos | hzero
      · have hev : ∀ᶠ j in atTop, F (δ j) x = η x * ‖∇ f x‖ ^ 2 +
            max (f x - δ j) 0 * inner ℝ (∇ f x) (∇ η x) := by
          filter_upwards [hδlim.eventually (gt_mem_nhds (hfgK x hx ▸ hpos))] with j hj
          simp [F, hj]
        refine Tendsto.congr' (EventuallyEq.symm hev) ?_
        have : Tendsto (fun j ↦ max (f x - δ j) 0) atTop (𝓝 (max (f x - 0) 0)) :=
          ((tendsto_const_nhds.sub hδlim).max tendsto_const_nhds)
        rw [sub_zero, max_eq_left hfx] at this
        have h2 := tendsto_const_nhds (x := η x * ‖∇ f x‖ ^ 2) |>.add
          (this.mul (tendsto_const_nhds (x := inner ℝ (∇ f x) (∇ η x))))
        convert h2 using 2
        ring
      · have hg0 := hcrit x (hηU hx) hzero.symm
        simp [F, hg0]
  -- conclude
  have hlimA' := hlimA.congr fun j ↦ (hredU _ (hA0 (δ j))).symm
  have hlimF' := hlimF.congr fun j ↦ (hredU _ (hF0 (δ j))).symm
  have heq : ∀ j, ∫ x in U, A (δ j) x = -∫ x in U, F (δ j) x := fun j ↦
    hstep (δ j) (hδpos j) (hδnull j)
  rw [hredU _ fun x hx ↦ by simp [hη0 x hx], hredU _ fun x hx ↦ by simp [hη0 x hx, hgη0 x hx]]
  exact tendsto_nhds_unique hlimA' ((hlimF'.neg).congr fun j ↦ (heq j).symm)

end LongTime

end PerronVariational

end
