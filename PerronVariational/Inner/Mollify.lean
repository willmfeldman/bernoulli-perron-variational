/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Setting -- shake: keep
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension -- shake: keep
public import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Density of translated bumps for first-order linear functionals

Tool for the time localization in the proof of **Theorem 3.10** (Steps 2 and 4) of F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981: a functional
`Ψ(ζ) = ∫ a ζ + Dζ(g)` (with `a`, `g` integrable) that vanishes on all translates `ρₙ(· - q)`
(`q` in a countable dense set) of a fixed countable family of mollifiers `ρₙ` supported in `W`
vanishes on every Lipschitz `ζ` with compact support in `W`.

Proof: `y ↦ Ψ(ρₙ(· - y))` is continuous, hence vanishes for every `y` with `B̄(y, rₙ) ⊂ W`; by
Fubini `Ψ(ζ ⋆ ρₙ) = ∫ ζ(y) Ψ(ρₙ(· - y)) dy = 0`; finally `ζ ⋆ ρₙ → ζ` pointwise and
`D(ζ ⋆ ρₙ) = (Dζ) ⋆ ρₙ → Dζ` a.e. (integration by parts for Lipschitz functions,
`integral_lineDeriv_mul_eq`, and Lebesgue differentiation), boundedly, so `Ψ(ζ ⋆ ρₙ) → Ψ(ζ)`.

## Main definitions

* `PerronVariational.LongTime.bumpRad`, `PerronVariational.LongTime.moll`: the mollifiers
  `ρₙ` (normed smooth bumps supported in `B̄(0, 1/(n+1))`).
* `PerronVariational.LongTime.firstOrderFunctional`: `Ψ(ζ) = ∫ a ζ + Dζ(g) dμ`.
* `PerronVariational.LongTime.mollify`: `ρₙ ⋆ ζ`.

## Main results

* `PerronVariational.LongTime.fderiv_mollify_eq`: `D(ρₙ ⋆ ζ) = ρₙ ⋆ Dζ` for Lipschitz `ζ`.
* `PerronVariational.LongTime.ae_tendsto_fderiv_mollify`: `D(ρₙ ⋆ ζ) → Dζ` a.e.
* `PerronVariational.LongTime.firstOrderFunctional_eq_zero_of_bumps`.
-/

open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped Convolution ContDiff

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-! ### The mollifiers -/

/-- The radii `rₙ = 1/(n+1)`. -/
noncomputable def bumpRad (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem bumpRad_pos (n : ℕ) : 0 < bumpRad n := by unfold bumpRad; positivity

theorem tendsto_bumpRad : Tendsto bumpRad atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- The smooth bump with radii `rₙ/2 < rₙ`. -/
noncomputable def bumpN (d n : ℕ) : ContDiffBump (0 : E d) :=
  ⟨bumpRad n / 2, bumpRad n, by have := bumpRad_pos n; positivity,
    by have := bumpRad_pos n; linarith⟩

/-- The mollifier `ρₙ` (normalized: `∫ ρₙ = 1`, `ρₙ ≥ 0`, `spt ρₙ = B̄(0, rₙ)`). -/
noncomputable def moll (d n : ℕ) : E d → ℝ := (bumpN d n).normed volume

theorem contDiff_moll (n : ℕ) : ContDiff ℝ ∞ (moll d n) := (bumpN d n).contDiff_normed

theorem hasCompactSupport_moll (n : ℕ) : HasCompactSupport (moll d n) :=
  (bumpN d n).hasCompactSupport_normed

theorem tsupport_moll (n : ℕ) : tsupport (moll d n) = closedBall 0 (bumpRad n) :=
  (bumpN d n).tsupport_normed_eq

theorem moll_nonneg (n : ℕ) (x : E d) : 0 ≤ moll d n x := (bumpN d n).nonneg_normed x

theorem integral_moll (n : ℕ) : ∫ x, moll d n x = 1 := (bumpN d n).integral_normed

theorem exists_bound_moll (n : ℕ) :
    ∃ C, ∀ x, |moll d n x| ≤ C ∧ ‖fderiv ℝ (moll d n) x‖ ≤ C := by
  obtain ⟨C₁, h₁⟩ := (contDiff_moll (d := d) n).continuous.bounded_above_of_compact_support
    (hasCompactSupport_moll n)
  have hc := (contDiff_moll (d := d) n).continuous_fderiv (by simp)
  obtain ⟨C₂, h₂⟩ := hc.bounded_above_of_compact_support
    ((hasCompactSupport_moll n).fderiv (𝕜 := ℝ))
  exact ⟨max C₁ C₂, fun x ↦ ⟨(Real.norm_eq_abs _ ▸ h₁ x).trans (le_max_left _ _),
    (h₂ x).trans (le_max_right _ _)⟩⟩

theorem translate_moll_eq_zero_of_notMem {n : ℕ} {y x : E d}
    (hx : x ∉ closedBall y (bumpRad n)) : moll d n (x - y) = 0 := by
  have : x - y ∉ tsupport (moll d n) := by
    rw [tsupport_moll, mem_closedBall, dist_zero_right, ← dist_eq_norm]; exact hx
  exact image_eq_zero_of_notMem_tsupport this

theorem fderiv_translate_moll_eq_zero_of_notMem {n : ℕ} {y x : E d}
    (hx : x ∉ closedBall y (bumpRad n)) : fderiv ℝ (moll d n) (x - y) = 0 := by
  have : x - y ∉ tsupport (moll d n) := by
    rw [tsupport_moll, mem_closedBall, dist_zero_right, ← dist_eq_norm]; exact hx
  exact fderiv_of_notMem_tsupport ℝ this

/-! ### The functional -/

/-- The first-order functional `Ψ(ζ) = ∫ a ζ + Dζ(g) dμ`. -/
noncomputable def firstOrderFunctional (μ : Measure (E d)) (a : E d → ℝ) (g : E d → E d)
    (ζ : E d → ℝ) : ℝ :=
  ∫ x, a x * ζ x + fderiv ℝ ζ x (g x) ∂μ

section Core

variable {μ : Measure (E d)} [SFinite μ] {a : E d → ℝ} {g : E d → E d}

omit [SFinite μ] in
/-- `Ψ` on the translate `ρₙ(· - y)`. -/
theorem firstOrderFunctional_translate (n : ℕ) (y : E d) :
    firstOrderFunctional μ a g (fun x ↦ moll d n (x - y)) =
      ∫ x, a x * moll d n (x - y) + fderiv ℝ (moll d n) (x - y) (g x) ∂μ := by
  unfold firstOrderFunctional
  congr 1
  ext x
  rw [fderiv_comp_sub]

omit [SFinite μ] in
/-- `y ↦ Ψ(ρₙ(· - y))` is continuous. -/
theorem continuous_firstOrderFunctional_translate (ha : Integrable a μ) (hg : Integrable g μ)
    (n : ℕ) : Continuous fun y ↦ firstOrderFunctional μ a g (fun x ↦ moll d n (x - y)) := by
  simp_rw [firstOrderFunctional_translate]
  obtain ⟨C, hC⟩ := exists_bound_moll (d := d) n
  have hm := (contDiff_moll (d := d) n).continuous
  have hdm := (contDiff_moll (d := d) n).continuous_fderiv (by simp)
  refine continuous_of_dominated (bound := fun x ↦ C * (|a x| + ‖g x‖)) (fun y ↦ ?_)
    (fun y ↦ Eventually.of_forall fun x ↦ ?_) ((ha.abs.add hg.norm).const_mul C)
    (Eventually.of_forall fun x ↦ ?_)
  · refine (ha.aestronglyMeasurable.mul
      (hm.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).add ?_
    exact (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((hdm.comp (continuous_id.sub continuous_const)).aestronglyMeasurable.prodMk
        hg.aestronglyMeasurable))
  · have h1 := (hC (x - y)).1
    have h2 := (hC (x - y)).2
    have hC0 : 0 ≤ C := (abs_nonneg _).trans h1
    calc ‖a x * moll d n (x - y) + fderiv ℝ (moll d n) (x - y) (g x)‖
        ≤ |a x| * |moll d n (x - y)| + ‖fderiv ℝ (moll d n) (x - y)‖ * ‖g x‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ (le_opNorm _ _))
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |a x| * C + C * ‖g x‖ := by gcongr
      _ = C * (|a x| + ‖g x‖) := by ring
  · exact (continuous_const.mul (hm.comp (continuous_const.sub continuous_id))).add
      ((isBoundedBilinearMap_apply.continuous.comp
        ((hdm.comp (continuous_const.sub continuous_id)).prodMk continuous_const)))

omit [SFinite μ] in
/-- If `Ψ` vanishes on the translates `ρₙ(· - q)`, `q ∈ D` dense, supported in `W`, then it
vanishes on `ρₙ(· - y)` whenever `B̄(y, rₙ + s) ⊆ W` for some `s > 0`. -/
theorem firstOrderFunctional_translate_eq_zero (ha : Integrable a μ) (hg : Integrable g μ)
    {W D : Set (E d)} (hD : Dense D) (n : ℕ)
    (hH : ∀ q ∈ D, closedBall q (bumpRad n) ⊆ W →
      firstOrderFunctional μ a g (fun x ↦ moll d n (x - q)) = 0)
    {y : E d} {s : ℝ} (hs : 0 < s) (hy : closedBall y (bumpRad n + s) ⊆ W) :
    firstOrderFunctional μ a g (fun x ↦ moll d n (x - y)) = 0 := by
  by_contra hne
  have hopen : IsOpen ({z | firstOrderFunctional μ a g (fun x ↦ moll d n (x - z)) ≠ 0} ∩
      ball y s) :=
    (isOpen_ne_fun (continuous_firstOrderFunctional_translate ha hg n) continuous_const).inter
      isOpen_ball
  obtain ⟨q, hqD, hq0, hqy⟩ := hD.exists_mem_open hopen ⟨y, hne, mem_ball_self hs⟩
  refine hq0 (hH q hqD ((closedBall_subset_closedBall' ?_).trans hy))
  rw [mem_ball] at hqy
  linarith

end Core

/-! ### Mollification of Lipschitz functions -/

/-- The mollification `ρₙ ⋆ ζ`. -/
noncomputable def mollify (n : ℕ) (ζ : E d → ℝ) : E d → ℝ :=
  (moll d n ⋆[lsmul ℝ ℝ, volume] ζ : E d → ℝ)

theorem mollify_apply (n : ℕ) (ζ : E d → ℝ) (x : E d) :
    mollify n ζ x = ∫ t, moll d n (x - t) * ζ t := by
  simp [mollify, convolution_lsmul_swap, smul_eq_mul]

theorem fderiv_mollify_apply (n : ℕ) {ζ : E d → ℝ} (hζ : Continuous ζ) (x v : E d) :
    fderiv ℝ (mollify n ζ) x v = ∫ t, fderiv ℝ (moll d n) (x - t) v * ζ t := by
  have h := (hasCompactSupport_moll (d := d) n).hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    ((contDiff_moll n).of_le (by simp)) (hζ.locallyIntegrable (μ := volume)) x
  have hex := ((hasCompactSupport_moll (d := d) n).fderiv (𝕜 := ℝ)).convolutionExists_left
    ((lsmul ℝ ℝ).precompL (E d)) ((contDiff_moll n).continuous_fderiv (by simp))
    hζ.locallyIntegrable (μ := volume) x
  rw [mollify, h.fderiv, convolution_def, integral_apply hex]
  simp only [precompL_apply, lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self _ volume x]
  simp

theorem hasCompactSupport_moll_sub (n : ℕ) (x : E d) :
    HasCompactSupport fun t ↦ moll d n (x - t) :=
  (hasCompactSupport_moll n).comp_homeomorph (Homeomorph.subLeft x)

theorem hasFDerivAt_moll_sub (n : ℕ) (x t : E d) :
    HasFDerivAt (fun t ↦ moll d n (x - t)) (-(fderiv ℝ (moll d n) (x - t))) t := by
  have h1 : HasFDerivAt (fun t : E d ↦ x - t) (-ContinuousLinearMap.id ℝ (E d)) t := by
    have h := (hasFDerivAt_const (𝕜 := ℝ) x t).sub (hasFDerivAt_id t)
    rw [zero_sub] at h
    exact h
  have := ((contDiff_moll (d := d) n).differentiable (by simp) (x - t)).hasFDerivAt.comp t h1
  convert this using 1 <;> first | rfl | simp

/-- Integration by parts for the mollification of a Lipschitz function. -/
theorem integral_fderiv_moll_mul_eq {ζ : E d → ℝ} {K : NNReal} (hζ : LipschitzWith K ζ)
    (n : ℕ) (x v : E d) :
    ∫ t, fderiv ℝ (moll d n) (x - t) v * ζ t = ∫ t, moll d n (x - t) * fderiv ℝ ζ t v := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hasCompactSupport_moll_sub n x)
    (((contDiff_moll (d := d) n).comp (contDiff_const.sub contDiff_id)).of_le (by simp) :
      ContDiff ℝ 1 fun t ↦ moll d n (x - t)) (by simp)
  have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume) hζ hC
    (hasCompactSupport_moll_sub n x) v
  have e1 : ∀ t, lineDeriv ℝ (fun t ↦ moll d n (x - t)) t (-v) =
      fderiv ℝ (moll d n) (x - t) v := fun t ↦ by
    rw [((hasFDerivAt_moll_sub n x t).hasLineDerivAt (-v)).lineDeriv]
    simp
  simp_rw [e1] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [hζ.ae_differentiableAt] with t ht
  rw [ht.lineDeriv_eq_fderiv, mul_comm]

theorem locallyIntegrable_fderiv_of_lipschitz {ζ : E d → ℝ} {K : NNReal}
    (hζ : LipschitzWith K ζ) : LocallyIntegrable (fderiv ℝ ζ) volume :=
  (locallyIntegrable_const (K : ℝ)).mono (measurable_fderiv ℝ ζ).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by
      simpa using norm_fderiv_le_of_lipschitz ℝ hζ)

/-- For Lipschitz `ζ`, `D(ρₙ ⋆ ζ) = ρₙ ⋆ Dζ`. -/
theorem fderiv_mollify_eq {ζ : E d → ℝ} {K : NNReal} (hζ : LipschitzWith K ζ) (n : ℕ)
    (x : E d) :
    fderiv ℝ (mollify n ζ) x = (moll d n ⋆[lsmul ℝ ℝ, volume] fderiv ℝ ζ) x := by
  ext v
  have hex := (hasCompactSupport_moll (d := d) n).convolutionExists_left (lsmul ℝ ℝ)
    (contDiff_moll n).continuous (locallyIntegrable_fderiv_of_lipschitz hζ) x
  rw [fderiv_mollify_apply n hζ.continuous, integral_fderiv_moll_mul_eq hζ, convolution_def,
    integral_apply hex, ← integral_sub_left_eq_self _ volume x]
  simp

/-- `D(ρₙ ⋆ ζ) → Dζ` a.e. for Lipschitz `ζ` (Lebesgue differentiation). -/
theorem ae_tendsto_fderiv_mollify {ζ : E d → ℝ} {K : NNReal} (hζ : LipschitzWith K ζ) :
    ∀ᵐ x, Tendsto (fun n ↦ fderiv ℝ (mollify n ζ) x) atTop (𝓝 (fderiv ℝ ζ x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (φ := bumpN d) (l := atTop) (K := 2) tendsto_bumpRad
    (Eventually.of_forall fun n ↦ by simp [bumpN]; linarith)
    (locallyIntegrable_fderiv_of_lipschitz hζ)
  filter_upwards [h] with x hx
  simpa [fderiv_mollify_eq hζ, moll] using hx

theorem tendsto_mollify {ζ : E d → ℝ} (hζ : Continuous ζ) (x : E d) :
    Tendsto (fun n ↦ mollify n ζ x) atTop (𝓝 (ζ x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous (φ := bumpN d) tendsto_bumpRad hζ x

theorem norm_moll_convolution_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E d → F} {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (n : ℕ) (x : E d) :
    ‖(moll d n ⋆[lsmul ℝ ℝ, volume] f) x‖ ≤ B := by
  rw [convolution_lsmul_swap]
  calc ‖∫ t, moll d n (x - t) • f t‖ ≤ ∫ t, moll d n (x - t) * B := by
        refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun t ↦ ?_)
        · exact (((contDiff_moll (d := d) n).continuous.comp
            (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
            (hasCompactSupport_moll_sub n x)).mul_const B
        · rw [norm_smul, Real.norm_of_nonneg (moll_nonneg n _)]
          exact mul_le_mul_of_nonneg_left (hf t) (moll_nonneg n _)
    _ = B := by
        rw [integral_mul_const, integral_sub_left_eq_self (fun t ↦ moll d n t), integral_moll,
          one_mul]

theorem continuous_mollify (n : ℕ) {ζ : E d → ℝ} (hζ : Continuous ζ) :
    Continuous (mollify n ζ) :=
  (hasCompactSupport_moll (d := d) n).continuous_convolution_left (lsmul ℝ ℝ)
    (contDiff_moll n).continuous (hζ.locallyIntegrable (μ := volume))

section Density

variable {μ : Measure (E d)} [SFinite μ] {a : E d → ℝ} {g : E d → E d}

/-- `Ψ(ρₙ ⋆ ζ) = ∫ ζ(t) Ψ(ρₙ(· - t)) dt` (Fubini). -/
theorem firstOrderFunctional_mollify (ha : Integrable a μ) (hg : Integrable g μ) (n : ℕ)
    {ζ : E d → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) :
    firstOrderFunctional μ a g (mollify n ζ) =
      ∫ t, ζ t * firstOrderFunctional μ a g (fun x ↦ moll d n (x - t)) := by
  obtain ⟨C, hC⟩ := exists_bound_moll (d := d) n
  have hm := (contDiff_moll (d := d) n).continuous
  have hdm := (contDiff_moll (d := d) n).continuous_fderiv (by simp)
  set F : E d → E d → ℝ := fun x t ↦
    ζ t * (a x * moll d n (x - t) + fderiv ℝ (moll d n) (x - t) (g x)) with hF
  have hζi : Integrable ζ volume := hζ.integrable_of_hasCompactSupport hζc
  have hFi : Integrable (Function.uncurry F) (μ.prod volume) := by
    refine Integrable.mono' (((ha.abs.add hg.norm).const_mul C).mul_prod hζi.abs) ?_
      (Eventually.of_forall fun p ↦ ?_)
    · refine (hζ.comp continuous_snd).aestronglyMeasurable.mul ?_
      refine (ha.aestronglyMeasurable.comp_fst.mul
        (hm.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).add ?_
      exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((hdm.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.prodMk
          hg.aestronglyMeasurable.comp_fst)
    · obtain ⟨x, t⟩ := p
      have h1 := (hC (x - t)).1
      have h2 := (hC (x - t)).2
      have hC0 : 0 ≤ C := (abs_nonneg _).trans h1
      simp only [Function.uncurry_apply_pair, hF, norm_mul, Real.norm_eq_abs]
      rw [mul_comm]
      gcongr
      calc |a x * moll d n (x - t) + fderiv ℝ (moll d n) (x - t) (g x)|
          ≤ |a x| * |moll d n (x - t)| + ‖fderiv ℝ (moll d n) (x - t)‖ * ‖g x‖ := by
            refine (abs_add_le _ _).trans (add_le_add (abs_mul _ _).le ?_)
            rw [← Real.norm_eq_abs]; exact le_opNorm _ _
        _ ≤ |a x| * C + C * ‖g x‖ := by gcongr
        _ = C * (|a x| + ‖g x‖) := by ring
  have hint : firstOrderFunctional μ a g (mollify n ζ) = ∫ x, ∫ t, F x t ∂volume ∂μ := by
    unfold firstOrderFunctional
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    have i1 : Integrable (fun t ↦ ζ t * (a x * moll d n (x - t))) volume :=
      (hζ.mul (continuous_const.mul (hm.comp (continuous_const.sub continuous_id)))
        ).integrable_of_hasCompactSupport hζc.mul_right
    have i2 : Integrable (fun t ↦ ζ t * fderiv ℝ (moll d n) (x - t) (g x)) volume :=
      (hζ.mul (isBoundedBilinearMap_apply.continuous.comp
        ((hdm.comp (continuous_const.sub continuous_id)).prodMk continuous_const))
        ).integrable_of_hasCompactSupport hζc.mul_right
    simp only [hF, mul_add]
    rw [integral_add i1 i2, mollify_apply, fderiv_mollify_apply n hζ, ← integral_const_mul]
    congr 1
    · congr 1; ext t; ring
    · congr 1; ext t; ring
  rw [hint, integral_integral_swap hFi]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp only [hF]
  rw [integral_const_mul, firstOrderFunctional_translate]

omit [SFinite μ] in
/-- `Ψ(ρₙ ⋆ ζ) → Ψ(ζ)` for Lipschitz `ζ` with compact support (dominated convergence). -/
theorem tendsto_firstOrderFunctional_mollify (hμ : μ ≪ volume) (ha : Integrable a μ)
    (hg : Integrable g μ) {ζ : E d → ℝ} {K : NNReal} (hζ : LipschitzWith K ζ)
    (hζc : HasCompactSupport ζ) :
    Tendsto (fun n ↦ firstOrderFunctional μ a g (mollify n ζ)) atTop
      (𝓝 (firstOrderFunctional μ a g ζ)) := by
  obtain ⟨B, hB⟩ := hζc.exists_bound_of_continuous hζ.continuous
  unfold firstOrderFunctional
  refine tendsto_integral_of_dominated_convergence (fun x ↦ |a x| * B + K * ‖g x‖)
    (fun n ↦ ?_) ((ha.abs.mul_const B).add (hg.norm.const_mul K))
    (fun n ↦ Eventually.of_forall fun x ↦ ?_) ?_
  · exact (ha.aestronglyMeasurable.mul
      (continuous_mollify n hζ.continuous).aestronglyMeasurable).add
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((measurable_fderiv ℝ _).aestronglyMeasurable.prodMk hg.aestronglyMeasurable))
  · have h1 : |mollify n ζ x| ≤ B := by
      rw [← Real.norm_eq_abs, mollify]; exact norm_moll_convolution_le hB n x
    have h2 : ‖fderiv ℝ (mollify n ζ) x‖ ≤ K := by
      rw [fderiv_mollify_eq hζ]
      exact norm_moll_convolution_le (fun y ↦ norm_fderiv_le_of_lipschitz ℝ hζ) n x
    calc ‖a x * mollify n ζ x + fderiv ℝ (mollify n ζ) x (g x)‖
        ≤ |a x| * |mollify n ζ x| + ‖fderiv ℝ (mollify n ζ) x‖ * ‖g x‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ (le_opNorm _ _))
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |a x| * B + K * ‖g x‖ := by gcongr
  · filter_upwards [hμ.ae_le (ae_tendsto_fderiv_mollify hζ)] with x hx
    exact (tendsto_const_nhds.mul (tendsto_mollify hζ.continuous x)).add
      (((ContinuousLinearMap.apply ℝ ℝ (g x)).continuous.tendsto _).comp hx)

/-- **Density of translated bumps**: if `Ψ(ζ) = ∫ a ζ + Dζ(g) dμ` (`μ ≪ volume`, `a`, `g`
integrable) vanishes on every translate `ρₙ(· - q)`, `q ∈ D` dense, with `B̄(q, rₙ) ⊆ W`, then it
vanishes on every Lipschitz `ζ` with compact support in the open set `W`. -/
theorem firstOrderFunctional_eq_zero_of_bumps (hμ : μ ≪ volume) (ha : Integrable a μ)
    (hg : Integrable g μ) {W D : Set (E d)} (hW : IsOpen W) (hD : Dense D)
    (hH : ∀ n, ∀ q ∈ D, closedBall q (bumpRad n) ⊆ W →
      firstOrderFunctional μ a g (fun x ↦ moll d n (x - q)) = 0)
    {ζ : E d → ℝ} (hζ : ∃ K, LipschitzWith K ζ) (hζc : HasCompactSupport ζ)
    (hζW : tsupport ζ ⊆ W) :
    firstOrderFunctional μ a g ζ = 0 := by
  obtain ⟨K, hK⟩ := hζ
  obtain ⟨δ, hδ, hδW⟩ := hζc.isCompact.exists_cthickening_subset_open hW hζW
  have hev : ∀ᶠ n in atTop, firstOrderFunctional μ a g (mollify n ζ) = 0 := by
    filter_upwards [tendsto_bumpRad.eventually (gt_mem_nhds (half_pos hδ))] with n hn
    rw [firstOrderFunctional_mollify ha hg n hK.continuous hζc]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
    simp only [Pi.zero_apply]
    by_cases ht : t ∈ tsupport ζ
    · rw [firstOrderFunctional_translate_eq_zero ha hg hD n (hH n) (half_pos hδ)
        ((closedBall_subset_closedBall (by linarith)).trans
          ((closedBall_subset_cthickening ht δ).trans hδW)), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  exact tendsto_nhds_unique (tendsto_firstOrderFunctional_mollify hμ ha hg hK hζc)
    (tendsto_const_nhds.congr' (hev.mono fun n hn ↦ hn.symm))

end Density

end LongTime

end PerronVariational

end
