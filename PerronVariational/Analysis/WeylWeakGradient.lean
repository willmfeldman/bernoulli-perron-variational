/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Sobolev -- shake: keep
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import ViscositySolns.Applications.Laplace.Weyl.MeanValue
import Mathlib.MeasureTheory.Function.L2Space
import ViscositySolns.Applications.Laplace.Weyl.Weyl

/-!
# Weyl's lemma for functions with a weak gradient

If `u` is continuous on an open set `U ⊆ ℝᵈ`, has weak gradient `G` in `U`, and
`∫_U G · ∇φ = 0` for all test functions `φ`, then `u` is `C^∞` in `U` and `Δu = 0` in `U`
(`harmonic_of_hasWeakGradient`). `Registry/Elliptic.lean` states Weyl's lemma in this
form for the rest of the library.

The only step is distributional harmonicity (`weaklyHarmonicOn_of_hasWeakGradient`): testing the
weak gradient against `∂ᵢφ` in direction `eᵢ` and summing over `i` gives
`∫_U u Δφ = -∫_U G · ∇φ = 0`. Weyl's lemma for continuous weakly harmonic functions
(`ViscositySolns.Analysis.weyl_of_weaklyHarmonicOn`, from viscosity-solution-theory v0.2.0) then
applies.
-/

open InnerProductSpace MeasureTheory Set
open scoped ContDiff Gradient Laplacian
open ViscositySolns.Analysis (WeaklyHarmonicOn weyl_of_weaklyHarmonicOn
  laplacian_eq_sum_fderiv_fderiv tsupport_laplacian_subset)

@[expose] public section

namespace PerronVariational

namespace Analysis

variable {d : ℕ}

/-- A function locally integrable on an open set `U`, times a continuous function with compact
support in `U`, is integrable on `U`. -/
theorem integrableOn_mul_of_tsupport_subset {U : Set (E d)} (hU : IsOpen U) {g ψ : E d → ℝ}
    (hg : LocallyIntegrableOn g U) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) : IntegrableOn (fun x ↦ g x * ψ x) U := by
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := tsupport ψ) ?_ hU.measurableSet fun x hx ↦ ?_
  · exact (hg.integrableOn_compact_subset hψU hψc.isCompact).mul_continuousOn hψ.continuousOn
      hψc.isCompact
  · simp [image_eq_zero_of_notMem_tsupport hx.2]

/-- **Distributional harmonicity.** If `G` is a weak gradient of `u` in the open set `U` and
`∫_U G · ∇φ = 0` for all test functions `φ`, then `u` is weakly harmonic in `U`. -/
theorem weaklyHarmonicOn_of_hasWeakGradient {U : Set (E d)} {u : E d → ℝ} {G : E d → E d}
    (hU : IsOpen U) (hG : HasWeakGradient U u G)
    (hweak : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, inner ℝ (G x) (∇ φ x) = 0) :
    WeaklyHarmonicOn volume u U := by
  intro χ hχ hχc hχU
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  -- the partial derivatives `∂ᵢχ` are test functions
  set D : Fin d → E d → ℝ := fun i y ↦ fderiv ℝ χ y (b i) with hD_def
  have hDs : ∀ i, ContDiff ℝ ∞ (D i) := fun i ↦
    (hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hDc : ∀ i, HasCompactSupport (D i) := fun i ↦ hχc.fderiv_apply (𝕜 := ℝ) (b i)
  have hDU : ∀ i, tsupport (D i) ⊆ U := fun i ↦ (tsupport_fderiv_apply_subset ℝ (b i)).trans hχU
  have hDDc : ∀ i, Continuous fun y ↦ fderiv ℝ (D i) y (b i) := fun i ↦
    ((hDs i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hDDs : ∀ i, HasCompactSupport fun y ↦ fderiv ℝ (D i) y (b i) := fun i ↦
    (hDc i).fderiv_apply (𝕜 := ℝ) (b i)
  have hDDU : ∀ i, tsupport (fun y ↦ fderiv ℝ (D i) y (b i)) ⊆ U := fun i ↦
    (tsupport_fderiv_apply_subset ℝ (b i)).trans (hDU i)
  -- `∫_U u Δχ = ∑ᵢ ∫_U u ∂ᵢ∂ᵢχ`
  have hΔ : ∀ x, Δ χ x = ∑ i, fderiv ℝ (D i) x (b i) := fun x ↦
    laplacian_eq_sum_fderiv_fderiv b (hχ.of_le (by norm_cast)) x
  have hlhs : ∫ x in U, u x * Δ χ x = ∑ i, ∫ x in U, u x * fderiv ℝ (D i) x (b i) := by
    simp_rw [hΔ, Finset.mul_sum]
    exact integral_finsetSum _ fun i _ ↦
      integrableOn_mul_of_tsupport_subset hU hG.1 (hDDc i) (hDDs i) (hDDU i)
  -- `∑ᵢ ∫_U ⟪G, eᵢ⟫ ∂ᵢχ = ∫_U ⟪G, ∇χ⟫ = 0`
  have hGi : ∀ i, LocallyIntegrableOn (fun x ↦ inner ℝ (G x) (b i)) U := fun i ↦
    fun x hx ↦ by
      obtain ⟨t, ht, hGt⟩ := hG.2.1 x hx
      exact ⟨t, ht, Integrable.inner_const hGt (b i)⟩
  have hrhs : ∑ i, ∫ x in U, inner ℝ (G x) (b i) * D i x = ∫ x in U, inner ℝ (G x) (∇ χ x) := by
    rw [← integral_finsetSum _ fun i _ ↦
      integrableOn_mul_of_tsupport_subset hU (hGi i) (hDs i).continuous (hDc i) (hDU i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [← b.sum_inner_mul_inner (G x) (∇ χ x)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm (∇ χ x) (b i), gradient, toDual_symm_apply]
  have hsum : ∫ x in U, u x * Δ χ x = 0 := by
    rw [hlhs, Finset.sum_congr rfl fun i _ ↦ hG.2.2 (D i) (hDs i) (hDc i) (hDU i) (b i),
      Finset.sum_neg_distrib, hrhs, hweak χ hχ hχc hχU, neg_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_]
  · simpa [smul_eq_mul, mul_comm] using hsum
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχU (tsupport_laplacian_subset _ h)),
      zero_smul]

/-- **Weyl's lemma, weak-gradient form**. If `u` is continuous on the open set
`U`, has weak gradient `G` in `U`, and `∫_U G · ∇φ = 0` for all test functions `φ`, then `u` is
`C^∞` in `U` and `Δu = 0` in `U`. -/
theorem harmonic_of_hasWeakGradient {U : Set (E d)} {u : E d → ℝ} {G : E d → E d}
    (hU : IsOpen U) (hu : ContinuousOn u U) (hG : HasWeakGradient U u G)
    (hweak : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, inner ℝ (G x) (∇ φ x) = 0) :
    ContDiffOn ℝ ∞ u U ∧ ∀ x ∈ U, Δ u x = 0 :=
  weyl_of_weaklyHarmonicOn hU hu (weaklyHarmonicOn_of_hasWeakGradient hU hG hweak)

end Analysis

end PerronVariational

end
