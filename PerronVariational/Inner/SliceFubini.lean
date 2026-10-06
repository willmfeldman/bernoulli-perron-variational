/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Setting -- shake: keep
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Order.CompletePartialOrder

/-!
# Time slices of space-time integrals

Tools for the time localization in the proof of **Theorem 3.10** (Steps 2 and 4) of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
the Bernoulli one-phase problem*, arXiv:2609.14981:

* `PerronVariational.LongTime.ae_setIntegral_slice_eq_zero`: du Bois-Reymond in time: if
  `∫_{A × I} ψ(s) h(x, s) = 0` for all `ψ ∈ C_c^∞(T)` (`T ⊆ I` open), then
  `∫_A h(·, s) = 0` for a.e. `s ∈ T`.
* `PerronVariational.LongTime.isOpen_setOf_forall_prod_mem`: `{s | K × {s} ⊆ O}` is open for
  `K` compact and `O` open (tube lemma).

(`exists_bound_of_isCompact`, formerly here, is now `GMTFoundations.exists_bound_of_isCompact` in
`GMTFoundations/Sobolev/Lipschitz.lean` of gmt-foundations v0.1.0.)
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-- **du Bois-Reymond in time.** -/
theorem ae_setIntegral_slice_eq_zero {A : Set (E d)} {I T : Set ℝ} (hA : MeasurableSet A)
    (hI : MeasurableSet I) (hT : IsOpen T) (hTI : T ⊆ I) {h : E d × ℝ → ℝ}
    (hint : ∀ J ⊆ T, IsCompact J → IntegrableOn h (A ×ˢ J))
    (hψ : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ T →
      ∫ p in A ×ˢ I, ψ p.2 * h p = 0) :
    ∀ᵐ s, s ∈ T → ∫ x in A, h (x, s) = 0 := by
  have hslice : ∀ J ⊆ T, IsCompact J →
      IntegrableOn (fun s ↦ ∫ x in A, h (x, s)) J := by
    intro J hJT hJ
    have := hint J hJT hJ
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at this
    exact this.integral_prod_right
  refine hT.ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ fun ψ hψs hψc hψT ↦ ?_
  · intro s hs
    obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.1 hT s hs
    refine ⟨closedBall s (ε / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds s
      (half_pos hε)), hslice _ ((closedBall_subset_ball (half_lt_self hε)).trans hεT)
      (isCompact_closedBall s _)⟩
  · set J := tsupport ψ
    have hJ : IsCompact J := hψc
    have hJm : MeasurableSet J := (isClosed_tsupport ψ).measurableSet
    have hψb : ∃ C, ∀ s, ‖ψ s‖ ≤ C := hψc.exists_bound_of_continuous hψs.continuous
    obtain ⟨C, hC⟩ := hψb
    have hint' : IntegrableOn (fun p : E d × ℝ ↦ ψ p.2 * h p) (A ×ˢ J) := by
      refine (hint J hψT hJ).bdd_mul (c := C) ?_ (Eventually.of_forall fun p ↦ hC p.2)
      exact (hψs.continuous.comp continuous_snd).aestronglyMeasurable
    have hzero : ∀ s ∉ J, ψ s = 0 := fun s hs ↦ image_eq_zero_of_notMem_tsupport hs
    have e1 : ∫ p in A ×ˢ I, ψ p.2 * h p = ∫ p in A ×ˢ J, ψ p.2 * h p := by
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hA.prod hI)
        (Set.prod_mono le_rfl ((hψT).trans hTI)) ?_
      · intro p hp
        have : p.2 ∉ J := fun h' ↦ hp.2 ⟨hp.1.1, h'⟩
        rw [hzero _ this, zero_mul]
    have e2 : ∫ p in A ×ˢ J, ψ p.2 * h p = ∫ s in J, ∫ x in A, ψ s * h (x, s) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint'
      exact integral_prod_symm _ hint'
    have e3 : ∫ s in J, ∫ x in A, ψ s * h (x, s) = ∫ s, ψ s • ∫ x in A, h (x, s) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := J)
        (f := fun s ↦ ψ s • ∫ x in A, h (x, s)) fun s hs ↦ by simp [hzero s hs]]
      refine setIntegral_congr_fun hJm fun s _ ↦ ?_
      rw [smul_eq_mul, integral_const_mul]
    rw [← e3, ← e2, ← e1]
    exact hψ ψ hψs hψc hψT

/-- **Tube lemma**: `{s | ∀ x ∈ K, (x, s) ∈ O}` is open for `K` compact and `O` open. -/
theorem isOpen_setOf_forall_prod_mem {K : Set (E d)} (hK : IsCompact K) {O : Set (E d × ℝ)}
    (hO : IsOpen O) : IsOpen {s : ℝ | ∀ x ∈ K, (x, s) ∈ O} := by
  refine isOpen_iff_mem_nhds.2 fun s hs ↦ ?_
  obtain ⟨u, v, -, hv, hKu, hsv, huv⟩ := generalized_tube_lemma hK (isCompact_singleton (x := s))
    hO (fun p hp ↦ by
      obtain ⟨x, t⟩ := p
      obtain ⟨hx, ht⟩ := hp
      have ht' : t = s := ht
      subst ht'; exact hs x hx)
  exact Filter.mem_of_superset (hv.mem_nhds (hsv rfl)) fun s' hs' x hx ↦ huv ⟨hKu hx, hs'⟩

end LongTime

end PerronVariational

end
