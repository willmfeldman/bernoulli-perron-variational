/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Selection of good times (proof of Theorem 3.10, Step 3)

Pure measure theory for the selection of the times `tᵢ` in Step 3 of the proof of **Theorem 3.10**
of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
the Bernoulli one-phase problem*, arXiv:2609.14981: Markov's inequality on unit time intervals for
countably many nonnegative functions simultaneously, avoiding a prescribed null set.

## Main results

* `PerronVariational.GoodTimes.measure_lt_mul_lintegral_le`: Markov's inequality in the form
  `μ {t | 2^(k+2) ∫ f < f t} ≤ 2^{-(k+2)}` (valid also when `∫ f ∈ {0, ∞}`).
* `PerronVariational.GoodTimes.exists_good_time`: in every interval `(a, a+1)` there is a time
  `t ∉ N` with `f k t ≤ 2^(k+2) ∫_{(a,a+1)} f k` for all `k`.
* `PerronVariational.GoodTimes.exists_good_times_seq`: the corresponding sequence `tᵢ ∈ (aᵢ, aᵢ+1)`.
* `PerronVariational.GoodTimes.tendsto_setLIntegral_Ioo_zero`: `∫_{(aᵢ, aᵢ+1)} g → 0` when
  `∫_{(0,∞)} g < ∞` and `aᵢ → ∞` (used for (4.13)).

The paper uses, for each `k ≤ i`, the threshold `C_k / θ` with `θ = 2^{-(k+1)}`, and a separate
threshold for `∫_U |∂ₜu(t)|²`; here all countably many functions are handled at once with the
thresholds `2^(k+2) ∫_{(a,a+1)} f k` (total exceptional measure `≤ 1/2`), which is all Step 3
needs.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

@[expose] public section

namespace PerronVariational

namespace GoodTimes

variable {α : Type*} [MeasurableSpace α]

/-- Markov's inequality with threshold `2^(k+2) ∫ f`: the set where `f` exceeds this threshold has
measure at most `2^{-(k+2)}` (also when `∫ f = 0` or `∫ f = ∞`). -/
theorem measure_lt_mul_lintegral_le (μ : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (k : ℕ) : μ {t | 2 ^ (k + 2) * ∫⁻ s, f s ∂μ < f t} ≤ 2⁻¹ ^ (k + 2) := by
  set I := ∫⁻ s, f s ∂μ with hI
  by_cases hI0 : I = 0
  · have hae : f =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hf).1 hI0
    have hnull : μ {t | 2 ^ (k + 2) * I < f t} = 0 := by
      refine measure_mono_null (fun t ht ↦ ?_) (ae_iff.1 hae)
      simp only [hI0, mul_zero, Set.mem_ofPred_eq] at ht
      exact ht.ne'
    simp [hnull]
  by_cases hItop : I = ⊤
  · have : {t | 2 ^ (k + 2) * I < f t} = ∅ := by
      ext t
      simp [hItop, ENNReal.mul_top (pow_ne_zero _ two_ne_zero)]
    simp [this]
  have hc0 : (2 : ℝ≥0∞) ^ (k + 2) * I ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hI0
  have hctop : (2 : ℝ≥0∞) ^ (k + 2) * I ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hItop
  calc μ {t | 2 ^ (k + 2) * I < f t}
      ≤ μ {t | 2 ^ (k + 2) * I ≤ f t} :=
        measure_mono fun t ht ↦ by simp only [Set.mem_ofPred_eq] at ht ⊢; exact ht.le
    _ ≤ I / (2 ^ (k + 2) * I) := meas_ge_le_lintegral_div hf hc0 hctop
    _ = 2⁻¹ ^ (k + 2) := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
        (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), mul_assoc,
        ENNReal.inv_mul_cancel hI0 hItop, mul_one, ENNReal.inv_pow]

/-- `∑_k 2^{-(k+2)} = 1/2 < 1`. -/
theorem tsum_inv_two_pow_add_two_lt_one : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 2) < 1 := by
  have h : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 2) = 2⁻¹ := by
    simp_rw [pow_add, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
      inv_inv]
    rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  rw [h]
  exact ENNReal.inv_lt_one.2 ENNReal.one_lt_two

/-- **Good time in a unit interval** (Markov + measure count, Step 3 of Theorem 3.10).
For a null set `N` and countably many functions `f k` (a.e.-measurable on `(a, a+1)`), there is
`t ∈ (a, a+1)`, `t ∉ N`, with `f k t ≤ 2^(k+2) ∫_{(a,a+1)} f k` for every `k`. -/
theorem exists_good_time (a : ℝ) {N : Set ℝ} (hN : volume N = 0) (f : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ k, AEMeasurable (f k) (volume.restrict (Ioo a (a + 1)))) :
    ∃ t ∈ Ioo a (a + 1), t ∉ N ∧
      ∀ k, f k t ≤ 2 ^ (k + 2) * ∫⁻ s in Ioo a (a + 1), f k s := by
  set μ := volume.restrict (Ioo a (a + 1))
  set B : Set ℝ := N ∪ ⋃ k, {t | 2 ^ (k + 2) * ∫⁻ s, f k s ∂μ < f k t}
  have hμN : μ N = 0 := le_antisymm ((Measure.restrict_le_self N).trans hN.le) bot_le
  have hB : μ B < 1 := by
    calc μ B ≤ μ N + μ (⋃ k, {t | 2 ^ (k + 2) * ∫⁻ s, f k s ∂μ < f k t}) := measure_union_le _ _
      _ ≤ 0 + ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 2) := by
        rw [hμN]
        gcongr
        exact (measure_iUnion_le _).trans
          (ENNReal.tsum_le_tsum fun k ↦ measure_lt_mul_lintegral_le μ (hf k) k)
      _ < 1 := by rw [zero_add]; exact tsum_inv_two_pow_add_two_lt_one
  have hμI : μ (Ioo a (a + 1)) = 1 := by
    simp [μ, Real.volume_Ioo]
  by_contra hcon
  push Not at hcon
  have hsub : Ioo a (a + 1) ⊆ B := by
    intro t ht
    by_contra htB
    simp only [B, mem_union, mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at htB
    obtain ⟨k, hk⟩ := hcon t ht htB.1
    exact (not_le.2 hk) (htB.2 k)
  exact absurd (hμI ▸ measure_mono hsub : (1 : ℝ≥0∞) ≤ μ B) (not_le.2 hB)

/-- **Sequence of good times** (Step 3 of Theorem 3.10): for intervals `(aᵢ, aᵢ + 1)`, a null set
`N` and countably many a.e.-measurable `f k`, there are `tᵢ ∈ (aᵢ, aᵢ + 1) \ N` with
`f k tᵢ ≤ 2^(k+2) ∫_{(aᵢ,aᵢ+1)} f k` for all `i, k`. -/
theorem exists_good_times_seq (a : ℕ → ℝ) {N : Set ℝ} (hN : volume N = 0)
    (f : ℕ → ℝ → ℝ≥0∞) (hf : ∀ k, AEMeasurable (f k)) :
    ∃ t : ℕ → ℝ, (∀ i, t i ∈ Ioo (a i) (a i + 1)) ∧ (∀ i, t i ∉ N) ∧
      ∀ i k, f k (t i) ≤ 2 ^ (k + 2) * ∫⁻ s in Ioo (a i) (a i + 1), f k s := by
  have h := fun i ↦ exists_good_time (a i) hN f fun k ↦ (hf k).restrict
  choose t ht hN' hf' using h
  exact ⟨t, ht, hN', hf'⟩

/-- If `∫_{(0,∞)} g < ∞` and `aᵢ → ∞`, then `∫_{(aᵢ, aᵢ+1)} g → 0` (tails of a finite integral;
used to obtain (4.13) from `∂ₜu ∈ L²(U_∞)`). -/
theorem tendsto_setLIntegral_Ioo_zero {g : ℝ → ℝ≥0∞} (hg : ∫⁻ t in Ioi 0, g t ≠ ⊤)
    {ι : Type*} {l : Filter ι} {a : ι → ℝ} (ha : Tendsto a l atTop) :
    Tendsto (fun i ↦ ∫⁻ t in Ioo (a i) (a i + 1), g t) l (𝓝 0) := by
  set ν := volume.withDensity g
  have hν : ∀ s, MeasurableSet s → ν s = ∫⁻ t in s, g t := fun s hs ↦ withDensity_apply _ hs
  -- tails `ν (Ioi n) → ν (⋂ n, Ioi n) = 0`
  have htail : Tendsto (fun n : ℕ ↦ ν (Ioi (n : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν) (s := fun n : ℕ ↦ Ioi (n : ℝ))
      (fun n ↦ measurableSet_Ioi.nullMeasurableSet)
      (fun m n hmn ↦ Ioi_subset_Ioi (Nat.cast_le.2 hmn)) ⟨0, by
        rw [hν _ measurableSet_Ioi]; simpa using hg⟩
    have hempty : (⋂ n : ℕ, Ioi (n : ℝ)) = ∅ := by
      ext x
      simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hn⟩
    rwa [hempty, measure_empty] at h
  rw [ENNReal.tendsto_nhds_zero] at htail ⊢
  intro ε hε
  obtain ⟨n, hn⟩ := (htail ε hε).exists_forall_of_atTop
  filter_upwards [ha.eventually_ge_atTop (n : ℝ)] with i hi
  calc ∫⁻ t in Ioo (a i) (a i + 1), g t = ν (Ioo (a i) (a i + 1)) :=
        (hν _ measurableSet_Ioo).symm
    _ ≤ ν (Ioi (n : ℝ)) := measure_mono fun t ht ↦ lt_of_le_of_lt hi ht.1
    _ ≤ ε := hn n le_rfl

end GoodTimes

end PerronVariational

end
