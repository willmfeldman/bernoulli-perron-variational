/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Sobolev -- shake: keep
public import PerronVariational.Defs.Semilinear
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.CompletePartialOrder
import PerronVariational.Semilinear.Profiles

/-!
# Limits of `χ_ε` (Lemma 4.3 and the proof of Proposition 4.1)

This file formalizes parts of Lemma 4.3 and of the proof of Proposition 4.1 of F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the
Bernoulli one-phase problem*, arXiv:2609.14981.

Pointwise facts about `χ_ε = 2 𝓑_ε(u_ε)` and their consequences for an a.e. limit `χ`:
* `Inner.chiEps_eq_one_of_le`: `χ_ε = 1` where `u_ε ≥ ε`;
* `Inner.chi_eq_one_of_pos`, `Inner.ae_chi_eq_one_of_pos`: `1_{u > 0} ≤ χ` (proof of Proposition
  4.1(ii));
* `Inner.ae_zero_or_one_of_tendsto`: `χ ∈ {0, 1}` a.e., from a local bound on `∫ β_ε(u_ε)`
  (end of the proof of Lemma 4.3, (4.11)).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ} {β : ℝ → ℝ}

/-- `χ_ε(p) = 1` where `u(p) ≥ ε`. -/
theorem chiEps_eq_one_of_le (hβ : IsReactionProfile β) {ε : ℝ} (hε : 0 < ε)
    {u : E d × ℝ → ℝ} {p : E d × ℝ} (hp : ε ≤ u p) : chiEps β ε u p = 1 := by
  rw [chiEps, IsReactionProfile.bigBEps_eq (β := β) hε.ne',
    hβ.bigB_of_one_le ((one_le_div hε).2 hp)]
  norm_num

/-- `0 ≤ χ_ε ≤ 1`. -/
theorem chiEps_mem_Icc (hβ : IsReactionProfile β) {ε : ℝ} (hε : 0 < ε) (u : E d × ℝ → ℝ)
    (p : E d × ℝ) : chiEps β ε u p ∈ Icc (0 : ℝ) 1 := by
  have h0 := hβ.bigBEps_nonneg hε.ne' (u p)
  have h1 := hβ.bigBEps_le_half hε.ne' (u p)
  simp only [chiEps, mem_Icc]
  constructor <;> linarith

/-- **`1_{u > 0} ≤ χ`, pointwise** (proof of Proposition 4.1(ii)): if `u_n(p) → u(p) > 0`,
`ε_n → 0⁺` and `χ_{ε_n}(u_n)(p) → χ(p)`, then `χ(p) = 1`. -/
theorem chi_eq_one_of_pos (hβ : IsReactionProfile β) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) {v : ℕ → E d × ℝ → ℝ} {u χ : E d × ℝ → ℝ} {p : E d × ℝ}
    (hvp : Tendsto (fun n ↦ v n p) atTop (𝓝 (u p)))
    (hχp : Tendsto (fun n ↦ chiEps β (ε n) (v n) p) atTop (𝓝 (χ p))) (hup : 0 < u p) :
    χ p = 1 := by
  have h1 : ∀ᶠ n in atTop, u p / 2 < v n p :=
    hvp.eventually (lt_mem_nhds (half_lt_self hup))
  have h2 : ∀ᶠ n in atTop, ε n < u p / 2 := hε0.eventually (gt_mem_nhds (half_pos hup))
  have hev : (fun _ : ℕ ↦ (1 : ℝ)) =ᶠ[atTop] fun n ↦ chiEps β (ε n) (v n) p := by
    filter_upwards [h1, h2] with n hn1 hn2
    exact (chiEps_eq_one_of_le hβ (hε n) (hn2.trans hn1).le).symm
  exact tendsto_nhds_unique hχp (tendsto_const_nhds.congr' hev)

/-- **`1_{u > 0} ≤ χ` a.e.** (proof of Proposition 4.1(ii)): pointwise convergence `u_n → u` on `Ω`
and a.e. convergence `χ_{ε_n}(u_n) → χ` on `Ω`, with `ε_n → 0⁺`. -/
theorem ae_chi_eq_one_of_pos (hβ : IsReactionProfile β) {Ω : Set (E d × ℝ)} {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) {v : ℕ → E d × ℝ → ℝ}
    {u χ : E d × ℝ → ℝ} (hv : ∀ p ∈ Ω, Tendsto (fun n ↦ v n p) atTop (𝓝 (u p)))
    (hΩ : MeasurableSet Ω)
    (hχ : ∀ᵐ p ∂(volume.restrict Ω), Tendsto (fun n ↦ chiEps β (ε n) (v n) p) atTop (𝓝 (χ p))) :
    ∀ᵐ p ∂(volume.restrict Ω), 0 < u p → χ p = 1 := by
  filter_upwards [hχ, ae_restrict_mem hΩ] with p hp hpΩ hup
  exact chi_eq_one_of_pos hβ hε hε0 (hv p hpΩ) hp hup

/-- Choice of the secondary parameter `δ₀` in the proof of Lemma 4.3:
`2 𝓑₁(δ₀) < δ` and `1 - δ < 2 𝓑₁(1 - δ₀)`. -/
theorem exists_bigB_margin (hβ : IsReactionProfile β) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ 2 * bigBEps β 1 δ₀ < δ ∧
      1 - δ < 2 * bigBEps β 1 (1 - δ₀) := by
  have h1 : ∀ᶠ z in 𝓝 (0 : ℝ), 2 * bigBEps β 1 z < δ := by
    have : Tendsto (fun z ↦ 2 * bigBEps β 1 z) (𝓝 0) (𝓝 (2 * bigBEps β 1 0)) :=
      (continuous_const.mul hβ.continuous_bigB).tendsto 0
    rw [hβ.bigB_of_nonpos le_rfl, mul_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  have h2 : ∀ᶠ z in 𝓝 (0 : ℝ), 1 - δ < 2 * bigBEps β 1 (1 - z) := by
    have : Tendsto (fun z ↦ 2 * bigBEps β 1 (1 - z)) (𝓝 0) (𝓝 (2 * bigBEps β 1 (1 - 0))) :=
      ((continuous_const.mul hβ.continuous_bigB).comp
        (continuous_const.sub continuous_id)).tendsto 0
    rw [sub_zero, hβ.bigB_one] at this
    exact this.eventually (lt_mem_nhds (by linarith))
  have h3 : ∀ᶠ z in 𝓝[>] (0 : ℝ), 0 < z ∧ z < 1 / 2 :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨z, ⟨hz0, hz1⟩, hz2, hz3⟩ :=
    (h3.and ((h1.filter_mono nhdsWithin_le_nhds).and (h2.filter_mono nhdsWithin_le_nhds))).exists
  exact ⟨z, hz0, hz1, hz2, hz3⟩

set_option maxHeartbeats 1000000 in
-- the measure bookkeeping below elaborates slowly
/-- Key measure estimate for `χ ∈ {0, 1}` (Lemma 4.3, (4.11)): on a
compact `K ⊆ Ω` with `∫_K β_{ε_n}(u_n) ≤ C` uniformly, the set where the a.e. limit `χ` lies in
`(δ, 1 - δ)` is null. -/
theorem volume_chi_mem_Ioo_eq_zero (hβ : IsReactionProfile β) {Ω K : Set (E d × ℝ)}
    (hKΩ : K ⊆ Ω) (hK : IsCompact K) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) {v : ℕ → E d × ℝ → ℝ} (hv : ∀ n, ContinuousOn (v n) Ω)
    {χ : E d × ℝ → ℝ} {C : ℝ}
    (hC : ∀ n, ∫⁻ p in K, ENNReal.ofReal (betaEps β (ε n) (v n p)) ≤ ENNReal.ofReal C)
    {δ : ℝ} (hδ : 0 < δ) :
    volume {p ∈ K | δ < χ p ∧ χ p < 1 - δ ∧
      Tendsto (fun n ↦ chiEps β (ε n) (v n) p) atTop (𝓝 (χ p))} = 0 := by
  obtain ⟨δ₀, hδ₀, hδ₀', hB0, hB1⟩ := exists_bigB_margin hβ hδ
  obtain ⟨c, hc, hcβ⟩ := hβ.exists_pos_le hδ₀ (by linarith : 1 - δ₀ < 1)
  set A : ℕ → Set (E d × ℝ) := fun n ↦
    {p ∈ K | δ < chiEps β (ε n) (v n) p ∧ chiEps β (ε n) (v n) p < 1 - δ} with hA
  have hAn : ∀ n, volume (A n) ≤ ENNReal.ofReal (C * ε n / c) := by
    intro n
    set f : E d × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (betaEps β (ε n) (v n p)) with hf
    have hfm : AEMeasurable f (volume.restrict K) :=
      ((ENNReal.continuous_ofReal.comp (hβ.continuous_betaEps _)).comp_continuousOn
        ((hv n).mono hKΩ)).aemeasurable hK.isClosed.measurableSet
    have hsub : A n ⊆ {p | ENNReal.ofReal (c / ε n) ≤ f p} := by
      rintro p ⟨-, hp1, hp2⟩
      simp only [chiEps, IsReactionProfile.bigBEps_eq (β := β) (hε n).ne'] at hp1 hp2
      have hlo : δ₀ ≤ v n p / ε n := by
        by_contra h
        have := hβ.bigB_monotone (not_le.1 h).le
        linarith
      have hhi : v n p / ε n ≤ 1 - δ₀ := by
        by_contra h
        have := hβ.bigB_monotone (not_le.1 h).le
        linarith
      simp only [Set.mem_ofPred_eq, hf, betaEps]
      exact ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hcβ _ ⟨hlo, hhi⟩) (hε n).le)
    have hmark := mul_meas_ge_le_lintegral₀ hfm (ENNReal.ofReal (c / ε n))
    have hpos : 0 < c / ε n := div_pos hc (hε n)
    have hne : ENNReal.ofReal (c / ε n) ≠ 0 := by simpa using hpos
    calc volume (A n) = volume (A n ∩ K) := by
          rw [inter_eq_left.2 (fun p hp ↦ hp.1)]
      _ ≤ volume.restrict K (A n) := Measure.le_restrict_apply _ _
      _ ≤ volume.restrict K {p | ENNReal.ofReal (c / ε n) ≤ f p} := measure_mono hsub
      _ ≤ ENNReal.ofReal C / ENNReal.ofReal (c / ε n) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
          exact hmark.trans (hC n)
      _ = ENNReal.ofReal (C * ε n / c) := by
          rw [← ENNReal.ofReal_div_of_pos hpos]
          congr 1
          field_simp
  have hsubA : {p ∈ K | δ < χ p ∧ χ p < 1 - δ ∧
      Tendsto (fun n ↦ chiEps β (ε n) (v n) p) atTop (𝓝 (χ p))} ⊆ ⋃ N, ⋂ n, A (n + N) := by
    rintro p ⟨hpK, h1, h2, hconv⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hconv.eventually (Ioo_mem_nhds h1 h2))
    exact mem_iUnion.2 ⟨N, mem_iInter.2 fun n ↦ ⟨hpK, (hN (n + N) (Nat.le_add_left _ _)).1,
      (hN (n + N) (Nat.le_add_left _ _)).2⟩⟩
  refine measure_mono_null hsubA (measure_iUnion_null fun N ↦ ?_)
  have hlim0 : Tendsto (fun n ↦ C * ε (n + N) / c) atTop (𝓝 (C * 0 / c)) :=
    (tendsto_const_nhds.mul (hε0.comp (tendsto_add_atTop_nat N))).div_const c
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (C * ε (n + N) / c)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hlim0
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim fun n ↦
    (measure_mono (iInter_subset _ n)).trans (hAn (n + N)))

/-- **`χ ∈ {0, 1}` a.e.** (end of the proof of Lemma 4.3): if `ε_n → 0⁺`, the `u_n`
are continuous on the open set `Ω`, `χ_{ε_n}(u_n) → χ` a.e. on `Ω`, and `∫_K β_{ε_n}(u_n)` is
bounded uniformly in `n` for every compact `K ⊆ Ω`, then `χ ∈ {0, 1}` a.e. on `Ω`. -/
theorem ae_zero_or_one_of_tendsto (hβ : IsReactionProfile β) {Ω : Set (E d × ℝ)}
    (hΩ : IsOpen Ω) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    {v : ℕ → E d × ℝ → ℝ} (hv : ∀ n, ContinuousOn (v n) Ω) {χ : E d × ℝ → ℝ}
    (hae : ∀ᵐ p ∂(volume.restrict Ω),
      Tendsto (fun n ↦ chiEps β (ε n) (v n) p) atTop (𝓝 (χ p)))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ n,
      ∫⁻ p in K, ENNReal.ofReal (betaEps β (ε n) (v n p)) ≤ ENNReal.ofReal C) :
    ∀ᵐ p ∂(volume.restrict Ω), χ p = 0 ∨ χ p = 1 := by
  have hΩσ : IsSigmaCompact Ω := by
    have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hKc, hKU⟩ := hΩσ
  have hKΩ : ∀ m, K m ⊆ Ω := fun m ↦ hKU ▸ subset_iUnion K m
  rw [ae_restrict_iff' hΩ.measurableSet] at hae ⊢
  have hnull : ∀ᵐ p ∂volume, ∀ m k : ℕ, p ∉ {p ∈ K m | 1 / ((k : ℝ) + 3) < χ p ∧
      χ p < 1 - 1 / ((k : ℝ) + 3) ∧
      Tendsto (fun n ↦ chiEps β (ε n) (v n) p) atTop (𝓝 (χ p))} := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro k
    obtain ⟨C, hC⟩ := hbd (K m) (hKΩ m) (hKc m)
    exact measure_eq_zero_iff_ae_notMem.1
      (volume_chi_mem_Ioo_eq_zero hβ (hKΩ m) (hKc m) hε hε0 hv hC (by positivity))
  filter_upwards [hae, hnull] with p hp hpn hpΩ
  have hconv := hp hpΩ
  have hmem : χ p ∈ Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hconv (Eventually.of_forall fun n ↦ chiEps_mem_Icc hβ (hε n) _ _)
  by_contra hne
  push Not at hne
  have h0 : 0 < χ p := lt_of_le_of_ne hmem.1 (Ne.symm hne.1)
  have h1 : 0 < 1 - χ p := sub_pos.2 (lt_of_le_of_ne hmem.2 hne.2)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_min h0 h1)
  have hk' : 1 / ((k : ℝ) + 3) < min (χ p) (1 - χ p) :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) hk
  obtain ⟨m, hm⟩ := mem_iUnion.1 (hKU.symm ▸ hpΩ : p ∈ ⋃ m, K m)
  exact hpn m k ⟨hm, (hk'.trans_le (min_le_left _ _)),
    by linarith [hk'.trans_le (min_le_right _ _)], hconv⟩

-- Lemma 4.3 (compactness part) is proved in `Inner/ChiCompact.lean`.

/-- `L¹_loc` convergence on an open set implies a.e. convergence along a subsequence. -/
theorem exists_subseq_ae_tendsto_of_tendstoLpLoc {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    {f : ℕ → E d × ℝ → ℝ} {f₀ : E d × ℝ → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict Ω))
    (hf₀ : AEStronglyMeasurable f₀ (volume.restrict Ω)) (h : TendstoLpLoc 1 volume Ω f f₀ atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ p ∂(volume.restrict Ω), Tendsto (fun n ↦ f (φ n) p) atTop (𝓝 (f₀ p)) := by
  have hΩσ : IsSigmaCompact Ω := by
    have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K₀, hK₀c, hK₀U⟩ := hΩσ
  set K := accumulate K₀ with hKdef
  have hKc : ∀ m, IsCompact (K m) := isCompact_accumulate hK₀c
  have hKΩ : ∀ m, K m ⊆ Ω := fun m ↦ (accumulate_subset_iUnion m).trans hK₀U.subset
  have hKmono : Monotone K := monotone_accumulate
  have hKU : ⋃ m, K m = Ω := by rw [iUnion_accumulate, hK₀U]
  have hev : ∀ k, ∀ᶠ n in atTop,
      eLpNorm (f n - f₀) 1 (volume.restrict (K k)) ≤ (2⁻¹ : ℝ≥0∞) ^ k := fun k ↦
    (h (K k) (hKΩ k) (hKc k)).eventually
      (Iic_mem_nhds (ENNReal.pow_pos (by norm_num) k))
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ?_⟩
  have hm : ∀ m, ∀ᵐ p ∂(volume.restrict (K m)),
      Tendsto (fun n ↦ f (φ n) p) atTop (𝓝 (f₀ p)) := by
    intro m
    have hmeasK : ∀ n, AEMeasurable (fun p ↦ ‖f (φ (n + m)) p - f₀ p‖ₑ)
        (volume.restrict (K m)) := fun n ↦
      (((hf _).sub hf₀).mono_measure (Measure.restrict_mono (hKΩ m) le_rfl)).enorm
    have hsum : ∫⁻ p in K m, ∑' n, ‖f (φ (n + m)) p - f₀ p‖ₑ ≠ ⊤ := by
      rw [lintegral_tsum hmeasK]
      refine ne_top_of_le_ne_top (b := ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) ?_
        (ENNReal.tsum_le_tsum fun n ↦ ?_)
      · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
        exact ENNReal.ofNat_ne_top
      · calc ∫⁻ p in K m, ‖f (φ (n + m)) p - f₀ p‖ₑ
            = eLpNorm (f (φ (n + m)) - f₀) 1 (volume.restrict (K m)) :=
              (eLpNorm_one_eq_lintegral_enorm
                (((hf _).sub hf₀).mono_measure (Measure.restrict_mono (hKΩ m) le_rfl))).symm
          _ ≤ eLpNorm (f (φ (n + m)) - f₀) 1 (volume.restrict (K (n + m))) :=
              eLpNorm_mono_measure _
                (Measure.restrict_mono (hKmono (Nat.le_add_left m n)) le_rfl)
          _ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + m) := hφP (n + m)
          _ ≤ (2⁻¹ : ℝ≥0∞) ^ n :=
              pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_add_right n m)
    have hae := ae_lt_top' (AEMeasurable.tsum hmeasK) hsum
    filter_upwards [hae] with p hp
    have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hp.ne
    have h1 : Tendsto (fun n ↦ f (φ (n + m)) p) atTop (𝓝 (f₀ p)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
      simpa [Function.comp_def] using this
    exact (tendsto_add_atTop_iff_nat m).1 h1
  rw [ae_restrict_iff' hΩ.measurableSet]
  have hall : ∀ᵐ p ∂volume, ∀ m, p ∈ K m → Tendsto (fun n ↦ f (φ n) p) atTop (𝓝 (f₀ p)) := by
    rw [ae_all_iff]
    intro m
    exact (ae_restrict_iff' (hKc m).isClosed.measurableSet).1 (hm m)
  filter_upwards [hall] with p hp hpΩ
  obtain ⟨m, hm'⟩ := mem_iUnion.1 (hKU.symm ▸ hpΩ : p ∈ ⋃ m, K m)
  exact hp m hm'

end Inner

end PerronVariational

end
