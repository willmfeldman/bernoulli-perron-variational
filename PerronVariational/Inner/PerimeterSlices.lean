/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import PerronVariational.Defs.Parabolic
import GMTFoundations.BV.TotalVariation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Slicing the spatial perimeter in time

Tool for **Theorem 3.10**, Step 3, of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981:
the partial variation `∫ η |∇ₓχ|` of a space-time
function controls the time integral of the variations of its time slices,
`∫ ψ(t) ∫_V |∇χ(·, t)| dt ≤ ∫ η |∇ₓχ|` for `η(x, t) = φ(x) ψ(t)` with `φ = 1` on `V`.

Proof: the total variation `∫_V |∇χ(·, t)|` is dominated by the supremum `F(t)` of
`a_j(t) = ∫_V χ(·, t) div φ_j` over a countable family of test fields `φ_j` (dense for the `L¹(V)`
distance of the divergences, by separability of `L¹`), which is measurable in `t`. For finitely
many `j`, split the time interval `(a, b)` into the measurable sets `B_j` where `j` is the first
maximizer, smooth the indicators `1_{B_j}` by mollification, test the partial variation with
`Ψₙ(x, t) = ∑_j (ρₙ ⋆ 1_{B_j})(t) φ_j(x)`, and let `n → ∞` (dominated convergence).

## Main results

* `PerronVariational.LongTime.exists_TV_family`: the countable family of test fields.
* `PerronVariational.LongTime.totalVariationOn_le_sliceTV`: `∫_V |∇χ(·, t)| ≤ F(t)` for `t > 0`.
* `PerronVariational.LongTime.setLIntegral_sliceTV_le`: `∫_{(a, b)} F ≤ ∫_{U_∞} η |∇ₓχ|`.
* `PerronVariational.LongTime.weightDist_prodWeight`, `weightTimeLength_prodWeight`,
  `l2H1Norm_prodWeight`: the parameters of (3.13) for `η(x, t) = θ(x) ψ(t - c)` do not depend
  on the time shift `c` once `c ≥ diam U + 2`.
-/

open Set Function Filter Topology MeasureTheory Metric InnerProductSpace ContinuousLinearMap
open scoped Gradient ContDiff NNReal ENNReal Convolution

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-! ### A countable family of test fields computing the total variation -/

theorem isTVTestField_zero (V : Set (E d)) : IsTVTestField V 1 (fun _ ↦ (0 : E d)) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp, fun x ↦ by simp⟩

theorem integrable_divergence_of_isTVTestField {V : Set (E d)} {ξ : E d → E d}
    (hξ : IsTVTestField V 1 ξ) (μ : Measure (E d)) [IsFiniteMeasureOnCompacts μ] :
    Integrable (divergence ξ) μ := by
  refine (GMTFoundations.continuous_divergence hξ.1).integrable_of_hasCompactSupport ?_
  refine hξ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport _) ?_
  refine closure_minimal (fun x hx ↦ ?_) (isClosed_tsupport _)
  by_contra h'
  exact hx (by simp [divergence, fderiv_of_notMem_tsupport ℝ h'])

/-- **A countable family of test fields**, containing `0` and dense (for the `L¹(V)` distance
of the divergences) among the test fields of `totalVariationOn V`. -/
theorem exists_TV_family (V : Set (E d)) :
    ∃ φ : ℕ → E d → E d, φ 0 = (fun _ ↦ 0) ∧ (∀ j, IsTVTestField V 1 (φ j)) ∧
      ∀ ξ, IsTVTestField V 1 ξ → ∀ ε > 0, ∃ j,
        ∫⁻ x in V, edist (divergence (φ j) x) (divergence ξ x) < ENNReal.ofReal ε := by
  set T := {ξ : E d → E d // IsTVTestField V 1 ξ}
  have hint : ∀ ξ : T, Integrable (divergence ξ.1) (volume.restrict V) := fun ξ ↦
    integrable_divergence_of_isTVTestField ξ.2 _
  set L : T → E d →₁[volume.restrict V] ℝ := fun ξ ↦ (hint ξ).toL1 _
  set R := range L
  haveI : Nonempty R := ⟨⟨L ⟨_, isTVTestField_zero V⟩, mem_range_self _⟩⟩
  haveI : Fact ((1 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  haveI : SecondCountableTopology (E d →₁[volume.restrict V] ℝ) := inferInstance
  haveI : SecondCountableTopology R := inferInstance
  haveI : TopologicalSpace.SeparableSpace R := inferInstance
  have hdense := TopologicalSpace.denseRange_denseSeq R
  set seq := TopologicalSpace.denseSeq R
  have hpre : ∀ j, ∃ ξ : T, L ξ = (seq j).1 := fun j ↦ (seq j).2
  choose ξs hξs using hpre
  refine ⟨fun j ↦ Nat.casesOn j (fun _ ↦ 0) fun j ↦ (ξs j).1, rfl, fun j ↦ ?_, ?_⟩
  · cases j with
    | zero => exact isTVTestField_zero V
    | succ j => exact (ξs j).2
  · intro ξ hξ ε hε
    obtain ⟨j, hj⟩ := hdense.exists_dist_lt (⟨L ⟨ξ, hξ⟩, mem_range_self _⟩ : R) hε
    refine ⟨j + 1, ?_⟩
    have hj' : dist (L (ξs j)) (L ⟨ξ, hξ⟩) < ε := by
      rw [hξs j, dist_comm]; exact hj
    rw [← edist_lt_ofReal, Integrable.edist_toL1_toL1] at hj'
    exact hj'

/-! ### The slice values `a_j(t)` and their running maxima -/

theorem divergence_eq_zero_of_notMem_tsupport {ξ : E d → E d} {x : E d} (hx : x ∉ tsupport ξ) :
    divergence ξ x = 0 := by
  simp [divergence, fderiv_of_notMem_tsupport ℝ hx]

/-- `a_j(t) = ∫ χ(x, t) div φ_j(x) dx`. -/
noncomputable def sliceVal (χ : E d × ℝ → ℝ) (φ : ℕ → E d → E d) (j : ℕ) (t : ℝ) : ℝ :=
  ∫ x, χ (x, t) * divergence (φ j) x

/-- `m_N(t) = max_{j ≤ N} a_j(t)`. -/
noncomputable def sliceMax (χ : E d × ℝ → ℝ) (φ : ℕ → E d → E d) (N : ℕ) (t : ℝ) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j ↦ sliceVal χ φ j t

/-- `F(t) = sup_j (a_j(t))₊`, the measurable majorant of the slice total variations. -/
noncomputable def sliceTV (χ : E d × ℝ → ℝ) (φ : ℕ → E d → E d) (t : ℝ) : ℝ≥0∞ :=
  ⨆ N, ENNReal.ofReal (sliceMax χ φ N t)

theorem measurable_sliceVal {χ : E d × ℝ → ℝ} (hχ : Measurable χ) {φ : ℕ → E d → E d}
    (hφ : ∀ j, ContDiff ℝ 1 (φ j)) (j : ℕ) : Measurable (sliceVal χ φ j) :=
  (hχ.mul ((GMTFoundations.continuous_divergence (hφ j)).measurable.comp
    measurable_fst)).stronglyMeasurable
    |>.integral_prod_left' (μ := volume) |>.measurable

theorem measurable_sliceMax {χ : E d × ℝ → ℝ} (hχ : Measurable χ) {φ : ℕ → E d → E d}
    (hφ : ∀ j, ContDiff ℝ 1 (φ j)) (N : ℕ) : Measurable (sliceMax χ φ N) := by
  have h := Finset.measurable_range_sup' (n := N) (f := sliceVal χ φ)
    fun k _ ↦ measurable_sliceVal hχ hφ k
  convert h using 1
  funext t
  simp [sliceMax, Finset.sup'_apply]

theorem measurable_sliceTV {χ : E d × ℝ → ℝ} (hχ : Measurable χ) {φ : ℕ → E d → E d}
    (hφ : ∀ j, ContDiff ℝ 1 (φ j)) : Measurable (sliceTV χ φ) :=
  Measurable.iSup fun N ↦ ENNReal.measurable_ofReal.comp (measurable_sliceMax hχ hφ N)

theorem sliceVal_le_sliceMax (χ : E d × ℝ → ℝ) (φ : ℕ → E d → E d) {j N : ℕ} (hj : j ≤ N)
    (t : ℝ) : sliceVal χ φ j t ≤ sliceMax χ φ N t :=
  Finset.le_sup' (fun j ↦ sliceVal χ φ j t) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem sliceMax_mono (χ : E d × ℝ → ℝ) (φ : ℕ → E d → E d) (t : ℝ) :
    Monotone fun N ↦ sliceMax χ φ N t := fun N N' hNN' ↦
  Finset.sup'_mono _ (Finset.range_subset_range.2 (by omega)) _

variable {U V : Set (E d)} {χ : E d × ℝ → ℝ}

/-- For `t > 0`, `x ↦ χ(x, t) div ξ(x)` is dominated by `|div ξ|` (`|χ| ≤ 1` on `U_∞`). -/
theorem norm_slice_mul_divergence_le (hVU : V ⊆ U) (hχ : ∀ p ∈ UInf U, |χ p| ≤ 1)
    {ξ : E d → E d} (hξ : tsupport ξ ⊆ V) {t : ℝ} (ht : 0 < t) (x : E d) :
    ‖χ (x, t) * divergence ξ x‖ ≤ ‖divergence ξ x‖ := by
  by_cases hx : x ∈ tsupport ξ
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ _ ⟨hVU (hξ hx), ht⟩)
  · simp [divergence_eq_zero_of_notMem_tsupport hx]

theorem integrable_slice_mul_divergence (hVU : V ⊆ U) (hχm : Measurable χ)
    (hχ : ∀ p ∈ UInf U, |χ p| ≤ 1) {ξ : E d → E d} (hξ : IsTVTestField V 1 ξ) {t : ℝ}
    (ht : 0 < t) : Integrable (fun x ↦ χ (x, t) * divergence ξ x) :=
  (integrable_divergence_of_isTVTestField hξ volume).norm.mono'
    ((hχm.comp measurable_prodMk_right).mul
      (GMTFoundations.continuous_divergence hξ.1).measurable).aestronglyMeasurable
    (Eventually.of_forall (norm_slice_mul_divergence_le hVU hχ hξ.2.2.1 ht))

theorem abs_sliceVal_le (hVU : V ⊆ U) (hχ : ∀ p ∈ UInf U, |χ p| ≤ 1) {φ : ℕ → E d → E d}
    (hφ : ∀ j, IsTVTestField V 1 (φ j)) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    |sliceVal χ φ j t| ≤ ∫ x, |divergence (φ j) x| :=
  norm_integral_le_of_norm_le (integrable_divergence_of_isTVTestField (hφ j) volume).abs
    (Eventually.of_forall fun x ↦ (norm_slice_mul_divergence_le hVU hχ (hφ j).2.2.1 ht x).trans_eq
      (Real.norm_eq_abs _))

/-- **The slice total variation is dominated by `F`** (for `t > 0`). -/
theorem totalVariationOn_le_sliceTV (hVm : MeasurableSet V) (hVU : V ⊆ U) (hχm : Measurable χ)
    (hχ : ∀ p ∈ UInf U, |χ p| ≤ 1) {φ : ℕ → E d → E d} (hφ : ∀ j, IsTVTestField V 1 (φ j))
    (hdense : ∀ ξ, IsTVTestField V 1 ξ → ∀ ε > 0, ∃ j,
        ∫⁻ x in V, edist (divergence (φ j) x) (divergence ξ x) < ENNReal.ofReal ε)
    {t : ℝ} (ht : 0 < t) : totalVariationOn V (fun x ↦ χ (x, t)) ≤ sliceTV χ φ t := by
  unfold totalVariationOn weightedTV
  refine iSup₂_le fun ξ hξ ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨j, hj⟩ := hdense ξ hξ ε (by exact_mod_cast hε)
  have hiξ := integrable_slice_mul_divergence hVU hχm hχ hξ ht
  have hij := integrable_slice_mul_divergence hVU hχm hχ (hφ j) ht
  have hvan : ∀ {ζ : E d → E d}, tsupport ζ ⊆ V → ∀ x, x ∉ V → χ (x, t) * divergence ζ x = 0 :=
    fun hζ x hx ↦ by rw [divergence_eq_zero_of_notMem_tsupport (fun h ↦ hx (hζ h)), mul_zero]
  have hjV : ∫ x in V, χ (x, t) * divergence (φ j) x = sliceVal χ φ j t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hvan (hφ j).2.2.1)
  have hdiff : (∫ x in V, χ (x, t) * divergence ξ x) - ∫ x in V, χ (x, t) * divergence (φ j) x
      ≤ ε := by
    rw [← integral_sub hiξ.integrableOn hij.integrableOn]
    refine (Real.le_norm_self _).trans ((norm_integral_le_lintegral_norm _).trans ?_)
    have hle : ∫⁻ x in V, ENNReal.ofReal
        ‖χ (x, t) * divergence ξ x - χ (x, t) * divergence (φ j) x‖ ≤
        ∫⁻ x in V, edist (divergence (φ j) x) (divergence ξ x) := by
      refine setLIntegral_mono' hVm fun x hx ↦ ?_
      rw [← mul_sub, edist_comm, edist_dist, Real.dist_eq, norm_mul]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (norm_nonneg _)
        (hχ _ ⟨hVU hx, ht⟩))
    have := (hle.trans_lt hj).trans_le le_rfl
    exact (ENNReal.toReal_le_of_le_ofReal hε.le this.le)
  calc ENNReal.ofReal (∫ x in V, χ (x, t) * divergence ξ x)
      ≤ ENNReal.ofReal (sliceVal χ φ j t + ε) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (sliceVal χ φ j t) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ ≤ sliceTV χ φ t + ENNReal.ofReal ε := by
      gcongr
      exact (ENNReal.ofReal_le_ofReal (sliceVal_le_sliceMax χ φ le_rfl t)).trans
        (le_iSup (fun N ↦ ENNReal.ofReal (sliceMax χ φ N t)) j)
    _ = sliceTV χ φ t + ε := by rw [ENNReal.ofReal_coe_nnreal]

/-! ### First-maximizer partition -/

/-- **First-maximizer partition**: the time axis splits into measurable sets `A_j`, `j ≤ N`
(`A_j` = where `j` is the first index realizing `max_{l ≤ N} a_l`), so that
`max_{l ≤ N} a_l = ∑_{j ≤ N} 1_{A_j} a_j`. -/
theorem exists_firstMax_partition (a : ℕ → ℝ → ℝ) (ha : ∀ j, Measurable (a j)) (N : ℕ) :
    ∃ A : ℕ → Set ℝ, (∀ j, MeasurableSet (A j)) ∧
      (∀ t, ∑ j ∈ Finset.range (N + 1), (A j).indicator (fun _ ↦ (1 : ℝ)) t = 1) ∧
      ∀ t, ∑ j ∈ Finset.range (N + 1), (A j).indicator (a j) t =
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j ↦ a j t := by
  classical
  set m : ℝ → ℝ := fun t ↦ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    fun j ↦ a j t with hm_def
  have hm : Measurable m := by
    have h := Finset.measurable_range_sup' (n := N) (f := a) fun k _ ↦ ha k
    convert h using 1
    funext t
    simp [m, Finset.sup'_apply]
  set A : ℕ → Set ℝ := fun j ↦ {t | a j t = m t ∧ ∀ l < j, a l t ≠ m t}
  have hAm : ∀ j, MeasurableSet (A j) := by
    intro j
    have : A j = {t | a j t = m t} ∩ ⋂ l : Fin j, {t | a l t = m t}ᶜ := by
      ext t; simp [A, Fin.forall_iff]
    rw [this]
    exact (measurableSet_eq_fun (ha j) hm).inter
      (MeasurableSet.iInter fun l ↦ (measurableSet_eq_fun (ha l) hm).compl)
  have hex : ∀ t, ∃ j, j ≤ N ∧ a j t = m t := fun t ↦ by
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      fun j ↦ a j t
    exact ⟨j, Nat.lt_succ_iff.1 (Finset.mem_range.1 hj), hjeq.symm⟩
  have hiff : ∀ t, ∀ j ≤ N, t ∈ A j ↔ j = Nat.find (hex t) := by
    intro t j hj
    constructor
    · rintro ⟨hjm, hl⟩
      refine le_antisymm ?_ (Nat.find_min' _ ⟨hj, hjm⟩)
      by_contra hlt
      exact hl _ (not_le.1 hlt) (Nat.find_spec (hex t)).2
    · rintro rfl
      refine ⟨(Nat.find_spec (hex t)).2, fun l hl hlm ↦ Nat.find_min (hex t) hl
        ⟨(hl.trans_le (Nat.find_spec (hex t)).1).le, hlm⟩⟩
  have hmem : ∀ t, Nat.find (hex t) ∈ Finset.range (N + 1) := fun t ↦
    Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.find_spec (hex t)).1)
  have hsum : ∀ (t : ℝ) (f : ℕ → ℝ → ℝ), ∑ j ∈ Finset.range (N + 1), (A j).indicator (f j) t =
      f (Nat.find (hex t)) t := by
    intro t f
    rw [Finset.sum_eq_single_of_mem _ (hmem t) fun b hb hne ↦ ?_]
    · exact indicator_of_mem (((hiff t _ (Nat.find_spec (hex t)).1)).2 rfl) _
    · exact indicator_of_notMem (fun h ↦ hne ((hiff t b
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hb))).1 h)) _
  refine ⟨A, hAm, fun t ↦ hsum t fun _ _ ↦ 1, fun t ↦ ?_⟩
  rw [hsum t a]
  exact (Nat.find_spec (hex t)).2

/-! ### Mollified indicators in time -/

/-- The 1D bump of radii `1/(8(n+1)) < 1/(4(n+1))`. -/
noncomputable def timeBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / (8 * ((n : ℝ) + 1))
  rOut := 1 / (4 * ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply one_div_lt_one_div_of_lt (by positivity)
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    linarith

theorem timeBump_rOut_le (n : ℕ) : (timeBump n).rOut ≤ 1 / 4 := by
  change 1 / (4 * ((n : ℝ) + 1)) ≤ 1 / 4
  apply one_div_le_one_div_of_le (by norm_num)
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  linarith

/-- The mollified indicator `ρₙ ⋆ 1_B`. -/
noncomputable def smoothInd (n : ℕ) (B : Set ℝ) : ℝ → ℝ :=
  (timeBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    B.indicator fun _ ↦ (1 : ℝ)

theorem smoothInd_apply (n : ℕ) (B : Set ℝ) (t : ℝ) :
    smoothInd n B t = ∫ s, (timeBump n).normed volume s * B.indicator (fun _ ↦ (1 : ℝ)) (t - s) :=
  by simp [smoothInd, convolution_def]

theorem contDiff_smoothInd (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    ContDiff ℝ 1 (smoothInd n B) :=
  (timeBump n).hasCompactSupport_normed.contDiff_convolution_left _
    (timeBump n).contDiff_normed ((locallyIntegrable_const 1).indicator hB)

theorem integrable_bump_mul_indicator (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) (t : ℝ) :
    Integrable fun s ↦ (timeBump n).normed volume s * B.indicator (fun _ ↦ (1 : ℝ)) (t - s) := by
  refine ((timeBump n).integrable_normed (μ := volume)).norm.mono'
    (((timeBump n).continuous_normed.measurable).mul
      ((measurable_const.indicator hB).comp
        (measurable_const.sub measurable_id))).aestronglyMeasurable
    (Eventually.of_forall fun s ↦ ?_)
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  by_cases h : t - s ∈ B <;> simp [h]

theorem smoothInd_nonneg (n : ℕ) (B : Set ℝ) (t : ℝ) : 0 ≤ smoothInd n B t := by
  rw [smoothInd_apply]
  exact integral_nonneg fun s ↦ mul_nonneg ((timeBump n).nonneg_normed s)
    (indicator_nonneg (fun _ _ ↦ zero_le_one) _)

theorem sum_smoothInd_le_one (n : ℕ) {B : ℕ → Set ℝ} (hB : ∀ j, MeasurableSet (B j))
    (s : Finset ℕ) (hs : ∀ t, ∑ j ∈ s, (B j).indicator (fun _ ↦ (1 : ℝ)) t ≤ 1) (t : ℝ) :
    ∑ j ∈ s, smoothInd n (B j) t ≤ 1 := by
  simp_rw [smoothInd_apply]
  rw [← integral_finsetSum _ fun j _ ↦ integrable_bump_mul_indicator n (hB j) t]
  calc ∫ r, ∑ j ∈ s, (timeBump n).normed volume r * (B j).indicator (fun _ ↦ (1 : ℝ)) (t - r)
      ≤ ∫ r, (timeBump n).normed volume r := by
        refine integral_mono (integrable_finsetSum _ fun j _ ↦
          integrable_bump_mul_indicator n (hB j) t) (timeBump n).integrable_normed fun r ↦ ?_
        rw [← Finset.mul_sum]
        exact mul_le_of_le_one_right ((timeBump n).nonneg_normed r) (hs _)
    _ = 1 := (timeBump n).integral_normed

theorem smoothInd_eq_zero {n : ℕ} {B : Set ℝ} {a b : ℝ} (hB : B ⊆ Ioo a b) {t : ℝ}
    (ht : t ∉ Icc (a - 1 / 4) (b + 1 / 4)) : smoothInd n B t = 0 := by
  rw [smoothInd_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun s ↦ ?_)
  by_cases hs : (timeBump n).normed volume s = 0
  · simp [hs]
  have hs' : s ∈ ball (0 : ℝ) (timeBump n).rOut := by
    rw [← (timeBump n).support_normed_eq (μ := volume)]; exact hs
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at hs'
  have hs'' := (timeBump_rOut_le n)
  have hnot : t - s ∉ B := fun h ↦ by
    obtain ⟨h1, h2⟩ := hB h
    refine ht ⟨?_, ?_⟩ <;> [skip; skip] <;> cases abs_lt.1 hs' <;> linarith
  simp [hnot]

theorem ae_tendsto_smoothInd {B : Set ℝ} (hB : MeasurableSet B) :
    ∀ᵐ t, Tendsto (fun n ↦ smoothInd n B t) atTop (𝓝 (B.indicator (fun _ ↦ (1 : ℝ)) t)) := by
  refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2) ?_
    (Eventually.of_forall fun n ↦ ?_) ((locallyIntegrable_const 1).indicator hB)
  · change Tendsto (fun n : ℕ ↦ 1 / (4 * ((n : ℝ) + 1))) atTop (𝓝 0)
    simpa [one_div, mul_inv, mul_comm] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 : ℝ)⁻¹)
  · change 1 / (4 * ((n : ℝ) + 1)) ≤ 2 * (1 / (8 * ((n : ℝ) + 1)))
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-! ### The space-time test fields `Ψ(x, t) = ∑_j (ρₙ ⋆ 1_{B_j})(t) φ_j(x)` -/

theorem divergence_sum_smul {s : Finset ℕ} (c : ℕ → ℝ) {φ : ℕ → E d → E d} {x : E d}
    (h : ∀ j ∈ s, DifferentiableAt ℝ (φ j) x) :
    divergence (fun y ↦ ∑ j ∈ s, c j • φ j y) x = ∑ j ∈ s, c j * divergence (φ j) x := by
  unfold divergence
  rw [fderiv_fun_sum (A := fun j y ↦ c j • φ j y) fun j hj ↦ (h j hj).const_smul (c j)]
  simp only [ContinuousLinearMap.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [fderiv_fun_const_smul (h j hj)]
  simp

/-- The space-time test field `Ψₙ(x, t) = ∑_{j ≤ N} (ρₙ ⋆ 1_{B_j})(t) φ_j(x)`. -/
noncomputable def mixField (φ : ℕ → E d → E d) (B : ℕ → Set ℝ) (N n : ℕ) (p : E d × ℝ) : E d :=
  ∑ j ∈ Finset.range (N + 1), smoothInd n (B j) p.2 • φ j p.1

variable {φ : ℕ → E d → E d} {B : ℕ → Set ℝ} {a b : ℝ}

theorem divₓ_mixField (hφ : ∀ j, ContDiff ℝ 1 (φ j)) (N n : ℕ) (p : E d × ℝ) :
    divₓ (mixField φ B N n) p =
      ∑ j ∈ Finset.range (N + 1), smoothInd n (B j) p.2 * divergence (φ j) p.1 :=
  divergence_sum_smul (fun j ↦ smoothInd n (B j) p.2)
    fun j _ ↦ (hφ j).differentiable one_ne_zero p.1

theorem mixField_eq_zero (hB : ∀ j, B j ⊆ Ioo a b) (N n : ℕ) {p : E d × ℝ}
    (hp : (∀ j ∈ Finset.range (N + 1), p.1 ∉ tsupport (φ j)) ∨
      p.2 ∉ Icc (a - 1 / 4) (b + 1 / 4)) : mixField φ B N n p = 0 := by
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rcases hp with hp | hp
  · rw [image_eq_zero_of_notMem_tsupport (hp j hj), smul_zero]
  · rw [smoothInd_eq_zero (hB j) hp, zero_smul]

theorem isTVTestFieldₓ_mixField (hVU : V ⊆ U) (hφ : ∀ j, IsTVTestField V 1 (φ j))
    (hBm : ∀ j, MeasurableSet (B j)) (hB : ∀ j, B j ⊆ Ioo a b) (N : ℕ)
    (hsum : ∀ t, ∑ j ∈ Finset.range (N + 1), (B j).indicator (fun _ ↦ (1 : ℝ)) t ≤ 1)
    (ha : 1 / 4 < a) {η : E d × ℝ → ℝ} (hη0 : ∀ p, 0 ≤ η p)
    (hη : ∀ x ∈ V, ∀ t ∈ Icc (a - 1 / 4) (b + 1 / 4), 1 ≤ η (x, t)) (n : ℕ) :
    IsTVTestFieldₓ (UInf U) η (mixField φ B N n) := by
  set K : Set (E d × ℝ) :=
    (⋃ j ∈ Finset.range (N + 1), tsupport (φ j)) ×ˢ Icc (a - 1 / 4) (b + 1 / 4)
  have hK : IsCompact K :=
    ((Finset.range (N + 1)).isCompact_biUnion fun j _ ↦ (hφ j).2.1).prod isCompact_Icc
  have hzero : ∀ p ∉ K, mixField φ B N n p = 0 := by
    intro p hp
    refine mixField_eq_zero hB N n ?_
    by_cases h2 : p.2 ∈ Icc (a - 1 / 4) (b + 1 / 4)
    · left
      intro j hj h1
      exact hp ⟨mem_biUnion hj h1, h2⟩
    · exact Or.inr h2
  have htsupp : tsupport (mixField φ B N n) ⊆ K :=
    closure_minimal (fun p hp ↦ by_contra fun h ↦ hp (hzero p h)) hK.isClosed
  refine ⟨ContDiff.sum fun j _ ↦ ((contDiff_smoothInd n (hBm j)).comp contDiff_snd).smul
    ((hφ j).1.comp contDiff_fst), HasCompactSupport.intro hK hzero, htsupp.trans ?_, fun p ↦ ?_⟩
  · rintro ⟨x, t⟩ ⟨hx, ht⟩
    obtain ⟨j, -, hxj⟩ := mem_iUnion₂.1 hx
    exact ⟨hVU ((hφ j).2.2.1 hxj), lt_of_lt_of_le (by linarith) ht.1⟩
  by_cases hp : p.1 ∈ V ∧ p.2 ∈ Icc (a - 1 / 4) (b + 1 / 4)
  · refine le_trans ?_ (hη p.1 hp.1 p.2 hp.2)
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun j _ ↦ ?_)
      (sum_smoothInd_le_one n hBm _ hsum p.2)
    rw [norm_smul, Real.norm_of_nonneg (smoothInd_nonneg n _ _)]
    exact mul_le_of_le_one_right (smoothInd_nonneg n _ _) (by simpa using (hφ j).2.2.2 p.1)
  · rw [mixField_eq_zero hB N n, norm_zero]
    · exact hη0 p
    · by_cases h1 : p.1 ∈ V
      · exact Or.inr fun h2 ↦ hp ⟨h1, h2⟩
      · exact Or.inl fun j _ h ↦ h1 ((hφ j).2.2.1 h)

theorem hasCompactSupport_smoothInd {n : ℕ} {B : Set ℝ} (hB : B ⊆ Ioo a b) :
    HasCompactSupport (smoothInd n B) :=
  HasCompactSupport.intro isCompact_Icc fun _ ht ↦ smoothInd_eq_zero hB ht

/-- **Slicing the test integral**: `∫_{U_∞} χ divₓ Ψₙ = ∑_j ∫ (ρₙ ⋆ 1_{B_j})(t) a_j(t) dt`. -/
theorem setIntegral_mul_divₓ_mixField (hVU : V ⊆ U) (hχm : Measurable χ)
    (hχ : ∀ p ∈ UInf U, |χ p| ≤ 1) (hφ : ∀ j, IsTVTestField V 1 (φ j))
    (hBm : ∀ j, MeasurableSet (B j)) (hB : ∀ j, B j ⊆ Ioo a b) (ha : 1 / 4 < a) (N n : ℕ) :
    ∫ p in UInf U, χ p * divₓ (mixField φ B N n) p =
      ∑ j ∈ Finset.range (N + 1), ∫ t, smoothInd n (B j) t * sliceVal χ φ j t := by
  have hpt : ∀ p, χ p * divₓ (mixField φ B N n) p = ∑ j ∈ Finset.range (N + 1),
      smoothInd n (B j) p.2 * (χ p * divergence (φ j) p.1) := fun p ↦ by
    rw [divₓ_mixField (fun j ↦ (hφ j).1), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  -- each term vanishes off `U_∞`
  have hvan : ∀ j, ∀ p ∉ UInf U, smoothInd n (B j) p.2 * (χ p * divergence (φ j) p.1) = 0 := by
    intro j p hp
    by_cases h1 : p.1 ∈ U
    · have h2 : p.2 ∉ Icc (a - 1 / 4) (b + 1 / 4) := fun h ↦
        hp ⟨h1, lt_of_lt_of_le (by linarith) h.1⟩
      rw [smoothInd_eq_zero (hB j) h2, zero_mul]
    · rw [divergence_eq_zero_of_notMem_tsupport fun h ↦ h1 (hVU ((hφ j).2.2.1 h)), mul_zero,
        mul_zero]
  have hint : ∀ j, Integrable (fun p : E d × ℝ ↦
      smoothInd n (B j) p.2 * (χ p * divergence (φ j) p.1)) (volume.prod volume) := by
    intro j
    have hG : Integrable (smoothInd n (B j)) :=
      (contDiff_smoothInd n (hBm j)).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_smoothInd (hB j))
    refine ((integrable_divergence_of_isTVTestField (hφ j) volume).norm.mul_prod
      hG.norm).mono' ?_ (Eventually.of_forall fun p ↦ ?_)
    · exact (((contDiff_smoothInd n (hBm j)).continuous.measurable.comp measurable_snd).mul
        (hχm.mul ((GMTFoundations.continuous_divergence (hφ j).1).measurable.comp
          measurable_fst))).aestronglyMeasurable
    · by_cases hp : p ∈ UInf U
      · rw [norm_mul, norm_mul, mul_comm]
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) (hχ p hp)
      · rw [hvan j p hp, norm_zero]
        positivity
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ by
      rw [hpt p]; exact Finset.sum_eq_zero fun j _ ↦ hvan j p hp]
  simp_rw [hpt]
  rw [Measure.volume_eq_prod, integral_finsetSum _ fun j _ ↦ hint j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_prod_symm _ (hint j)]
  simp_rw [integral_const_mul]
  rfl

/-! ### The slicing inequality -/

theorem sliceVal_zero (χ : E d × ℝ → ℝ) (hφ0 : φ 0 = fun _ ↦ 0) (t : ℝ) :
    sliceVal χ φ 0 t = 0 := by
  simp [sliceVal, hφ0, divergence]

/-- **Slicing of the partial variation** (Theorem 3.10, Step 3): if `η ≥ 1` on
`V × [a - 1/4, b + 1/4]`, then `∫_{(a, b)} F ≤ ∫_{U_∞} η |∇ₓχ|`, where `F = sliceTV χ φ`
dominates the total variations `∫_V |∇χ(·, t)|` (`totalVariationOn_le_sliceTV`). -/
theorem setLIntegral_sliceTV_le (hVU : V ⊆ U) (hχm : Measurable χ)
    (hχ : ∀ p ∈ UInf U, |χ p| ≤ 1) (hφ : ∀ j, IsTVTestField V 1 (φ j))
    (hφ0 : φ 0 = fun _ ↦ 0) (ha : 1 / 4 < a) {η : E d × ℝ → ℝ} (hη0 : ∀ p, 0 ≤ η p)
    (hη : ∀ x ∈ V, ∀ t ∈ Icc (a - 1 / 4) (b + 1 / 4), 1 ≤ η (x, t)) :
    ∫⁻ t in Ioo a b, sliceTV χ φ t ≤ weightedTVₓ (UInf U) η χ := by
  unfold sliceTV
  rw [lintegral_iSup (f := fun N t ↦ ENNReal.ofReal (sliceMax χ φ N t))
    (fun N ↦ ENNReal.measurable_ofReal.comp
    (measurable_sliceMax hχm (fun j ↦ (hφ j).1) N))
    fun N N' h t ↦ ENNReal.ofReal_le_ofReal (sliceMax_mono χ φ t h)]
  refine iSup_le fun N ↦ ?_
  set W := weightedTVₓ (UInf U) η χ
  rcases eq_or_ne W ⊤ with hW | hW
  · rw [hW]; exact le_top
  have hvm := measurable_sliceVal hχm (fun j ↦ (hφ j).1)
  obtain ⟨A, hAm, hA1, hAsum⟩ := exists_firstMax_partition (sliceVal χ φ) hvm N
  set I := Ioo a b
  set B : ℕ → Set ℝ := fun j ↦ A j ∩ I
  have hBm : ∀ j, MeasurableSet (B j) := fun j ↦ (hAm j).inter measurableSet_Ioo
  have hBI : ∀ j, B j ⊆ I := fun j ↦ inter_subset_right
  have hBind : ∀ (f : ℝ → ℝ) j t, (B j).indicator f t = if t ∈ I then (A j).indicator f t else 0 :=
    fun f j t ↦ by by_cases ht : t ∈ I <;> by_cases ht' : t ∈ A j <;> simp [B, ht, ht']
  have hsum : ∀ t, ∑ j ∈ Finset.range (N + 1), (B j).indicator (fun _ ↦ (1 : ℝ)) t ≤ 1 := by
    intro t
    simp_rw [hBind]
    split_ifs
    · rw [hA1 t]
    · simp
  set M : ℕ → ℝ := fun j ↦ ∫ x, |divergence (φ j) x|
  set J := Icc (a - 1 / 4) (b + 1 / 4)
  have habs : ∀ j, ∀ t ∈ J, |sliceVal χ φ j t| ≤ M j := fun j t ht ↦
    abs_sliceVal_le hVU hχ hφ j (lt_of_lt_of_le (by linarith) ht.1)
  have hbdd_int : ∀ j, Integrable (J.indicator fun _ ↦ M j) :=
    fun j ↦ (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hG1 : ∀ n j, j ∈ Finset.range (N + 1) → ∀ t, smoothInd n (B j) t ≤ 1 := fun n j hj t ↦
    (Finset.single_le_sum (fun i _ ↦ smoothInd_nonneg n (B i) t) hj).trans
      (sum_smoothInd_le_one n hBm _ hsum t)
  -- the limit of the tested integrals
  have hlim : Tendsto (fun n ↦ ∑ j ∈ Finset.range (N + 1),
      ∫ t, smoothInd n (B j) t * sliceVal χ φ j t) atTop
      (𝓝 (∑ j ∈ Finset.range (N + 1),
        ∫ t, (B j).indicator (fun _ ↦ (1 : ℝ)) t * sliceVal χ φ j t)) := by
    refine tendsto_finsetSum _ fun j hj ↦ ?_
    refine tendsto_integral_of_dominated_convergence (J.indicator fun _ ↦ M j)
      (fun n ↦ ((contDiff_smoothInd n (hBm j)).continuous.measurable.mul
        (hvm j)).aestronglyMeasurable) (hbdd_int j) (fun n ↦ Eventually.of_forall fun t ↦ ?_)
      ?_
    · by_cases ht : t ∈ J
      · rw [indicator_of_mem ht, norm_mul, Real.norm_of_nonneg (smoothInd_nonneg n _ _),
          Real.norm_eq_abs]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hG1 n j hj t)).trans (habs j t ht)
      · rw [smoothInd_eq_zero (hBI j) ht]
        simp only [zero_mul, norm_zero]
        exact indicator_nonneg (fun t ht ↦ (abs_nonneg _).trans (habs j t ht)) _
    · filter_upwards [ae_tendsto_smoothInd (hBm j)] with t ht using ht.mul_const _
  -- each tested integral is bounded by `W`
  have hle : ∀ n, ∑ j ∈ Finset.range (N + 1), ∫ t, smoothInd n (B j) t * sliceVal χ φ j t ≤
      W.toReal := by
    intro n
    rw [← setIntegral_mul_divₓ_mixField hVU hχm hχ hφ hBm hBI ha N n]
    refine (ENNReal.ofReal_le_iff_le_toReal hW).1 ?_
    exact le_iSup₂ (f := fun ψ (_ : IsTVTestFieldₓ (UInf U) η ψ) ↦
      ENNReal.ofReal (∫ p in UInf U, χ p * divₓ ψ p)) (mixField φ B N n)
      (isTVTestFieldₓ_mixField hVU hφ hBm hBI N hsum ha hη0 hη n)
  have hlimle := le_of_tendsto' hlim hle
  -- identification of the limit
  have hint : ∀ j, Integrable fun t ↦ (B j).indicator (fun _ ↦ (1 : ℝ)) t * sliceVal χ φ j t := by
    intro j
    refine (hbdd_int j).mono' (((measurable_const.indicator (hBm j)).mul
      (hvm j)).aestronglyMeasurable) (Eventually.of_forall fun t ↦ ?_)
    by_cases ht : t ∈ B j
    · have htJ : t ∈ J := ⟨by linarith [(hBI j ht).1], by linarith [(hBI j ht).2]⟩
      rw [indicator_of_mem ht, indicator_of_mem htJ, one_mul, Real.norm_eq_abs]
      exact habs j t htJ
    · rw [indicator_of_notMem ht, zero_mul, norm_zero]
      exact indicator_nonneg (fun t ht ↦ (abs_nonneg _).trans (habs j t ht)) _
  have hpt : ∀ t, ∑ j ∈ Finset.range (N + 1),
      (B j).indicator (fun _ ↦ (1 : ℝ)) t * sliceVal χ φ j t = I.indicator (sliceMax χ φ N) t := by
    intro t
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht, sliceMax, ← hAsum t]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hBind, if_pos ht]
      by_cases ht' : t ∈ A j <;> simp [ht']
    · rw [indicator_of_notMem ht]
      exact Finset.sum_eq_zero fun j _ ↦ by rw [hBind, if_neg ht, zero_mul]
  rw [← integral_finsetSum _ fun j _ ↦ hint j] at hlimle
  simp_rw [hpt] at hlimle
  have hIint : Integrable (I.indicator (sliceMax χ φ N)) := by
    rw [← funext hpt]; exact integrable_finsetSum _ fun j _ ↦ hint j
  rw [integral_indicator measurableSet_Ioo] at hlimle
  have hnn : ∀ t, 0 ≤ sliceMax χ φ N t := fun t ↦
    (sliceVal_zero χ hφ0 t).symm.le.trans (sliceVal_le_sliceMax χ φ (Nat.zero_le N) t)
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_indicator_iff measurableSet_Ioo).1 hIint)
    (Eventually.of_forall hnn)]
  exact (ENNReal.ofReal_le_ofReal hlimle).trans (ENNReal.ofReal_toReal_le)

/-! ### Product weights `η(x, t) = θ(x) ψ(t - c)` and their parameters in (3.13) -/

/-- The time cutoff `ψ_c`: a bump centered at `c`, `= 1` on `[c - 1, c + 1]`, supported in
`[c - 2, c + 2]`. -/
noncomputable def timeCut (c : ℝ) : ContDiffBump c := ⟨1, 2, one_pos, one_lt_two⟩

theorem timeCut_apply (c t : ℝ) : timeCut c t = timeCut 0 (t - c) := by
  simp [ContDiffBump.toFun, timeCut]

/-- The product weight `η(x, t) = θ(x) ψ_c(t)`. -/
noncomputable def prodWeight (θ : E d → ℝ) (c : ℝ) (p : E d × ℝ) : ℝ := θ p.1 * timeCut c p.2

theorem tsupport_prodWeight (θ : E d → ℝ) (c : ℝ) :
    tsupport (prodWeight θ c) = tsupport θ ×ˢ closedBall c 2 := by
  have : support (prodWeight θ c) = support θ ×ˢ support (timeCut c) := by
    ext p; simp [prodWeight]
  rw [tsupport, this, closure_prod_eq, ← tsupport, ← tsupport, ContDiffBump.tsupport_eq]
  rfl

open Classical in
theorem weightTimeLength_prodWeight (θ : E d → ℝ) (c : ℝ) :
    weightTimeLength (prodWeight θ c) = if (tsupport θ).Nonempty then 4 else 0 := by
  rw [weightTimeLength, tsupport_prodWeight]
  split_ifs with h
  · rw [snd_image_prod h, Real.closedBall_eq_Icc, csSup_Icc (by linarith),
      csInf_Icc (by linarith)]
    ring
  · rw [not_nonempty_iff_eq_empty.1 h, empty_prod, image_empty, Real.sSup_empty,
      Real.sInf_empty, sub_zero]

/-- For `x ∈ U` and `t ≥ diam U`, the distance of `(x, t)` to the parabolic boundary of `U_∞` is
the lateral distance `dist(x, ∂U)`. -/
theorem infDist_parBdryInf {U : Set (E d)} (hUb : Bornology.IsBounded U) (hUc : Uᶜ.Nonempty)
    {x : E d} (hx : x ∈ U) {t : ℝ} (ht : Metric.diam U ≤ t) :
    infDist (x, t) (parBdryInf U) = infDist x (frontier U) := by
  have hF : (frontier U).Nonempty :=
    nonempty_frontier_iff.2 ⟨⟨x, hx⟩, fun h ↦ by simp [h] at hUc⟩
  have ht0 : 0 ≤ t := Metric.diam_nonneg.trans ht
  have hle : infDist x (frontier U) ≤ t := by
    obtain ⟨y, hy⟩ := hF
    refine (infDist_le_dist_of_mem hy).trans (le_trans ?_ ht)
    rw [← Metric.diam_closure]
    exact Metric.dist_le_diam_of_mem hUb.closure (subset_closure hx) (frontier_subset_closure hy)
  have hP : (parBdryInf U).Nonempty := ⟨(x, 0), Or.inl ⟨subset_closure hx, rfl⟩⟩
  refine le_antisymm ((Metric.le_infDist hF).2 fun y hy ↦ ?_)
    ((Metric.le_infDist hP).2 fun q hq ↦ ?_)
  · have hyt : (y, t) ∈ parBdryInf U := Or.inr ⟨hy, mem_Ici.2 ht0⟩
    refine (infDist_le_dist_of_mem hyt).trans ?_
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
  · rcases hq with ⟨-, hq2⟩ | ⟨hq1, -⟩
    · refine hle.trans ((le_of_eq ?_).trans (le_max_right _ _))
      rw [mem_singleton_iff.1 hq2, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    · exact (infDist_le_dist_of_mem hq1).trans (le_max_left _ _)

theorem weightDist_prodWeight {U : Set (E d)} (hUb : Bornology.IsBounded U) (hUc : Uᶜ.Nonempty)
    {θ : E d → ℝ} (hθU : tsupport θ ⊆ U) {c : ℝ} (hc : Metric.diam U + 2 ≤ c) :
    weightDist U (prodWeight θ c) = sInf ((fun x ↦ infDist x (frontier U)) '' tsupport θ) := by
  rw [weightDist, tsupport_prodWeight]
  congr 1
  ext r
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    refine ⟨x, hx, (infDist_parBdryInf hUb hUc (hθU hx) ?_).symm⟩
    rw [Real.closedBall_eq_Icc] at ht
    linarith [ht.1]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x, c), ⟨hx, mem_closedBall_self zero_le_two⟩,
      infDist_parBdryInf hUb hUc (hθU hx) (by linarith)⟩

theorem norm_gradient_mul_const {θ : E d → ℝ} {x : E d} (hθ : DifferentiableAt ℝ θ x) (k : ℝ) :
    ‖∇ (fun y ↦ θ y * k) x‖ = |k| * ‖∇ θ x‖ := by
  simp only [gradient, LinearIsometryEquiv.norm_map, fderiv_mul_const hθ, norm_smul,
    Real.norm_eq_abs]

theorem l2H1Norm_prodWeight {U : Set (E d)} {θ : E d → ℝ} (hθ : Differentiable ℝ θ) {c : ℝ}
    (hc : 2 ≤ c) :
    l2H1Norm U (prodWeight θ c) =
      Real.sqrt ((∫ x in U, θ x ^ 2 + ‖∇ θ x‖ ^ 2) * ∫ t, timeCut 0 t ^ 2) := by
  have hpt : ∀ p : E d × ℝ, prodWeight θ c p ^ 2 + ‖gradₓ (prodWeight θ c) p‖ ^ 2 =
      (θ p.1 ^ 2 + ‖∇ θ p.1‖ ^ 2) * timeCut c p.2 ^ 2 := by
    intro p
    rw [gradₓ]
    simp only [prodWeight]
    rw [norm_gradient_mul_const (hθ p.1)]
    simp only [mul_pow, sq_abs]
    ring
  have htime : ∫ t in Ioi 0, timeCut c t ^ 2 = ∫ t, timeCut 0 t ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ ?_]
    · simp_rw [timeCut_apply c]
      exact integral_sub_right_eq_self (fun t ↦ timeCut 0 t ^ 2) c
    · have : t ∉ support (timeCut c) := by
        rw [ContDiffBump.support_eq, mem_ball, Real.dist_eq]
        rw [mem_Ioi, not_lt] at ht
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        change ¬ c - t < 2
        linarith
      rw [notMem_support.1 this]; ring
  rw [l2H1Norm, UInf]
  simp_rw [hpt]
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun x ↦ θ x ^ 2 + ‖∇ θ x‖ ^ 2)
    (fun t ↦ timeCut c t ^ 2), htime]

theorem isPerimeterWeight_prodWeight {U : Set (E d)} {θ : E d → ℝ} (hθ : ContDiff ℝ 1 θ)
    (hθc : HasCompactSupport θ) (hθU : tsupport θ ⊆ U) (hθ0 : ∀ x, 0 ≤ θ x) {c : ℝ}
    (hc : 2 < c) : IsPerimeterWeight U (prodWeight θ c) := by
  refine ⟨(hθ.comp contDiff_fst).mul ((timeCut c).contDiff.comp contDiff_snd), ?_, ?_,
    fun p ↦ mul_nonneg (hθ0 _) (timeCut c).nonneg⟩
  · rw [HasCompactSupport, tsupport_prodWeight]
    exact hθc.prod (isCompact_closedBall _ _)
  · rw [tsupport_prodWeight]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    rw [Real.closedBall_eq_Icc] at ht
    exact ⟨hθU hx, show (0 : ℝ) < t by linarith [ht.1]⟩

end LongTime

end PerronVariational

end
