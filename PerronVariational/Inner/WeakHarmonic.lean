/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import PerronVariational.Inner.InnerVarLinear
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.MeasureTheory.Function.L2Space
import PerronVariational.Inner.SliceHeat

/-!
# Integration by parts for locally Lipschitz functions, and limits of the weak heat equation

Tools for **Theorem 3.10**, Step 2, of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981:
the long-time limit `u_∞` is weakly harmonic in `{u_∞ > 0}`.

* `∫_U ∇f · ∇φ = -∫_U f Δφ` for `f` locally Lipschitz on the open set `U` and `φ ∈ C²_c(U)`,
  from the integration by parts `GMTFoundations.integral_fderiv_mul_eq_neg`
  (gmt-foundations v0.1.0, `GMTFoundations/Sobolev/Lipschitz.lean`).
* `∫_U fₙ ψ → ∫_U f ψ` when `fₙ → f` uniformly on the compact support of `ψ`.
* `∫_U wₙ φ → 0` when `∫_U wₙ² → 0` (Cauchy–Schwarz).

## Main definitions

* `PerronVariational.LongTime.coordLap`: `Δφ = ∑ᵢ ∂ᵢ∂ᵢφ` written with `fderiv`.

## Main results

* `PerronVariational.LongTime.integral_inner_gradient_eq_neg`
* `PerronVariational.LongTime.tendsto_setIntegral_mul_of_tendstoUniformlyOn`
* `PerronVariational.LongTime.tendsto_setIntegral_mul_of_lintegral_sq`
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient ContDiff NNReal ENNReal

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-! ### Integration by parts -/

/-- `Δφ = ∑ᵢ ∂ᵢ∂ᵢφ`, written with `fderiv` and the coordinate vectors. -/
noncomputable def coordLap (φ : E d → ℝ) (x : E d) : ℝ :=
  ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ φ y (coordVec i)) x (coordVec i)

theorem tsupport_fderiv_apply_subset (φ : E d → ℝ) (v : E d) :
    tsupport (fun y ↦ fderiv ℝ φ y v) ⊆ tsupport φ :=
  closure_minimal (fun y hy ↦ by
    by_contra h'
    exact hy (by simp [fderiv_of_notMem_tsupport ℝ h'])) (isClosed_tsupport _)

theorem tsupport_coordLap_subset (φ : E d → ℝ) : tsupport (coordLap φ) ⊆ tsupport φ :=
  closure_minimal (fun y hy ↦ by
    by_contra h'
    refine hy (Finset.sum_eq_zero fun i _ ↦ ?_)
    simp [fderiv_of_notMem_tsupport ℝ fun h ↦ h' (tsupport_fderiv_apply_subset φ _ h)])
    (isClosed_tsupport _)

theorem continuous_coordLap {φ : E d → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (coordLap φ) := by
  refine continuous_finsetSum _ fun i _ ↦ ?_
  have hφi : ContDiff ℝ 1 (fun y ↦ fderiv ℝ φ y (coordVec i)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact (hφi.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem hasCompactSupport_coordLap {φ : E d → ℝ} (hφc : HasCompactSupport φ) :
    HasCompactSupport (coordLap φ) :=
  hφc.isCompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordLap_subset φ)

theorem inner_eq_sum_fderiv_coord {f φ : E d → ℝ} (x : E d) :
    inner ℝ (∇ f x) (∇ φ x) = ∑ i, fderiv ℝ f x (coordVec i) * fderiv ℝ φ x (coordVec i) := by
  have hf : ∀ i, fderiv ℝ f x (coordVec i) = (∇ f x) i := fun i ↦ by
    rw [← inner_gradient_eq_fderiv, real_inner_comm, coordVec, EuclideanSpace.inner_single_right]
    simp
  have hφ : ∀ i, fderiv ℝ φ x (coordVec i) = (∇ φ x) i := fun i ↦ by
    rw [← inner_gradient_eq_fderiv, real_inner_comm, coordVec, EuclideanSpace.inner_single_right]
    simp
  simp only [hf, hφ, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- **Integration by parts**, `∫_U ∇f · ∇φ = -∫_U f Δφ` for `f` locally Lipschitz on the open
set `U` and `φ ∈ C²_c(U)`. -/
theorem integral_inner_gradient_eq_neg {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : LocallyLipschitzOn U f) {φ : E d → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    ∫ x in U, inner ℝ (∇ f x) (∇ φ x) = -∫ x in U, f x * coordLap φ x := by
  have hK := hφc.isCompact
  obtain ⟨B, hB⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hf hK hφU
  -- the partial derivatives `∂ᵢφ`
  have hφi : ∀ i : Fin d, ContDiff ℝ 1 (fun y ↦ fderiv ℝ φ y (coordVec i)) := fun i ↦
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hφic : ∀ i : Fin d, HasCompactSupport (fun y ↦ fderiv ℝ φ y (coordVec i)) := fun i ↦
    (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E d →L[ℝ] ℝ ↦ L (coordVec i)) (by simp)
  have hφiU : ∀ i : Fin d, tsupport (fun y ↦ fderiv ℝ φ y (coordVec i)) ⊆ tsupport φ :=
    fun i ↦ closure_minimal (fun y hy ↦ by
      by_contra h'
      exact hy (by simp [fderiv_of_notMem_tsupport ℝ h'])) (isClosed_tsupport _)
  have hint : ∀ i : Fin d, IntegrableOn
      (fun x ↦ fderiv ℝ f x (coordVec i) * fderiv ℝ φ x (coordVec i)) U := by
    intro i
    obtain ⟨C, hC⟩ := (hφic i).exists_bound_of_continuous (hφi i).continuous
    refine IntegrableOn.of_forall_diff_eq_zero (s := tsupport φ) ?_ hU.measurableSet
      fun x hx ↦ ?_
    · refine IntegrableOn.of_bound hK.measure_lt_top
        ((measurable_fderiv_apply_const ℝ f _).mul
          (hφi i).continuous.measurable).aestronglyMeasurable (B * ‖coordVec i‖ * C)
        ((ae_restrict_mem hK.measurableSet).mono fun x hx ↦ ?_)
      rw [norm_mul]
      exact mul_le_mul ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg _))) (hC x) (norm_nonneg _)
        (mul_nonneg ((norm_nonneg _).trans (hB x hx)) (norm_nonneg _))
    · simp [fderiv_of_notMem_tsupport ℝ hx.2]
  simp_rw [inner_eq_sum_fderiv_coord]
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  simp_rw [coordLap, Finset.mul_sum]
  rw [integral_finsetSum, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact GMTFoundations.integral_fderiv_mul_eq_neg hU hf (hφi i) (hφic i) ((hφiU i).trans hφU) _
  · intro i _
    have hc : Continuous fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ φ y (coordVec i)) x (coordVec i) :=
      ((hφi i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs : tsupport (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ φ y (coordVec i)) x (coordVec i))
        ⊆ tsupport φ := closure_minimal (fun y hy ↦ by
          by_contra h'
          exact hy (by simp [fderiv_of_notMem_tsupport ℝ fun h ↦ h' (hφiU i h)]))
          (isClosed_tsupport _)
    refine IntegrableOn.of_forall_diff_eq_zero (s := tsupport φ) ?_ hU.measurableSet
      fun x hx ↦ ?_
    · exact ((hf.continuousOn.mono hφU).mul hc.continuousOn).integrableOn_compact hK
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx.2 (hcs h)]

/-! ### Limits of integrals -/

/-- Reindexing uniform convergence along a sequence `sₙ → ∞`. -/
theorem TendstoUniformlyOn.comp_seq {α β ι : Type*} [UniformSpace β] {F : ι → α → β}
    {f : α → β} {l : Filter ι} {K : Set α} (h : TendstoUniformlyOn F f l K) {s : ℕ → ι}
    (hs : Tendsto s atTop l) : TendstoUniformlyOn (fun n ↦ F (s n)) f atTop K :=
  fun u hu ↦ hs.eventually (h u hu)

/-- Uniform convergence to a function that is positive on a compact set `K` makes the
approximants eventually positive on `K`. -/
theorem eventually_forall_pos_of_tendstoUniformlyOn {K : Set (E d)} (hK : IsCompact K)
    {F : ℕ → E d → ℝ} {f : E d → ℝ} (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x)
    (hconv : TendstoUniformlyOn F f atTop K) : ∀ᶠ n in atTop, ∀ x ∈ K, 0 < F n x := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe; simp
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne hf
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv _ (hpos x₀ hx₀K)] with n hn x hx
  have h1 := hn x hx
  have h2 : f x₀ ≤ f x := hmin hx
  rw [Real.dist_eq] at h1
  linarith [le_abs_self (f x - F n x)]

/-- If `Fₙ → f` uniformly on the compact support of the continuous function `ψ`, then
`∫_U Fₙ ψ → ∫_U f ψ`. -/
theorem tendsto_setIntegral_mul_of_tendstoUniformlyOn {U : Set (E d)} (hU : MeasurableSet U)
    {ψ : E d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    {F : ℕ → E d → ℝ} {f : E d → ℝ} (hF : ∀ᶠ n in atTop, ContinuousOn (F n) (tsupport ψ))
    (hf : ContinuousOn f (tsupport ψ)) (hconv : TendstoUniformlyOn F f atTop (tsupport ψ)) :
    Tendsto (fun n ↦ ∫ x in U, F n x * ψ x) atTop (𝓝 (∫ x in U, f x * ψ x)) := by
  set K := tsupport ψ
  have hK : IsCompact K := hψc.isCompact
  have hred : ∀ g : E d → ℝ, ∫ x in U, g x * ψ x = ∫ x in K, g x * ψ x := fun g ↦
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hU hψU fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx.2]
  simp_rw [hred]
  set C := ∫ x in K, |ψ x|
  have hC0 : 0 ≤ C := setIntegral_nonneg hK.measurableSet fun x _ ↦ abs_nonneg _
  have hψi : IntegrableOn (fun x ↦ |ψ x|) K := hψ.abs.continuousOn.integrableOn_compact hK
  rw [Metric.tendsto_atTop']
  intro ε hε
  have hη : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hev := (Metric.tendstoUniformlyOn_iff.1 hconv _ hη).and hF
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn.le
  have i1 : IntegrableOn (fun x ↦ F n x * ψ x) K :=
    (h2.mul hψ.continuousOn).integrableOn_compact hK
  have i2 : IntegrableOn (fun x ↦ f x * ψ x) K :=
    (hf.mul hψ.continuousOn).integrableOn_compact hK
  rw [dist_eq_norm, ← integral_sub i1 i2]
  calc ‖∫ x in K, (F n x * ψ x - f x * ψ x)‖ ≤ ∫ x in K, ε / (C + 1) * |ψ x| := by
        refine norm_integral_le_of_norm_le (hψi.const_mul _)
          ((ae_restrict_mem hK.measurableSet).mono fun x hx ↦ ?_)
        have := h1 x hx
        rw [Real.dist_eq, abs_sub_comm] at this
        rw [← sub_mul, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right this.le (abs_nonneg _)
    _ = ε / (C + 1) * C := integral_const_mul _ _
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- If `∫ wₙ² → 0` and `φ ∈ L²`, then `∫ wₙ φ → 0` (Cauchy–Schwarz). -/
theorem tendsto_integral_mul_of_lintegral_sq {μ : Measure (E d)} {W : ℕ → E d → ℝ}
    (hW : ∀ n, AEStronglyMeasurable (W n) μ)
    (h0 : Tendsto (fun n ↦ ∫⁻ x, ENNReal.ofReal (W n x ^ 2) ∂μ) atTop (𝓝 0))
    {φ : E d → ℝ} (hφ : MemLp φ 2 μ) :
    Tendsto (fun n ↦ ∫ x, W n x * φ x ∂μ) atTop (𝓝 0) := by
  have hfin : ∀ᶠ n in atTop, ∫⁻ x, ENNReal.ofReal (W n x ^ 2) ∂μ < ⊤ :=
    h0.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  set c := (∫ x, ‖φ x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
  set a : ℕ → ℝ := fun n ↦ ((∫⁻ x, ENNReal.ofReal (W n x ^ 2) ∂μ).toReal) ^ (1 / (2 : ℝ)) * c
  have ha : Tendsto a atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ (∫⁻ x, ENNReal.ofReal (W n x ^ 2) ∂μ).toReal) atTop (𝓝 0) := by
      simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    have h2 := ((Real.continuous_rpow_const (q := 1 / (2 : ℝ)) (by norm_num)).tendsto 0).comp h1
    rw [Real.zero_rpow (by norm_num)] at h2
    simpa [a] using h2.mul_const c
  have hφ' : MemLp φ (ENNReal.ofReal 2) μ := by simpa using hφ
  refine squeeze_zero_norm' ?_ ha
  filter_upwards [hfin] with n hn
  have hm : MemLp (W n) 2 μ := by
    rw [memLp_two_iff_integrable_sq (hW n)]
    exact ⟨(hW n).pow 2, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun x ↦ sq_nonneg (W n x))).2 hn⟩
  have hm' : MemLp (W n) (ENNReal.ofReal 2) μ := by simpa using hm
  have hH := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hm' hφ'
  have hW2 : ∫ x, ‖W n x‖ ^ (2 : ℝ) ∂μ = (∫⁻ x, ENNReal.ofReal (W n x ^ 2) ∂μ).toReal := by
    rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x ↦ sq_nonneg _)
      ((hW n).pow 2)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp [sq_abs]
  rw [hW2] at hH
  refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ hH)
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp [norm_mul]

/-- If `∫ wₙ² → 0` and `|Φₙ| ≤ c` eventually, then `∫ wₙ Φₙ → 0` on a finite measure space. -/
theorem tendsto_integral_mul_of_lintegral_sq_of_bdd {μ : Measure (E d)} [IsFiniteMeasure μ]
    {W Φ : ℕ → E d → ℝ} (hW : ∀ n, AEStronglyMeasurable (W n) μ)
    (h0 : Tendsto (fun n ↦ ∫⁻ x, ENNReal.ofReal (W n x ^ 2) ∂μ) atTop (𝓝 0)) {c : ℝ}
    (hc : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, ‖Φ n x‖ ≤ c) :
    Tendsto (fun n ↦ ∫ x, W n x * Φ n x ∂μ) atTop (𝓝 0) := by
  have habs : Tendsto (fun n ↦ ∫ x, |W n x| * c ∂μ) atTop (𝓝 0) :=
    tendsto_integral_mul_of_lintegral_sq (W := fun n x ↦ |W n x|)
      (fun n ↦ continuous_abs.comp_aestronglyMeasurable (hW n))
      (by simpa [sq_abs] using h0) (memLp_const c)
  refine squeeze_zero_norm' ?_ habs
  have hfin : ∀ᶠ n in atTop, ∫⁻ x, ENNReal.ofReal (W n x ^ 2) ∂μ < ⊤ :=
    h0.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  filter_upwards [hfin, hc] with n hn hcn
  have hm : MemLp (W n) 2 μ := by
    rw [memLp_two_iff_integrable_sq (hW n)]
    exact ⟨(hW n).pow 2, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun x ↦ sq_nonneg (W n x))).2 hn⟩
  refine norm_integral_le_of_norm_le ((hm.integrable one_le_two).abs.mul_const c) ?_
  filter_upwards [hcn] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

/-- The inner variation integrand vanishes outside the support of `ξ`. -/
theorem innerVarIntegrand_eq_zero_of_notMem (Q v χ : E d → ℝ) {ξ : E d → E d} {x : E d}
    (hx : x ∉ tsupport ξ) : innerVarIntegrand Q v χ ξ x = 0 := by
  simp [innerVarIntegrand, divergence, fderiv_of_notMem_tsupport ℝ hx,
    image_eq_zero_of_notMem_tsupport hx]

/-- **Uniform gradient bound for large times** on a compact `K ⊆ U`, from the interior Lipschitz
estimate (3.12) and `0 ≤ u ≤ M`. -/
theorem exists_bound_gradₓ_of_interiorLipEst {U : Set (E d)} (hU : IsOpen U)
    {u : E d × ℝ → ℝ} {C M : ℝ} (hlip : InteriorLipEst U u C) (h0 : ∀ p ∈ UInf U, 0 ≤ u p)
    (hM : ∀ p ∈ UInf U, u p ≤ M) {K : Set (E d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B T : ℝ, ∀ t, T < t → ∀ x ∈ K, ‖gradₓ u (x, t)‖ ≤ B := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  set r := min (δ / 4) 1
  have hr : 0 < r := lt_min (by linarith) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hrδ : r ≤ δ / 4 := min_le_left _ _
  refine ⟨C * (M / r + 1), (2 * r) ^ 2, fun t ht x hx ↦ ?_⟩
  have hcyl : parCyl x t (2 * r) ⊆ UInf U := fun q hq ↦ by
    refine ⟨hδU (mem_cthickening_of_dist_le q.1 x δ K hx ?_), ?_⟩
    · have := mem_ball.1 hq.1
      linarith
    · have := hq.2.1
      change 0 < q.2
      linarith
  refine hlip x t r hr hr1 hcyl M (fun q hq ↦ ?_) (x, t) ⟨mem_ball_self hr, ?_⟩
  · rw [abs_le]
    exact ⟨by linarith [h0 q (hcyl hq), hM q (hcyl hq)], hM q (hcyl hq)⟩
  · simp only [mem_Ioc]
    constructor <;> nlinarith

end LongTime

end PerronVariational

end
