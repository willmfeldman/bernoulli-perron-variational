/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.Common
public import PerronVariational.Statements.Intermediate
import Mathlib.Algebra.Order.Ring.Star
import PerronVariational.Inner.WeakGrad
import PerronVariational.Registry.FunctionalAnalysis

/-!
# Weak and strong convergence of derivatives

Section 4.2 and Lemma 4.2 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. Named analytic
steps of the compactness argument of Proposition 4.1, for a sequence `v_n` converging locally
uniformly on `U_∞` to `u`:
* `Inner.tendstoWeakL2_gradₓ`: `∇v_n ⇀ ∇u` weakly in `L²(U × (0, T))` (identification of the weak
  limit on time slices, through Rademacher's theorem: the a.e. gradient of a locally Lipschitz
  function is its weak gradient);
* `Inner.hasWeakTimeDeriv_of_tendsto`: a weak `L²` limit of `∂ₜv_n` is the weak time derivative
  of `u`;
* Lemma 4.2 (strong `L²_loc` convergence of `∇v_n`) is proved in `Inner/StrongConv.lean`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-- For a `C¹` test function, `∂ₜψ(p) = Dψ(p)(0, 1)`. -/
theorem hasDerivAt_time_slice {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (p : E d × ℝ) :
    HasDerivAt (fun s ↦ ψ (p.1, s)) (fderiv ℝ ψ p (0, 1)) p.2 := by
  have h1 : HasDerivAt (fun s : ℝ ↦ (p.1, s)) ((0 : E d), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h2 : HasFDerivAt ψ (fderiv ℝ ψ p) (p.1, p.2) :=
    (hψ.differentiable one_ne_zero p).hasFDerivAt
  exact h2.comp_hasDerivAt p.2 h1

theorem dₜ_eq_fderiv {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (p : E d × ℝ) :
    dₜ ψ p = fderiv ℝ ψ p (0, 1) :=
  (hasDerivAt_time_slice hψ p).deriv

theorem continuous_dₜ {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) : Continuous (dₜ ψ) := by
  have : dₜ ψ = fun p ↦ fderiv ℝ ψ p (0, 1) := funext (dₜ_eq_fderiv hψ)
  rw [this]
  exact (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem dₜ_eq_zero_of_notMem {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {p : E d × ℝ}
    (hp : p ∉ tsupport ψ) : dₜ ψ p = 0 := by
  rw [dₜ_eq_fderiv hψ, fderiv_of_notMem_tsupport ℝ hp]
  rfl

/-- **Integration by parts in time** on `U_∞`: for `f` with continuous time derivative on `U_∞`
and `ψ ∈ C¹_c(U_∞)`, `∫ f ∂ₜψ = -∫ (∂ₜf) ψ`. -/
theorem integral_mul_dₜ_eq_neg {U : Set (E d)} {f ψ : E d × ℝ → ℝ}
    (hfd : ∀ p ∈ UInf U, HasDerivAt (fun s ↦ f (p.1, s)) (dₜ f p) p.2)
    (hfc : ContinuousOn f (UInf U)) (hfdc : ContinuousOn (dₜ f) (UInf U))
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ UInf U) :
    ∫ p in UInf U, f p * dₜ ψ p = -∫ p in UInf U, dₜ f p * ψ p := by
  set K := tsupport ψ with hKdef
  have hK : IsCompact K := hψc
  have hψ0 : ∀ p, p ∉ K → ψ p = 0 := fun p hp ↦ image_eq_zero_of_notMem_tsupport hp
  have hdψ0 : ∀ p, p ∉ K → dₜ ψ p = 0 := fun p hp ↦ dₜ_eq_zero_of_notMem hψ hp
  -- time margins `0 < a < t < b` on `K`
  obtain ⟨a, ha0, haK⟩ : ∃ a : ℝ, 0 < a ∧ ∀ p ∈ K, a < p.2 := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun p hp ↦ by simp [he] at hp⟩
    · obtain ⟨q, hqK, hmin⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
      have hq0 : 0 < q.2 := (hψs hqK).2
      exact ⟨q.2 / 2, half_pos hq0, fun p hp ↦ by
        have := hmin hp
        simp only [Set.mem_ofPred_eq] at this
        linarith⟩
  obtain ⟨B, hB⟩ := (hK.image continuous_snd).bddAbove
  set b := max B a + 1 with hbdef
  have hab : a < b := by have := le_max_right B a; linarith
  have hbK : ∀ p ∈ K, p.2 < b := fun p hp ↦ by
    have := hB (mem_image_of_mem _ hp)
    have := le_max_left B a
    linarith
  -- the two integrands vanish off `K` and are integrable
  set F : E d × ℝ → ℝ := fun p ↦ f p * dₜ ψ p with hFdef
  set G : E d × ℝ → ℝ := fun p ↦ dₜ f p * ψ p with hGdef
  have hF0 : ∀ p, p ∉ K → F p = 0 := fun p hp ↦ by simp [F, hdψ0 p hp]
  have hG0 : ∀ p, p ∉ K → G p = 0 := fun p hp ↦ by simp [G, hψ0 p hp]
  have hFi : Integrable F := by
    refine (integrableOn_iff_integrable_of_support_subset fun p hp ↦ ?_).1
      (((hfc.mono hψs).mul (continuous_dₜ hψ).continuousOn).integrableOn_compact hK)
    by_contra h
    exact hp (hF0 p h)
  have hGi : Integrable G := by
    refine (integrableOn_iff_integrable_of_support_subset fun p hp ↦ ?_).1
      (((hfdc.mono hψs).mul hψ.continuous.continuousOn).integrableOn_compact hK)
    by_contra h
    exact hp (hG0 p h)
  have hΩF : ∫ p in UInf U, F p = ∫ p, F p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ hF0 p fun h ↦ hp (hψs h)
  have hΩG : ∫ p in UInf U, G p = ∫ p, G p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ hG0 p fun h ↦ hp (hψs h)
  change ∫ p in UInf U, F p = -∫ p in UInf U, G p
  rw [hΩF, hΩG]
  rw [Measure.volume_eq_prod] at hFi hGi ⊢
  rw [integral_prod F hFi, integral_prod G hGi, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only
  by_cases hx : x ∈ U
  · -- one-dimensional integration by parts on `[a, b]`
    have hIoc : ∀ H : E d × ℝ → ℝ, (∀ p, p ∉ K → H p = 0) →
        ∫ t, H (x, t) = ∫ t in a..b, H (x, t) := by
      intro H hH
      rw [intervalIntegral.integral_of_le hab.le]
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ hH _ fun hK' ↦ ht
        (show t ∈ Ioc a b from ⟨haK _ hK', (hbK _ hK').le⟩)).symm
    rw [hIoc F hF0, hIoc G hG0]
    have hmem : ∀ t ∈ uIcc a b, (x, t) ∈ UInf U := fun t ht ↦
      ⟨hx, lt_of_lt_of_le ha0 (by rw [uIcc_of_le hab.le] at ht; exact ht.1)⟩
    have hu : ∀ t ∈ uIcc a b, HasDerivAt (fun s ↦ f (x, s)) (dₜ f (x, t)) t :=
      fun t ht ↦ hfd (x, t) (hmem t ht)
    have hv : ∀ t ∈ uIcc a b, HasDerivAt (fun s ↦ ψ (x, s)) (dₜ ψ (x, t)) t := fun t _ ↦ by
      rw [dₜ_eq_fderiv hψ]
      exact hasDerivAt_time_slice hψ (x, t)
    have hu' : IntervalIntegrable (fun t ↦ dₜ f (x, t)) volume a b :=
      (hfdc.comp (continuous_const.prodMk continuous_id).continuousOn hmem).intervalIntegrable
    have hv' : IntervalIntegrable (fun t ↦ dₜ ψ (x, t)) volume a b :=
      ((continuous_dₜ hψ).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
    have hψa : ψ (x, a) = 0 := hψ0 _ fun h ↦ lt_irrefl a (haK _ h)
    have hψb : ψ (x, b) = 0 := hψ0 _ fun h ↦ lt_irrefl b (hbK _ h)
    simp only [F, G]
    rw [hibp, hψa, hψb, ← intervalIntegral.integral_neg]
    simp
  · have hnK : ∀ t, (x, t) ∉ K := fun t h ↦ hx (hψs h).1
    simp [F, G, hψ0 _ (hnK _), hdψ0 _ (hnK _)]

/-- **Weak convergence of spatial gradients** (Section 4.2: "`u_ε` is uniformly bounded in
`H¹(U × (0, T))` ... weakly converges"). Proposition 4.1(i) of the paper states weak convergence
in `L²(U_∞)`; here it is in `L²(U × (0, T))` for every `T`, because `∇u` is in general only in
`L^∞_t L²_x`, not in `L²(U_∞)`. If `v_n → u`
locally uniformly on `U_∞`, the time slices of `v_n` are differentiable with `∇ₓv_n` continuous on
`U_∞`, `u` is continuous and locally Lipschitz in space on `U_∞`, and
`∫_U |∇v_n(·, t)|² ≤ E` for all `t > 0` and `n`, then `∇v_n ⇀ ∇u` weakly in `L²(U × (0, T))` for
every `T > 0` (the whole sequence converges since the limit is identified). -/
theorem tendstoWeakL2_gradₓ {U : Set (E d)} (hU : IsOpen U) {v : ℕ → E d × ℝ → ℝ}
    {u : E d × ℝ → ℝ} (hvd : ∀ n, ∀ t > 0, DifferentiableOn ℝ (fun x ↦ v n (x, t)) U)
    (hvg : ∀ n, ContinuousOn (gradₓ (v n)) (UInf U))
    (hconv : TendstoLocallyUniformlyOn v u atTop (UInf U)) (hucont : ContinuousOn u (UInf U))
    (hulip : LocLipₓ (UInf U) u) {E0 : ℝ≥0∞} (hE0 : E0 ≠ ⊤)
    (hbd : ∀ n, ∀ t > 0, ∫⁻ x in U, ENNReal.ofReal (‖gradₓ (v n) (x, t)‖ ^ 2) ≤ E0) :
    ∀ T > 0, TendstoWeakL2 volume (U ×ˢ Ioo 0 T) (fun n ↦ gradₓ (v n)) (gradₓ u) atTop := by
  intro T hT
  have hUInfo : IsOpen (UInf U) := hU.prod isOpen_Ioi
  have hIm : MeasurableSet (Ioo (0 : ℝ) T) := measurableSet_Ioo
  have hI : volume (Ioo (0 : ℝ) T) ≠ ⊤ := by simp [Real.volume_Ioo]
  have hsub : U ×ˢ Ioo 0 T ⊆ UInf U := prod_mono le_rfl Ioo_subset_Ioi_self
  have hsubm : volume.restrict (U ×ˢ Ioo 0 T) ≤ volume.restrict (UInf U) :=
    Measure.restrict_mono hsub le_rfl
  have hsl : ∀ t > 0, TendstoWeakL2 volume U (fun n x ↦ gradₓ (v n) (x, t))
      (fun x ↦ gradₓ u (x, t)) atTop := by
    intro t ht
    have hmaps : MapsTo (fun x : E d ↦ (x, t)) U (UInf U) := fun x hx ↦ ⟨hx, ht⟩
    have hc : ContinuousOn (fun x : E d ↦ (x, t)) U := by fun_prop
    have hl : ∀ n, LocallyLipschitzOn U (fun x ↦ v n (x, t)) := fun n ↦
      locallyLipschitzOn_of_gradient hU (hvd n t ht) ((hvg n).comp hc hmaps)
    have hcv : TendstoLocallyUniformlyOn (fun n x ↦ v n (x, t)) (fun x ↦ u (x, t)) atTop U :=
      hconv.comp _ hmaps hc
    have key := tendstoWeakL2_gradient_of_tendsto hU hl (hulip.locallyLipschitzOn_slice ht) hcv
      hE0 (fun n ↦ hbd n t ht)
    unfold gradₓ
    exact key
  have hubd : ∀ t > 0, ∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, t)‖ ^ 2) ≤ E0 := by
    intro t ht
    have h := Registry.lintegral_weighted_sq_le_liminf volume U _ _ (hsl t ht) (fun _ ↦ 1)
      measurable_const (fun _ ↦ zero_le_one) 1 (fun _ ↦ le_rfl)
    simp only [one_mul] at h
    exact h.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n ↦ hbd n t ht))
  have hvm : ∀ n, AEStronglyMeasurable (gradₓ (v n)) (volume.restrict (U ×ˢ Ioo 0 T)) :=
    fun n ↦ ((hvg n).mono hsub).aestronglyMeasurable (hU.measurableSet.prod hIm)
  have hum : AEStronglyMeasurable (gradₓ u) (volume.restrict (U ×ˢ Ioo 0 T)) :=
    ((locallyIntegrableOn_gradₓ hUInfo hucont hulip).aestronglyMeasurable).mono_measure hsubm
  exact tendstoWeakL2_prod_of_slices hIm hI
    (fun n ↦ memLp_prod_of_slices hIm hI (hvm n) hE0 fun t ht ↦ hbd n t ht.1)
    (memLp_prod_of_slices hIm hI hum hE0 fun t ht ↦ hubd t ht.1) hE0
    (fun n t ht ↦ hbd n t ht.1) fun t ht ↦ hsl t ht.1

/-- **The weak limit of `∂ₜv_n` is `∂ₜu`** (proof of Proposition 4.1, Section 4.4). If `v_n` are
`C¹` in time on `U_∞` (with continuous `∂ₜv_n`), `v_n → u` locally uniformly on `U_∞`, and
`∂ₜv_n ⇀ w` weakly in `L²(U_∞)`, then `w` is the weak time derivative of `u` in `U_∞` (integrate by
parts in `t` and pass to the limit). -/
theorem hasWeakTimeDeriv_of_tendsto {U : Set (E d)} (hU : IsOpen U) {v : ℕ → E d × ℝ → ℝ}
    {u w : E d × ℝ → ℝ}
    (hvd : ∀ n, ∀ p ∈ UInf U, DifferentiableAt ℝ (fun s ↦ v n (p.1, s)) p.2)
    (hvc : ∀ n, ContinuousOn (v n) (UInf U)) (hvdc : ∀ n, ContinuousOn (dₜ (v n)) (UInf U))
    (hconv : TendstoLocallyUniformlyOn v u atTop (UInf U)) (hucont : ContinuousOn u (UInf U))
    (hw : TendstoWeakL2 volume (UInf U) (fun n ↦ dₜ (v n)) w atTop) :
    HasWeakTimeDeriv (UInf U) u w := by
  have hΩo : IsOpen (UInf U) := hU.prod isOpen_Ioi
  have hΩm : MeasurableSet (UInf U) := hΩo.measurableSet
  refine ⟨hucont.locallyIntegrableOn hΩm, ?_, ?_⟩
  · rw [locallyIntegrableOn_iff hΩo.isLocallyClosed]
    intro k hk hkc
    have : IsFiniteMeasure (volume.restrict k) :=
      isFiniteMeasure_restrict.2 hkc.measure_lt_top.ne
    have h := hw.2.1.restrict k
    rw [Measure.restrict_restrict_of_subset hk] at h
    exact h.integrable one_le_two
  · intro ψ hψ hψc hψs
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    set K := tsupport ψ with hKdef
    have hK : IsCompact K := hψc
    have hKm : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    have hid : ∀ n, ∫ p in UInf U, v n p * dₜ ψ p = -∫ p in UInf U, dₜ (v n) p * ψ p :=
      fun n ↦ integral_mul_dₜ_eq_neg (fun p hp ↦ (hvd n p hp).hasDerivAt) (hvc n) (hvdc n)
        hψ1 hψc hψs
    -- the `u`-term: uniform convergence on `K`
    have hΩK : ∀ g : E d × ℝ → ℝ, ∫ p in UInf U, g p * dₜ ψ p = ∫ p in K, g p * dₜ ψ p :=
      fun g ↦ setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩm hψs fun p hp ↦ by
        simp [dₜ_eq_zero_of_notMem hψ1 hp.2]
    obtain ⟨Bu, hBu⟩ := hK.exists_bound_of_continuousOn (hucont.mono hψs)
    obtain ⟨Bψ, hBψ⟩ := hK.exists_bound_of_continuousOn (continuous_dₜ hψ1).continuousOn
    have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩo).1 hconv K hψs hK
    have T1 : Tendsto (fun n ↦ ∫ p in UInf U, v n p * dₜ ψ p) atTop
        (𝓝 (∫ p in UInf U, u p * dₜ ψ p)) := by
      simp only [hΩK]
      refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (Bu + 1) * Bψ)
        (Eventually.of_forall fun n ↦ (((hvc n).mono hψs).aestronglyMeasurable hKm).mul
          (continuous_dₜ hψ1).aestronglyMeasurable) ?_ (integrable_const _) ?_
      · filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hunif) 1 one_pos] with n hn
        refine ae_restrict_of_forall_mem hKm fun p hp ↦ ?_
        have h1 := hn p hp
        have h2 := hBu p hp
        have h3 := hBψ p hp
        rw [Real.dist_eq] at h1
        rw [Real.norm_eq_abs] at h2 h3 ⊢
        rw [abs_mul]
        have : |v n p| ≤ Bu + 1 := by
          have := abs_sub_abs_le_abs_sub (v n p) (u p)
          rw [abs_sub_comm] at h1
          linarith
        exact mul_le_mul this h3 (abs_nonneg _) (by linarith [abs_nonneg (u p)])
      · exact ae_restrict_of_forall_mem hKm fun p hp ↦
          (hconv.tendsto_at (hψs hp)).mul_const _
    -- the `w`-term: weak convergence tested with `ψ`
    have hψmem : MemLp ψ 2 (volume.restrict (UInf U)) :=
      (hψ.continuous.memLp_of_hasCompactSupport hψc).restrict _
    have T2 : Tendsto (fun n ↦ ∫ p in UInf U, dₜ (v n) p * ψ p) atTop
        (𝓝 (∫ p in UInf U, w p * ψ p)) := by
      have h := hw.2.2 ψ hψmem
      have e : ∀ a b : ℝ, inner ℝ a b = a * b := fun a b ↦ by
        simp [RCLike.inner_apply, mul_comm]
      simp only [e] at h
      exact h
    have T3 := T2.neg
    simp only [← hid] at T3
    exact tendsto_nhds_unique T1 T3

end Inner

end PerronVariational

end
