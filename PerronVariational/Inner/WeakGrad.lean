/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.Common
public import PerronVariational.Statements.Intermediate
import GMTFoundations.Sobolev.L2Inner
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Registry.FunctionalAnalysis

/-!
# Weak convergence of gradients under locally uniform convergence

The spatial identification step behind the weak convergence of the gradients (Section 4.2) and the
limit of the dissipation inequality (proof of Proposition 4.1, Section 4.4) in F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981: if `f_n → f` locally uniformly on an open `U ⊆ ℝᵈ`, all
`f_n` and `f` are locally Lipschitz on `U`, and `∫_U |∇f_n|² ≤ E`, then `∇f_n ⇀ ∇f` weakly in
`L²(U)` (the whole sequence: every weak subsequential limit, which exists by weak compactness of
bounded sets in `L²`, is identified with `∇f` through the weak gradients of Lipschitz functions
and the fundamental lemma of the calculus of variations; both results are from gmt-foundations
v0.1.0).

* `Inner.tendstoWeakL2_gradient_of_tendsto`: the statement above.
* `Inner.locallyLipschitzOn_of_gradient`: `C¹` on an open set implies locally Lipschitz.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

theorem eLpNorm_two_sq {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} (f : X → F) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) two_ne_zero
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [h]
  congr 1
  ext x
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- `eLpNorm f 2 μ ≤ √A` from `∫⁻ |f|² ≤ A`. -/
theorem eLpNorm_two_le_of_lintegral_norm {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} {f : X → F} {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (h : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤ A) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt A.toReal) := by
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, eLpNorm_two_sq,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hA]
  exact h

/-- A function differentiable on an open set with continuous gradient there is locally
Lipschitz on it. -/
theorem locallyLipschitzOn_of_gradient {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hd : DifferentiableOn ℝ f U) (hc : ContinuousOn (∇ f) U) : LocallyLipschitzOn U f := by
  have hfd : ContinuousOn (fderiv ℝ f) U := by
    have : fderiv ℝ f = fun x ↦ InnerProductSpace.toDual ℝ (E d) (∇ f x) := by
      ext1 x
      simp [gradient]
    rw [this]
    exact (InnerProductSpace.toDual ℝ (E d)).continuous.comp_continuousOn hc
  have h1 : ContDiffOn ℝ 1 f U := by
    rw [← zero_add (1 : WithTop ℕ∞), contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hd, by simp, contDiffOn_zero.2 hfd⟩
  intro x hx
  obtain ⟨K, t, ht, hK⟩ := (h1.contDiffAt (hU.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- `∫_U f_n h → ∫_U f h` for `f_n → f` locally uniformly on `U` and `h ∈ C_c(U)`. -/
theorem tendsto_setIntegral_mul_of_tendstoLocallyUniformlyOn {U : Set (E d)} (hU : IsOpen U)
    {f : ℕ → E d → ℝ} {f₀ : E d → ℝ} (hfc : ∀ n, ContinuousOn (f n) U)
    (hf₀c : ContinuousOn f₀ U) (hconv : TendstoLocallyUniformlyOn f f₀ atTop U) {h : E d → ℝ}
    (hh : Continuous h) (hhc : HasCompactSupport h) (hhs : tsupport h ⊆ U) :
    Tendsto (fun n ↦ ∫ x in U, f n x * h x) atTop (𝓝 (∫ x in U, f₀ x * h x)) := by
  set K := tsupport h with hKdef
  have hK : IsCompact K := hhc
  have hKm : MeasurableSet K := (isClosed_tsupport h).measurableSet
  have hUK : ∀ g : E d → ℝ, ∫ x in U, g x * h x = ∫ x in K, g x * h x := fun g ↦
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hU.measurableSet hhs fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx.2]
  simp only [hUK]
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨Bu, hBu⟩ := hK.exists_bound_of_continuousOn (hf₀c.mono hhs)
  obtain ⟨Bh, hBh⟩ := hK.exists_bound_of_continuousOn hh.continuousOn
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv K hhs hK
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (Bu + 1) * Bh)
    (Eventually.of_forall fun n ↦ (((hfc n).mono hhs).aestronglyMeasurable hKm).mul
      hh.aestronglyMeasurable) ?_ (integrable_const _) ?_
  · filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hunif) 1 one_pos] with n hn
    refine ae_restrict_of_forall_mem hKm fun p hp ↦ ?_
    have h1 := hn p hp
    have h2 := hBu p hp
    have h3 := hBh p hp
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs] at h2 h3 ⊢
    rw [abs_mul]
    have : |f n p| ≤ Bu + 1 := by
      have := abs_sub_abs_le_abs_sub (f n p) (f₀ p)
      rw [abs_sub_comm] at h1
      linarith
    exact mul_le_mul this h3 (abs_nonneg _) (by linarith [abs_nonneg (f₀ p)])
  · exact ae_restrict_of_forall_mem hKm fun p hp ↦
      (hconv.tendsto_at (hhs hp)).mul_const _

/-- **Weak convergence of gradients.** If `f_n → f` locally uniformly on the open set `U`, all
`f_n` and `f` are locally Lipschitz on `U`, and `∫_U |∇f_n|² ≤ E < ∞`, then `∇f_n ⇀ ∇f` weakly
in `L²(U)`. -/
theorem tendstoWeakL2_gradient_of_tendsto {U : Set (E d)} (hU : IsOpen U) {f : ℕ → E d → ℝ}
    {f₀ : E d → ℝ} (hf : ∀ n, LocallyLipschitzOn U (f n)) (hf₀ : LocallyLipschitzOn U f₀)
    (hconv : TendstoLocallyUniformlyOn f f₀ atTop U) {E0 : ℝ≥0∞} (hE0 : E0 ≠ ⊤)
    (hbd : ∀ n, ∫⁻ x in U, ENNReal.ofReal (‖∇ (f n) x‖ ^ 2) ≤ E0) :
    TendstoWeakL2 volume U (fun n ↦ ∇ (f n)) (∇ f₀) atTop := by
  set μ := volume.restrict U with hμ
  have hUm : MeasurableSet U := hU.measurableSet
  set B := Real.sqrt E0.toReal with hBdef
  have hB : ∀ n, eLpNorm (∇ (f n)) 2 μ ≤ ENNReal.ofReal B := fun n ↦
    eLpNorm_two_le_of_lintegral_norm hE0 (hbd n)
  have hmem : ∀ n, MemLp (∇ (f n)) 2 μ := fun n ↦
    ⟨(GMTFoundations.measurable_gradient _).aestronglyMeasurable,
      (hB n).trans_lt ENNReal.ofReal_lt_top⟩
  have hW : ∀ n, HasWeakGradient U (f n) (∇ (f n)) := fun n ↦
    (Registry.memH1Loc_gradient_of_locallyLipschitzOn hU (hf n)).1
  have hW₀ : HasWeakGradient U f₀ (∇ f₀) :=
    (Registry.memH1Loc_gradient_of_locallyLipschitzOn hU hf₀).1
  have hfc : ∀ n, ContinuousOn (f n) U := fun n ↦ (hf n).continuousOn
  have hf₀c : ContinuousOn f₀ U := hf₀.continuousOn
  -- identification of weak subsequential limits
  have hid : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ G : E d → E d,
      TendstoWeakL2 volume U (fun n ↦ ∇ (f (ns n))) G atTop → G =ᵐ[μ] ∇ f₀ := by
    intro ns hns G hG
    -- `∫_U ⟪G, g v⟫ = ∫_U ⟪∇f₀, v⟫ g` for test functions `g`
    have hkey : ∀ g : E d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ U →
        ∀ v : E d, ∫ x in U, ⟪G x, g x • v⟫ = ∫ x in U, ⟪∇ f₀ x, v⟫ * g x := by
      intro g hg hgc hgs v
      have hgv : MemLp (fun x ↦ g x • v) 2 μ :=
        ((hg.continuous.smul continuous_const).memLp_of_hasCompactSupport
          (hgc.smul_right)).restrict _
      have h1 := hG.2.2 _ hgv
      have heq : ∀ n, ∫ x in U, ⟪∇ (f (ns n)) x, g x • v⟫ =
          -∫ x in U, f (ns n) x * fderiv ℝ g x v := by
        intro n
        rw [(hW (ns n)).2.2 g hg hgc hgs v, neg_neg]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [inner_smul_right]
        ring
      have hdg : Continuous fun x ↦ fderiv ℝ g x v :=
        (hg.continuous_fderiv (by simp)).clm_apply continuous_const
      have h2 := (tendsto_setIntegral_mul_of_tendstoLocallyUniformlyOn hU
        (fun n ↦ hfc (ns n)) hf₀c
        (fun u hu x hx ↦ let ⟨t, ht, h⟩ := hconv u hu x hx; ⟨t, ht, hns.eventually h⟩) hdg
        (hgc.fderiv_apply ℝ v)
        ((tsupport_fderiv_apply_subset ℝ v).trans hgs)).neg
      simp only [← heq] at h2
      rw [tendsto_nhds_unique h1 h2, hW₀.2.2 g hg hgc hgs v, neg_neg]
    have hGloc : LocallyIntegrableOn G U volume := by
      rw [locallyIntegrableOn_iff hU.isLocallyClosed]
      intro k hk hkc
      haveI : IsFiniteMeasure (volume.restrict k) :=
        isFiniteMeasure_restrict.2 hkc.measure_lt_top.ne
      have h := hG.2.1.restrict k
      rw [Measure.restrict_restrict_of_subset hk] at h
      exact h.integrable one_le_two
    have hloc : LocallyIntegrableOn (fun x ↦ G x - ∇ f₀ x) U volume := hGloc.sub hW₀.2.1
    have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs ↦ by
      by_cases hI : Integrable (fun x ↦ g x • (G x - ∇ f₀ x))
      swap
      · exact integral_undef hI
      refine ext_inner_left ℝ fun v ↦ ?_
      rw [inner_zero_right, ← integral_inner hI v]
      have hK : IsCompact (tsupport g) := hgc
      have hKm : MeasurableSet (tsupport g) := (isClosed_tsupport g).measurableSet
      have hg0 : ∀ x, x ∉ tsupport g → g x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
      -- integrability of `g ⟪G, v⟫`
      have hgv : MemLp (fun x ↦ g x • v) 2 μ :=
        ((hg.continuous.smul continuous_const).memLp_of_hasCompactSupport
          (hgc.smul_right)).restrict _
      have hA : Integrable (fun x ↦ ⟪G x, g x • v⟫) := by
        refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).1
          (GMTFoundations.integrable_inner_of_memLp hG.2.1 hgv)
        by_contra hxU
        exact hx (by simp [hg0 x fun h ↦ hxU (hgs h)])
      have hI' : Integrable (fun x ↦ ⟪v, g x • (G x - ∇ f₀ x)⟫) := hI.const_inner v
      have hC : Integrable (fun x ↦ ⟪∇ f₀ x, v⟫ * g x) := by
        refine (hA.sub hI').congr (Eventually.of_forall fun x ↦ ?_)
        simp only [Pi.sub_apply]
        rw [inner_smul_right, inner_smul_right, inner_sub_right, real_inner_comm v (G x),
          real_inner_comm v (∇ f₀ x)]
        ring
      have hpt : (fun x ↦ ⟪v, g x • (G x - ∇ f₀ x)⟫) =
          fun x ↦ ⟪G x, g x • v⟫ - ⟪∇ f₀ x, v⟫ * g x := by
        ext x
        rw [inner_smul_right, inner_smul_right, inner_sub_right, real_inner_comm v (G x),
          real_inner_comm v (∇ f₀ x)]
        ring
      rw [hpt, integral_sub hA hC]
      have hA' : ∫ x, ⟪G x, g x • v⟫ = ∫ x in U, ⟪G x, g x • v⟫ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          simp [hg0 x fun h ↦ hx (hgs h)]).symm
      have hC' : ∫ x, ⟪∇ f₀ x, v⟫ * g x = ∫ x in U, ⟪∇ f₀ x, v⟫ * g x :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          simp [hg0 x fun h ↦ hx (hgs h)]).symm
      rw [hA', hC', hkey g hg hgc hgs v, sub_self]
    rw [EventuallyEq, ae_restrict_iff' hUm]
    filter_upwards [hz] with x hx hxU
    exact sub_eq_zero.1 (hx hxU)
  -- every subsequence has a further subsequence converging weakly to `∇f₀`
  have hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      TendstoWeakL2 volume U (fun n ↦ ∇ (f (ns (ms n)))) (∇ f₀) atTop := by
    intro ns hns
    obtain ⟨φ, hφ, G, hG⟩ := Registry.exists_tendstoWeakL2_subseq volume U
      (fun n ↦ ∇ (f (ns n))) B (fun n ↦ hmem _) (fun n ↦ hB _)
    have hGe := hid (fun n ↦ ns (φ n)) (hns.comp hφ.tendsto_atTop) G hG
    refine ⟨φ, hG.1, hG.2.1.ae_eq hGe, fun ψ hψ ↦ ?_⟩
    have : ∫ x in U, ⟪∇ f₀ x, ψ x⟫ = ∫ x in U, ⟪G x, ψ x⟫ :=
      integral_congr_ae (hGe.mono fun x hx ↦ by simp only [hx])
    rw [this]
    exact hG.2.2 ψ hψ
  obtain ⟨ms, h0⟩ := hsub id tendsto_id
  refine ⟨hmem, h0.2.1, fun ψ hψ ↦ tendsto_of_subseq_tendsto fun ns hns ↦ ?_⟩
  obtain ⟨ms, h⟩ := hsub ns hns
  exact ⟨ms, h.2.2 ψ hψ⟩

/-! ### Space-time versions -/

/-- `∇ₓφ = 0` off `spt φ`. -/
theorem gradₓ_eq_zero_of_notMem {φ : E d × ℝ → ℝ} {p : E d × ℝ} (hp : p ∉ tsupport φ) :
    gradₓ φ p = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at hp
  have ht : Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝 p) :=
    (continuous_id.prodMk continuous_const).tendsto' p.1 p (by simp)
  have : (fun y : E d ↦ φ (y, p.2)) =ᶠ[𝓝 p.1] fun _ ↦ (0 : ℝ) := ht.eventually hp
  rw [gradₓ, gradient, this.fderiv_eq]
  simp

/-- `∇ₓφ` is Borel measurable for continuous `φ`. -/
theorem measurable_gradₓ {φ : E d × ℝ → ℝ} (hφ : Continuous φ) : Measurable (gradₓ φ) := by
  have h := measurable_fderiv_with_param (𝕜 := ℝ) (f := fun (t : ℝ) (y : E d) ↦ φ (y, t))
    (by exact hφ.comp continuous_swap)
  have : gradₓ φ = fun p ↦ (InnerProductSpace.toDual ℝ (E d)).symm
      (fderiv ℝ (fun y ↦ φ (y, p.2)) p.1) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.measurable.comp
    (h.comp measurable_swap)

/-- `|∇ₓφ| ≤ Lip φ`. -/
theorem norm_gradₓ_le {φ : E d × ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (p : E d × ℝ) :
    ‖gradₓ φ p‖ ≤ K := by
  rw [gradₓ, gradient, LinearIsometryEquiv.norm_map]
  simpa using norm_fderiv_le_of_lipschitz ℝ (hφ.comp (LipschitzWith.prodMk_right p.2))

/-- `∇ₓu` is locally integrable on an open set `Ω` where `u` is continuous and locally Lipschitz in
space (hence `AEStronglyMeasurable` on `Ω`): near each point `∇ₓu` agrees with `∇ₓ(η u)` for a
continuous cut-off `η`, which is Borel measurable, and is bounded by the local Lipschitz
constant. -/
theorem locallyIntegrableOn_gradₓ {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u Ω) (hlip : LocLipₓ Ω u) : LocallyIntegrableOn (gradₓ u) Ω volume := by
  intro p hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ p hp
  set r := ε / 3 with hr
  have hr0 : 0 < r := by positivity
  set η : E d × ℝ → ℝ := fun q ↦ max 0 (min 1 (2 - dist q p / r)) with hη
  have hηc : Continuous η :=
    continuous_const.max (continuous_const.min (continuous_const.sub
      ((continuous_id.dist continuous_const).div_const r)))
  have hη1 : ∀ q ∈ ball p r, η q = 1 := fun q hq ↦ by
    have : dist q p / r < 1 := (div_lt_one hr0).2 (mem_ball.1 hq)
    simp only [η]
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hη0 : ∀ q, q ∉ closedBall p (2 * r) → η q = 0 := fun q hq ↦ by
    have : 2 < dist q p / r := by
      rw [mem_closedBall, not_le] at hq
      rw [lt_div_iff₀ hr0]
      linarith
    simp only [η]
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  have hcb : closedBall p (2 * r) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hball
  set w : E d × ℝ → ℝ := fun q ↦ η q * u q with hw
  have hwc : Continuous w := by
    refine continuous_iff_continuousAt.2 fun q ↦ ?_
    by_cases hq : q ∈ Ω
    · exact hηc.continuousAt.mul (hu.continuousAt (hΩ.mem_nhds hq))
    · have hq' : q ∉ closedBall p (2 * r) := fun h ↦ hq (hcb h)
      have hev : w =ᶠ[𝓝 q] fun _ ↦ 0 := by
        filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hq'] with q' hq''
        simp [w, hη0 q' hq'']
      exact continuousAt_const.congr hev.symm
  have hgeq : ∀ q ∈ ball p r, gradₓ w q = gradₓ u q := by
    intro q hq
    have hn : {y | (y, q.2) ∈ ball p r} ∈ 𝓝 q.1 :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds hq)
    have : (fun y ↦ w (y, q.2)) =ᶠ[𝓝 q.1] fun y ↦ u (y, q.2) :=
      Filter.mem_of_superset hn fun y hy ↦ by simp [w, hη1 _ hy]
    simp only [gradₓ, gradient]
    rw [this.fderiv_eq]
  obtain ⟨K, N, hN, hK⟩ := hlip p hp
  set V := interior N ∩ ball p r with hVdef
  have hVo : IsOpen V := isOpen_interior.inter isOpen_ball
  have hpV : p ∈ V := ⟨mem_interior_iff_mem_nhds.2 hN, mem_ball_self hr0⟩
  have hbound : ∀ q ∈ V, ‖gradₓ u q‖ ≤ Real.toNNReal K := by
    intro q hq
    have hn : {y | (y, q.2) ∈ interior N} ∈ 𝓝 q.1 :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hq.1)
    have hlipq : LipschitzOnWith (Real.toNNReal K) (fun y ↦ u (y, q.2))
        {y | (y, q.2) ∈ interior N} := LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ by
      rw [Real.dist_eq, dist_eq_norm]
      exact (hK _ (interior_subset hy) _ (interior_subset hz) rfl).trans
        (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) (norm_nonneg _))
    rw [gradₓ, gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitzOn ℝ hn hlipq
  have hVfin : volume V < ⊤ := (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
  refine ⟨V, mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hpV), ?_⟩
  refine IntegrableOn.of_bound hVfin ?_ (Real.toNNReal K)
    (ae_restrict_of_forall_mem hVo.measurableSet hbound)
  exact (measurable_gradₓ hwc).aestronglyMeasurable.congr
    (ae_restrict_of_forall_mem hVo.measurableSet fun q hq ↦ hgeq q hq.2)

/-- Time slices of a function locally Lipschitz in space on `U_∞` are locally Lipschitz. -/
theorem LocLipₓ.locallyLipschitzOn_slice {U : Set (E d)} {u : E d × ℝ → ℝ}
    (h : LocLipₓ (UInf U) u) {t : ℝ} (ht : 0 < t) : LocallyLipschitzOn U (fun x ↦ u (x, t)) := by
  intro x hx
  obtain ⟨K, N, hN, hK⟩ := h (x, t) ⟨hx, ht⟩
  have hN' : {y | (y, t) ∈ N} ∈ 𝓝 x :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hN
  refine ⟨Real.toNNReal K, {y | (y, t) ∈ N}, mem_nhdsWithin_of_mem_nhds hN',
    LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  exact (hK (y, t) hy (z, t) hz rfl).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) (norm_nonneg _))

theorem volume_restrict_prod (U : Set (E d)) (I : Set ℝ) :
    volume.restrict (U ×ˢ I) = (volume.restrict U).prod (volume.restrict I) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]

/-- `L²(U × I)` from uniform `L²(U)` bounds on the time slices (Tonelli). -/
theorem memLp_prod_of_slices {U : Set (E d)} {I : Set ℝ} (hIm : MeasurableSet I)
    (hI : volume I ≠ ⊤) {F : E d × ℝ → E d}
    (hFm : AEStronglyMeasurable F (volume.restrict (U ×ˢ I))) {E0 : ℝ≥0∞} (hE0 : E0 ≠ ⊤)
    (hbd : ∀ t ∈ I, ∫⁻ x in U, ENNReal.ofReal (‖F (x, t)‖ ^ 2) ≤ E0) :
    MemLp F 2 (volume.restrict (U ×ˢ I)) := by
  refine ⟨hFm, ?_⟩
  have hle : eLpNorm F 2 (volume.restrict (U ×ˢ I)) ^ 2 ≤ E0 * volume I := by
    have hm : AEMeasurable (fun p ↦ ENNReal.ofReal (‖F p‖ ^ 2)) (volume.restrict (U ×ˢ I)) :=
      (hFm.norm.aemeasurable.pow_const 2).ennreal_ofReal
    rw [eLpNorm_two_sq, volume_restrict_prod] at *
    rw [lintegral_prod_symm _ hm]
    calc ∫⁻ t, ∫⁻ x, ENNReal.ofReal (‖F (x, t)‖ ^ 2) ∂volume.restrict U ∂volume.restrict I
        ≤ ∫⁻ _, E0 ∂volume.restrict I := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hIm] with t ht
          exact hbd t ht
      _ = E0 * volume I := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  refine lt_top_iff_ne_top.2 fun h ↦ ?_
  rw [h] at hle
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.top_pow, top_le_iff] at hle
  exact ENNReal.mul_ne_top hE0 hI hle

/-- **Weak `L²(U × I)` convergence from weak convergence on time slices**, given a uniform bound
on the slice energies (dominated convergence in `t`). -/
theorem tendstoWeakL2_prod_of_slices {U : Set (E d)} {I : Set ℝ} (hIm : MeasurableSet I)
    (hI : volume I ≠ ⊤) {F : ℕ → E d × ℝ → E d} {F₀ : E d × ℝ → E d}
    (hF : ∀ n, MemLp (F n) 2 (volume.restrict (U ×ˢ I)))
    (hF₀ : MemLp F₀ 2 (volume.restrict (U ×ˢ I))) {E0 : ℝ≥0∞} (hE0 : E0 ≠ ⊤)
    (hbd : ∀ n, ∀ t ∈ I, ∫⁻ x in U, ENNReal.ofReal (‖F n (x, t)‖ ^ 2) ≤ E0)
    (hslice : ∀ t ∈ I,
      TendstoWeakL2 volume U (fun n x ↦ F n (x, t)) (fun x ↦ F₀ (x, t)) atTop) :
    TendstoWeakL2 volume (U ×ˢ I) F F₀ atTop := by
  refine ⟨hF, hF₀, fun φ hφ ↦ ?_⟩
  set μU := volume.restrict U with hμU
  set μI := volume.restrict I with hμI
  haveI : IsFiniteMeasure μI := isFiniteMeasure_restrict.2 hI
  set φ' := hφ.1.mk φ with hφ'def
  have hφφ' : φ =ᵐ[volume.restrict (U ×ˢ I)] φ' := hφ.1.ae_eq_mk
  have hcongr : ∀ G : E d × ℝ → E d,
      ∫ p in U ×ˢ I, ⟪G p, φ p⟫ = ∫ p in U ×ˢ I, ⟪G p, φ' p⟫ := fun G ↦
    integral_congr_ae (hφφ'.mono fun p hp ↦ by simp only [hp])
  simp only [hcongr]
  have hφ'm : StronglyMeasurable φ' := hφ.1.stronglyMeasurable_mk
  have hφ'L : MemLp φ' 2 (volume.restrict (U ×ˢ I)) := hφ.ae_eq hφφ'
  rw [volume_restrict_prod] at hF hF₀ hφ'L ⊢
  have hfub : ∀ G : E d × ℝ → E d, MemLp G 2 (μU.prod μI) →
      ∫ p, ⟪G p, φ' p⟫ ∂(μU.prod μI) = ∫ t, (∫ x, ⟪G (x, t), φ' (x, t)⟫ ∂μU) ∂μI :=
    fun G hG ↦ integral_prod_symm _ (GMTFoundations.integrable_inner_of_memLp hG hφ'L)
  rw [hfub _ hF₀]
  have hseq : (fun n ↦ ∫ p, ⟪F n p, φ' p⟫ ∂(μU.prod μI)) =
      fun n ↦ ∫ t, (∫ x, ⟪F n (x, t), φ' (x, t)⟫ ∂μU) ∂μI := funext fun n ↦ hfub _ (hF n)
  rw [hseq]
  -- the slice norms of `φ'`
  have hφ2m : Measurable fun p ↦ ENNReal.ofReal (‖φ' p‖ ^ 2) :=
    (hφ'm.measurable.norm.pow_const 2).ennreal_ofReal
  set N : ℝ → ℝ≥0∞ := fun t ↦ ∫⁻ x, ENNReal.ofReal (‖φ' (x, t)‖ ^ 2) ∂μU with hNdef
  have hNm : Measurable N := hφ2m.lintegral_prod_left'
  have hNint : ∫⁻ t, N t ∂μI ≠ ⊤ := by
    rw [hNdef, ← lintegral_prod_symm' _ hφ2m, ← eLpNorm_two_sq]
    exact ENNReal.pow_ne_top hφ'L.2.ne
  have hNfin : ∀ᵐ t ∂μI, N t < ⊤ := ae_lt_top hNm hNint
  have hsl : ∀ t, N t < ⊤ → MemLp (fun x ↦ φ' (x, t)) 2 μU := by
    intro t ht
    refine ⟨(hφ'm.comp_measurable measurable_prodMk_right).aestronglyMeasurable, ?_⟩
    have h2 : eLpNorm (fun x ↦ φ' (x, t)) 2 μU ^ 2 = N t := eLpNorm_two_sq _
    refine lt_top_iff_ne_top.2 fun h ↦ ?_
    rw [h] at h2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.top_pow] at h2
    exact ht.ne h2.symm
  set C := Real.sqrt E0.toReal with hC
  set bound : ℝ → ℝ := fun t ↦ C * Real.sqrt (N t).toReal with hbounddef
  have hbint : Integrable bound μI := by
    refine Integrable.mono' ((((integrable_toReal_of_lintegral_ne_top hNm.aemeasurable
      hNint).add (integrable_const 1)).div_const 2).const_mul C) ?_ ?_
    · exact ((hNm.ennreal_toReal.sqrt).const_mul C).aestronglyMeasurable
    · refine Eventually.of_forall fun t ↦ ?_
      have hC0 : 0 ≤ C := Real.sqrt_nonneg _
      have ha : 0 ≤ (N t).toReal := ENNReal.toReal_nonneg
      have hs : Real.sqrt (N t).toReal ≤ ((N t).toReal + 1) / 2 := by
        nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg (N t).toReal,
          sq_nonneg (Real.sqrt (N t).toReal - 1)]
      simp only [Pi.add_apply, bound]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hs hC0
  refine tendsto_integral_of_dominated_convergence bound
    (fun n ↦ (Integrable.integral_prod_right
      (GMTFoundations.integrable_inner_of_memLp (hF n) hφ'L)).aestronglyMeasurable) hbint
      (fun n ↦ ?_) ?_
  · filter_upwards [ae_restrict_mem hIm, hNfin] with t ht hNt
    rw [Real.norm_eq_abs]
    refine (GMTFoundations.abs_integral_inner_le ((hslice t ht).1 n) (hsl t hNt)).trans ?_
    have h1 : (eLpNorm (fun x ↦ F n (x, t)) 2 μU).toReal ≤ C :=
      ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _)
        (eLpNorm_two_le_of_lintegral_norm hE0 (hbd n t ht))
    have h2 : (eLpNorm (fun x ↦ φ' (x, t)) 2 μU).toReal = Real.sqrt (N t).toReal := by
      have h3 : eLpNorm (fun x ↦ φ' (x, t)) 2 μU ^ 2 = N t := eLpNorm_two_sq _
      rw [← h3, ENNReal.toReal_pow, Real.sqrt_sq ENNReal.toReal_nonneg]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
  · filter_upwards [ae_restrict_mem hIm, hNfin] with t ht hNt
    exact (hslice t ht).2.2 _ (hsl t hNt)

end Inner

end PerronVariational

end
