/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.Common
public import PerronVariational.Statements.Intermediate
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import PerronVariational.Inner.EnergyConv
import PerronVariational.Inner.StrongGrad
import PerronVariational.Inner.WeakGrad

/-!
# Lemma 4.2: strong `L²_loc` convergence of the spatial gradients

Lemma 4.2 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. Proof of
`Inner.tendstoLpLoc_gradₓ_semilinear` by the energy argument (4.3)–(4.6) of the paper,
arranged so that no chain rule in time is needed for the limit `u`:

1. the `ε`-level energy inequality `∫ η |∇v_n|² ≤ ∫ (v_n²/2) ∂ₜη - ∫ v_n ∇v_n · ∇η`
   (`energy_ineq_semilinear`), whose right-hand side converges to
   `R(u) = ∫ (u²/2) ∂ₜη - ∫ u ∇u · ∇η` (uniform × weak products);
2. the time identity `∫ w u η = -∫ (u²/2) ∂ₜη`, as the limit of the classical identity for `v_n`
   (`integral_dₜ_mul_self`);
3. the weak heat equation in `{u > 0}` tested with `(u - δ)₊ η` and `δ → 0`, which gives
   `∫ η |∇u|² = -∫ w u η - ∫ u ∇u · ∇η = R(u)`;
4. hence `limsup ∫ η |∇v_n - ∇u|² ≤ 0`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-! ### Bounded functions with compact support -/

/-- A compact subset of `U_∞` lies in `U × (0, T)` for some `T > 0`. -/
theorem exists_subset_prod_Ioo {U : Set (E d)} {K : Set (E d × ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ UInf U) : ∃ T > 0, K ⊆ U ×ˢ Ioo 0 T := by
  obtain ⟨B, hB⟩ := (hK.image continuous_snd).bddAbove
  refine ⟨max B 0 + 1, by positivity, fun p hp ↦ ⟨(hKU hp).1, (hKU hp).2, ?_⟩⟩
  have := hB (mem_image_of_mem _ hp)
  have := le_max_left B 0
  linarith

theorem integrable_of_bound_of_compact {Ω L : Set (E d × ℝ)} (hL : IsCompact L) {F : Type*}
    [NormedAddCommGroup F] {f : E d × ℝ → F} (hm : AEStronglyMeasurable f (volume.restrict Ω))
    (C : ℝ) (hb : ∀ p ∈ L, ‖f p‖ ≤ C) (h0 : ∀ p ∉ L, f p = 0) :
    Integrable f (volume.restrict Ω) := by
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  have hon : IntegrableOn f L (volume.restrict Ω) :=
    IntegrableOn.of_bound ((Measure.restrict_apply_le _ _).trans_lt hL.measure_lt_top)
      hm.restrict C (ae_restrict_of_forall_mem hLm hb)
  refine (integrableOn_iff_integrable_of_support_subset fun p hp ↦ ?_).1 hon
  by_contra h
  exact hp (h0 p h)

theorem memLp_two_of_bound_of_compact {Ω L : Set (E d × ℝ)} (hL : IsCompact L) {F : Type*}
    [NormedAddCommGroup F] {f : E d × ℝ → F} (hm : AEStronglyMeasurable f (volume.restrict Ω))
    (C : ℝ) (hb : ∀ p ∈ L, ‖f p‖ ≤ C) (h0 : ∀ p ∉ L, f p = 0) :
    MemLp f 2 (volume.restrict Ω) := by
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  have heq : L.indicator f = f := indicator_eq_self.2 fun p hp ↦ by
    by_contra h
    exact hp (h0 p h)
  rw [← heq, memLp_indicator_iff_restrict hLm]
  have : IsFiniteMeasure ((volume.restrict Ω).restrict L) :=
    isFiniteMeasure_restrict.2 ((Measure.restrict_apply_le _ _).trans_lt hL.measure_lt_top).ne
  exact MemLp.of_bound hm.restrict C (ae_restrict_of_forall_mem hLm hb)

/-- Dominated convergence for functions vanishing off a compact `L ⊆ Ω`. -/
theorem tendsto_setIntegral_of_dominated_compact {Ω L : Set (E d × ℝ)} (hΩ : MeasurableSet Ω)
    (hL : IsCompact L) (hLΩ : L ⊆ Ω) {F : ℕ → E d × ℝ → ℝ} {F₀ : E d × ℝ → ℝ}
    (hF0 : ∀ n, ∀ p ∉ L, F n p = 0) (hF₀0 : ∀ p ∉ L, F₀ p = 0)
    (hm : ∀ n, AEStronglyMeasurable (F n) (volume.restrict L)) {g : E d × ℝ → ℝ}
    (hg : IntegrableOn g L) (hb : ∀ᶠ n in atTop, ∀ p ∈ L, |F n p| ≤ g p)
    (hlim : ∀ p ∈ L, Tendsto (fun n ↦ F n p) atTop (𝓝 (F₀ p))) :
    Tendsto (fun n ↦ ∫ p in Ω, F n p) atTop (𝓝 (∫ p in Ω, F₀ p)) := by
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  have hred : ∀ G : E d × ℝ → ℝ, (∀ p ∉ L, G p = 0) → ∫ p in Ω, G p = ∫ p in L, G p :=
    fun G hG ↦ setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ hLΩ fun p hp ↦ hG p hp.2
  rw [hred _ hF₀0]
  refine (tendsto_integral_filter_of_dominated_convergence g (Eventually.of_forall hm) ?_ hg
    (ae_restrict_of_forall_mem hLm hlim)).congr fun n ↦ (hred _ (hF0 n)).symm
  filter_upwards [hb] with n hn
  exact ae_restrict_of_forall_mem hLm fun p hp ↦ by rw [Real.norm_eq_abs]; exact hn p hp

/-- Uniformly small functions supported in a fixed compact set are small in `L²`. -/
theorem tendsto_eLpNorm_of_uniform {Ω L : Set (E d × ℝ)} (hL : IsCompact L) {F : Type*}
    [NormedAddCommGroup F] {c : ℕ → E d × ℝ → F} (h0 : ∀ n, ∀ p ∉ L, c n p = 0)
    (hcm : ∀ n, AEStronglyMeasurable (c n) (volume.restrict Ω))
    (hsmall : ∀ δ > 0, ∀ᶠ n in atTop, ∀ p ∈ L, ‖c n p‖ ≤ δ) :
    Tendsto (fun n ↦ eLpNorm (c n) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  set A : ℝ≥0∞ := volume L ^ (2 : ℝ≥0∞).toReal⁻¹ with hAdef
  have hA : A ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hL.measure_lt_top.ne
  have hbd : ∀ δ > 0, ∀ᶠ n in atTop,
      eLpNorm (c n) 2 (volume.restrict Ω) ≤ A * ENNReal.ofReal δ := by
    intro δ hδ
    filter_upwards [hsmall δ hδ] with n hn
    have hsupp : Function.support (c n) ⊆ L := fun p hp ↦ by
      by_contra h
      exact hp (h0 n p h)
    rw [← eLpNorm_restrict_eq_of_support_subset (hcm n) hsupp]
    refine (eLpNorm_le_of_ae_bound (hcm n).restrict (ae_restrict_of_forall_mem hLm hn)).trans ?_
    refine mul_le_mul_left (ENNReal.rpow_le_rpow ?_ (inv_nonneg.2 ENNReal.toReal_nonneg)) _
    rw [Measure.restrict_apply_univ]
    exact Measure.restrict_apply_le _ _
  have hT : Tendsto (fun δ : ℝ ↦ A * ENNReal.ofReal δ) (𝓝 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ))))
      (Or.inr hA)
    simpa using this
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (ENNReal.tendsto_nhds_zero.1 hT ε hε)
  have hr2 : dist (r / 2) 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith
  filter_upwards [hbd (r / 2) (half_pos hr)] with n hn
  exact hn.trans (hball hr2)

/-- Tonelli: `L²(U × I)` bound from uniform `L²(U)` bounds on the time slices. -/
theorem eLpNorm_prod_le_of_slices {U : Set (E d)} {I : Set ℝ} (hIm : MeasurableSet I)
    (hI : volume I ≠ ⊤) {F : E d × ℝ → E d}
    (hFm : AEStronglyMeasurable F (volume.restrict (U ×ˢ I))) {E0 : ℝ≥0∞} (hE0 : E0 ≠ ⊤)
    (hbd : ∀ t ∈ I, ∫⁻ x in U, ENNReal.ofReal (‖F (x, t)‖ ^ 2) ≤ E0) :
    eLpNorm F 2 (volume.restrict (U ×ˢ I)) ≤
      ENNReal.ofReal (Real.sqrt (E0 * volume I).toReal) := by
  have hle : eLpNorm F 2 (volume.restrict (U ×ˢ I)) ^ 2 ≤ E0 * volume I := by
    have hm : AEMeasurable (fun p ↦ ENNReal.ofReal (‖F p‖ ^ 2)) (volume.restrict (U ×ˢ I)) :=
      (hFm.norm.aemeasurable.pow_const 2).ennreal_ofReal
    rw [eLpNorm_two_sq F hFm]
    rw [volume_restrict_prod] at hm ⊢
    rw [lintegral_prod_symm _ hm]
    calc ∫⁻ t, ∫⁻ x, ENNReal.ofReal (‖F (x, t)‖ ^ 2) ∂volume.restrict U ∂volume.restrict I
        ≤ ∫⁻ _, E0 ∂volume.restrict I := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hIm] with t ht
          exact hbd t ht
      _ = E0 * volume I := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  have hA : E0 * volume I ≠ ⊤ := ENNReal.mul_ne_top hE0 hI
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hA]
  exact hle

/-- Weak `L²(U × (0, T))` convergence for all `T` gives convergence of `∫_{U_∞} ⟪a_n, G⟫` for
bounded `G` with compact support in `U_∞`. -/
theorem tendsto_setIntegral_inner_of_weak {U : Set (E d)} (hU : IsOpen U)
    {a : ℕ → E d × ℝ → E d} {a₀ : E d × ℝ → E d}
    (ha : ∀ T > 0, TendstoWeakL2 volume (U ×ˢ Ioo 0 T) a a₀ atTop) {L : Set (E d × ℝ)}
    (hL : IsCompact L) (hLU : L ⊆ UInf U) {G : E d × ℝ → E d}
    (hGm : AEStronglyMeasurable G (volume.restrict (UInf U))) (C : ℝ)
    (hGb : ∀ p ∈ L, ‖G p‖ ≤ C) (hG0 : ∀ p ∉ L, G p = 0) :
    Tendsto (fun n ↦ ∫ p in UInf U, ⟪a n p, G p⟫) atTop (𝓝 (∫ p in UInf U, ⟪a₀ p, G p⟫)) := by
  obtain ⟨T, hT, hLT⟩ := exists_subset_prod_Ioo hL hLU
  have hΩm : MeasurableSet (UInf U) := (hU.prod isOpen_Ioi).measurableSet
  have hsub : U ×ˢ Ioo 0 T ⊆ UInf U := prod_mono le_rfl Ioo_subset_Ioi_self
  have hred : ∀ A : E d × ℝ → E d,
      ∫ p in UInf U, ⟪A p, G p⟫ = ∫ p in U ×ˢ Ioo 0 T, ⟪A p, G p⟫ := fun A ↦
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩm hsub fun p hp ↦ by
      rw [hG0 p fun h ↦ hp.2 (hLT h), inner_zero_right]
  simp only [hred]
  exact (ha T hT).2.2 G (memLp_two_of_bound_of_compact hL
    (hGm.mono_measure (Measure.restrict_mono hsub le_rfl)) C hGb hG0)

/-! ### Pointwise facts on spatial gradients -/

/-- Local Lipschitz bounds in space bound `∇ₓu` on compact sets. -/
theorem exists_bound_gradₓ_of_locLipₓ {Ω L : Set (E d × ℝ)} (hL : IsCompact L) (hLΩ : L ⊆ Ω)
    {u : E d × ℝ → ℝ} (h : LocLipₓ Ω u) : ∃ C : ℝ, ∀ q ∈ L, ‖gradₓ u q‖ ≤ C :=
  exists_bound_of_forall_nhds hL fun p hp ↦ by
    obtain ⟨K, N, hN, hK⟩ := h p (hLΩ hp)
    refine ⟨Real.toNNReal K, interior N, interior_mem_nhds.2 hN, fun q hq ↦ ?_⟩
    have hs : {y | (y, q.2) ∈ interior N} ∈ 𝓝 q.1 :=
      (isOpen_interior.preimage (continuous_id.prodMk continuous_const)).mem_nhds hq
    refine norm_gradₓ_le_of_lipschitzOn hs (LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_)
    rw [Real.dist_eq, dist_eq_norm]
    exact (hK _ (interior_subset hy) _ (interior_subset hz) rfl).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) (norm_nonneg _))

/-- `∇ₓu = 0` where a nonnegative `u` vanishes (local minimum of the time slice). -/
theorem gradₓ_eq_zero_of_nonneg {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {u : E d × ℝ → ℝ}
    (hu0 : ∀ q ∈ Ω, 0 ≤ u q) {p : E d × ℝ} (hp : p ∈ Ω) (hup : u p = 0) : gradₓ u p = 0 := by
  apply gradₓ_eq_zero_of_isLocalMin
  have : ∀ᶠ y in 𝓝 p.1, (y, p.2) ∈ Ω :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp)
  filter_upwards [this] with y hy
  change u (p.1, p.2) ≤ u (y, p.2)
  rw [Prod.mk.eta, hup]
  exact hu0 _ hy

/-- The gradient of the truncated test function `(u - δ)₊ η` against `∇ₓu`. -/
theorem inner_gradₓ_posPart_mul {u η : E d × ℝ → ℝ} (hη : ContDiff ℝ 1 η) (hη0 : ∀ p, 0 ≤ η p)
    (δ : ℝ) (p : E d × ℝ) :
    ⟪gradₓ u p, gradₓ (fun q ↦ max (u q - δ) 0 * η q) p⟫ =
      if δ < u p then η p * ‖gradₓ u p‖ ^ 2 + (u p - δ) * ⟪gradₓ u p, gradₓ η p⟫ else 0 := by
  split_ifs with h
  · by_cases hd : DifferentiableAt ℝ (fun y ↦ u (y, p.2)) p.1
    · have hev : (fun y ↦ max (u (y, p.2) - δ) 0) =ᶠ[𝓝 p.1] fun y ↦ u (y, p.2) - δ := by
        filter_upwards [hd.continuousAt.eventually (lt_mem_nhds h)] with y hy
        exact max_eq_left (by linarith)
      have hFd : DifferentiableAt ℝ (fun y ↦ max (u (y, p.2) - δ) 0) p.1 :=
        (hd.sub_const δ).congr_of_eventuallyEq hev
      have hgF : gradₓ (fun q ↦ max (u q - δ) 0) p = gradₓ u p := by
        simp only [gradₓ, gradient]
        rw [hev.fderiv_eq, fderiv_sub_const]
      rw [gradₓ_mul (F := fun q ↦ max (u q - δ) 0) hFd (differentiableAt_slice hη p), hgF,
        inner_add_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq,
        max_eq_left (by linarith)]
    · have : gradₓ u p = 0 := by
        simp only [gradₓ, gradient]
        rw [fderiv_zero_of_not_differentiableAt hd, map_zero]
      simp [this]
  · have hmin : IsLocalMin (fun y ↦ max (u (y, p.2) - δ) 0 * η (y, p.2)) p.1 :=
      Eventually.of_forall fun y ↦ by
        change max (u (p.1, p.2) - δ) 0 * η (p.1, p.2) ≤ _
        rw [Prod.mk.eta, max_eq_right (by linarith : u p - δ ≤ 0), zero_mul]
        exact mul_nonneg (le_max_right _ _) (hη0 _)
    rw [gradₓ_eq_zero_of_isLocalMin (φ := fun q ↦ max (u q - δ) 0 * η q) hmin, inner_zero_right]

/-! ### Lemma 4.2 -/

/-- **Lemma 4.2**: strong `L²_loc(U_∞)` convergence of the spatial
gradients. Let `v_n ≥ 0` be classical solutions of (3.4) with `ε_n → 0⁺`, converging locally
uniformly on `U_∞` to `u` (continuous, locally Lipschitz in space), with `∇v_n ⇀ ∇u` weakly in
`L²(U × (0, T))` for all `T`, uniformly bounded slice energies `∫_U |∇v_n(·, t)|² ≤ E₀`, and
`∂ₜv_n ⇀ w` weakly in `L²(U_∞)` with `‖∂ₜv_n‖_{L²(U_∞)} ≤ B`. Then `∇v_n → ∇u` in `L²_loc(U_∞)`
(along the whole sequence).

Proof: (4.3)–(4.6) of the paper, see the module docstring. The time chain rule for `u` used in
the paper's derivation of (4.4) is avoided: `∫ w u η = -∫ (u²/2) ∂ₜη` is obtained as the limit of
the classical identity for `v_n`. -/
theorem tendstoLpLoc_gradₓ_semilinear (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    {v : ℕ → E d × ℝ → ℝ} {u w : E d × ℝ → ℝ}
    (hv : ∀ n, IsSemilinearSolOn S.U S.Q β (ε n) (Ioi 0) (v n))
    (hv0 : ∀ n, ∀ p ∈ UInf S.U, 0 ≤ v n p)
    (hconv : TendstoLocallyUniformlyOn v u atTop (UInf S.U)) (hucont : ContinuousOn u (UInf S.U))
    (hulip : LocLipₓ (UInf S.U) u)
    (hgrad : ∀ T > 0, TendstoWeakL2 volume (S.U ×ˢ Ioo 0 T) (fun n ↦ gradₓ (v n)) (gradₓ u)
      atTop)
    {E0 : ℝ≥0∞} (hE0 : E0 ≠ ⊤)
    (hslice : ∀ n, ∀ t > 0, ∫⁻ x in S.U, ENNReal.ofReal (‖gradₓ (v n) (x, t)‖ ^ 2) ≤ E0)
    (hw : TendstoWeakL2 volume (UInf S.U) (fun n ↦ dₜ (v n)) w atTop) {B : ℝ} (hB0 : 0 ≤ B)
    (hdtB : ∀ n, eLpNorm (dₜ (v n)) 2 (volume.restrict (UInf S.U)) ≤ ENNReal.ofReal B) :
    TendstoLpLoc 2 volume (UInf S.U) (fun n ↦ gradₓ (v n)) (gradₓ u) atTop := by
  intro K hKΩ hK
  have hU := S.isOpen
  set Ω := UInf S.U with hΩdef
  have hΩ : IsOpen Ω := hU.prod isOpen_Ioi
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  obtain ⟨η, hη, hηc, hηs, hη01, hη1⟩ := exists_cutoff hK hΩ hKΩ
  have hη0 : ∀ p, 0 ≤ η p := fun p ↦ (hη01 p).1
  set L := tsupport η with hLdef
  have hL : IsCompact L := hηc
  have hLm : MeasurableSet L := (isClosed_tsupport η).measurableSet
  have : IsFiniteMeasure (volume.restrict L) := isFiniteMeasure_restrict.2 hL.measure_lt_top.ne
  obtain ⟨T, hT, hLT⟩ := exists_subset_prod_Ioo hL hηs
  have hUTm : MeasurableSet (S.U ×ˢ Ioo (0 : ℝ) T) := hU.measurableSet.prod measurableSet_Ioo
  have hUTΩ : S.U ×ˢ Ioo (0 : ℝ) T ⊆ Ω := prod_mono le_rfl Ioo_subset_Ioi_self
  have hη0' : ∀ p ∉ L, η p = 0 := fun p hp ↦ image_eq_zero_of_notMem_tsupport hp
  have hgη0 : ∀ p ∉ L, gradₓ η p = 0 := fun p hp ↦ gradₓ_eq_zero_of_notMem hp
  have hdη0 : ∀ p ∉ L, dₜ η p = 0 := fun p hp ↦ dₜ_eq_zero_of_notMem hη hp
  -- bounds on `L`
  have hu0 : ∀ p ∈ Ω, 0 ≤ u p := fun p hp ↦
    ge_of_tendsto' (hconv.tendsto_at hp) fun n ↦ hv0 n p hp
  have hunif : TendstoUniformlyOn v u atTop L :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).1 hconv L hηs hL
  obtain ⟨Bu, hBu0, hBu⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ L, 0 ≤ u p ∧ u p ≤ C := by
    obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn (hucont.mono hηs)
    refine ⟨max C 0, le_max_right _ _, fun p hp ↦ ⟨hu0 p (hηs hp), ?_⟩⟩
    have h := hC p hp
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_max_left _ _))
  obtain ⟨Gu, hGu0, hGu⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ L, ‖gradₓ u p‖ ≤ C := by
    obtain ⟨C, hC⟩ := exists_bound_gradₓ_of_locLipₓ hL hηs hulip
    exact ⟨max C 0, le_max_right _ _, fun p hp ↦ (hC p hp).trans (le_max_left _ _)⟩
  obtain ⟨Cg, hCg0, hCg⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ L, ‖gradₓ η p‖ ≤ C := by
    obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn (continuous_gradₓ hη).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun p hp ↦ (hC p hp).trans (le_max_left _ _)⟩
  obtain ⟨Cd, hCd⟩ := hL.exists_bound_of_continuousOn (continuous_dₜ hη).continuousOn
  have hvb : ∀ᶠ n in atTop, ∀ p ∈ L, |v n p| ≤ Bu + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif 1 one_pos] with n hn p hp
    have h1 := hn p hp
    rw [Real.dist_eq, abs_sub_comm] at h1
    have := abs_sub_abs_le_abs_sub (v n p) (u p)
    have := hBu p hp
    rw [abs_of_nonneg this.1] at *
    linarith
  have hsmall : ∀ δ > 0, ∀ᶠ n in atTop, ∀ p ∈ L, |v n p - u p| ≤ δ := fun δ hδ ↦ by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif δ hδ] with n hn p hp
    have h1 := hn p hp
    rw [Real.dist_eq, abs_sub_comm] at h1
    exact h1.le
  have hgum : AEStronglyMeasurable (gradₓ u) (volume.restrict Ω) :=
    (locallyIntegrableOn_gradₓ hΩ hucont hulip).aestronglyMeasurable
  have huam : AEStronglyMeasurable u (volume.restrict Ω) := hucont.aestronglyMeasurable hΩm
  have hgvm : ∀ n, AEStronglyMeasurable (gradₓ (v n)) (volume.restrict Ω) := fun n ↦
    (hv n).2.2.1.aestronglyMeasurable hΩm
  have hLΩ : volume.restrict L ≤ volume.restrict Ω := Measure.restrict_mono hηs le_rfl
  have hηm : AEStronglyMeasurable η (volume.restrict Ω) := hη.continuous.aestronglyMeasurable
  have hgηm : AEStronglyMeasurable (gradₓ η) (volume.restrict Ω) :=
    (continuous_gradₓ hη).aestronglyMeasurable
  -- Step 1: the right-hand side of the `ε`-level energy inequality converges
  have T1 : Tendsto (fun n ↦ ∫ p in Ω, v n p ^ 2 / 2 * dₜ η p) atTop
      (𝓝 (∫ p in Ω, u p ^ 2 / 2 * dₜ η p)) := by
    refine tendsto_setIntegral_of_dominated_compact hΩm hL hηs
      (fun n p hp ↦ by simp [hdη0 p hp]) (fun p hp ↦ by simp [hdη0 p hp])
      (fun n ↦ (((((hv n).1.mono hηs).pow 2).div_const 2).mul
        (continuous_dₜ hη).continuousOn).aestronglyMeasurable hLm)
      (g := fun _ ↦ (Bu + 1) ^ 2 / 2 * Cd) (integrable_const _) ?_
      fun p hp ↦ (((hconv.tendsto_at (hηs hp)).pow 2).div_const 2).mul_const _
    filter_upwards [hvb] with n hn p hp
    have h1 := hn p hp
    have h2 := hCd p hp
    rw [Real.norm_eq_abs] at h2
    calc |v n p ^ 2 / 2 * dₜ η p| = |v n p| ^ 2 / 2 * |dₜ η p| := by
          rw [abs_mul, abs_div, abs_pow, abs_two]
      _ ≤ (Bu + 1) ^ 2 / 2 * Cd := by gcongr
  have hred : ∀ G : E d × ℝ → ℝ, (∀ p ∉ L, G p = 0) →
      ∫ p in Ω, G p = ∫ p in S.U ×ˢ Ioo 0 T, G p := fun G hG ↦
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩm hUTΩ fun p hp ↦
      hG p fun h ↦ hp.2 (hLT h)
  have hgw := hgrad T hT
  have hBv : ∀ n, eLpNorm (gradₓ (v n)) 2 (volume.restrict (S.U ×ˢ Ioo 0 T)) ≤
      ENNReal.ofReal (Real.sqrt (E0 * volume (Ioo (0 : ℝ) T)).toReal) := fun n ↦
    eLpNorm_prod_le_of_slices measurableSet_Ioo (by simp [Real.volume_Ioo])
      ((hgvm n).mono_measure (Measure.restrict_mono hUTΩ le_rfl)) hE0
      fun t ht ↦ hslice n t ht.1
  have hsmem : ∀ f : E d × ℝ → ℝ, ContinuousOn f Ω →
      MemLp (fun p ↦ f p • gradₓ η p) 2 (volume.restrict (S.U ×ˢ Ioo 0 T)) := fun f hf ↦ by
    obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn
      ((hf.mono hηs).smul (continuous_gradₓ hη).continuousOn)
    exact memLp_two_of_bound_of_compact hL (((hf.mono hUTΩ).smul
      (continuous_gradₓ hη).continuousOn).aestronglyMeasurable hUTm) C hC
      fun p hp ↦ by simp [hgη0 p hp]
  have hbc : Tendsto (fun n ↦ eLpNorm ((fun p ↦ v n p • gradₓ η p) - fun p ↦ u p • gradₓ η p)
      2 (volume.restrict (S.U ×ˢ Ioo 0 T))) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_of_uniform hL (fun n p hp ↦ by simp [hgη0 p hp])
      (fun n ↦ ((hsmem _ (hv n).1).sub (hsmem u hucont)).aestronglyMeasurable) fun δ hδ ↦ ?_
    filter_upwards [hsmall (δ / (Cg + 1)) (by positivity)] with n hn p hp
    simp only [Pi.sub_apply, ← sub_smul, norm_smul, Real.norm_eq_abs]
    calc |v n p - u p| * ‖gradₓ η p‖ ≤ δ / (Cg + 1) * (Cg + 1) := by
          gcongr
          · exact hn p hp
          · exact (hCg p hp).trans (by linarith)
      _ = δ := by field_simp
  have T2 : Tendsto (fun n ↦ ∫ p in Ω, v n p * ⟪gradₓ (v n) p, gradₓ η p⟫) atTop
      (𝓝 (∫ p in Ω, u p * ⟪gradₓ u p, gradₓ η p⟫)) := by
    have h := tendsto_integral_inner_of_weak_strong (μ := volume.restrict (S.U ×ˢ Ioo 0 T))
      (b := fun n p ↦ v n p • gradₓ η p) hgw.1 _ (Real.sqrt_nonneg _) hBv
      (hgw.2.2 _ (hsmem u hucont)) (fun n ↦ hsmem _ (hv n).1) (hsmem u hucont) hbc
    have e : ∀ (f : E d × ℝ → ℝ) (G : E d × ℝ → E d), ∫ p in Ω, f p * ⟪G p, gradₓ η p⟫ =
        ∫ p in S.U ×ˢ Ioo 0 T, ⟪G p, f p • gradₓ η p⟫ := fun f G ↦ by
      rw [hred _ fun p hp ↦ by simp [hgη0 p hp]]
      congr 1
      ext p
      rw [inner_smul_right]
    simp only [e]
    exact h
  -- Step 2: the time identity `∫ w u η = -∫ (u²/2) ∂ₜη`
  have hηmem : ∀ f : E d × ℝ → ℝ, ContinuousOn f Ω →
      MemLp (fun p ↦ f p * η p) 2 (volume.restrict Ω) := fun f hf ↦ by
    obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn
      ((hf.mono hηs).mul hη.continuous.continuousOn)
    exact memLp_two_of_bound_of_compact hL
      ((hf.mul hη.continuous.continuousOn).aestronglyMeasurable hΩm) C hC
      fun p hp ↦ by simp [hη0' p hp]
  have hbc' : Tendsto (fun n ↦ eLpNorm ((fun p ↦ v n p * η p) - fun p ↦ u p * η p) 2
      (volume.restrict Ω)) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_of_uniform hL (fun n p hp ↦ by simp [hη0' p hp])
      (fun n ↦ ((hηmem _ (hv n).1).sub (hηmem u hucont)).aestronglyMeasurable) fun δ hδ ↦ ?_
    filter_upwards [hsmall δ hδ] with n hn p hp
    simp only [Pi.sub_apply, ← sub_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hη0 p)]
    calc |v n p - u p| * η p ≤ δ * 1 := mul_le_mul (hn p hp) (hη01 p).2 (hη0 p) hδ.le
      _ = δ := mul_one δ
  have e : ∀ a b : ℝ, inner ℝ a b = a * b := fun a b ↦ by simp [RCLike.inner_apply, mul_comm]
  have T3 : Tendsto (fun n ↦ ∫ p in Ω, dₜ (v n) p * (v n p * η p)) atTop
      (𝓝 (∫ p in Ω, w p * (u p * η p))) := by
    have h := tendsto_integral_inner_of_weak_strong (μ := volume.restrict Ω)
      (a := fun n ↦ dₜ (v n)) (b := fun n p ↦ v n p * η p) hw.1 B hB0 hdtB
      (hw.2.2 _ (hηmem u hucont)) (fun n ↦ hηmem _ (hv n).1) (hηmem u hucont) hbc'
    simp only [e] at h
    exact h
  have htimeId : ∫ p in Ω, w p * (u p * η p) = -∫ p in Ω, u p ^ 2 / 2 * dₜ η p :=
    tendsto_nhds_unique T3 (T1.neg.congr fun n ↦ (integral_dₜ_mul_self hU (hv n) hη hηc hηs).symm)
  -- Step 3: the weak heat equation tested with `(u - δ)₊ η`
  have hRgrad : ∀ φ : E d × ℝ → ℝ, IsSliceLipTest φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      Tendsto (fun n ↦ ∫ p in Ω, ⟪gradₓ (v n) p, gradₓ φ p⟫) atTop
        (𝓝 (∫ p in Ω, ⟪gradₓ u p, gradₓ φ p⟫)) := by
    intro φ hφ hφc hφs
    obtain ⟨hφcont, -, Kφ, hKφ⟩ := hφ
    exact tendsto_setIntegral_inner_of_weak hU hgrad hφc hφs
      (measurable_gradₓ hφcont).aestronglyMeasurable Kφ (fun p _ ↦ hKφ p)
      fun p hp ↦ gradₓ_eq_zero_of_notMem hp
  have hFc : ∀ δ : ℝ, ContinuousOn (fun p ↦ max (u p - δ) 0) Ω := fun δ ↦
    (hucont.sub continuousOn_const).sup continuousOn_const
  have hwh : ∀ δ > 0, ∫ p in Ω, w p * (max (u p - δ) 0 * η p) =
      -∫ p in Ω, ⟪gradₓ u p, gradₓ (fun q ↦ max (u q - δ) 0 * η q) p⟫ := by
    intro δ hδ
    refine weakHeat_of_tendsto_of_grad hU hβ hε hε0 hv hconv hRgrad hw
      (fun q ↦ max (u q - δ) 0 * η q)
      (isSliceLipTest_mul hΩ (hFc δ) (hulip.posPart_sub δ) hη hηc hηs) hηc.mul_left ?_
    intro p hp
    have hpL : p ∈ L := tsupport_mul_subset_right hp
    refine ⟨hηs hpL, ?_⟩
    by_contra hle
    push Not at hle
    have hev : (fun q ↦ max (u q - δ) 0 * η q) =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hucont.continuousAt (hΩ.mem_nhds (hηs hpL))).eventually
        (gt_mem_nhds (show u p < δ by linarith))] with q hq
      simp [max_eq_right (show u q - δ ≤ 0 by linarith)]
    exact (notMem_tsupport_iff_eventuallyEq.2 hev) hp
  -- Step 3': `δ → 0`
  set δs : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hδs
  have hδpos : ∀ k, 0 < δs k := fun k ↦ by positivity
  have hδ0 : Tendsto δs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hwL : IntegrableOn w L := by
    have h := hw.2.1.restrict L
    rw [Measure.restrict_restrict_of_subset hηs] at h
    exact h.integrable one_le_two
  have L1 : Tendsto (fun k ↦ ∫ p in Ω, w p * (max (u p - δs k) 0 * η p)) atTop
      (𝓝 (∫ p in Ω, w p * (u p * η p))) := by
    refine tendsto_setIntegral_of_dominated_compact hΩm hL hηs
      (fun k p hp ↦ by simp [hη0' p hp]) (fun p hp ↦ by simp [hη0' p hp])
      (fun k ↦ hwL.aestronglyMeasurable.mul
        ((((hFc _).mono hηs).mul hη.continuous.continuousOn).aestronglyMeasurable hLm))
      (g := fun p ↦ ‖w p‖ * Bu) (hwL.norm.mul_const Bu) (Eventually.of_forall fun k p hp ↦ ?_)
      fun p hp ↦ ?_
    · rw [abs_mul, ← Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h := hBu p hp
      rw [abs_of_nonneg (mul_nonneg (le_max_right _ _) (hη0 p))]
      calc max (u p - δs k) 0 * η p ≤ u p * 1 :=
            mul_le_mul (max_le (by linarith [hδpos k]) h.1) (hη01 p).2 (hη0 p) h.1
        _ ≤ Bu := by linarith [h.2]
    · have h := ((tendsto_const_nhds (x := u p)).sub hδ0).max
        (tendsto_const_nhds (x := (0 : ℝ)))
      rw [sub_zero, max_eq_left (hu0 p (hηs hp))] at h
      exact tendsto_const_nhds.mul (h.mul_const (η p))
  have hpt : ∀ k p, ⟪gradₓ u p, gradₓ (fun q ↦ max (u q - δs k) 0 * η q) p⟫ =
      if δs k < u p then η p * ‖gradₓ u p‖ ^ 2 + (u p - δs k) * ⟪gradₓ u p, gradₓ η p⟫
      else 0 := fun k p ↦ inner_gradₓ_posPart_mul hη hη0 _ p
  have R1 : Tendsto (fun k ↦ ∫ p in Ω, ⟪gradₓ u p, gradₓ (fun q ↦ max (u q - δs k) 0 * η q) p⟫)
      atTop (𝓝 (∫ p in Ω, (η p * ‖gradₓ u p‖ ^ 2 + u p * ⟪gradₓ u p, gradₓ η p⟫))) := by
    refine tendsto_setIntegral_of_dominated_compact hΩm hL hηs
      (fun k p hp ↦ by rw [hpt]; simp [hη0' p hp, hgη0 p hp])
      (fun p hp ↦ by simp [hη0' p hp, hgη0 p hp])
      (fun k ↦ (hgum.mono_measure hLΩ).inner (measurable_gradₓ
        (continuous_mul_of_tsupport_subset hΩ (hFc _) hη.continuous hηs)).aestronglyMeasurable)
      (g := fun _ ↦ Gu ^ 2 + Bu * Gu * Cg) (integrable_const _)
      (Eventually.of_forall fun k p hp ↦ ?_) fun p hp ↦ ?_
    · rw [hpt]
      split_ifs with hk
      · have hg := hGu p hp
        have hc := hCg p hp
        have hu := hBu p hp
        have h1 : |η p * ‖gradₓ u p‖ ^ 2| ≤ Gu ^ 2 := by
          rw [abs_of_nonneg (mul_nonneg (hη0 p) (sq_nonneg _))]
          calc η p * ‖gradₓ u p‖ ^ 2 ≤ 1 * Gu ^ 2 :=
                mul_le_mul (hη01 p).2 (pow_le_pow_left₀ (norm_nonneg _) hg 2)
                  (sq_nonneg _) zero_le_one
            _ = Gu ^ 2 := one_mul _
        have h2 : |(u p - δs k) * ⟪gradₓ u p, gradₓ η p⟫| ≤ Bu * Gu * Cg := by
          rw [abs_mul, abs_of_pos (by linarith), mul_assoc]
          exact mul_le_mul (by linarith [hδpos k]) ((abs_real_inner_le_norm _ _).trans
            (mul_le_mul hg hc (norm_nonneg _) hGu0)) (abs_nonneg _) hBu0
        exact (abs_add_le _ _).trans (add_le_add h1 h2)
      · rw [abs_zero]
        exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hBu0 hGu0) hCg0)
    · by_cases hup : 0 < u p
      · have hev : ∀ᶠ k in atTop,
            ⟪gradₓ u p, gradₓ (fun q ↦ max (u q - δs k) 0 * η q) p⟫ =
              η p * ‖gradₓ u p‖ ^ 2 + (u p - δs k) * ⟪gradₓ u p, gradₓ η p⟫ := by
          filter_upwards [hδ0.eventually (gt_mem_nhds hup)] with k hk
          rw [hpt, ite_eq_left hk]
        refine (tendsto_congr' hev).2 ?_
        have h := tendsto_const_nhds (x := η p * ‖gradₓ u p‖ ^ 2) |>.add
          (((tendsto_const_nhds (x := u p)).sub hδ0).mul_const ⟪gradₓ u p, gradₓ η p⟫)
        rwa [sub_zero] at h
      · have hu0' : u p = 0 := le_antisymm (not_lt.1 hup) (hu0 p (hηs hp))
        have hg0 := gradₓ_eq_zero_of_nonneg hΩ hu0 (hηs hp) hu0'
        simp only [hg0, inner_zero_left, hu0', norm_zero]
        simp
  have hF₀id : ∫ p in Ω, w p * (u p * η p) =
      -∫ p in Ω, (η p * ‖gradₓ u p‖ ^ 2 + u p * ⟪gradₓ u p, gradₓ η p⟫) :=
    tendsto_nhds_unique L1 (R1.neg.congr fun k ↦ (hwh _ (hδpos k)).symm)
  have iD : Integrable (fun p ↦ η p * ‖gradₓ u p‖ ^ 2) (volume.restrict Ω) := by
    refine integrable_of_bound_of_compact hL (hηm.mul (hgum.norm.pow 2)) (Gu ^ 2)
      (fun p hp ↦ ?_) fun p hp ↦ by simp [hη0' p hp]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hη0 p) (sq_nonneg _))]
    calc η p * ‖gradₓ u p‖ ^ 2 ≤ 1 * Gu ^ 2 :=
          mul_le_mul (hη01 p).2 (pow_le_pow_left₀ (norm_nonneg _) (hGu p hp) 2)
            (sq_nonneg _) zero_le_one
      _ = Gu ^ 2 := one_mul _
  have iJ : Integrable (fun p ↦ u p * ⟪gradₓ u p, gradₓ η p⟫) (volume.restrict Ω) := by
    refine integrable_of_bound_of_compact hL (huam.mul (hgum.inner hgηm)) (Bu * (Gu * Cg))
      (fun p hp ↦ ?_) fun p hp ↦ by simp [hgη0 p hp]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hBu p hp).1]
    exact mul_le_mul (hBu p hp).2 ((norm_inner_le_norm _ _).trans
      (mul_le_mul (hGu p hp) (hCg p hp) (norm_nonneg _) hGu0)) (norm_nonneg _) hBu0
  have hR0 : (∫ p in Ω, u p ^ 2 / 2 * dₜ η p) - ∫ p in Ω, u p * ⟪gradₓ u p, gradₓ η p⟫ =
      ∫ p in Ω, η p * ‖gradₓ u p‖ ^ 2 := by
    have h1 : ∫ p in Ω, (η p * ‖gradₓ u p‖ ^ 2 + u p * ⟪gradₓ u p, gradₓ η p⟫) =
        (∫ p in Ω, η p * ‖gradₓ u p‖ ^ 2) + ∫ p in Ω, u p * ⟪gradₓ u p, gradₓ η p⟫ :=
      integral_add iD iJ
    linarith
  -- Step 4: `∫ η |∇v_n - ∇u|² → 0`
  have hC : Tendsto (fun n ↦ ∫ p in Ω, ⟪gradₓ (v n) p, η p • gradₓ u p⟫) atTop
      (𝓝 (∫ p in Ω, η p * ‖gradₓ u p‖ ^ 2)) := by
    have h := tendsto_setIntegral_inner_of_weak hU hgrad hL hηs (G := fun p ↦ η p • gradₓ u p)
      (hηm.smul hgum) Gu (fun p hp ↦ ?_) fun p hp ↦ by simp [hη0' p hp]
    · have e2 : ∫ p in Ω, ⟪gradₓ u p, η p • gradₓ u p⟫ = ∫ p in Ω, η p * ‖gradₓ u p‖ ^ 2 := by
        congr 1
        ext p
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
      rwa [e2] at h
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη0 p)]
      calc η p * ‖gradₓ u p‖ ≤ 1 * Gu := mul_le_mul (hη01 p).2 (hGu p hp) (norm_nonneg _)
            zero_le_one
        _ = Gu := one_mul _
  have hvbd : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ L, ‖gradₓ (v n) p‖ ≤ C := fun n ↦ by
    obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn ((hv n).2.2.1.mono hηs)
    exact ⟨max C 0, le_max_right _ _, fun p hp ↦ (hC p hp).trans (le_max_left _ _)⟩
  have iA : ∀ n, Integrable (fun p ↦ η p * ‖gradₓ (v n) p‖ ^ 2) (volume.restrict Ω) := by
    intro n
    obtain ⟨C, -, hC⟩ := hvbd n
    refine integrable_of_bound_of_compact hL (hηm.mul ((hgvm n).norm.pow 2)) (C ^ 2)
      (fun p hp ↦ ?_) fun p hp ↦ by simp [hη0' p hp]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hη0 p) (sq_nonneg _))]
    calc η p * ‖gradₓ (v n) p‖ ^ 2 ≤ 1 * C ^ 2 :=
          mul_le_mul (hη01 p).2 (pow_le_pow_left₀ (norm_nonneg _) (hC p hp) 2)
            (sq_nonneg _) zero_le_one
      _ = C ^ 2 := one_mul _
  have iC : ∀ n, Integrable (fun p ↦ ⟪gradₓ (v n) p, η p • gradₓ u p⟫) (volume.restrict Ω) := by
    intro n
    obtain ⟨C, hC0, hC⟩ := hvbd n
    refine integrable_of_bound_of_compact hL ((hgvm n).inner (hηm.smul hgum)) (C * Gu)
      (fun p hp ↦ ?_) fun p hp ↦ by simp [hη0' p hp]
    refine (norm_inner_le_norm _ _).trans (mul_le_mul (hC p hp) ?_ (norm_nonneg _) hC0)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη0 p)]
    calc η p * ‖gradₓ u p‖ ≤ 1 * Gu := mul_le_mul (hη01 p).2 (hGu p hp) (norm_nonneg _)
          zero_le_one
      _ = Gu := one_mul _
  have hpw : ∀ n p, η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2 =
      η p * ‖gradₓ (v n) p‖ ^ 2 - 2 * ⟪gradₓ (v n) p, η p • gradₓ u p⟫ +
        η p * ‖gradₓ u p‖ ^ 2 := fun n p ↦ by
    rw [norm_sub_sq_real, inner_smul_right]
    ring
  have iI : ∀ n, Integrable (fun p ↦ η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2)
      (volume.restrict Ω) := fun n ↦
    (((iA n).sub ((iC n).const_mul 2)).add iD).congr
      (ae_of_all _ fun p ↦ (hpw n p).symm)
  have hIeq : ∀ n, ∫ p in Ω, η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2 =
      (∫ p in Ω, η p * ‖gradₓ (v n) p‖ ^ 2) -
        2 * (∫ p in Ω, ⟪gradₓ (v n) p, η p • gradₓ u p⟫) + ∫ p in Ω, η p * ‖gradₓ u p‖ ^ 2 := by
    intro n
    simp only [hpw]
    have h1 : Integrable (fun p ↦ η p * ‖gradₓ (v n) p‖ ^ 2 -
        2 * ⟪gradₓ (v n) p, η p • gradₓ u p⟫) (volume.restrict Ω) :=
      (iA n).sub ((iC n).const_mul 2)
    rw [integral_add h1 iD,
      integral_sub (iA n) ((iC n).const_mul 2), integral_const_mul]
  have hI0 : ∀ n, 0 ≤ ∫ p in Ω, η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2 := fun n ↦
    integral_nonneg fun p ↦ mul_nonneg (hη0 p) (sq_nonneg _)
  have hIle : ∀ n, ∫ p in Ω, η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2 ≤
      ((∫ p in Ω, v n p ^ 2 / 2 * dₜ η p) - ∫ p in Ω, v n p * ⟪gradₓ (v n) p, gradₓ η p⟫) -
        2 * (∫ p in Ω, ⟪gradₓ (v n) p, η p • gradₓ u p⟫) + ∫ p in Ω, η p * ‖gradₓ u p‖ ^ 2 := by
    intro n
    rw [hIeq]
    have := energy_ineq_semilinear S hβ (hε n) (hv n) (hv0 n) hη hηc hηs hη0
    linarith
  have hlim := ((T1.sub T2).sub (hC.const_mul 2)).add_const (∫ p in Ω, η p * ‖gradₓ u p‖ ^ 2)
  rw [hR0, show ∀ D : ℝ, D - 2 * D + D = 0 from fun D ↦ by ring] at hlim
  have hI : Tendsto (fun n ↦ ∫ p in Ω, η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero hI0 hIle hlim
  -- conclusion: `‖∇v_n - ∇u‖²_{L²(K)} ≤ ∫ η |∇v_n - ∇u|²`
  have hle : ∀ n, eLpNorm (gradₓ (v n) - gradₓ u) 2 (volume.restrict K) ≤
      ENNReal.ofReal (Real.sqrt (∫ p in Ω, η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2)) := by
    intro n
    rw [← ENNReal.pow_le_pow_left_iff two_ne_zero,
      eLpNorm_two_sq _ (((hgvm n).sub hgum).mono_measure (Measure.restrict_mono hKΩ le_rfl)),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hI0 n),
      ofReal_integral_eq_lintegral_ofReal (iI n)
        (ae_of_all _ fun p ↦ mul_nonneg (hη0 p) (sq_nonneg _))]
    calc ∫⁻ p in K, ENNReal.ofReal (‖(gradₓ (v n) - gradₓ u) p‖ ^ 2)
        = ∫⁻ p in K, ENNReal.ofReal (η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2) :=
          setLIntegral_congr_fun hKm fun p hp ↦ by rw [hη1 p hp, one_mul, Pi.sub_apply]
      _ ≤ ∫⁻ p in Ω, ENNReal.ofReal (η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2) :=
          lintegral_mono_set hKΩ
  have hsq : Tendsto (fun n ↦ ENNReal.ofReal
      (Real.sqrt (∫ p in Ω, η p * ‖gradₓ (v n) p - gradₓ u p‖ ^ 2))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal ((Real.continuous_sqrt.tendsto 0).comp hI)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq (fun _ ↦ zero_le) hle

end Inner

end PerronVariational

end
