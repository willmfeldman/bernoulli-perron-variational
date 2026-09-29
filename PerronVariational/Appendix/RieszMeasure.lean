/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Appendix.CircleMean
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Order.CompletePartialOrder
import PerronVariational.Appendix.PlanarGreen

/-!
# Existence of the Riesz measure (Appendix B)

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper"). The
proof of Lemma B.3 in Appendix B of the paper uses without proof that `Δu` is a non-negative (Riesz)
measure, together with the derivative formula for spherical means. Here we prove it in the plane.

Let `Ω ⊆ ℝ²` be open and `u ≥ 0` continuous on `Ω`, `C²` and harmonic in `{u > 0}`. We construct
the Riesz measure `μ = Δu` of `u` on `Ω` and prove the Riesz–Jensen formula of `IsRieszMeasure`
(`exists_isRieszMeasure`).

Route.
1. *Smooth approximations.* `w_δ = G_δ ∘ u`, where `G_δ` is smooth and convex, vanishes on
   `(-∞, δ]` and satisfies `|G_δ(t) - t| ≤ 2δ` for `t ≥ 0`. Then `w_δ` is `C²` on `Ω` and
   `Δw_δ = G_δ''(u) |∇u|² ≥ 0` (`laplacian_cutG_comp_nonneg`).
2. *Smooth Riesz–Jensen formula* (`integral_ball_laplacian_div_E2`, from `PlanarGreen`):
   `∫_a^R (∫_{B_s} Δw) / s ds = 2π (⨍_{∂B_R} w - ⨍_{∂B_a} w)`.
3. *Layer cake* (`lintegral_logCut`): for the test function
   `ψ = (log (R / max(a, |y - x|)))₊`, `∫ ψ dν = ∫_a^R ν(B_s) / s ds` for every measure `ν`.
4. *Limit functional.* `Λ_n φ = ∫_Ω φ Δw_{δ_n}` are positive functionals on `C_c(Ω)`, bounded
   for each `φ` uniformly in `n` (by 2, 3 and a finite covering). Their limit along an
   ultrafilter is a positive linear functional `Λ`; no density argument is needed.
   Riesz–Markov–Kakutani gives the measure `μ`.
5. *Riesz–Jensen formula for `μ`.* By 2 and 3, `∫_a^R μ(B_s)/s ds = 2π (⨍_{∂B_R} u - ⨍_{∂B_a} u)`;
   let `a → 0`.
-/

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Laplacian Real ENNReal

@[expose] public section

namespace PerronVariational

namespace RieszMeasure

/-! ### Green's identity on discs in `E 2` -/

theorem measurePreserving_toE2 : MeasurePreserving toE2 volume volume :=
  Complex.orthonormalBasisOneI.measurePreserving_repr

theorem preimage_toE2_ball (x : E 2) (s : ℝ) : toE2 ⁻¹' ball x s = ball (toE2.symm x) s := by
  ext z
  simp only [mem_preimage, mem_ball]
  rw [← LinearIsometryEquiv.dist_map toE2.symm, LinearIsometryEquiv.symm_apply_apply]

theorem integral_ball_laplacian_eq (w : E 2 → ℝ) (x : E 2) (s : ℝ) :
    ∫ y in ball x s, Δ w y = ∫ z in ball (toE2.symm x) s, Δ (w ∘ toE2) z := by
  simp_rw [laplacian_comp_toE2]
  rw [← preimage_toE2_ball]
  exact (measurePreserving_toE2.setIntegral_preimage_emb
    toE2.toHomeomorph.measurableEmbedding _ _).symm

/-- **Smooth Riesz–Jensen formula** in `E 2`. -/
theorem integral_ball_laplacian_div_E2 {w : E 2 → ℝ} {V : Set (E 2)} (hV : IsOpen V)
    (hw : ContDiffOn ℝ 2 w V) {x : E 2} {a R : ℝ} (ha : 0 < a) (haR : a ≤ R)
    (hsub : closedBall x R ⊆ V) :
    ∫ s in a..R, (∫ y in ball x s, Δ w y) / s =
      2 * π * (circleMean w x R - circleMean w x a) := by
  have hU : IsOpen (toE2 ⁻¹' V) := hV.preimage toE2.continuous
  have hv : ContDiffOn ℝ 2 (w ∘ toE2) (toE2 ⁻¹' V) :=
    hw.comp toE2.contDiff.contDiffOn (mapsTo_preimage _ _)
  have hsub' : closedBall (toE2.symm x) R ⊆ toE2 ⁻¹' V := by
    intro z hz
    apply hsub
    rw [mem_closedBall, ← LinearIsometryEquiv.dist_map toE2.symm,
      LinearIsometryEquiv.symm_apply_apply]
    exact hz
  simp_rw [integral_ball_laplacian_eq]
  exact PlanarGreen.integral_integral_ball_laplacian_div hU hv ha haR hsub'

/-! ### The convex cut-offs `G_δ` -/

/-- `G_δ(t) = ∫_0^t S((τ - δ)/δ) dτ`, `S` the smooth transition. -/
noncomputable def cutG (δ t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, Real.smoothTransition ((τ - δ) / δ)

theorem continuous_cutG_deriv (δ : ℝ) :
    Continuous fun τ : ℝ ↦ Real.smoothTransition ((τ - δ) / δ) :=
  Real.smoothTransition.continuous.comp (by fun_prop)

theorem hasDerivAt_cutG (δ t : ℝ) :
    HasDerivAt (cutG δ) (Real.smoothTransition ((t - δ) / δ)) t :=
  ((continuous_cutG_deriv δ).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem deriv_cutG (δ : ℝ) :
    deriv (cutG δ) = fun t ↦ Real.smoothTransition ((t - δ) / δ) :=
  funext fun t ↦ (hasDerivAt_cutG δ t).deriv

theorem contDiff_cutG (δ : ℝ) : ContDiff ℝ 2 (cutG δ) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv, deriv_cutG]
  refine ⟨fun t ↦ (hasDerivAt_cutG δ t).differentiableAt, by simp, ?_⟩
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem cutG_eq_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) : cutG δ t = 0 := by
  unfold cutG
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)), intervalIntegral.integral_zero]
  intro τ hτ
  refine Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ?_ hδ.le)
  have : τ ≤ max 0 t := by
    rcases le_total 0 t with h | h
    · rw [uIcc_of_le h] at hτ; exact hτ.2.trans (le_max_right _ _)
    · rw [uIcc_of_ge h] at hτ; exact hτ.2.trans (le_max_left _ _)
  have : max 0 t ≤ δ := max_le hδ.le ht
  linarith

theorem cutG_le {δ t : ℝ} (ht : 0 ≤ t) : cutG δ t ≤ t := by
  unfold cutG
  calc _ ≤ ∫ _ in (0 : ℝ)..t, (1 : ℝ) :=
        intervalIntegral.integral_mono_on ht ((continuous_cutG_deriv δ).intervalIntegrable _ _)
          intervalIntegrable_const fun _ _ ↦ Real.smoothTransition.le_one _
    _ = t := by simp

theorem cutG_nonneg {δ t : ℝ} (ht : 0 ≤ t) : 0 ≤ cutG δ t :=
  intervalIntegral.integral_nonneg ht fun _ _ ↦ Real.smoothTransition.nonneg _

theorem sub_le_cutG {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) : t - 2 * δ ≤ cutG δ t := by
  rcases le_total t (2 * δ) with h | h
  · linarith [cutG_nonneg (δ := δ) ht]
  · unfold cutG
    have hi := (continuous_cutG_deriv δ).intervalIntegrable (μ := volume)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (2 * δ)) (hi (2 * δ) t)]
    have h1 : 0 ≤ ∫ τ in (0 : ℝ)..2 * δ, Real.smoothTransition ((τ - δ) / δ) :=
      intervalIntegral.integral_nonneg (by linarith) fun τ _ ↦ Real.smoothTransition.nonneg _
    have h2 : ∫ τ in (2 * δ)..t, Real.smoothTransition ((τ - δ) / δ) = t - 2 * δ := by
      rw [intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ))]
      · simp
      intro τ hτ
      rw [uIcc_of_le h] at hτ
      refine Real.smoothTransition.one_of_one_le ?_
      rw [le_div_iff₀ hδ]; linarith [hτ.1]
    linarith

theorem abs_cutG_sub_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) : |cutG δ t - t| ≤ 2 * δ := by
  rw [abs_le]
  constructor
  · linarith [sub_le_cutG hδ ht]
  · linarith [cutG_le (δ := δ) ht]

/-! ### `Δ (G ∘ u) ≥ 0` for convex `G` and harmonic `u` -/

/-- If `G` is `C²` and convex (`G'' ≥ 0`) and `u` is `C²` and harmonic near `x`, then
`Δ(G ∘ u)(x) = G''(u) |∇u|² ≥ 0`. -/
theorem laplacian_comp_nonneg {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (hG'' : ∀ t, 0 ≤ deriv (deriv G) t) {u : E 2 → ℝ} {P : Set (E 2)} (hP : IsOpen P)
    (hu : ContDiffOn ℝ 2 u P) (hΔ : ∀ x ∈ P, Δ u x = 0) {x : E 2} (hx : x ∈ P) :
    0 ≤ Δ (G ∘ u) x := by
  have hdG : ∀ t, HasDerivAt G (deriv G t) t := fun t ↦
    ((hG.differentiable (by norm_num)) t).hasDerivAt
  have hG1 : ContDiff ℝ 1 (deriv G) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv] at hG
    exact hG.2.2
  have hddG : ∀ t, HasDerivAt (deriv G) (deriv (deriv G) t) t := fun t ↦
    ((hG1.differentiable one_ne_zero) t).hasDerivAt
  have hdu : ∀ y ∈ P, HasFDerivAt u (fderiv ℝ u y) y := fun y hy ↦
    ((hu.contDiffAt (hP.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  have hddu : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x := by
    have h := (hu.contDiffAt (hP.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)
    exact (h.differentiableAt (by norm_num)).hasFDerivAt
  have heq : fderiv ℝ (G ∘ u) =ᶠ[𝓝 x] fun y ↦ deriv G (u y) • fderiv ℝ u y := by
    filter_upwards [hP.mem_nhds hx] with y hy
    exact ((hdG (u y)).comp_hasFDerivAt y (hdu y hy)).fderiv
  have hc : HasFDerivAt (fun y ↦ deriv G (u y)) (deriv (deriv G) (u x) • fderiv ℝ u x) x :=
    (hddG (u x)).comp_hasFDerivAt x (hdu x hx)
  have h2 := (heq.fderiv_eq).trans (hc.smul hddu).fderiv
  set b := stdOrthonormalBasis ℝ (E 2)
  have hΔx := hΔ x hx
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b] at hΔx
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (G ∘ u) b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hΔx ⊢
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    hΔx, mul_zero, zero_add]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [mul_assoc]
  exact mul_nonneg (hG'' _) (mul_self_nonneg _)

theorem deriv_deriv_cutG_nonneg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ deriv (deriv (cutG δ)) t := by
  rw [deriv_cutG]
  refine Monotone.deriv_nonneg fun a b hab ↦ Real.smoothTransition.monotone ?_
  gcongr

section Approx

variable {Ω : Set (E 2)} {u : E 2 → ℝ}

theorem isOpen_posSet (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω) : IsOpen (posSet u Ω) :=
  hu.isOpen_inter_preimage hΩ isOpen_Ioi

theorem cutG_comp_eventuallyEq_zero (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω) {δ : ℝ}
    (hδ : 0 < δ) {x : E 2} (hx : x ∈ Ω) (hux : u x < δ) :
    cutG δ ∘ u =ᶠ[𝓝 x] fun _ ↦ 0 := by
  filter_upwards [(hu.continuousAt (hΩ.mem_nhds hx)).eventually (gt_mem_nhds hux)] with y hy
  exact cutG_eq_zero hδ hy.le

theorem contDiffOn_cutG_comp (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hnn : ∀ x ∈ Ω, 0 ≤ u x) (hC2 : ContDiffOn ℝ 2 u (posSet u Ω)) {δ : ℝ} (hδ : 0 < δ) :
    ContDiffOn ℝ 2 (cutG δ ∘ u) Ω := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  rcases (hnn x hx).lt_or_eq with h | h
  · have hxP : x ∈ posSet u Ω := ⟨hx, h⟩
    exact (contDiff_cutG δ).contDiffAt.comp x
      (hC2.contDiffAt ((isOpen_posSet hΩ hu).mem_nhds hxP))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cutG_comp_eventuallyEq_zero hΩ hu hδ hx (h ▸ hδ))

theorem laplacian_cutG_comp_nonneg (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hnn : ∀ x ∈ Ω, 0 ≤ u x) (hC2 : ContDiffOn ℝ 2 u (posSet u Ω))
    (hΔ : ∀ x ∈ posSet u Ω, Δ u x = 0) {δ : ℝ} (hδ : 0 < δ) {x : E 2} (hx : x ∈ Ω) :
    0 ≤ Δ (cutG δ ∘ u) x := by
  rcases (hnn x hx).lt_or_eq with h | h
  · exact laplacian_comp_nonneg (contDiff_cutG δ) (deriv_deriv_cutG_nonneg hδ)
      (isOpen_posSet hΩ hu) hC2 hΔ ⟨hx, h⟩
  · rw [(InnerProductSpace.laplacian_congr_nhds
      (cutG_comp_eventuallyEq_zero hΩ hu hδ hx (h ▸ hδ))).eq_of_nhds,
      InnerProductSpace.laplacian_const]
    rfl

end Approx

/-! ### Layer cake for the logarithmic test function -/

/-- The test function `ψ(y) = (log (R / max(a, |y - x|)))₊`, the truncated Green function of
`B_R(x)`: `ψ = ∫_a^R 1_{B_s(x)} ds / s`. -/
noncomputable def logCut (x : E 2) (a R : ℝ) (y : E 2) : ℝ :=
  max (Real.log (R / max a (dist y x))) 0

theorem logCut_nonneg (x : E 2) (a R : ℝ) (y : E 2) : 0 ≤ logCut x a R y := le_max_right _ _

theorem continuous_logCut (x : E 2) {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    Continuous (logCut x a R) := by
  unfold logCut
  refine Continuous.max ?_ continuous_const
  refine Continuous.log (continuous_const.div (continuous_const.max
    (continuous_id.dist continuous_const)) fun y ↦ ?_) fun y ↦ ?_
  · exact (ha.trans_le (le_max_left _ _)).ne'
  · exact (div_pos (ha.trans_le haR) (ha.trans_le (le_max_left _ _))).ne'

theorem lintegral_inv_Ioo {b R : ℝ} (hb : 0 < b) (hbR : b ≤ R) :
    ∫⁻ s in Ioo b R, (ENNReal.ofReal s)⁻¹ = ENNReal.ofReal (Real.log (R / b)) := by
  rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun s ↦ ENNReal.ofReal s⁻¹)
    fun s hs ↦ (ENNReal.ofReal_inv_of_pos (hb.trans hs.1)).symm]
  have hint : IntegrableOn (fun s : ℝ ↦ s⁻¹) (Ioo b R) :=
    ((continuousOn_inv₀.mono fun s hs ↦ (hb.trans_le hs.1).ne').integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs ↦
      (inv_pos.2 (hb.trans hs.1)).le)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hbR,
    integral_inv_of_pos hb (hb.trans_le hbR)]

theorem lintegral_indicator_inv (x : E 2) {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) (y : E 2) :
    ∫⁻ s in Ioo a R, (Ioi (dist y x)).indicator (fun s ↦ (ENNReal.ofReal s)⁻¹) s =
      ENNReal.ofReal (logCut x a R y) := by
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioo]
  set m := max a (dist y x) with hm
  have hm' : dist y x ⊔ a = m := by rw [hm, max_comm]
  have hpos : 0 < m := ha.trans_le (le_max_left _ _)
  rw [hm']
  unfold logCut
  rw [← hm]
  rcases le_total m R with h | h
  · rw [lintegral_inv_Ioo hpos h, max_eq_left]
    exact Real.log_nonneg (by rw [le_div_iff₀ hpos]; linarith)
  · rw [Ioo_eq_empty (not_lt.2 h), Measure.restrict_empty, lintegral_zero_measure,
      max_eq_right, ENNReal.ofReal_zero]
    exact Real.log_nonpos (div_nonneg (ha.le.trans haR) hpos.le) (by rwa [div_le_one hpos])

/-- **Layer cake**: `∫ ψ dν = ∫_a^R ν(B_s(x)) / s ds` for the logarithmic test function `ψ`. -/
theorem lintegral_logCut (ν : Measure (E 2)) [SFinite ν] (x : E 2) {a R : ℝ} (ha : 0 < a)
    (haR : a ≤ R) :
    ∫⁻ y, ENNReal.ofReal (logCut x a R y) ∂ν =
      ∫⁻ s in Ioo a R, ν (ball x s) / ENNReal.ofReal s := by
  set k : E 2 → ℝ → ℝ≥0∞ := fun y s ↦ (Ioi (dist y x)).indicator
    (fun s ↦ (ENNReal.ofReal s)⁻¹) s with hk
  have hmeas : Measurable (Function.uncurry k) := by
    have : Function.uncurry k = {p : E 2 × ℝ | dist p.1 x < p.2}.indicator
        (fun p ↦ (ENNReal.ofReal p.2)⁻¹) := by
      ext p; simp [hk, indicator, mem_Ioi, Function.uncurry]
    rw [this]
    exact (ENNReal.measurable_ofReal.comp measurable_snd).inv.indicator
      (measurableSet_lt (measurable_fst.dist measurable_const) measurable_snd)
  calc ∫⁻ y, ENNReal.ofReal (logCut x a R y) ∂ν = ∫⁻ y, (∫⁻ s in Ioo a R, k y s) ∂ν := by
        simp_rw [hk, lintegral_indicator_inv x ha haR]
    _ = ∫⁻ s in Ioo a R, (∫⁻ y, k y s ∂ν) := lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ s in Ioo a R, ν (ball x s) / ENNReal.ofReal s := by
        refine lintegral_congr fun s ↦ ?_
        have : (fun y ↦ k y s) = (ball x s).indicator fun _ ↦ (ENNReal.ofReal s)⁻¹ := by
          ext y; simp [hk, indicator, mem_Ioi, mem_ball]
        rw [this, lintegral_indicator_const measurableSet_ball, div_eq_mul_inv, mul_comm]

/-! ### The smooth Riesz–Jensen formula tested against `ψ` -/

theorem laplacian_eq_sum_fderiv (w : E 2 → ℝ) :
    Δ w = fun y ↦ ∑ i, fderiv ℝ (fderiv ℝ w) y (stdOrthonormalBasis ℝ (E 2) i)
      (stdOrthonormalBasis ℝ (E 2) i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem measurable_laplacian (w : E 2 → ℝ) : Measurable (Δ w) := by
  rw [laplacian_eq_sum_fderiv]
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  have h := measurable_fderiv ℝ (fderiv ℝ w)
  exact (ContinuousLinearMap.apply ℝ ℝ _).continuous.measurable.comp
    ((ContinuousLinearMap.apply ℝ _ _).continuous.measurable.comp h)

theorem continuousOn_laplacian {w : E 2 → ℝ} {V : Set (E 2)} (hV : IsOpen V)
    (hw : ContDiffOn ℝ 2 w V) : ContinuousOn (Δ w) V := by
  rw [laplacian_eq_sum_fderiv]
  have hD : ContinuousOn (fderiv ℝ (fderiv ℝ w)) V :=
    (hw.fderiv_of_isOpen hV (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl
  exact continuousOn_finsetSum _ fun i _ ↦
    (hD.clm_apply continuousOn_const).clm_apply continuousOn_const

theorem logCut_eq_zero {x y : E 2} {a R : ℝ} (hR : 0 ≤ R) (hy : y ∉ closedBall x R) :
    logCut x a R y = 0 := by
  rw [mem_closedBall, not_le] at hy
  have hm : dist y x ≤ max a (dist y x) := le_max_right _ _
  have hpos : 0 < max a (dist y x) := by linarith
  refine max_eq_right (Real.log_nonpos (div_nonneg hR hpos.le) ?_)
  rw [div_le_one hpos]; linarith

/-- The smooth Riesz–Jensen formula tested against `ψ`: for `w` of class `C²` with `Δw ≥ 0` on
`Ω ⊇ B̄_R(x)`, `∫_Ω ψ Δw = 2π (⨍_{∂B_R} w - ⨍_{∂B_a} w)`. -/
theorem integral_logCut_mul_laplacian {Ω : Set (E 2)} (hΩ : IsOpen Ω) {w : E 2 → ℝ}
    (hw : ContDiffOn ℝ 2 w Ω) (hΔ : ∀ y ∈ Ω, 0 ≤ Δ w y) {x : E 2} {a R : ℝ} (ha : 0 < a)
    (haR : a ≤ R) (hsub : closedBall x R ⊆ Ω) :
    ∫ y in Ω, logCut x a R y * Δ w y = 2 * π * (circleMean w x R - circleMean w x a) := by
  set F : E 2 → ℝ := fun y ↦ logCut x a R y * Δ w y with hF
  have hΔc := continuousOn_laplacian hΩ hw
  have hF0 : ∀ y ∉ closedBall x R, F y = 0 := fun y hy ↦ by
    simp [hF, logCut_eq_zero (ha.le.trans haR) hy]
  have hFnn : ∀ y, 0 ≤ F y := by
    intro y
    by_cases hy : y ∈ closedBall x R
    · exact mul_nonneg (logCut_nonneg _ _ _ _) (hΔ y (hsub hy))
    · rw [hF0 y hy]
  have hFint : Integrable F := by
    rw [← integrableOn_univ, ← union_compl_self (closedBall x R)]
    refine IntegrableOn.union ?_ ?_
    · exact (((continuous_logCut x ha haR).continuousOn.mul (hΔc.mono hsub)).integrableOn_compact
        (isCompact_closedBall x R))
    · exact (integrableOn_zero).congr_fun (fun y hy ↦ (hF0 y hy).symm)
        isClosed_closedBall.isOpen_compl.measurableSet
  -- reduce `∫_Ω` to `∫`
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ hF0 y fun h ↦ hy (hsub h)]
  -- the ball integrals `I(s) = ∫_{B_s} Δw`
  set I : ℝ → ℝ := fun s ↦ ∫ y in ball x s, Δ w y with hI
  have hIint : ∀ s ≤ R, IntegrableOn (Δ w) (ball x s) :=
    fun s hs ↦ ((hΔc.mono hsub).integrableOn_compact (isCompact_closedBall x R)).mono_set
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hs))
  have hInn : ∀ s ≤ R, 0 ≤ I s := fun s hs ↦
    setIntegral_nonneg measurableSet_ball fun y hy ↦
      hΔ y (hsub (ball_subset_closedBall.trans (closedBall_subset_closedBall hs) hy))
  have hball : ∀ s ≤ R, ∫⁻ y in ball x s, ENNReal.ofReal (Δ w y) = ENNReal.ofReal (I s) :=
    fun s hs ↦ (ofReal_integral_eq_lintegral_ofReal (hIint s hs)
      ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun y hy ↦
        hΔ y (hsub (ball_subset_closedBall.trans (closedBall_subset_closedBall hs) hy))))).symm
  have hImono : MonotoneOn I (uIcc a R) := by
    intro s hs s' hs' hss'
    rw [uIcc_of_le haR] at hs hs'
    refine setIntegral_mono_set (hIint s' hs'.2) ((ae_restrict_iff' measurableSet_ball).2
      (Eventually.of_forall fun y hy ↦ hΔ y (hsub (ball_subset_closedBall.trans
        (closedBall_subset_closedBall hs'.2) hy)))) (Eventually.of_forall (ball_subset_ball hss'))
  have hIdiv : IntegrableOn (fun s ↦ I s / s) (Ioo a R) := by
    have h := (hImono.intervalIntegrable (μ := volume)).mul_continuousOn (g := fun s : ℝ ↦ s⁻¹)
      (continuousOn_inv₀.mono fun s hs ↦ by
        rw [uIcc_of_le haR] at hs; exact (ha.trans_le hs.1).ne')
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le haR] at h
    exact h.mono_set Ioo_subset_Ioc_self
  -- compare via lintegrals
  have hgreen := integral_ball_laplacian_div_E2 hΩ hw ha haR hsub
  rw [← hgreen]
  have hlhs : ENNReal.ofReal (∫ y, F y) = ∫⁻ y, ENNReal.ofReal (logCut x a R y) ∂
      (volume.withDensity fun y ↦ ENNReal.ofReal (Δ w y)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hFint (Eventually.of_forall hFnn),
      lintegral_withDensity_eq_lintegral_mul _ (measurable_laplacian w).ennreal_ofReal
        (continuous_logCut x ha haR).measurable.ennreal_ofReal]
    refine lintegral_congr fun y ↦ ?_
    simp only [hF, Pi.mul_apply]
    rw [ENNReal.ofReal_mul (logCut_nonneg _ _ _ _), mul_comm]
  have hrhs : ENNReal.ofReal (∫ s in a..R, I s / s) =
      ∫⁻ s in Ioo a R, (volume.withDensity fun y ↦ ENNReal.ofReal (Δ w y)) (ball x s) /
        ENNReal.ofReal s := by
    rw [intervalIntegral.integral_of_le haR, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hIdiv ((ae_restrict_iff' measurableSet_Ioo).2
        (Eventually.of_forall fun s hs ↦ div_nonneg (hInn s hs.2.le) (ha.trans hs.1).le))]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s hs ↦ ?_
    rw [withDensity_apply _ measurableSet_ball, hball s hs.2.le,
      ENNReal.ofReal_div_of_pos (ha.trans hs.1)]
  rw [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hFnn)
    (intervalIntegral.integral_nonneg haR fun s hs ↦ div_nonneg (hInn s hs.2) (ha.le.trans hs.1)),
    hlhs, hrhs, lintegral_logCut _ x ha haR]

/-! ### Positive functionals on `C_c(Ω)` -/

section Functional

variable {Ω : Set (E 2)}

open CompactlySupportedContinuousMap
open scoped CompactlySupported

/-- Lebesgue measure on `Ω`. -/
noncomputable abbrev volΩ (Ω : Set (E 2)) : Measure Ω :=
  (volume : Measure (E 2)).comap Subtype.val

theorem isFiniteMeasureOnCompacts_volΩ (hΩ : IsOpen Ω) : IsFiniteMeasureOnCompacts (volΩ Ω) :=
  ⟨fun K hK ↦ by
    rw [(MeasurableEmbedding.subtype_coe hΩ.measurableSet).comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top⟩

theorem integrable_mul (hΩ : IsOpen Ω) {f : E 2 → ℝ} (hf : ContinuousOn f Ω)
    (φ : C_c(Ω, ℝ)) : Integrable (fun y : Ω ↦ φ y * f y) (volΩ Ω) := by
  haveI := isFiniteMeasureOnCompacts_volΩ hΩ
  exact (φ.continuous.mul
    (continuousOn_iff_continuous_restrict.1 hf)).integrable_of_hasCompactSupport
    φ.hasCompactSupport.mul_right

/-- `φ ↦ ∫_Ω φ f`. -/
noncomputable def lapFunctional (hΩ : IsOpen Ω) {f : E 2 → ℝ} (hf : ContinuousOn f Ω) :
    C_c(Ω, ℝ) →ₗ[ℝ] ℝ where
  toFun φ := ∫ y, φ y * f y ∂(volΩ Ω)
  map_add' φ ψ := by
    simp only [coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrable_mul hΩ hf φ) (integrable_mul hΩ hf ψ)
  map_smul' c φ := by
    simp only [coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
    exact integral_const_mul c _

theorem lapFunctional_apply (hΩ : IsOpen Ω) {f : E 2 → ℝ} (hf : ContinuousOn f Ω)
    (φ : C_c(Ω, ℝ)) : lapFunctional hΩ hf φ = ∫ y, φ y * f y ∂(volΩ Ω) := rfl

theorem lapFunctional_nonneg (hΩ : IsOpen Ω) {f : E 2 → ℝ} (hf : ContinuousOn f Ω)
    (hf0 : ∀ y ∈ Ω, 0 ≤ f y) {φ : C_c(Ω, ℝ)} (hφ : 0 ≤ φ) : 0 ≤ lapFunctional hΩ hf φ :=
  integral_nonneg fun y ↦ mul_nonneg (le_def.1 hφ y) (hf0 y y.2)

theorem abs_lapFunctional_le (hΩ : IsOpen Ω) {f : E 2 → ℝ} (hf : ContinuousOn f Ω)
    (hf0 : ∀ y ∈ Ω, 0 ≤ f y) {φ ψ : C_c(Ω, ℝ)} {c : ℝ} (h : ∀ y, |φ y| ≤ c * ψ y) :
    |lapFunctional hΩ hf φ| ≤ c * lapFunctional hΩ hf ψ := by
  rw [lapFunctional_apply, lapFunctional_apply, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrable_mul hΩ hf ψ).const_mul c)
    (Eventually.of_forall fun y ↦ ?_)
  change ‖φ y * f y‖ ≤ c * (ψ y * f y)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 y y.2), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h y) (hf0 y y.2)

theorem lapFunctional_eq_setIntegral (hΩ : IsOpen Ω) {f : E 2 → ℝ} (hf : ContinuousOn f Ω)
    {g : E 2 → ℝ} {φ : C_c(Ω, ℝ)} (hφ : ∀ y : Ω, φ y = g y) :
    lapFunctional hΩ hf φ = ∫ y in Ω, g y * f y := by
  rw [lapFunctional_apply, ← integral_subtype_comap hΩ.measurableSet]
  simp_rw [hφ]

/-- The limit of a bounded real sequence along the hyperfilter of `ℕ`. -/
noncomputable def uLim (g : ℕ → ℝ) : ℝ := limUnder (hyperfilter ℕ : Filter ℕ) g

theorem tendsto_uLim {g : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |g n| ≤ C) :
    Tendsto g (hyperfilter ℕ) (𝓝 (uLim g)) := by
  obtain ⟨a, -, ha⟩ := (isCompact_Icc (a := -C) (b := C)).ultrafilter_le_nhds
    ((hyperfilter ℕ).map g) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      exact Filter.mem_map.2 (univ_mem' fun n ↦ abs_le.1 (hC n)))
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem uLim_eq {g : ℕ → ℝ} {c : ℝ} (h : Tendsto g atTop (𝓝 c)) : uLim g = c :=
  (h.mono_left (hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)).limUnder_eq

/-- The limit functional of a pointwise bounded sequence of positive functionals. -/
noncomputable def limFunctional (L : ℕ → C_c(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hb : ∀ φ, ∃ C, ∀ n, |L n φ| ≤ C) (hpos : ∀ n φ, 0 ≤ φ → 0 ≤ L n φ) :
    C_c(Ω, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun φ ↦ uLim fun n ↦ L n φ
      map_add' := fun φ ψ ↦ by
        obtain ⟨C₁, h₁⟩ := hb φ
        obtain ⟨C₂, h₂⟩ := hb ψ
        refine Tendsto.limUnder_eq ?_
        simp_rw [map_add]
        exact (tendsto_uLim h₁).add (tendsto_uLim h₂)
      map_smul' := fun c φ ↦ by
        obtain ⟨C, h⟩ := hb φ
        refine Tendsto.limUnder_eq ?_
        simp_rw [map_smul, smul_eq_mul, RingHom.id_apply]
        exact (tendsto_uLim h).const_mul c }
    fun φ hφ ↦ by
      obtain ⟨C, h⟩ := hb φ
      exact ge_of_tendsto (tendsto_uLim h) (Eventually.of_forall fun n ↦ hpos n φ hφ)

theorem limFunctional_eq (L : ℕ → C_c(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hb : ∀ φ, ∃ C, ∀ n, |L n φ| ≤ C) (hpos : ∀ n φ, 0 ≤ φ → 0 ≤ L n φ) {φ : C_c(Ω, ℝ)}
    {c : ℝ} (h : Tendsto (fun n ↦ L n φ) atTop (𝓝 c)) : limFunctional L hb hpos φ = c :=
  uLim_eq h

/-- `ψ = logCut x a R` as an element of `C_c(Ω)`. -/
noncomputable def logCutC {x : E 2} {a R : ℝ} (ha : 0 < a) (haR : a ≤ R)
    (hsub : closedBall x R ⊆ Ω) : C_c(Ω, ℝ) :=
  ⟨⟨fun y ↦ logCut x a R y, (continuous_logCut x ha haR).comp continuous_subtype_val⟩,
    HasCompactSupport.intro (K := Subtype.val ⁻¹' closedBall x R)
      (Subtype.isCompact_iff.2 (by
        rw [Subtype.image_preimage_coe, inter_eq_right.2 hsub]
        exact isCompact_closedBall x R))
      fun y hy ↦ logCut_eq_zero (ha.le.trans haR) hy⟩

theorem logCutC_apply {x : E 2} {a R : ℝ} (ha : 0 < a) (haR : a ≤ R)
    (hsub : closedBall x R ⊆ Ω) (y : Ω) : logCutC ha haR hsub y = logCut x a R y := rfl

end Functional

/-! ### Circle means: comparison -/

theorem circleMean_sub {w v : E 2 → ℝ} {x : E 2} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ContinuousOn w (sphere x ρ)) (hv : ContinuousOn v (sphere x ρ)) :
    circleMean (w - v) x ρ = circleMean w x ρ - circleMean v x ρ :=
  Real.circleAverage_sub (circleIntegrable_of_continuousOn hρ hw)
    (circleIntegrable_of_continuousOn hρ hv)

theorem circleMean_const (c : ℝ) (x : E 2) (ρ : ℝ) : circleMean (fun _ ↦ c) x ρ = c :=
  Real.circleAverage_const c _ _

theorem abs_circleMean_sub_le {w v : E 2 → ℝ} {x : E 2} {ρ M : ℝ} (hρ : 0 ≤ ρ)
    (hw : ContinuousOn w (sphere x ρ)) (hv : ContinuousOn v (sphere x ρ))
    (h : ∀ z ∈ sphere x ρ, |w z - v z| ≤ M) :
    |circleMean w x ρ - circleMean v x ρ| ≤ M := by
  rw [abs_le]
  constructor
  · have := circleMean_le (u := v - w) hρ (hv.sub hw) fun z hz ↦ by
      have := (abs_le.1 (h z hz)).1; simp only [Pi.sub_apply]; linarith
    rw [circleMean_sub hρ hv hw] at this
    linarith
  · have := circleMean_le (u := w - v) hρ (hw.sub hv) fun z hz ↦ (abs_le.1 (h z hz)).2
    rw [circleMean_sub hρ hw hv] at this
    exact this

/-! ### The approximating functionals -/

section Construction

open CompactlySupportedContinuousMap
open scoped CompactlySupported

/-- The hypotheses of `exists_isRieszMeasure`. -/
structure Hyp (Ω : Set (E 2)) (u : E 2 → ℝ) : Prop where
  isOpen : IsOpen Ω
  cont : ContinuousOn u Ω
  nonneg : ∀ x ∈ Ω, 0 ≤ u x
  c2 : ContDiffOn ℝ 2 u (posSet u Ω)
  harm : ∀ x ∈ posSet u Ω, Δ u x = 0

variable {Ω : Set (E 2)} {u : E 2 → ℝ}

/-- `δ_n = 1/(n+1)`. -/
noncomputable def δseq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem δseq_pos (n : ℕ) : 0 < δseq n := Nat.one_div_pos_of_nat

theorem δseq_le_one (n : ℕ) : δseq n ≤ 1 := by
  unfold δseq
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_δseq : Tendsto δseq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- `w_n = G_{δ_n} ∘ u`. -/
noncomputable def wseq (u : E 2 → ℝ) (n : ℕ) : E 2 → ℝ := cutG (δseq n) ∘ u

namespace Hyp

variable (h : Hyp Ω u)
include h

theorem wseq_contDiffOn (n : ℕ) : ContDiffOn ℝ 2 (wseq u n) Ω :=
  contDiffOn_cutG_comp h.isOpen h.cont h.nonneg h.c2 (δseq_pos n)

theorem wseq_continuousOn (n : ℕ) : ContinuousOn (wseq u n) Ω :=
  (h.wseq_contDiffOn n).continuousOn

theorem laplacian_wseq_nonneg (n : ℕ) : ∀ y ∈ Ω, 0 ≤ Δ (wseq u n) y := fun _ hy ↦
  laplacian_cutG_comp_nonneg h.isOpen h.cont h.nonneg h.c2 h.harm (δseq_pos n) hy

theorem continuousOn_laplacian_wseq (n : ℕ) : ContinuousOn (Δ (wseq u n)) Ω :=
  continuousOn_laplacian h.isOpen (h.wseq_contDiffOn n)

theorem abs_wseq_sub_le (n : ℕ) {y : E 2} (hy : y ∈ Ω) : |wseq u n y - u y| ≤ 2 * δseq n :=
  abs_cutG_sub_le (δseq_pos n) (h.nonneg y hy)

/-- `Λ_n φ = ∫_Ω φ Δw_n`. -/
noncomputable def L (n : ℕ) : C_c(Ω, ℝ) →ₗ[ℝ] ℝ :=
  lapFunctional h.isOpen (h.continuousOn_laplacian_wseq n)

theorem L_nonneg (n : ℕ) (φ : C_c(Ω, ℝ)) (hφ : 0 ≤ φ) : 0 ≤ h.L n φ :=
  lapFunctional_nonneg _ _ (h.laplacian_wseq_nonneg n) hφ

theorem L_logCutC (n : ℕ) {x : E 2} {a R : ℝ} (ha : 0 < a) (haR : a ≤ R)
    (hsub : closedBall x R ⊆ Ω) :
    h.L n (logCutC ha haR hsub) =
      2 * π * (circleMean (wseq u n) x R - circleMean (wseq u n) x a) := by
  rw [L, lapFunctional_eq_setIntegral (g := logCut x a R) _ _ fun y ↦ rfl]
  exact integral_logCut_mul_laplacian h.isOpen (h.wseq_contDiffOn n)
    (h.laplacian_wseq_nonneg n) ha haR hsub

theorem abs_circleMean_wseq_sub_le (n : ℕ) {x : E 2} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsph : sphere x ρ ⊆ Ω) :
    |circleMean (wseq u n) x ρ - circleMean u x ρ| ≤ 2 * δseq n :=
  abs_circleMean_sub_le hρ ((h.wseq_continuousOn n).mono hsph) (h.cont.mono hsph)
    fun _ hz ↦ h.abs_wseq_sub_le n (hsph hz)

theorem abs_circleMean_wseq_le (n : ℕ) {x : E 2} {ρ B : ℝ} (hρ : 0 ≤ ρ)
    (hsph : sphere x ρ ⊆ Ω) (hB : ∀ z ∈ sphere x ρ, |u z| ≤ B) :
    |circleMean (wseq u n) x ρ| ≤ B + 2 := by
  have := abs_circleMean_sub_le (v := fun _ ↦ 0) (M := B + 2) hρ
    ((h.wseq_continuousOn n).mono hsph) continuousOn_const fun z hz ↦ by
      have h1 := h.abs_wseq_sub_le n (hsph hz)
      have h2 := hB z hz
      have h3 := δseq_le_one n
      rw [sub_zero]
      calc |wseq u n z| ≤ |wseq u n z - u z| + |u z| := by
            have := abs_add_le (wseq u n z - u z) (u z); rwa [sub_add_cancel] at this
        _ ≤ B + 2 := by linarith
  rwa [circleMean_const, sub_zero] at this

theorem L_bounded (φ : C_c(Ω, ℝ)) : ∃ C, ∀ n, |h.L n φ| ≤ C := by
  classical
  have hr : ∀ y ∈ Ω, ∃ r > 0, closedBall y (3 * r) ⊆ Ω := by
    intro y hy
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 h.isOpen y hy
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hεΩ⟩
  choose! r hr0 hrΩ using hr
  have hB : ∀ y ∈ Ω, ∃ B, ∀ z ∈ closedBall y (3 * r y), |u z| ≤ B := fun y hy ↦ by
    obtain ⟨B, hB⟩ := (isCompact_closedBall y (3 * r y)).exists_bound_of_continuousOn
      (h.cont.mono (hrΩ y hy))
    exact ⟨B, fun z hz ↦ by simpa [Real.norm_eq_abs] using hB z hz⟩
  choose! B hB using hB
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hsub : ∀ y ∈ Ω, closedBall y (Real.exp 1 * r y) ⊆ Ω := fun y hy ↦
    (closedBall_subset_closedBall (by nlinarith [hr0 y hy])).trans (hrΩ y hy)
  have hle : ∀ y ∈ Ω, r y ≤ Real.exp 1 * r y := fun y hy ↦
    le_mul_of_one_le_left (hr0 y hy).le he1
  let Ψ : E 2 → C_c(Ω, ℝ) := fun y ↦
    if hy : y ∈ Ω then logCutC (hr0 y hy) (hle y hy) (hsub y hy) else 0
  set K := ((↑) : Ω → E 2) '' tsupport φ with hKdef
  have hK : IsCompact K := φ.hasCompactSupport.image continuous_subtype_val
  have hKΩ : K ⊆ Ω := by rintro _ ⟨z, -, rfl⟩; exact z.2
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun y ↦ ball y (r y))
    fun y hy ↦ ball_mem_nhds y (hr0 y (hKΩ hy))
  obtain ⟨M₀, hM₀⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  obtain ⟨M, hM0', hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖φ z‖ ≤ M :=
    ⟨max M₀ 0, le_max_right _ _, fun z ↦ (hM₀ z).trans (le_max_left _ _)⟩
  have hM0 : ∀ _z : Ω, 0 ≤ M := fun _ ↦ hM0'
  set ψ := ∑ y ∈ t, Ψ y with hψ
  have hΨnn : ∀ y z, 0 ≤ Ψ y z := by
    intro y z
    by_cases hy : y ∈ Ω
    · simp only [Ψ, dif_pos hy, logCutC_apply]; exact logCut_nonneg _ _ _ _
    · simp [Ψ, hy]
  have hψz : ∀ z, ψ z = ∑ y ∈ t, Ψ y z := fun z ↦ by rw [hψ, sum_apply]
  have hdom : ∀ z, |φ z| ≤ M * ψ z := by
    intro z
    by_cases hz : φ z = 0
    · rw [hz, abs_zero, hψz]
      exact mul_nonneg (hM0 z) (Finset.sum_nonneg fun y _ ↦ hΨnn y z)
    · have hzK : (z : E 2) ∈ K := ⟨z, subset_tsupport _ hz, rfl⟩
      obtain ⟨y, hyt, hzy⟩ := mem_iUnion₂.1 (hcover hzK)
      have hyΩ := hKΩ (htK y hyt)
      have hone : Ψ y z = 1 := by
        simp only [Ψ, dif_pos hyΩ, logCutC_apply, logCut]
        rw [mem_ball] at hzy
        rw [max_eq_left hzy.le, mul_div_assoc, div_self (hr0 y hyΩ).ne', mul_one, Real.log_exp,
          max_eq_left zero_le_one]
      have h1 : 1 ≤ ψ z := by
        rw [hψz, ← hone]
        exact Finset.single_le_sum (fun y _ ↦ hΨnn y z) hyt
      calc |φ z| = ‖φ z‖ := (Real.norm_eq_abs _).symm
        _ ≤ M := hM z
        _ ≤ M * ψ z := le_mul_of_one_le_right (hM0 z) h1
  have hLΨ : ∀ n, ∀ y ∈ t, h.L n (Ψ y) ≤ 2 * π * (2 * (B y + 2)) := by
    intro n y hyt
    have hyΩ := hKΩ (htK y hyt)
    have hr := hr0 y hyΩ
    simp only [Ψ, dif_pos hyΩ]
    rw [h.L_logCutC]
    have hsph : ∀ ρ, 0 ≤ ρ → ρ ≤ 3 * r y → sphere y ρ ⊆ closedBall y (3 * r y) :=
      fun ρ _ hρ ↦ sphere_subset_closedBall.trans (closedBall_subset_closedBall hρ)
    have h1 := h.abs_circleMean_wseq_le n (x := y) (ρ := Real.exp 1 * r y) (B := B y)
      (by positivity) ((hsph _ (by positivity) (by nlinarith)).trans (hrΩ y hyΩ))
      fun z hz ↦ hB y hyΩ z (hsph _ (by positivity) (by nlinarith) hz)
    have h2 := h.abs_circleMean_wseq_le n (x := y) (ρ := r y) (B := B y)
      hr.le ((hsph _ hr.le (by linarith)).trans (hrΩ y hyΩ))
      fun z hz ↦ hB y hyΩ z (hsph _ hr.le (by linarith) hz)
    have := (abs_le.1 h1).2
    have := (abs_le.1 h2).1
    have hπ := Real.pi_pos
    nlinarith
  refine ⟨M * ∑ y ∈ t, 2 * π * (2 * (B y + 2)), fun n ↦ ?_⟩
  calc |h.L n φ| ≤ M * h.L n ψ :=
        abs_lapFunctional_le _ _ (h.laplacian_wseq_nonneg n) hdom
    _ = M * ∑ y ∈ t, h.L n (Ψ y) := by rw [hψ, map_sum]
    _ ≤ M * ∑ y ∈ t, 2 * π * (2 * (B y + 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (hLΨ n)) hM0'

/-- The limit functional `Λ = lim_𝒰 Λ_n`, positive and linear on `C_c(Ω)`. -/
noncomputable def Λ : C_c(Ω, ℝ) →ₚ[ℝ] ℝ := limFunctional h.L h.L_bounded h.L_nonneg

theorem Λ_logCutC {x : E 2} {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) (hsub : closedBall x R ⊆ Ω) :
    h.Λ (logCutC ha haR hsub) = 2 * π * (circleMean u x R - circleMean u x a) := by
  refine limFunctional_eq _ _ _ ?_
  simp_rw [h.L_logCutC]
  have hm : ∀ ρ, 0 ≤ ρ → ρ ≤ R →
      Tendsto (fun n ↦ circleMean (wseq u n) x ρ) atTop (𝓝 (circleMean u x ρ)) := by
    intro ρ h0 hρ
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (by simpa using tendsto_δseq.const_mul 2)
    rw [Real.norm_eq_abs]
    exact h.abs_circleMean_wseq_sub_le n h0
      (sphere_subset_closedBall.trans ((closedBall_subset_closedBall hρ).trans hsub))
  exact ((hm R (ha.le.trans haR) le_rfl).sub (hm a ha.le haR)).const_mul (2 * π)

/-- `⨍_{∂B_ρ(x)} u → u(x)` as `ρ → 0⁺`. -/
theorem tendsto_circleMean {x : E 2} (hx : x ∈ Ω) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (hlim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun k ↦ circleMean u x (a k)) atTop (𝓝 (u x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hηΩ⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  obtain ⟨θ, hθ, hθu⟩ := Metric.continuousAt_iff.1 (h.cont.continuousAt (h.isOpen.mem_nhds hx))
    (ε / 2) (by positivity)
  filter_upwards [(Metric.tendsto_nhds.1 hlim) (min η θ) (lt_min hη hθ)] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_pos (ha k)] at hk
  have hsph : sphere x (a k) ⊆ Ω := fun z hz ↦ hηΩ (by
    rw [mem_ball, mem_sphere.1 hz]; exact hk.trans_le (min_le_left _ _))
  have := abs_circleMean_sub_le (v := fun _ ↦ u x) (M := ε / 2) (ha k).le (h.cont.mono hsph)
    continuousOn_const fun z hz ↦ by
      have := hθu (x := z) (by rw [mem_sphere.1 hz]; exact hk.trans_le (min_le_right _ _))
      rw [Real.dist_eq] at this; exact this.le
  rw [circleMean_const] at this
  rw [Real.dist_eq]
  linarith

/-- **Existence of the Riesz measure**, under the bundled hypotheses `h`. -/
theorem exists_isRieszMeasure : ∃ μ : Measure (E 2), IsRieszMeasure Ω u μ := by
  haveI := h.isOpen.locallyCompactSpace
  set μΩ := RealRMK.rieszMeasure h.Λ with hμΩ
  set μ : Measure (E 2) := μΩ.map Subtype.val with hμ
  refine ⟨μ, fun x R hR hsub ↦ ?_⟩
  set M : ℝ → ℝ := fun ρ ↦ circleMean u x ρ with hM
  have hxΩ : x ∈ Ω := hsub (mem_closedBall_self hR.le)
  -- Step 1: the Riesz–Jensen formula between radii `a` and `R`
  have hstep : ∀ a, 0 < a → a ≤ R →
      ∫⁻ s in Ioo a R, μ (ball x s) / ENNReal.ofReal s = ENNReal.ofReal (2 * π * (M R - M a)) := by
    intro a ha haR
    set ν := μ.restrict (closedBall x R)
    have hcpt : IsCompact (Subtype.val ⁻¹' closedBall x R : Set Ω) :=
      Subtype.isCompact_iff.2 (by
        rw [Subtype.image_preimage_coe, inter_eq_right.2 hsub]; exact isCompact_closedBall x R)
    haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by
      rw [hμ, Measure.map_apply measurable_subtype_coe measurableSet_closedBall]
      exact hcpt.measure_lt_top.ne)
    have h1 : ∫⁻ y, ENNReal.ofReal (logCut x a R y) ∂ν = ENNReal.ofReal (2 * π * (M R - M a)) := by
      rw [setLIntegral_eq_of_support_subset (fun y hy ↦ by
          by_contra h'
          exact hy (by
            change ENNReal.ofReal (logCut x a R y) = 0
            rw [logCut_eq_zero (ha.le.trans haR) h', ENNReal.ofReal_zero])),
        hμ, lintegral_map (continuous_logCut x ha haR).measurable.ennreal_ofReal
          measurable_subtype_coe]
      set φ := logCutC ha haR hsub
      have hφi : Integrable (fun z : Ω ↦ logCut x a R z) μΩ :=
        φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      rw [← ofReal_integral_eq_lintegral_ofReal hφi
        (Eventually.of_forall fun z ↦ logCut_nonneg _ _ _ _)]
      congr 1
      exact (RealRMK.integral_rieszMeasure h.Λ φ).trans (h.Λ_logCutC ha haR hsub)
    rw [← h1, lintegral_logCut ν x ha haR]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s hs ↦ ?_
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hs.2.le))]
  have hnn : ∀ a, 0 < a → a ≤ R → 0 ≤ M R - M a := by
    intro a ha haR
    have h0 := h.Λ.map_nonneg (x := logCutC ha haR hsub)
      (le_def.2 fun z ↦ logCut_nonneg _ _ _ _)
    rw [h.Λ_logCutC] at h0
    have := Real.pi_pos
    nlinarith
  -- Step 2: `a → 0`
  set a : ℕ → ℝ := fun k ↦ R * δseq k with ha
  have ha0 : ∀ k, 0 < a k := fun k ↦ mul_pos hR (δseq_pos k)
  have haR : ∀ k, a k ≤ R := fun k ↦ mul_le_of_le_one_right hR.le (δseq_le_one k)
  have hamono : Antitone a := fun i j hij ↦
    mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) (by gcongr)) hR.le
  have hatend : Tendsto a atTop (𝓝 0) := by simpa using tendsto_δseq.const_mul R
  have hMa := h.tendsto_circleMean hxΩ ha0 hatend
  have hUnion : ⋃ k, Ioo (a k) R = Ioo 0 R := by
    ext s
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨k, hk1, hk2⟩; exact ⟨(ha0 k).trans hk1, hk2⟩
    · rintro ⟨hs0, hsR⟩
      obtain ⟨k, hk⟩ := ((Metric.tendsto_nhds.1 hatend) s hs0).exists
      rw [Real.dist_eq, sub_zero, abs_of_pos (ha0 k)] at hk
      exact ⟨k, hk, hsR⟩
  set F : ℝ → ℝ≥0∞ := fun s ↦ μ (ball x s) / ENNReal.ofReal s
  have hlim1 : Tendsto (fun k ↦ ∫⁻ s in Ioo (a k) R, F s) atTop (𝓝 (∫⁻ s in Ioo 0 R, F s)) := by
    simp_rw [← withDensity_apply F measurableSet_Ioo]
    rw [← hUnion]
    exact tendsto_measure_iUnion_atTop fun i j hij ↦ Ioo_subset_Ioo_left (hamono hij)
  have hlim2 : Tendsto (fun k ↦ ∫⁻ s in Ioo (a k) R, F s) atTop
      (𝓝 (ENNReal.ofReal (2 * π * (M R - u x)))) := by
    have hk : ∀ k, ∫⁻ s in Ioo (a k) R, F s = ENNReal.ofReal (2 * π * (M R - M (a k))) :=
      fun k ↦ hstep (a k) (ha0 k) (haR k)
    simp_rw [hk]
    exact ENNReal.tendsto_ofReal ((tendsto_const_nhds.sub hMa).const_mul _)
  have heq := tendsto_nhds_unique hlim1 hlim2
  have hpos : 0 ≤ M R - u x := ge_of_tendsto (tendsto_const_nhds.sub hMa)
    (Eventually.of_forall fun k ↦ hnn (a k) (ha0 k) (haR k))
  refine ⟨by rw [heq]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [heq, ENNReal.toReal_ofReal (by positivity)]
  field_simp
  rfl

end Hyp

end Construction

end RieszMeasure

/-- **Existence of the Riesz measure.** Let `Ω ⊆ E 2` be open and `u`
continuous and non-negative on `Ω`, `C²` and harmonic in `{u > 0}`. Then `u` has a Riesz measure
`μ = Δu` on `Ω`: for every closed disc `B̄_r(x) ⊆ Ω`,
`⨍_{∂B_r(x)} u - u(x) = (1/2π) ∫₀^r μ(B_s(x)) / s ds` (`IsRieszMeasure`).

This is the fact "since `Δu` is a non-negative measure" together with the formula
`d/dr ⨍_{∂B_r} u = |∂B_1|⁻¹ r^{1-d} ∫_{B_r} Δu` used without proof in the proof of Lemma B.3.
The construction is described in the module docstring. Normalization check: `u = |x|²` gives
`μ = 4 dx` and both sides equal `r²`. -/
theorem exists_isRieszMeasure {Ω : Set (E 2)} (hΩ : IsOpen Ω) {u : E 2 → ℝ}
    (hu : ContinuousOn u Ω) (hnn : ∀ x ∈ Ω, 0 ≤ u x) (hC2 : ContDiffOn ℝ 2 u (posSet u Ω))
    (hΔ : ∀ x ∈ posSet u Ω, Δ u x = 0) : ∃ μ : Measure (E 2), IsRieszMeasure Ω u μ :=
  RieszMeasure.Hyp.exists_isRieszMeasure ⟨hΩ, hu, hnn, hC2, hΔ⟩

end PerronVariational

end
