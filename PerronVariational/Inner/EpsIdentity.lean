/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
import GMTFoundations.BV.TotalVariation
import GMTFoundations.Sobolev.L2Inner
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered

/-!
# Passage to the limit in the inner-variation identity

Proof of Proposition 4.1(ii) of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: "The
convergence obtained above is sufficient to pass to the limit in (4.2)". Given, on `U_∞`,
* `∇u_n → ∇u` strongly in `L²_loc`,
* `χ_n → χ` in `L¹_loc` with `|χ_n|, |χ| ≤ 1`,
* `∂ₜu_n ⇀ w` weakly in `L²(U_∞)` with bounded norms,
the identities `∫ paraInnerVarIntegrand Q u_n (∂ₜu_n) χ_n ξ = 0` pass to the limit
(`Inner.paraInnerVar_integral_eq_zero_of_tendsto`). Pure measure theory: products of strongly and
strongly/weakly convergent sequences.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

@[expose] public section

namespace PerronVariational

namespace Inner

section L2

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure X}

theorem integrable_mul_of_memLp {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ f x * g x) μ := by
  refine (GMTFoundations.integrable_inner_of_memLp hg hf).congr (Eventually.of_forall fun x ↦ ?_)
  simp [RCLike.inner_apply]

/-- Strong × strong: `∫ ⟪f_i, g_i⟫ → ∫ ⟪f, g⟫` if `f_i → f`, `g_i → g` in `L²`. -/
theorem tendsto_integral_inner_of_tendsto {ι : Type*} {l : Filter ι} {f g : ι → X → F}
    {f₀ g₀ : X → F} (hf : ∀ i, MemLp (f i) 2 μ) (hf₀ : MemLp f₀ 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hg₀ : MemLp g₀ 2 μ) (hfc : Tendsto (fun i ↦ eLpNorm (f i - f₀) 2 μ) l (𝓝 0))
    (hgc : Tendsto (fun i ↦ eLpNorm (g i - g₀) 2 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, inner ℝ (f i x) (g i x) ∂μ) l
      (𝓝 (∫ x, inner ℝ (f₀ x) (g₀ x) ∂μ)) := by
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf f₀ hf₀).2 hfc
  have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg g₀ hg₀).2 hgc
  rw [GMTFoundations.integral_inner_eq_L2 hf₀ hg₀]
  refine (h1.inner h2).congr fun i ↦ ?_
  rw [GMTFoundations.integral_inner_eq_L2 (hf i) (hg i)]

/-- Strong × weak: `∫ f_i w_i → ∫ f w` if `f_i → f` strongly in `L²`, `‖w_i‖_{L²} ≤ B` and
`∫ f w_i → ∫ f w`. -/
theorem tendsto_integral_mul_of_strong_weak {ι : Type*} {l : Filter ι} {f w : ι → X → ℝ}
    {f₀ w₀ : X → ℝ} (hf : ∀ i, MemLp (f i) 2 μ) (hf₀ : MemLp f₀ 2 μ) (hw : ∀ i, MemLp (w i) 2 μ)
    (hfc : Tendsto (fun i ↦ eLpNorm (f i - f₀) 2 μ) l (𝓝 0)) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i, eLpNorm (w i) 2 μ ≤ ENNReal.ofReal B)
    (hweak : Tendsto (fun i ↦ ∫ x, f₀ x * w i x ∂μ) l (𝓝 (∫ x, f₀ x * w₀ x ∂μ))) :
    Tendsto (fun i ↦ ∫ x, f i x * w i x ∂μ) l (𝓝 (∫ x, f₀ x * w₀ x ∂μ)) := by
  have hsplit : ∀ i, ∫ x, f i x * w i x ∂μ =
      ∫ x, (f i x - f₀ x) * w i x ∂μ + ∫ x, f₀ x * w i x ∂μ := by
    intro i
    rw [← integral_add (integrable_mul_of_memLp (f := fun x ↦ f i x - f₀ x) ((hf i).sub hf₀) (hw i))
      (integrable_mul_of_memLp hf₀ (hw i))]
    congr 1
    ext x
    ring
  have hsmall : Tendsto (fun i ↦ ∫ x, (f i x - f₀ x) * w i x ∂μ) l (𝓝 0) := by
    have hbd : ∀ i, |∫ x, (f i x - f₀ x) * w i x ∂μ| ≤ (eLpNorm (f i - f₀) 2 μ).toReal * B := by
      intro i
      have hmi := (hf i).sub hf₀
      have heq : ∫ x, (f i x - f₀ x) * w i x ∂μ =
          inner ℝ (hmi.toLp (f i - f₀)) ((hw i).toLp (w i)) := by
        rw [← GMTFoundations.integral_inner_eq_L2 hmi (hw i)]
        congr 1
        ext x
        simp [RCLike.inner_apply, mul_comm]
      rw [heq]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [Lp.norm_toLp, Lp.norm_toLp]
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      calc (eLpNorm (w i) 2 μ).toReal ≤ (ENNReal.ofReal B).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hB i)
        _ = B := ENNReal.toReal_ofReal hB0
    have hto : Tendsto (fun i ↦ (eLpNorm (f i - f₀) 2 μ).toReal * B) l (𝓝 0) := by
      have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hfc).mul_const B
      simpa using this
    exact squeeze_zero_norm (fun i ↦ by rw [Real.norm_eq_abs]; exact hbd i) hto
  have := hsmall.add hweak
  rw [zero_add] at this
  exact this.congr fun i ↦ (hsplit i).symm

omit [InnerProductSpace ℝ F] in
/-- Bounded multiplier: if `‖h_i - h₀‖ ≤ c ‖f_i - f₀‖` a.e. then `L²` convergence transfers. -/
theorem tendsto_eLpNorm_of_le_mul {ι G : Type*} [NormedAddCommGroup G] {l : Filter ι}
    {f : ι → X → F} {f₀ : X → F} {h : ι → X → G} {h₀ : X → G} {c : ℝ}
    (hle : ∀ i, ∀ᵐ x ∂μ, ‖h i x - h₀ x‖ ≤ c * ‖f i x - f₀ x‖)
    (hfc : Tendsto (fun i ↦ eLpNorm (f i - f₀) 2 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (h i - h₀) 2 μ) l (𝓝 0) := by
  have hb : ∀ i, eLpNorm (h i - h₀) 2 μ ≤ ENNReal.ofReal c * eLpNorm (f i - f₀) 2 μ :=
    fun i ↦ eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by simpa using hle i) 2
  have ht : Tendsto (fun i ↦ ENNReal.ofReal c * eLpNorm (f i - f₀) 2 μ) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hfc (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ ↦ bot_le) hb

/-- `L¹` convergence against a bounded weight: `∫ b χ_i → ∫ b χ`. -/
theorem tendsto_integral_mul_of_tendsto_L1 {ι : Type*} {l : Filter ι} {b : X → ℝ}
    {χ : ι → X → ℝ} {χ₀ : X → ℝ} (hb : AEStronglyMeasurable b μ) {B : ℝ}
    (hbB : ∀ᵐ x ∂μ, |b x| ≤ B) (hχ : ∀ i, Integrable (χ i) μ) (hχ₀ : Integrable χ₀ μ)
    (hc : Tendsto (fun i ↦ eLpNorm (χ i - χ₀) 1 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, b x * χ i x ∂μ) l (𝓝 (∫ x, b x * χ₀ x ∂μ)) := by
  have hint : ∀ i, Integrable (fun x ↦ b x * χ i x) μ := fun i ↦
    (hχ i).bdd_mul hb (hbB.mono fun x hx ↦ by rwa [Real.norm_eq_abs])
  have hint₀ : Integrable (fun x ↦ b x * χ₀ x) μ :=
    hχ₀.bdd_mul hb (hbB.mono fun x hx ↦ by rwa [Real.norm_eq_abs])
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) (?_ : Tendsto (fun i ↦
    B * (eLpNorm (χ i - χ₀) 1 μ).toReal) l (𝓝 0))
  · rw [← integral_sub (hint i) hint₀]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h1 : ∫ x, ‖b x * χ i x - b x * χ₀ x‖ ∂μ ≤ ∫ x, B * ‖χ i x - χ₀ x‖ ∂μ := by
      refine integral_mono_ae ((hint i).sub hint₀).norm
        (((hχ i).sub hχ₀).norm.const_mul B) ?_
      filter_upwards [hbB] with x hx
      rw [← mul_sub, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    refine h1.trans (le_of_eq ?_)
    rw [integral_const_mul]
    change B * ∫ a, ‖(χ i - χ₀) a‖ ∂μ = _
    rw [integral_norm_eq_lintegral_enorm ((hχ i).sub hχ₀).1, eLpNorm_one_eq_lintegral_enorm]
  · have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc).const_mul B
    simpa using this

end L2

section Field

variable {d : ℕ}

theorem fderivₓ_eq_comp {ξ : E d × ℝ → E d} (hξ : ContDiff ℝ 1 ξ) (p : E d × ℝ) :
    fderivₓ ξ p = (fderiv ℝ ξ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ) := by
  have h1 : HasFDerivAt (fun y : E d ↦ (y, p.2)) (ContinuousLinearMap.inl ℝ (E d) ℝ) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have h2 : HasFDerivAt ξ (fderiv ℝ ξ p) (p.1, p.2) :=
    (hξ.differentiable one_ne_zero p).hasFDerivAt
  exact (h2.comp p.1 h1).fderiv

theorem continuous_fderivₓ {ξ : E d × ℝ → E d} (hξ : ContDiff ℝ 1 ξ) :
    Continuous (fderivₓ ξ) := by
  have : fderivₓ ξ = fun p ↦ (fderiv ℝ ξ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ) :=
    funext (fderivₓ_eq_comp hξ)
  rw [this]
  exact (hξ.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem fderivₓ_eq_zero_of_notMem {ξ : E d × ℝ → E d} {p : E d × ℝ} (hp : p ∉ tsupport ξ) :
    fderivₓ ξ p = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at hp
  have ht : Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝 p) :=
    (continuous_id.prodMk continuous_const).tendsto' p.1 p (by simp)
  have : (fun y : E d ↦ ξ (y, p.2)) =ᶠ[𝓝 p.1] fun _ ↦ (0 : E d) := ht.eventually hp
  rw [fderivₓ, this.fderiv_eq]
  exact fderiv_const_apply _

theorem divₓ_eq_zero_of_notMem {ξ : E d × ℝ → E d} {p : E d × ℝ} (hp : p ∉ tsupport ξ) :
    divₓ ξ p = 0 := by
  simp [divₓ, fderivₓ_eq_zero_of_notMem hp]

theorem paraInnerVarIntegrand_eq_zero_of_notMem {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ}
    {ξ : E d × ℝ → E d} {p : E d × ℝ} (hp : p ∉ tsupport ξ) :
    paraInnerVarIntegrand Q u w χ ξ p = 0 := by
  have hξp : ξ p = 0 := (notMem_tsupport_iff_eventuallyEq.1 hp).self_of_nhds
  simp [paraInnerVarIntegrand, divₓ_eq_zero_of_notMem hp, fderivₓ_eq_zero_of_notMem hp, hξp]

/-- The integrand of (3.3) rewritten as `⟪∇u, M ∇u⟫ + b χ - 2 ⟪ξ, ∇u⟫ w` with
`M = (div ξ) Id - 2 Dξ` and `b = Q² div ξ + ∇(Q²) · ξ`. -/
theorem paraInnerVarIntegrand_eq (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (ξ : E d × ℝ → E d)
    (p : E d × ℝ) :
    paraInnerVarIntegrand Q u w χ ξ p =
      inner ℝ (gradₓ u p) ((divₓ ξ p • ContinuousLinearMap.id ℝ (E d) - (2 : ℝ) • fderivₓ ξ p)
          (gradₓ u p)) +
        (Q p.1 ^ 2 * divₓ ξ p + fderiv ℝ (fun y ↦ Q y ^ 2) p.1 (ξ p)) * χ p -
        2 * (inner ℝ (ξ p) (gradₓ u p) * w p) := by
  simp only [paraInnerVarIntegrand, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, inner_sub_right,
    inner_smul_right, real_inner_self_eq_norm_sq]
  ring

end Field

section Limit

variable {d : ℕ}

/-- **Passage to the limit in (4.2)** (proof of Proposition 4.1(ii)). Let `ξ ∈ C¹_c(Ω)` and
`K = spt ξ`. Assume `∫_Ω paraInnerVarIntegrand Q u_n w_n χ_n ξ = 0` for all `n`, and
* `∇u_n → ∇u` in `L²(K)`,
* `χ_n → χ` in `L¹(K)`, `|χ_n|, |χ| ≤ 1`,
* `w_n ⇀ w` weakly in `L²(Ω)` with `‖w_n‖_{L²(Ω)} ≤ B`,
* `Q` continuous on `K` (through `p ↦ Q p.1`) with `∇(Q²)` bounded on `K`.
Then the limit integrand is integrable on `Ω` and integrates to `0`. -/
theorem paraInnerVar_integral_eq_zero_of_tendsto {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    {Q : E d → ℝ} {v w χ : ℕ → E d × ℝ → ℝ} {u w₀ χ₀ : E d × ℝ → ℝ}
    {ξ : E d × ℝ → E d} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξs : tsupport ξ ⊆ Ω) (hQ : ContinuousOn (fun p : E d × ℝ ↦ Q p.1) (tsupport ξ))
    (hQd : ∃ BD : ℝ, ∀ p ∈ tsupport ξ, ‖fderiv ℝ (fun y ↦ Q y ^ 2) p.1‖ ≤ BD)
    (hid : ∀ n, ∫ p in Ω, paraInnerVarIntegrand Q (v n) (w n) (χ n) ξ p = 0)
    (hg : ∀ n, MemLp (gradₓ (v n)) 2 (volume.restrict (tsupport ξ)))
    (hg₀ : MemLp (gradₓ u) 2 (volume.restrict (tsupport ξ)))
    (hgc : Tendsto (fun n ↦ eLpNorm (gradₓ (v n) - gradₓ u) 2 (volume.restrict (tsupport ξ)))
      atTop (𝓝 0))
    (hχm : ∀ n, AEStronglyMeasurable (χ n) (volume.restrict (tsupport ξ)))
    (hχb : ∀ n p, |χ n p| ≤ 1)
    (hχ₀m : AEStronglyMeasurable χ₀ (volume.restrict (tsupport ξ))) (hχ₀b : ∀ p, |χ₀ p| ≤ 1)
    (hχc : Tendsto (fun n ↦ eLpNorm (χ n - χ₀) 1 (volume.restrict (tsupport ξ))) atTop (𝓝 0))
    (hw : TendstoWeakL2 volume Ω w w₀ atTop) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ n, eLpNorm (w n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal B) :
    Integrable (paraInnerVarIntegrand Q u w₀ χ₀ ξ) (volume.restrict Ω) ∧
      ∫ p in Ω, paraInnerVarIntegrand Q u w₀ χ₀ ξ p = 0 := by
  set K := tsupport ξ with hKdef
  have hK : IsCompact K := hξc
  have hKm : MeasurableSet K := (isClosed_tsupport ξ).measurableSet
  set μ := volume.restrict K with hμ
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hμΩ : (volume.restrict Ω).restrict K = μ := Measure.restrict_restrict_of_subset hξs
  -- the coefficient fields
  set M : E d × ℝ → (E d →L[ℝ] E d) :=
    fun p ↦ divₓ ξ p • ContinuousLinearMap.id ℝ (E d) - (2 : ℝ) • fderivₓ ξ p with hMdef
  have hMc : Continuous M :=
    ((GMTFoundations.continuous_divₓ hξ).smul continuous_const).sub
      (continuous_const.smul (continuous_fderivₓ hξ))
  obtain ⟨BM, hBM⟩ := hK.exists_bound_of_continuousOn hMc.continuousOn
  obtain ⟨Bξ, hBξ⟩ := hK.exists_bound_of_continuousOn hξ.continuous.continuousOn
  obtain ⟨Bdiv, hBdiv⟩ :=
    hK.exists_bound_of_continuousOn (GMTFoundations.continuous_divₓ hξ).continuousOn
  obtain ⟨BQ, hBQ⟩ := hK.exists_bound_of_continuousOn hQ
  obtain ⟨BD, hBD⟩ := hQd
  set b : E d × ℝ → ℝ :=
    fun p ↦ Q p.1 ^ 2 * divₓ ξ p + fderiv ℝ (fun y ↦ Q y ^ 2) p.1 (ξ p) with hbdef
  have hbm : AEStronglyMeasurable b μ := by
    refine ((hQ.aestronglyMeasurable hKm).pow 2).mul
      (GMTFoundations.continuous_divₓ hξ).aestronglyMeasurable |>.add ?_
    have h1 : AEStronglyMeasurable (fun p : E d × ℝ ↦ fderiv ℝ (fun y ↦ Q y ^ 2) p.1) μ :=
      ((measurable_fderiv ℝ (fun y ↦ Q y ^ 2)).comp measurable_fst).aestronglyMeasurable
    exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ h1
      hξ.continuous.aestronglyMeasurable
  have hbb : ∀ᵐ p ∂μ, |b p| ≤ BQ ^ 2 * Bdiv + BD * Bξ := by
    refine ae_restrict_of_forall_mem hKm fun p hp ↦ ?_
    have hQp := hBQ p hp
    have hdp := hBdiv p hp
    have hDp := hBD p hp
    have hξp := hBξ p hp
    simp only [Real.norm_eq_abs] at hQp hdp
    calc |b p| ≤ |Q p.1 ^ 2 * divₓ ξ p| + |fderiv ℝ (fun y ↦ Q y ^ 2) p.1 (ξ p)| :=
          abs_add_le _ _
      _ ≤ BQ ^ 2 * Bdiv + BD * Bξ := by
          gcongr
          · rw [abs_mul, abs_pow]
            gcongr
          · rw [← Real.norm_eq_abs]
            refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
            gcongr
            exact (norm_nonneg _).trans hDp
  -- generic facts for a gradient field `g ∈ L²(K)`
  have hMg : ∀ g : E d × ℝ → E d, MemLp g 2 μ → MemLp (fun p ↦ M p (g p)) 2 μ := by
    intro g hg'
    refine hg'.of_le_mul (c := BM)
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
        hMc.aestronglyMeasurable hg'.1) (ae_restrict_of_forall_mem hKm fun p hp ↦ ?_)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    gcongr
    exact hBM p hp
  have hsg : ∀ g : E d × ℝ → E d, MemLp g 2 μ →
      MemLp (fun p ↦ inner ℝ (ξ p) (g p)) 2 μ := by
    intro g hg'
    refine hg'.of_le_mul (c := Bξ) (hξ.continuous.aestronglyMeasurable.inner hg'.1)
      (ae_restrict_of_forall_mem hKm fun p hp ↦ ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    exact hBξ p hp
  have hχint : ∀ n, Integrable (χ n) μ := fun n ↦
    Integrable.of_bound (hχm n) 1 (Eventually.of_forall fun p ↦ by
      rw [Real.norm_eq_abs]; exact hχb n p)
  have hχ₀int : Integrable χ₀ μ :=
    Integrable.of_bound hχ₀m 1 (Eventually.of_forall fun p ↦ by
      rw [Real.norm_eq_abs]; exact hχ₀b p)
  have hwK : ∀ n, MemLp (w n) 2 μ := fun n ↦ hμΩ ▸ (hw.1 n).restrict K
  have hw₀K : MemLp w₀ 2 μ := hμΩ ▸ hw.2.1.restrict K
  have hBK : ∀ n, eLpNorm (w n) 2 μ ≤ ENNReal.ofReal B := fun n ↦
    (eLpNorm_mono_measure _ (Measure.restrict_mono hξs le_rfl)).trans (hB n)
  -- the integral over `Ω` is the integral over `K`, split into three terms
  set F : (E d × ℝ → E d) → (E d × ℝ → ℝ) → (E d × ℝ → ℝ) → E d × ℝ → ℝ :=
    fun g ww cc p ↦ inner ℝ (g p) (M p (g p)) + b p * cc p - 2 * (inner ℝ (ξ p) (g p) * ww p)
    with hFdef
  have hFeq : ∀ uu ww cc, paraInnerVarIntegrand Q uu ww cc ξ = F (gradₓ uu) ww cc :=
    fun uu ww cc ↦ funext fun p ↦ paraInnerVarIntegrand_eq Q uu ww cc ξ p
  have hint1 : ∀ g, MemLp g 2 μ → Integrable (fun p ↦ inner ℝ (g p) (M p (g p))) μ :=
    fun g hg' ↦ GMTFoundations.integrable_inner_of_memLp hg' (hMg g hg')
  have hint2 : ∀ cc, Integrable cc μ → Integrable (fun p ↦ b p * cc p) μ :=
    fun cc hcc ↦ hcc.bdd_mul hbm (hbb.mono fun p hp ↦ by rwa [Real.norm_eq_abs])
  have hint3 : ∀ g ww, MemLp g 2 μ → MemLp ww 2 μ →
      Integrable (fun p ↦ inner ℝ (ξ p) (g p) * ww p) μ :=
    fun g ww hg' hww ↦ integrable_mul_of_memLp (hsg g hg') hww
  have hFint : ∀ g ww cc, MemLp g 2 μ → MemLp ww 2 μ → Integrable cc μ →
      Integrable (F g ww cc) μ := fun g ww cc hg' hww hcc ↦
    ((hint1 g hg').add (hint2 cc hcc)).sub ((hint3 g ww hg' hww).const_mul 2)
  have hFintegral : ∀ g ww cc, MemLp g 2 μ → MemLp ww 2 μ → Integrable cc μ →
      ∫ p, F g ww cc p ∂μ = (∫ p, inner ℝ (g p) (M p (g p)) ∂μ) + (∫ p, b p * cc p ∂μ) -
        2 * ∫ p, inner ℝ (ξ p) (g p) * ww p ∂μ := by
    intro g ww cc hg' hww hcc
    have h1 : Integrable (fun p ↦ inner ℝ (g p) (M p (g p)) + b p * cc p) μ :=
      (hint1 g hg').add (hint2 cc hcc)
    have h2 : Integrable (fun p ↦ 2 * (inner ℝ (ξ p) (g p) * ww p)) μ :=
      (hint3 g ww hg' hww).const_mul 2
    change ∫ p, (inner ℝ (g p) (M p (g p)) + b p * cc p -
      2 * (inner ℝ (ξ p) (g p) * ww p)) ∂μ = _
    rw [integral_sub h1 h2, integral_add (hint1 g hg') (hint2 cc hcc), integral_const_mul]
  have hΩK : ∀ uu ww cc, ∫ p in Ω, paraInnerVarIntegrand Q uu ww cc ξ p =
      ∫ p, F (gradₓ uu) ww cc p ∂μ := by
    intro uu ww cc
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hΩ.measurableSet hξs
      (fun p hp ↦ paraInnerVarIntegrand_eq_zero_of_notMem hp.2), hFeq]
  -- convergence of the three terms
  have T1 : Tendsto (fun n ↦ ∫ p, inner ℝ (gradₓ (v n) p) (M p (gradₓ (v n) p)) ∂μ) atTop
      (𝓝 (∫ p, inner ℝ (gradₓ u p) (M p (gradₓ u p)) ∂μ)) := by
    refine tendsto_integral_inner_of_tendsto hg hg₀ (fun n ↦ hMg _ (hg n)) (hMg _ hg₀) hgc
      (tendsto_eLpNorm_of_le_mul (c := BM) (fun n ↦ ae_restrict_of_forall_mem hKm fun p hp ↦ ?_)
        hgc)
    rw [← map_sub]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    gcongr
    exact hBM p hp
  have T2 : Tendsto (fun n ↦ ∫ p, b p * χ n p ∂μ) atTop (𝓝 (∫ p, b p * χ₀ p ∂μ)) :=
    tendsto_integral_mul_of_tendsto_L1 hbm hbb hχint hχ₀int hχc
  set s₀ : E d × ℝ → ℝ := fun p ↦ inner ℝ (ξ p) (gradₓ u p) with hs₀
  have hconvw : ∀ ww : E d × ℝ → ℝ, ∫ x in Ω, inner ℝ (ww x) (K.indicator s₀ x) =
      ∫ p, s₀ p * ww p ∂μ := by
    intro ww
    have : (fun x ↦ inner ℝ (ww x) (K.indicator s₀ x)) = K.indicator (fun p ↦ s₀ p * ww p) := by
      ext x
      by_cases hx : x ∈ K <;> simp [hx, RCLike.inner_apply]
    rw [this, integral_indicator hKm, hμΩ]
  have hweak : Tendsto (fun n ↦ ∫ p, s₀ p * w n p ∂μ) atTop (𝓝 (∫ p, s₀ p * w₀ p ∂μ)) := by
    have hφ : MemLp (K.indicator s₀) 2 (volume.restrict Ω) :=
      (memLp_indicator_iff_restrict hKm).2 (hμΩ ▸ hsg _ hg₀)
    have := hw.2.2 _ hφ
    simp only [hconvw] at this
    exact this
  have T3 : Tendsto (fun n ↦ ∫ p, inner ℝ (ξ p) (gradₓ (v n) p) * w n p ∂μ) atTop
      (𝓝 (∫ p, s₀ p * w₀ p ∂μ)) := by
    refine tendsto_integral_mul_of_strong_weak (f := fun n p ↦ inner ℝ (ξ p) (gradₓ (v n) p))
      (fun n ↦ hsg _ (hg n)) (hsg _ hg₀) hwK
      (tendsto_eLpNorm_of_le_mul (c := Bξ) (fun n ↦ ae_restrict_of_forall_mem hKm fun p hp ↦ ?_)
        hgc) B hB0 hBK hweak
    rw [← inner_sub_right, Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    exact hBξ p hp
  have hlim := (T1.add T2).sub (T3.const_mul 2)
  have hzero : ∀ n, (∫ p, inner ℝ (gradₓ (v n) p) (M p (gradₓ (v n) p)) ∂μ) +
      (∫ p, b p * χ n p ∂μ) - 2 * (∫ p, inner ℝ (ξ p) (gradₓ (v n) p) * w n p ∂μ) = 0 := by
    intro n
    rw [← hFintegral _ _ _ (hg n) (hwK n) (hχint n), ← hΩK]
    exact hid n
  have hL := tendsto_nhds_unique (hlim.congr hzero) tendsto_const_nhds
  refine ⟨?_, ?_⟩
  · have hi : IntegrableOn (paraInnerVarIntegrand Q u w₀ χ₀ ξ) K volume := by
      rw [hFeq]
      exact hFint _ _ _ hg₀ hw₀K hχ₀int
    exact hi.of_forall_diff_eq_zero hΩ.measurableSet
      (fun p hp ↦ paraInnerVarIntegrand_eq_zero_of_notMem hp.2)
  · rw [hΩK, hFintegral _ _ _ hg₀ hw₀K hχ₀int]
    exact hL

end Limit

end Inner

end PerronVariational

end
