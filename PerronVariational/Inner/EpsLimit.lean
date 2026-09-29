/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.SemilinearEstimates
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Inner.ChiConverge
import PerronVariational.Inner.Compactness
import PerronVariational.Inner.EpsIdentity
import PerronVariational.Inner.InnerVarEps
import PerronVariational.Inner.PerimeterEps
import PerronVariational.Inner.ReactionBound
import PerronVariational.Inner.StrongConv
import PerronVariational.Inner.StrongGrad
import PerronVariational.Inner.WeakGrad
import PerronVariational.Inner.WeakHeat
import PerronVariational.Inner.WeissTime.ChiEps
import PerronVariational.Registry.FunctionalAnalysis
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Profiles

/-!
# Proposition 4.1: the `ε → 0` inner-variational limit

`Inner.eps_inner_limit : EpsInnerLimitStatement` is **Proposition 4.1** of F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the
Bernoulli one-phase problem*, arXiv:2609.14981. It is assembled from the named steps:
* uniform estimates for arbitrary semilinear solutions (`Inner/SemilinearEstimates.lean`);
* Arzelà–Ascoli compactness (`Inner/Compactness.lean`);
* weak/strong convergence of derivatives, Lemma 4.2 (`Inner/StrongGrad.lean`);
* `χ` convergence and `χ ∈ {0, 1}`, `1_{u>0} ≤ χ`, Lemma 4.3 (`Inner/ChiConverge.lean`);
* passage to the limit in (4.2) (`Inner/EpsIdentity.lean`);
* the weak heat equation (4.5) in `{u > 0}` (`Inner/WeakHeat.lean`);
* the lower-semicontinuity steps of (iii) (this file).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal Gradient

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-! ### Small helpers -/

theorem TendstoLpLoc.comp_tendsto {X F : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [NormedAddCommGroup F] {p : ℝ≥0∞} {μ : Measure X} {Ω : Set X} {f : ℕ → X → F}
    {f₀ : X → F} (h : TendstoLpLoc p μ Ω f f₀ atTop) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) : TendstoLpLoc p μ Ω (fun n ↦ f (φ n)) f₀ atTop :=
  fun K hK hKc ↦ (h K hK hKc).comp hφ

theorem TendstoWeakL2.comp_tendsto {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {μ : Measure X} {Ω : Set X} {f : ℕ → X → F} {f₀ : X → F}
    (h : TendstoWeakL2 μ Ω f f₀ atTop) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    TendstoWeakL2 μ Ω (fun n ↦ f (φ n)) f₀ atTop :=
  ⟨fun n ↦ h.1 (φ n), h.2.1, fun ψ hψ ↦ (h.2.2 ψ hψ).comp hφ⟩

/-- The interior Lipschitz estimate `InteriorLipEst` is monotone in the constant. -/
theorem InteriorLipEst.mono {U : Set (E d)} {u : E d × ℝ → ℝ} {C C' : ℝ}
    (h : InteriorLipEst U u C) (hC : C ≤ C') : InteriorLipEst U u C' := by
  intro x t r hr hr1 hcyl M hM p hp
  have hxt : (x, t) ∈ parCyl x t (2 * r) :=
    ⟨mem_ball_self (by linarith), by simp only [mem_Ioc]; constructor <;> nlinarith⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ hxt)
  exact (h x t r hr hr1 hcyl M hM p hp).trans
    (mul_le_mul_of_nonneg_right hC (by positivity))

/-- `L²(U_∞)` bound from uniform bounds on `U × (0, T]`. -/
theorem lintegral_UInf_le {U : Set (E d)} {f : E d × ℝ → ℝ} {A : ℝ≥0∞}
    (h : ∀ T > 0, ∫⁻ p in U ×ˢ Ioc 0 T, ENNReal.ofReal (f p ^ 2) ≤ A) :
    ∫⁻ p in UInf U, ENNReal.ofReal (f p ^ 2) ≤ A := by
  have hU : UInf U = ⋃ N : ℕ, U ×ˢ Ioc 0 ((N : ℝ) + 1) := by
    ext ⟨x, t⟩
    simp only [UInf, mem_prod, mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · rintro ⟨hx, ht⟩
      obtain ⟨N, hN⟩ := exists_nat_ge t
      exact ⟨N, hx, ht, by linarith⟩
    · rintro ⟨N, hx, ht, -⟩
      exact ⟨hx, ht⟩
  rw [hU, setLIntegral_iUnion_of_directed]
  · exact iSup_le fun N ↦ h _ (by positivity)
  · refine Monotone.directed_le fun m n hmn ↦ prod_mono le_rfl (Ioc_subset_Ioc le_rfl ?_)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith

/-- `eLpNorm f 2 μ ≤ √A` from `∫⁻ f² ≤ A`. -/
theorem eLpNorm_two_le_of_lintegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {A : ℝ≥0∞} (hA : A ≠ ⊤) (h : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ A) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt A.toReal) := by
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, eLpNorm_two_sq,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hA]
  simpa [Real.norm_eq_abs, sq_abs] using h

/-! ### Named limit steps for (iii) -/

/-- The energy bound `∫_U |G|² + Q_max²|U|` written with the `L²(U)` norm of `G`. -/
theorem energyBound_eq (S : Setting d) {G : E d → E d}
    (hG : AEStronglyMeasurable G (volume.restrict S.U)) :
    energyBound S G =
      eLpNorm G 2 (volume.restrict S.U) ^ 2 + ENNReal.ofReal (S.Qmax ^ 2) * volume S.U := by
  have hm : AEMeasurable (fun x ↦ ENNReal.ofReal (‖G x‖ ^ 2)) (volume.restrict S.U) :=
    (hG.norm.aemeasurable.pow_const 2).ennreal_ofReal
  rw [energyBound, eLpNorm_two_sq, ← setLIntegral_const, ← lintegral_add_left' hm]
  congr 1
  ext x
  exact ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)

/-- **Convergence of the energy bounds**: `‖G_i - G₀‖_{L²(U)} → 0` implies
`∫_U |G_i|² + Q_max²|U| → ∫_U |G₀|² + Q_max²|U|`. -/
theorem tendsto_energyBound (S : Setting d) {ι : Type*} {l : Filter ι} {G : ι → E d → E d}
    {G₀ : E d → E d} (hG : ∀ᶠ i in l, MemLp (G i) 2 (volume.restrict S.U))
    (hG₀ : MemLp G₀ 2 (volume.restrict S.U))
    (h : Tendsto (fun i ↦ eLpNorm (G i - G₀) 2 (volume.restrict S.U)) l (𝓝 0)) :
    Tendsto (fun i ↦ energyBound S (G i)) l (𝓝 (energyBound S G₀)) := by
  set μ := volume.restrict S.U with hμ
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable (G i) μ := hG.mono fun i hi ↦ hi.1
  have hfin : eLpNorm G₀ 2 μ ≠ ⊤ := hG₀.2.ne
  have hn : Tendsto (fun i ↦ eLpNorm (G i) 2 μ) l (𝓝 (eLpNorm G₀ 2 μ)) := by
    have hup : Tendsto (fun i ↦ eLpNorm G₀ 2 μ + eLpNorm (G i - G₀) 2 μ) l
        (𝓝 (eLpNorm G₀ 2 μ)) := by
      simpa using tendsto_const_nhds.add h
    have hlo : Tendsto (fun i ↦ eLpNorm G₀ 2 μ - eLpNorm (G i - G₀) 2 μ) l
        (𝓝 (eLpNorm G₀ 2 μ)) := by
      simpa using ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl hfin)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [hmeas] with i hi
      rw [tsub_le_iff_right]
      calc eLpNorm G₀ 2 μ = eLpNorm (G i - (G i - G₀)) 2 μ := by rw [sub_sub_cancel]
        _ ≤ eLpNorm (G i) 2 μ + eLpNorm (G i - G₀) 2 μ :=
          eLpNorm_sub_le hi (hi.sub hG₀.1) (by norm_num)
    · filter_upwards [hmeas] with i hi
      calc eLpNorm (G i) 2 μ = eLpNorm (G₀ + (G i - G₀)) 2 μ := by rw [add_sub_cancel]
        _ ≤ _ := eLpNorm_add_le hG₀.1 (hi.sub hG₀.1) (by norm_num)
  have hlim := (ENNReal.Tendsto.pow (n := 2) hn).add_const
    (ENNReal.ofReal (S.Qmax ^ 2) * volume S.U)
  rw [energyBound_eq S hG₀.1]
  exact hlim.congr' (hmeas.mono fun i hi ↦ (energyBound_eq S hi).symm)

theorem ennreal_le_of_half_le {a b : ℝ≥0∞} (h : a / 2 ≤ b / 2) : a ≤ b :=
  calc a = a / 2 * 2 := (ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
    _ ≤ b / 2 * 2 := mul_le_mul_left h 2
    _ = b := ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

theorem ennreal_le_liminf_add (a b : ℕ → ℝ≥0∞) :
    liminf a atTop + liminf b atTop ≤ liminf (fun n ↦ a n + b n) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  rw [ENNReal.iSup_add_iSup_of_monotone]
  · exact iSup_mono fun n ↦ le_iInf₂ fun i hi ↦ add_le_add (iInf₂_le i hi) (iInf₂_le i hi)
  · exact fun m n hmn ↦ biInf_mono fun i hi ↦ le_trans hmn hi
  · exact fun m n hmn ↦ biInf_mono fun i hi ↦ le_trans hmn hi

theorem ennreal_half_add_eq (x y : ℝ≥0∞) : x / 2 + y = (x + 2 * y) / 2 := by
  rw [ENNReal.add_div, mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

/-- Weak `L²` convergence restricts to measurable subsets. -/
theorem TendstoWeakL2.mono_set {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {μ : Measure X} {Ω Ω' : Set X} {f : ℕ → X → F} {f₀ : X → F}
    (h : TendstoWeakL2 μ Ω f f₀ atTop) (hΩ' : Ω' ⊆ Ω) (hm : MeasurableSet Ω') :
    TendstoWeakL2 μ Ω' f f₀ atTop := by
  have hle : μ.restrict Ω' ≤ μ.restrict Ω := Measure.restrict_mono hΩ' le_rfl
  refine ⟨fun i ↦ (h.1 i).mono_measure hle, h.2.1.mono_measure hle, fun φ hφ ↦ ?_⟩
  have hφ' : MemLp (Ω'.indicator φ) 2 (μ.restrict Ω) :=
    (memLp_indicator_iff_restrict hm).2 (by rwa [Measure.restrict_restrict_of_subset hΩ'])
  have key : ∀ g : X → F, ∫ x in Ω, inner ℝ (g x) (Ω'.indicator φ x) ∂μ =
      ∫ x in Ω', inner ℝ (g x) (φ x) ∂μ := by
    intro g
    have : (fun x ↦ inner ℝ (g x) (Ω'.indicator φ x)) =
        Ω'.indicator (fun x ↦ inner ℝ (g x) (φ x)) := by
      ext x
      by_cases hx : x ∈ Ω' <;> simp [hx]
    rw [this, integral_indicator hm, Measure.restrict_restrict_of_subset hΩ']
  have := h.2.2 _ hφ'
  simp only [key] at this
  exact this

/-- **Dissipation inequality in the limit** (proof of Proposition 4.1(iii): "follows from
(3.8) and weak lower semi-continuity of the energy"). If the `v_n` satisfy (3.8) with bounds
`E n → E0` (`E n ≤ E1 < ∞`), their time slices are differentiable with `∇ₓv_n` continuous on `U_∞`,
`v_n → u` locally uniformly on `U_∞` (`u` locally Lipschitz in space), `0 ≤ χ_n` continuous on
`U_∞`, `χ_n → χ` a.e. on `U_∞` (`0 ≤ χ` measurable) and `∂ₜv_n ⇀ w` weakly in `L²(U_∞)`, then
`(u, w, χ)` satisfies (3.11) with bound `E0`. (For each `T`, `∇v_n(·, T) ⇀ ∇u(·, T)` weakly in
`L²(U)`; Fatou for the `χ` term on a.e. slice; weak lower semicontinuity of the weighted `L²`
norm, from gmt-foundations v0.1.0, for the gradient and for `w`.) -/
theorem dissipationIneq_of_tendsto (S : Setting d) {v χ : ℕ → E d × ℝ → ℝ}
    {u w χ₀ : E d × ℝ → ℝ} {En : ℕ → ℝ≥0∞} {E0 E1 : ℝ≥0∞} (hE1 : E1 ≠ ⊤) (hEb : ∀ n, En n ≤ E1)
    (hvd : ∀ n, ∀ t > 0, DifferentiableOn ℝ (fun x ↦ v n (x, t)) S.U)
    (hvg : ∀ n, ContinuousOn (gradₓ (v n)) (UInf S.U))
    (hdiss : ∀ n, ∀ T > 0,
      energyJχ S.U S.Q (fun x ↦ gradₓ (v n) (x, T)) (fun x ↦ χ n (x, T)) / 2 +
        ∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ (v n) p ^ 2) ≤ En n / 2)
    (hE : Tendsto En atTop (𝓝 E0)) (hconv : TendstoLocallyUniformlyOn v u atTop (UInf S.U))
    (hulip : LocLipₓ (UInf S.U) u)
    (hχc : ∀ n, ContinuousOn (χ n) (UInf S.U)) (hχ0 : ∀ n p, 0 ≤ χ n p)
    (hχ₀0 : ∀ p, 0 ≤ χ₀ p)
    (hχ : ∀ᵐ p ∂(volume.restrict (UInf S.U)), Tendsto (fun n ↦ χ n p) atTop (𝓝 (χ₀ p)))
    (hw : TendstoWeakL2 volume (UInf S.U) (fun n ↦ dₜ (v n)) w atTop) :
    DissipationIneq S.U S.Q u w χ₀ E0 := by
  have hU := S.isOpen
  have hUm : MeasurableSet S.U := hU.measurableSet
  obtain ⟨LQ, hLQ⟩ := S.lip
  have hQc : ContinuousOn S.Q S.U := hLQ.continuousOn.mono subset_closure
  -- a.e. convergence of `χ_n` on a.e. time slice
  have hχs : ∀ᵐ T ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ x ∂(volume.restrict S.U),
      Tendsto (fun n ↦ χ n (x, T)) atTop (𝓝 (χ₀ (x, T))) := by
    rw [show volume.restrict (UInf S.U) =
      (volume.restrict S.U).prod (volume.restrict (Ioi (0 : ℝ))) from
      volume_restrict_prod _ _] at hχ
    exact Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
      (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict S.U)).quasiMeasurePreserving.ae
      hχ)
  -- splitting the energy
  have hsplit : ∀ (G : E d → E d) (c : E d → ℝ), Measurable G → (∀ x, 0 ≤ c x) →
      energyJχ S.U S.Q G c = (∫⁻ x in S.U, ENNReal.ofReal (‖G x‖ ^ 2)) +
        ∫⁻ x in S.U, ENNReal.ofReal (S.Q x ^ 2 * c x) := by
    intro G c hG hc
    have hm : Measurable fun x ↦ ENNReal.ofReal (‖G x‖ ^ 2) :=
      (hG.norm.pow_const 2).ennreal_ofReal
    rw [energyJχ, ← lintegral_add_left hm]
    refine lintegral_congr fun x ↦ ?_
    exact ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hc x))
  filter_upwards [hχs, ae_restrict_mem measurableSet_Ioi] with T hT hTpos
  have hTpos : 0 < T := hTpos
  set A : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ x in S.U, ENNReal.ofReal (‖gradₓ (v n) (x, T)‖ ^ 2) with hA
  set B : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ x in S.U, ENNReal.ofReal (S.Q x ^ 2 * χ n (x, T)) with hB
  set C : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ (v n) p ^ 2) with hC
  have hgm : ∀ f : E d × ℝ → ℝ, Measurable fun x ↦ gradₓ f (x, T) := fun f ↦
    GMTFoundations.measurable_gradient (fun y ↦ f (y, T))
  have hn : ∀ n, A n + B n + 2 * C n ≤ En n := by
    intro n
    have h := hdiss n T hTpos
    rw [hsplit _ _ (hgm _) (fun x ↦ hχ0 n _), ennreal_half_add_eq] at h
    exact ennreal_le_of_half_le h
  -- the gradient term
  have hmaps : MapsTo (fun x : E d ↦ (x, T)) S.U (UInf S.U) := fun x hx ↦ ⟨hx, hTpos⟩
  have hsc : ContinuousOn (fun x : E d ↦ (x, T)) S.U :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hAlim : ∫⁻ x in S.U, ENNReal.ofReal (‖gradₓ u (x, T)‖ ^ 2) ≤ liminf A atTop := by
    have hweak := tendstoWeakL2_gradient_of_tendsto hU
      (fun n ↦ locallyLipschitzOn_of_gradient hU (hvd n T hTpos) ((hvg n).comp hsc hmaps))
      (hulip.locallyLipschitzOn_slice hTpos) (hconv.comp _ hmaps hsc) hE1
      (fun n ↦ le_trans (le_self_add.trans le_self_add) ((hn n).trans (hEb n)))
    have h := Registry.lintegral_weighted_sq_le_liminf volume S.U _ _ hweak (fun _ ↦ 1)
      measurable_const (fun _ ↦ zero_le_one) 1 (fun _ ↦ le_rfl)
    simp only [one_mul] at h
    exact h
  -- the `χ` term (Fatou)
  have hBlim : ∫⁻ x in S.U, ENNReal.ofReal (S.Q x ^ 2 * χ₀ (x, T)) ≤ liminf B atTop := by
    calc ∫⁻ x in S.U, ENNReal.ofReal (S.Q x ^ 2 * χ₀ (x, T))
        = ∫⁻ x in S.U, liminf (fun n ↦ ENNReal.ofReal (S.Q x ^ 2 * χ n (x, T))) atTop := by
          refine lintegral_congr_ae (hT.mono fun x hx ↦ ?_)
          exact (((ENNReal.continuous_ofReal.tendsto _).comp
            (hx.const_mul (S.Q x ^ 2))).liminf_eq).symm
      _ ≤ liminf B atTop := by
          refine lintegral_liminf_le' fun n ↦ ?_
          exact ((((hQc.pow 2).mul ((hχc n).comp hsc hmaps)).aestronglyMeasurable
            hUm).aemeasurable).ennreal_ofReal
  -- the dissipation term
  have hClim : ∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (w p ^ 2) ≤ liminf C atTop := by
    have hw' := TendstoWeakL2.mono_set (Ω' := S.U ×ˢ Ioc 0 T) hw
      (prod_mono le_rfl (Ioc_subset_Ioi_self))
      (hUm.prod measurableSet_Ioc)
    have h := Registry.lintegral_weighted_sq_le_liminf volume _ _ _ hw' (fun _ ↦ 1)
      measurable_const (fun _ ↦ zero_le_one) 1 (fun _ ↦ le_rfl)
    simpa only [one_mul, Real.norm_eq_abs, sq_abs] using h
  have htot : (∫⁻ x in S.U, ENNReal.ofReal (‖gradₓ u (x, T)‖ ^ 2)) +
      (∫⁻ x in S.U, ENNReal.ofReal (S.Q x ^ 2 * χ₀ (x, T))) +
      2 * (∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (w p ^ 2)) ≤ E0 := by
    calc _ ≤ liminf A atTop + liminf B atTop + 2 * liminf C atTop := by gcongr
      _ = liminf A atTop + liminf B atTop + liminf (fun n ↦ 2 * C n) atTop := by
          rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofNat_ne_top]
      _ ≤ liminf (fun n ↦ A n + B n) atTop + liminf (fun n ↦ 2 * C n) atTop := by
          gcongr
          exact ennreal_le_liminf_add A B
      _ ≤ liminf (fun n ↦ A n + B n + 2 * C n) atTop := ennreal_le_liminf_add _ _
      _ ≤ liminf En atTop := liminf_le_liminf (Eventually.of_forall fun n ↦ hn n)
      _ = E0 := hE.liminf_eq
  rw [hsplit _ _ (hgm _) (fun x ↦ hχ₀0 _), ennreal_half_add_eq]
  exact ENNReal.div_le_div_right htot 2

/-- **(3.12) in the limit** (proof of Proposition 4.1(iii): the interior Lipschitz bound "passes
to the limit by the locally uniform convergence"). -/
theorem interiorLipEst_of_tendsto {U : Set (E d)} (hU : IsOpen U) {v : ℕ → E d × ℝ → ℝ}
    {u : E d × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hv : ∀ n, InteriorLipEst U (v n) C)
    (hvd : ∀ n, ∀ t > 0, DifferentiableOn ℝ (fun x ↦ v n (x, t)) U)
    (hconv : TendstoLocallyUniformlyOn v u atTop (UInf U)) : InteriorLipEst U u C := by
  intro x t r hr hr1 hcyl M hM p hp
  have hUo : IsOpen (UInf U) := hU.prod isOpen_Ioi
  obtain ⟨hp1, hp2⟩ := hp
  simp only [mem_Ioc] at hp2
  have hxt : (x, t) ∈ parCyl x t (2 * r) :=
    ⟨mem_ball_self (by linarith), by simp only [mem_Ioc]; constructor <;> nlinarith⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ hxt)
  set f : E d → ℝ := fun y ↦ u (y, p.2) with hfdef
  change ‖∇ f p.1‖ ≤ C * (M / r + 1)
  by_cases hdf : ¬ DifferentiableAt ℝ f p.1
  · rw [gradient_eq_zero_of_not_differentiableAt hdf, norm_zero]
    positivity
  rw [norm_gradient_eq_norm_fderiv]
  have hd : dist p.1 x < r := hp1
  have htp : 0 ≤ t - p.2 := by linarith [hp2.2]
  have htp' : t - p.2 < r ^ 2 := by linarith [hp2.1]
  set a := Real.sqrt (t - p.2) with hadef
  have ha : a < r := by
    rw [← Real.sqrt_sq hr.le]
    exact Real.sqrt_lt_sqrt htp htp'
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = t - p.2 := Real.sq_sqrt htp
  set s0 := min (r - dist p.1 x) (r - a) with hs0def
  have hs0 : 0 < s0 := lt_min (by linarith) (by linarith)
  have key : ∀ s ∈ Ioo 0 s0, ‖fderiv ℝ f p.1‖ ≤ C * ((M + s) / (r - s) + 1) := by
    rintro s ⟨hs1, hs2⟩
    have hs2a : s < r - dist p.1 x := hs2.trans_le (min_le_left _ _)
    have hs2b : s < r - a := hs2.trans_le (min_le_right _ _)
    set r' := r - s with hr'def
    have hr'0 : 0 < r' := by linarith
    have hr'r : r' < r := by linarith
    have hr'1 : r' ≤ 1 := by linarith
    have hr'a : a < r' := by linarith
    set Kc : Set (E d × ℝ) := closedBall x (2 * r') ×ˢ Icc (t - (2 * r') ^ 2) t with hKcdef
    have hKc : IsCompact Kc := (isCompact_closedBall _ _).prod isCompact_Icc
    have hKcsub : Kc ⊆ parCyl x t (2 * r) := by
      rintro ⟨y, τ⟩ ⟨hy, hτ⟩
      refine ⟨Metric.closedBall_subset_ball (by linarith) hy, ?_, hτ.2⟩
      have : (2 * r') ^ 2 < (2 * r) ^ 2 := by nlinarith
      linarith [hτ.1]
    have hcyl' : parCyl x t (2 * r') ⊆ Kc := by
      rintro ⟨y, τ⟩ ⟨hy, hτ⟩
      exact ⟨Metric.ball_subset_closedBall hy, hτ.1.le, hτ.2⟩
    have hsmall : ∀ y ∈ ball x r', (y, p.2) ∈ parCyl x t r' := by
      intro y hy
      refine ⟨hy, ?_, hp2.2⟩
      have : a ^ 2 < r' ^ 2 := by nlinarith
      linarith
    have hr'2 : parCyl x t r' ⊆ parCyl x t (2 * r') := by
      rintro ⟨y, τ⟩ ⟨hy, hτ⟩
      refine ⟨Metric.ball_subset_ball (by linarith) hy, ?_, hτ.2⟩
      have : r' ^ 2 ≤ (2 * r') ^ 2 := by nlinarith
      linarith [hτ.1]
    have hmemU : ∀ y ∈ ball x r', (y, p.2) ∈ UInf U := fun y hy ↦
      hcyl (hKcsub (hcyl' (hr'2 (hsmall y hy))))
    have hp1' : p.1 ∈ ball x r' := by
      change dist p.1 x < r'
      linarith
    have hp2pos : 0 < p.2 := (hmemU p.1 hp1').2
    have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hUo).1 hconv Kc
      (hKcsub.trans hcyl) hKc
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) s hs1)
    set Ls := C * ((M + s) / r' + 1) with hLsdef
    have hLs0 : 0 ≤ Ls := by positivity
    have hvlip : ∀ n ≥ N, ∀ y ∈ ball x r', ∀ z ∈ ball x r',
        |v n (y, p.2) - v n (z, p.2)| ≤ Ls * ‖y - z‖ := by
      intro n hn y hy z hz
      have hbnd : ∀ q ∈ parCyl x t (2 * r'), |v n q| ≤ M + s := fun q hq ↦ by
        have h1 := hN n hn q (hcyl' hq)
        have h2 := hM q (hKcsub (hcyl' hq))
        rw [Real.dist_eq] at h1
        have h3 := abs_sub_abs_le_abs_sub (v n q) (u q)
        rw [abs_sub_comm] at h1
        linarith
      have hgrad : ∀ w ∈ ball x r', ‖fderiv ℝ (fun y ↦ v n (y, p.2)) w‖ ≤ Ls := by
        intro w hw
        rw [← norm_gradient_eq_norm_fderiv]
        exact hv n x t r' hr'0 hr'1 ((hcyl'.trans hKcsub).trans hcyl) (M + s) hbnd (w, p.2)
          (hsmall w hw)
      have hdiff : ∀ w ∈ ball x r', DifferentiableAt ℝ (fun y ↦ v n (y, p.2)) w :=
        fun w hw ↦ (hvd n p.2 hp2pos).differentiableAt (hU.mem_nhds (hmemU w hw).1)
      have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hgrad (convex_ball _ _) hz hy
      simpa [Real.norm_eq_abs] using this
    have hulip : LipschitzOnWith (Real.toNNReal Ls) f (ball x r') := by
      refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
      rw [Real.coe_toNNReal _ hLs0, Real.dist_eq, dist_eq_norm]
      have hty : Tendsto (fun n ↦ |v n (y, p.2) - v n (z, p.2)|) atTop (𝓝 |f y - f z|) :=
        ((hconv.tendsto_at (hmemU y hy)).sub (hconv.tendsto_at (hmemU z hz))).abs
      exact le_of_tendsto hty (eventually_atTop.2 ⟨N, fun n hn ↦ hvlip n hn y hy z hz⟩)
    have := norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hp1') hulip
    rwa [Real.coe_toNNReal _ hLs0] at this
  have hcont : ContinuousAt (fun s : ℝ ↦ C * ((M + s) / (r - s) + 1)) 0 :=
    continuousAt_const.mul (((continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) (by simpa using hr.ne')).add continuousAt_const)
  have hlim : Tendsto (fun s : ℝ ↦ C * ((M + s) / (r - s) + 1)) (𝓝[>] 0)
      (𝓝 (C * (M / r + 1))) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT hs0) key)

/-- `Q²` is Lipschitz on `Ū`. -/
theorem exists_lipschitzOnWith_Q_sq (S : Setting d) :
    ∃ K : NNReal, LipschitzOnWith K (fun y ↦ S.Q y ^ 2) (closure S.U) := by
  obtain ⟨L, hL⟩ := S.lip
  refine ⟨Real.toNNReal (2 * S.Qmax) * L, LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
  have hQx := S.Q_mem x hx
  have hQy := S.Q_mem y hy
  have hQ0 := S.Qmin_pos
  have hd := hL.dist_le_mul x hx y hy
  rw [Real.dist_eq] at hd ⊢
  have h1 : S.Q x ^ 2 - S.Q y ^ 2 = (S.Q x + S.Q y) * (S.Q x - S.Q y) := by ring
  rw [h1, abs_mul, NNReal.coe_mul, Real.coe_toNNReal _ (by linarith), mul_assoc]
  have h2 : |S.Q x + S.Q y| ≤ 2 * S.Qmax := by
    rw [abs_of_nonneg (by linarith)]; linarith
  exact mul_le_mul h2 hd (abs_nonneg _) (by linarith)

/-- `χ_ε(u)` is continuous where `u` is. -/
theorem continuousOn_chiEps {β : ℝ → ℝ} (hβ : IsReactionProfile β) (ε : ℝ)
    {u : E d × ℝ → ℝ} {Ω : Set (E d × ℝ)} (hu : ContinuousOn u Ω) :
    ContinuousOn (chiEps β ε u) Ω := by
  have hB : Continuous (bigBEps β ε) :=
    continuous_iff_continuousAt.2 fun z ↦ (hβ.hasDerivAt_bigBEps ε z).continuousAt
  exact (continuous_const.mul hB).comp_continuousOn hu

/-! ### Assembly -/

/-- **Proposition 4.1**, in the form `EpsInnerLimitStatement` (whose docstring records how it
differs from the paper's statement). -/
theorem eps_inner_limit : EpsInnerLimitStatement := by
  intro d S β hβ
  obtain ⟨C₀, ε₁, hε₁, hLip⟩ := semilinear_interiorLipEst S hβ
  obtain ⟨ε₂, hε₂, hTime⟩ := semilinear_time_equicontinuous S hβ
  obtain ⟨ε₃, hε₃, hBeta⟩ := semilinear_betaEps_lintegral_le S hβ
  obtain ⟨ε₄, hε₄, hPer⟩ := semilinear_weightedPerimeterEst S hβ
  refine ⟨max C₀ 0, fun M Ebd hEbd ↦ ?_⟩
  set E1 : ℝ≥0∞ := Ebd + 1 with hE1def
  have hE1 : E1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hEbd, ENNReal.one_ne_top⟩
  obtain ⟨Cper, hCper⟩ := hPer M E1 hE1
  refine ⟨Cper, ?_⟩
  intro ε₀ g Gg gε Gε uε hε₀ hg hgε hH1 hbd hEbd' hsol
  -- convergence of the energy bounds of the data
  have hGconv : Tendsto (fun ε ↦ eLpNorm (Gε ε - Gg) 2 (volume.restrict S.U)) (𝓝[>] 0)
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hH1 (fun _ ↦ bot_le)
      (fun _ ↦ le_add_self)
  have hmemG : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MemLp (Gε ε) 2 (volume.restrict S.U) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hε₀) fun ε hε ↦ (hgε ε hε).2.1
  have hEconv := tendsto_energyBound S hmemG hg.2.1 hGconv
  have hlt : energyBound S Gg < E1 :=
    lt_of_le_of_lt hEbd' (ENNReal.lt_add_right hEbd one_ne_zero)
  obtain ⟨ε₅, hε₅, hε₅E⟩ : ∃ ε₅ : ℝ, 0 < ε₅ ∧ ∀ ε ∈ Ioo 0 ε₅, energyBound S (Gε ε) ≤ E1 := by
    obtain ⟨ε₅, hε₅, h⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hEconv.eventually (gt_mem_nhds hlt))
    exact ⟨ε₅, hε₅, fun ε hε ↦ (h hε).le⟩
  -- the base sequence `e n ↓ 0`
  set ε' : ℝ := min (min ε₀ ε₁) (min (min ε₂ ε₃) (min ε₄ ε₅)) with hε'def
  have hε'pos : 0 < ε' := lt_min (lt_min hε₀ hε₁) (lt_min (lt_min hε₂ hε₃) (lt_min hε₄ hε₅))
  set e : ℕ → ℝ := fun n ↦ ε' / ((n : ℝ) + 2) with hedef
  have he_pos : ∀ n, 0 < e n := fun n ↦ div_pos hε'pos (by positivity)
  have he_lt : ∀ n, e n < ε' := fun n ↦
    div_lt_self hε'pos (by have := n.cast_nonneg (α := ℝ); linarith)
  have he_anti : StrictAnti e := by
    intro m n hmn
    have : (m : ℝ) < n := by exact_mod_cast hmn
    exact div_lt_div_of_pos_left hε'pos (by positivity) (by linarith)
  have he0 : Tendsto e atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hmem : ∀ n, ∀ {a : ℝ}, 0 < a → ε' ≤ a → e n ∈ Ioo 0 a := fun n a _ ha ↦
    ⟨he_pos n, (he_lt n).trans_le ha⟩
  have he₀ : ∀ n, e n ∈ Ioo 0 ε₀ := fun n ↦ hmem n hε₀ ((min_le_left _ _).trans (min_le_left _ _))
  have he₁ : ∀ n, e n ∈ Ioo 0 ε₁ := fun n ↦ hmem n hε₁ ((min_le_left _ _).trans (min_le_right _ _))
  have he₂ : ∀ n, e n ∈ Ioo 0 ε₂ := fun n ↦ hmem n hε₂
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have he₃ : ∀ n, e n ∈ Ioo 0 ε₃ := fun n ↦ hmem n hε₃
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have he₄ : ∀ n, e n ∈ Ioo 0 ε₄ := fun n ↦ hmem n hε₄
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he₅ : ∀ n, e n ∈ Ioo 0 ε₅ := fun n ↦ hmem n hε₅
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- the base sequence of solutions and its properties
  set v : ℕ → E d × ℝ → ℝ := fun n ↦ uε (e n) with hvdef
  have hsolv : ∀ n, IsSemilinearSolution S.U S.Q β (e n) (gε (e n)) (v n) :=
    fun n ↦ hsol _ (he₀ n)
  have hH1n : ∀ n, MemH1 S.U (gε (e n)) (Gε (e n)) := fun n ↦ hgε _ (he₀ n)
  have hEn : ∀ n, energyBound S (Gε (e n)) ≤ E1 := fun n ↦ hε₅E _ (he₅ n)
  have hgM : ∀ n, ∀ x ∈ S.U, 0 ≤ gε (e n) x ∧ gε (e n) x ≤ M := fun n ↦ hbd _ (he₀ n)
  have hUInf_sub : UInf S.U ⊆ closure S.U ×ˢ Ici (0 : ℝ) :=
    prod_mono subset_closure Ioi_subset_Ici_self
  have hvbd : ∀ n, ∀ q ∈ UInf S.U, 0 ≤ v n q ∧ v n q ≤ max M ε' := fun n q hq ↦ by
    have h := semilinear_nonneg_le_max S hβ (he_pos n) (hsolv n) (hgM n) q (hUInf_sub hq)
    exact ⟨h.1, h.2.trans (max_le_max le_rfl (he_lt n).le)⟩
  have hlipn : ∀ n, InteriorLipEst S.U (v n) (max C₀ 0) := fun n ↦
    InteriorLipEst.mono (hLip _ (he₁ n) M _ _ (hsolv n) (hgM n)) (le_max_left _ _)
  have hvd : ∀ n, ∀ t > 0, DifferentiableOn ℝ (fun x ↦ v n (x, t)) S.U := fun n t ht ↦
    ((hsolv n).2.1.2.1 t ht).differentiableOn (by norm_num)
  have hvc : ∀ n, ContinuousOn (v n) (UInf S.U) := fun n ↦ (hsolv n).2.1.1
  have htime : ∀ p ∈ UInf S.U, ∀ η > 0, ∃ δ > 0, ∀ n, ∀ s : ℝ, |s - p.2| < δ →
      |v n (p.1, s) - v n p| < η := by
    intro p hp η hη
    obtain ⟨δ, hδ, h⟩ := hTime M E1 hE1 p hp η hη
    exact ⟨δ, hδ, fun n s hs ↦ h _ (he₂ n) _ _ _ (hH1n n) (hEn n) (hsolv n) (hgM n) s hs⟩
  -- Step A: locally uniform limit
  obtain ⟨φ₁, hφ₁, u, hucont, hconv₁, hubd, hulip⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_of_lip S.isOpen hlipn hvd hvc hvbd htime
  -- Step B: weak limit of the time derivatives
  have hdiss : ∀ n, ∀ T > 0,
      energyJχ S.U S.Q (fun x ↦ gradₓ (v n) (x, T)) (fun x ↦ chiEps β (e n) (v n) (x, T)) / 2 +
        ∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ (v n) p ^ 2) ≤ E1 / 2 := fun n T hT ↦
    (semilinear_dissipation S hβ (he_pos n) (hH1n n) (hsolv n) T hT).trans
      (ENNReal.div_le_div_right (hEn n) 2)
  have hE1h : E1 / 2 ≠ ⊤ := ENNReal.div_ne_top hE1 two_ne_zero
  have hdtL2 : ∀ n, ∫⁻ p in UInf S.U, ENNReal.ofReal (dₜ (v n) p ^ 2) ≤ E1 / 2 := fun n ↦
    lintegral_UInf_le fun T hT ↦ le_trans le_add_self (hdiss n T hT)
  set B : ℝ := Real.sqrt (E1 / 2).toReal with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hdtB : ∀ n, eLpNorm (dₜ (v n)) 2 (volume.restrict (UInf S.U)) ≤ ENNReal.ofReal B :=
    fun n ↦ eLpNorm_two_le_of_lintegral hE1h (hdtL2 n)
  have hUInfm : MeasurableSet (UInf S.U) := S.isOpen.measurableSet.prod measurableSet_Ioi
  have hUInfo : IsOpen (UInf S.U) := S.isOpen.prod isOpen_Ioi
  have hdtc : ∀ n, ContinuousOn (dₜ (v n)) (UInf S.U) := fun n ↦ (hsolv n).2.1.2.2.2.2.2.1
  have hdtmem : ∀ n, MemLp (dₜ (v n)) 2 (volume.restrict (UInf S.U)) := fun n ↦
    ⟨(hdtc n).aestronglyMeasurable hUInfm, (hdtB n).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨φ₂, hφ₂, w, hw₂⟩ := Registry.exists_tendstoWeakL2_subseq volume (UInf S.U)
    (fun n ↦ dₜ (v (φ₁ n))) B (fun n ↦ hdtmem _) (fun n ↦ hdtB _)
  set ψ : ℕ → ℕ := fun n ↦ φ₁ (φ₂ n) with hψdef
  have hψ : StrictMono ψ := hφ₁.comp hφ₂
  have hconv₂ : TendstoLocallyUniformlyOn (fun n ↦ v (ψ n)) u atTop (UInf S.U) :=
    TendstoLocallyUniformlyOn.comp_tendsto hconv₁ hφ₂.tendsto_atTop
  -- Step C: identification of `∂ₜu` and weak convergence of `∇v_n`
  have hwu : HasWeakTimeDeriv (UInf S.U) u w :=
    hasWeakTimeDeriv_of_tendsto S.isOpen (fun n p hp ↦ (hsolv (ψ n)).2.1.2.2.2.2.1 p hp)
      (fun n ↦ hvc _) (fun n ↦ hdtc _) hconv₂ hucont hw₂
  have hslice : ∀ n, ∀ t > 0,
      ∫⁻ x in S.U, ENNReal.ofReal (‖gradₓ (v n) (x, t)‖ ^ 2) ≤ E1 := by
    intro n t ht
    refine le_trans (b := energyJχ S.U S.Q (fun x ↦ gradₓ (v n) (x, t))
      (fun x ↦ chiEps β (e n) (v n) (x, t))) (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
      (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _)
        (chiEps_mem_Icc hβ (he_pos n) (v n) (x, t)).1))) (ennreal_le_of_half_le ?_)
    exact le_trans le_self_add (hdiss n t ht)
  have hgradw : ∀ T > 0, TendstoWeakL2 volume (S.U ×ˢ Ioo 0 T) (fun n ↦ gradₓ (v (ψ n)))
      (gradₓ u) atTop :=
    tendstoWeakL2_gradₓ S.isOpen (fun n ↦ hvd _) (fun n ↦ (hsolv _).2.1.2.2.1) hconv₂ hucont
      hulip hE1 (fun n ↦ hslice _)
  -- Step D: strong convergence of `∇v_n` (Lemma 4.2)
  have hstrong : TendstoLpLoc 2 volume (UInf S.U) (fun n ↦ gradₓ (v (ψ n))) (gradₓ u) atTop :=
    tendstoLpLoc_gradₓ_semilinear S hβ (ε := fun n ↦ e (ψ n)) (fun n ↦ he_pos _)
      (he0.comp hψ.tendsto_atTop) (fun n ↦ (hsolv _).2.1) (fun n q hq ↦ (hvbd _ q hq).1) hconv₂
      hucont hulip hgradw hE1 (fun n ↦ hslice _) hw₂ hB0 (fun n ↦ hdtB _)
  -- Step E: `L¹_loc` and a.e. convergence of `χ_ε` (Lemma 4.3)
  have hχcont : ∀ n, ContinuousOn (chiEps β (e n) (v n)) (UInf S.U) := fun n ↦
    continuousOn_chiEps hβ _ (hvc n)
  obtain ⟨φ₃, hφ₃, χ₀, hχ₀m, hχ₃⟩ := exists_tendstoLpLoc_chiEps_subseq S hβ
    (ε := fun n ↦ e (ψ n)) (g := fun n ↦ gε (e (ψ n))) (G := fun n ↦ Gε (e (ψ n)))
    (v := fun n ↦ v (ψ n)) (u := u) (M := M) (fun n ↦ he_pos _) (he0.comp hψ.tendsto_atTop) hE1
    (fun n ↦ hsolv _) (fun n ↦ hH1n _) (fun n ↦ hEn _) (fun n ↦ hgM _) hconv₂ hstrong
    hucont hulip
  obtain ⟨φ₄, hφ₄, hae₄⟩ := exists_subseq_ae_tendsto_of_tendstoLpLoc hUInfo
    (fun n ↦ (hχcont _).aestronglyMeasurable hUInfm) hχ₀m.aestronglyMeasurable hχ₃
  set Φ : ℕ → ℕ := fun n ↦ ψ (φ₃ (φ₄ n)) with hΦdef
  have hΦ : StrictMono Φ := (hψ.comp hφ₃).comp hφ₄
  have hφ34 : Tendsto (fun n ↦ φ₃ (φ₄ n)) atTop atTop := (hφ₃.comp hφ₄).tendsto_atTop
  have heΦ : Tendsto (fun n ↦ e (Φ n)) atTop (𝓝 0) := he0.comp hΦ.tendsto_atTop
  -- Step F: `χ ∈ {0, 1}` and the Borel representative `χ`
  have hzo : ∀ᵐ p ∂(volume.restrict (UInf S.U)), χ₀ p = 0 ∨ χ₀ p = 1 :=
    ae_zero_or_one_of_tendsto hβ hUInfo (ε := fun n ↦ e (Φ n)) (v := fun n ↦ v (Φ n))
      (fun n ↦ he_pos _) heΦ (fun n ↦ hvc _) hae₄ fun K hK hKc ↦ by
        obtain ⟨Cb, hCb⟩ := hBeta M E1 hE1 K hK hKc
        exact ⟨Cb, fun n ↦ hCb _ (he₃ _) _ _ _ (hH1n _) (hEn _) (hsolv _) (hgM _)⟩
  set χ : E d × ℝ → ℝ := {p | χ₀ p = 1}.indicator 1 with hχdef
  have hχm : Measurable χ :=
    measurable_const.indicator (measurableSet_eq_fun hχ₀m measurable_const)
  have hχeq : χ =ᵐ[volume.restrict (UInf S.U)] χ₀ := by
    filter_upwards [hzo] with p hp
    rcases hp with hp | hp <;> simp [χ, hp]
  have hχ01 : ∀ p, χ p = 0 ∨ χ p = 1 := fun p ↦ by
    by_cases hp : χ₀ p = 1 <;> simp [χ, hp]
  have hχb : ∀ p, |χ p| ≤ 1 := fun p ↦ by rcases hχ01 p with h | h <;> simp [h]
  -- convergences along the final subsequence
  have hconvΦ : TendstoLocallyUniformlyOn (fun n ↦ v (Φ n)) u atTop (UInf S.U) :=
    TendstoLocallyUniformlyOn.comp_tendsto hconv₂ hφ34
  have hstrongΦ : TendstoLpLoc 2 volume (UInf S.U) (fun n ↦ gradₓ (v (Φ n))) (gradₓ u) atTop :=
    TendstoLpLoc.comp_tendsto hstrong hφ34
  have hgradwΦ : ∀ T > 0, TendstoWeakL2 volume (S.U ×ˢ Ioo 0 T) (fun n ↦ gradₓ (v (Φ n)))
      (gradₓ u) atTop := fun T hT ↦ TendstoWeakL2.comp_tendsto (hgradw T hT) hφ34
  have hwΦ : TendstoWeakL2 volume (UInf S.U) (fun n ↦ dₜ (v (Φ n))) w atTop :=
    TendstoWeakL2.comp_tendsto hw₂ hφ34
  have hχL1 : TendstoLpLoc 1 volume (UInf S.U) (fun n ↦ chiEps β (e (Φ n)) (v (Φ n))) χ
      atTop := by
    intro K hK hKc
    refine ((hχ₃ K hK hKc).comp hφ₄.tendsto_atTop).congr fun n ↦ eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hK hχeq] with p hp
    rw [Pi.sub_apply, Pi.sub_apply, hp]
  have hχae : ∀ᵐ p ∂(volume.restrict (UInf S.U)),
      Tendsto (fun n ↦ chiEps β (e (Φ n)) (v (Φ n)) p) atTop (𝓝 (χ p)) := by
    filter_upwards [hae₄, hχeq] with p hp hpe
    rw [hpe]
    exact hp
  have hχloc : LocallyIntegrableOn χ (UInf S.U) volume :=
    (locallyIntegrableOn_iff hUInfo.isLocallyClosed).2 fun k _ hkc ↦
      IntegrableOn.of_bound hkc.measure_lt_top hχm.aestronglyMeasurable 1
        (Eventually.of_forall fun p ↦ by rw [Real.norm_eq_abs]; exact hχb p)
  have hgu : ∀ K ⊆ UInf S.U, IsCompact K → MemLp (gradₓ u) 2 (volume.restrict K) := by
    intro K hKs hK
    obtain ⟨T0, hT0⟩ := (hK.image continuous_snd).bddAbove
    have hsub : K ⊆ S.U ×ˢ Ioo 0 (max T0 0 + 1) := fun p hp ↦
      ⟨(hKs hp).1, (hKs hp).2, by
        have := hT0 (mem_image_of_mem _ hp)
        linarith [le_max_left T0 0]⟩
    have := ((hgradw (max T0 0 + 1) (by positivity)).2.1).restrict K
    rwa [Measure.restrict_restrict_of_subset hsub] at this
  -- the inner variation identity in the limit
  obtain ⟨KQ, hKQ⟩ := exists_lipschitzOnWith_Q_sq S
  have hid : ∀ ξ : E d × ℝ → E d, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ UInf S.U →
      Integrable (paraInnerVarIntegrand S.Q u w χ ξ) (volume.restrict (UInf S.U)) ∧
        ∫ p in UInf S.U, paraInnerVarIntegrand S.Q u w χ ξ p = 0 := by
    intro ξ hξ hξc hξs
    have hK : IsCompact (tsupport ξ) := hξc
    have hKm : MeasurableSet (tsupport ξ) := (isClosed_tsupport ξ).measurableSet
    haveI : IsFiniteMeasure (volume.restrict (tsupport ξ)) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    obtain ⟨LQ, hLQ⟩ := S.lip
    have hQc : ContinuousOn (fun p : E d × ℝ ↦ S.Q p.1) (tsupport ξ) :=
      hLQ.continuousOn.comp continuous_fst.continuousOn
        (fun p hp ↦ subset_closure (hξs hp).1)
    have hQd : ∃ BD : ℝ, ∀ p ∈ tsupport ξ, ‖fderiv ℝ (fun y ↦ S.Q y ^ 2) p.1‖ ≤ BD :=
      ⟨KQ, fun p hp ↦ norm_fderiv_le_of_lipschitzOn ℝ
        (Filter.mem_of_superset (S.isOpen.mem_nhds (hξs hp).1) subset_closure) hKQ⟩
    have hg : ∀ n, MemLp (gradₓ (v (Φ n))) 2 (volume.restrict (tsupport ξ)) := by
      intro n
      have hc : ContinuousOn (gradₓ (v (Φ n))) (tsupport ξ) :=
        (hsolv (Φ n)).2.1.2.2.1.mono hξs
      obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn hc
      exact MemLp.of_bound (hc.aestronglyMeasurable hKm) Cg (ae_restrict_of_forall_mem hKm hCg)
    have hg₀ : MemLp (gradₓ u) 2 (volume.restrict (tsupport ξ)) := hgu _ hξs hK
    have hχn : ∀ n p, |chiEps β (e (Φ n)) (v (Φ n)) p| ≤ 1 := fun n p ↦ by
      have h := chiEps_mem_Icc hβ (he_pos (Φ n)) (v (Φ n)) p
      exact abs_le.2 ⟨by linarith [h.1], h.2⟩
    exact paraInnerVar_integral_eq_zero_of_tendsto hUInfo hξ hξc hξs hQc hQd
      (fun n ↦ (semilinear_innerVar_identity S hβ (he_pos _) (hsolv _) ξ hξ hξc hξs).2)
      hg hg₀ (hstrongΦ _ hξs hK)
      (fun n ↦ ((hχcont _).mono hξs).aestronglyMeasurable hKm) hχn
      hχm.aestronglyMeasurable hχb (hχL1 _ hξs hK) hwΦ B hB0 (fun n ↦ hdtB _)
  have hEΦ : Tendsto (fun n ↦ energyBound S (Gε (e (Φ n)))) atTop (𝓝 (energyBound S Gg)) :=
    hEconv.comp (tendsto_nhdsWithin_iff.2 ⟨heΦ, Eventually.of_forall fun n ↦ he_pos _⟩)
  refine ⟨fun n ↦ e (Φ n), u, w, χ, fun n ↦ he₀ _, he_anti.comp_strictMono hΦ, heΦ, hconvΦ,
    hgradwΦ, hχL1, hχae, Eventually.of_forall hχ01, ?_, ?_, ?_, ?_, ?_⟩
  · -- (ii) the limit is a parabolic inner variational solution
    refine ⟨hucont, fun q hq ↦ (hubd q hq).1, hulip, hwu, hw₂.2.1, hχm, fun p _ ↦ hχ01 p,
      ?_, fun ξ hξ hξc hξs ↦ (hid ξ hξ hξc hξs).1, fun ξ hξ hξc hξs ↦ (hid ξ hξ hξc hξs).2⟩
    exact ae_chi_eq_one_of_pos hβ (fun n ↦ he_pos (Φ n)) heΦ
      (fun p hp ↦ hconvΦ.tendsto_at hp) hUInfm hχae
  · -- (4.5)
    exact weakHeat_of_tendsto S.isOpen hβ (fun n ↦ he_pos _) heΦ (fun n ↦ (hsolv _).2.1) hconvΦ
      hstrongΦ hgu hwΦ
  · -- (3.11)
    exact dissipationIneq_of_tendsto S (v := fun n ↦ v (Φ n))
      (χ := fun n ↦ chiEps β (e (Φ n)) (v (Φ n)))
      (En := fun n ↦ energyBound S (Gε (e (Φ n)))) hE1 (fun n ↦ hEn _) (fun n ↦ hvd _)
      (fun n ↦ (hsolv _).2.1.2.2.1)
      (fun n T hT ↦ semilinear_dissipation S hβ (he_pos _) (hH1n _) (hsolv _) T hT) hEΦ
      hconvΦ hulip (fun n ↦ hχcont _) (fun n p ↦ (chiEps_mem_Icc hβ (he_pos _) _ p).1)
      (fun p ↦ by rcases hχ01 p with h | h <;> simp [h]) hχae hwΦ
  · -- (3.12)
    exact interiorLipEst_of_tendsto S.isOpen (le_max_right _ _) (fun n ↦ hlipn _)
      (fun n ↦ hvd _) hconvΦ
  · -- (3.13)
    intro η hη
    have hlsc := Registry.weightedTVₓ_le_liminf (l := atTop) hUInfo η
      (fun n ↦ chiEps β (e (Φ n)) (v (Φ n))) χ
      (fun n ↦ (hχcont _).locallyIntegrableOn hUInfm) hχloc hχL1
    refine hlsc.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n ↦ ?_))
    exact hCper _ (he₄ _) _ _ _ (hH1n _) (hEn _) (hsolv _) (hgM _) η hη

end Inner

end PerronVariational

end
