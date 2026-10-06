/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import GMTFoundations.Sobolev.Cutoff
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Inner.EnergyConv
import PerronVariational.Inner.SemilinearEstimates
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Profiles

/-!
# Local bound on the reaction term (as in (4.7))

A step of Section 4.3 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. For a solution `u` of
(3.4), testing the equation with a spatial cut-off `θ` on a time slice gives
`∫ θ Q² β_ε(u) = -∫ ∇θ · ∇u - ∫ θ ∂ₜu`; with the interior Lipschitz bound (3.9) and the
dissipation estimate (3.8) this bounds `∫_K β_ε(u)` on compact `K ⊆ U_∞` uniformly in `ε`.

The file also holds `exists_box_lipschitz_of_interiorLipEst` (the local spatial Lipschitz bound
from `InteriorLipEst`), used here and by `Inner.Compactness`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-- **Uniform local spatial Lipschitz bound from the interior Lipschitz estimate**
(`InteriorLipEst`, the form of (3.9) and (3.12)). Near every `p ∈ U_∞` there is a box
`B_r(p.1) × (p.2 - r, p.2 + r) ⊆ U_∞` and a constant `L` (depending only on `p`, `U`, `C`, `M`)
such that every `v` satisfying `InteriorLipEst` with constant `C`, with differentiable time
slices and `|v| ≤ M` on `U_∞`, is `L`-Lipschitz in space on the box. -/
theorem exists_box_lipschitz_of_interiorLipEst {U : Set (E d)} (hU : IsOpen U) (C M : ℝ)
    {p : E d × ℝ} (hp : p ∈ UInf U) :
    ∃ r > 0, ∃ L : ℝ, ball p.1 r ×ˢ Ioo (p.2 - r) (p.2 + r) ⊆ UInf U ∧
      ∀ v : E d × ℝ → ℝ, InteriorLipEst U v C →
        (∀ t > 0, DifferentiableOn ℝ (fun x ↦ v (x, t)) U) → (∀ q ∈ UInf U, |v q| ≤ M) →
        ∀ x ∈ ball p.1 r, ∀ y ∈ ball p.1 r, ∀ t ∈ Ioo (p.2 - r) (p.2 + r),
          |v (x, t) - v (y, t)| ≤ L * ‖x - y‖ := by
  obtain ⟨hx0, ht0⟩ := hp
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU p.1 hx0
  have ht0' : (0 : ℝ) < p.2 := ht0
  set s : ℝ := min (min 1 (ρ / 2)) (Real.sqrt p.2 / 2) with hsdef
  have hs0 : 0 < s := lt_min (lt_min one_pos (half_pos hρ)) (half_pos (Real.sqrt_pos.2 ht0'))
  have hs1 : s ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hsρ : s ≤ ρ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hs2 : s ^ 2 ≤ p.2 / 4 := by
    have h1 : s ≤ Real.sqrt p.2 / 2 := min_le_right _ _
    have h2 : (Real.sqrt p.2 / 2) ^ 2 = p.2 / 4 := by
      rw [div_pow, Real.sq_sqrt ht0'.le]; norm_num
    rw [← h2]
    exact pow_le_pow_left₀ hs0.le h1 2
  set h : ℝ := s ^ 2 / 2 with hhdef
  have hh0 : 0 < h := by positivity
  have hhs : h ≤ s := by nlinarith
  set t₁ : ℝ := p.2 + h with ht₁
  have hcyl : parCyl p.1 t₁ (2 * s) ⊆ UInf U := by
    rintro ⟨y, τ⟩ ⟨hy, hτ⟩
    refine ⟨hρU (Metric.ball_subset_ball (by linarith) hy), ?_⟩
    simp only [mem_Ioc] at hτ
    change 0 < τ
    linarith [hτ.1]
  refine ⟨h, hh0, C * (M / s + 1), ?_, ?_⟩
  · rintro ⟨y, τ⟩ ⟨hy, hτ⟩
    refine ⟨hρU (Metric.ball_subset_ball (by linarith) hy), ?_⟩
    simp only [mem_Ioo] at hτ
    change 0 < τ
    linarith [hτ.1]
  · intro v hv hvd hvM x hx y hy t ht
    have ht0 : 0 < t := by
      simp only [mem_Ioo] at ht
      linarith [ht.1]
    have hball : ball p.1 h ⊆ U := (Metric.ball_subset_ball (by linarith)).trans hρU
    have hgrad : ∀ z ∈ ball p.1 h, ‖fderiv ℝ (fun z ↦ v (z, t)) z‖ ≤ C * (M / s + 1) := by
      intro z hz
      rw [← norm_gradient_eq_norm_fderiv]
      have hmem : (z, t) ∈ parCyl p.1 t₁ s := by
        refine ⟨Metric.ball_subset_ball hhs hz, ?_⟩
        simp only [mem_Ioo] at ht
        simp only [mem_Ioc]
        constructor <;> linarith
      exact hv p.1 t₁ s hs0 hs1 hcyl M (fun q hq ↦ hvM q (hcyl hq)) (z, t) hmem
    have hdiff : ∀ z ∈ ball p.1 h, DifferentiableAt ℝ (fun z ↦ v (z, t)) z := fun z hz ↦
      (hvd t ht0).differentiableAt (hU.mem_nhds (hball hz))
    have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hgrad (convex_ball _ _) hy hx
    simpa [Real.norm_eq_abs] using this

/-- A family satisfying (3.12) with a common constant and a common bound has uniformly bounded
spatial gradients on compact subsets of `U_∞`. -/
theorem exists_bound_gradₓ_of_interiorLipEst {U : Set (E d)} (hU : IsOpen U) (C M : ℝ)
    {K : Set (E d × ℝ)} (hK : IsCompact K) (hKU : K ⊆ UInf U) :
    ∃ L : ℝ, ∀ v : E d × ℝ → ℝ, InteriorLipEst U v C →
      (∀ t > 0, DifferentiableOn ℝ (fun x ↦ v (x, t)) U) → (∀ q ∈ UInf U, |v q| ≤ M) →
        ∀ q ∈ K, ‖gradₓ v q‖ ≤ L := by
  choose! r hr L hbox hlip using fun p (hp : p ∈ K) ↦
    exists_box_lipschitz_of_interiorLipEst hU C M (hKU hp)
  set V : E d × ℝ → Set (E d × ℝ) := fun p ↦ ball p.1 (r p) ×ˢ Ioo (p.2 - r p) (p.2 + r p)
  have hV : ∀ p ∈ K, V p ∈ 𝓝 p := fun p hp ↦
    ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨mem_ball_self (hr p hp),
      by linarith [hr p hp], by linarith [hr p hp]⟩)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun p hp ↦ V p) hV
  refine ⟨∑ i ∈ t, |L i|, fun v hv hvd hvb q hq ↦ ?_⟩
  obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.1 (ht hq)
  have hlipq : LipschitzOnWith (Real.toNNReal (L i)) (fun y ↦ v (y, q.2)) (ball (i : E d × ℝ).1
      (r i)) := LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ by
    rw [Real.dist_eq, dist_eq_norm]
    exact (hlip i i.2 v hv hvd hvb x hx y hy q.2 hqi.2).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
  refine (norm_gradₓ_le_of_lipschitzOn (isOpen_ball.mem_nhds hqi.1) hlipq).trans ?_
  rw [Real.coe_toNNReal']
  refine (max_le (le_abs_self _) (abs_nonneg _)).trans ?_
  exact Finset.single_le_sum (f := fun j : K ↦ |L j|) (fun j _ ↦ abs_nonneg _) hi

/-- A compact subset of `U_∞` lies in a box `K₁ × [T₁, T₂]` with `K₁ ⊆ U` compact, `T₁ > 0`. -/
theorem exists_box {U : Set (E d)} {A : Set (E d × ℝ)} (hA : A ⊆ UInf U) (hAc : IsCompact A)
    (hne : A.Nonempty) : ∃ K₁ : Set (E d), IsCompact K₁ ∧ K₁ ⊆ U ∧ ∃ T₁ T₂ : ℝ, 0 < T₁ ∧
      T₁ ≤ T₂ ∧ A ⊆ K₁ ×ˢ Icc T₁ T₂ := by
  obtain ⟨p₁, hp₁, hmin⟩ := hAc.exists_isMinOn hne continuous_snd.continuousOn
  obtain ⟨p₂, hp₂, hmax⟩ := hAc.exists_isMaxOn hne continuous_snd.continuousOn
  refine ⟨Prod.fst '' A, hAc.image continuous_fst, ?_, p₁.2, p₂.2, (hA hp₁).2,
    isMinOn_iff.1 hmin p₂ hp₂, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hA hp).1
  · intro p hp
    exact ⟨mem_image_of_mem _ hp, isMinOn_iff.1 hmin p hp, isMaxOn_iff.1 hmax p hp⟩

/-- **Testing the equation with a spatial cut-off** on a time slice:
`∫ θ Q² β_ε(u) = -∫ ∇u · ∇θ - ∫ θ ∂ₜu`. -/
theorem integral_cutoff_reaction_eq {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ} {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {ε : ℝ} {u : E d × ℝ → ℝ}
    (hsol : IsSemilinearSolOn U Q β ε (Ioi 0) u) (hQ : ContinuousOn Q U) {θ : E d → ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (hθU : tsupport θ ⊆ U) {t : ℝ}
    (ht : 0 < t) :
    ∫ x, θ x * (Q x ^ 2 * betaEps β ε (u (x, t))) =
      -(∫ x, ⟪gradₓ u (x, t), ∇ θ x⟫) - ∫ x, θ x * dₜ u (x, t) := by
  set K := tsupport θ with hKdef
  have hK : IsCompact K := hθc
  have hθ0 : ∀ x ∉ K, θ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hlc := IsSemilinearSolOn.continuousOn_lapₓ hβ hsol hQ
  have hpt : ∀ x, θ x * (Q x ^ 2 * betaEps β ε (u (x, t))) =
      θ x * lapₓ u (x, t) - θ x * dₜ u (x, t) := by
    intro x
    by_cases hx : x ∈ K
    · rw [hsol.2.2.2.2.2.2 (x, t) ⟨hθU hx, ht⟩]
      ring
    · simp [hθ0 x hx]
  have i1 : Integrable fun x ↦ θ x * lapₓ u (x, t) :=
    GMTFoundations.integrable_of_continuousOn_of_zero hK ((hθ.continuous.continuousOn.mul
      (continuousOn_slice_of_prod hlc ht)).mono hθU) fun x hx ↦ by simp [hθ0 x hx]
  have i2 : Integrable fun x ↦ θ x * dₜ u (x, t) :=
    GMTFoundations.integrable_of_continuousOn_of_zero hK ((hθ.continuous.continuousOn.mul
      (continuousOn_slice_of_prod hsol.2.2.2.2.2.1 ht)).mono hθU) fun x hx ↦ by simp [hθ0 x hx]
  obtain ⟨Cθ, hθL⟩ := hθ.lipschitzWith_of_hasCompactSupport hθc one_ne_zero
  have h := integral_laplacian_mul_eq_neg hU (hsol.2.1 t ht) hθL hθc hθU
  have h' : ∫ x, θ x * lapₓ u (x, t) = -∫ x, ⟪gradₓ u (x, t), ∇ θ x⟫ := by
    refine (integral_congr_ae (ae_of_all _ fun x ↦ ?_)).trans (h.trans rfl)
    simp only [lapₓ]
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub i1 i2, h']

theorem abs_le_sq_add_one (a : ℝ) : |a| ≤ a ^ 2 + 1 := by
  rcases le_total (|a|) 1 with h | h
  · linarith [sq_nonneg a, abs_nonneg a]
  · nlinarith [sq_abs a, abs_nonneg a]

/-- Bound for the tested reaction term on a time slice. -/
theorem ofReal_integral_cutoff_reaction_le {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ}
    {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ} {u : E d × ℝ → ℝ}
    (hsol : IsSemilinearSolOn U Q β ε (Ioi 0) u) (hQ : ContinuousOn Q U) {θ : E d → ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (hθU : tsupport θ ⊆ U)
    (hθ01 : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1) {Cθ L : ℝ} (hCθ : ∀ x, ‖∇ θ x‖ ≤ Cθ) (hL0 : 0 ≤ L)
    {t : ℝ} (ht : 0 < t) (hL : ∀ x ∈ tsupport θ, ‖gradₓ u (x, t)‖ ≤ L) :
    ENNReal.ofReal (∫ x, θ x * (Q x ^ 2 * betaEps β ε (u (x, t)))) ≤
      ENNReal.ofReal (L * Cθ * (volume (tsupport θ)).toReal) +
        ∫⁻ x in tsupport θ, (ENNReal.ofReal (dₜ u (x, t) ^ 2) + 1) := by
  set K := tsupport θ with hKdef
  have hK : IsCompact K := hθc
  have hKm : MeasurableSet K := (isClosed_tsupport θ).measurableSet
  have hθ0 : ∀ x ∉ K, θ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hC0 : 0 ≤ Cθ := (norm_nonneg _).trans (hCθ 0)
  rw [integral_cutoff_reaction_eq hU hβ hsol hQ hθ hθc hθU ht]
  have h1 : |∫ x, ⟪gradₓ u (x, t), ∇ θ x⟫| ≤ L * Cθ * (volume K).toReal := by
    have hi : Integrable (K.indicator fun _ ↦ L * Cθ) :=
      (integrable_indicator_iff hKm).2 (continuousOn_const.integrableOn_compact hK)
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hi (ae_of_all _ fun x ↦ ?_)).trans (le_of_eq ?_)
    · by_cases hx : x ∈ K
      · rw [indicator_of_mem hx, Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hL x hx) (hCθ x) (norm_nonneg _)
          hL0)
      · have : ∇ θ x = 0 := by
          simp only [gradient]
          rw [fderiv_of_notMem_tsupport ℝ hx, map_zero]
        simp [indicator_of_notMem hx, this]
    · rw [integral_indicator_const _ hKm, smul_eq_mul, measureReal_def, mul_comm]
  have h2 : ENNReal.ofReal |∫ x, θ x * dₜ u (x, t)| ≤
      ∫⁻ x in K, (ENNReal.ofReal (dₜ u (x, t) ^ 2) + 1) := by
    rw [← Real.norm_eq_abs, ofReal_norm, ← lintegral_indicator hKm]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x ↦ ?_)
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (sq_nonneg _) zero_le_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_mul, abs_of_nonneg (hθ01 x).1]
      calc θ x * |dₜ u (x, t)| ≤ 1 * |dₜ u (x, t)| :=
            mul_le_mul_of_nonneg_right (hθ01 x).2 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact abs_le_sq_add_one _
    · simp [hθ0 x hx]
  calc ENNReal.ofReal (-(∫ x, ⟪gradₓ u (x, t), ∇ θ x⟫) - ∫ x, θ x * dₜ u (x, t))
      ≤ ENNReal.ofReal (L * Cθ * (volume K).toReal + |∫ x, θ x * dₜ u (x, t)|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hA : -(∫ x, ⟪gradₓ u (x, t), ∇ θ x⟫) ≤ L * Cθ * (volume K).toReal :=
          (neg_le_abs _).trans h1
        have hB : -(∫ x, θ x * dₜ u (x, t)) ≤ |∫ x, θ x * dₜ u (x, t)| := neg_le_abs _
        linarith
    _ ≤ _ := by
        rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
        exact add_le_add le_rfl h2

/-- **Local bound on the reaction term** (the computation (4.7), used in (4.11)): for compact
`K ⊆ U_∞` there is `C` (depending on `K`, the setting, `β`, `M` and an energy bound `E0`) such
that `∫_K β_ε(u) ≤ C` for every solution with data `0 ≤ gε ≤ M`, `gε ∈ H¹(U)`,
`∫_U |Gε|² + Q_max² |U| ≤ E0`, `0 < ε < ε₁`. (Proof: test the equation with a cutoff `η ≥ 1_K`
and use (3.8).) -/
theorem semilinear_betaEps_lintegral_le (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (M : ℝ) (E0 : ℝ≥0∞), E0 ≠ ⊤ → ∀ K ⊆ UInf S.U, IsCompact K →
      ∃ C : ℝ, ∀ ε ∈ Ioo 0 ε₁, ∀ (gε : E d → ℝ) (Gε : E d → E d) (u : E d × ℝ → ℝ),
        MemH1 S.U gε Gε → energyBound S Gε ≤ E0 → IsSemilinearSolution S.U S.Q β ε gε u →
        (∀ x ∈ S.U, 0 ≤ gε x ∧ gε x ≤ M) →
        ∫⁻ p in K, ENNReal.ofReal (betaEps β ε (u p)) ≤ ENNReal.ofReal C := by
  classical
  obtain ⟨KQ, hKQ⟩ := S.lip
  have hQc : ContinuousOn S.Q S.U := hKQ.continuousOn.mono subset_closure
  obtain ⟨C, ε₁, hε₁, hLip⟩ := semilinear_interiorLipEst S hβ
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, fun M E0 hE0 K hK hKc ↦ ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun _ _ _ _ _ _ _ _ _ ↦ by simp⟩
  obtain ⟨K₁, hK₁c, hK₁U, T₁, T₂, hT₁, hT₁₂, hKB⟩ := exists_box hK hKc hne
  obtain ⟨θ, hθ, hθc, hθU, hθ01, hθ1⟩ := GMTFoundations.exists_smooth_cutoff hK₁c S.isOpen hK₁U
  have hθ1' : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  set Ks := tsupport θ with hKsdef
  have hKsc : IsCompact Ks := hθc
  have hKsm : MeasurableSet Ks := (isClosed_tsupport θ).measurableSet
  set I := Icc T₁ T₂ with hIdef
  set Bx := Ks ×ˢ I with hBxdef
  have hBxc : IsCompact Bx := hKsc.prod isCompact_Icc
  have hBxm : MeasurableSet Bx := hKsm.prod measurableSet_Icc
  have hBxU : Bx ⊆ UInf S.U := prod_mono hθU fun t ht ↦ hT₁.trans_le ht.1
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  obtain ⟨L, hL⟩ := exists_bound_gradₓ_of_interiorLipEst S.isOpen C (max M 1) hBxc hBxU
  set L' := max L 0 with hL'def
  have hL'0 : 0 ≤ L' := le_max_right _ _
  obtain ⟨Cθ, hCθ⟩ := (hθ1'.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hθc.fderiv (𝕜 := ℝ))
  set Cθ' := max Cθ 0 with hCθ'def
  have hCθ' : ∀ x, ‖∇ θ x‖ ≤ Cθ' := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]
    exact (hCθ x).trans (le_max_left _ _)
  set m := S.Qmin ^ 2 with hmdef
  have hm : 0 < m := by have := S.Qmin_pos; positivity
  set c₁ := L' * Cθ' * (volume Ks).toReal with hc₁def
  have hc₁ : 0 ≤ c₁ := by positivity
  refine ⟨(1 / m) * (c₁ * (T₂ - T₁) + E0.toReal / 2 + (volume Bx).toReal),
    fun ε hε gε Gε u hH1 hEn hu hg ↦ ?_⟩
  have hεpos : 0 < ε := hε.1
  have hsol := hu.2.1
  have hLu : ∀ q ∈ Bx, ‖gradₓ u q‖ ≤ L' := fun q hq ↦
    (hL u (hLip ε ⟨hεpos, hε.2.trans_le (min_le_left _ _)⟩ M gε u hu hg)
      (fun t ht ↦ (hsol.2.1 t ht).differentiableOn (by norm_num))
      (fun q hq ↦ by
        have h := semilinear_nonneg_le_max S hβ hεpos hu hg q
          ⟨subset_closure hq.1, mem_Ici.2 (le_of_lt hq.2)⟩
        rw [abs_of_nonneg h.1]
        exact h.2.trans (max_le_max le_rfl (hε.2.trans_le (min_le_right _ _)).le)) q hq).trans
      (le_max_left _ _)
  have hβc : ContinuousOn (fun q : E d × ℝ ↦ betaEps β ε (u q)) (UInf S.U) :=
    (hβ.continuous_betaEps ε).comp_continuousOn hsol.1
  have hQ2c : ContinuousOn (fun q : E d × ℝ ↦ S.Q q.1 ^ 2) (UInf S.U) :=
    (hQc.comp continuousOn_fst fun p hp ↦ hp.1).pow 2
  -- the tested reaction term
  set f : E d × ℝ → ℝ≥0∞ := Bx.indicator
    (fun q ↦ ENNReal.ofReal (θ q.1 * (S.Q q.1 ^ 2 * betaEps β ε (u q)))) with hfdef
  have hfm : Measurable f := by
    rw [hfdef, ← piecewise_eq_indicator]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hBxm
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (((hθ.continuous.comp continuous_fst).continuousOn.mul (hQ2c.mul hβc)).mono hBxU)
  have hstep1 : ∫⁻ p in K, ENNReal.ofReal (betaEps β ε (u p)) ≤
      ENNReal.ofReal (1 / m) * ∫⁻ q, f q := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_mono' hKm fun p hp ↦ ?_).trans (setLIntegral_le_lintegral _ _)
    have hpB := hKB hp
    have hpBx : p ∈ Bx :=
      ⟨subset_tsupport θ (by rw [Function.mem_support, hθ1 _ hpB.1]; norm_num), hpB.2⟩
    have hb0 : 0 ≤ betaEps β ε (u p) := hβ.betaEps_nonneg ε _ hεpos.le
    have hQp := S.Q_mem p.1 (subset_closure (hK₁U hpB.1))
    have hQm : m ≤ S.Q p.1 ^ 2 := pow_le_pow_left₀ S.Qmin_pos.le hQp.1 2
    rw [hfdef, indicator_of_mem hpBx, hθ1 _ hpB.1, one_mul, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, le_div_iff₀ hm]
    nlinarith
  have hstep2 : ∫⁻ q, f q = ∫⁻ t, ∫⁻ x, f (x, t) := by
    rw [Measure.volume_eq_prod, lintegral_prod_symm' _ hfm]
  have hstep3 : ∀ t, ∫⁻ x, f (x, t) ≤ I.indicator (fun t ↦ ENNReal.ofReal c₁ +
      ∫⁻ x in Ks, (ENNReal.ofReal (dₜ u (x, t) ^ 2) + 1)) t := by
    intro t
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht]
      have htpos : 0 < t := hT₁.trans_le ht.1
      have hint : Integrable fun x ↦ θ x * (S.Q x ^ 2 * betaEps β ε (u (x, t))) := by
        refine GMTFoundations.integrable_of_continuousOn_of_zero hKsc ?_ fun x hx ↦ by
          simp [image_eq_zero_of_notMem_tsupport hx]
        exact (hθ.continuous.continuousOn.mul ((hQc.pow 2).mul
          (continuousOn_slice_of_prod hβc htpos))).mono hθU
      have heq : ∫⁻ x, f (x, t) =
          ENNReal.ofReal (∫ x, θ x * (S.Q x ^ 2 * betaEps β ε (u (x, t)))) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x ↦ ?_)]
        · refine lintegral_congr fun x ↦ ?_
          by_cases hx : x ∈ Ks
          · rw [hfdef, indicator_of_mem (show (x, t) ∈ Bx from ⟨hx, ht⟩)]
          · rw [hfdef, indicator_of_notMem (show (x, t) ∉ Bx from fun h ↦ hx h.1),
              image_eq_zero_of_notMem_tsupport hx, zero_mul, ENNReal.ofReal_zero]
        · exact mul_nonneg (hθ01 x).1 (mul_nonneg (sq_nonneg _)
            (hβ.betaEps_nonneg ε _ hεpos.le))
      rw [heq]
      exact ofReal_integral_cutoff_reaction_le S.isOpen hβ hsol hQc hθ1' hθc hθU hθ01 hCθ' hL'0
        htpos fun x hx ↦ hLu (x, t) ⟨hx, ht⟩
    · rw [indicator_of_notMem ht]
      have h0 : ∀ x, f (x, t) = 0 := fun x ↦ indicator_of_notMem (fun h ↦ ht h.2) _
      simp [h0]
  -- the dissipation term
  set F : E d × ℝ → ℝ≥0∞ := fun q ↦ ENNReal.ofReal (dₜ u q ^ 2) + 1 with hFdef
  have hgm : Measurable (Bx.indicator F) := by
    rw [← piecewise_eq_indicator]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hBxm
    exact (ENNReal.continuous_ofReal.comp_continuousOn
      ((hsol.2.2.2.2.2.1.mono hBxU).pow 2)).add continuousOn_const
  have hgeq : ∫⁻ t in I, ∫⁻ x in Ks, F (x, t) = ∫⁻ q in Bx, F q := by
    rw [← lintegral_indicator hBxm, Measure.volume_eq_prod, lintegral_prod_symm' _ hgm,
      ← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun t ↦ ?_
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht, ← lintegral_indicator hKsm]
      refine lintegral_congr fun x ↦ ?_
      by_cases hx : x ∈ Ks
      · rw [indicator_of_mem hx, indicator_of_mem (show (x, t) ∈ Bx from ⟨hx, ht⟩)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (show (x, t) ∉ Bx from fun h ↦ hx h.1)]
    · rw [indicator_of_notMem ht]
      have h0 : ∀ x, Bx.indicator F (x, t) = 0 := fun x ↦
        indicator_of_notMem (fun h ↦ ht h.2) _
      simp [h0]
  have hdis := semilinear_dissipation S hβ hεpos hH1 hu T₂ (by linarith)
  have hBxsub : Bx ⊆ S.U ×ˢ Ioc 0 T₂ := prod_mono hθU fun t ht ↦ ⟨hT₁.trans_le ht.1, ht.2⟩
  have hD : ∫⁻ q in Bx, F q ≤
      ENNReal.ofReal (E0.toReal / 2) + ENNReal.ofReal (volume Bx).toReal := by
    rw [hFdef, lintegral_add_right _ measurable_const, setLIntegral_const, one_mul,
      ENNReal.ofReal_toReal hBxc.measure_lt_top.ne]
    gcongr
    refine (lintegral_mono_set hBxsub).trans (le_add_self.trans (hdis.trans ?_))
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hE0, ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_div_right hEn 2
  calc ∫⁻ p in K, ENNReal.ofReal (betaEps β ε (u p))
      ≤ ENNReal.ofReal (1 / m) * ∫⁻ q, f q := hstep1
    _ = ENNReal.ofReal (1 / m) * ∫⁻ t, ∫⁻ x, f (x, t) := by rw [hstep2]
    _ ≤ ENNReal.ofReal (1 / m) * ∫⁻ t, I.indicator (fun t ↦ ENNReal.ofReal c₁ +
          ∫⁻ x in Ks, F (x, t)) t := by
        gcongr with t
        exact hstep3 t
    _ = ENNReal.ofReal (1 / m) * (ENNReal.ofReal c₁ * ENNReal.ofReal (T₂ - T₁) +
          ∫⁻ q in Bx, F q) := by
        rw [lintegral_indicator measurableSet_Icc, lintegral_add_left measurable_const,
          setLIntegral_const, Real.volume_Icc, hgeq]
    _ ≤ ENNReal.ofReal (1 / m) * (ENNReal.ofReal c₁ * ENNReal.ofReal (T₂ - T₁) +
          (ENNReal.ofReal (E0.toReal / 2) + ENNReal.ofReal (volume Bx).toReal)) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by nlinarith) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        ring_nf


end Inner

end PerronVariational

end
