/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.EnergyDissipationStepB
import Mathlib.Order.CompletePartialOrder
import PerronVariational.Semilinear.Profiles

/-!
# Energy dissipation, part 4: the limit `h → 0` (Step C) and the main theorem

The energy dissipation inequality (A.1), i.e. (3.8) of Proposition 3.8(iii), of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981,
for data in `H¹`. This is a result from the literature (L. C. Evans, *Partial Differential
Equations*, 2nd ed., AMS, 2010, doi:10.1090/gsm/019, §7.1.3, Theorem 5), proved here. The proof
has three steps: Step A, the energy bound near `t = 0` (`EnergyDissipationStepA`); Step B, the
Steklov-averaged energy identity (`EnergyDissipationStepB`); and Step C, in this file.

Step C. Divide the Steklov identity (Step B) by `h²` and take
`t₀ = h²`:

`½ ∫_U |A_h∇u(T)|² + ∫_{h²}^T ∫_U (D_h u)² = ½ ∫_U |A_h∇u(h²)|² - ∫_{h²}^T ∫_U D_h u A_h f`.

* The first term on the right is at most `½ (1 + h) (‖G‖² + o(1))` by Cauchy–Schwarz and Step A.
* The reaction term is compared with the telescoping difference quotients of `B = Q² 𝓑_ε(u)`;
  the error is at most `L ω(h) ∫∫ |D_h u|`, where `ω` is a modulus of continuity of `u` on
  `Ū × [0, T + 1]` and `L` a Lipschitz constant of `Q² β_ε`. Absorbing gives a uniform bound on
  `∫∫ (D_h u)²`, so the error tends to `0`.
* Fatou's lemma on the left-hand side (pointwise `A_h∇u(T) → ∇u(T)`, `D_h u → ∂ₜu`).

The result is `semilinear_energy_dissipation`, which proves
`Registry.semilinear_energy_dissipation`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace ContDiff

@[expose] public section

namespace PerronVariational

namespace EnergyDissipation

variable {d : ℕ}

/-! ### Constants of the reaction term -/

section Constants

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ}
include hβ

/-- `|Q² β_ε(z)| ≤ M` for `x ∈ Ū`. -/
theorem exists_reaction_bound (S : Setting d) (hε : 0 < ε) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ closure S.U, ∀ z, |S.Q x ^ 2 * betaEps β ε z| ≤ M := by
  obtain ⟨Mβ, hMβ, hβle⟩ := hβ.exists_le
  refine ⟨S.Qmax ^ 2 * (Mβ / ε), by positivity, fun x hx z ↦ ?_⟩
  obtain ⟨h1, h2⟩ := S.Q_mem x hx
  have hQ0 : 0 ≤ S.Q x := S.Qmin_pos.le.trans h1
  have hb0 : 0 ≤ betaEps β ε z := hβ.betaEps_nonneg ε z hε.le
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hb0)]
  refine mul_le_mul (pow_le_pow_left₀ hQ0 h2 2) ?_ hb0 (sq_nonneg _)
  exact div_le_div_of_nonneg_right (hβle _) hε.le

/-- `z ↦ Q(x)² β_ε(z)` is Lipschitz, uniformly in `x ∈ Ū`. -/
theorem exists_reaction_lipschitz (S : Setting d) (hε : 0 < ε) :
    ∃ L, 0 ≤ L ∧ ∀ x ∈ closure S.U, ∀ z₁ z₂,
      |S.Q x ^ 2 * betaEps β ε z₁ - S.Q x ^ 2 * betaEps β ε z₂| ≤ L * |z₁ - z₂| := by
  have hcs : HasCompactSupport β := by
    refine HasCompactSupport.intro (K := Icc 0 1) isCompact_Icc fun s hs ↦ hβ.2.1 s ?_
    exact fun h ↦ hs (Ioo_subset_Icc_self h)
  obtain ⟨K, hK⟩ := hβ.1.lipschitzWith_of_hasCompactSupport hcs (by simp)
  refine ⟨S.Qmax ^ 2 * (K / ε ^ 2), by positivity, fun x hx z₁ z₂ ↦ ?_⟩
  obtain ⟨h1, h2⟩ := S.Q_mem x hx
  have hQ0 : 0 ≤ S.Q x := S.Qmin_pos.le.trans h1
  rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _), mul_assoc]
  refine mul_le_mul (pow_le_pow_left₀ hQ0 h2 2) ?_ (abs_nonneg _) (sq_nonneg _)
  have hl := hK.dist_le_mul (z₁ / ε) (z₂ / ε)
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hε] at hl
  rw [betaEps, betaEps, ← sub_div, abs_div, abs_of_pos hε]
  calc |β (z₁ / ε) - β (z₂ / ε)| / ε ≤ K * (|z₁ - z₂| / ε) / ε :=
        div_le_div_of_nonneg_right hl hε.le
    _ = K / ε ^ 2 * |z₁ - z₂| := by field_simp

end Constants

/-- The potential `B(x, z) = Q(x)² 𝓑_ε(z)`, with `∂_z B = Q² β_ε`. -/
noncomputable def potential (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ) (x : E d) (z : ℝ) : ℝ :=
  Q x ^ 2 * bigBEps β ε z

theorem hasDerivAt_potential {β : ℝ → ℝ} (hβ : IsReactionProfile β) (Q : E d → ℝ) (ε : ℝ)
    (x : E d) (z : ℝ) : HasDerivAt (potential Q β ε x) (Q x ^ 2 * betaEps β ε z) z :=
  (hβ.hasDerivAt_bigBEps ε z).const_mul _

theorem continuous_potential {β : ℝ → ℝ} (hβ : IsReactionProfile β) (Q : E d → ℝ) (ε : ℝ)
    (x : E d) : Continuous (potential Q β ε x) :=
  continuous_iff_continuousAt.2 fun z ↦ (hasDerivAt_potential hβ Q ε x z).continuousAt

theorem potential_nonneg {β : ℝ → ℝ} (hβ : IsReactionProfile β) (Q : E d → ℝ) {ε : ℝ}
    (hε : ε ≠ 0) (x : E d) (z : ℝ) : 0 ≤ potential Q β ε x z :=
  mul_nonneg (sq_nonneg _) (hβ.bigBEps_nonneg hε z)

/-- `B(x, ·)` is `M`-Lipschitz. -/
theorem abs_potential_sub_le {β : ℝ → ℝ} (hβ : IsReactionProfile β) {Q : E d → ℝ} {ε M : ℝ}
    {x : E d} (hM : ∀ z, |Q x ^ 2 * betaEps β ε z| ≤ M) (z₁ z₂ : ℝ) :
    |potential Q β ε x z₁ - potential Q β ε x z₂| ≤ M * |z₁ - z₂| := by
  have := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := potential Q β ε x) (C := M)
    (fun z _ ↦ (hasDerivAt_potential hβ Q ε x z).hasDerivWithinAt)
    (fun z _ ↦ by rw [Real.norm_eq_abs]; exact hM z) (mem_univ z₂) (mem_univ z₁)
  simpa [Real.norm_eq_abs] using this

/-- **The pointwise reaction estimate.** If `|φ(z) - c| ≤ η` on the segment between `z₁` and
`z₂`, where `φ = ∂_z B(x, ·)`, then `|B(z₂) - B(z₁) - c (z₂ - z₁)| ≤ η |z₂ - z₁|`. -/
theorem abs_potential_sub_sub_le {β : ℝ → ℝ} (hβ : IsReactionProfile β) {Q : E d → ℝ}
    {ε : ℝ} (x : E d) {z₁ z₂ c η : ℝ}
    (hc : ∀ z ∈ uIcc z₁ z₂, |Q x ^ 2 * betaEps β ε z - c| ≤ η) :
    |potential Q β ε x z₂ - potential Q β ε x z₁ - c * (z₂ - z₁)| ≤ η * |z₂ - z₁| := by
  have := (convex_uIcc z₁ z₂).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z ↦ potential Q β ε x z - c * z) (C := η)
    (fun z _ ↦ ((hasDerivAt_potential hβ Q ε x z).sub
      ((hasDerivAt_id z).const_mul c)).hasDerivWithinAt)
    (fun z hz ↦ by rw [Real.norm_eq_abs, mul_one]; exact hc z hz) left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  convert this using 2; ring

/-- A point between `z₁` and `z₂` is within `max |z₁ - w| |z₂ - w|` of `w`. -/
theorem abs_sub_le_of_mem_uIcc {z₁ z₂ z w η : ℝ} (hz : z ∈ uIcc z₁ z₂) (h₁ : |z₁ - w| ≤ η)
    (h₂ : |z₂ - w| ≤ η) : |z - w| ≤ η := by
  rw [mem_uIcc] at hz
  rw [abs_le] at h₁ h₂ ⊢
  rcases hz with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-! ### Uniform continuity -/

/-- A uniform modulus of continuity in time of `u` on `Ū × [0, T']`. -/
theorem exists_time_modulus {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ}
    {u : E d × ℝ → ℝ} (hUb : Bornology.IsBounded U) (hu : IsSemilinearSolution U Q β ε g u)
    (T' : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ x ∈ closure U, ∀ t ∈ Icc 0 T', ∀ r ∈ Icc 0 T', |r - t| < ρ →
      |u (x, r) - u (x, t)| < η := by
  have hC : IsCompact (closure U ×ˢ Icc 0 T') := hUb.isCompact_closure.prod isCompact_Icc
  have huc := hC.uniformContinuousOn_of_continuous
    (hu.1.mono (prod_mono le_rfl Icc_subset_Ici_self))
  obtain ⟨ρ, hρ, hρu⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  refine ⟨ρ, hρ, fun x hx t ht r hr hrt ↦ ?_⟩
  have := hρu (x, r) ⟨hx, hr⟩ (x, t) ⟨hx, ht⟩ (by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]; simpa using hrt)
  rwa [Real.dist_eq] at this

/-! ### Step A in product form -/

section StepAProd

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {G : E d → E d}
  {u : E d × ℝ → ℝ}

theorem aemeasurable_grad_sq (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    {a b : ℝ} (ha : 0 ≤ a) :
    AEMeasurable (fun p ↦ ENNReal.ofReal (‖gradₓ u p‖ ^ 2))
      ((volume.restrict U).prod (volume.restrict (Ioc a b))) := by
  rw [← restrict_prod_eq]
  refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
  exact ((hu.2.1.2.2.1.norm.pow 2).mono fun p hp ↦ ⟨hp.1, ha.trans_lt hp.2.1⟩).aemeasurable
    (hU.measurableSet.prod measurableSet_Ioc)

/-- Step A, stated as a lintegral over `U × (0, s]`. -/
theorem lintegral_prod_energy_le (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    (hg : MemH1 U g G) {M : ℝ} (hM : ∀ p ∈ U ×ˢ Ioi 0, |reaction Q β ε u p| ≤ M) {s δ : ℝ}
    (hs : 0 < s) (hδ : ∀ x ∈ U, ∀ t ∈ Ioc 0 s, |u (x, t) - g x| ≤ δ) :
    ∫⁻ p in U ×ˢ Ioc 0 s, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) ≤
      ENNReal.ofReal (s * (∫ x in U, ‖G x‖ ^ 2) + 2 * (M * δ * (volume.real U * s))) := by
  rw [restrict_prod_eq, lintegral_prod_symm _ (aemeasurable_grad_sq hU hu le_rfl)]
  exact lintegral_energy_le hU hUb hQ hβ hu hg hs hδ fun x hx t ht ↦ hM (x, t) ⟨hx, ht.1⟩

/-- `∇u ∈ L²(U × (0, s])` for every `s`. -/
theorem lintegral_grad_sq_lt_top (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    (hg : MemH1 U g G) {M : ℝ} (hM : ∀ p ∈ U ×ˢ Ioi 0, |reaction Q β ε u p| ≤ M) {s : ℝ}
    (hs : 0 < s) : ∫⁻ p in U ×ˢ Ioc 0 s, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) < ⊤ := by
  obtain ⟨δ, hδ⟩ := (hUb.isCompact_closure.prod (isCompact_Icc (a := (0 : ℝ)) (b := s))
    ).exists_bound_of_continuousOn ((continuousOn_sub_data hu).mono
      (prod_mono le_rfl Icc_subset_Ici_self))
  refine (lintegral_prod_energy_le hU hUb hQ hβ hu hg hM hs (δ := δ) fun x hx t ht ↦ ?_).trans_lt
    ENNReal.ofReal_lt_top
  simpa using hδ (x, t) ⟨subset_closure hx, ht.1.le, ht.2⟩

/-- Step A near `t = 0`: `∫_{U × (0, s]} |∇u|² ≤ s (‖G‖² + η)` for small `s`. -/
theorem exists_energy_near_zero (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    (hg : MemH1 U g G) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p ∈ U ×ˢ Ioi 0, |reaction Q β ε u p| ≤ M)
    {η : ℝ} (hη : 0 < η) :
    ∃ s₀ > 0, ∀ s, 0 < s → s ≤ s₀ →
      ∫⁻ p in U ×ˢ Ioc 0 s, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) ≤
        ENNReal.ofReal (s * ((∫ x in U, ‖G x‖ ^ 2) + η)) := by
  set δ := η / (2 * M * volume.real U + 1) with hδdef
  have hden : 0 < 2 * M * volume.real U + 1 := by positivity
  have hδ : 0 < δ := div_pos hη hden
  obtain ⟨ρ, hρ, hρu⟩ := exists_time_modulus hUb hu 1 hδ
  refine ⟨min (ρ / 2) 1, lt_min (half_pos hρ) one_pos, fun s hs hs₀ ↦ ?_⟩
  refine (lintegral_prod_energy_le hU hUb hQ hβ hu hg hM hs (δ := δ) fun x hx t ht ↦ ?_).trans ?_
  · have ht1 : t ≤ 1 := ht.2.trans (hs₀.trans (min_le_right _ _))
    have hlt : |t - 0| < ρ := by
      rw [sub_zero, abs_of_pos ht.1]
      linarith [ht.2, hs₀.trans (min_le_left _ _)]
    have := hρu x (subset_closure hx) 0 ⟨le_rfl, zero_le_one⟩ t ⟨ht.1.le, ht1⟩ hlt
    rw [hu.2.2.1 x (subset_closure hx)] at this
    exact this.le
  · refine ENNReal.ofReal_le_ofReal ?_
    have : 2 * (M * δ * (volume.real U * s)) = s * (δ * (2 * M * volume.real U)) := by ring
    rw [this, mul_add]
    have h2 : δ * (2 * M * volume.real U) ≤ η := by
      rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hden]
      linarith
    linarith [mul_le_mul_of_nonneg_left h2 hs.le]

end StepAProd

/-! ### One-dimensional lemmas -/

/-- `|h⁻¹ ∫ₐ^{a+h} φ - c| ≤ K` if `|φ - c| ≤ K` on `[a, a + h]`. -/
theorem abs_average_sub_le {φ : ℝ → ℝ} {a h c K : ℝ} (hh : 0 < h)
    (hφ : ContinuousOn φ (Icc a (a + h))) (hK : ∀ r ∈ Icc a (a + h), |φ r - c| ≤ K) :
    |(∫ r in a..a + h, φ r) / h - c| ≤ K := by
  have hle : a ≤ a + h := by linarith
  have hi : IntervalIntegrable φ volume a (a + h) :=
    (hφ.mono (uIcc_of_le hle).subset).intervalIntegrable
  have h1 : (∫ r in a..a + h, φ r) - h * c = ∫ r in a..a + h, (φ r - c) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  have h2 : |∫ r in a..a + h, (φ r - c)| ≤ K * |a + h - a| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + h) (C := K)
      (f := fun r ↦ φ r - c) fun r hr ↦ by
        rw [uIoc_of_le hle] at hr
        exact hK r ⟨hr.1.le, hr.2⟩
    simpa [Real.norm_eq_abs] using this
  rw [add_sub_cancel_left, abs_of_pos hh] at h2
  rw [show (∫ r in a..a + h, φ r) / h - c = ((∫ r in a..a + h, φ r) - h * c) / h by
    field_simp, abs_div, abs_of_pos hh, div_le_iff₀ hh, h1]
  exact h2

/-- **Telescoping**: `∫_{t₀}^T (φ(t + h) - φ(t)) dt = ∫_T^{T+h} φ - ∫_{t₀}^{t₀+h} φ`. -/
theorem integral_telescope {φ : ℝ → ℝ} {t₀ T h : ℝ} (hT : t₀ ≤ T) (hh : 0 ≤ h)
    (hφ : ContinuousOn φ (Icc t₀ (T + h))) :
    ∫ t in Ioc t₀ T, (φ (t + h) - φ t) =
      (∫ r in T..T + h, φ r) - ∫ r in t₀..t₀ + h, φ r := by
  have hint : ∀ a b, a ∈ Icc t₀ (T + h) → b ∈ Icc t₀ (T + h) →
      IntervalIntegrable φ volume a b := fun a b ha hb ↦
    (hφ.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hA : t₀ ∈ Icc t₀ (T + h) := ⟨le_rfl, by linarith⟩
  have hB : T ∈ Icc t₀ (T + h) := ⟨hT, by linarith⟩
  have hC : t₀ + h ∈ Icc t₀ (T + h) := ⟨by linarith, by linarith⟩
  have hD : T + h ∈ Icc t₀ (T + h) := ⟨by linarith, le_rfl⟩
  rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_comp_add_right (fun t ↦ φ t) h]
    rw [intervalIntegral.integral_interval_sub_interval_comm' (hint _ _ hC hD)
      (hint _ _ hA hB) (hint _ _ hC hA)]
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hT]
    exact hφ.comp (continuous_add_const h).continuousOn fun t ht ↦
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · exact hint _ _ hA hB

theorem measureReal_prod_Ioc' (U : Set (E d)) {a b : ℝ} (hab : a ≤ b) :
    volume.real (U ×ˢ Ioc a b) = volume.real U * (b - a) := by
  rw [measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), measureReal_def]

/-! ### The estimate at a fixed `h` -/

section FixedH

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {G : E d → E d}
  {u : E d × ℝ → ℝ}

set_option maxHeartbeats 800000 in
-- The combination of the Step B identity with all the error estimates is a long proof.
/-- **Step C at a fixed `h`.** With `P = ½ ∫_U |V(T)/h|²`, `X = ∫_{t₀}^T ∫_U (v/h)²`,
`R = ½ ∫_U |V(t₀)/h|²`, and if `u` oscillates by at most `η` over time windows of length `h`
(and stays `η`-close to `g` on `[t₀, t₀ + h]`):
`P + X ≤ R - ∫_U (B(u(T)) - B(g)) + 2 M η |U| + L η (X/2 + |U| T / 2)` and
`X ≤ 2 R + M² |U| T`. -/
theorem fixed_h_estimate (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : IsReactionProfile β) (hu : IsSemilinearSolution U Q β ε g u)
    {M L : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x ∈ U, ∀ z, |Q x ^ 2 * betaEps β ε z| ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ U, ∀ z₁ z₂, |Q x ^ 2 * betaEps β ε z₁ - Q x ^ 2 * betaEps β ε z₂| ≤
      L * |z₁ - z₂|)
    {h t₀ T η : ℝ} (hh : 0 < h) (ht₀ : 0 < t₀) (hT : t₀ ≤ T) (hη : 0 ≤ η)
    (hmod : ∀ x ∈ U, ∀ t ∈ Icc t₀ (T + h), ∀ r ∈ Icc t₀ (T + h), |r - t| ≤ h →
      |u (x, r) - u (x, t)| ≤ η)
    (hdata : ∀ x ∈ U, ∀ r ∈ Icc t₀ (t₀ + h), |u (x, r) - g x| ≤ η)
    (hA : ∫⁻ p in U ×ˢ Ioc 0 (T + h), ENNReal.ofReal (‖gradₓ u p‖ ^ 2) < ⊤) :
    (∫ x in U, ‖avgGrad u h (x, T)‖ ^ 2) / 2 / h ^ 2 +
        (∫ p in U ×ˢ Ioc t₀ T, dq u h p ^ 2) / h ^ 2 ≤
      (∫ x in U, ‖avgGrad u h (x, t₀)‖ ^ 2) / 2 / h ^ 2 -
        (∫ x in U, (potential Q β ε x (u (x, T)) - potential Q β ε x (g x))) +
          2 * M * η * volume.real U +
            L * η * ((∫ p in U ×ˢ Ioc t₀ T, dq u h p ^ 2) / h ^ 2 / 2 + volume.real U * T / 2) ∧
    (∫ p in U ×ˢ Ioc t₀ T, dq u h p ^ 2) / h ^ 2 ≤
      2 * ((∫ x in U, ‖avgGrad u h (x, t₀)‖ ^ 2) / 2 / h ^ 2) + M ^ 2 * volume.real U * T := by
  have hβc : Continuous β := hβ.continuous
  have hM' : ∀ p ∈ U ×ˢ Ioi 0, |reaction Q β ε u p| ≤ M := fun p hp ↦ hM p.1 hp.1 _
  set Ω := U ×ˢ Ioc t₀ T with hΩdef
  have hΩm : MeasurableSet Ω := hU.measurableSet.prod measurableSet_Ioc
  have hΩb : Bornology.IsBounded Ω := hUb.prod (Metric.isBounded_Ioc t₀ T)
  have hΩ : Ω ⊆ U ×ˢ Ioi 0 := fun p hp ↦ ⟨hp.1, ht₀.trans hp.2.1⟩
  have hvolΩ : volume.real Ω = volume.real U * (T - t₀) := measureReal_prod_Ioc' U hT
  have hvolU : 0 ≤ volume.real U := measureReal_nonneg
  have hvolΩT : volume.real Ω ≤ volume.real U * T := by
    rw [hvolΩ]; exact mul_le_mul_of_nonneg_left (by linarith) hvolU
  have hB := steklov_identity hU hUb hQ hβc hu hh.le hM' ht₀ hT hA
  -- bounds and integrability on `Ω`
  obtain ⟨C₁, hC₁⟩ := (hUb.isCompact_closure.prod (isCompact_Icc (a := (0 : ℝ)) (b := T))
    ).exists_bound_of_continuousOn ((continuousOn_dq hu hh.le).mono
      (prod_mono le_rfl Icc_subset_Ici_self))
  have hv : ∀ p ∈ Ω, |dq u h p| ≤ C₁ := fun p hp ↦ by
    simpa using hC₁ p ⟨subset_closure hp.1, (ht₀.trans hp.2.1).le, hp.2.2⟩
  have hF : ∀ p ∈ Ω, |avgRxn Q β ε u h p| ≤ M * h := fun p hp ↦
    abs_avgRxn_le hM' hh.le hp.1 (ht₀.trans hp.2.1)
  have hdqc : ContinuousOn (dq u h) Ω :=
    (continuousOn_dq hu hh.le).mono fun p hp ↦ ⟨subset_closure hp.1, (ht₀.trans hp.2.1).le⟩
  have hFc : ContinuousOn (avgRxn Q β ε u h) Ω :=
    (continuousOn_avgRxn hU hQ hβc hu hh.le).mono hΩ
  set ΔB : E d × ℝ → ℝ := fun p ↦
    potential Q β ε p.1 (u (p.1, p.2 + h)) - potential Q β ε p.1 (u p) with hΔB
  have hpotc : ContinuousOn (fun q : E d × ℝ ↦ potential Q β ε q.1 q.2) (U ×ˢ univ) := by
    have hBc : Continuous (bigBEps β ε) :=
      continuous_iff_continuousAt.2 fun z ↦ (hβ.hasDerivAt_bigBEps ε z).continuousAt
    exact ((hQ.comp continuousOn_fst fun q hq ↦ hq.1).pow 2).mul
      (hBc.comp continuous_snd).continuousOn
  have hu2c : ContinuousOn (fun p : E d × ℝ ↦ u (p.1, p.2 + h)) Ω :=
    hu.2.1.1.comp (by fun_prop : Continuous fun p : E d × ℝ ↦ (p.1, p.2 + h)).continuousOn
      fun p hp ↦ ⟨hp.1, by have := ht₀.trans hp.2.1; simp only [mem_Ioi]; linarith⟩
  have hΔBc : ContinuousOn ΔB Ω :=
    (hpotc.comp ((continuousOn_fst).prodMk hu2c) fun p hp ↦ ⟨hp.1, mem_univ _⟩).sub
      (hpotc.comp ((continuousOn_fst).prodMk (hu.2.1.1.mono hΩ)) fun p hp ↦ ⟨hp.1, mem_univ _⟩)
  have hΔBb : ∀ p ∈ Ω, |ΔB p| ≤ M * C₁ := fun p hp ↦ by
    refine (abs_potential_sub_le hβ (hM p.1 hp.1) _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (hv p hp) hM0
  have hi1 : IntegrableOn (fun p ↦ dq u h p ^ 2) Ω :=
    integrableOn_of_continuousOn_of_bdd hΩm hΩb (hdqc.pow 2) (C := C₁ ^ 2) fun p hp ↦ by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hv p hp) 2
  have hi2 : IntegrableOn (fun p ↦ dq u h p * avgRxn Q β ε u h p) Ω :=
    integrableOn_of_continuousOn_of_bdd hΩm hΩb (hdqc.mul hFc) (C := C₁ * (M * h))
      fun p hp ↦ by
        rw [abs_mul]
        exact mul_le_mul (hv p hp) (hF p hp) (abs_nonneg _) ((abs_nonneg _).trans (hv p hp))
  have hi3 : IntegrableOn ΔB Ω := integrableOn_of_continuousOn_of_bdd hΩm hΩb hΔBc hΔBb
  have hi4 : IntegrableOn (fun p ↦ |dq u h p|) Ω :=
    integrableOn_of_continuousOn_of_bdd hΩm hΩb hdqc.abs (C := C₁) fun p hp ↦ by
      rw [abs_abs]; exact hv p hp
  have hconst : IntegrableOn (fun _ : E d × ℝ ↦ (1 : ℝ)) Ω :=
    integrableOn_const hΩb.measure_lt_top.ne
  set X₀ := ∫ p in Ω, dq u h p ^ 2 with hX₀
  set IY := ∫ p in Ω, dq u h p * avgRxn Q β ε u h p with hIY
  set IB := ∫ p in Ω, ΔB p with hIB
  have hX₀nn : 0 ≤ X₀ := setIntegral_nonneg hΩm fun p _ ↦ sq_nonneg _
  have hh2 : 0 < h ^ 2 := by positivity
  -- (e4) crude bound on the reaction term
  have hc2 : IntegrableOn (fun _ : E d × ℝ ↦ (M * h) ^ 2 / 2) Ω :=
    integrableOn_const hΩb.measure_lt_top.ne
  have hYcrude : |IY| ≤ X₀ / 2 + (M * h) ^ 2 / 2 * volume.real Ω := by
    have : |IY| ≤ ∫ p in Ω, (dq u h p ^ 2 / 2 + (M * h) ^ 2 / 2) := by
      rw [hIY]
      refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hi2.abs
        ((hi1.div_const 2).add hc2) hΩm fun p hp ↦ ?_)
      rw [abs_mul]
      have h1 := mul_le_mul_of_nonneg_left (hF p hp) (abs_nonneg (dq u h p))
      have h2 := two_mul_le_add_sq |dq u h p| (M * h)
      have h3 := sq_abs (dq u h p)
      linarith
    rw [integral_add (hi1.div_const 2) (integrableOn_const hΩb.measure_lt_top.ne),
      integral_div, setIntegral_const, smul_eq_mul] at this
    linarith
  -- (e1) the reaction error
  have hptErr : ∀ p ∈ Ω, |dq u h p * avgRxn Q β ε u h p - h * ΔB p| ≤
      h * (L * η * |dq u h p|) := by
    intro p hp
    set x := p.1
    set t := p.2
    have hx : x ∈ U := hp.1
    have ht : t ∈ Ioc t₀ T := hp.2
    have hwin : ∀ r ∈ Icc t (t + h), r ∈ Icc t₀ (T + h) := fun r hr ↦
      ⟨ht.1.le.trans hr.1, by linarith [hr.2, ht.2]⟩
    have htI : t ∈ Icc t₀ (T + h) := ⟨ht.1.le, by linarith [ht.2]⟩
    have hthI : t + h ∈ Icc t₀ (T + h) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc : ∀ z ∈ uIcc (u (x, t)) (u (x, t + h)),
        |Q x ^ 2 * betaEps β ε z - avgRxn Q β ε u h (x, t) / h| ≤ L * η := by
      intro z hz
      rw [abs_sub_comm]
      refine abs_average_sub_le hh ?_ fun r hr ↦ ?_
      · exact (continuousOn_reaction hQ hβc hu.2.1.1).comp
          (by fun_prop : Continuous fun r : ℝ ↦ (x, r)).continuousOn
          fun r hr ↦ ⟨hx, ht₀.trans (ht.1.trans_le hr.1)⟩
      · refine (hL x hx _ _).trans (mul_le_mul_of_nonneg_left ?_ hL0)
        rw [abs_sub_comm]
        refine abs_sub_le_of_mem_uIcc hz ?_ ?_
        · rw [abs_sub_comm]
          exact hmod x hx t htI r (hwin r hr)
            (by rw [abs_le]; constructor <;> linarith [hr.1, hr.2])
        · rw [abs_sub_comm]
          exact hmod x hx (t + h) hthI r (hwin r hr)
            (by rw [abs_le]; constructor <;> linarith [hr.1, hr.2])
    have := abs_potential_sub_sub_le hβ x hc
    have e : dq u h p * avgRxn Q β ε u h p - h * ΔB p =
        -h * (potential Q β ε x (u (x, t + h)) - potential Q β ε x (u (x, t)) -
          avgRxn Q β ε u h (x, t) / h * (u (x, t + h) - u (x, t))) := by
      simp only [hΔB, dq, x, t]
      field_simp
      ring
    rw [e, abs_mul, abs_neg, abs_of_pos hh]
    refine mul_le_mul_of_nonneg_left ?_ hh.le
    simpa [dq, x, t] using this
  have hErr : |IY - h * IB| ≤ L * η * (X₀ / 2 + h ^ 2 / 2 * volume.real Ω) := by
    have h1 : |IY - h * IB| ≤ ∫ p in Ω, h * (L * η * |dq u h p|) := by
      rw [hIY, hIB, ← integral_const_mul, ← integral_sub hi2 (hi3.const_mul h)]
      refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on
        (hi2.sub (hi3.const_mul h)).abs ((hi4.const_mul (L * η)).const_mul h) hΩm hptErr)
    have h2 : ∫ p in Ω, h * (L * η * |dq u h p|) ≤
        ∫ p in Ω, L * η * (dq u h p ^ 2 / 2 + h ^ 2 / 2) := by
      refine setIntegral_mono_on ((hi4.const_mul (L * η)).const_mul h)
        (((hi1.div_const 2).add (integrableOn_const hΩb.measure_lt_top.ne)).const_mul (L * η))
        hΩm fun p _ ↦ ?_
      have hLη : 0 ≤ L * η := mul_nonneg hL0 hη
      have : h * |dq u h p| ≤ dq u h p ^ 2 / 2 + h ^ 2 / 2 := by
        linarith [sq_nonneg (|dq u h p| - h), sq_abs (dq u h p)]
      linarith [mul_le_mul_of_nonneg_left this hLη]
    have h3 : ∫ p in Ω, L * η * (dq u h p ^ 2 / 2 + h ^ 2 / 2) =
        L * η * (X₀ / 2 + h ^ 2 / 2 * volume.real Ω) := by
      rw [integral_const_mul, integral_add (hi1.div_const 2)
        (integrableOn_const hΩb.measure_lt_top.ne), integral_div, setIntegral_const,
        smul_eq_mul, mul_comm (volume.real Ω)]
    linarith
  -- (e2) the telescoped term
  have hphic : ∀ x ∈ U, ContinuousOn (fun r ↦ potential Q β ε x (u (x, r))) (Ioi 0) :=
    fun x hx ↦ (continuous_potential hβ Q ε x).comp_continuousOn
      (continuousOn_slice_Ioi hu.2.1.1 hx)
  have hIB : IB = ∫ x in U, ((∫ r in T..T + h, potential Q β ε x (u (x, r))) -
      ∫ r in t₀..t₀ + h, potential Q β ε x (u (x, r))) := by
    have hi3' : Integrable ΔB ((volume.restrict U).prod (volume.restrict (Ioc t₀ T))) := by
      rw [← restrict_prod_eq]; exact hi3
    rw [hIB, hΩdef, restrict_prod_eq, integral_prod _ hi3']
    refine setIntegral_congr_fun hU.measurableSet fun x hx ↦ ?_
    exact integral_telescope hT hh.le ((hphic x hx).mono fun r hr ↦ ht₀.trans_le hr.1)
  have hbdT : ∀ x ∈ U, |(∫ r in T..T + h, potential Q β ε x (u (x, r))) / h -
      potential Q β ε x (u (x, T))| ≤ M * η := by
    intro x hx
    refine abs_average_sub_le hh ((hphic x hx).mono fun r hr ↦
      (ht₀.trans_le hT).trans_le hr.1) fun r hr ↦ ?_
    refine (abs_potential_sub_le hβ (hM x hx) _ _).trans (mul_le_mul_of_nonneg_left ?_ hM0)
    exact hmod x hx T ⟨hT, by linarith⟩ r ⟨hT.trans hr.1, hr.2⟩
      (by rw [abs_le]; constructor <;> linarith [hr.1, hr.2])
  have hbd0 : ∀ x ∈ U, |(∫ r in t₀..t₀ + h, potential Q β ε x (u (x, r))) / h -
      potential Q β ε x (g x)| ≤ M * η := by
    intro x hx
    refine abs_average_sub_le hh ((hphic x hx).mono fun r hr ↦ ht₀.trans_le hr.1)
      fun r hr ↦ ?_
    exact (abs_potential_sub_le hβ (hM x hx) _ _).trans
      (mul_le_mul_of_nonneg_left (hdata x hx r hr) hM0)
  -- integrability of the `x`-integrands
  have hi3' : Integrable ΔB ((volume.restrict U).prod (volume.restrict (Ioc t₀ T))) := by
    rw [← restrict_prod_eq]; exact hi3
  have hItel : IntegrableOn (fun x ↦ ((∫ r in T..T + h, potential Q β ε x (u (x, r))) -
      ∫ r in t₀..t₀ + h, potential Q β ε x (u (x, r)))) U := by
    refine hi3'.integral_prod_left.congr ?_
    refine (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
    exact integral_telescope hT hh.le ((hphic x hx).mono fun r hr ↦ ht₀.trans_le hr.1)
  obtain ⟨C₂, hC₂⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn
    ((continuousOn_slice hu (ht₀.trans_le hT).le).sub (continuousOn_data hu))
  have hDc : ContinuousOn (fun x ↦ potential Q β ε x (u (x, T)) - potential Q β ε x (g x)) U :=
    ((hpotc.comp (continuousOn_id.prodMk ((continuousOn_slice hu (ht₀.trans_le hT).le).mono
      subset_closure)) fun x hx ↦ ⟨hx, mem_univ _⟩).sub
    (hpotc.comp (continuousOn_id.prodMk ((continuousOn_data hu).mono subset_closure))
      fun x hx ↦ ⟨hx, mem_univ _⟩))
  have hID : IntegrableOn (fun x ↦ potential Q β ε x (u (x, T)) - potential Q β ε x (g x)) U :=
    ⟨hDc.aestronglyMeasurable hU.measurableSet, .restrict_of_bounded (C := M * C₂)
      hUb.measure_lt_top ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall
        fun x hx ↦ by
          rw [Real.norm_eq_abs]
          refine (abs_potential_sub_le hβ (hM x hx) _ _).trans
            (mul_le_mul_of_nonneg_left ?_ hM0)
          simpa using hC₂ x (subset_closure hx)))⟩
  have hIBID : |IB / h - ∫ x in U, (potential Q β ε x (u (x, T)) - potential Q β ε x (g x))| ≤
      2 * M * η * volume.real U := by
    rw [hIB, ← integral_div, ← integral_sub (hItel.div_const h) hID]
    have hb : ∀ x ∈ U, |((∫ r in T..T + h, potential Q β ε x (u (x, r))) -
        ∫ r in t₀..t₀ + h, potential Q β ε x (u (x, r))) / h -
          (potential Q β ε x (u (x, T)) - potential Q β ε x (g x))| ≤ 2 * M * η := by
      intro x hx
      have := abs_sub_le_iff.1 (hbdT x hx)
      have := abs_sub_le_iff.1 (hbd0 x hx)
      rw [sub_div, abs_le]
      constructor <;> linarith
    calc _ ≤ ∫ x in U, 2 * M * η :=
          (abs_integral_le_integral_abs).trans (setIntegral_mono_on
            ((hItel.div_const h).sub hID).abs
            (integrableOn_const hUb.measure_lt_top.ne) hU.measurableSet hb)
      _ = 2 * M * η * volume.real U := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hVTnn : 0 ≤ ∫ x in U, ‖avgGrad u h (x, T)‖ ^ 2 :=
    setIntegral_nonneg hU.measurableSet fun _ _ ↦ sq_nonneg _
  have hΩnn : 0 ≤ volume.real Ω := measureReal_nonneg
  have hLη : 0 ≤ L * η := mul_nonneg hL0 hη
  constructor
  · -- `P + X = R - IY / h²` and `IY / h² ≥ IB / h - |IY - h IB| / h²`
    have hE : |IY / h ^ 2 - IB / h| ≤ L * η * (X₀ / h ^ 2 / 2 + volume.real U * T / 2) := by
      have e : IY / h ^ 2 - IB / h = (IY - h * IB) / h ^ 2 := by field_simp
      rw [e, abs_div, abs_of_pos hh2, div_le_iff₀ hh2]
      refine hErr.trans ?_
      have : h ^ 2 / 2 * volume.real Ω ≤ h ^ 2 * (volume.real U * T / 2) := by
        linarith [mul_le_mul_of_nonneg_left hvolΩT (sq_nonneg h)]
      have hX : X₀ / 2 = X₀ / h ^ 2 / 2 * h ^ 2 := by field_simp
      have hA : X₀ / 2 + h ^ 2 / 2 * volume.real Ω ≤
          (X₀ / h ^ 2 / 2 + volume.real U * T / 2) * h ^ 2 := by
        rw [hX]; linarith
      linarith [mul_le_mul_of_nonneg_left hA hLη]
    have hmain : (∫ x in U, ‖avgGrad u h (x, T)‖ ^ 2) / 2 / h ^ 2 + X₀ / h ^ 2 =
        (∫ x in U, ‖avgGrad u h (x, t₀)‖ ^ 2) / 2 / h ^ 2 - IY / h ^ 2 := by
      rw [← add_div, ← sub_div, hB]
    rw [hmain]
    have := abs_sub_le_iff.1 hE
    have := abs_sub_le_iff.1 hIBID
    linarith
  · have hX : X₀ ≤ (∫ x in U, ‖avgGrad u h (x, t₀)‖ ^ 2) + (M * h) ^ 2 * volume.real Ω := by
      have := neg_abs_le IY
      linarith
    rw [div_le_iff₀ hh2]
    have : (M * h) ^ 2 * volume.real Ω ≤ M ^ 2 * volume.real U * T * h ^ 2 := by
      rw [mul_pow]
      linarith [mul_le_mul_of_nonneg_left hvolΩT (mul_nonneg (sq_nonneg M) (sq_nonneg h))]
    have e : 2 * ((∫ x in U, ‖avgGrad u h (x, t₀)‖ ^ 2) / 2 / h ^ 2) * h ^ 2 =
        ∫ x in U, ‖avgGrad u h (x, t₀)‖ ^ 2 := by field_simp
    linarith

end FixedH

/-! ### Limits -/

theorem le_liminf_add_ennreal (a b : ℕ → ℝ≥0∞) :
    liminf a atTop + liminf b atTop ≤ liminf (fun n ↦ a n + b n) atTop := by
  have hmono : ∀ c : ℕ → ℝ≥0∞, Monotone fun n ↦ ⨅ i ≥ n, c i :=
    fun c n m h ↦ biInf_mono fun i hi ↦ h.trans hi
  rw [liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat,
    ENNReal.iSup_add_iSup_of_monotone (hmono a) (hmono b)]
  exact iSup_mono fun n ↦ le_iInf₂ fun i hi ↦ add_le_add (iInf₂_le i hi) (iInf₂_le i hi)

/-- The Steklov step sizes `hₙ = 1/(n + 2)`. -/
noncomputable def step (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem step_pos (n : ℕ) : 0 < step n := by unfold step; positivity

theorem step_le_half (n : ℕ) : step n ≤ 1 / 2 := by
  unfold step
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

theorem tendsto_step : Tendsto step atTop (𝓝 0) := by
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop := tendsto_add_atTop_nat 1
  refine (this.comp h2).congr fun n ↦ ?_
  simp only [Function.comp, step, Nat.cast_add, Nat.cast_one]
  ring

theorem tendsto_step_ne : Tendsto step atTop (𝓝[≠] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_step, Eventually.of_forall fun n ↦ (step_pos n).ne'⟩

theorem eventually_step_lt {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ n in atTop, step n < δ :=
  tendsto_step.eventually (gt_mem_nhds hδ)

section Limits

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {G : E d → E d}
  {u : E d × ℝ → ℝ}

/-- `h⁻¹ V(x, T) → ∇u(x, T)`. -/
theorem tendsto_avgGrad (hu : IsSemilinearSolution U Q β ε g u) {x : E d} (hx : x ∈ U) {T : ℝ}
    (hT : 0 < T) :
    Tendsto (fun n ↦ (step n)⁻¹ • avgGrad u (step n) (x, T)) atTop (𝓝 (gradₓ u (x, T))) := by
  have hc := continuousOn_slice_Ioi hu.2.1.2.2.1 hx
  have hd : HasDerivAt (fun s ↦ ∫ r in T..s, gradₓ u (x, r)) (gradₓ u (x, T)) T :=
    intervalIntegral.integral_hasDerivAt_right (by simp)
      (hc.stronglyMeasurableAtFilter isOpen_Ioi T hT) (hc.continuousAt (isOpen_Ioi.mem_nhds hT))
  refine (hd.tendsto_slope_zero.comp tendsto_step_ne).congr fun n ↦ ?_
  simp [avgGrad]

/-- `h⁻¹ v(x, t) → ∂ₜu(x, t)`. -/
theorem tendsto_dq (hu : IsSemilinearSolution U Q β ε g u) {p : E d × ℝ}
    (hp : p ∈ U ×ˢ Ioi 0) :
    Tendsto (fun n ↦ dq u (step n) p / step n) atTop (𝓝 (dₜ u p)) := by
  have hd : HasDerivAt (fun s ↦ u (p.1, s)) (dₜ u p) p.2 := (hu.2.1.2.2.2.2.1 p hp).hasDerivAt
  refine (hd.tendsto_slope_zero.comp tendsto_step_ne).congr fun n ↦ ?_
  simp only [Function.comp, dq, smul_eq_mul]
  rw [div_eq_inv_mul]

/-- `∫_U |V(t₀)|² ≤ h K` if `∫_{U × (0, t₀ + h]} |∇u|² ≤ K`. -/
theorem integral_norm_avgGrad_sq_le (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    {h t₀ K : ℝ} (hh : 0 ≤ h) (ht₀ : 0 < t₀) (hK : 0 ≤ K)
    (hbd : ∫⁻ p in U ×ˢ Ioc 0 (t₀ + h), ENNReal.ofReal (‖gradₓ u p‖ ^ 2) ≤ ENNReal.ofReal K) :
    ∫ x in U, ‖avgGrad u h (x, t₀)‖ ^ 2 ≤ h * K := by
  have hint := integrableOn_norm_avgGrad_sq hU hu hh ht₀ le_rfl
    (hbd.trans_lt ENNReal.ofReal_lt_top)
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ ↦ sq_nonneg _)]
  calc ∫⁻ x in U, ENNReal.ofReal (‖avgGrad u h (x, t₀)‖ ^ 2)
      ≤ ∫⁻ x in U, ENNReal.ofReal h *
          ∫⁻ r in Ioc 0 (t₀ + h), ENNReal.ofReal (‖gradₓ u (x, r)‖ ^ 2) :=
        setLIntegral_mono' hU.measurableSet fun x hx ↦
          ofReal_norm_avgGrad_sq_le hu hh hx ht₀ le_rfl
    _ = ENNReal.ofReal h * ∫⁻ p in U ×ˢ Ioc 0 (t₀ + h), ENNReal.ofReal (‖gradₓ u p‖ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_iterated_eq hU hu le_rfl]
    _ ≤ ENNReal.ofReal h * ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (h * K) := (ENNReal.ofReal_mul hh).symm

/-- **Fatou at time `T`.** -/
theorem lintegral_grad_T_le_liminf (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    {T : ℝ} (hT : 0 < T)
    (hfin : ∀ s > 0, ∫⁻ p in U ×ˢ Ioc 0 s, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) < ⊤) :
    ∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, T)‖ ^ 2 / 2) ≤
      liminf (fun n ↦ ENNReal.ofReal
        ((∫ x in U, ‖avgGrad u (step n) (x, T)‖ ^ 2) / 2 / step n ^ 2)) atTop := by
  have hval : ∀ n, ENNReal.ofReal ((∫ x in U, ‖avgGrad u (step n) (x, T)‖ ^ 2) / 2 / step n ^ 2) =
      ∫⁻ x in U, ENNReal.ofReal (‖(step n)⁻¹ • avgGrad u (step n) (x, T)‖ ^ 2 / 2) := by
    intro n
    have hint := integrableOn_norm_avgGrad_sq hU hu (step_pos n).le hT le_rfl
      (hfin (T + step n) (by linarith [step_pos n]))
    have e : ∀ x, ‖(step n)⁻¹ • avgGrad u (step n) (x, T)‖ ^ 2 / 2 =
        ‖avgGrad u (step n) (x, T)‖ ^ 2 / 2 / step n ^ 2 := by
      intro x
      rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos (step_pos n), inv_pow]
      field_simp
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal ((hint.div_const 2).div_const _)
      (Eventually.of_forall fun _ ↦ by positivity), integral_div, integral_div]
  simp_rw [hval]
  calc ∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, T)‖ ^ 2 / 2)
      = ∫⁻ x in U, liminf (fun n ↦
          ENNReal.ofReal (‖(step n)⁻¹ • avgGrad u (step n) (x, T)‖ ^ 2 / 2)) atTop := by
        refine setLIntegral_congr_fun hU.measurableSet fun x hx ↦ ?_
        refine (Tendsto.liminf_eq ?_).symm
        exact (ENNReal.continuous_ofReal.tendsto _).comp
          ((((tendsto_avgGrad hu hx hT).norm).pow 2).div_const 2)
    _ ≤ _ := by
        refine lintegral_liminf_le' fun n ↦ ?_
        refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
        have hc : ContinuousOn (fun x ↦ avgGrad u (step n) (x, T)) U :=
          (continuousOn_avgGrad hU hu (step_pos n).le).comp
            (by fun_prop : Continuous fun x : E d ↦ (x, T)).continuousOn fun x hx ↦ ⟨hx, hT⟩
        exact (((continuousOn_const.smul hc).norm.pow 2).div_const 2).aemeasurable
          hU.measurableSet

/-- **Fatou for the time derivative.** -/
theorem lintegral_dt_sq_le_liminf (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) {T : ℝ} :
    ∫⁻ p in U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ u p ^ 2) ≤
      liminf (fun n ↦ ENNReal.ofReal
        ((∫ p in U ×ˢ Ioc (step n ^ 2) T, dq u (step n) p ^ 2) / step n ^ 2)) atTop := by
  set A := U ×ˢ Ioc (0 : ℝ) T with hA
  have hAm : MeasurableSet A := hU.measurableSet.prod measurableSet_Ioc
  set f : ℕ → E d × ℝ → ℝ≥0∞ := fun n ↦ (U ×ˢ Ioc (step n ^ 2) T).indicator
    fun p ↦ ENNReal.ofReal ((dq u (step n) p / step n) ^ 2) with hf
  have hval : ∀ n, ENNReal.ofReal
      ((∫ p in U ×ˢ Ioc (step n ^ 2) T, dq u (step n) p ^ 2) / step n ^ 2) = ∫⁻ p in A, f n p := by
    intro n
    have hΩm : MeasurableSet (U ×ˢ Ioc (step n ^ 2) T) := hU.measurableSet.prod measurableSet_Ioc
    have hsub : U ×ˢ Ioc (step n ^ 2) T ⊆ A := fun p hp ↦
      ⟨hp.1, (sq_nonneg _).trans_lt hp.2.1, hp.2.2⟩
    rw [hf, setLIntegral_indicator hΩm, inter_eq_left.2 hsub]
    obtain ⟨C₁, hC₁⟩ := (hUb.isCompact_closure.prod (isCompact_Icc (a := (0 : ℝ)) (b := T))
      ).exists_bound_of_continuousOn ((continuousOn_dq hu (step_pos n).le).mono
        (prod_mono le_rfl Icc_subset_Ici_self))
    have hi : IntegrableOn (fun p ↦ dq u (step n) p ^ 2) (U ×ˢ Ioc (step n ^ 2) T) :=
      integrableOn_of_continuousOn_of_bdd hΩm (hUb.prod (Metric.isBounded_Ioc _ _))
        (((continuousOn_dq hu (step_pos n).le).mono fun p hp ↦
          ⟨subset_closure hp.1, ((sq_nonneg _).trans hp.2.1.le)⟩).pow 2) (C := C₁ ^ 2)
        fun p hp ↦ by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (by
            simpa using hC₁ p ⟨subset_closure hp.1, (sq_nonneg _).trans hp.2.1.le, hp.2.2⟩) 2
    rw [← integral_div, ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (Eventually.of_forall fun _ ↦ by positivity)]
    congr 1; funext p; rw [div_pow]
  simp_rw [hval]
  calc ∫⁻ p in A, ENNReal.ofReal (dₜ u p ^ 2)
      = ∫⁻ p in A, liminf (fun n ↦ f n p) atTop := by
        refine setLIntegral_congr_fun hAm fun p hp ↦ ?_
        refine (Tendsto.liminf_eq ?_).symm
        have hp' : p ∈ U ×ˢ Ioi 0 := ⟨hp.1, hp.2.1⟩
        have hev : ∀ᶠ n in atTop, step n ^ 2 < p.2 := by
          have h2 : Tendsto (fun n ↦ step n ^ 2) atTop (𝓝 0) := by
            simpa using tendsto_step.pow 2
          exact h2.eventually (gt_mem_nhds hp.2.1)
        have hlim := (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_dq hu hp').pow 2)
        refine hlim.congr' ?_
        filter_upwards [hev] with n hn
        simp only [hf, Function.comp]
        rw [indicator_of_mem (show p ∈ U ×ˢ Ioc (step n ^ 2) T from ⟨hp.1, hn, hp.2.2⟩)]
    _ ≤ _ := by
        refine lintegral_liminf_le' fun n ↦ ?_
        have hΩm : MeasurableSet (U ×ˢ Ioc (step n ^ 2) T) :=
          hU.measurableSet.prod measurableSet_Ioc
        refine (aemeasurable_indicator_iff hΩm).2 ?_
        rw [Measure.restrict_restrict hΩm]
        refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
        refine ((((continuousOn_dq hu (step_pos n).le).div_const _).pow 2).mono ?_).aemeasurable
          (hΩm.inter hAm)
        exact fun p hp ↦ ⟨subset_closure hp.1.1, ((sq_nonneg _).trans hp.1.2.1.le)⟩

end Limits

/-- A bounded function continuous on a bounded open set `U ⊆ ℝᵈ` is integrable on `U`. -/
theorem integrableOn_of_continuousOn_of_bdd' {U : Set (E d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : E d → ℝ} (hf : ContinuousOn f U) {C : ℝ}
    (hC : ∀ x ∈ U, |f x| ≤ C) : IntegrableOn f U :=
  ⟨hf.aestronglyMeasurable hU.measurableSet, .restrict_of_bounded (C := C) hUb.measure_lt_top
    ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun x hx ↦ by
      rw [Real.norm_eq_abs]; exact hC x hx))⟩

end EnergyDissipation

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
-- The final assembly (limits, Fatou, and the energy bookkeeping) is long.
open EnergyDissipation in
/-- **Energy dissipation inequality** (the statement of
`Registry.semilinear_energy_dissipation`; (A.1), i.e. (3.8), with `≤`). The paper states equality;
here we prove only `≤`, because only the inequality is used. Under the standing assumptions, for
`ε > 0`, data `g ∈ H¹(U)` with weak gradient `G`, and a solution `u` of (3.4) (so `g = u(·, 0)`
is continuous on `Ū`), for every `T > 0`,
`½ J(u(T), χ_ε(T); U) + ∫₀ᵀ ∫_U (∂ₜu)² ≤ ½ J(g, χ_ε(0); U)`.

Proof: truncation in the values and Steklov averages, so that every
integration by parts is interior (`EnergyDissipationStepA`, `EnergyDissipationStepB`), and the
limit `h → 0` of the Steklov identity (`fixed_h_estimate`, Fatou). -/
theorem semilinear_energy_dissipation (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {ε : ℝ} (hε : 0 < ε) {g : E d → ℝ} {G : E d → E d} (hg : MemH1 S.U g G)
    {u : E d × ℝ → ℝ} (hu : IsSemilinearSolution S.U S.Q β ε g u) {T : ℝ} (hT : 0 < T) :
    energyJχ S.U S.Q (fun x ↦ gradₓ u (x, T)) (fun x ↦ chiEps β ε u (x, T)) / 2 +
        ∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ u p ^ 2) ≤
      energyJχ S.U S.Q G (fun x ↦ chiEps β ε u (x, 0)) / 2 := by
  set U := S.U with hUdef
  have hU : IsOpen U := S.isOpen
  have hUb : Bornology.IsBounded U := S.isBounded
  have hQc : ContinuousOn S.Q (closure U) := by
    obtain ⟨K, hK⟩ := S.lip; exact hK.continuousOn
  have hQ : ContinuousOn S.Q U := hQc.mono subset_closure
  obtain ⟨M, hM0, hMb⟩ := exists_reaction_bound hβ S hε
  obtain ⟨L, hL0, hLb⟩ := exists_reaction_lipschitz hβ S hε
  have hMU : ∀ x ∈ U, ∀ z, |S.Q x ^ 2 * betaEps β ε z| ≤ M := fun x hx ↦
    hMb x (subset_closure hx)
  have hLU : ∀ x ∈ U, ∀ z₁ z₂, |S.Q x ^ 2 * betaEps β ε z₁ - S.Q x ^ 2 * betaEps β ε z₂| ≤
      L * |z₁ - z₂| := fun x hx ↦ hLb x (subset_closure hx)
  have hM' : ∀ p ∈ U ×ˢ Ioi 0, |reaction S.Q β ε u p| ≤ M := fun p hp ↦ hMU p.1 hp.1 _
  have hfin : ∀ s > 0, ∫⁻ p in U ×ˢ Ioc 0 s, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) < ⊤ :=
    fun s hs ↦ lintegral_grad_sq_lt_top hU hUb hQ hβ.continuous hu hg hM' hs
  set Gn := ∫ x in U, ‖G x‖ ^ 2 with hGn
  have hGn0 : 0 ≤ Gn := setIntegral_nonneg hU.measurableSet fun _ _ ↦ sq_nonneg _
  set vU := volume.real U with hvU
  have hvU0 : 0 ≤ vU := measureReal_nonneg
  -- the potentials
  have hpotb : ∀ x ∈ U, ∀ z, |potential S.Q β ε x z| ≤ S.Qmax ^ 2 := by
    intro x hx z
    obtain ⟨h1, h2⟩ := S.Q_mem x (subset_closure hx)
    have hQ0 : 0 ≤ S.Q x := S.Qmin_pos.le.trans h1
    rw [abs_of_nonneg (potential_nonneg hβ _ hε.ne' _ _), potential]
    have := hβ.bigBEps_le_half hε.ne' z
    have := pow_le_pow_left₀ hQ0 h2 2
    linarith [mul_le_mul_of_nonneg_left (hβ.bigBEps_le_half hε.ne' z) (sq_nonneg (S.Q x)),
      sq_nonneg S.Qmax]
  have hBc : Continuous (bigBEps β ε) :=
    continuous_iff_continuousAt.2 fun z ↦ (hβ.hasDerivAt_bigBEps ε z).continuousAt
  have hpotT_c : ContinuousOn (fun x ↦ potential S.Q β ε x (u (x, T))) U :=
    (hQ.pow 2).mul (hBc.comp_continuousOn ((continuousOn_slice hu hT.le).mono subset_closure))
  have hpot0_c : ContinuousOn (fun x ↦ potential S.Q β ε x (g x)) U :=
    (hQ.pow 2).mul (hBc.comp_continuousOn ((continuousOn_data hu).mono subset_closure))
  have hpotT : IntegrableOn (fun x ↦ potential S.Q β ε x (u (x, T))) U :=
    integrableOn_of_continuousOn_of_bdd' hU hUb hpotT_c fun x hx ↦ hpotb x hx _
  have hpot0 : IntegrableOn (fun x ↦ potential S.Q β ε x (g x)) U :=
    integrableOn_of_continuousOn_of_bdd' hU hUb hpot0_c fun x hx ↦ hpotb x hx _
  set ZT := ∫ x in U, potential S.Q β ε x (u (x, T)) with hZT
  set W0 := ∫ x in U, potential S.Q β ε x (g x) with hW0
  have hZT0 : 0 ≤ ZT := setIntegral_nonneg hU.measurableSet fun x _ ↦
    potential_nonneg hβ _ hε.ne' _ _
  set D := Gn / 2 - (ZT - W0) with hD
  -- the sequences
  set P : ℕ → ℝ := fun n ↦ (∫ x in U, ‖avgGrad u (step n) (x, T)‖ ^ 2) / 2 / step n ^ 2 with hP
  set X : ℕ → ℝ := fun n ↦
    (∫ p in U ×ˢ Ioc (step n ^ 2) T, dq u (step n) p ^ 2) / step n ^ 2 with hX
  have hP0 : ∀ n, 0 ≤ P n := fun n ↦ div_nonneg (div_nonneg
    (setIntegral_nonneg hU.measurableSet fun _ _ ↦ sq_nonneg _) zero_le_two) (sq_nonneg _)
  have hX0 : ∀ n, 0 ≤ X n := fun n ↦ div_nonneg
    (setIntegral_nonneg (hU.measurableSet.prod measurableSet_Ioc) fun _ _ ↦ sq_nonneg _)
    (sq_nonneg _)
  set C₀ := Gn + 2 + M ^ 2 * vU * T with hC₀
  set c := 1 + 2 * M * vU + L * (C₀ + vU * T) / 2 with hc
  have hc0 : 0 ≤ c := by positivity
  -- the key eventual estimate
  have hK : ∀ η, 0 < η → η ≤ 1 → ∀ᶠ n in atTop, P n + X n ≤ D + c * η := by
    intro η hη hη1
    obtain ⟨s₀, hs₀, hnear⟩ := exists_energy_near_zero hU hUb hQ hβ.continuous hu hg hM0 hM' hη
    obtain ⟨ρ, hρ, hmod⟩ := exists_time_modulus hUb hu (T + 1) hη
    set δ₁ := min (min (ρ / 2) (s₀ / 2)) (min (η / (Gn + 1)) (min T 1)) with hδ₁
    have hδ₁0 : 0 < δ₁ := lt_min (lt_min (half_pos hρ) (half_pos hs₀))
      (lt_min (div_pos hη (by linarith)) (lt_min hT one_pos))
    filter_upwards [eventually_step_lt hδ₁0] with n hn
    set h := step n with hhdef
    have hh : 0 < h := step_pos n
    have h1 : h < ρ / 2 := hn.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have h2 : h < s₀ / 2 := hn.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have h3 : h < η / (Gn + 1) := hn.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have h4 : h < T := hn.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
    have h5 : h < 1 := hn.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
    have hh2 : h ^ 2 ≤ h := pow_le_of_le_one hh.le h5.le two_ne_zero
    have ht₀ : 0 < h ^ 2 := by positivity
    have ht₀T : h ^ 2 ≤ T := hh2.trans h4.le
    have hA := hfin (T + h) (by linarith)
    have hmod' : ∀ x ∈ U, ∀ t ∈ Icc (h ^ 2) (T + h), ∀ r ∈ Icc (h ^ 2) (T + h), |r - t| ≤ h →
        |u (x, r) - u (x, t)| ≤ η := fun x hx t ht r hr hrt ↦
      (hmod x (subset_closure hx) t ⟨ht₀.le.trans ht.1, by linarith [ht.2]⟩ r
        ⟨ht₀.le.trans hr.1, by linarith [hr.2]⟩ (hrt.trans_lt (by linarith))).le
    have hdata : ∀ x ∈ U, ∀ r ∈ Icc (h ^ 2) (h ^ 2 + h), |u (x, r) - g x| ≤ η := by
      intro x hx r hr
      have := hmod x (subset_closure hx) 0 ⟨le_rfl, by linarith⟩ r
        ⟨ht₀.le.trans hr.1, by linarith [hr.2]⟩ (by
          rw [sub_zero, abs_of_nonneg (ht₀.le.trans hr.1)]; linarith [hr.2])
      rw [hu.2.2.1 x (subset_closure hx)] at this
      exact this.le
    obtain ⟨hmain, hXb⟩ := fixed_h_estimate hU hUb hQ hβ hu hM0 hMU hL0 hLU hh ht₀ ht₀T
      hη.le hmod' hdata hA
    -- the bound on `R`
    have hbd := hnear (h ^ 2 + h) (by positivity) (by linarith)
    have hV := integral_norm_avgGrad_sq_le hU hu hh.le ht₀ (by positivity) hbd
    set R := (∫ x in U, ‖avgGrad u h (x, h ^ 2)‖ ^ 2) / 2 / h ^ 2 with hR
    have hRb : R ≤ Gn / 2 + η := by
      have hhG : h * (Gn + 1) ≤ η := by
        have := (lt_div_iff₀ (by linarith : (0 : ℝ) < Gn + 1)).1 h3
        linarith
      rw [hR, div_div, div_le_iff₀ (by positivity)]
      have : h * ((h ^ 2 + h) * (Gn + η)) = h ^ 2 * 2 * ((1 + h) * (Gn + η) / 2) := by ring
      rw [this] at hV
      have hb : (1 + h) * (Gn + η) / 2 ≤ Gn / 2 + η := by
        linarith [mul_le_mul_of_nonneg_left hη1 hh.le]
      calc _ ≤ h ^ 2 * 2 * ((1 + h) * (Gn + η) / 2) := hV
        _ ≤ (Gn / 2 + η) * (2 * h ^ 2) := by
          linarith [mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ h ^ 2 * 2)]
    have hXC : X n ≤ C₀ := by
      have : X n ≤ 2 * R + M ^ 2 * vU * T := hXb
      linarith
    have hLη : 0 ≤ L * η := mul_nonneg hL0 hη.le
    have hLX : L * η * (X n / 2 + vU * T / 2) ≤ L * η * (C₀ / 2 + vU * T / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hLη
    have hID : (∫ x in U, (potential S.Q β ε x (u (x, T)) - potential S.Q β ε x (g x))) =
        ZT - W0 := integral_sub hpotT hpot0
    have hmain' : P n + X n ≤ R - (ZT - W0) + 2 * M * η * vU +
        L * η * (X n / 2 + vU * T / 2) := by
      rw [← hID]; exact hmain
    have : c * η = η + 2 * M * η * vU + L * η * (C₀ / 2 + vU * T / 2) := by
      rw [hc]; ring
    rw [hD, this]
    linarith
  -- consequences
  have hcη : ∀ ε' : ℝ, 0 < ε' → ∃ η, 0 < η ∧ η ≤ 1 ∧ c * η ≤ ε' := by
    intro ε' hε'
    refine ⟨min 1 (ε' / (c + 1)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    calc c * min 1 (ε' / (c + 1)) ≤ c * (ε' / (c + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hc0
      _ ≤ ε' := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]; linarith
  have hD0 : 0 ≤ D := by
    by_contra hneg
    push Not at hneg
    obtain ⟨η, hη, hη1, hcη'⟩ := hcη (-D / 2) (by linarith)
    obtain ⟨n, hn⟩ := (hK η hη hη1).exists
    linarith [hP0 n, hX0 n]
  have hlim : liminf (fun n ↦ ENNReal.ofReal (P n + X n)) atTop ≤ ENNReal.ofReal D := by
    refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ ↦ ?_
    obtain ⟨η, hη, hη1, hcη'⟩ := hcη ε' hε'
    refine (liminf_le_of_frequently_le' ((hK η hη hη1).mono fun n hn ↦
      ENNReal.ofReal_le_ofReal hn).frequently).trans ?_
    refine ENNReal.ofReal_add_le.trans (add_le_add le_rfl ?_)
    exact (ENNReal.ofReal_le_ofReal hcη').trans (by simp)
  have hPX : (∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, T)‖ ^ 2 / 2)) +
      ∫⁻ p in U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ u p ^ 2) ≤
        liminf (fun n ↦ ENNReal.ofReal (P n + X n)) atTop := by
    have h1 := (add_le_add (lintegral_grad_T_le_liminf hU hu hT hfin)
      (lintegral_dt_sq_le_liminf hU hUb hu (T := T))).trans (le_liminf_add_ennreal _ _)
    refine h1.trans (le_of_eq ?_)
    refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
    exact (ENNReal.ofReal_add (hP0 n) (hX0 n)).symm
  have hLHS := hPX.trans hlim
  -- the energies
  have hhalf : ∀ a : ℝ, 0 ≤ a → ENNReal.ofReal a * 2⁻¹ = ENNReal.ofReal (a / 2) := by
    intro a ha
    rw [div_eq_mul_inv, ENNReal.ofReal_mul ha, ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  have hJT : energyJχ U S.Q (fun x ↦ gradₓ u (x, T)) (fun x ↦ chiEps β ε u (x, T)) / 2 =
      (∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, T)‖ ^ 2 / 2)) + ENNReal.ofReal ZT := by
    rw [energyJχ, div_eq_mul_inv, ← lintegral_mul_const' _ _ (by simp),
      hZT, ofReal_integral_eq_lintegral_ofReal hpotT
        (Eventually.of_forall fun x ↦ potential_nonneg hβ _ hε.ne' _ _)]
    rw [← lintegral_add_left']
    · refine lintegral_congr fun x ↦ ?_
      rw [← ENNReal.ofReal_add (by positivity) (potential_nonneg hβ _ hε.ne' _ _),
        hhalf _ (by
          have := hβ.bigBEps_nonneg hε.ne' (u (x, T))
          simp only [chiEps]; positivity)]
      congr 1
      simp only [chiEps, potential]; ring
    · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      exact ((((hu.2.1.2.2.1.comp (by fun_prop : Continuous fun x : E d ↦ (x, T)).continuousOn
        fun x hx ↦ ⟨hx, hT⟩).norm.pow 2).div_const 2)).aemeasurable hU.measurableSet
  have hJ0 : energyJχ U S.Q G (fun x ↦ chiEps β ε u (x, 0)) / 2 =
      ENNReal.ofReal (Gn / 2 + W0) := by
    have hint : IntegrableOn (fun x ↦ ‖G x‖ ^ 2 / 2 + potential S.Q β ε x (g x)) U :=
      ((integrable_norm_sq_of_memLp hg.2.1).div_const 2).add hpot0
    rw [energyJχ, div_eq_mul_inv, ← lintegral_mul_const' _ _ (by simp), hGn, hW0,
      ← integral_div, ← integral_add ((integrable_norm_sq_of_memLp hg.2.1).div_const 2) hpot0,
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x ↦
        add_nonneg (by positivity) (potential_nonneg hβ _ hε.ne' _ _))]
    refine setLIntegral_congr_fun hU.measurableSet fun x hx ↦ ?_
    rw [hhalf _ (by
        have := hβ.bigBEps_nonneg hε.ne' (u (x, 0))
        simp only [chiEps]; positivity)]
    congr 1
    simp only [chiEps, potential]
    rw [hu.2.2.1 x (subset_closure hx)]; ring
  rw [hJT, hJ0]
  calc (∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, T)‖ ^ 2 / 2)) + ENNReal.ofReal ZT +
        ∫⁻ p in U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ u p ^ 2)
      = ((∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, T)‖ ^ 2 / 2)) +
          ∫⁻ p in U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ u p ^ 2)) + ENNReal.ofReal ZT := by ring
    _ ≤ ENNReal.ofReal D + ENNReal.ofReal ZT := add_le_add hLHS le_rfl
    _ = ENNReal.ofReal (Gn / 2 + W0) := by
        rw [← ENNReal.ofReal_add hD0 hZT0, hD]; congr 1; ring

end PerronVariational

end
