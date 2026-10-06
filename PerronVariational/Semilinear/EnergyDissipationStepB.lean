/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.EnergyDissipationStepA
import GMTFoundations.Sobolev.Lattice
import Mathlib.Order.CompletePartialOrder

/-!
# Energy dissipation, part 3: the Steklov-averaged energy identity (Step B)

Step B of the proof of the energy dissipation inequality (A.1) of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981.
Fix `h > 0` and write, for `x ∈ U` and `t > 0`,
`v(x, t) = u(x, t + h) - u(x, t)`, `V(x, t) = ∫ₜ^{t+h} ∇u(x, r) dr` and
`F(x, t) = ∫ₜ^{t+h} f(x, r) dr` (`f = Q² β_ε(u)`). Since the lateral data do not depend on time,
`v` vanishes on `∂U`; testing the time-integrated equation `∫ₜ^{t+h} Δu = v + F` with the
truncation `T_σ(v(·, t))` (compact support in `U`), letting `σ → 0`, and integrating
`∂ₜ ½|V|² = V · ∇v` in time gives

`½ ∫_U |V(T)|² + ∫_{t₀}^T ∫_U v² = ½ ∫_U |V(t₀)|² - ∫_{t₀}^T ∫_U v F`.

No mixed derivative `∂ₜ∇u` is used.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace ContDiff

@[expose] public section

namespace PerronVariational

namespace EnergyDissipation

variable {d : ℕ}

/-! ### Parametric integrals over a moving time window -/

section Window

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

omit [CompleteSpace F'] in
/-- `∫ₜ^{t+h} a(x, r) dr` is continuous on `U × (0, ∞)` if `a` is. -/
theorem continuousOn_integral_window {U : Set (E d)} (hU : IsOpen U) {a : E d × ℝ → F'}
    (ha : ContinuousOn a (U ×ˢ Ioi 0)) {h : ℝ} (hh : 0 ≤ h) :
    ContinuousOn (fun p : E d × ℝ ↦ ∫ r in p.2..p.2 + h, a (p.1, r)) (U ×ˢ Ioi 0) := by
  have hrw : (fun p : E d × ℝ ↦ ∫ r in p.2..p.2 + h, a (p.1, r)) =
      fun p ↦ ∫ τ in (0 : ℝ)..h, a (p.1, p.2 + τ) := by
    funext p
    rw [intervalIntegral.integral_comp_add_left (fun r ↦ a (p.1, r)) p.2]
    simp
  rw [hrw]
  intro p hp
  have hΩ : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU p.1 hp.1
  have hp2 : 0 < p.2 := hp.2
  set N : Set (E d × ℝ) := closedBall p.1 (ρ / 2) ×ˢ Icc (p.2 / 2) (p.2 + 1 + h) with hN
  have hNc : IsCompact N := (isCompact_closedBall _ _).prod isCompact_Icc
  have hNΩ : N ⊆ U ×ˢ Ioi 0 := fun q hq ↦
    ⟨hρU (closedBall_subset_ball (half_lt_self hρ) hq.1), by
      have := hq.2.1; simp only [mem_Ioi]; linarith⟩
  obtain ⟨C, hC⟩ := hNc.exists_bound_of_continuousOn (ha.mono hNΩ)
  refine ContinuousAt.continuousWithinAt ?_
  have hW : ball p.1 (ρ / 2) ×ˢ Ioo (p.2 / 2) (p.2 + 1) ∈ 𝓝 p :=
    prod_mem_nhds (ball_mem_nhds _ (half_pos hρ)) (Ioo_mem_nhds (by linarith) (by linarith))
  have hmemN : ∀ q ∈ ball p.1 (ρ / 2) ×ˢ Ioo (p.2 / 2) (p.2 + 1), ∀ τ ∈ Icc 0 h,
      (q.1, q.2 + τ) ∈ N := fun q hq τ hτ ↦
    ⟨ball_subset_closedBall hq.1, by linarith [hq.2.1, hτ.1], by linarith [hq.2.2, hτ.2]⟩
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ ↦ C) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hW] with q hq
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine (ha.mono hNΩ).comp (Continuous.continuousOn (by fun_prop)) fun τ hτ ↦ ?_
    rw [uIoc_of_le hh] at hτ
    exact hmemN q hq τ ⟨hτ.1.le, hτ.2⟩
  · filter_upwards [hW] with q hq
    refine Eventually.of_forall fun τ hτ ↦ ?_
    rw [uIoc_of_le hh] at hτ
    exact hC _ (hmemN q hq τ ⟨hτ.1.le, hτ.2⟩)
  · refine Eventually.of_forall fun τ hτ ↦ ?_
    rw [uIoc_of_le hh] at hτ
    have hmem : (p.1, p.2 + τ) ∈ U ×ˢ Ioi 0 := ⟨hp.1, by simp only [mem_Ioi]; linarith [hτ.1]⟩
    have hc : ContinuousAt (fun q : E d × ℝ ↦ (q.1, q.2 + τ)) p := by fun_prop
    exact ContinuousAt.comp (g := a) (ha.continuousAt (hΩ.mem_nhds hmem)) hc

/-- `t ↦ ∫ₜ^{t+h} f` has derivative `f(t + h) - f(t)` on `(0, ∞)` for `f` continuous there. -/
theorem hasDerivAt_integral_window {f : ℝ → F'} (hf : ContinuousOn f (Ioi 0)) {h t : ℝ}
    (hh : 0 ≤ h) (ht : 0 < t) :
    HasDerivAt (fun t ↦ ∫ r in t..t + h, f r) (f (t + h) - f t) t := by
  set c := t / 2 with hc
  have hc0 : 0 < c := half_pos ht
  have hP : ∀ s, c ≤ s → HasDerivAt (fun s ↦ ∫ r in c..s, f r) (f s) s := by
    intro s hs
    have hs0 : 0 < s := hc0.trans_le hs
    refine intervalIntegral.integral_hasDerivAt_right ?_
      (hf.stronglyMeasurableAtFilter isOpen_Ioi s hs0)
      (hf.continuousAt (isOpen_Ioi.mem_nhds hs0))
    refine (hf.mono fun r hr ↦ ?_).intervalIntegrable
    rw [uIcc_of_le hs] at hr
    exact hc0.trans_le hr.1
  have h1 := (hP (t + h) (by linarith)).comp_add_const t h
  have h2 := hP t (by linarith)
  refine (h1.sub h2).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (show c < t by linarith)] with s hs
  have hs' : c < s := hs
  change _ = (∫ r in c..s + h, f r) - ∫ r in c..s, f r
  rw [intervalIntegral.integral_interval_sub_left]
  · refine (hf.mono fun r hr ↦ ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hr
    exact hc0.trans_le hr.1
  · refine (hf.mono fun r hr ↦ ?_).intervalIntegrable
    rw [uIcc_of_le hs'.le] at hr
    exact hc0.trans_le hr.1

end Window

/-! ### Cauchy–Schwarz for interval integrals -/

/-- `(∫ₐᵇ g)² ≤ (b - a) ∫ₐᵇ g²` for `g` continuous on `[a, b]`. -/
theorem sq_integral_le {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) :
    (∫ r in a..b, g r) ^ 2 ≤ (b - a) * ∫ r in a..b, g r ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · simp [h]
  have hgi : IntervalIntegrable g volume a b := (hg.mono (uIcc_of_le hab).subset).intervalIntegrable
  have hg2 : IntervalIntegrable (fun r ↦ g r ^ 2) volume a b :=
    ((hg.pow 2).mono (uIcc_of_le hab).subset).intervalIntegrable
  set m := (∫ r in a..b, g r) / (b - a) with hm
  have hba : 0 < b - a := sub_pos.2 h
  have hnn : 0 ≤ ∫ r in a..b, (g r - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun r _ ↦ sq_nonneg _
  have hexp : ∫ r in a..b, (g r - m) ^ 2 =
      (∫ r in a..b, g r ^ 2) - 2 * m * (∫ r in a..b, g r) + m ^ 2 * (b - a) := by
    have e : (fun r ↦ (g r - m) ^ 2) = fun r ↦ (g r ^ 2 - 2 * m * g r) + m ^ 2 := by
      funext r; ring
    rw [e, intervalIntegral.integral_add (hg2.sub (hgi.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hg2 (hgi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hexp] at hnn
  have hm' : m * (b - a) = ∫ r in a..b, g r := by rw [hm]; field_simp
  nlinarith [hm']

/-- `‖∫ₐᵇ f‖² ≤ (b - a) ∫ₐᵇ ‖f‖²` for `f` continuous on `[a, b]`. -/
theorem norm_integral_sq_le {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {f : ℝ → F'} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ‖∫ r in a..b, f r‖ ^ 2 ≤ (b - a) * ∫ r in a..b, ‖f r‖ ^ 2 := by
  have h1 : ‖∫ r in a..b, f r‖ ≤ ∫ r in a..b, ‖f r‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have h2 := sq_integral_le hab hf.norm
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-! ### Truncated integration by parts for functions vanishing on `∂U` -/

/-- **Truncated integration by parts.** If `φ₀` has weak gradient `Φ₀` in `U`, is continuous on
`Ū` and vanishes on `∂U`, then for `f ∈ C²(U)` and `σ > 0`,
`∫ Δf T_σ(φ₀) = -∫ ∇f · T_σ'(φ₀) Φ₀` (both truncations extended by `0` off `U`). -/
theorem integral_laplacian_mul_trunc {U : Set (E d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : E d → ℝ} (hf : ContDiffOn ℝ 2 f U) {φ₀ : E d → ℝ}
    {Φ₀ : E d → E d} (hφ : HasWeakGradient U φ₀ Φ₀) (hφc : ContinuousOn φ₀ (closure U))
    (hφ0 : ∀ x ∈ frontier U, φ₀ x = 0) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x, Δ f x * U.indicator (fun x ↦ trunc σ (φ₀ x)) x =
      -∫ x, ⟪∇ f x, U.indicator (fun x ↦ truncDeriv σ (φ₀ x) • Φ₀ x) x⟫ := by
  set K := {x ∈ closure U | σ ≤ |φ₀ x|} with hKdef
  have hK : IsCompact K := isCompact_setOf_le_abs hUb.isCompact_closure hφc σ
  have hKU : K ⊆ U := setOf_le_abs_subset (fun x hx hxU ↦
    hφ0 x (mem_frontier_of_mem_closure hU hx hxU)) hσ
  have hlt : ∀ x ∈ U, x ∉ K → |φ₀ x| < σ := fun x hx hxK ↦
    not_le.1 fun h ↦ hxK ⟨subset_closure hx, h⟩
  have hw := (hφ.comp hU (contDiff_trunc σ) (nnnorm_deriv_trunc_le σ))
  simp only [deriv_trunc] at hw
  refine integral_laplacian_mul_eq_neg_of_hasWeakGradient hU hf ?_ hK hKU ?_ ?_
  · refine (hw.congr_fun_ae ?_).congr_ae ?_
    · exact (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun x hx ↦ by
        rw [indicator_of_mem hx])
    · exact (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun x hx ↦ by
        rw [indicator_of_mem hx])
  · intro x hx
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU, trunc_eq_zero hσ (hlt x hxU hx).le]
    · rw [indicator_of_notMem hxU]
  · intro x hx
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU, truncDeriv_eq_zero hσ (hlt x hxU hx).le, zero_smul]
    · rw [indicator_of_notMem hxU]

/-- Fubini on `K × [a, b]` for a function continuous there and vanishing for `x ∉ K`. -/
theorem integral_window_swap {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] {K : Set (E d)} (hK : IsCompact K) {a b : ℝ} (hab : a ≤ b)
    {Φ : E d → ℝ → F'} (hΦ : ContinuousOn (Function.uncurry Φ) (K ×ˢ Icc a b))
    (hΦ0 : ∀ x ∉ K, ∀ r, Φ x r = 0) :
    ∫ r in a..b, ∫ x, Φ x r = ∫ x, ∫ r in a..b, Φ x r := by
  simp_rw [intervalIntegral.integral_of_le hab]
  have hint : Integrable (Function.uncurry Φ)
      ((volume : Measure (E d)).prod (volume.restrict (Ioc a b))) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (E d))), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
    have h1 : IntegrableOn (Function.uncurry Φ) (K ×ˢ Icc a b) :=
      hΦ.integrableOn_compact (hK.prod isCompact_Icc)
    refine (h1.mono_set (prod_mono le_rfl Ioc_subset_Icc_self)).of_forall_sdiff_eq_zero
      (MeasurableSet.univ.prod measurableSet_Ioc) fun p hp ↦ ?_
    have hpK : p.1 ∉ K := fun h ↦ hp.2 ⟨h, hp.1.2⟩
    exact hΦ0 p.1 hpK p.2
  exact (integral_integral_swap hint).symm

/-! ### Steklov quantities -/

/-- The time difference `v(x, t) = u(x, t + h) - u(x, t)`. -/
noncomputable def dq (u : E d × ℝ → ℝ) (h : ℝ) (p : E d × ℝ) : ℝ := u (p.1, p.2 + h) - u p

/-- Its spatial gradient `∇v(x, t) = ∇u(x, t + h) - ∇u(x, t)`. -/
noncomputable def dqGrad (u : E d × ℝ → ℝ) (h : ℝ) (p : E d × ℝ) : E d :=
  gradₓ u (p.1, p.2 + h) - gradₓ u p

/-- The Steklov integral `V(x, t) = ∫ₜ^{t+h} ∇u(x, r) dr`. -/
noncomputable def avgGrad (u : E d × ℝ → ℝ) (h : ℝ) (p : E d × ℝ) : E d :=
  ∫ r in p.2..p.2 + h, gradₓ u (p.1, r)

/-- The Steklov integral `F(x, t) = ∫ₜ^{t+h} f(x, r) dr` of the reaction term. -/
noncomputable def avgRxn (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ) (u : E d × ℝ → ℝ) (h : ℝ)
    (p : E d × ℝ) : ℝ :=
  ∫ r in p.2..p.2 + h, reaction Q β ε u (p.1, r)

section Steklov

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ}
  {h : ℝ}

theorem continuousOn_lapₓ (hQ : ContinuousOn Q U) (hβ : Continuous β)
    (hu : IsSemilinearSolution U Q β ε g u) : ContinuousOn (lapₓ u) (U ×ˢ Ioi 0) :=
  (hu.2.1.2.2.2.2.2.1.add (continuousOn_reaction hQ hβ hu.2.1.1)).congr fun _ hp ↦
    lapₓ_eq hu hp

theorem continuousOn_dq (hu : IsSemilinearSolution U Q β ε g u) (hh : 0 ≤ h) :
    ContinuousOn (dq u h) (closure U ×ˢ Ici 0) :=
  (hu.1.comp (by fun_prop : Continuous fun p : E d × ℝ ↦ (p.1, p.2 + h)).continuousOn
    fun p hp ↦ ⟨hp.1, by have := hp.2; simp only [mem_Ici] at this ⊢; linarith⟩).sub hu.1

theorem dq_eq_zero_of_mem_frontier (hu : IsSemilinearSolution U Q β ε g u) (hh : 0 ≤ h)
    {x : E d} (hx : x ∈ frontier U) {t : ℝ} (ht : 0 ≤ t) : dq u h (x, t) = 0 := by
  simp only [dq]
  rw [hu.2.2.2 x hx (t + h) (by linarith), hu.2.2.2 x hx t ht, sub_self]

theorem continuousOn_dqGrad (hu : IsSemilinearSolution U Q β ε g u) (hh : 0 ≤ h) :
    ContinuousOn (dqGrad u h) (U ×ˢ Ioi 0) :=
  (hu.2.1.2.2.1.comp (by fun_prop : Continuous fun p : E d × ℝ ↦ (p.1, p.2 + h)).continuousOn
    fun p hp ↦ ⟨hp.1, by have := hp.2; simp only [mem_Ioi] at this ⊢; linarith⟩).sub hu.2.1.2.2.1

theorem continuousOn_avgGrad (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    (hh : 0 ≤ h) : ContinuousOn (avgGrad u h) (U ×ˢ Ioi 0) :=
  continuousOn_integral_window hU hu.2.1.2.2.1 hh

theorem continuousOn_avgRxn (hU : IsOpen U) (hQ : ContinuousOn Q U) (hβ : Continuous β)
    (hu : IsSemilinearSolution U Q β ε g u) (hh : 0 ≤ h) :
    ContinuousOn (avgRxn Q β ε u h) (U ×ˢ Ioi 0) :=
  continuousOn_integral_window hU (continuousOn_reaction hQ hβ hu.2.1.1) hh

theorem hasWeakGradient_dq (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    (hh : 0 ≤ h) {t : ℝ} (ht : 0 < t) :
    HasWeakGradient U (fun x ↦ dq u h (x, t)) (fun x ↦ dqGrad u h (x, t)) :=
  (hasWeakGradient_slice hU hu (by linarith : 0 < t + h)).sub (hasWeakGradient_slice hU hu ht)

theorem continuousOn_slice_Ioi {F' : Type*} [TopologicalSpace F'] {a : E d × ℝ → F'}
    (ha : ContinuousOn a (U ×ˢ Ioi 0)) {x : E d} (hx : x ∈ U) :
    ContinuousOn (fun r ↦ a (x, r)) (Ioi 0) :=
  ha.comp (by fun_prop : Continuous fun r : ℝ ↦ (x, r)).continuousOn fun _ hr ↦ ⟨hx, hr⟩

theorem uIcc_subset_Ioi {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) : uIcc t (t + h) ⊆ Ioi 0 := by
  intro r hr
  rw [uIcc_of_le (by linarith)] at hr
  exact ht.trans_le hr.1

/-- `∫ₜ^{t+h} Δu(x, r) dr = v(x, t) + F(x, t)`. -/
theorem integral_lapₓ_window (hQ : ContinuousOn Q U) (hβ : Continuous β)
    (hu : IsSemilinearSolution U Q β ε g u) (hh : 0 ≤ h) {x : E d} (hx : x ∈ U) {t : ℝ}
    (ht : 0 < t) :
    ∫ r in t..t + h, lapₓ u (x, r) = dq u h (x, t) + avgRxn Q β ε u h (x, t) := by
  have hsub := uIcc_subset_Ioi ht hh
  have hdt := continuousOn_slice_Ioi hu.2.1.2.2.2.2.2.1 hx
  have hf := continuousOn_slice_Ioi (continuousOn_reaction (ε := ε) hQ hβ hu.2.1.1) hx
  rw [intervalIntegral.integral_congr (g := fun r ↦ dₜ u (x, r) + reaction Q β ε u (x, r))
    fun r hr ↦ lapₓ_eq hu (p := (x, r)) ⟨hx, hsub hr⟩,
    intervalIntegral.integral_add ((hdt.mono hsub).intervalIntegrable)
      ((hf.mono hsub).intervalIntegrable)]
  congr 1
  have hd : ∀ r ∈ uIcc t (t + h), HasDerivAt (fun r ↦ u (x, r)) (dₜ u (x, r)) r :=
    fun r hr ↦ (hu.2.1.2.2.2.2.1 (x, r) ⟨hx, hsub hr⟩).hasDerivAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((hdt.mono hsub).intervalIntegrable)]
  rfl

/-- `∂ₜV = ∇v`. -/
theorem hasDerivAt_avgGrad (hu : IsSemilinearSolution U Q β ε g u) (hh : 0 ≤ h) {x : E d}
    (hx : x ∈ U) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ avgGrad u h (x, t)) (dqGrad u h (x, t)) t :=
  hasDerivAt_integral_window (continuousOn_slice_Ioi hu.2.1.2.2.1 hx) hh ht

/-- **(B1) The Steklov slice identity.** For `t > 0` and `σ > 0`,
`∫_U (v + F) T_σ(v) = -∫_U V · T_σ'(v) ∇v` (at time `t`). -/
theorem integral_steklov_slice (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    (hh : 0 ≤ h) {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    ∫ x, (dq u h (x, t) + avgRxn Q β ε u h (x, t)) *
        U.indicator (fun x ↦ trunc σ (dq u h (x, t))) x =
      -∫ x, ⟪avgGrad u h (x, t),
        U.indicator (fun x ↦ truncDeriv σ (dq u h (x, t)) • dqGrad u h (x, t)) x⟫ := by
  set ψ := U.indicator (fun x ↦ trunc σ (dq u h (x, t))) with hψ
  set Ψ := U.indicator (fun x ↦ truncDeriv σ (dq u h (x, t)) • dqGrad u h (x, t)) with hΨ
  set K := {x ∈ closure U | σ ≤ |dq u h (x, t)|} with hKdef
  have hsub := uIcc_subset_Ioi ht hh
  have hth : t ≤ t + h := by linarith
  have hφc : ContinuousOn (fun x ↦ dq u h (x, t)) (closure U) :=
    (continuousOn_dq hu hh).comp (by fun_prop : Continuous fun x : E d ↦ (x, t)).continuousOn
      fun x hx ↦ ⟨hx, mem_Ici.2 ht.le⟩
  have hK : IsCompact K := isCompact_setOf_le_abs hUb.isCompact_closure hφc σ
  have hKU : K ⊆ U := setOf_le_abs_subset (fun x hx hxU ↦
    dq_eq_zero_of_mem_frontier hu hh (mem_frontier_of_mem_closure hU hx hxU) ht.le) hσ
  have hlt : ∀ x ∈ U, x ∉ K → |dq u h (x, t)| < σ := fun x hx hxK ↦
    not_le.1 fun h ↦ hxK ⟨subset_closure hx, h⟩
  have hψ0 : ∀ x ∉ K, ψ x = 0 := by
    intro x hx
    by_cases hxU : x ∈ U
    · rw [hψ, indicator_of_mem hxU, trunc_eq_zero hσ (hlt x hxU hx).le]
    · rw [hψ, indicator_of_notMem hxU]
  have hΨ0 : ∀ x ∉ K, Ψ x = 0 := by
    intro x hx
    by_cases hxU : x ∈ U
    · rw [hΨ, indicator_of_mem hxU, truncDeriv_eq_zero hσ (hlt x hxU hx).le, zero_smul]
    · rw [hΨ, indicator_of_notMem hxU]
  have hKprod : K ×ˢ Icc t (t + h) ⊆ U ×ˢ Ioi 0 := fun p hp ↦
    ⟨hKU hp.1, hsub (by rw [uIcc_of_le hth]; exact hp.2)⟩
  have hψc : ContinuousOn ψ K := by
    refine ContinuousOn.congr ?_ fun x hx ↦ indicator_of_mem (hKU hx) _
    exact (continuous_trunc σ).comp_continuousOn (hφc.mono fun x hx ↦ subset_closure (hKU hx))
  have hΨc : ContinuousOn Ψ K := by
    refine ContinuousOn.congr ?_ fun x hx ↦ indicator_of_mem (hKU hx) _
    have h1 : ContinuousOn (fun x ↦ dqGrad u h (x, t)) K :=
      (continuousOn_dqGrad hu hh).comp (by fun_prop : Continuous fun x : E d ↦ (x, t)).continuousOn
        fun x hx ↦ ⟨hKU hx, ht⟩
    exact ((continuous_truncDeriv σ).comp_continuousOn
      (hφc.mono fun x hx ↦ subset_closure (hKU hx))).smul h1
  have hibp : ∀ r ∈ uIcc t (t + h),
      ∫ x, lapₓ u (x, r) * ψ x = -∫ x, ⟪gradₓ u (x, r), Ψ x⟫ := fun r hr ↦
    integral_laplacian_mul_trunc hU hUb (hu.2.1.2.1 r (hsub hr)) (hasWeakGradient_dq hU hu hh ht)
      hφc (fun x hx ↦ dq_eq_zero_of_mem_frontier hu hh hx ht.le) hσ
  have hL : ∫ r in t..t + h, ∫ x, lapₓ u (x, r) * ψ x =
      ∫ x, (dq u h (x, t) + avgRxn Q β ε u h (x, t)) * ψ x := by
    rw [integral_window_swap hK hth]
    · congr 1; funext x
      by_cases hx : x ∈ U
      · rw [intervalIntegral.integral_mul_const, integral_lapₓ_window hQ hβ hu hh hx ht]
      · simp [hψ, indicator_of_notMem hx]
    · exact ((continuousOn_lapₓ hQ hβ hu).mono hKprod).mul
        (hψc.comp continuousOn_fst fun p hp ↦ hp.1)
    · intro x hx r; simp [hψ0 x hx]
  have hR : ∫ r in t..t + h, ∫ x, ⟪gradₓ u (x, r), Ψ x⟫ = ∫ x, ⟪avgGrad u h (x, t), Ψ x⟫ := by
    rw [integral_window_swap hK hth]
    · congr 1; funext x
      by_cases hx : x ∈ U
      · have hi : IntervalIntegrable (fun r ↦ gradₓ u (x, r)) volume t (t + h) :=
          ((continuousOn_slice_Ioi hu.2.1.2.2.1 hx).mono hsub).intervalIntegrable
        simp_rw [real_inner_comm (Ψ x), avgGrad]
        exact (innerSL ℝ (Ψ x)).intervalIntegral_comp_comm hi
      · simp [hΨ, indicator_of_notMem hx]
    · exact (hu.2.1.2.2.1.mono hKprod).inner (hΨc.comp continuousOn_fst fun p hp ↦ hp.1)
    · intro x hx r; simp [hΨ0 x hx]
  rw [← hL, ← hR, ← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr hibp

theorem abs_avgRxn_le {M : ℝ} (hM : ∀ p ∈ U ×ˢ Ioi 0, |reaction Q β ε u p| ≤ M) (hh : 0 ≤ h)
    {x : E d} (hx : x ∈ U) {t : ℝ} (ht : 0 < t) : |avgRxn Q β ε u h (x, t)| ≤ M * h := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := t + h) (C := M)
    (f := fun r ↦ reaction Q β ε u (x, r)) fun r hr ↦ by
      rw [uIoc_of_le (by linarith)] at hr
      exact hM (x, r) ⟨hx, ht.trans hr.1⟩
  simpa [avgRxn, abs_of_nonneg hh] using this

/-- **(B2)**: the limit `σ → 0` in the Steklov slice identity, at a time `t` where
`V · ∇v ∈ L¹(U)`: `∫_U (v + F) v = -∫_U V · ∇v`. -/
theorem integral_steklov_slice_lim (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    (hh : 0 ≤ h) {M : ℝ} (hM : ∀ p ∈ U ×ˢ Ioi 0, |reaction Q β ε u p| ≤ M) {t : ℝ}
    (ht : 0 < t) (hI : IntegrableOn (fun x ↦ ⟪avgGrad u h (x, t), dqGrad u h (x, t)⟫) U) :
    ∫ x in U, (dq u h (x, t) + avgRxn Q β ε u h (x, t)) * dq u h (x, t) =
      -∫ x in U, ⟪avgGrad u h (x, t), dqGrad u h (x, t)⟫ := by
  have hemb : Continuous fun x : E d ↦ (x, t) := by fun_prop
  have hφc : ContinuousOn (fun x ↦ dq u h (x, t)) (closure U) :=
    (continuousOn_dq hu hh).comp hemb.continuousOn fun x hx ↦ ⟨hx, mem_Ici.2 ht.le⟩
  have hFc : ContinuousOn (fun x ↦ avgRxn Q β ε u h (x, t)) U :=
    (continuousOn_avgRxn hU hQ hβ hu hh).comp hemb.continuousOn fun x hx ↦ ⟨hx, ht⟩
  obtain ⟨C₁, hC₁⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn hφc
  have hfin : volume U < ⊤ := hUb.measure_lt_top
  -- rewrite both sides of (B1) as set integrals over `U`
  have hB1 : ∀ n, ∫ x in U, (dq u h (x, t) + avgRxn Q β ε u h (x, t)) *
      trunc (lev n) (dq u h (x, t)) =
        -∫ x in U, truncDeriv (lev n) (dq u h (x, t)) *
          ⟪avgGrad u h (x, t), dqGrad u h (x, t)⟫ := by
    intro n
    have hs := integral_steklov_slice hU hUb hQ hβ hu hh (lev_pos n) ht
    have e1 : (fun x ↦ (dq u h (x, t) + avgRxn Q β ε u h (x, t)) *
        U.indicator (fun x ↦ trunc (lev n) (dq u h (x, t))) x) = U.indicator (fun x ↦
          (dq u h (x, t) + avgRxn Q β ε u h (x, t)) * trunc (lev n) (dq u h (x, t))) := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    have e2 : (fun x ↦ ⟪avgGrad u h (x, t), U.indicator (fun x ↦
        truncDeriv (lev n) (dq u h (x, t)) • dqGrad u h (x, t)) x⟫) = U.indicator (fun x ↦
          truncDeriv (lev n) (dq u h (x, t)) * ⟪avgGrad u h (x, t), dqGrad u h (x, t)⟫) := by
      funext x; by_cases hx : x ∈ U <;> simp [hx, real_inner_smul_right]
    rw [e1, e2, integral_indicator hU.measurableSet, integral_indicator hU.measurableSet] at hs
    exact hs
  have hmeas1 : AEStronglyMeasurable (fun x ↦ (dq u h (x, t) + avgRxn Q β ε u h (x, t)) *
      dq u h (x, t)) (volume.restrict U) :=
    (((hφc.mono subset_closure).add hFc).mul (hφc.mono subset_closure)).aestronglyMeasurable
      hU.measurableSet
  have hbd : ∀ x ∈ U, |(dq u h (x, t) + avgRxn Q β ε u h (x, t))| * |dq u h (x, t)| ≤
      (C₁ + M * h) * C₁ := by
    intro x hx
    have h1 : |dq u h (x, t)| ≤ C₁ := by simpa using hC₁ x (subset_closure hx)
    have h2 := abs_avgRxn_le hM hh hx ht
    exact mul_le_mul ((abs_add_le _ _).trans (add_le_add h1 h2)) h1 (abs_nonneg _)
      ((abs_nonneg _).trans (h1.trans (le_add_of_nonneg_right
        ((abs_nonneg _).trans h2))))
  have hL : Tendsto (fun n ↦ ∫ x in U, (dq u h (x, t) + avgRxn Q β ε u h (x, t)) *
      trunc (lev n) (dq u h (x, t))) atTop
        (𝓝 (∫ x in U, (dq u h (x, t) + avgRxn Q β ε u h (x, t)) * dq u h (x, t))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (C₁ + M * h) * C₁) (fun n ↦ ?_)
      (integrableOn_const hfin.ne) (fun n ↦ ?_) ?_
    · exact (((hφc.mono subset_closure).add hFc).mul ((continuous_trunc _).comp_continuousOn
        (hφc.mono subset_closure))).aestronglyMeasurable hU.measurableSet
    · refine (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul]
      refine le_trans ?_ (hbd x hx)
      exact mul_le_mul_of_nonneg_left (abs_trunc_le _ _) (abs_nonneg _)
    · exact Eventually.of_forall fun x ↦ tendsto_const_nhds.mul
        ((tendsto_trunc (dq u h (x, t))).comp tendsto_lev)
  have hae := HasWeakGradient.ae_eq_zero_of_eq_zero hU (hasWeakGradient_dq hU hu hh ht)
  have hR : Tendsto (fun n ↦ ∫ x in U, truncDeriv (lev n) (dq u h (x, t)) *
      ⟪avgGrad u h (x, t), dqGrad u h (x, t)⟫) atTop
        (𝓝 (∫ x in U, ⟪avgGrad u h (x, t), dqGrad u h (x, t)⟫)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖⟪avgGrad u h (x, t), dqGrad u h (x, t)⟫‖) (fun n ↦ ?_) hI.norm (fun n ↦ ?_) ?_
    · have hVc : ContinuousOn (fun x ↦ avgGrad u h (x, t)) U :=
        (continuousOn_avgGrad hU hu hh).comp hemb.continuousOn fun x hx ↦ ⟨hx, ht⟩
      have hGc : ContinuousOn (fun x ↦ dqGrad u h (x, t)) U :=
        (continuousOn_dqGrad hu hh).comp hemb.continuousOn fun x hx ↦ ⟨hx, ht⟩
      exact (((continuous_truncDeriv _).comp_continuousOn (hφc.mono subset_closure)).mul
        (hVc.inner hGc)).aestronglyMeasurable hU.measurableSet
    · refine Eventually.of_forall fun x ↦ ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (truncDeriv_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (truncDeriv_le_one _ _)
    · filter_upwards [hae] with x hx
      by_cases h0 : dq u h (x, t) = 0
      · rw [hx h0, inner_zero_right]
        simp
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [tendsto_lev.eventually (eventually_truncDeriv_eq_one h0)] with n hn
        rw [hn, one_mul]
  have := hR.neg
  simp_rw [← hB1] at this
  exact tendsto_nhds_unique hL this

/-- **(B3)** `∫_{t₀}^T V · ∇v = ½|V(T)|² - ½|V(t₀)|²` at a fixed `x ∈ U`. -/
theorem integral_inner_avgGrad (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    (hh : 0 ≤ h) {x : E d} (hx : x ∈ U) {t₀ T : ℝ} (ht₀ : 0 < t₀) (hT : t₀ ≤ T) :
    ∫ t in Ioc t₀ T, ⟪avgGrad u h (x, t), dqGrad u h (x, t)⟫ =
      ‖avgGrad u h (x, T)‖ ^ 2 / 2 - ‖avgGrad u h (x, t₀)‖ ^ 2 / 2 := by
  have hsub : uIcc t₀ T ⊆ Ioi 0 := fun r hr ↦ by
    rw [uIcc_of_le hT] at hr; exact ht₀.trans_le hr.1
  have hVc := continuousOn_slice_Ioi (continuousOn_avgGrad hU hu hh) hx
  have hGc := continuousOn_slice_Ioi (continuousOn_dqGrad hu hh) hx
  have hd : ∀ t ∈ uIcc t₀ T, HasDerivAt (fun t ↦ ‖avgGrad u h (x, t)‖ ^ 2 / 2)
      ⟪avgGrad u h (x, t), dqGrad u h (x, t)⟫ t := by
    intro t ht
    have := ((hasDerivAt_avgGrad hu hh hx (hsub ht)).norm_sq).div_const 2
    convert this using 1
    ring
  rw [← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (((hVc.inner hGc).mono hsub).intervalIntegrable)]

theorem restrict_prod_eq (U : Set (E d)) (I : Set ℝ) :
    (volume : Measure (E d × ℝ)).restrict (U ×ˢ I) =
      (volume.restrict U).prod (volume.restrict I) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

/-- Pointwise Cauchy–Schwarz for the Steklov integral:
`|V(x, t)|² ≤ h ∫_{(0, S]} |∇u(x, r)|² dr` whenever `(t, t + h] ⊆ (0, S]`. -/
theorem ofReal_norm_avgGrad_sq_le (hu : IsSemilinearSolution U Q β ε g u) (hh : 0 ≤ h)
    {x : E d} (hx : x ∈ U) {t S : ℝ} (ht : 0 < t) (hS : t + h ≤ S) :
    ENNReal.ofReal (‖avgGrad u h (x, t)‖ ^ 2) ≤
      ENNReal.ofReal h * ∫⁻ r in Ioc 0 S, ENNReal.ofReal (‖gradₓ u (x, r)‖ ^ 2) := by
  have hsub := uIcc_subset_Ioi ht hh
  have hth : t ≤ t + h := by linarith
  have hc := continuousOn_slice_Ioi hu.2.1.2.2.1 hx
  have hIcc : Icc t (t + h) ⊆ Ioi 0 := by rw [← uIcc_of_le hth]; exact hsub
  have h1 := norm_integral_sq_le hth (hc.mono hIcc)
  simp only [add_sub_cancel_left] at h1
  have hint : IntegrableOn (fun r ↦ ‖gradₓ u (x, r)‖ ^ 2) (Ioc t (t + h)) :=
    (((hc.norm.pow 2).mono hIcc).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  calc ENNReal.ofReal (‖avgGrad u h (x, t)‖ ^ 2)
      ≤ ENNReal.ofReal (h * ∫ r in t..t + h, ‖gradₓ u (x, r)‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal h * ∫⁻ r in Ioc t (t + h), ENNReal.ofReal (‖gradₓ u (x, r)‖ ^ 2) := by
        rw [ENNReal.ofReal_mul hh, intervalIntegral.integral_of_le hth,
          ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun r ↦ sq_nonneg _)]
    _ ≤ _ := by
        have hIoc : Ioc t (t + h) ⊆ Ioc 0 S := fun r hr ↦ ⟨ht.trans hr.1, hr.2.trans hS⟩
        exact mul_le_mul_right (lintegral_mono_set hIoc) _

/-- `∫⁻_U ∫⁻_{(0, S]} = ∫⁻_{U × (0, S]}` for `|∇u|²`. -/
theorem lintegral_iterated_eq (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    {a b : ℝ} (ha : 0 ≤ a) :
    ∫⁻ x in U, ∫⁻ r in Ioc a b, ENNReal.ofReal (‖gradₓ u (x, r)‖ ^ 2) =
      ∫⁻ p in U ×ˢ Ioc a b, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) := by
  rw [restrict_prod_eq, lintegral_prod]
  rw [← restrict_prod_eq]
  refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
  refine ((hu.2.1.2.2.1.norm.pow 2).mono ?_).aemeasurable
    (hU.measurableSet.prod measurableSet_Ioc)
  exact fun p hp ↦ ⟨hp.1, ha.trans_lt hp.2.1⟩

/-- `|V(·, t)|² ∈ L¹(U)` when `∇u ∈ L²(U × (0, S])` and `(t, t + h] ⊆ (0, S]`. -/
theorem integrableOn_norm_avgGrad_sq (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    (hh : 0 ≤ h) {t S : ℝ} (ht : 0 < t) (hS : t + h ≤ S)
    (hA : ∫⁻ p in U ×ˢ Ioc 0 S, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) < ⊤) :
    IntegrableOn (fun x ↦ ‖avgGrad u h (x, t)‖ ^ 2) U := by
  have hc : ContinuousOn (fun x ↦ avgGrad u h (x, t)) U :=
    (continuousOn_avgGrad hU hu hh).comp
      (by fun_prop : Continuous fun x : E d ↦ (x, t)).continuousOn fun x hx ↦ ⟨hx, ht⟩
  refine ⟨((hc.norm.pow 2).aestronglyMeasurable hU.measurableSet), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x ↦ sq_nonneg _)]
  calc ∫⁻ x in U, ENNReal.ofReal (‖avgGrad u h (x, t)‖ ^ 2)
      ≤ ∫⁻ x in U, ENNReal.ofReal h *
          ∫⁻ r in Ioc 0 S, ENNReal.ofReal (‖gradₓ u (x, r)‖ ^ 2) :=
        setLIntegral_mono' hU.measurableSet fun x hx ↦ ofReal_norm_avgGrad_sq_le hu hh hx ht hS
    _ = ENNReal.ofReal h * ∫⁻ p in U ×ˢ Ioc 0 S, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_iterated_eq hU hu le_rfl]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA

/-- Time translation of a set lintegral over `U × (a, b]`. -/
theorem setLIntegral_time_shift (φ : E d × ℝ → ℝ≥0∞) (U : Set (E d)) (hUm : MeasurableSet U)
    (a b h : ℝ) :
    ∫⁻ p in U ×ˢ Ioc a b, φ (p.1, p.2 + h) = ∫⁻ p in U ×ˢ Ioc (a + h) (b + h), φ p := by
  have hm1 : MeasurableSet (U ×ˢ Ioc a b) := hUm.prod measurableSet_Ioc
  have hm2 : MeasurableSet (U ×ˢ Ioc (a + h) (b + h)) := hUm.prod measurableSet_Ioc
  rw [← lintegral_indicator hm1, ← lintegral_indicator hm2, Measure.volume_eq_prod]
  conv_rhs => rw [← lintegral_add_right_eq_self _ ((0, h) : E d × ℝ)]
  congr 1; funext p
  have hmem : p + ((0, h) : E d × ℝ) ∈ U ×ˢ Ioc (a + h) (b + h) ↔ p ∈ U ×ˢ Ioc a b := by
    simp only [Prod.fst_add, Prod.snd_add, add_zero, mem_prod, mem_Ioc]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by linarith, by linarith⟩
  have hp : p + ((0, h) : E d × ℝ) = (p.1, p.2 + h) := by ext <;> simp
  by_cases h' : p ∈ U ×ˢ Ioc a b
  · rw [indicator_of_mem h', indicator_of_mem (hmem.2 h'), hp]
  · rw [indicator_of_notMem h', indicator_of_notMem (fun h'' ↦ h' (hmem.1 h''))]

/-- **(B4)** `V · ∇v ∈ L¹(U × (t₀, T])` when `∇u ∈ L²(U × (0, T + h])`. -/
theorem integrableOn_inner_avgGrad (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    (hh : 0 ≤ h) {t₀ T : ℝ} (ht₀ : 0 < t₀)
    (hA : ∫⁻ p in U ×ˢ Ioc 0 (T + h), ENNReal.ofReal (‖gradₓ u p‖ ^ 2) < ⊤) :
    IntegrableOn (fun p ↦ ⟪avgGrad u h p, dqGrad u h p⟫) (U ×ˢ Ioc t₀ T) := by
  set Ω := U ×ˢ Ioc t₀ T with hΩdef
  have hΩm : MeasurableSet Ω := hU.measurableSet.prod measurableSet_Ioc
  have hΩ : Ω ⊆ U ×ˢ Ioi 0 := fun p hp ↦ ⟨hp.1, ht₀.trans hp.2.1⟩
  have hVc := (continuousOn_avgGrad hU hu hh).mono hΩ
  have hGc := (continuousOn_dqGrad hu hh).mono hΩ
  have hgc := hu.2.1.2.2.1.mono hΩ
  have hg2c : ContinuousOn (fun p : E d × ℝ ↦ gradₓ u (p.1, p.2 + h)) Ω :=
    hu.2.1.2.2.1.comp (by fun_prop : Continuous fun p : E d × ℝ ↦ (p.1, p.2 + h)).continuousOn
      fun p hp ↦ ⟨hp.1, by have := ht₀.trans (hp.2.1); simp only [mem_Ioi]; linarith⟩
  refine ⟨(hVc.inner hGc).aestronglyMeasurable hΩm, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hpt : ∀ p, ENNReal.ofReal ‖⟪avgGrad u h p, dqGrad u h p⟫‖ ≤
      ENNReal.ofReal (‖avgGrad u h p‖ ^ 2) + 2 * ENNReal.ofReal (‖gradₓ u (p.1, p.2 + h)‖ ^ 2) +
        2 * ENNReal.ofReal (‖gradₓ u p‖ ^ 2) := by
    intro p
    have h1 : ‖⟪avgGrad u h p, dqGrad u h p⟫‖ ≤ ‖avgGrad u h p‖ ^ 2 +
        (2 * ‖gradₓ u (p.1, p.2 + h)‖ ^ 2 + 2 * ‖gradₓ u p‖ ^ 2) := by
      have e1 : ‖⟪avgGrad u h p, dqGrad u h p⟫‖ ≤ ‖avgGrad u h p‖ * ‖dqGrad u h p‖ :=
        norm_inner_le_norm _ _
      have e2 : ‖dqGrad u h p‖ ≤ ‖gradₓ u (p.1, p.2 + h)‖ + ‖gradₓ u p‖ := norm_sub_le _ _
      have e3 : ‖dqGrad u h p‖ ^ 2 ≤ (‖gradₓ u (p.1, p.2 + h)‖ + ‖gradₓ u p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) e2 2
      nlinarith [sq_nonneg (‖avgGrad u h p‖ - ‖dqGrad u h p‖),
        sq_nonneg (‖gradₓ u (p.1, p.2 + h)‖ - ‖gradₓ u p‖)]
    calc ENNReal.ofReal ‖⟪avgGrad u h p, dqGrad u h p⟫‖
        ≤ ENNReal.ofReal (‖avgGrad u h p‖ ^ 2 +
            (2 * ‖gradₓ u (p.1, p.2 + h)‖ ^ 2 + 2 * ‖gradₓ u p‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), add_assoc]
          norm_num
  have hm1 : AEMeasurable (fun p ↦ ENNReal.ofReal (‖avgGrad u h p‖ ^ 2)) (volume.restrict Ω) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hVc.norm.pow 2).aemeasurable hΩm)
  have hm2 : AEMeasurable (fun p : E d × ℝ ↦ 2 * ENNReal.ofReal (‖gradₓ u (p.1, p.2 + h)‖ ^ 2))
      (volume.restrict Ω) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable ((hg2c.norm.pow 2).aemeasurable hΩm)).const_mul _
  have hT1 : ∫⁻ p in Ω, ENNReal.ofReal (‖avgGrad u h p‖ ^ 2) < ⊤ := by
    calc ∫⁻ p in Ω, ENNReal.ofReal (‖avgGrad u h p‖ ^ 2)
        ≤ ∫⁻ p in Ω, ENNReal.ofReal h *
            ∫⁻ r in Ioc 0 (T + h), ENNReal.ofReal (‖gradₓ u (p.1, r)‖ ^ 2) :=
          setLIntegral_mono' hΩm fun p hp ↦ ofReal_norm_avgGrad_sq_le hu hh hp.1
            (ht₀.trans hp.2.1) (by linarith [hp.2.2])
      _ ≤ ∫⁻ x in U, ∫⁻ t in Ioc t₀ T, ENNReal.ofReal h *
            ∫⁻ r in Ioc 0 (T + h), ENNReal.ofReal (‖gradₓ u (x, r)‖ ^ 2) := by
          rw [hΩdef, restrict_prod_eq]; exact lintegral_prod_le _
      _ = ∫⁻ x in U, ENNReal.ofReal h * volume (Ioc t₀ T) *
            ∫⁻ r in Ioc 0 (T + h), ENNReal.ofReal (‖gradₓ u (x, r)‖ ^ 2) := by
          congr 1; funext x; rw [setLIntegral_const]; ring
      _ = ENNReal.ofReal h * volume (Ioc t₀ T) *
            ∫⁻ p in U ×ˢ Ioc 0 (T + h), ENNReal.ofReal (‖gradₓ u p‖ ^ 2) := by
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (by simp [Real.volume_Ioc])), lintegral_iterated_eq hU hu le_rfl]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (by simp [Real.volume_Ioc])) hA
  have hsubS : Ω ⊆ U ×ˢ Ioc 0 (T + h) := fun p hp ↦
    ⟨hp.1, ht₀.trans hp.2.1, by linarith [hp.2.2]⟩
  have hT2 : ∫⁻ p in Ω, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) < ⊤ :=
    (lintegral_mono_set hsubS).trans_lt hA
  have hT3 : ∫⁻ p in Ω, ENNReal.ofReal (‖gradₓ u (p.1, p.2 + h)‖ ^ 2) < ⊤ := by
    rw [hΩdef, setLIntegral_time_shift (fun p ↦ ENNReal.ofReal (‖gradₓ u p‖ ^ 2)) U
      hU.measurableSet]
    refine (lintegral_mono_set fun p hp ↦ ?_).trans_lt hA
    exact ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩
  calc ∫⁻ p in Ω, ENNReal.ofReal ‖⟪avgGrad u h p, dqGrad u h p⟫‖
      ≤ ∫⁻ p in Ω, (ENNReal.ofReal (‖avgGrad u h p‖ ^ 2) +
          2 * ENNReal.ofReal (‖gradₓ u (p.1, p.2 + h)‖ ^ 2) +
            2 * ENNReal.ofReal (‖gradₓ u p‖ ^ 2)) := lintegral_mono hpt
    _ = (∫⁻ p in Ω, ENNReal.ofReal (‖avgGrad u h p‖ ^ 2)) +
          2 * (∫⁻ p in Ω, ENNReal.ofReal (‖gradₓ u (p.1, p.2 + h)‖ ^ 2)) +
            2 * ∫⁻ p in Ω, ENNReal.ofReal (‖gradₓ u p‖ ^ 2) := by
        rw [lintegral_add_left' (f := fun p ↦ ENNReal.ofReal (‖avgGrad u h p‖ ^ 2) +
            2 * ENNReal.ofReal (‖gradₓ u (p.1, p.2 + h)‖ ^ 2)) (hm1.add hm2),
          lintegral_add_left' hm1,
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hT1, ?_⟩, ?_⟩
        · exact ENNReal.mul_lt_top (by norm_num) hT3
        · exact ENNReal.mul_lt_top (by norm_num) hT2

/-- A bounded function, continuous on a bounded measurable set, is integrable there. -/
theorem integrableOn_of_continuousOn_of_bdd {Ω : Set (E d × ℝ)} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) {f : E d × ℝ → ℝ} (hf : ContinuousOn f Ω) {C : ℝ}
    (hC : ∀ p ∈ Ω, |f p| ≤ C) : IntegrableOn f Ω :=
  ⟨hf.aestronglyMeasurable hΩm, .restrict_of_bounded (C := C) hΩb.measure_lt_top
    ((ae_restrict_iff' hΩm).2 (Eventually.of_forall fun p hp ↦ by
      rw [Real.norm_eq_abs]; exact hC p hp))⟩

/-- **Step B: the Steklov-averaged energy identity.** For `h ≥ 0`, `0 < t₀ ≤ T` and
`∇u ∈ L²(U × (0, T + h])`,
`½ ∫_U |V(T)|² + ∫_{t₀}^T ∫_U v² = ½ ∫_U |V(t₀)|² - ∫_{t₀}^T ∫_U v F`. -/
theorem steklov_identity (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    (hh : 0 ≤ h) {M : ℝ} (hM : ∀ p ∈ U ×ˢ Ioi 0, |reaction Q β ε u p| ≤ M) {t₀ T : ℝ}
    (ht₀ : 0 < t₀) (hT : t₀ ≤ T)
    (hA : ∫⁻ p in U ×ˢ Ioc 0 (T + h), ENNReal.ofReal (‖gradₓ u p‖ ^ 2) < ⊤) :
    (∫ x in U, ‖avgGrad u h (x, T)‖ ^ 2) / 2 + ∫ p in U ×ˢ Ioc t₀ T, dq u h p ^ 2 =
      (∫ x in U, ‖avgGrad u h (x, t₀)‖ ^ 2) / 2 -
        ∫ p in U ×ˢ Ioc t₀ T, dq u h p * avgRxn Q β ε u h p := by
  set Ω := U ×ˢ Ioc t₀ T with hΩdef
  have hΩm : MeasurableSet Ω := hU.measurableSet.prod measurableSet_Ioc
  have hΩb : Bornology.IsBounded Ω := hUb.prod (Metric.isBounded_Ioc t₀ T)
  have hΩ : Ω ⊆ U ×ˢ Ioi 0 := fun p hp ↦ ⟨hp.1, ht₀.trans hp.2.1⟩
  have hI := integrableOn_inner_avgGrad hU hu hh ht₀ hA
  -- bounds for `v` and `F`
  obtain ⟨C₁, hC₁⟩ := (hUb.isCompact_closure.prod (isCompact_Icc (a := (0 : ℝ)) (b := T))
    ).exists_bound_of_continuousOn ((continuousOn_dq hu hh).mono
      (prod_mono le_rfl Icc_subset_Ici_self))
  have hv : ∀ p ∈ Ω, |dq u h p| ≤ C₁ := fun p hp ↦ by
    simpa using hC₁ p ⟨subset_closure hp.1, (ht₀.trans hp.2.1).le, hp.2.2⟩
  have hF : ∀ p ∈ Ω, |avgRxn Q β ε u h p| ≤ M * h := fun p hp ↦
    abs_avgRxn_le hM hh hp.1 (ht₀.trans hp.2.1)
  have hdqc : ContinuousOn (dq u h) Ω :=
    (continuousOn_dq hu hh).mono fun p hp ↦ ⟨subset_closure hp.1, (ht₀.trans hp.2.1).le⟩
  have hFc : ContinuousOn (avgRxn Q β ε u h) Ω := (continuousOn_avgRxn hU hQ hβ hu hh).mono hΩ
  have hi1 : IntegrableOn (fun p ↦ dq u h p ^ 2) Ω :=
    integrableOn_of_continuousOn_of_bdd hΩm hΩb (hdqc.pow 2) (C := C₁ ^ 2) fun p hp ↦ by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hv p hp) 2
  have hi2 : IntegrableOn (fun p ↦ dq u h p * avgRxn Q β ε u h p) Ω :=
    integrableOn_of_continuousOn_of_bdd hΩm hΩb (hdqc.mul hFc) (C := C₁ * (M * h))
      fun p hp ↦ by
        rw [abs_mul]
        exact mul_le_mul (hv p hp) (hF p hp) (abs_nonneg _) ((abs_nonneg _).trans (hv p hp))
  have hi3 : IntegrableOn (fun p ↦ (dq u h p + avgRxn Q β ε u h p) * dq u h p) Ω := by
    refine (hi1.add hi2).congr_fun (fun p _ ↦ ?_) hΩm
    simp only [Pi.add_apply]; ring
  -- Fubini, first order: `x` outside
  have hI' : Integrable (fun p ↦ ⟪avgGrad u h p, dqGrad u h p⟫)
      ((volume.restrict U).prod (volume.restrict (Ioc t₀ T))) := by
    rw [← restrict_prod_eq]; exact hI
  have e1 : ∫ p in Ω, ⟪avgGrad u h p, dqGrad u h p⟫ =
      (∫ x in U, ‖avgGrad u h (x, T)‖ ^ 2) / 2 - (∫ x in U, ‖avgGrad u h (x, t₀)‖ ^ 2) / 2 := by
    rw [hΩdef, restrict_prod_eq, integral_prod _ hI',
      setIntegral_congr_fun hU.measurableSet fun x hx ↦
        integral_inner_avgGrad hU hu hh hx ht₀ hT,
      integral_sub ((integrableOn_norm_avgGrad_sq hU hu hh (ht₀.trans_le hT) le_rfl hA).div_const 2)
        ((integrableOn_norm_avgGrad_sq hU hu hh ht₀ (by linarith) hA).div_const 2),
      integral_div, integral_div]
  -- Fubini, second order: `t` outside, and (B2) for a.e. `t`
  have hi3' : Integrable (fun p ↦ (dq u h p + avgRxn Q β ε u h p) * dq u h p)
      ((volume.restrict U).prod (volume.restrict (Ioc t₀ T))) := by
    rw [← restrict_prod_eq]; exact hi3
  have e2 : ∫ p in Ω, ⟪avgGrad u h p, dqGrad u h p⟫ =
      -∫ p in Ω, (dq u h p + avgRxn Q β ε u h p) * dq u h p := by
    rw [hΩdef, restrict_prod_eq, integral_prod_symm _ hI', integral_prod_symm _ hi3',
      ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hI'.prod_left_ae, ae_restrict_mem measurableSet_Ioc] with t ht ht'
    rw [integral_steklov_slice_lim hU hUb hQ hβ hu hh hM (ht₀.trans ht'.1) ht, neg_neg]
  have e3 : ∫ p in Ω, (dq u h p + avgRxn Q β ε u h p) * dq u h p =
      (∫ p in Ω, dq u h p ^ 2) + ∫ p in Ω, dq u h p * avgRxn Q β ε u h p := by
    rw [← integral_add hi1 hi2]
    congr 1; funext p; ring
  rw [e1, e3] at e2
  linarith

end Steklov

end EnergyDissipation

end PerronVariational

end
