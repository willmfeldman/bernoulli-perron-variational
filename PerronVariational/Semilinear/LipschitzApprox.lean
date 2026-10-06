/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Registry.Semilinear
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Registry.Comparison
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Monotone
import PerronVariational.Semilinear.Profiles

/-!
# Smooth approximation of the semilinear problem

Appendix A.4 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: the proof of
Propositions A.5–A.6 ("We can assume that `Q` is smooth ... we can derive the general Lipschitz
case by approximation") and the proof of Lemma A.7 ("By a mollification argument using the
uniqueness ... it suffices to consider the case `g_ε` is smooth"). With `Q` only Lipschitz,
solutions of (3.4) are classical `C^{2,1}` but not `C^∞`, so the Bernstein argument is run on
smooth approximate problems.

## Main results

* `LipschitzWith.exists_contDiff_approx`: mollification of a `K`-Lipschitz function preserves the
  Lipschitz constant and the bounds, and is uniformly close.
* `IsSemilinearViscSuperOn.add_time`, `IsSemilinearViscSubOn.sub_time`: shifting a viscosity
  super/subsolution of the equation with coefficient `Q₁` by a function of time gives a
  super/subsolution of the equation with coefficient `Q₂`, if the shift grows fast enough.
* `IsSemilinearSolution.exists_smooth_approx`: a solution of (3.4) with Lipschitz data is the
  uniform limit on `Ū × [0, T]` of solutions with smooth `Q` and smooth data (with the same
  bounds and Lipschitz constants).
* `norm_gradient_le_of_tendsto_pointwise`: gradient bounds pass to pointwise limits on convex
  open sets.
-/

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ContDiff Gradient Laplacian Convolution

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Mollification of Lipschitz functions -/

/-- **Mollification of a Lipschitz function**: for `f` `K`-Lipschitz on `ℝᵈ` and `δ > 0` there is
a smooth `K`-Lipschitz `f'` with `|f' - f| ≤ δ`, which moreover takes values in `[a, b]` whenever
`f` does. -/
theorem LipschitzWith.exists_contDiff_approx {f : E d → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ f' : E d → ℝ, ContDiff ℝ ∞ f' ∧ LipschitzWith K f' ∧ (∀ x, |f' x - f x| ≤ δ) ∧
      ∀ a b : ℝ, (∀ x, a ≤ f x ∧ f x ≤ b) → ∀ x, a ≤ f' x ∧ f' x ≤ b := by
  set R := δ / (K + 1) with hR
  have hR0 : 0 < R := by positivity
  let φ : ContDiffBump (0 : E d) := ⟨R / 2, R, half_pos hR0, half_lt_self hR0⟩
  set f' : E d → ℝ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f with hf'
  have hval : ∀ x, f' x = ∫ t, φ.normed volume t * f (x - t) := fun x ↦ by
    rw [hf', convolution_lsmul]; rfl
  have hint : ∀ x, Integrable (fun t ↦ φ.normed volume t * f (x - t)) := fun x ↦ by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact φ.continuous_normed.mul (hf.continuous.comp (continuous_const.sub continuous_id))
    · exact φ.hasCompactSupport_normed.mul_right
  have hint1 : Integrable (φ.normed volume) := φ.integrable_normed
  refine ⟨f', ?_, ?_, ?_, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hf.continuous.locallyIntegrable
  · refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [hval, hval, Real.dist_eq, ← integral_sub (hint x) (hint y)]
    have hb : ∀ t, ‖φ.normed volume t * f (x - t) - φ.normed volume t * f (y - t)‖ ≤
        φ.normed volume t * (K * dist x y) := fun t ↦ by
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (φ.nonneg_normed t)]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
      have := hf.dist_le_mul (x - t) (y - t)
      rwa [dist_sub_right, Real.dist_eq] at this
    refine (norm_integral_le_of_norm_le (hint1.mul_const _) (Eventually.of_forall hb)).trans ?_
    rw [integral_mul_const, φ.integral_normed, one_mul]
  · intro x
    have := φ.dist_normed_convolution_le (μ := volume) hf.continuous.aestronglyMeasurable
      (x₀ := x) (ε := δ) fun y hy ↦ by
        refine (hf.dist_le_mul y x).trans ?_
        rw [mem_ball] at hy
        have hK : (K : ℝ) * R ≤ δ := by
          rw [hR, mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          linarith
        calc (K : ℝ) * dist y x ≤ K * R := mul_le_mul_of_nonneg_left hy.le K.2
          _ ≤ δ := hK
    rwa [Real.dist_eq] at this
  · intro a b hab x
    rw [hval]
    constructor
    · calc a = ∫ t, φ.normed volume t * a := by rw [integral_mul_const, φ.integral_normed, one_mul]
        _ ≤ ∫ t, φ.normed volume t * f (x - t) :=
          integral_mono (hint1.mul_const _) (hint x) fun t ↦
            mul_le_mul_of_nonneg_left (hab _).1 (φ.nonneg_normed t)
    · calc ∫ t, φ.normed volume t * f (x - t) ≤ ∫ t, φ.normed volume t * b :=
          integral_mono (hint x) (hint1.mul_const _) fun t ↦
            mul_le_mul_of_nonneg_left (hab _).2 (φ.nonneg_normed t)
        _ = b := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- A function `K`-Lipschitz on a set `s` with values in `[a, b]` on `s` is, for every `δ > 0`,
uniformly `δ`-close on `s` to a smooth `K`-Lipschitz function with values in `[a, b]`
(McShane extension, truncation, mollification). -/
theorem LipschitzOnWith.exists_contDiff_approx {f : E d → ℝ} {K : ℝ≥0} {s : Set (E d)}
    (hf : LipschitzOnWith K f s) {a b : ℝ} (hab : a ≤ b) (hfab : ∀ x ∈ s, a ≤ f x ∧ f x ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ f' : E d → ℝ, ContDiff ℝ ∞ f' ∧ LipschitzWith K f' ∧ (∀ x ∈ s, |f' x - f x| ≤ δ) ∧
      ∀ x, a ≤ f' x ∧ f' x ≤ b := by
  obtain ⟨F, hF, hFeq⟩ := hf.extend_real
  set G : E d → ℝ := fun x ↦ max a (min (F x) b) with hG
  have hGlip : LipschitzWith K G := (hF.min_const b).const_max a
  have hGab : ∀ x, a ≤ G x ∧ G x ≤ b := fun x ↦
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hGeq : ∀ x ∈ s, G x = f x := fun x hx ↦ by
    simp only [hG, ← hFeq hx, min_eq_left (hfab x hx).2, max_eq_right (hfab x hx).1]
  obtain ⟨f', hf's, hf'lip, hf'close, hf'ab⟩ := LipschitzWith.exists_contDiff_approx hGlip hδ
  exact ⟨f', hf's, hf'lip, fun x hx ↦ by rw [← hGeq x hx]; exact hf'close x,
    hf'ab a b hGab⟩

/-! ### Shifting viscosity solutions by a function of time -/

section Shift

variable {V : Set (E d)} {I : Set ℝ} {Q₁ Q₂ : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ}
  {u : E d × ℝ → ℝ} {c : ℝ → ℝ}

/-- `ψ ± c(t)` and `ψ` have the same spatial Laplacian. -/
theorem lapₓ_add_time {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (c : ℝ → ℝ) (p : E d × ℝ) :
    lapₓ (fun q ↦ ψ q + c q.2) p = lapₓ ψ p := by
  simp only [lapₓ]
  have e : (fun y ↦ ψ (y, p.2) + c p.2) = (fun y ↦ ψ (y, p.2)) + fun _ ↦ c p.2 := rfl
  rw [e, ContDiffAt.laplacian_add (contDiff_spaceSlice_two hψ p.2).contDiffAt contDiffAt_const,
    InnerProductSpace.laplacian_const, Pi.zero_apply, add_zero]

/-- The time derivative of `ψ + c(t)`. -/
theorem dₜ_add_time {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) {c : ℝ → ℝ} (hc : Differentiable ℝ c)
    (p : E d × ℝ) : dₜ (fun q ↦ ψ q + c q.2) p = dₜ ψ p + deriv c p.2 := by
  simp only [dₜ]
  exact deriv_add (differentiableAt_timeLine hψ p.1 p.2) (hc p.2)

/-- **Shift of a supersolution.** If `u` is a viscosity supersolution with coefficient `Q₁` and
`c ∈ C²(ℝ)` satisfies `Q₁² β_ε(u) - Q₂² β_ε(u + c) ≤ c'` on `V × I`, then `u + c(t)` is a
viscosity supersolution with coefficient `Q₂`. -/
theorem IsSemilinearViscSuperOn.add_time (hu : IsSemilinearViscSuperOn V Q₁ β ε I u)
    (hc : ContDiff ℝ 2 c)
    (h : ∀ p ∈ V ×ˢ I, Q₁ p.1 ^ 2 * betaEps β ε (u p) - Q₂ p.1 ^ 2 * betaEps β ε (u p + c p.2) ≤
      deriv c p.2) :
    IsSemilinearViscSuperOn V Q₂ β ε I (fun p ↦ u p + c p.2) := by
  refine ⟨hu.1.add (hc.continuous.comp continuous_snd).continuousOn, fun ψ hψ p hp htouch ↦ ?_⟩
  have hc' : ContDiff ℝ 2 (-c) := hc.neg
  have hψ' : ContDiff ℝ 2 (fun q ↦ ψ q + (-c) q.2) := hψ.add (hc'.comp contDiff_snd)
  obtain ⟨hpS, hpeq, hev⟩ := htouch
  have htouch' : TouchesBelow (fun q ↦ ψ q + (-c) q.2) u ((V ×ˢ I) ∩ {q | q.2 ≤ p.2}) p := by
    refine ⟨hpS, by simp only [Pi.neg_apply] at hpeq ⊢; linarith, hev.mono fun q hq ↦ ?_⟩
    simp only [Pi.neg_apply] at hq ⊢; linarith
  have key := hu.2 _ hψ' p hp htouch'
  rw [dₜ_add_time hψ (hc'.differentiable (by norm_num)), lapₓ_add_time hψ] at key
  have hd : deriv (-c) p.2 = -deriv c p.2 := by
    change deriv (fun s ↦ -c s) p.2 = _; exact deriv.neg
  rw [hd] at key
  have := h p hp
  linarith

/-- **Shift of a subsolution** (dual of `IsSemilinearViscSuperOn.add_time`): if
`Q₂² β_ε(u - c) - Q₁² β_ε(u) ≤ c'` on `V × I`, then `u - c(t)` is a viscosity subsolution with
coefficient `Q₂`. -/
theorem IsSemilinearViscSubOn.sub_time (hu : IsSemilinearViscSubOn V Q₁ β ε I u)
    (hc : ContDiff ℝ 2 c)
    (h : ∀ p ∈ V ×ˢ I, Q₂ p.1 ^ 2 * betaEps β ε (u p - c p.2) - Q₁ p.1 ^ 2 * betaEps β ε (u p) ≤
      deriv c p.2) :
    IsSemilinearViscSubOn V Q₂ β ε I (fun p ↦ u p - c p.2) := by
  refine ⟨hu.1.sub (hc.continuous.comp continuous_snd).continuousOn, fun ψ hψ p hp htouch ↦ ?_⟩
  have hψ' : ContDiff ℝ 2 (fun q ↦ ψ q + c q.2) := hψ.add (hc.comp contDiff_snd)
  obtain ⟨hpS, hpeq, hev⟩ := htouch
  have htouch' : TouchesAbove (fun q ↦ ψ q + c q.2) u ((V ×ˢ I) ∩ {q | q.2 ≤ p.2}) p := by
    refine ⟨hpS, by simp only at hpeq ⊢; linarith, hev.mono fun q hq ↦ ?_⟩
    simp only at hq ⊢; linarith
  have key := hu.2 _ hψ' p hp htouch'
  rw [dₜ_add_time hψ (hc.differentiable (by norm_num)), lapₓ_add_time hψ] at key
  have := h p hp
  simp only at this ⊢
  linarith

end Shift

/-! ### Approximation by smooth problems -/

section Approx

variable {β : ℝ → ℝ}

/-- The pointwise inequality behind the approximation: for `q₁, q₂ ∈ [0, Q_max]` with
`|q₁² - q₂²| ≤ θ` and `|s - s'| ≤ c`, `q₁² β_ε(s) - q₂² β_ε(s') ≤ θ βmax/ε + Q_max² (Lβ/ε²) c`. -/
theorem sq_mul_betaEps_sub_le (hβ : IsReactionProfile β) {βmax Lβ : ℝ}
    (hβmax : ∀ s, β s ≤ βmax)
    (hLβ : ∀ ε > 0, ∀ s s' : ℝ, |betaEps β ε s - betaEps β ε s'| ≤ Lβ / ε ^ 2 * |s - s'|)
    (hLβ0 : 0 ≤ Lβ) {ε : ℝ} (hε : 0 < ε) {q₁ q₂ Qmax θ s s' c : ℝ} (hq₂ : 0 ≤ q₂)
    (hq₂M : q₂ ≤ Qmax) (hθ : |q₁ ^ 2 - q₂ ^ 2| ≤ θ) (hc : |s - s'| ≤ c) :
    q₁ ^ 2 * betaEps β ε s - q₂ ^ 2 * betaEps β ε s' ≤
      θ * (βmax / ε) + Qmax ^ 2 * (Lβ / ε ^ 2) * c := by
  have hb0 : 0 ≤ betaEps β ε s := hβ.betaEps_nonneg ε s hε.le
  have hb1 : betaEps β ε s ≤ βmax / ε := div_le_div_of_nonneg_right (hβmax _) hε.le
  have h1 : (q₁ ^ 2 - q₂ ^ 2) * betaEps β ε s ≤ θ * (βmax / ε) := by
    calc (q₁ ^ 2 - q₂ ^ 2) * betaEps β ε s ≤ |q₁ ^ 2 - q₂ ^ 2| * betaEps β ε s :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hb0
      _ ≤ θ * (βmax / ε) := mul_le_mul hθ hb1 hb0 ((abs_nonneg _).trans hθ)
  have h2 : q₂ ^ 2 * (betaEps β ε s - betaEps β ε s') ≤ Qmax ^ 2 * (Lβ / ε ^ 2) * c := by
    have hq : q₂ ^ 2 ≤ Qmax ^ 2 := pow_le_pow_left₀ hq₂ hq₂M 2
    have hd := (le_abs_self _).trans (hLβ ε hε s s')
    have hd' : Lβ / ε ^ 2 * |s - s'| ≤ Lβ / ε ^ 2 * c :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    calc q₂ ^ 2 * (betaEps β ε s - betaEps β ε s') ≤ q₂ ^ 2 * (Lβ / ε ^ 2 * c) :=
          mul_le_mul_of_nonneg_left (hd.trans hd') (sq_nonneg _)
      _ ≤ Qmax ^ 2 * (Lβ / ε ^ 2 * c) :=
          mul_le_mul_of_nonneg_right hq (mul_nonneg (by positivity) ((abs_nonneg _).trans hc))
      _ = _ := by ring
  linarith

/-- The same setting with a different coefficient field `Q'` (Lipschitz on `Ū`, same bounds). -/
def Setting.withQ (S : Setting d) (Q' : E d → ℝ) (hlip : ∃ K, LipschitzOnWith K Q' (closure S.U))
    (hmem : ∀ x ∈ closure S.U, S.Qmin ≤ Q' x ∧ Q' x ≤ S.Qmax) : Setting d :=
  { S with Q := Q', lip := hlip, Q_mem := hmem }

/-- **Smooth approximation of the problem.** Let `u` solve (3.4) with data `g` which is
`L`-Lipschitz on `Ū` with values in `[m, M]`, and let `Q` be `K`-Lipschitz on `Ū`. For every
`δ > 0` and `T` there are a setting `S'` (same domain and bounds) with smooth `K`-Lipschitz
coefficient `S'.Q ∈ [Q_min, Q_max]`, smooth `L`-Lipschitz data `g' ∈ [m, M]`, and a solution `u'`
of (3.4) for `(S', g')` with `|u' - u| ≤ δ` on `Ū × [0, T]`. Existence of `u'` is the classical
well-posedness of the semilinear problem (`Registry.semilinear_exists`, from parabolic-basic-theory
v0.1.0); closeness is the comparison principle `Registry.semilinear_comparison` with
`u' ± c(t)`, `c(t) = (η + D t) e^{Λ t}`. -/
theorem IsSemilinearSolution.exists_smooth_approx (S : Setting d) (hβ : IsReactionProfile β)
    {ε : ℝ} (hε : 0 < ε) {g : E d → ℝ} {L : ℝ≥0} (hg : LipschitzOnWith L g (closure S.U))
    {m M : ℝ} (hmM : m ≤ M) (hgM : ∀ x ∈ closure S.U, m ≤ g x ∧ g x ≤ M)
    {u : E d × ℝ → ℝ} (hu : IsSemilinearSolution S.U S.Q β ε g u) {K : ℝ≥0}
    (hK : LipschitzOnWith K S.Q (closure S.U)) :
    ∀ δ > 0, ∀ T : ℝ, ∃ (S' : Setting d) (g' : E d → ℝ) (u' : E d × ℝ → ℝ),
      S'.U = S.U ∧ S'.Qmin = S.Qmin ∧ S'.Qmax = S.Qmax ∧ ContDiff ℝ ∞ S'.Q ∧
      LipschitzWith K S'.Q ∧ (∀ x, S.Qmin ≤ S'.Q x ∧ S'.Q x ≤ S.Qmax) ∧
      ContDiff ℝ ∞ g' ∧ LipschitzWith L g' ∧ (∀ x, m ≤ g' x ∧ g' x ≤ M) ∧
      IsSemilinearSolution S.U S'.Q β ε g' u' ∧
      ∀ x ∈ closure S.U, ∀ t ∈ Icc 0 T, |u' (x, t) - u (x, t)| ≤ δ := by
  intro δ hδ T
  obtain ⟨βmax, hβmax0, hβmax⟩ := hβ.exists_le
  obtain ⟨Lβ, hLβ0, hLβ⟩ := hβ.exists_abs_betaEps_sub_le
  have hQmax0 : 0 ≤ S.Qmax := S.Qmin_pos.le.trans S.Qmin_le_Qmax
  set T' := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  set Λ := S.Qmax ^ 2 * (Lβ / ε ^ 2) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set η := δ / 2 * Real.exp (-(Λ * T')) with hη
  have hη0 : 0 < η := by positivity
  set ρ := δ * ε / (4 * (S.Qmax + 1) * (βmax + 1) * (T' + 1) * Real.exp (Λ * T')) with hρ
  have hρ0 : 0 < ρ := by positivity
  set D := 2 * S.Qmax * ρ * (βmax / ε) with hD
  have hD0 : 0 ≤ D := by positivity
  -- the smooth coefficient and data
  obtain ⟨Q', hQ's, hQ'lip, hQ'close, hQ'mem⟩ :=
    LipschitzOnWith.exists_contDiff_approx hK S.Qmin_le_Qmax
    (fun x hx ↦ S.Q_mem x hx) hρ0
  obtain ⟨g', hg's, hg'lip, hg'close, hg'mem⟩ :=
    LipschitzOnWith.exists_contDiff_approx hg hmM hgM hη0
  set S' := S.withQ Q' ⟨K, hQ'lip.lipschitzOnWith⟩ (fun x _ ↦ hQ'mem x) with hS'
  obtain ⟨u', hu'⟩ := Registry.semilinear_exists S' hβ hε ⟨L, hg'lip.lipschitzOnWith⟩
  refine ⟨S', g', u', rfl, rfl, rfl, hQ's, hQ'lip, hQ'mem, hg's, hg'lip, hg'mem, hu', ?_⟩
  -- the shift `c(t) = (η + D t) e^{Λ t}`
  set c : ℝ → ℝ := fun t ↦ (η + D * t) * Real.exp (Λ * t) with hc
  have hcs : ContDiff ℝ 2 c := by rw [hc]; fun_prop
  have hderiv : ∀ t, deriv c t = D * Real.exp (Λ * t) + Λ * c t := fun t ↦ by
    have h1 : HasDerivAt (fun t ↦ η + D * t) D t := by
      simpa using ((hasDerivAt_id t).const_mul D).const_add η
    have h2 : HasDerivAt (fun t ↦ Real.exp (Λ * t)) (Real.exp (Λ * t) * Λ) t := by
      simpa using ((hasDerivAt_id t).const_mul Λ).exp
    have h3 : HasDerivAt c (D * Real.exp (Λ * t) + (η + D * t) * (Real.exp (Λ * t) * Λ)) t :=
      h1.mul h2
    rw [h3.deriv, hc]; ring
  have hc0 : ∀ t, 0 ≤ t → η ≤ c t := fun t ht ↦ by
    have h1 : 1 ≤ Real.exp (Λ * t) := Real.one_le_exp (by positivity)
    have h2 : η ≤ η + D * t := by nlinarith
    calc η ≤ η + D * t := h2
      _ ≤ (η + D * t) * Real.exp (Λ * t) := le_mul_of_one_le_right (by positivity) h1
  have hcT : ∀ t ∈ Icc 0 T', c t ≤ δ := fun t ht ↦ by
    have h1 : Real.exp (Λ * t) ≤ Real.exp (Λ * T') :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hΛ0)
    have h2 : (η + D * t) * Real.exp (Λ * t) ≤ (η + D * T') * Real.exp (Λ * T') :=
      mul_le_mul (by nlinarith [ht.2, ht.1]) h1 (by positivity) (by nlinarith [ht.1])
    have h3 : η * Real.exp (Λ * T') = δ / 2 := by
      rw [hη, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    have h4 : D * T' * Real.exp (Λ * T') ≤ δ / 2 := by
      have hE : 0 < Real.exp (Λ * T') := Real.exp_pos _
      have e : D * T' * Real.exp (Λ * T') = δ / 2 * (S.Qmax * βmax * T' /
          ((S.Qmax + 1) * (βmax + 1) * (T' + 1))) := by
        rw [hD, hρ]; field_simp; ring
      rw [e]
      have : S.Qmax * βmax * T' ≤ (S.Qmax + 1) * (βmax + 1) * (T' + 1) := by
        linarith [mul_nonneg (mul_nonneg hQmax0 hβmax0.le) hT'0, mul_nonneg hQmax0 hβmax0.le,
          mul_nonneg hQmax0 hT'0, mul_nonneg hβmax0.le hT'0]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 this)
    change (η + D * t) * Real.exp (Λ * t) ≤ δ
    linarith
  -- the two pointwise shift inequalities
  have hQsq : ∀ x ∈ closure S.U, |Q' x ^ 2 - S.Q x ^ 2| ≤ 2 * S.Qmax * ρ := fun x hx ↦ by
    have h1 := hQ'close x hx
    obtain ⟨a1, a2⟩ := S.Q_mem x hx
    obtain ⟨b1, b2⟩ := hQ'mem x
    rw [sq_sub_sq, abs_mul]
    have : |Q' x + S.Q x| ≤ 2 * S.Qmax := by
      rw [abs_of_nonneg (by linarith [S.Qmin_pos])]; linarith
    exact mul_le_mul this h1 (abs_nonneg _) (by linarith)
  have hkey : ∀ x ∈ closure S.U, ∀ t, 0 ≤ t → ∀ s s' : ℝ, |s - s'| ≤ c t →
      (∀ q₁ q₂ : ℝ, (q₁ = Q' x ∧ q₂ = S.Q x) ∨ (q₁ = S.Q x ∧ q₂ = Q' x) →
        q₁ ^ 2 * betaEps β ε s - q₂ ^ 2 * betaEps β ε s' ≤ deriv c t) := by
    intro x hx t ht s s' hss q₁ q₂ hq
    have hθ : |q₁ ^ 2 - q₂ ^ 2| ≤ 2 * S.Qmax * ρ := by
      rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hQsq x hx
      · rw [abs_sub_comm]; exact hQsq x hx
    have hq₂ : 0 ≤ q₂ ∧ q₂ ≤ S.Qmax := by
      rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨S.Qmin_pos.le.trans (S.Q_mem x hx).1, (S.Q_mem x hx).2⟩
      · exact ⟨S.Qmin_pos.le.trans (hQ'mem x).1, (hQ'mem x).2⟩
    have h := sq_mul_betaEps_sub_le hβ hβmax hLβ hLβ0 hε hq₂.1 hq₂.2 hθ hss
    rw [hderiv]
    have h1 : 1 ≤ Real.exp (Λ * t) := Real.one_le_exp (by positivity)
    have : 2 * S.Qmax * ρ * (βmax / ε) = D := by rw [hD]
    rw [this] at h
    nlinarith
  -- comparison
  intro x hx t ht
  have hb : (0 : ℝ) < t + 1 := by linarith [ht.1]
  have hpt : (x, t) ∈ closure S.U ×ˢ Icc 0 (t + 1) := ⟨hx, ht.1, by linarith⟩
  have hctT : c t ≤ δ := hcT t ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
  have hsub_u := hu.viscSubOn (t + 1)
  have hsuper_u := hu.viscSuperOn (t + 1)
  have hsub_u' := hu'.viscSubOn (t + 1)
  have hsuper_u' := hu'.viscSuperOn (t + 1)
  have hcc : ContinuousOn (fun q : E d × ℝ ↦ c q.2) (closure S.U ×ˢ Icc 0 (t + 1)) :=
    (hcs.continuous.comp continuous_snd).continuousOn
  -- `u ≤ u' + c`
  have h1 : u (x, t) ≤ u' (x, t) + c t := by
    have hS : IsSemilinearViscSuperOn S.U S.Q β ε (Ioc 0 (t + 1)) (fun p ↦ u' p + c p.2) :=
      hsuper_u'.add_time hcs fun p hp ↦ hkey p.1 (subset_closure hp.1) p.2 hp.2.1.le _ _
        (by rw [sub_add_cancel_left, abs_neg, abs_of_nonneg (hη0.le.trans (hc0 p.2 hp.2.1.le))])
        _ _ (Or.inl ⟨rfl, rfl⟩)
    refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
      (hu.continuousOn_Icc _) ((hu'.continuousOn_Icc _).add hcc) hsub_u hS (fun p hp ↦ ?_) _ hpt
    rw [hu.eq_on_parBdry hp]
    have hp1 := parBdry_fst_mem hp
    have ht0 : 0 ≤ p.2 := by
      rcases hp with ⟨-, h⟩ | ⟨-, h⟩
      · rw [mem_singleton_iff] at h; rw [h]
      · exact h.1
    have e : u' p = g' p.1 := hu'.eq_on_parBdry (S := S') hp
    change g p.1 ≤ u' p + c p.2
    rw [e]
    have h3 := hg'close p.1 hp1
    have h4 := hc0 p.2 ht0
    rw [abs_le] at h3
    linarith
  -- `u' - c ≤ u`
  have h2 : u' (x, t) - c t ≤ u (x, t) := by
    have hS : IsSemilinearViscSubOn S.U S.Q β ε (Ioc 0 (t + 1)) (fun p ↦ u' p - c p.2) :=
      hsub_u'.sub_time hcs fun p hp ↦ hkey p.1 (subset_closure hp.1) p.2 hp.2.1.le _ _
        (by rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (hη0.le.trans (hc0 p.2 hp.2.1.le))])
        _ _ (Or.inr ⟨rfl, rfl⟩)
    refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
      ((hu'.continuousOn_Icc _).sub hcc) (hu.continuousOn_Icc _) hS hsuper_u (fun p hp ↦ ?_) _ hpt
    rw [hu.eq_on_parBdry hp]
    have hp1 := parBdry_fst_mem hp
    have ht0 : 0 ≤ p.2 := by
      rcases hp with ⟨-, h⟩ | ⟨-, h⟩
      · rw [mem_singleton_iff] at h; rw [h]
      · exact h.1
    have e : u' p = g' p.1 := hu'.eq_on_parBdry (S := S') hp
    change u' p - c p.2 ≤ g p.1
    rw [e]
    have h3 := hg'close p.1 hp1
    have h4 := hc0 p.2 ht0
    rw [abs_le] at h3
    linarith
  rw [abs_le]
  constructor <;> linarith

/-! ### Gradient bounds pass to pointwise limits -/

/-- **Gradient bounds pass to pointwise limits** on convex open sets: if `F i → f` pointwise on
`V` along a nontrivial filter, `F i` differentiable on `V` with `‖∇F i‖ ≤ C i` there and
`C i → C₀`, then `‖∇f‖ ≤ C₀` on `V`. -/
theorem norm_gradient_le_of_tendsto_pointwise {ι : Type*} {l : Filter ι} [l.NeBot] {V : Set (E d)}
    (hV : IsOpen V) (hVc : Convex ℝ V) {f : E d → ℝ} {F : ι → E d → ℝ} {C : ι → ℝ} {C₀ : ℝ}
    (hF : ∀ i, ∀ y ∈ V, DifferentiableAt ℝ (F i) y) (hFC : ∀ i, ∀ y ∈ V, ‖∇ (F i) y‖ ≤ C i)
    (hC : Tendsto C l (𝓝 C₀)) (hlim : ∀ y ∈ V, Tendsto (fun i ↦ F i y) l (𝓝 (f y)))
    {x : E d} (hx : x ∈ V) : ‖∇ f x‖ ≤ C₀ := by
  have hC₀ : 0 ≤ C₀ := ge_of_tendsto hC (Eventually.of_forall fun i ↦
    (norm_nonneg _).trans (hFC i x hx))
  rw [norm_gradient_eq_norm_fderiv]
  refine norm_fderiv_le_of_lip' ℝ hC₀ ?_
  filter_upwards [hV.mem_nhds hx] with y hy
  have hi : ∀ i, ‖F i y - F i x‖ ≤ C i * ‖y - x‖ := fun i ↦
    hVc.norm_image_sub_le_of_norm_fderiv_le (hF i)
      (fun z hz ↦ by rw [← norm_gradient_eq_norm_fderiv]; exact hFC i z hz) hx hy
  exact le_of_tendsto_of_tendsto (((hlim y hy).sub (hlim x hx)).norm)
    (hC.mul_const _) (Eventually.of_forall hi)

end Approx

end PerronVariational

end
