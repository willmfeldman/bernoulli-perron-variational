/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Registry.Semilinear
public import PerronVariational.Semilinear.Profiles
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Registry.Comparison
import PerronVariational.Semilinear.ViscosityLimitCalculus

/-!
# The semilinear limit is a supersolution

Step 2 of the proof of [Proposition 5.3](#AFS:p.semilinear-limit-viscosity) of F. Abedin, W. M.
Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981.

Let `u_j` solve `∂ₜu = Δu - Q² β_{ε_j}(u)` in `U × (0, T]` with `ε_j → 0` and `u_j → u` locally
uniformly. Then `u` is a parabolic viscosity supersolution of [(3.1)](#AFS:e.bernoulli-parabolic)
([Definition 3.3](#AFS:d.parabolic-supersolution)): `semilinear_limit_isParaSuper`.

## Proof (Step 2 of the paper)

Let `φ` be a classical strict subsolution on `V̄ × [a, b]` with constants `a₀, δ₀` and `φ ≺ u` on
`∂_P(V × (a, b])`, and suppose `u(p₀) ≤ φ(p₀)` at some `p₀ ∈ \overline{{φ > 0}} ∩ (V × (a, b])`.

* As the paper says, `φ + δ` is again a classical strict subsolution for small `δ > 0`
  (`IsClassicalStrictParaSubWith.add_const`, constants `a₀ - δ, δ₀`).
* The ordering on `∂_P`: by compactness `φ + μ < u` on `∂_P` near
  `A = \overline{{φ > 0}} ∩ (V̄ × [a, b])` (`exists_bdry_margin`), and every point of `V̄ × [a, b]`
  with `φ > -δ₁` is near `A` (`exists_infDist_lt_of_neg_lt`; this is the identity
  [(5.6)](#AFS:eqn:containerMe), `limsup*_{δ → 0} \overline{{φ + δ > 0}} = \overline{{φ > 0}}`,
  which uses `|∇φ| > 0` on `{φ = 0}`).
* `(Φ_{ε,θ}(φ + δ))₊` with `θ = 1/(1 + δ₀)` is a viscosity subsolution of the semilinear equation
  (`IsClassicalStrictParaSubWith.isSemilinearViscSubOn_profileSub`, the parabolic form of
  [Lemma 3.11](#AFS:l.well-prepared)), it lies below `u_j` on `∂_P` for large `j`, so below `u_j` in
  the cylinder by the comparison principle; at `p₀` this contradicts `φ(p₀) + δ > u(p₀)`.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Helpers -/

section Helpers

/-- A zero of a differentiable space-time function with nonzero spatial gradient lies in the
closure of its positivity set. -/
theorem mem_closure_pos_of_gradₓ_ne_zero {φ : E d × ℝ → ℝ} {p : E d × ℝ}
    (hφ : DifferentiableAt ℝ φ p) (hp0 : φ p = 0) (hg : gradₓ φ p ≠ 0) :
    p ∈ closure {q | 0 < φ q} := by
  set v := gradₓ φ p with hv
  set L : ℝ → E d × ℝ := fun s ↦ (p.1 + s • v, p.2) with hL_def
  have hL : HasDerivAt L (v, (0 : ℝ)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ ↦ p.1 + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p.1
    exact h1.prodMk (hasDerivAt_const 0 p.2)
  have hL0 : L 0 = p := by simp [hL_def]
  have hφ' : HasFDerivAt φ (fderiv ℝ φ p) (L 0) := by rw [hL0]; exact hφ.hasFDerivAt
  have hd : HasDerivAt (φ ∘ L) (fderiv ℝ φ p (v, 0)) 0 := hφ'.comp_hasDerivAt 0 hL
  have hval : fderiv ℝ φ p (v, 0) = ‖v‖ ^ 2 := by
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E d) (x := v)
      (y := (fderiv ℝ φ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ))
    rw [← gradₓ_eq_fderiv hφ, ← hv, real_inner_self_eq_norm_sq] at h
    rw [h]; rfl
  have hpos : 0 < ‖v‖ ^ 2 := by positivity
  rw [hval] at hd
  have hslope := hasDerivAt_iff_tendsto_slope.1 hd
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < slope (φ ∘ L) 0 s :=
    (hslope.mono_left (nhdsWithin_mono _ fun s (hs : 0 < s) ↦ ne_of_gt hs)).eventually
      (lt_mem_nhds hpos)
  have hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), L s ∈ {q | 0 < φ q} := by
    filter_upwards [hev, self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
    rw [slope_def_field, sub_zero] at hs
    have h2 : 0 < (φ ∘ L) s - (φ ∘ L) 0 := (div_pos_iff_of_pos_right hs0).1 hs
    simp only [Function.comp, hL0, hp0, sub_zero] at h2
    exact h2
  have htend : Tendsto L (𝓝[>] 0) (𝓝 p) := by
    rw [← hL0]; exact hL.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto htend hmem

theorem isClosed_parBdry (V : Set (E d)) (a b : ℝ) : IsClosed (parBdry V a b) :=
  (isClosed_closure.prod isClosed_singleton).union (isClosed_frontier.prod isClosed_Icc)

theorem parBdry_subset {V : Set (E d)} {a b : ℝ} (hab : a ≤ b) :
    parBdry V a b ⊆ closure V ×ˢ Icc a b := by
  rintro ⟨x, t⟩ (⟨hx, ht⟩ | ⟨hx, ht⟩)
  · rw [mem_singleton_iff] at ht; subst ht; exact ⟨hx, le_rfl, hab⟩
  · exact ⟨frontier_subset_closure hx, ht⟩

theorem cyl_subset {V : Set (E d)} {a b : ℝ} : cyl V a b ⊆ closure V ×ˢ Icc a b :=
  fun _ hp ↦ ⟨subset_closure hp.1, Ioc_subset_Icc_self hp.2⟩

theorem Ioc_leftNhds {a b : ℝ} : ∀ t ∈ Ioc a b, ∃ δ > 0, Ioc (t - δ) t ⊆ Ioc a b :=
  fun t ht ↦ ⟨t - a, by linarith [ht.1], fun s hs ↦ ⟨by linarith [hs.1], hs.2.trans ht.2⟩⟩

end Helpers

/-! ### Geometry of a strict subsolution near its positivity set -/

section Geometry

variable {φ : E d × ℝ → ℝ} {K : Set (E d × ℝ)} {Q : E d → ℝ}

/-- **The identity [(5.6)](#AFS:eqn:containerMe).** If every zero of `φ` in the compact `K` lies in
`A = \overline{{φ > 0}} ∩ K`, then for every `r > 0` there is `δ₁ > 0` such that every point of `K`
with `φ > -δ₁` is within `r` of `A` (i.e. `limsup*_{δ → 0} \overline{{φ + δ > 0}} ∩ K ⊆ A`). -/
theorem exists_infDist_lt_of_neg_lt (hφ : Continuous φ) (hK : IsCompact K)
    (h0 : ∀ p ∈ K, φ p = 0 → p ∈ closure {q | 0 < φ q}) {r : ℝ} (hr : 0 < r) :
    ∃ δ₁ > 0, ∀ p ∈ K, -δ₁ < φ p → infDist p (closure {q | 0 < φ q} ∩ K) < r := by
  obtain ⟨δ₁, hδ₁, m, hm, hle⟩ := exists_margin_of_nonneg (f := φ)
    (F := fun p ↦ r - infDist p (closure {q | 0 < φ q} ∩ K)) hK hφ.continuousOn
    (continuous_const.sub (continuous_infDist_pt _)).continuousOn fun p hp hφp ↦ by
      have hpA : p ∈ closure {q | 0 < φ q} ∩ K := by
        refine ⟨?_, hp⟩
        rcases hφp.lt_or_eq with h | h
        · exact subset_closure h
        · exact h0 p hp h.symm
      rw [infDist_zero_of_mem hpA]
      linarith
  exact ⟨δ₁, hδ₁, fun p hp hφp ↦ by have := hle p hp hφp; linarith⟩

/-- **Boundary margin.** If `φ < u` on `A ∩ P_b` (`P_b` closed, inside the compact `K`), then for
some `μ, r₃ > 0`, `φ + μ < u` on `P_b ∩ {dist(·, A) < r₃}`. -/
theorem exists_bdry_margin {Pb A : Set (E d × ℝ)} (hK : IsCompact K) (hPb : IsClosed Pb)
    (hPbK : Pb ⊆ K) (hAne : A.Nonempty) (hAc : IsClosed A) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u K) (hφ : Continuous φ) (hbd : ∀ p ∈ A ∩ Pb, φ p < u p) :
    ∃ μ > 0, ∃ r₃ > 0, ∀ p ∈ Pb, infDist p A < r₃ → φ p + μ < u p := by
  have hPbc : IsCompact Pb := hK.of_isClosed_subset hPb hPbK
  obtain ⟨m', hm', hm'le⟩ := exists_pos_le_of_isCompact (hPbc.inter_left hAc)
    ((hu.mono (inter_subset_right.trans hPbK)).sub hφ.continuousOn)
    (fun p hp ↦ sub_pos.2 (hbd p hp))
  have hB4 : IsCompact (Pb ∩ (fun p ↦ u p - φ p) ⁻¹' Iic (m' / 2)) :=
    hPbc.of_isClosed_subset (((hu.mono hPbK).sub hφ.continuousOn).preimage_isClosed_of_isClosed
      hPb isClosed_Iic) inter_subset_left
  obtain ⟨r₃, hr₃, hr₃le⟩ := exists_pos_le_of_isCompact hB4
    (continuous_infDist_pt A).continuousOn (fun p hp ↦ by
      rcases (infDist_nonneg (x := p) (s := A)).lt_or_eq with h | h
      · exact h
      · exfalso
        have hpA : p ∈ A := by
          have := (mem_closure_iff_infDist_zero hAne).2 h.symm
          rwa [hAc.closure_eq] at this
        have h1 := hm'le p ⟨hpA, hp.1⟩
        have h2 : u p - φ p ≤ m' / 2 := hp.2
        rw [Pi.sub_apply] at h1
        linarith)
  refine ⟨m' / 2, by positivity, r₃, hr₃, fun p hp hd ↦ ?_⟩
  by_contra hc
  push Not at hc
  exact (hr₃le p ⟨hp, show u p - φ p ≤ m' / 2 by linarith⟩).not_gt hd

end Geometry

/-! ### The subsolution `(Φ_{ε,θ}(ψ))₊` -/

section ProfileSub

variable {β : ℝ → ℝ} {Q : E d → ℝ} {ψ : E d × ℝ → ℝ} {V : Set (E d)} {a b a₀ δ₀ ε : ℝ}

/-- **The parabolic form of [Lemma 3.11](#AFS:l.well-prepared) (subsolution case).** If `ψ` is a
classical strict subsolution of [(3.1)](#AFS:e.bernoulli-parabolic) on `V̄ × [a, b]` with constants
`a₀, δ₀`, `θ = 1/(1 + δ₀)`, and `ε` is small (`c_θ ε < a₀`, `ε ≤ a₀`), then `(Φ_{ε,θ}(ψ))₊` is a
viscosity subsolution of the semilinear equation in `V × (a, b]`. -/
theorem IsClassicalStrictParaSubWith.isSemilinearViscSubOn_profileSub
    (hψ : IsClassicalStrictParaSubWith Q ψ V a b a₀ δ₀) (hV : IsOpen V)
    (hβ : IsReactionProfile β) (hε : 0 < ε) (hcε : subConst (1 / (1 + δ₀)) * ε < a₀)
    (hεa : ε ≤ a₀) :
    IsSemilinearViscSubOn V Q β ε (Ioc a b)
      (fun p ↦ max (profileSubEps β (1 / (1 + δ₀)) ε (ψ p)) 0) := by
  set θ := 1 / (1 + δ₀) with hθ_def
  have hδ₀ := hψ.δ₀_pos
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ_def, div_lt_one (by linarith)]; linarith
  have hψ2 : ContDiff ℝ 2 ψ := hψ.contDiff.of_le (WithTop.coe_le_coe.2 le_top)
  set f := profileSubEps β θ ε with hf_def
  have hfc : ContDiff ℝ 2 f :=
    (profileSubEps_contDiff hβ hθ0 hθ1).of_le (WithTop.coe_le_coe.2 le_top)
  have hfψ : Continuous fun q ↦ f (ψ q) :=
    (profileSubEps_continuous hβ hθ0 hθ1).comp hψ.contDiff.continuous
  have hs₀ : -(subConst θ * ε) ≤ ε * profileSubZero β θ := by
    have := mul_le_mul_of_nonneg_right (profileSubZero_mem hβ hθ0 hθ1).1 hε.le
    linarith
  refine isSemilinearViscSubOn_of_local hV Ioc_leftNhds (hfψ.max continuous_const).continuousOn
    fun p hp ↦ ?_
  have hpK : p ∈ closure V ×ˢ Icc a b := ⟨subset_closure hp.1, Ioc_subset_Icc_self hp.2⟩
  rcases (le_max_right (f (ψ p)) 0).eq_or_lt with h0 | hpos
  · -- `w(p) = 0`: compare with `F = 0`
    refine ⟨fun _ ↦ 0, contDiff_const, h0, Eventually.of_forall fun q ↦ le_max_right _ _, ?_⟩
    rw [← h0, hβ.betaEps_zero]
    simp [dₜ, lapₓ]
  · have hΦ : 0 < f (ψ p) := by
      by_contra hc
      push Not at hc
      rw [max_eq_right hc] at hpos
      exact lt_irrefl _ hpos
    -- where `Φ_ε(ψ) > 0`, `ψ > ε s₀ ≥ -c_θ ε > -a₀`
    have hψp : -a₀ < ψ p := by
      have := (profileSubEps_pos_iff hβ hθ0 hθ1 hε (ψ p)).1 hΦ
      linarith
    have heq : (fun q ↦ f (ψ q)) =ᶠ[𝓝 p] fun q ↦ max (f (ψ q)) 0 := by
      filter_upwards [hfψ.continuousAt.eventually (lt_mem_nhds hΦ)] with q hq
      exact (max_eq_left hq.le).symm
    refine ⟨fun q ↦ f (ψ q), hfc.comp hψ2, heq.eq_of_nhds, heq.le, ?_⟩
    rw [heat_comp hfc hψ2, ← heq.eq_of_nhds]
    have hLap : 0 ≤ lapₓ ψ p - dₜ ψ p := by
      have := hψ.heat p ⟨hψp, hpK⟩
      linarith
    have hineq := profileSubEps_ineq hβ hθ0 hθ1 hε (ψ p) (‖gradₓ ψ p‖ ^ 2)
      (lapₓ ψ p - dₜ ψ p) (Q p.1) hLap (fun hb ↦ by
        -- where `β_ε(Φ_ε(ψ)) > 0`, `|ψ| < ε ≤ a₀`, so `(1 + δ₀) Q² ≤ |∇ψ|²`
        have hlt := mem_of_betaEps_profileSubEps_pos hβ hθ0 hθ1 hε hb
        have hg := hψ.grad p ⟨show |ψ p| ≤ a₀ from abs_le.2 ⟨by linarith, by linarith⟩, hpK⟩
        rw [hθ_def, one_div, inv_mul_eq_div, le_div_iff₀ (by linarith)]
        linarith)
    linarith

end ProfileSub

/-! ### Step 2 of [Proposition 5.3](#AFS:p.semilinear-limit-viscosity) -/

section Step2

variable {S : Setting d} {β : ℝ → ℝ} {T : ℝ} {εs : ℕ → ℝ} {us : ℕ → E d × ℝ → ℝ}
  {u : E d × ℝ → ℝ}

/-- The locally uniform limit is continuous on `U × (0, T]`. -/
theorem continuousOn_semilinearLimit
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    ContinuousOn u (S.U ×ˢ Ioc 0 T) :=
  hconv.continuousOn (Frequently.of_forall fun j ↦ (hsol j).1)

/-- The locally uniform limit is nonnegative. -/
theorem semilinearLimit_nonneg (hnn : ∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p)
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ u p := fun p hp ↦
  ge_of_tendsto (hconv.tendsto_at hp) (Eventually.of_forall fun j ↦ hnn j p hp)

/-- Uniform convergence on a compact subset of `U × (0, T]`. -/
theorem eventually_abs_sub_lt_of_isCompact
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) {K : Set (E d × ℝ)}
    (hK : IsCompact K) (hKΩ : K ⊆ S.U ×ˢ Ioc 0 T) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ j in atTop, ∀ q ∈ K, |us j q - u q| < c := by
  have h := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 (hconv.mono hKΩ)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h c hc] with j hj q hq
  rw [← Real.dist_eq, dist_comm]
  exact hj q hq

/-- **[Proposition 5.3](#AFS:p.semilinear-limit-viscosity), Step 2**: the locally uniform
limit `u` of solutions `u_j` of the semilinear equation with `ε_j → 0` is a viscosity
supersolution of [(3.1)](#AFS:e.bernoulli-parabolic) in `U × (0, T]`
([Definition 3.3](#AFS:d.parabolic-supersolution)). See the module docstring. -/
theorem semilinear_limit_isParaSuper (hβ : IsReactionProfile β) (hεpos : ∀ j, 0 < εs j)
    (hεlim : Tendsto εs atTop (𝓝 0))
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hnn : ∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p)
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    IsParaSuper S.U S.Q (Ioc 0 T) u := by
  have hucont := continuousOn_semilinearLimit hsol hconv
  refine ⟨hucont, semilinearLimit_nonneg hnn hconv, ?_⟩
  intro V a b φ hcyl hφ hbd
  obtain ⟨a₀, δ₀, hφ⟩ := hφ
  obtain ⟨hVo, hVb, hab, hKΩ⟩ := hcyl
  set K := closure V ×ˢ Icc a b with hK_def
  have hKc : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hφc : Continuous φ := hφ.contDiff.continuous
  have hposeq : posSetP φ univ = {q | 0 < φ q} := by ext; simp [posSetP]
  simp only [Prec, PrecOn, hposeq] at hbd ⊢
  intro p₀ ⟨hp₀P, hp₀cyl⟩
  by_contra hlt
  push Not at hlt
  have hp₀K : p₀ ∈ K := cyl_subset hp₀cyl
  set A := closure {q | 0 < φ q} ∩ K with hA_def
  have hAne : A.Nonempty := ⟨p₀, hp₀P, hp₀K⟩
  have hAc : IsClosed A := isClosed_closure.inter hKc.isClosed
  obtain ⟨L, hL⟩ := S.lip
  have hVU : closure V ⊆ S.U := fun x hx ↦
    (hKΩ (show (x, a) ∈ K from ⟨hx, left_mem_Icc.2 hab.le⟩)).1
  -- boundary margin: `φ + μ < u` on `∂_P` near `A`
  have hPbK : parBdry V a b ⊆ K := parBdry_subset hab.le
  obtain ⟨μ, hμ, r₃, hr₃, hmargin⟩ := exists_bdry_margin hKc (isClosed_parBdry V a b) hPbK hAne
    hAc (hucont.mono hKΩ) hφc (fun p hp ↦ hbd p ⟨hp.1.1, hp.2⟩)
  -- [(5.6)](#AFS:eqn:containerMe): points of `K` with `φ > -δ₁` are near `A`, as `∇φ ≠ 0` on
  -- `{φ = 0} ∩ K`
  obtain ⟨δ₁, hδ₁, hnear⟩ := exists_infDist_lt_of_neg_lt hφc hKc (fun p hp h0 ↦ by
    refine mem_closure_pos_of_gradₓ_ne_zero (hφ.contDiff.differentiable (by simp) p) h0 ?_
    intro hg
    have h1 := hφ.grad p ⟨show |φ p| ≤ a₀ by rw [h0, abs_zero]; exact hφ.a₀_pos.le, hp⟩
    have hQp : S.Qmin ≤ S.Q p.1 := (S.Q_mem _ (subset_closure (hVU hp.1))).1
    rw [hg, norm_zero] at h1
    nlinarith [S.Qmin_pos, hφ.δ₀_pos]) hr₃
  set δ := min (min (a₀ / 4) (μ / 4)) (δ₁ / 4) with hδ_def
  have hδ : 0 < δ := lt_min (lt_min (by linarith [hφ.a₀_pos]) (by positivity)) (by positivity)
  have hδa : 4 * δ ≤ a₀ := by
    have := min_le_left (min (a₀ / 4) (μ / 4)) (δ₁ / 4); have := min_le_left (a₀ / 4) (μ / 4)
    linarith
  have hδμ : 4 * δ ≤ μ := by
    have := min_le_left (min (a₀ / 4) (μ / 4)) (δ₁ / 4); have := min_le_right (a₀ / 4) (μ / 4)
    linarith
  have hδδ₁ : 4 * δ ≤ δ₁ := by
    have := min_le_right (min (a₀ / 4) (μ / 4)) (δ₁ / 4); linarith
  -- `φ + δ` is still a classical strict subsolution (constants `a₀ - δ, δ₀`)
  have hφδ := hφ.add_const (c := δ) (by rw [abs_of_pos hδ]; linarith)
  rw [abs_of_pos hδ] at hφδ
  set θ := 1 / (1 + δ₀) with hθ_def
  -- choose `j`
  have hev1 : ∀ᶠ j in atTop, εs j ≤ δ := hεlim.eventually (ge_mem_nhds hδ)
  have hev2 : ∀ᶠ j in atTop, subConst θ * εs j ≤ δ := by
    have : Tendsto (fun j ↦ subConst θ * εs j) atTop (𝓝 0) := by
      simpa using hεlim.const_mul (subConst θ)
    exact this.eventually (ge_mem_nhds hδ)
  obtain ⟨j, hj1, hj2, hj3⟩ := (hev1.and (hev2.and
    (eventually_abs_sub_lt_of_isCompact hconv hKc hKΩ hδ))).exists
  have hε := hεpos j
  set w : E d × ℝ → ℝ := fun p ↦ max (profileSubEps β θ (εs j) (φ p + δ)) 0 with hw_def
  have hθ0 : 0 < θ := by have := hφ.δ₀_pos; positivity
  have hθ1 : θ < 1 := by
    have := hφ.δ₀_pos; rw [hθ_def, div_lt_one (by linarith)]; linarith
  -- `w` is a viscosity subsolution of the semilinear equation ([Lemma 3.11](#AFS:l.well-prepared))
  have hsub : IsSemilinearViscSubOn V S.Q β (εs j) (Ioc a b) w :=
    hφδ.isSemilinearViscSubOn_profileSub hVo hβ hε (by linarith) (by linarith)
  -- the solution `u_j` is a viscosity supersolution in `V × (a, b]`
  have hVU' : V ⊆ S.U := subset_closure.trans hVU
  have hIoc : Ioc a b ⊆ Ioc 0 T := fun t ht ↦
    (hKΩ (show (p₀.1, t) ∈ K from ⟨subset_closure hp₀cyl.1, Ioc_subset_Icc_self ht⟩)).2
  have hsuper := Registry.isSemilinearViscSuperOn_of_solOn hVo Ioc_leftNhds
    ((hsol j).mono_domain hVU' hIoc)
  -- `w ≤ u_j` on `∂_P(V × (a, b])`
  have hbdry : ∀ p ∈ parBdry V a b, w p ≤ us j p := by
    intro p hp
    have hpK := hPbK hp
    have hpΩ := hKΩ hpK
    rcases (le_max_right (profileSubEps β θ (εs j) (φ p + δ)) 0).eq_or_lt with h0 | hpos
    · rw [hw_def]; simp only; rw [← h0]; exact hnn j p hpΩ
    · have hΦ : 0 < profileSubEps β θ (εs j) (φ p + δ) := by
        by_contra hc
        push Not at hc
        rw [max_eq_right hc] at hpos
        exact lt_irrefl _ hpos
      have hφp : -(2 * δ) < φ p := by
        have h1 := (profileSubEps_pos_iff hβ hθ0 hθ1 hε (φ p + δ)).1 hΦ
        have h2 := mul_le_mul_of_nonneg_right (profileSubZero_mem hβ hθ0 hθ1).1 hε.le
        linarith
      have hm := hmargin p hp (hnear p hpK (by linarith))
      have hup := (abs_le.1 (abs_max_profileSubEps_sub_le hβ hθ0 hθ1 hε (φ p + δ))).2
      have hj := abs_lt.1 (hj3 p hpK)
      simp only [hw_def]
      rcases le_total 0 (φ p + δ) with hφ0 | hφ0
      · rw [max_eq_left hφ0] at hup; linarith
      · rw [max_eq_right hφ0] at hup; linarith
  have hwc : ContinuousOn w K :=
    (((profileSubEps_continuous hβ hθ0 hθ1).comp (hφc.add continuous_const)).max
      continuous_const).continuousOn
  have hcomp := Registry.semilinear_comparison hVo hVb hab
    ⟨L, hL.mono (closure_mono hVU')⟩ hβ hε hwc ((hsol j).1.mono hKΩ) hsub hsuper hbdry
  have h1 := hcomp p₀ hp₀K
  have h2 : φ p₀ + δ ≤ w p₀ :=
    (self_le_profileSubEps hβ hθ0 hθ1 hε _).trans (le_max_left _ _)
  have h3 := abs_lt.1 (hj3 p₀ hp₀K)
  linarith

end Step2

end PerronVariational

end
