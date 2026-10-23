/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import PerronVariational.Defs.Stationary

/-!
# Stationary solutions are stationary parabolic solutions ([Remark 3.4](#AFS:r.statToPara))

[Remark 3.4](#AFS:r.statToPara) of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. A viscosity
subsolution (resp. supersolution) `u` of [(1.1)](#AFS:e.bernoulli-basic) in `U` gives the
time-independent parabolic subsolution (resp. supersolution) `(x, t) ↦ u(x)` of
[(3.1)](#AFS:e.bernoulli-parabolic) on `U × I`, for any time set `I`.

The proof is the paper's first-crossing argument: for a strict barrier `φ` ordered on the
parabolic boundary, take the first time `t₀` at which the ordering fails on the relevant closed
set (compactness of `V̄ × [a, b]`); the crossing point `(x₀, t₀)` lies off the parabolic boundary,
`x ↦ φ(x, t₀)` touches `u` at `x₀`, and `∂ₜφ(x₀, t₀)` has a sign. Since `φ(x₀, t₀) = u(x₀) ≥ 0`,
condition (i) of the classical strict barrier gives the sign of `Δφ(x₀, t₀)`, and if
`φ(x₀, t₀) = 0` condition (ii) gives `|∇φ(x₀, t₀)| < Q(x₀)` (resp. `>`); this needs `Q > 0`,
assumed on `U`. This contradicts the stationary viscosity property.

The same lift applies to barriers: a smooth strict sub/supersolution of
[(1.1)](#AFS:e.bernoulli-basic) in the sense of [Definition 2.3](#AFS:d.strict-sub)
(`IsUnifStrictSub`/`IsUnifStrictSuper`), viewed as time-independent, is a classical strict
sub/supersolution of [(3.1)](#AFS:e.bernoulli-parabolic) on every `V̄ × [a, b]` with the same
constants (`IsUnifStrictSub.isClassicalStrictParaSub`,
`IsUnifStrictSuper.isClassicalStrictParaSuper`; used for the barrier of
[Proposition 3.6](#AFS:p.monotone-nondegen-relaxed)).
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Auxiliary one-variable facts -/

/-- If `f(t₀) ≤ f(t)` for `t ∈ (a, t₀)`, then `f'(t₀) ≤ 0`. -/
theorem deriv_nonpos_of_le_left {f : ℝ → ℝ} {a t₀ : ℝ} (hf : DifferentiableAt ℝ f t₀)
    (ha : a < t₀) (h : ∀ t ∈ Ioo a t₀, f t₀ ≤ f t) : deriv f t₀ ≤ 0 := by
  have ht := (hasDerivAt_iff_tendsto_slope.1 hf.hasDerivAt).mono_left
    (show 𝓝[<] t₀ ≤ 𝓝[≠] t₀ from nhdsWithin_mono t₀ fun t (ht : t < t₀) ↦ ne_of_lt ht)
  refine le_of_tendsto ht (Filter.mem_of_superset (Ioo_mem_nhdsLT ha) fun t htI ↦ ?_)
  rw [Set.mem_ofPred_eq, slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith [h t htI]) (by linarith [htI.2])

/-- If `f(t) ≤ f(t₀)` for `t ∈ (a, t₀)`, then `0 ≤ f'(t₀)`. -/
theorem deriv_nonneg_of_le_left {f : ℝ → ℝ} {a t₀ : ℝ} (hf : DifferentiableAt ℝ f t₀)
    (ha : a < t₀) (h : ∀ t ∈ Ioo a t₀, f t ≤ f t₀) : 0 ≤ deriv f t₀ := by
  have := deriv_nonpos_of_le_left (f := fun t ↦ -f t) hf.neg ha fun t ht ↦ neg_le_neg (h t ht)
  rw [deriv.fun_neg] at this
  linarith

/-! ### First crossing -/

/-- **First crossing time.** If `f ≤ 0` somewhere on `S ∩ (V̄ × [a, b])` (`S` closed, `V`
bounded, `f` continuous there), there is a point `p₀` of `S ∩ (V̄ × [a, b])` with `f p₀ ≤ 0` such
that `f > 0` on all points of `S ∩ (V̄ × [a, b])` at earlier times. -/
theorem exists_first_crossing {V : Set (E d)} {a b : ℝ} (hV : Bornology.IsBounded V)
    {S : Set (E d × ℝ)} (hS : IsClosed S) {f : E d × ℝ → ℝ}
    (hf : ContinuousOn f (closure V ×ˢ Icc a b)) {p : E d × ℝ}
    (hp : p ∈ S ∩ (closure V ×ˢ Icc a b)) (hfp : f p ≤ 0) :
    ∃ p₀ ∈ S ∩ (closure V ×ˢ Icc a b), f p₀ ≤ 0 ∧
      ∀ q ∈ S ∩ (closure V ×ˢ Icc a b), q.2 < p₀.2 → 0 < f q := by
  have hD : IsClosed (S ∩ (closure V ×ˢ Icc a b)) := hS.inter (isClosed_closure.prod isClosed_Icc)
  have hC : IsClosed ((S ∩ (closure V ×ˢ Icc a b)) ∩ f ⁻¹' Iic 0) :=
    (hf.mono inter_subset_right).preimage_isClosed_of_isClosed hD isClosed_Iic
  have hCc : IsCompact ((S ∩ (closure V ×ˢ Icc a b)) ∩ f ⁻¹' Iic 0) :=
    (hV.isCompact_closure.prod isCompact_Icc).of_isClosed_subset hC fun q hq ↦ hq.1.2
  obtain ⟨p₀, hp₀, hmin⟩ := hCc.exists_isMinOn ⟨p, hp, hfp⟩ continuous_snd.continuousOn
  refine ⟨p₀, hp₀.1, hp₀.2, fun q hq hlt ↦ not_le.1 fun hfq ↦ ?_⟩
  have := hmin ⟨hq, hfq⟩
  simp only [Set.mem_ofPred_eq] at this
  linarith

theorem posSetP_const (u : E d → ℝ) (U : Set (E d)) (I : Set ℝ) :
    posSetP (fun p : E d × ℝ ↦ u p.1) (U ×ˢ I) = posSet u U ×ˢ I := by
  ext p
  simp only [posSetP, posSet, mem_prod, Set.mem_ofPred_eq]
  tauto

/-! ### [Remark 3.4](#AFS:r.statToPara) -/

/-- **[Remark 3.4](#AFS:r.statToPara)**, subsolution case. A viscosity subsolution of
[(1.1)](#AFS:e.bernoulli-basic) in `U` is a (stationary) parabolic viscosity subsolution of
[(3.1)](#AFS:e.bernoulli-parabolic) in `U × I`. -/
theorem IsViscSub.isParaSub_const {U : Set (E d)} {Q u : E d → ℝ} (hu : IsViscSub U Q u)
    (hQ : ∀ x ∈ U, 0 < Q x) (I : Set ℝ) : IsParaSub U Q I (fun p ↦ u p.1) := by
  refine ⟨hu.1.comp continuousOn_fst fun p hp ↦ hp.1, fun p hp ↦ hu.2.1 p.1 hp.1, ?_⟩
  intro V a b φ hadm hφ hbd
  obtain ⟨hVo, hVb, hab, hVU⟩ := hadm
  obtain ⟨a₀, δ₀, hφ⟩ := hφ
  have hφs := hφ.contDiff
  have hEcl' : closure (posSetP (fun p : E d × ℝ ↦ u p.1) (U ×ˢ I)) =
      closure (posSet u U) ×ˢ closure I := by
    rw [posSetP_const, closure_prod_eq]
  rintro p ⟨hpE, hpcyl⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hwc : ContinuousOn (fun q : E d × ℝ ↦ φ q - u q.1) (closure V ×ˢ Icc a b) :=
    hφs.continuous.continuousOn.sub ((hu.1.comp continuousOn_fst fun q hq ↦ hq.1).mono hVU)
  obtain ⟨⟨y₀, t₀⟩, ⟨hp₀E, hy₀V, ht₀⟩, hf₀, hfirst⟩ := exists_first_crossing hVb isClosed_closure
    hwc ⟨hpE, subset_closure hpcyl.1, Ioc_subset_Icc_self hpcyl.2⟩ (by simpa using hcon)
  simp only at hf₀ hfirst hy₀V ht₀
  have hIcc : Icc a b ⊆ I := fun t ht ↦
    (hVU (show (y₀, t) ∈ closure V ×ˢ Icc a b from ⟨hy₀V, ht⟩)).2
  have hy₀P : y₀ ∈ closure (posSet u U) := by rw [hEcl'] at hp₀E; exact hp₀E.1
  -- the crossing point is not on the parabolic boundary
  have hnotbd : (y₀, t₀) ∉ parBdry V a b := fun h ↦ by
    have := hbd (y₀, t₀) ⟨hp₀E, h⟩
    simp only at this
    linarith
  have hat₀ : a < t₀ := lt_of_le_of_ne ht₀.1 fun h ↦ hnotbd (Or.inl ⟨hy₀V, h.symm⟩)
  have hy₀ : y₀ ∈ V := by
    by_contra hy
    exact hnotbd (Or.inr ⟨⟨hy₀V, fun h ↦ hy (hVo.interior_eq ▸ h)⟩, ht₀⟩)
  have hy₀U : y₀ ∈ U :=
    (hVU (show (y₀, t₀) ∈ closure V ×ˢ Icc a b from ⟨subset_closure hy₀, ht₀⟩)).1
  -- ordering before `t₀`
  have hbefore : ∀ y ∈ closure (posSet u U), y ∈ closure V → ∀ t ∈ Ioo a t₀, u y < φ (y, t) := by
    intro y hyP hyV t ht
    have hq : (y, t) ∈ closure (posSetP (fun p : E d × ℝ ↦ u p.1) (U ×ˢ I)) ∩
        (closure V ×ˢ Icc a b) := by
      refine ⟨?_, hyV, ht.1.le, ht.2.le.trans ht₀.2⟩
      rw [hEcl']; exact ⟨hyP, subset_closure (hIcc ⟨ht.1.le, ht.2.le.trans ht₀.2⟩)⟩
    have := hfirst (y, t) hq ht.2
    simp only at this
    linarith
  -- ordering at `t₀`
  have hat : ∀ y ∈ closure (posSet u U), y ∈ closure V → u y ≤ φ (y, t₀) := by
    intro y hyP hyV
    have hc : Continuous fun t ↦ φ (y, t) := hφs.continuous.comp (by fun_prop)
    exact ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset (Ioo_mem_nhdsLT hat₀) fun t ht ↦ (hbefore y hyP hyV t ht).le)
  have hφ₀ : φ (y₀, t₀) = u y₀ := le_antisymm (by linarith) (hat y₀ hy₀P hy₀V)
  -- time derivative
  have hdt : dₜ φ (y₀, t₀) ≤ 0 := by
    have hd : DifferentiableAt ℝ (fun s ↦ φ (y₀, s)) t₀ :=
      ((hφs.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) t₀
    exact deriv_nonpos_of_le_left hd hat₀ fun t ht ↦ by
      rw [hφ₀]; exact (hbefore y₀ hy₀P hy₀V t ht).le
  -- spatial touching
  set ψ : E d → ℝ := fun y ↦ φ (y, t₀) with hψ
  have hψs : ContDiff ℝ ∞ ψ := hφs.comp (contDiff_id.prodMk contDiff_const)
  have htouch : TouchesAbove (fun y ↦ max (ψ y) 0) u (closure (posSet u U) ∩ U) y₀ := by
    refine ⟨⟨hy₀P, hy₀U⟩, by simp only [hψ, hφ₀]; exact max_eq_left (hu.2.1 y₀ hy₀U), ?_⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hy₀), self_mem_nhdsWithin]
      with y hyV hyS
    exact (hat y hyS.1 (subset_closure hyV)).trans (le_max_left _ _)
  -- the strict supersolution inequalities at `(y₀, t₀)`, where `φ = u ≥ 0 > -a₀`
  have hmem : (y₀, t₀) ∈ closure V ×ˢ Icc a b := ⟨hy₀V, ht₀⟩
  have hφnn : 0 ≤ φ (y₀, t₀) := hφ₀ ▸ hu.2.1 y₀ hy₀U
  have hstrict := hφ.heat (y₀, t₀) ⟨show -a₀ < φ (y₀, t₀) by linarith [hφ.a₀_pos], hmem⟩
  rcases hu.2.2 ψ hψs y₀ htouch with hlap | ⟨hzero, hgrad⟩
  · have : lapₓ φ (y₀, t₀) = Δ ψ y₀ := rfl
    linarith [hφ.δ₀_pos]
  · -- `φ(y₀, t₀) = 0`, so `|∇φ|² ≤ (1 - δ₀) Q² < Q²`
    have hz : φ (y₀, t₀) = 0 := hzero
    have hg := hφ.grad (y₀, t₀) ⟨show |φ (y₀, t₀)| ≤ a₀ by rw [hz, abs_zero]; exact hφ.a₀_pos.le,
      hmem⟩
    have hgψ : gradₓ φ (y₀, t₀) = ∇ ψ y₀ := rfl
    rw [hgψ] at hg
    have hQ0 := hQ y₀ hy₀U
    have h2 : Q y₀ ^ 2 ≤ ‖∇ ψ y₀‖ ^ 2 := pow_le_pow_left₀ hQ0.le hgrad 2
    nlinarith [mul_pos hφ.δ₀_pos (pow_pos hQ0 2)]

/-- **[Remark 3.4](#AFS:r.statToPara)**, supersolution case ("similar" in the paper). A
viscosity supersolution of [(1.1)](#AFS:e.bernoulli-basic) in `U` is a (stationary) parabolic
viscosity supersolution of [(3.1)](#AFS:e.bernoulli-parabolic) in `U × I`. -/
theorem IsViscSuper.isParaSuper_const {U : Set (E d)} {Q u : E d → ℝ} (hu : IsViscSuper U Q u)
    (hQ : ∀ x ∈ U, 0 < Q x) (I : Set ℝ) : IsParaSuper U Q I (fun p ↦ u p.1) := by
  refine ⟨hu.1.comp continuousOn_fst fun p hp ↦ hp.1, fun p hp ↦ hu.2.1 p.1 hp.1, ?_⟩
  intro V a b φ hadm hφ hbd
  obtain ⟨hVo, hVb, hab, hVU⟩ := hadm
  obtain ⟨a₀, δ₀, hφ⟩ := hφ
  have hφs := hφ.contDiff
  have hEq : posSetP φ univ = {q | 0 < φ q} := by ext q; simp [posSetP]
  simp only [Prec, hEq] at hbd ⊢
  rintro p ⟨hpE, hpcyl⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hwc : ContinuousOn (fun q : E d × ℝ ↦ u q.1 - φ q) (closure V ×ˢ Icc a b) :=
    ((hu.1.comp continuousOn_fst fun q hq ↦ hq.1).mono hVU).sub hφs.continuous.continuousOn
  obtain ⟨⟨y₀, t₀⟩, ⟨hp₀E, hy₀V, ht₀⟩, hf₀, hfirst⟩ := exists_first_crossing hVb isClosed_closure
    hwc ⟨hpE, subset_closure hpcyl.1, Ioc_subset_Icc_self hpcyl.2⟩ (by simpa using hcon)
  simp only at hf₀ hfirst hy₀V ht₀
  have hnotbd : (y₀, t₀) ∉ parBdry V a b := fun h ↦ by
    have := hbd (y₀, t₀) ⟨hp₀E, h⟩
    simp only at this
    linarith
  have hat₀ : a < t₀ := lt_of_le_of_ne ht₀.1 fun h ↦ hnotbd (Or.inl ⟨hy₀V, h.symm⟩)
  have hy₀ : y₀ ∈ V := by
    by_contra hy
    exact hnotbd (Or.inr ⟨⟨hy₀V, fun h ↦ hy (hVo.interior_eq ▸ h)⟩, ht₀⟩)
  have hy₀U : y₀ ∈ U :=
    (hVU (show (y₀, t₀) ∈ closure V ×ˢ Icc a b from ⟨subset_closure hy₀, ht₀⟩)).1
  -- ordering before `t₀`, on `{φ > 0}`
  have hbefore : ∀ y ∈ closure V, ∀ t ∈ Ioo a t₀, 0 < φ (y, t) → φ (y, t) < u y := by
    intro y hyV t ht hpos
    have := hfirst (y, t) ⟨subset_closure hpos, hyV, ht.1.le, ht.2.le.trans ht₀.2⟩ ht.2
    simp only at this
    linarith
  -- ordering at `t₀`
  have hat : ∀ y ∈ closure V, φ (y, t₀) ≤ u y := by
    intro y hyV
    have hyU : y ∈ U := (hVU (show (y, t₀) ∈ closure V ×ˢ Icc a b from ⟨hyV, ht₀⟩)).1
    rcases le_or_gt (φ (y, t₀)) 0 with h0 | h0
    · exact h0.trans (hu.2.1 y hyU)
    · have hc : Continuous fun t ↦ φ (y, t) := hφs.continuous.comp (by fun_prop)
      have hev : ∀ᶠ t in 𝓝[<] t₀, 0 < φ (y, t) :=
        nhdsWithin_le_nhds (hc.continuousAt.eventually (lt_mem_nhds h0))
      refine le_of_tendsto (hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Iio t₀))) ?_
      filter_upwards [hev, Ioo_mem_nhdsLT hat₀] with t ht1 ht2
      exact (hbefore y hyV t ht2 ht1).le
  have hφ₀ : φ (y₀, t₀) = u y₀ := le_antisymm (hat y₀ hy₀V) (by linarith)
  -- time derivative
  have hdt : 0 ≤ dₜ φ (y₀, t₀) := by
    have hd : DifferentiableAt ℝ (fun s ↦ φ (y₀, s)) t₀ :=
      ((hφs.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) t₀
    refine deriv_nonneg_of_le_left hd hat₀ fun t ht ↦ ?_
    simp only [hφ₀]
    rcases le_or_gt (φ (y₀, t)) 0 with h0 | h0
    · exact h0.trans (hu.2.1 y₀ hy₀U)
    · exact (hbefore y₀ hy₀V t ht h0).le
  -- spatial touching
  set ψ : E d → ℝ := fun y ↦ φ (y, t₀) with hψ
  have hψs : ContDiff ℝ ∞ ψ := hφs.comp (contDiff_id.prodMk contDiff_const)
  have htouch : TouchesBelow ψ u U y₀ := by
    refine ⟨hy₀U, hφ₀, ?_⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hy₀)] with y hyV
    exact hat y (subset_closure hyV)
  -- the strict subsolution inequalities at `(y₀, t₀) ∈ \overline{{φ > 0}}`
  have hmem : (y₀, t₀) ∈ closure V ×ˢ Icc a b := ⟨hy₀V, ht₀⟩
  have hφnn : 0 ≤ φ (y₀, t₀) := closure_lt_subset_le continuous_const hφs.continuous hp₀E
  have hstrict := hφ.heat (y₀, t₀) ⟨show -a₀ < φ (y₀, t₀) by linarith [hφ.a₀_pos], hmem⟩
  rcases hu.2.2 ψ hψs y₀ hy₀U htouch with hlap | ⟨hzero, hgrad⟩
  · have : lapₓ φ (y₀, t₀) = Δ ψ y₀ := rfl
    linarith [hφ.δ₀_pos]
  · -- `φ(y₀, t₀) = 0`, so `|∇φ|² ≥ (1 + δ₀) Q² > Q²`
    have hz : φ (y₀, t₀) = 0 := hzero
    have hg := hφ.grad (y₀, t₀) ⟨show |φ (y₀, t₀)| ≤ a₀ by rw [hz, abs_zero]; exact hφ.a₀_pos.le,
      hmem⟩
    have hgψ : gradₓ φ (y₀, t₀) = ∇ ψ y₀ := rfl
    rw [hgψ] at hg
    have hQ0 := hQ y₀ hy₀U
    have h2 : ‖∇ ψ y₀‖ ^ 2 ≤ Q y₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgrad 2
    nlinarith [mul_pos hφ.δ₀_pos (pow_pos hQ0 2)]

/-! ### Time-independent lift of stationary strict barriers -/

section Lift

variable {V : Set (E d)} {Q g : E d → ℝ}

theorem dₜ_comp_fst (g : E d → ℝ) (p : E d × ℝ) : dₜ (fun q : E d × ℝ ↦ g q.1) p = 0 := by
  simp [dₜ]

theorem lapₓ_comp_fst (g : E d → ℝ) (p : E d × ℝ) :
    lapₓ (fun q : E d × ℝ ↦ g q.1) p = Δ g p.1 := rfl

theorem gradₓ_comp_fst (g : E d → ℝ) (p : E d × ℝ) :
    gradₓ (fun q : E d × ℝ ↦ g q.1) p = ∇ g p.1 := rfl

/-- **A stationary strict subsolution is a parabolic one** (the step "smooth strict subsolution of
[(1.1)](#AFS:e.bernoulli-basic) and hence also of [(3.1)](#AFS:e.bernoulli-parabolic)", used in the
proof of [Proposition 3.6](#AFS:p.monotone-nondegen-relaxed) for supersolutions). A smooth strict
subsolution `g` of [(1.1)](#AFS:e.bernoulli-basic) in `V` in the sense of
[Definition 2.3](#AFS:d.strict-sub) (`IsUnifStrictSub`), viewed as the time-independent function
`(x, t) ↦ g(x)`, is a classical strict subsolution of [(3.1)](#AFS:e.bernoulli-parabolic) on every
`V̄ × [a, b]`, with the same constants `a₀, δ₀`: `∂ₜ - Δ` becomes `-Δ` and the spatial gradient is
`∇g`. Smoothness of `g` is assumed, since [Definition 2.3](#AFS:d.strict-sub) only asks `g ∈ C²`
while the parabolic barriers are smooth. -/
theorem IsUnifStrictSub.isClassicalStrictParaSub (h : IsUnifStrictSub V Q g)
    (hg : ContDiff ℝ ∞ g) (a b : ℝ) :
    IsClassicalStrictParaSub Q (fun p ↦ g p.1) V a b := by
  obtain ⟨-, a₀, ha₀, δ₀, hδ₀, ha₀le, hδ₀le, h1, h2⟩ := h
  refine ⟨a₀, δ₀, hg.comp contDiff_fst, ha₀, ha₀le, hδ₀, hδ₀le, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rw [dₜ_comp_fst, lapₓ_comp_fst]
    linarith [h1 p.1 hp.2.1 hp.1]
  · rw [gradₓ_comp_fst]
    exact h2 p.1 hp.2.1 hp.1

/-- **A stationary strict supersolution is a parabolic one** (proof of
[Proposition 3.6](#AFS:p.monotone-nondegen-relaxed): "`h` is a smooth strict supersolution of
[(1.1)](#AFS:e.bernoulli-basic) and hence also of [(3.1)](#AFS:e.bernoulli-parabolic)"). A smooth
strict supersolution `g` of [(1.1)](#AFS:e.bernoulli-basic) in `V` in the sense of
[Definition 2.3](#AFS:d.strict-sub) (`IsUnifStrictSuper`), viewed as the time-independent function
`(x, t) ↦ g(x)`, is a classical strict supersolution of [(3.1)](#AFS:e.bernoulli-parabolic) on every
`V̄ × [a, b]`, with the same constants `a₀, δ₀`. As in `IsUnifStrictSub.isClassicalStrictParaSub`,
smoothness of `g` is assumed. -/
theorem IsUnifStrictSuper.isClassicalStrictParaSuper (h : IsUnifStrictSuper V Q g)
    (hg : ContDiff ℝ ∞ g) (a b : ℝ) :
    IsClassicalStrictParaSuper Q (fun p ↦ g p.1) V a b := by
  obtain ⟨-, a₀, ha₀, δ₀, hδ₀, ha₀le, hδ₀le, h1, h2⟩ := h
  refine ⟨a₀, δ₀, hg.comp contDiff_fst, ha₀, ha₀le, hδ₀, hδ₀le, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rw [dₜ_comp_fst, lapₓ_comp_fst]
    linarith [h1 p.1 hp.2.1 hp.1]
  · rw [gradₓ_comp_fst]
    exact h2 p.1 hp.2.1 hp.1

end Lift

end PerronVariational

end
