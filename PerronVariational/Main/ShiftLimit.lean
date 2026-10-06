/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import PerronVariational.Parabolic.LongTimeInnerViscosity
import PerronVariational.Registry.KriventsovWeiss
import PerronVariational.Stationary.Perron
import PerronVariational.Stationary.ViscosityJet

/-!
# Common steps of Propositions 6.1 and 6.2

Shared ingredients of the proofs of Propositions 6.1 and 6.2 of F. Abedin, W. M. Feldman,
K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase
problem*, arXiv:2609.14981:

* congruence of the stationary solution notions under `EqOn · · U`;
* `mem_nhdsSet_precOn`: strict ordering on a *neighbourhood* of a set from strict ordering at its
  points of the `≺`-set. The comparison principle (Theorem 3.6) needs `u ≺ v` on a neighbourhood
  of the parabolic boundary; the paper checks the ordering only on the parabolic boundary itself;
* time restriction of parabolic viscosity sub/supersolutions from `(0, ∞)` to `(0, T]`
  (`IsParaSuper.mono_time`, `IsParaSub.Ioc_of_Ioi`), needed to apply the comparison principle
  (Theorem 3.6) on `U × (0, T]`; for subsolutions this is not a formality, since `≺` is computed
  with `closure {u > 0}` taken in `U × I`, which changes at the top time;
* the `a → 0` limit of the shifted long-time limits via the compactness of inner variational
  solutions (Lemma 2.10, `exists_innerVar_limit`);
* the sandwich argument identifying the limit with Perron's solution (`eqOn_perronSmallest_of_le`,
  `eqOn_perronLargest_of_le`). It needs the boundary values of the limit, which the paper does
  not address; they are supplied as a one-sided modulus bound at `∂U`, obtained in
  Propositions 6.1/6.2 from the attainment modulus of Proposition A.8, which depends on the data
  only through its Lipschitz constant and sup norm and is therefore uniform over the shifts
  `g + a`. As a by-product Perron's solution is continuous on `Ū` (input of Lemma 2.7).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Congruence on `U` -/

section Congr

variable {U : Set (E d)} {Q u v : E d → ℝ}

theorem IsViscSuper.congr (h : IsViscSuper U Q u) (heq : EqOn u v U) : IsViscSuper U Q v := by
  refine ⟨h.1.congr fun x hx ↦ (heq hx).symm, fun x hx ↦ heq hx ▸ h.2.1 x hx, ?_⟩
  intro φ hφ x hx ht
  refine h.2.2 φ hφ x hx ⟨ht.1, ht.2.1.trans (heq ht.1).symm, ?_⟩
  filter_upwards [ht.2.2, self_mem_nhdsWithin] with y hy hyU
  exact (heq hyU).symm ▸ hy

theorem posSet_congr (heq : EqOn u v U) : posSet u U = posSet v U := by
  ext y
  simp only [posSet, Set.mem_ofPred_eq]
  exact ⟨fun h ↦ ⟨h.1, heq h.1 ▸ h.2⟩, fun h ↦ ⟨h.1, (heq h.1).symm ▸ h.2⟩⟩

theorem IsViscSub.congr (h : IsViscSub U Q u) (heq : EqOn u v U) : IsViscSub U Q v := by
  refine ⟨h.1.congr fun x hx ↦ (heq hx).symm, fun x hx ↦ heq hx ▸ h.2.1 x hx, ?_⟩
  intro φ hφ x ht
  rw [← posSet_congr heq] at ht
  refine h.2.2 φ hφ x ⟨ht.1, ht.2.1.trans (heq ht.1.2).symm, ?_⟩
  filter_upwards [ht.2.2, self_mem_nhdsWithin] with y hy hyU
  exact (heq hyU.2).symm ▸ hy

theorem IsInnerVarSolution.congr (hU : IsOpen U) {χ : E d → ℝ} (h : IsInnerVarSolution U Q u χ)
    (heq : EqOn u v U) : IsInnerVarSolution U Q v χ := by
  have hev : ∀ x ∈ U, u =ᶠ[𝓝 x] v := fun x hx ↦
    Filter.mem_of_superset (hU.mem_nhds hx) fun y hy ↦ heq hy
  have hgrad : ∀ x ∈ U, ∇ v x = ∇ u x := fun x hx ↦ (hev x hx).symm.gradient_eq
  refine ⟨fun x hx ↦ heq hx ▸ h.nonneg x hx, ?_, ?_, ?_, h.meas, h.zero_one, ?_, ?_⟩
  · intro x hx
    obtain ⟨K, t, ht, hK⟩ := h.locLip hx
    refine ⟨K, t ∩ U, inter_mem ht self_mem_nhdsWithin, fun y hy z hz ↦ ?_⟩
    rw [← heq hy.2, ← heq hz.2]
    exact hK hy.1 hz.1
  · rw [← posSet_congr heq]
    exact h.c2.congr fun x hx ↦ (heq hx.1).symm
  · intro x hx
    rw [← posSet_congr heq] at hx
    rw [(InnerProductSpace.laplacian_congr_nhds (hev x hx.1).symm).eq_of_nhds]
    exact h.harmonic x hx
  · filter_upwards [h.pos_le, ae_restrict_mem hU.measurableSet] with x hx hxU
    rw [← heq hxU]
    exact hx
  · intro ξ hξ hc hs
    rw [← h.stationary ξ hξ hc hs]
    refine setIntegral_congr_fun hU.measurableSet fun x hx ↦ ?_
    simp only [innerVarIntegrand, hgrad x hx]

end Congr

/-! ### Strict ordering on a neighbourhood -/

/-- If `f < h` at the points of `B` lying in the closed set `E ⊆ D`, and `f`, `h` are continuous on
`D`, then `{p | p ∈ E → f p < h p}` is a neighbourhood of `B`. (Points of `B \ E` have the open
neighbourhood `Eᶜ`.) Used to verify the hypothesis "`u ≺ v` on a neighbourhood of `∂_P`" of the
comparison principle (Theorem 3.6) in Propositions 6.1/6.2. -/
theorem mem_nhdsSet_precOn {X : Type*} [TopologicalSpace X] {f h : X → ℝ} {D Eset B : Set X}
    (hE : IsClosed Eset) (hED : Eset ⊆ D) (hf : ContinuousOn f D) (hh : ContinuousOn h D)
    (hB : ∀ p ∈ B ∩ Eset, f p < h p) : {p | p ∈ Eset → f p < h p} ∈ 𝓝ˢ B := by
  rw [mem_nhdsSet_iff_forall]
  intro p hp
  by_cases hpE : p ∈ Eset
  · have hlt : 0 < h p - f p := sub_pos.2 (hB p ⟨hp, hpE⟩)
    have hc : ContinuousWithinAt (fun q ↦ h q - f q) D p := (hh.sub hf) p (hED hpE)
    have hev : ∀ᶠ q in 𝓝[D] p, 0 < h q - f q := hc.eventually (lt_mem_nhds hlt)
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with q hq hqE
    exact sub_pos.1 (hq (hED hqE))
  · filter_upwards [hE.isOpen_compl.mem_nhds hpE] with q hq hqE using absurd hqE hq

/-! ### Time restriction of parabolic viscosity solutions -/

section TimeRestriction

variable {U : Set (E d)} {Q : E d → ℝ} {u : E d × ℝ → ℝ}

/-- Parabolic supersolutions restrict to smaller time sets (`≺` is computed with the positivity
set of the test function, independent of the time set). -/
theorem IsParaSuper.mono_time {I J : Set ℝ} (h : IsParaSuper U Q I u) (hJI : J ⊆ I) :
    IsParaSuper U Q J u :=
  ⟨h.1.mono (prod_mono subset_rfl hJI), fun p hp ↦ h.2.1 p ⟨hp.1, hJI hp.2⟩,
    fun V a b φ hadm hφ hbd ↦ h.2.2 V a b φ
      ⟨hadm.1, hadm.2.1, hadm.2.2.1, hadm.2.2.2.trans (prod_mono subset_rfl hJI)⟩ hφ hbd⟩

/-- The spatial gradient of a `C¹` space-time function is continuous. -/
theorem continuous_gradₓ {φ : E d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) : Continuous (gradₓ φ) := by
  have key : ∀ p : E d × ℝ, gradₓ φ p = (InnerProductSpace.toDual ℝ (E d)).symm
      ((fderiv ℝ φ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) := by
    intro p
    have h1 : HasFDerivAt (fun y : E d ↦ (y, p.2)) (ContinuousLinearMap.inl ℝ (E d) ℝ) p.1 :=
      hasFDerivAt_prodMk_left p.1 p.2
    have h2 : HasFDerivAt (fun y : E d ↦ φ (y, p.2))
        ((fderiv ℝ φ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) p.1 :=
      ((hφ.differentiable one_ne_zero) p).hasFDerivAt.comp p.1 h1
    simp only [gradₓ, gradient, h2.fderiv]
  rw [show gradₓ φ = _ from funext key]
  exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp
    ((hφ.continuous_fderiv one_ne_zero).clm_comp continuous_const)

/-- A continuous function which is positive on a compact set has a positive lower bound there. -/
theorem exists_pos_forall_le_of_isCompact {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ m > 0, ∀ x ∈ K, m ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun x hx ↦ hx.elim⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x₀, hpos x₀ hx₀, fun x hx ↦ hmin hx⟩

theorem IsClassicalStrictParaSuper.mono_top {φ : E d × ℝ → ℝ} {V : Set (E d)} {a b b' : ℝ}
    (h : IsClassicalStrictParaSuper Q φ V a b) (hb : b' ≤ b) :
    IsClassicalStrictParaSuper Q φ V a b' :=
  ⟨h.1, fun p hp ↦ h.2.1 p ⟨hp.1, hp.2.1, Icc_subset_Icc_right hb hp.2.2⟩,
    fun p hp ↦ h.2.2 p ⟨hp.1, hp.2.1, Icc_subset_Icc_right hb hp.2.2⟩⟩

theorem dₜ_sub_const (φ : E d × ℝ → ℝ) (η : ℝ) (p : E d × ℝ) :
    dₜ (fun q ↦ φ q - η) p = dₜ φ p := by
  simp [dₜ]

theorem lapₓ_sub_const {φ : E d × ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (η : ℝ) (p : E d × ℝ) :
    lapₓ (fun q ↦ φ q - η) p = lapₓ φ p := by
  have hs : ContDiff ℝ 2 fun y : E d ↦ φ (y, p.2) := hφ.comp (contDiff_id.prodMk contDiff_const)
  simp only [lapₓ, sub_eq_add_neg]
  exact laplacian_add_const hs.contDiffAt (-η)

theorem gradₓ_sub_const (φ : E d × ℝ → ℝ) (η : ℝ) (p : E d × ℝ) :
    gradₓ (fun q ↦ φ q - η) p = gradₓ φ p := by
  simp only [gradₓ, sub_eq_add_neg]
  exact gradient_add_const _ _ _

/-- A classical strict supersolution on a compact cylinder `V̄ × [a, b]` (`V̄ ⊆ U`, `Q` continuous
on `U`) stays one after subtracting a small positive constant. -/
theorem IsClassicalStrictParaSuper.sub_const (hQ : ContinuousOn Q U) {φ : E d × ℝ → ℝ}
    {V : Set (E d)} {a b : ℝ} (hVU : closure V ⊆ U) (hVb : Bornology.IsBounded V)
    (h : IsClassicalStrictParaSuper Q φ V a b) :
    ∃ m > 0, ∀ η, 0 < η → η < m → IsClassicalStrictParaSuper Q (fun p ↦ φ p - η) V a b := by
  have hφc : Continuous φ := h.1.continuous
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_of_smooth h.1
  have hφ1 : ContDiff ℝ 1 φ := hφ2.of_le one_le_two
  set K : Set (E d × ℝ) := closure V ×ˢ Icc a b with hKdef
  have hK : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hKc : IsClosed (K ∩ closure {q | 0 < φ q}) := hK.isClosed.inter isClosed_closure
  set A : Set (E d × ℝ) := (K ∩ closure {q | 0 < φ q}) ∩
    (fun p ↦ ‖gradₓ φ p‖ - Q p.1) ⁻¹' Ici 0 with hAdef
  have hAcl : IsClosed A := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ hKc isClosed_Ici
    exact (continuous_gradₓ hφ1).norm.continuousOn.sub
      (hQ.comp continuousOn_fst fun p hp ↦ hVU hp.1.1)
  have hA : IsCompact A := hK.of_isClosed_subset hAcl fun p hp ↦ hp.1.1
  have hopen : IsOpen {q | 0 < φ q} := isOpen_lt continuous_const hφc
  have hpos : ∀ p ∈ A, 0 < φ p := by
    intro p hp
    have h0 : 0 ≤ φ p := closure_lt_subset_le continuous_const hφc hp.1.2
    refine lt_of_le_of_ne h0 fun h0' ↦ ?_
    have hfr : p ∈ frontier {q | 0 < φ q} := by
      rw [hopen.frontier_eq]
      exact ⟨hp.1.2, fun hp' ↦ (lt_irrefl 0) (h0' ▸ hp' : (0 : ℝ) < 0)⟩
    have hlt := h.2.2 p ⟨hfr, hp.1.1⟩
    have hge : 0 ≤ ‖gradₓ φ p‖ - Q p.1 := hp.2
    linarith
  obtain ⟨m, hm, hmA⟩ := exists_pos_forall_le_of_isCompact hA hφc.continuousOn hpos
  refine ⟨m, hm, fun η hη hηm ↦ ⟨h.1.sub contDiff_const, ?_, ?_⟩⟩
  · intro p hp
    rw [dₜ_sub_const, lapₓ_sub_const hφ2]
    refine h.2.1 p ⟨closure_mono (fun q (hq : 0 < φ q - η) ↦ ?_) hp.1, hp.2⟩
    change 0 < φ q
    linarith
  · intro p hp
    rw [gradₓ_sub_const]
    have hset : {q | 0 < φ q - η} = {q | η < φ q} := by ext q; simp [sub_pos]
    rw [hset] at hp
    have hopen' : IsOpen {q | η < φ q} := isOpen_lt continuous_const hφc
    rw [hopen'.frontier_eq] at hp
    have hge : η ≤ φ p := closure_lt_subset_le continuous_const hφc hp.1.1
    have hle : φ p ≤ η := not_lt.1 hp.1.2
    have hφp : φ p = η := le_antisymm hle hge
    by_contra hcon
    have hpA : p ∈ A := by
      refine ⟨⟨hp.2, subset_closure (show 0 < φ p by linarith)⟩, ?_⟩
      change 0 ≤ ‖gradₓ φ p‖ - Q p.1
      linarith [not_lt.1 hcon]
    linarith [hmA p hpA]

/-- `p ∈ closure {u > 0}` does not depend on the domain `Ω` of `{u > 0}` near points of an open set
`W` on which the domains agree. -/
theorem mem_closure_posSetP_iff {Ω₁ Ω₂ W : Set (E d × ℝ)} (hW : IsOpen W)
    (h : Ω₁ ∩ W = Ω₂ ∩ W) {q : E d × ℝ} (hq : q ∈ W) :
    q ∈ closure (posSetP u Ω₁) ↔ q ∈ closure (posSetP u Ω₂) := by
  have hP : W ∩ posSetP u Ω₁ = W ∩ posSetP u Ω₂ := by
    ext p
    simp only [posSetP, mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpW, hp1, hpos⟩
      exact ⟨hpW, (h.subset ⟨hp1, hpW⟩).1, hpos⟩
    · rintro ⟨hpW, hp2, hpos⟩
      exact ⟨hpW, (h.symm.subset ⟨hp2, hpW⟩).1, hpos⟩
  constructor
  · intro h1
    have := hW.inter_closure ⟨hq, h1⟩
    rw [hP] at this
    exact closure_mono inter_subset_right this
  · intro h2
    have := hW.inter_closure ⟨hq, h2⟩
    rw [← hP] at this
    exact closure_mono inter_subset_right this

theorem parBdry_subset (V : Set (E d)) {a b : ℝ} (hab : a ≤ b) :
    parBdry V a b ⊆ closure V ×ˢ Icc a b := by
  rintro p (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
  · exact ⟨hp1, by rw [mem_singleton_iff.1 hp2]; exact ⟨le_rfl, hab⟩⟩
  · exact ⟨frontier_subset_closure hp1, hp2⟩

theorem isClosed_parBdry (V : Set (E d)) (a b : ℝ) : IsClosed (parBdry V a b) :=
  (isClosed_closure.prod isClosed_singleton).union (isClosed_frontier.prod isClosed_Icc)

theorem parBdry_mono_top (V : Set (E d)) {a b b' : ℝ} (hb : b' ≤ b) :
    parBdry V a b' ⊆ parBdry V a b := by
  rintro p (hp | ⟨hp1, hp2⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨hp1, Icc_subset_Icc_right hb hp2⟩

/-- A parabolic viscosity subsolution in `U × (0, ∞)` is one in `U × (0, T]`.

The relation `u ≺ φ` of Definition 3.2 is computed with `closure {u > 0}` taken inside `U × I`,
which for `I = (0, T]` and `I = (0, ∞)` differs at time `T`. Test cylinders ending before `T` are
handled directly; for a cylinder with top time `T` we subtract a small constant `η` from the strict
supersolution `φ` (`IsClassicalStrictParaSuper.sub_const`), compare on the cylinders `V × (a, b']`,
`b' < T`, and reach the top time by approximating positivity points from below in time (continuity
of `u`). -/
theorem IsParaSub.Ioc_of_Ioi (hU : IsOpen U) (hQ : ContinuousOn Q U) {T : ℝ}
    (h : IsParaSub U Q (Ioi 0) u) : IsParaSub U Q (Ioc 0 T) u := by
  have hIoc : U ×ˢ Ioc 0 T ⊆ U ×ˢ Ioi 0 := prod_mono subset_rfl Ioc_subset_Ioi_self
  refine ⟨h.1.mono hIoc, fun p hp ↦ h.2.1 p (hIoc hp), ?_⟩
  intro V a b φ hadm hφ hbd
  obtain ⟨hVo, hVb, hab, hVU⟩ := hadm
  rcases V.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · rintro p ⟨-, hp⟩
    exact absurd hp.1 (notMem_empty _)
  have ha0 : 0 < a :=
    (hVU (show (x₀, a) ∈ closure V ×ˢ Icc a b from ⟨subset_closure hx₀, le_rfl, hab.le⟩)).2.1
  have hbT : b ≤ T :=
    (hVU (show (x₀, b) ∈ closure V ×ˢ Icc a b from ⟨subset_closure hx₀, hab.le, le_rfl⟩)).2.2
  have hVU' : closure V ⊆ U := fun x hx ↦
    (hVU (show (x, a) ∈ closure V ×ˢ Icc a b from ⟨hx, le_rfl, hab.le⟩)).1
  set W : Set (E d × ℝ) := U ×ˢ Ioo 0 T with hWdef
  have hWo : IsOpen W := hU.prod isOpen_Ioo
  have hWD : U ×ˢ Ioc 0 T ∩ W = U ×ˢ Ioi 0 ∩ W := by
    rw [inter_eq_right.2 (Set.prod_mono subset_rfl Ioo_subset_Ioc_self),
      inter_eq_right.2 (Set.prod_mono subset_rfl Ioo_subset_Ioi_self)]
  -- points of `V̄ × [a, b']` with `b' < T` lie in `W`
  have hKW : ∀ b', b' < T → closure V ×ˢ Icc a b' ⊆ W := fun b' hb' q hq ↦
    ⟨hVU' hq.1, ha0.trans_le hq.2.1, hq.2.2.trans_lt hb'⟩
  have hcylK : ∀ b', cyl V a b' ⊆ closure V ×ˢ Icc a b' := fun b' q hq ↦
    ⟨subset_closure hq.1, hq.2.1.le, hq.2.2⟩
  -- direct comparison on cylinders ending before `T`
  have hdirect : ∀ (ψ : E d × ℝ → ℝ) (b' : ℝ), a < b' → b' ≤ b → b' < T →
      IsClassicalStrictParaSuper Q ψ V a b' →
      (∀ q ∈ closure (posSetP u (U ×ˢ Ioc 0 T)) ∩ parBdry V a b', u q < ψ q) →
      ∀ q ∈ closure (posSetP u (U ×ˢ Ioc 0 T)) ∩ cyl V a b', u q < ψ q := by
    intro ψ b' hab' hb'b hb'T hψ hψbd q hq
    have hadm : AdmissibleCyl U (Ioi 0) V a b' :=
      ⟨hVo, hVb, hab', fun r hr ↦ hIoc (hVU ⟨hr.1, hr.2.1, hr.2.2.trans hb'b⟩)⟩
    refine h.2.2 V a b' ψ hadm hψ (fun r hr ↦ hψbd r ⟨?_, hr.2⟩) q
      ⟨(mem_closure_posSetP_iff hWo hWD (hKW b' hb'T (hcylK b' hq.2))).1 hq.1, hq.2⟩
    exact (mem_closure_posSetP_iff hWo hWD
      (hKW b' hb'T (parBdry_subset V hab'.le hr.2))).2 hr.1
  rcases lt_or_eq_of_le hbT with hbT' | rfl
  · exact hdirect φ b hab le_rfl hbT' hφ hbd
  -- the top time of the cylinder is `T` (now called `b`)
  set Eset := closure (posSetP u (U ×ˢ Ioc 0 b)) with hEdef
  set K : Set (E d × ℝ) := closure V ×ˢ Icc a b with hKdef
  have hK : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have huK : ContinuousOn u K := h.1.mono fun q hq ↦ hIoc (hVU hq)
  have hφc : Continuous φ := hφ.1.continuous
  -- margin on the parabolic boundary
  have hBc : IsCompact (Eset ∩ parBdry V a b) :=
    hK.of_isClosed_subset (isClosed_closure.inter (isClosed_parBdry V a b))
      (inter_subset_right.trans (parBdry_subset V hab.le))
  obtain ⟨m₁, hm₁, hm₁'⟩ := exists_pos_forall_le_of_isCompact hBc (f := fun q ↦ φ q - u q)
    (hφc.continuousOn.sub (huK.mono (inter_subset_right.trans (parBdry_subset V hab.le))))
    fun q hq ↦ sub_pos.2 (hbd q hq)
  obtain ⟨m₂, hm₂, hsc⟩ := hφ.sub_const hQ hVU' hVb
  set η := min m₁ m₂ / 2 with hηdef
  have hη : 0 < η := by positivity
  have hη₁ : η < m₁ := by
    have := min_le_left m₁ m₂; rw [hηdef]; linarith
  have hη₂ : η < m₂ := by
    have := min_le_right m₁ m₂; rw [hηdef]; linarith
  have hψ := hsc η hη hη₂
  have hψbd : ∀ q ∈ Eset ∩ parBdry V a b, u q < φ q - η := fun q hq ↦ by
    have := hm₁' q hq; linarith
  -- comparison on `V × (a, b']`, `b' < b`
  have hstep : ∀ b' ∈ Ioo a b, ∀ q ∈ Eset ∩ cyl V a b', u q < φ q - η := by
    intro b' hb'
    exact hdirect (fun q ↦ φ q - η) b' hb'.1 hb'.2.le hb'.2 (hψ.mono_top hb'.2.le)
      fun q hq ↦ hψbd q ⟨hq.1, parBdry_mono_top V hb'.2.le hq.2⟩
  rintro p ⟨hpE, hpV, hpa, hpb⟩
  rcases lt_or_eq_of_le hpb with hpb' | hpb'
  · have := hstep p.2 ⟨hpa, hpb'⟩ p ⟨hpE, hpV, hpa, le_rfl⟩
    linarith
  -- `p` at the top time: approximate positivity points from below in time
  have hposW : posSetP u (U ×ˢ Ioc 0 b) ⊆ closure (posSetP u W) := by
    rintro q ⟨⟨hqU, hq0, hqb⟩, hqpos⟩
    have hcurve : Tendsto (fun s : ℝ ↦ (q.1, q.2 - s)) (𝓝[>] 0) (𝓝 q) := by
      have : Continuous fun s : ℝ ↦ (q.1, q.2 - s) :=
        continuous_const.prodMk (continuous_const.sub continuous_id)
      exact (this.tendsto' 0 q (by simp)).mono_left nhdsWithin_le_nhds
    have hin : ∀ᶠ s in 𝓝[>] (0 : ℝ), (q.1, q.2 - s) ∈ W := by
      filter_upwards [Ioo_mem_nhdsGT hq0] with s hs
      exact ⟨hqU, by simp only; linarith [hs.2], by simp only; linarith [hs.1]⟩
    have hcurve' : Tendsto (fun s : ℝ ↦ (q.1, q.2 - s)) (𝓝[>] 0) (𝓝[U ×ˢ Ioi 0] q) :=
      tendsto_nhdsWithin_iff.2 ⟨hcurve, hin.mono fun s hs ↦ ⟨hs.1, hs.2.1⟩⟩
    have hu : Tendsto (fun s : ℝ ↦ u (q.1, q.2 - s)) (𝓝[>] 0) (𝓝 (u q)) :=
      (h.1 q (hIoc ⟨hqU, hq0, hqb⟩)).tendsto.comp hcurve'
    refine mem_closure_of_tendsto hcurve ?_
    filter_upwards [hin, hu.eventually (lt_mem_nhds hqpos)] with s hs hs'
    exact ⟨hs, hs'⟩
  have hpW : p ∈ closure (posSetP u W) :=
    closure_minimal hposW isClosed_closure hpE
  have hO : IsOpen (V ×ˢ Ioi a) := hVo.prod isOpen_Ioi
  have hpO : p ∈ V ×ˢ Ioi a := ⟨hpV, hpa⟩
  have hp' : p ∈ closure (V ×ˢ Ioi a ∩ posSetP u W) := hO.inter_closure ⟨hpO, hpW⟩
  have hC : IsClosed (K ∩ (fun q ↦ u q - (φ q - η)) ⁻¹' Iic 0) :=
    (huK.sub (hφc.continuousOn.sub continuousOn_const)).preimage_isClosed_of_isClosed
      hK.isClosed isClosed_Iic
  have hsub : V ×ˢ Ioi a ∩ posSetP u W ⊆ K ∩ (fun q ↦ u q - (φ q - η)) ⁻¹' Iic 0 := by
    rintro q ⟨⟨hqV, hqa⟩, ⟨hqU, hq0, hqb⟩, hqpos⟩
    refine ⟨⟨subset_closure hqV, hqa.le, hqb.le⟩, ?_⟩
    have hqE : q ∈ Eset :=
      subset_closure ⟨⟨hqU, hq0, hqb.le⟩, hqpos⟩
    have := hstep q.2 ⟨hqa, hqb⟩ q ⟨hqE, hqV, hqa, le_rfl⟩
    change u q - (φ q - η) ≤ 0
    linarith
  have hple := (closure_minimal hsub hC hp').2
  simp only [mem_preimage, mem_Iic] at hple
  linarith

end TimeRestriction

/-! ### Uniform data bounds for the shifts `g + a`

Propositions 6.1/6.2 need the constants of the estimates to be uniform over the shifted data
`g + a`; the paper uses this without saying so. -/

/-- For `g ∈ C¹`, the energy bound `E₀ = ∫_U |∇g|² + Q_max² |U|` is finite. -/
theorem energyBound_ne_top (S : Setting d) {g : E d → ℝ} (hg : ContDiff ℝ 1 g) :
    energyBound S (∇ g) ≠ ⊤ := by
  obtain ⟨B, hB⟩ := S.isBounded.isCompact_closure.exists_bound_of_continuousOn
    (continuous_gradient hg).continuousOn
  refine (lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := B ^ 2 + S.Qmax ^ 2))
    (S.isBounded.measure_lt_top (μ := volume)))).ne
  rw [energyBound, ← setLIntegral_const]
  refine setLIntegral_mono' S.isOpen.measurableSet fun x hx ↦ ENNReal.ofReal_le_ofReal ?_
  have := hB x (subset_closure hx)
  gcongr

/-- The gradient is unchanged by adding a constant (as functions). -/
theorem gradient_add_const' (g : E d → ℝ) (a : ℝ) : ∇ (fun x ↦ g x + a) = ∇ g :=
  funext fun x ↦ gradient_add_const g x a

/-! ### The limit `a → 0` -/

/-- **The limit `a → 0`** (Propositions 6.1/6.2). A sequence of inner variational solutions
`(u k, χ k)` in `U` with `0 ≤ u k ≤ M`, the interior Lipschitz bound (3.14) with a common
constant `C` and the perimeter bound (3.15) with a common `CV` has a subsequence converging
locally uniformly in `U` to an inner variational solution. This is Lemma 2.10
(`Registry.innerVar_compactness`), whose hypotheses (a local `L^∞` bound, which the paper's
statement of Lemma 2.10 omits; equi-Lipschitz; perimeter bounds) follow from the uniform
bounds. -/
theorem exists_innerVar_limit (S : Setting d) {M C : ℝ} {CV : Set (E d) → ℝ}
    (u χ : ℕ → E d → ℝ) (hinner : ∀ k, IsInnerVarSolution S.U S.Q (u k) (χ k))
    (hbd : ∀ k, ∀ x ∈ S.U, 0 ≤ u k x ∧ u k x ≤ M)
    (hLip : ∀ k (x : E d) (r : ℝ), 0 < r → r ≤ 1 → ball x (2 * r) ⊆ S.U →
      ∀ M' : ℝ, (∀ y ∈ ball x (2 * r), |u k y| ≤ M') →
        ∀ y ∈ ball x r, ‖∇ (u k) y‖ ≤ C * (M' / r + 1))
    (hPer : ∀ k, ∀ V : Set (E d), CompactlyContained V S.U →
      totalVariationOn V (χ k) ≤ ENNReal.ofReal (CV V)) :
    ∃ (φ : ℕ → ℕ) (u₀ χ₀ : E d → ℝ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun j ↦ u (φ j)) u₀ atTop S.U ∧
      IsInnerVarSolution S.U S.Q u₀ χ₀ := by
  have hbdd : ∀ V, CompactlyContained V S.U → ∃ M : ℝ, ∀ k, ∀ x ∈ V, |u k x| ≤ M := by
    intro V hV
    refine ⟨M, fun k x hx ↦ ?_⟩
    have hxU := hV.2 (subset_closure hx)
    rw [abs_of_nonneg (hbd k x hxU).1]
    exact (hbd k x hxU).2
  have hLip' : ∀ V, CompactlyContained V S.U → ∃ L : ℝ, ∀ k, ∀ x ∈ V, ‖∇ (u k) x‖ ≤ L := by
    intro V hV
    obtain ⟨δ, hδ, hthick⟩ := hV.1.exists_thickening_subset_open S.isOpen hV.2
    set r := min 1 (δ / 2) with hrdef
    have hr : 0 < r := lt_min one_pos (half_pos hδ)
    refine ⟨C * (M / r + 1), fun k x hx ↦ ?_⟩
    have hball : ball x (2 * r) ⊆ S.U := by
      refine (ball_subset_ball ?_).trans
        ((Metric.ball_subset_thickening (subset_closure hx) δ).trans hthick)
      have := min_le_right 1 (δ / 2)
      linarith
    refine hLip k x r hr (min_le_left _ _) hball M (fun y hy ↦ ?_) x (mem_ball_self hr)
    rw [abs_of_nonneg (hbd k y (hball hy)).1]
    exact (hbd k y (hball hy)).2
  obtain ⟨φ, u₀, χ₀, hφ, hconv, -, -, hlim⟩ :=
    Registry.innerVar_compactness S.two_le S.isOpen S.lipschitzOn_U S.exists_pos_le_Q S.exists_Q_le
      u χ hinner hbdd hLip' fun V hV ↦ ⟨CV V, fun k ↦ hPer k V hV⟩
  exact ⟨φ, u₀, χ₀, hφ, hconv, hlim⟩

/-! ### The sandwich argument -/

/-- A function tending to `0` along `𝓝[≥] 0` is `< δ` on some `[0, r)`. -/
theorem exists_pos_forall_lt_of_tendsto_nhdsGE {ϖ : ℝ → ℝ} (hϖ : Tendsto ϖ (𝓝[≥] 0) (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) : ∃ r > 0, ∀ s, 0 ≤ s → s < r → ϖ s < δ := by
  obtain ⟨r, hr, h⟩ := Metric.mem_nhdsWithin_iff.1 (hϖ.eventually (gt_mem_nhds hδ))
  refine ⟨r, hr, fun s hs0 hsr ↦ h ⟨?_, hs0⟩⟩
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs0]
  exact hsr

/-- Near a boundary point `x₀`, eventually in `𝓝[closure U] x₀`, a point is either in `U` at
distance `< r` from `x₀`, or outside `U` (on `∂U`). -/
theorem eventually_nhdsWithin_closure_ball {U : Set (E d)} {x₀ : E d} {r : ℝ} (hr : 0 < r) :
    ∀ᶠ y in 𝓝[closure U] x₀, y ∈ closure U ∧ ‖y - x₀‖ < r := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds x₀ hr)] with y hy hy'
  exact ⟨hy, by rwa [mem_ball, dist_eq_norm] at hy'⟩

/-- **Sandwich, smallest case.** If `û` is a viscosity supersolution in `U` with `g₊ ≤ û ≤ v` in `U`
for every `v ∈ 𝒮_g`, and `û(x) ≤ g₊(x₀) + ϖ(|x - x₀|)` for `x ∈ U`, `x₀ ∈ ∂U`, with a modulus `ϖ`
(the boundary values, from the modulus of Proposition A.8 uniform over the shifts), then `û` is
Perron's smallest supersolution on `U`, and the latter is continuous on `Ū` (`û` extended by `g₊` to
`∂U` lies in `𝒮_g`). -/
theorem eqOn_perronSmallest_of_le (S : Setting d) {g û : E d → ℝ} (hg : Continuous g)
    (hsuper : IsViscSuper S.U S.Q û) (hlow : ∀ x ∈ S.U, max (g x) 0 ≤ û x)
    (hup : ∀ v ∈ perronSuperClass S.U S.Q g, ∀ x ∈ S.U, û x ≤ v x) {ϖ : ℝ → ℝ}
    (hϖ : Tendsto ϖ (𝓝[≥] 0) (𝓝 0))
    (hbdry : ∀ x ∈ S.U, ∀ x₀ ∈ frontier S.U, û x ≤ max (g x₀) 0 + ϖ ‖x - x₀‖) :
    EqOn (perronSmallest S.U S.Q g) û S.U ∧
      ContinuousOn (perronSmallest S.U S.Q g) (closure S.U) := by
  classical
  have hne := S.perronSuperClass_nonempty (g := g) hg.continuousOn
  have hgp : Continuous fun x ↦ max (g x) 0 := hg.max continuous_const
  set w := S.U.piecewise û (fun x ↦ max (g x) 0) with hwdef
  have hwU : EqOn û w S.U := fun x hx ↦ (piecewise_eq_of_mem _ _ _ hx).symm
  have hwlow : ∀ x ∈ closure S.U, max (g x) 0 ≤ w x := by
    intro x hx
    by_cases hxU : x ∈ S.U
    · rw [← hwU hxU]; exact hlow x hxU
    · rw [hwdef, piecewise_eq_of_notMem _ _ _ hxU]
  have hwup : ∀ v ∈ perronSuperClass S.U S.Q g, ∀ x ∈ closure S.U, w x ≤ v x := by
    intro v hv x hx
    by_cases hxU : x ∈ S.U
    · rw [← hwU hxU]; exact hup v hv x hxU
    · rw [hwdef, piecewise_eq_of_notMem _ _ _ hxU]; exact hv.2.2 x hx
  have hw : w ∈ perronSuperClass S.U S.Q g := by
    refine ⟨fun x hx ↦ ?_, hsuper.congr hwU, hwlow⟩
    by_cases hxU : x ∈ S.U
    · refine ContinuousAt.continuousWithinAt ?_
      refine (hsuper.1.continuousAt (S.isOpen.mem_nhds hxU)).congr ?_
      filter_upwards [S.isOpen.mem_nhds hxU] with y hy using hwU hy
    · have hfr : x ∈ frontier S.U := by rw [S.isOpen.frontier_eq]; exact ⟨hx, hxU⟩
      have hwx : w x = max (g x) 0 := by rw [hwdef, piecewise_eq_of_notMem _ _ _ hxU]
      rw [ContinuousWithinAt, hwx, tendsto_order]
      constructor
      · intro c hc
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (hgp.continuousAt.eventually (lt_mem_nhds hc))] with y hy hy'
        exact hy'.trans_le (hwlow y hy)
      · intro c hc
        obtain ⟨r, hr, hϖr⟩ := exists_pos_forall_lt_of_tendsto_nhdsGE hϖ (sub_pos.2 hc)
        filter_upwards [eventually_nhdsWithin_closure_ball (U := S.U) hr,
          nhdsWithin_le_nhds (hgp.continuousAt.eventually (gt_mem_nhds hc))] with y hy hy'
        by_cases hyU : y ∈ S.U
        · rw [← hwU hyU]
          have := hϖr _ (norm_nonneg _) hy.2
          linarith [hbdry y hyU x hfr]
        · rwa [hwdef, piecewise_eq_of_notMem _ _ _ hyU]
  have hEq : EqOn (perronSmallest S.U S.Q g) w (closure S.U) := fun x hx ↦
    le_antisymm (perronSmallest_le hw hx)
      (le_csInf (hne.image _) (by rintro _ ⟨v, hv, rfl⟩; exact hwup v hv x hx))
  exact ⟨fun x hx ↦ (hEq (subset_closure hx)).trans (hwU hx).symm, hw.1.congr hEq⟩

/-- **Sandwich, largest case.** If `û` is a viscosity subsolution in `U` with
`v ≤ û ≤ g₊` in `U` for every `v ∈ 𝒮^g`, and `g₊(x₀) - ϖ(|x - x₀|) ≤ û(x)` for `x ∈ U`,
`x₀ ∈ ∂U`, with a modulus `ϖ`, then `û` is Perron's largest subsolution on `U`, and the
latter is continuous on `Ū` (`û` extended by `g₊` to `∂U` lies in `𝒮^g`). -/
theorem eqOn_perronLargest_of_le (S : Setting d) {g û : E d → ℝ} (hg : Continuous g)
    (hsub : IsViscSub S.U S.Q û) (hup : ∀ x ∈ S.U, û x ≤ max (g x) 0)
    (hlow : ∀ v ∈ perronSubClass S.U S.Q g, ∀ x ∈ S.U, v x ≤ û x) {ϖ : ℝ → ℝ}
    (hϖ : Tendsto ϖ (𝓝[≥] 0) (𝓝 0))
    (hbdry : ∀ x ∈ S.U, ∀ x₀ ∈ frontier S.U, max (g x₀) 0 - ϖ ‖x - x₀‖ ≤ û x) :
    EqOn (perronLargest S.U S.Q g) û S.U ∧
      ContinuousOn (perronLargest S.U S.Q g) (closure S.U) := by
  classical
  have hne : (perronSubClass S.U S.Q g).Nonempty := ⟨0, zero_mem_perronSubClass _ _ _⟩
  have hgp : Continuous fun x ↦ max (g x) 0 := hg.max continuous_const
  set w := S.U.piecewise û (fun x ↦ max (g x) 0) with hwdef
  have hwU : EqOn û w S.U := fun x hx ↦ (piecewise_eq_of_mem _ _ _ hx).symm
  have hwup : ∀ x ∈ closure S.U, w x ≤ max (g x) 0 := by
    intro x hx
    by_cases hxU : x ∈ S.U
    · rw [← hwU hxU]; exact hup x hxU
    · rw [hwdef, piecewise_eq_of_notMem _ _ _ hxU]
  have hwlow : ∀ v ∈ perronSubClass S.U S.Q g, ∀ x ∈ closure S.U, v x ≤ w x := by
    intro v hv x hx
    by_cases hxU : x ∈ S.U
    · rw [← hwU hxU]; exact hlow v hv x hxU
    · rw [hwdef, piecewise_eq_of_notMem _ _ _ hxU]; exact hv.2.2 x hx
  have hw : w ∈ perronSubClass S.U S.Q g := by
    refine ⟨fun x hx ↦ ?_, hsub.congr hwU, hwup⟩
    by_cases hxU : x ∈ S.U
    · refine ContinuousAt.continuousWithinAt ?_
      refine (hsub.1.continuousAt (S.isOpen.mem_nhds hxU)).congr ?_
      filter_upwards [S.isOpen.mem_nhds hxU] with y hy using hwU hy
    · have hfr : x ∈ frontier S.U := by rw [S.isOpen.frontier_eq]; exact ⟨hx, hxU⟩
      have hwx : w x = max (g x) 0 := by rw [hwdef, piecewise_eq_of_notMem _ _ _ hxU]
      rw [ContinuousWithinAt, hwx, tendsto_order]
      constructor
      · intro c hc
        obtain ⟨r, hr, hϖr⟩ := exists_pos_forall_lt_of_tendsto_nhdsGE hϖ (sub_pos.2 hc)
        filter_upwards [eventually_nhdsWithin_closure_ball (U := S.U) hr,
          nhdsWithin_le_nhds (hgp.continuousAt.eventually (lt_mem_nhds hc))] with y hy hy'
        by_cases hyU : y ∈ S.U
        · rw [← hwU hyU]
          have := hϖr _ (norm_nonneg _) hy.2
          linarith [hbdry y hyU x hfr]
        · rwa [hwdef, piecewise_eq_of_notMem _ _ _ hyU]
      · intro c hc
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (hgp.continuousAt.eventually (gt_mem_nhds hc))] with y hy hy'
        exact (hwup y hy).trans_lt hy'
  have hEq : EqOn (perronLargest S.U S.Q g) w (closure S.U) := fun x hx ↦
    le_antisymm (csSup_le (hne.image _) (by rintro _ ⟨v, hv, rfl⟩; exact hwlow v hv x hx))
      (le_perronLargest hw hx)
  exact ⟨fun x hx ↦ (hEq (subset_closure hx)).trans (hwU hx).symm, hw.1.congr hEq⟩

end PerronVariational

end
