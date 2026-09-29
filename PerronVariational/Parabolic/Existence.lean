/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Semilinear.Attainment
import PerronVariational.Semilinear.Monotone
import PerronVariational.Topology.KLimit

/-!
# Theorem 3.9: existence for the parabolic problem (assembly)

**Theorem 3.9** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, is assembled, as in the
paper's proof, from the *statements* of
* Proposition 3.8 (`SemilinearWellposedStatement`): the well-prepared semilinear family;
* Proposition 4.1 (`EpsInnerLimitStatement`): the `ε → 0` limit is a parabolic inner variational
  solution with the estimates (3.11)–(3.13);
* Proposition 5.3 (`SemilinearLimitRelaxedStatement`): the limit is a relaxed viscosity solution;
* Corollary 5.4 (`SemilinearLimitIncreasingStatement`): in the increasing case it is a viscosity
  solution.

The ingredients not supplied by the statements, all proved here:
* `exists_isReactionProfile`: some `β` satisfying (3.5) exists (the paper fixes one);
* `exists_limit_extension`: the limit extends continuously to `Ū × [0, ∞)` (Proposition 3.8(v):
  a modulus of continuity uniform in `ε`, and density of `U_∞`); it attains `g₊` on `∂_P U_∞`;
* congruence lemmas: the properties (3.3), (3.11), (3.12) only see `u` on the open set `U_∞`;
* gluing lemmas: Proposition 5.3 and Corollary 5.4 are stated on `U × (0, T]`, Theorem 3.9 on
  `U × (0, ∞)`.

We also prove the strengthening `parabolic_existence_bdd_of`. It additionally exports the bound
`0 ≤ u ≤ M` on `Ū × [0, ∞)` (from (3.7)), and the modulus of continuity of Proposition A.8
(`exists_modulus`), which depends on `g` only through a Lipschitz constant `L` of `g` on `Ū` and
`M`, using the Lipschitz item of `IsWellPreparedFamily`. The paper's Theorem 3.9 states neither;
both are needed to get the boundary values of Perron's solutions in Propositions 6.1 and 6.2.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### A reaction profile -/

section ReactionProfile

/-- The unnormalized profile `s ↦ exp(-1/(s(1-s)))` on `(0, 1)`, `0` elsewhere. -/
noncomputable def bumpProfile (s : ℝ) : ℝ := expNegInvGlue (s * (1 - s))

theorem contDiff_bumpProfile : ContDiff ℝ ∞ bumpProfile :=
  (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_id.mul (contDiff_const.sub contDiff_id))

theorem bumpProfile_nonneg (s : ℝ) : 0 ≤ bumpProfile s := expNegInvGlue.nonneg _

theorem bumpProfile_pos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < bumpProfile s :=
  expNegInvGlue.pos_of_pos (mul_pos hs.1 (sub_pos.2 hs.2))

theorem bumpProfile_eq_zero {s : ℝ} (hs : s ∉ Ioo (0 : ℝ) 1) : bumpProfile s = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  simp only [mem_Ioo, not_and_or, not_lt] at hs
  rcases hs with hs | hs
  · exact mul_nonpos_of_nonpos_of_nonneg hs (by linarith)
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

theorem bumpProfile_monotoneOn : MonotoneOn bumpProfile (Icc 0 (1 / 2)) := by
  intro s hs t ht hst
  apply expNegInvGlue.monotone
  nlinarith [hs.1, hs.2, ht.1, ht.2]

theorem bumpProfile_antitoneOn : AntitoneOn bumpProfile (Icc (1 / 2) 1) := by
  intro s hs t ht hst
  apply expNegInvGlue.monotone
  nlinarith [hs.1, hs.2, ht.1, ht.2]

theorem hasCompactSupport_bumpProfile : HasCompactSupport bumpProfile := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc (0 : ℝ) 1) isCompact_Icc ?_
  intro s hs
  by_contra h
  exact hs (bumpProfile_eq_zero fun h' ↦ h (Ioo_subset_Icc_self h'))

theorem integrable_bumpProfile : Integrable bumpProfile :=
  contDiff_bumpProfile.continuous.integrable_of_hasCompactSupport hasCompactSupport_bumpProfile

theorem integral_bumpProfile_pos : 0 < ∫ s, bumpProfile s := by
  rw [integral_pos_iff_support_of_nonneg bumpProfile_nonneg integrable_bumpProfile]
  refine lt_of_lt_of_le ?_ (measure_mono fun s hs ↦ (bumpProfile_pos hs).ne')
  simp

/-- Some reaction profile `β` satisfying (3.5) exists: `β = b / (2 ∫ b)` with
`b(s) = exp(-1/(s(1-s)))` on `(0, 1)`. -/
theorem exists_isReactionProfile : ∃ β : ℝ → ℝ, IsReactionProfile β := by
  set c := ∫ s, bumpProfile s with hc
  have hc0 : 0 < c := integral_bumpProfile_pos
  refine ⟨fun s ↦ bumpProfile s / (2 * c), contDiff_bumpProfile.div_const _,
    fun s hs ↦ by simp [bumpProfile_eq_zero hs], fun s hs ↦ by
      have := bumpProfile_pos hs; positivity, ?_, ?_, ?_⟩
  · exact fun s hs t ht hst ↦ div_le_div_of_nonneg_right (bumpProfile_monotoneOn hs ht hst)
      (by positivity)
  · exact fun s hs t ht hst ↦ div_le_div_of_nonneg_right (bumpProfile_antitoneOn hs ht hst)
      (by positivity)
  · rw [integral_div, ← hc]
    field_simp

end ReactionProfile

/-! ### Extension of the limit to the closure -/

section Extension

variable {X : Type*} [PseudoMetricSpace X]

/-- A function tending to `0` along `𝓝[≥] 0` is `< δ` on some `[0, r)`. -/
theorem exists_pos_forall_lt_of_tendsto {ϖ : ℝ → ℝ} (hϖ : Tendsto ϖ (𝓝[≥] 0) (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) : ∃ r > 0, ∀ s, 0 ≤ s → s < r → ϖ s < δ := by
  obtain ⟨r, hr, h⟩ := Metric.mem_nhdsWithin_iff.1 (hϖ.eventually (gt_mem_nhds hδ))
  refine ⟨r, hr, fun s hs0 hsr ↦ h ⟨?_, hs0⟩⟩
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs0]
  exact hsr

/-- **Extension lemma** (the step "by Proposition 3.8(v), `u` extends to `C(Ū × [0, ∞))`" of the
proof of Theorem 3.9). Functions `v j` on `F` with a common modulus of continuity `ϖ` (w.r.t. a
gauge `ρ ≤ 2 dist`), converging pointwise on a dense subset `D ⊆ F`, converge pointwise on all of
`F` to a function that is continuous on `F` and agrees with the given limit on `D`. (No
Arzelà–Ascoli argument is needed: the sequence is pointwise Cauchy.) -/
theorem exists_limit_extension {F D : Set X} (hDF : D ⊆ F) (hFD : F ⊆ closure D)
    {v : ℕ → X → ℝ} {u : X → ℝ} (hconv : ∀ p ∈ D, Tendsto (fun j ↦ v j p) atTop (𝓝 (u p)))
    {ϖ : ℝ → ℝ} (hϖ : Tendsto ϖ (𝓝[≥] 0) (𝓝 0)) (ρ : X → X → ℝ) (hρ : ∀ p q, 0 ≤ ρ p q)
    (hρd : ∀ p q, ρ p q ≤ 2 * dist p q)
    (hmod : ∀ j, ∀ p ∈ F, ∀ q ∈ F, |v j p - v j q| ≤ ϖ (ρ p q)) :
    ∃ ũ : X → ℝ, (∀ p ∈ F, Tendsto (fun j ↦ v j p) atTop (𝓝 (ũ p))) ∧ EqOn ũ u D ∧
      ContinuousOn ũ F ∧ ∀ p ∈ F, ∀ q ∈ F, |ũ p - ũ q| ≤ ϖ (ρ p q) := by
  have hcauchy : ∀ p ∈ F, CauchySeq fun j ↦ v j p := by
    intro p hp
    rw [Metric.cauchySeq_iff']
    intro δ hδ
    obtain ⟨r, hr, hϖr⟩ := exists_pos_forall_lt_of_tendsto hϖ (by positivity : 0 < δ / 3)
    obtain ⟨q, hqD, hpq⟩ := Metric.mem_closure_iff.1 (hFD hp) (r / 2) (half_pos hr)
    have hρpq : ϖ (ρ p q) < δ / 3 := hϖr _ (hρ p q) (by linarith [hρd p q])
    have hρqp : ϖ (ρ q p) < δ / 3 :=
      hϖr _ (hρ q p) (by linarith [hρd q p, dist_comm p q])
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 (hconv q hqD).cauchySeq (δ / 3) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have h1 := hmod n p hp q (hDF hqD)
    have h2 := hN n hn
    have h3 := hmod N q (hDF hqD) p hp
    rw [Real.dist_eq] at h2 ⊢
    calc |v n p - v N p| ≤ |v n p - v n q| + |v n q - v N q| + |v N q - v N p| := by
          have := abs_sub_le (v n p) (v n q) (v N p)
          have := abs_sub_le (v n q) (v N q) (v N p)
          linarith
      _ < δ / 3 + δ / 3 + δ / 3 := by gcongr <;> linarith
      _ = δ := by ring
  set ũ : X → ℝ := fun p ↦ limUnder atTop fun j ↦ v j p with hũ
  have hlim : ∀ p ∈ F, Tendsto (fun j ↦ v j p) atTop (𝓝 (ũ p)) := fun p hp ↦
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy p hp))
  have hmodũ : ∀ p ∈ F, ∀ q ∈ F, |ũ p - ũ q| ≤ ϖ (ρ p q) := fun p hp q hq ↦
    le_of_tendsto' (((hlim p hp).sub (hlim q hq)).abs) fun j ↦ hmod j p hp q hq
  refine ⟨ũ, hlim, fun p hp ↦ (hconv p hp).limUnder_eq, ?_, hmodũ⟩
  rw [Metric.continuousOn_iff]
  intro p hp δ hδ
  obtain ⟨r, hr, hϖr⟩ := exists_pos_forall_lt_of_tendsto hϖ hδ
  refine ⟨r / 2, half_pos hr, fun q hq hqp ↦ ?_⟩
  rw [Real.dist_eq]
  exact (hmodũ q hq p hp).trans_lt (hϖr _ (hρ q p) (by linarith [hρd q p]))

end Extension

/-! ### Congruence: properties that only see `u` on `U_∞` -/

section Congr

variable {U : Set (E d)} {Q : E d → ℝ} {u u' w χ : E d × ℝ → ℝ}

theorem isOpen_UInf (hU : IsOpen U) : IsOpen (UInf U) := hU.prod isOpen_Ioi

theorem gradₓ_congr (hU : IsOpen U) (heq : EqOn u u' (UInf U)) {p : E d × ℝ}
    (hp : p ∈ UInf U) : gradₓ u p = gradₓ u' p := by
  unfold gradₓ
  refine Filter.EventuallyEq.gradient_eq ?_
  filter_upwards [hU.mem_nhds hp.1] with y hy
  exact heq ⟨hy, hp.2⟩

theorem paraInnerVarIntegrand_congr (hU : IsOpen U) (heq : EqOn u u' (UInf U))
    (ξ : E d × ℝ → E d) : EqOn (paraInnerVarIntegrand Q u w χ ξ)
      (paraInnerVarIntegrand Q u' w χ ξ) (UInf U) := by
  intro p hp
  simp only [paraInnerVarIntegrand, gradₓ_congr hU heq hp]

theorem IsParaInnerVarSolution.congr (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (heq : EqOn u u' (UInf U)) : IsParaInnerVarSolution U Q u' w χ := by
  have hO := isOpen_UInf hU
  have hM := hO.measurableSet
  have hlip : ∀ p ∈ UInf U, ∃ K : ℝ, ∃ N ∈ 𝓝 p, ∀ q ∈ N, ∀ q' ∈ N, q.2 = q'.2 →
      |u' q - u' q'| ≤ K * ‖q.1 - q'.1‖ := by
    intro p hp
    obtain ⟨K, N, hN, hK⟩ := h.locLipₓ p hp
    refine ⟨K, N ∩ UInf U, inter_mem hN (hO.mem_nhds hp), fun q hq q' hq' ht ↦ ?_⟩
    rw [← heq hq.2, ← heq hq'.2]
    exact hK q hq.1 q' hq'.1 ht
  have htd : HasWeakTimeDeriv (UInf U) u' w := by
    refine ⟨h.timeDeriv.1.congr ((ae_restrict_mem hM).mono fun p hp ↦ heq hp),
      h.timeDeriv.2.1, fun ψ hψ hψc hψs ↦ ?_⟩
    rw [← h.timeDeriv.2.2 ψ hψ hψc hψs]
    exact setIntegral_congr_fun hM fun p hp ↦ by simp only [heq hp]
  have hpos : ∀ᵐ p ∂(volume.restrict (UInf U)), 0 < u' p → χ p = 1 := by
    filter_upwards [h.pos_le, ae_restrict_mem hM] with p h1 h2 hp
    exact h1 (by rwa [heq h2])
  exact
    { continuousOn := h.continuousOn.congr fun p hp ↦ (heq hp).symm
      nonneg := fun p hp ↦ heq hp ▸ h.nonneg p hp
      locLipₓ := hlip
      timeDeriv := htd
      timeDeriv_memL2 := h.timeDeriv_memL2
      meas := h.meas
      zero_one := h.zero_one
      pos_le := hpos
      integrable := fun ξ hξ hξc hξs ↦
        IntegrableOn.congr_fun (h.integrable ξ hξ hξc hξs) (paraInnerVarIntegrand_congr hU heq ξ) hM
      stationary := fun ξ hξ hξc hξs ↦ by
        rw [← setIntegral_congr_fun hM (paraInnerVarIntegrand_congr hU heq ξ)]
        exact h.stationary ξ hξ hξc hξs }

/-- The weak heat equation (4.5) in `{u > 0}` only sees `u` on `U_∞`. -/
theorem WeakHeatInPos.congr (hU : IsOpen U) (h : WeakHeatInPos U u w)
    (heq : EqOn u u' (UInf U)) : WeakHeatInPos U u' w := by
  intro φ hφ hc hsupp
  have hpos : posSetP u' (UInf U) = posSetP u (UInf U) := by
    ext p; simp only [posSetP, mem_setOf_eq]
    exact ⟨fun ⟨hp, h⟩ ↦ ⟨hp, (heq hp) ▸ h⟩, fun ⟨hp, h⟩ ↦ ⟨hp, (heq hp).symm ▸ h⟩⟩
  rw [h φ hφ hc (hpos ▸ hsupp)]
  congr 1
  refine setIntegral_congr_fun (isOpen_UInf hU).measurableSet fun p hp ↦ ?_
  simp only [gradₓ_congr hU heq hp]

theorem DissipationIneq.congr (hU : IsOpen U) {E0 : ℝ≥0∞} (h : DissipationIneq U Q u w χ E0)
    (heq : EqOn u u' (UInf U)) : DissipationIneq U Q u' w χ E0 := by
  unfold DissipationIneq at h ⊢
  filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with T hT hT0
  have : energyJχ U Q (fun x ↦ gradₓ u' (x, T)) (fun x ↦ χ (x, T)) =
      energyJχ U Q (fun x ↦ gradₓ u (x, T)) (fun x ↦ χ (x, T)) := by
    unfold energyJχ
    exact setLIntegral_congr_fun hU.measurableSet fun x hx ↦ by
      simp only [gradₓ_congr hU heq (show (x, T) ∈ UInf U from ⟨hx, hT0⟩)]
  rwa [this]

theorem DissipationIneq.mono {E0 E1 : ℝ≥0∞} (h : DissipationIneq U Q u w χ E0) (hE : E0 ≤ E1) :
    DissipationIneq U Q u w χ E1 := by
  unfold DissipationIneq at h ⊢
  filter_upwards [h] with T hT
  exact hT.trans (ENNReal.div_le_div_right hE 2)

theorem parCyl_subset_two {x : E d} {t r : ℝ} (hr : 0 < r) : parCyl x t r ⊆ parCyl x t (2 * r) :=
  prod_mono (ball_subset_ball (by linarith)) (Ioc_subset_Ioc_left (by nlinarith))

theorem InteriorLipEst.congr (hU : IsOpen U) {C : ℝ} (h : InteriorLipEst U u C)
    (heq : EqOn u u' (UInf U)) : InteriorLipEst U u' C := by
  intro x t r hr hr1 hcyl M hM p hp
  rw [← gradₓ_congr hU heq (hcyl (parCyl_subset_two hr hp))]
  exact h x t r hr hr1 hcyl M (fun q hq ↦ by rw [heq (hcyl hq)]; exact hM q hq) p hp

end Congr

/-! ### Gluing `(0, T]` statements to `(0, ∞)` -/

section Glue

variable {U : Set (E d)} {Q : E d → ℝ} {u : E d × ℝ → ℝ}

theorem AdmissibleCyl.Ioc_of_Ioi {V : Set (E d)} {a b T : ℝ} (h : AdmissibleCyl U (Ioi 0) V a b)
    (hbT : b ≤ T) : AdmissibleCyl U (Ioc 0 T) V a b :=
  ⟨h.1, h.2.1, h.2.2.1, fun _ hp ↦ ⟨(h.2.2.2 hp).1, (h.2.2.2 hp).2, hp.2.2.trans hbT⟩⟩

theorem mem_cyl_snd_le {V : Set (E d)} {a b : ℝ} {p : E d × ℝ} (hp : p ∈ cyl V a b) : p.2 ≤ b :=
  hp.2.2

theorem isOpen_snd_lt (T : ℝ) : IsOpen {p : E d × ℝ | p.2 < T} :=
  isOpen_Iio.preimage continuous_snd

/-- Gluing of parabolic viscosity supersolutions. -/
theorem isParaSuper_Ioi_of_Ioc (hcont : ContinuousOn u (U ×ˢ Ioi 0))
    (hnn : ∀ p ∈ U ×ˢ Ioi 0, 0 ≤ u p) (h : ∀ T > 0, IsParaSuper U Q (Ioc 0 T) u) :
    IsParaSuper U Q (Ioi 0) u := by
  refine ⟨hcont, hnn, fun V a b φ hadm hφ hprec ↦ ?_⟩
  have hT : 0 < max b 0 + 1 := by positivity
  exact (h _ hT).2.2 V a b φ (hadm.Ioc_of_Ioi (by linarith [le_max_left b 0])) hφ hprec

/-- Gluing of parabolic viscosity subsolutions. The ordering `u ≺ φ` uses `closure {u > 0}`
taken in `U × I`, which depends on `I` near the top time, so the `(0, T]` statement is used with
`T > b` for a test cylinder `V × (a, b]`. -/
theorem isParaSub_Ioi_of_Ioc (hcont : ContinuousOn u (U ×ˢ Ioi 0))
    (hnn : ∀ p ∈ U ×ˢ Ioi 0, 0 ≤ u p) (h : ∀ T > 0, IsParaSub U Q (Ioc 0 T) u) :
    IsParaSub U Q (Ioi 0) u := by
  refine ⟨hcont, hnn, fun V a b φ hadm hφ hprec ↦ ?_⟩
  set T := max b 0 + 1 with hT_def
  have hT : 0 < T := by positivity
  have hbT : b < T := by linarith [le_max_left b 0]
  have hsubset : posSetP u (U ×ˢ Ioc 0 T) ⊆ posSetP u (U ×ˢ Ioi 0) :=
    fun p hp ↦ ⟨⟨hp.1.1, hp.1.2.1⟩, hp.2⟩
  have key := (h T hT).2.2 V a b φ (hadm.Ioc_of_Ioi hbT.le) hφ
    (fun p hp ↦ hprec p ⟨closure_mono hsubset hp.1, hp.2⟩)
  intro p hp
  refine key p ⟨?_, hp.2⟩
  have hpO : p ∈ {q : E d × ℝ | q.2 < T} := (mem_cyl_snd_le hp.2).trans_lt hbT
  refine closure_mono ?_ ((isOpen_snd_lt T).inter_closure ⟨hpO, hp.1⟩)
  rintro q ⟨hqT, ⟨hqU, hq0⟩, hqpos⟩
  exact ⟨⟨hqU, hq0, le_of_lt hqT⟩, hqpos⟩

theorem isParaSolution_Ioi_of_Ioc (hcont : ContinuousOn u (U ×ˢ Ioi 0))
    (hnn : ∀ p ∈ U ×ˢ Ioi 0, 0 ≤ u p) (h : ∀ T > 0, IsParaSolution U Q (Ioc 0 T) u) :
    IsParaSolution U Q (Ioi 0) u :=
  ⟨isParaSuper_Ioi_of_Ioc hcont hnn fun T hT ↦ (h T hT).1,
    isParaSub_Ioi_of_Ioc hcont hnn fun T hT ↦ (h T hT).2⟩

/-- Gluing of parabolic relaxed subsolutions, for sets `E T` (on `U × (0, T]`) and `E∞`
(on `U × (0, ∞)`) with `E T ⊆ E∞` and `E∞ ∩ {t < T} ⊆ E T`. -/
theorem isParaRelaxedSub_Ioi_of_Ioc {Et : ℝ → Set (E d × ℝ)} {Einf : Set (E d × ℝ)}
    (hcont : ContinuousOn u (U ×ˢ Ioi 0)) (hnn : ∀ p ∈ U ×ˢ Ioi 0, 0 ≤ u p)
    (hclosed : IsClosed Einf) (hsub : Einf ⊆ closure U ×ˢ closure (Ioi 0))
    (hle : ∀ T > 0, Et T ⊆ Einf) (hge : ∀ T > 0, Einf ∩ {p | p.2 < T} ⊆ Et T)
    (h : ∀ T > 0, IsParaRelaxedSub U Q (Ioc 0 T) u (Et T)) :
    IsParaRelaxedSub U Q (Ioi 0) u Einf := by
  refine ⟨hcont, hnn, hclosed, hsub, ?_, fun V a b φ hadm hφ hprec ↦ ?_⟩
  · rintro p ⟨⟨hpU, hp0⟩, hpos⟩
    have hT : (0 : ℝ) < p.2 + 1 := by linarith [mem_Ioi.1 hp0]
    exact hle _ hT ((h _ hT).2.2.2.2.1 ⟨⟨hpU, hp0, by linarith⟩, hpos⟩)
  · set T := max b 0 + 1 with hT_def
    have hT : 0 < T := by positivity
    have hbT : b < T := by linarith [le_max_left b 0]
    have key := (h T hT).2.2.2.2.2 V a b φ (hadm.Ioc_of_Ioi hbT.le) hφ
      (fun p hp ↦ hprec p ⟨hle T hT hp.1, hp.2⟩)
    intro p hp
    exact key p ⟨hge T hT ⟨hp.1, (mem_cyl_snd_le hp.2).trans_lt hbT⟩, hp.2⟩

theorem closure_Ioi_inter_subset (T : ℝ) :
    closure (U ×ˢ Ioi (0 : ℝ)) ∩ {p | p.2 < T} ⊆ closure (U ×ˢ Ioc 0 T) := by
  rintro p ⟨hp, hpT⟩
  refine closure_mono ?_ ((isOpen_snd_lt T).inter_closure ⟨hpT, hp⟩)
  rintro q ⟨hqT, hqU, hq0⟩
  exact ⟨hqU, hq0, le_of_lt hqT⟩

theorem semilinearLimitSet_Ioc_subset (εs : ℕ → ℝ) (us : ℕ → E d × ℝ → ℝ) (T : ℝ) :
    semilinearLimitSet U (Ioc 0 T) εs us ⊆ semilinearLimitSet U (Ioi 0) εs us :=
  upperKLimit_mono fun _ _ hp ↦ ⟨⟨hp.1.1, hp.1.2.1⟩, hp.2⟩

theorem semilinearLimitSet_Ioi_inter_subset (εs : ℕ → ℝ) (us : ℕ → E d × ℝ → ℝ) (T : ℝ) :
    semilinearLimitSet U (Ioi 0) εs us ∩ {p | p.2 < T} ⊆ semilinearLimitSet U (Ioc 0 T) εs us := by
  rintro p ⟨hp, hpT⟩ N hN
  refine (hp (N ∩ {q | q.2 < T}) (inter_mem hN ((isOpen_snd_lt T).mem_nhds hpT))).mono ?_
  rintro j ⟨q, ⟨⟨hqU, hq0⟩, hq⟩, hqN, hqT⟩
  exact ⟨q, ⟨⟨hqU, hq0, le_of_lt hqT⟩, hq⟩, hqN⟩

theorem semilinearLimitSet_subset_closure (εs : ℕ → ℝ) (us : ℕ → E d × ℝ → ℝ) (I : Set ℝ) :
    semilinearLimitSet U I εs us ⊆ closure U ×ˢ closure I :=
  upperKLimit_subset_of_eventually (isClosed_closure.prod isClosed_closure)
    (Eventually.of_forall fun _ _ hp ↦ ⟨subset_closure hp.1.1, subset_closure hp.1.2⟩)


end Glue

/-! ### Theorem 3.9 -/

/-- **Theorem 3.9** as in `ParabolicExistenceStatement`, with the additional export `0 ≤ u ≤ M` on
`Ū × [0, ∞)` (the bound (3.7) of Proposition 3.8 passed to the limit), which the applications
(Lemma 5.8, and Theorem 3.10 in Propositions 6.1 and 6.2) need and which
`ParabolicExistenceStatement` does not contain.

It also exports the modulus of continuity `ϖ` of Proposition 3.8(v) / Proposition A.8 on
`Ū × [0, ∞)`, which depends on `g` only through a Lipschitz constant `L` of `g` on `Ū` and the
sup bound `M` (so `ϖ` is chosen after `L` and before `g`). The paper's Theorem 3.9 exports no
modulus, and the paper does not note this uniformity. Propositions 6.1 and 6.2 use it, uniformly
over the shifts `g + a`, to get the boundary values of Perron's solutions, which the paper does
not check. -/
def ParabolicExistenceBddStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d), ∃ C : ℝ, ∀ (M : ℝ) (E0 : ℝ≥0∞), E0 ≠ ⊤ → ∃ Cper : ℝ → ℝ → ℝ,
    ∀ L : ℝ≥0, ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
    ∀ g : E d → ℝ, (∀ x ∈ S.U, |g x| ≤ M) → energyBound S (∇ g) ≤ E0 →
      LipschitzOnWith L g (closure S.U) →
      (IsStrictSub S.U S.Q g → ∃ u w χ : E d × ℝ → ℝ,
        ParabolicExistenceCommon S g C Cper u w χ ∧ MonotoneInTime u (closure S.U) (Ici 0) ∧
          IsParaSolution S.U S.Q (Ioi 0) u ∧
          (∀ K : Set (E d), IsCompact K → K ⊆ closure S.U \ closure (posSet g (closure S.U)) →
            ∃ τ > 0, ∀ x ∈ K, ∀ t ∈ Icc 0 τ, u (x, t) = 0) ∧
          (∀ p ∈ closure S.U ×ˢ Ici 0, 0 ≤ u p ∧ u p ≤ M) ∧
          ∀ p ∈ closure S.U ×ˢ Ici 0, ∀ q ∈ closure S.U ×ˢ Ici 0,
            |u p - u q| ≤ ϖ (‖p.1 - q.1‖ + |p.2 - q.2|)) ∧
      (IsStrictSuper S.U S.Q g → ∃ u w χ : E d × ℝ → ℝ,
        ParabolicExistenceCommon S g C Cper u w χ ∧ AntitoneInTime u (closure S.U) (Ici 0) ∧
          (∃ Eset : Set (E d × ℝ), IsParaRelaxedSolution S.U S.Q (Ioi 0) u Eset) ∧
          (∀ p ∈ closure S.U ×ˢ Ici 0, 0 ≤ u p ∧ u p ≤ M) ∧
          ∀ p ∈ closure S.U ×ˢ Ici 0, ∀ q ∈ closure S.U ×ˢ Ici 0,
            |u p - u q| ≤ ϖ (‖p.1 - q.1‖ + |p.2 - q.2|))

theorem energyBound_indicator_le (S : Setting d) (g : E d → ℝ) :
    energyBound S ({x | 0 < g x}.indicator (∇ g)) ≤ energyBound S (∇ g) := by
  unfold energyBound
  refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_
  gcongr
  exact norm_indicator_le_norm_self _ _

/-- The gauge `‖x - y‖ + |s - t|` of Proposition 3.8(v) is at most twice the (sup) distance. -/
theorem norm_add_abs_le_two_mul_dist (p q : E d × ℝ) :
    ‖p.1 - q.1‖ + |p.2 - q.2| ≤ 2 * dist p q := by
  rw [Prod.dist_eq, ← dist_eq_norm, ← Real.dist_eq]
  linarith [le_max_left (dist p.1 q.1) (dist p.2 q.2), le_max_right (dist p.1 q.1) (dist p.2 q.2)]

/-- **Theorem 3.9** with the bound `0 ≤ u ≤ M` and the uniform modulus, from Propositions 3.8,
4.1, 5.3 and Corollary 5.4 (as statements), following the paper's proof. -/
theorem parabolic_existence_bdd_of (h37 : SemilinearWellposedStatement)
    (h41 : EpsInnerLimitStatement) (h53 : SemilinearLimitRelaxedStatement)
    (h54 : SemilinearLimitIncreasingStatement) : ParabolicExistenceBddStatement := by
  intro d S
  obtain ⟨β, hβ⟩ := exists_isReactionProfile
  obtain ⟨C, hC⟩ := h41 d S β hβ
  refine ⟨C, fun M E0 hE0 ↦ ?_⟩
  obtain ⟨Cper, hCper⟩ := hC (M + 1) E0 hE0
  refine ⟨Cper, fun L ↦ ?_⟩
  -- the modulus of Proposition A.8, depending on the data only through `L` and `M + 1`
  obtain ⟨ϖ, hϖ, hmodA⟩ := exists_modulus S hβ L (M + 1)
  refine ⟨ϖ, hϖ, fun g hgM hgE hgL ↦ ?_⟩
  have hgMcl : ∀ x ∈ closure S.U, |g x| ≤ M := fun x hx ↦
    ContinuousWithinAt.closure_le hx ((hgL.continuousOn x hx).mono subset_closure).abs
      continuousWithinAt_const hgM
  -- the `ε → 0` limit along the subsequence of Proposition 4.1, extended to `Ū × [0, ∞)`
  have key : ∀ (b : Bool) (ε₀ : ℝ) (gε : ℝ → E d → ℝ) (uε : ℝ → E d × ℝ → ℝ),
      IsWellPreparedFamily S g β b ε₀ gε uε → ∃ (εs : ℕ → ℝ) (u w χ : E d × ℝ → ℝ),
        (∀ j, εs j ∈ Ioo 0 ε₀) ∧ Tendsto εs atTop (𝓝 0) ∧
        TendstoLocallyUniformlyOn (fun j ↦ uε (εs j)) u atTop (UInf S.U) ∧
        (∀ p ∈ closure S.U ×ˢ Ici 0, Tendsto (fun j ↦ uε (εs j) p) atTop (𝓝 (u p))) ∧
        ParabolicExistenceCommon S g C Cper u w χ ∧
        (∀ p ∈ closure S.U ×ˢ Ici 0, 0 ≤ u p ∧ u p ≤ M) ∧
        ∀ p ∈ closure S.U ×ˢ Ici 0, ∀ q ∈ closure S.U ×ˢ Ici 0,
          |u p - u q| ≤ ϖ (‖p.1 - q.1‖ + |p.2 - q.2|) := by
    intro b ε₀ gε uε hfam
    obtain ⟨hε₀, hfamε, hgpH1, hH1conv, -, -, -, -⟩ := hfam
    have hε₀' : 0 < min ε₀ 1 := lt_min hε₀ one_pos
    have hsubε : ∀ ε ∈ Ioo 0 (min ε₀ 1), ε ∈ Ioo 0 ε₀ :=
      fun ε hε ↦ ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
    have hGg := energyBound_indicator_le S g
    have hgε : ∀ ε ∈ Ioo 0 (min ε₀ 1), ∀ x ∈ S.U, 0 ≤ gε ε x ∧ gε ε x ≤ M + 1 := by
      intro ε hε x hx
      have hb := (hfamε ε (hsubε ε hε)).2.2.1 x (subset_closure hx)
      have hε1 : ε < 1 := hε.2.trans_le (min_le_right _ _)
      have hmax : max (g x) 0 ≤ M :=
        max_le ((le_abs_self _).trans (hgM x hx)) ((abs_nonneg _).trans (hgM x hx))
      exact ⟨(le_max_right _ _).trans hb.1, by linarith [hb.2]⟩
    obtain ⟨εs, u, w, χ, hεs, -, hεs0, hloc, -, -, -, -, hinner, hheat, hdiss, hlip, hper⟩ :=
      hCper (min ε₀ 1) (fun x ↦ max (g x) 0) ({x | 0 < g x}.indicator (∇ g)) gε
        (fun ε ↦ ∇ (gε ε)) uε hε₀' hgpH1 (fun ε hε ↦ (hfamε ε (hsubε ε hε)).2.2.2.2.1)
        hH1conv hgε (hGg.trans hgE) (fun ε hε ↦ (hfamε ε (hsubε ε hε)).1)
    have hεs' : ∀ j, εs j ∈ Ioo 0 ε₀ := fun j ↦ hsubε _ (hεs j)
    -- the uniform modulus (Proposition A.8)
    have hmod : ∀ ε ∈ Ioo 0 (min ε₀ 1), ∀ p ∈ closure S.U ×ˢ Ici 0,
        ∀ q ∈ closure S.U ×ˢ Ici 0, |uε ε p - uε ε q| ≤ ϖ (‖p.1 - q.1‖ + |p.2 - q.2|) := by
      intro ε hε
      have hf := hfamε ε (hsubε ε hε)
      refine hmodA ε ⟨hε.1, hε.2.le.trans (min_le_right _ _)⟩ (gε ε) (uε ε)
        (hf.2.2.2.2.2.2.2.2.2 L hgL) (fun x hx ↦ ?_) hf.1
      have hb := hf.2.2.1 x hx
      have hε1 : ε < 1 := hε.2.trans_le (min_le_right _ _)
      have hmax : max (g x) 0 ≤ M :=
        max_le ((le_abs_self _).trans (hgMcl x hx)) ((abs_nonneg _).trans (hgMcl x hx))
      exact ⟨(le_max_right _ _).trans hb.1, by linarith [hb.2]⟩
    obtain ⟨ũ, hlim, heq, hcont, hmodũ⟩ :=
      exists_limit_extension (F := closure S.U ×ˢ Ici 0) (D := UInf S.U)
        (prod_mono subset_closure Ioi_subset_Ici_self)
        (fun p hp ↦ by rw [UInf, closure_prod_eq, closure_Ioi]; exact hp)
        (v := fun j ↦ uε (εs j)) (fun p hp ↦ hloc.tendsto_at hp) hϖ
        (fun p q ↦ ‖p.1 - q.1‖ + |p.2 - q.2|) (fun p q ↦ by positivity)
        norm_add_abs_le_two_mul_dist (fun j p hp q hq ↦ hmod (εs j) (hεs j) p hp q hq)
    have heq' : EqOn u ũ (UInf S.U) := fun p hp ↦ (heq hp).symm
    have hbd : ∀ p ∈ closure S.U ×ˢ Ici 0, 0 ≤ ũ p ∧ ũ p ≤ M := by
      intro p hp
      have hb : ∀ j, 0 ≤ uε (εs j) p ∧ uε (εs j) p ≤ M + εs j := fun j ↦
        (hfamε (εs j) (hεs' j)).2.2.2.2.2.2.2.1 M hgM p hp
      refine ⟨ge_of_tendsto' (hlim p hp) fun j ↦ (hb j).1, ?_⟩
      have := le_of_tendsto_of_tendsto' (hlim p hp) (tendsto_const_nhds.add hεs0) fun j ↦ (hb j).2
      simpa using this
    have hbdry : ∀ p ∈ parBdryInf S.U, ũ p = max (g p.1) 0 := by
      rintro ⟨x, t⟩ hp
      have hxt : x ∈ closure S.U ∧ 0 ≤ t ∧ ∀ j, uε (εs j) (x, t) = gε (εs j) x := by
        rcases hp with ⟨hx, ht⟩ | ⟨hx, ht⟩
        · have ht0 : t = 0 := ht
          subst ht0
          exact ⟨hx, le_rfl, fun j ↦ (hfamε (εs j) (hεs' j)).1.2.2.1 x hx⟩
        · exact ⟨frontier_subset_closure hx, ht,
            fun j ↦ (hfamε (εs j) (hεs' j)).1.2.2.2 x hx t ht⟩
      obtain ⟨hx, ht, hj⟩ := hxt
      have hup : Tendsto (fun j ↦ max (g x) 0 + εs j) atTop (𝓝 (max (g x) 0)) := by
        simpa using (tendsto_const_nhds (x := max (g x) 0)).add hεs0
      have hg : Tendsto (fun j ↦ gε (εs j) x) atTop (𝓝 (max (g x) 0)) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          (fun j ↦ ((hfamε _ (hεs' j)).2.2.1 x hx).1) (fun j ↦ ((hfamε _ (hεs' j)).2.2.1 x hx).2)
      refine tendsto_nhds_unique (hlim (x, t) ⟨hx, ht⟩) ?_
      simpa only [hj] using hg
    exact ⟨εs, ũ, w, χ, hεs', hεs0, hloc.congr_right heq', hlim,
      ⟨hcont, hbdry, hinner.congr S.isOpen heq', hheat.congr S.isOpen heq',
        ((hdiss.congr S.isOpen heq').mono hGg), hlip.congr S.isOpen heq', hper⟩, hbd, hmodũ⟩
  have hUI : UInf S.U ⊆ closure S.U ×ˢ Ici 0 := prod_mono subset_closure Ioi_subset_Ici_self
  have hIoc : ∀ T, S.U ×ˢ Ioc 0 T ⊆ UInf S.U := fun T ↦ prod_mono subset_rfl Ioc_subset_Ioi_self
  refine ⟨fun hsub ↦ ?_, fun hsuper ↦ ?_⟩
  · -- strict subsolution data: Corollary 5.4
    obtain ⟨ε₀, gε, uε, hfam⟩ := (h37 d S g β hβ).1 hsub
    obtain ⟨εs, u, w, χ, hεs, hεs0, hloc, hlim, hcommon, hbd, hmodu⟩ := key true ε₀ gε uε hfam
    have hcont : ContinuousOn u (S.U ×ˢ Ioi 0) := hcommon.1.mono hUI
    have hnn : ∀ p ∈ S.U ×ˢ Ioi 0, 0 ≤ u p := fun p hp ↦ (hbd p (hUI hp)).1
    have hmono : ∀ j, MonotoneInTime (uε (εs j)) (closure S.U) (Ici 0) := fun j ↦ by
      simpa using (hfam.2.1 (εs j) (hεs j)).2.2.2.2.2.2.1
    refine ⟨u, w, χ, hcommon, ?_, ?_, ?_, hbd, hmodu⟩
    · intro x hx s hs t ht hst
      exact le_of_tendsto_of_tendsto' (hlim (x, s) ⟨hx, hs⟩) (hlim (x, t) ⟨hx, ht⟩)
        fun j ↦ hmono j x hx hs ht hst
    · exact isParaSolution_Ioi_of_Ioc hcont hnn fun T hT ↦
        (h54 d S g β ε₀ gε uε hβ hsub hfam T εs u hT hεs hεs0 (hloc.mono (hIoc T))).2.2
    · intro K hK hKsub
      obtain ⟨τ, hτ, ε₁, hε₁, hjump⟩ := hfam.2.2.2.2.2.2.2.1 K hK hKsub
      refine ⟨τ, hτ, fun x hx t ht ↦ le_antisymm ?_ (hbd (x, t) ⟨(hKsub hx).1, ht.1⟩).1⟩
      refine le_of_tendsto_of_tendsto (hlim (x, t) ⟨(hKsub hx).1, ht.1⟩) hεs0 ?_
      filter_upwards [hεs0.eventually (gt_mem_nhds hε₁)] with j hj
      exact (hjump (εs j) ⟨(hεs j).1, hj⟩ (hεs j).2 x hx t ht).le
  · -- strict supersolution data: Proposition 5.3
    obtain ⟨ε₀, gε, uε, hfam⟩ := (h37 d S g β hβ).2 hsuper
    obtain ⟨εs, u, w, χ, hεs, hεs0, hloc, hlim, hcommon, hbd, hmodu⟩ := key false ε₀ gε uε hfam
    have hcont : ContinuousOn u (S.U ×ˢ Ioi 0) := hcommon.1.mono hUI
    have hnn : ∀ p ∈ S.U ×ˢ Ioi 0, 0 ≤ u p := fun p hp ↦ (hbd p (hUI hp)).1
    have hanti : ∀ j, AntitoneInTime (uε (εs j)) (closure S.U) (Ici 0) := fun j ↦ by
      simpa using (hfam.2.1 (εs j) (hεs j)).2.2.2.2.2.2.1
    refine ⟨u, w, χ, hcommon, ?_, ⟨closure (S.U ×ˢ Ioi 0), ?_⟩, hbd, hmodu⟩
    · intro x hx s hs t ht hst
      exact le_of_tendsto_of_tendsto' (hlim (x, t) ⟨hx, ht⟩) (hlim (x, s) ⟨hx, hs⟩)
        fun j ↦ hanti j x hx hs ht hst
    · -- Proposition 5.3, in the form proved here: relaxed solution with the set
      -- `E = \overline{U × (0, T]}` (the paper's set `limsup* {u_ε > ε}` can fail)
      have hrel : ∀ T > 0, IsParaRelaxedSolution S.U S.Q (Ioc 0 T) u
          (closure (S.U ×ˢ Ioc 0 T)) := fun T hT ↦
        h53 d S β hβ T εs (fun j ↦ uε (εs j)) u hT (fun j ↦ (hεs j).1) hεs0
          (fun j ↦ (hfam.2.1 (εs j) (hεs j)).1.2.1.mono Ioc_subset_Ioi_self)
          (fun j p hp ↦ ((hfam.2.1 (εs j) (hεs j)).2.2.2.2.2.2.2.1 M hgM p
            ⟨subset_closure hp.1, le_of_lt hp.2.1⟩).1)
          (hloc.mono (hIoc T))
      exact ⟨isParaSuper_Ioi_of_Ioc hcont hnn fun T hT ↦ (hrel T hT).1,
        isParaRelaxedSub_Ioi_of_Ioc hcont hnn isClosed_closure closure_prod_eq.subset
          (fun T _ ↦ closure_mono (hIoc T))
          (fun T _ ↦ closure_Ioi_inter_subset T) fun T hT ↦ (hrel T hT).2⟩

/-- **Theorem 3.9** from Proposition 3.8 (`h37`), Proposition 4.1 (`h41`), Proposition 5.3
(`h53`) and Corollary 5.4 (`h54`), taken as statements. -/
theorem parabolic_existence_of (h37 : SemilinearWellposedStatement)
    (h41 : EpsInnerLimitStatement) (h53 : SemilinearLimitRelaxedStatement)
    (h54 : SemilinearLimitIncreasingStatement) : ParabolicExistenceStatement := by
  intro d S
  obtain ⟨C, hC⟩ := parabolic_existence_bdd_of h37 h41 h53 h54 d S
  refine ⟨C, fun M E0 hE0 ↦ ?_⟩
  obtain ⟨Cper, hCper⟩ := hC M E0 hE0
  have hL : ∀ g : E d → ℝ, ContDiff ℝ 2 g → ∃ L, LipschitzOnWith L g (closure S.U) := fun g hg ↦
    (hg.of_le one_le_two).locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      S.isBounded.isCompact_closure
  refine ⟨Cper, fun g hgM hgE ↦ ⟨fun hsub ↦ ?_, fun hsuper ↦ ?_⟩⟩
  · obtain ⟨L, hgL⟩ := hL g hsub.1
    obtain ⟨ϖ, -, hϖ⟩ := hCper L
    obtain ⟨u, w, χ, h1, h2, h3, h4, -⟩ := (hϖ g hgM hgE hgL).1 hsub
    exact ⟨u, w, χ, h1, h2, h3, h4⟩
  · obtain ⟨L, hgL⟩ := hL g hsuper.1
    obtain ⟨ϖ, -, hϖ⟩ := hCper L
    obtain ⟨u, w, χ, h1, h2, h3, -⟩ := (hϖ g hgM hgE hgL).2 hsuper
    exact ⟨u, w, χ, h1, h2, h3⟩

end PerronVariational

end
