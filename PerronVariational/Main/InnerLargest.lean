/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Parabolic.Existence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Main.ShiftLimit
import PerronVariational.Parabolic.LongTimeInnerViscosity
import PerronVariational.Parabolic.LongTimeViscosity
import PerronVariational.Parabolic.StatToPara
import PerronVariational.Registry.Comparison
import PerronVariational.Stationary.InnerSub
import PerronVariational.Stationary.Perron
import PerronVariational.Stationary.ViscosityStability

/-!
# Proposition 6.2: the largest subsolution is an inner variational and viscosity solution

**Proposition 6.2** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. If `g` is a smooth
strict supersolution, Perron's largest subsolution below `g` is both an inner variational and a
viscosity solution of (1.1) in `U`, and it is continuous on `Ū`.

Proof:
1. (`largest_shift`) For `0 < a ≤ a₁` the shift `g + a` is a strict supersolution with uniform
   constants; Theorem 3.9 (`ParabolicExistenceBddStatement`) gives the decreasing flow `𝔲^a`, a
   parabolic viscosity supersolution. For `v ∈ 𝒮^g`, the comparison principle (Theorem 3.6) on
   `U × (0, T]` (with `v` a stationary parabolic subsolution by Remark 3.3) gives `v ≤ 𝔲^a`. Its
   hypothesis `v ≺ 𝔲^a` on a neighbourhood of `∂_P` follows from strictness at the points of
   `∂_P ∩ closure {v > 0}`, where `g ≥ 0` because `0 < v ≤ g₊` forces `g > 0`, so
   `v ≤ g < g + a = (g + a)₊` (a step the paper leaves implicit). Theorem 3.10 gives the long-time
   limit `u^a_∞`, inner variational with (3.14), (3.15) uniform in `a`; Lemma 5.6
   (`longtime_super`) makes it a viscosity supersolution.
2. (`inner_largest_of`) Along `a_k ↓ 0`, the compactness of inner variational solutions
   (Lemma 2.10) gives a locally uniform limit `ǔ` along a subsequence, an inner variational
   solution; Lemma 2.4 gives the supersolution and Lemma 2.9 the subsolution property. The
   sandwich `v ≤ ǔ ≤ g₊` (`v ∈ 𝒮^g`) identifies `ǔ` with Perron's solution
   (`eqOn_perronLargest_of_le`). The boundary values of `ǔ`, which the paper does not check, come
   from the attainment modulus `ϖ` of Proposition A.8 exported by Theorem 3.9, uniform in `a`:
   `u^a_∞(x) ≥ (g + a)₊(x₀) - ϖ(|x - x₀|) ≥ g₊(x₀) - ϖ(|x - x₀|)` for `x₀ ∈ ∂U`. As a by-product
   Perron's solution is continuous on `Ū`.

Theorem 3.12(ii) (`LongtimeViscInnerStatement`) is not needed (as in Proposition 6.1): the
subsolution property is only used for the final limit, via Lemma 2.9.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- **Step 1 of Proposition 6.2**: the long-time limits `u^a_∞` of the flows with data
`(g + a)₊`, `0 < a ≤ a₁`, with all constants (`M`, `C`, `CV`) uniform in `a`. -/
theorem largest_shift (h38 : ParabolicExistenceBddStatement) (h310 : LongtimeInnerStatement)
    (S : Setting d) {g : E d → ℝ} (hg : IsStrictSuper S.U S.Q g) :
    ∃ (a₁ M C : ℝ) (CV : Set (E d) → ℝ) (ϖ : ℝ → ℝ), 0 < a₁ ∧ Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ a : ℝ, 0 < a → a ≤ a₁ →
      ∃ uInf χInf : E d → ℝ, IsInnerVarSolution S.U S.Q uInf χInf ∧ IsViscSuper S.U S.Q uInf ∧
        (∀ x ∈ S.U, 0 ≤ uInf x ∧ uInf x ≤ M) ∧ (∀ x ∈ S.U, uInf x ≤ max (g x + a) 0) ∧
        (∀ v ∈ perronSubClass S.U S.Q g, ∀ x ∈ S.U, v x ≤ uInf x) ∧
        (∀ (x : E d) (r : ℝ), 0 < r → r ≤ 1 → ball x (2 * r) ⊆ S.U →
            ∀ M' : ℝ, (∀ y ∈ ball x (2 * r), |uInf y| ≤ M') →
              ∀ y ∈ ball x r, ‖∇ uInf y‖ ≤ C * (M' / r + 1)) ∧
        (∀ V : Set (E d), CompactlyContained V S.U →
          totalVariationOn V χInf ≤ ENNReal.ofReal (CV V)) ∧
        ∀ x ∈ S.U, ∀ x₀ ∈ frontier S.U, max (g x₀) 0 - ϖ ‖x - x₀‖ ≤ uInf x := by
  obtain ⟨a₀, δ₀, hw⟩ := isStrictSuper_iff.1 hg
  obtain ⟨Mg, hMg⟩ := S.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hg.1.continuous.continuousOn
  set M := Mg + a₀ / 2 with hMdef
  set E0 := energyBound S (∇ g) with hE0def
  have hE0 : E0 ≠ ⊤ := energyBound_ne_top S (hg.1.of_le one_le_two)
  -- constants uniform in the shift
  obtain ⟨C, hC⟩ := h38 d S
  obtain ⟨Cper, hCper⟩ := hC M E0 hE0
  obtain ⟨CV, hCV⟩ := h310 d S M E0 C Cper hE0
  -- the modulus of Prop A.8, uniform in the shift: it depends on `g + a` only through its
  -- Lipschitz constant `L` (that of `g`) and `M`
  obtain ⟨L, hL⟩ := (hg.1.of_le one_le_two).locallyLipschitz.locallyLipschitzOn
    |>.exists_lipschitzOnWith_of_compact S.isBounded.isCompact_closure
  obtain ⟨ϖ, hϖ, hCperL⟩ := hCper L
  refine ⟨a₀ / 2, M, C, CV, ϖ, half_pos hw.2.1, hϖ, fun a ha₁ ha₂ ↦ ?_⟩
  have hLa : LipschitzOnWith L (fun x ↦ g x + a) (closure S.U) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ by
      rw [dist_add_right]; exact hL.dist_le_mul x hx y hy
  have hga : IsStrictSuper S.U S.Q (fun x ↦ g x + a) :=
    isStrictSuper_iff.2 ⟨_, _, hw.add_const (abs_le.2 ⟨by linarith [hw.2.1], ha₂⟩)⟩
  have hgaM : ∀ x ∈ S.U, |g x + a| ≤ M := fun x hx ↦ by
    have h1 := hMg x (subset_closure hx)
    rw [Real.norm_eq_abs] at h1
    calc |g x + a| ≤ |g x| + |a| := abs_add_le _ _
      _ ≤ M := add_le_add h1 (abs_le.2 ⟨by linarith [hw.2.1], ha₂⟩)
  have hgaE : energyBound S (∇ fun x ↦ g x + a) ≤ E0 := by rw [gradient_add_const']
  obtain ⟨u, w, χ, hcom, hanti, ⟨Erel, hrel⟩, hbd, hmodu⟩ := (hCperL _ hgaM hgaE hLa).2 hga
  obtain ⟨hcont, hbdry, hinner, hheat, hdiss, hlip, hper⟩ := hcom
  rw [gradient_add_const'] at hdiss
  have hgc : Continuous g := hg.1.continuous
  -- comparison with `v ∈ 𝒮^g` (Theorem 3.6 on `U × (0, T]`, Remark 3.3)
  have hcomp : ∀ v ∈ perronSubClass S.U S.Q g, ∀ p ∈ closure S.U ×ˢ Ici 0, v p.1 ≤ u p := by
    intro v hv p hp
    have hp2 : (0 : ℝ) ≤ p.2 := hp.2
    set T := p.2 + 1 with hTdef
    have hT : 0 < T := by linarith
    set D := closure S.U ×ˢ Icc 0 T with hDdef
    set Eset := closure (posSetP (fun q : E d × ℝ ↦ v q.1) D) with hEdef
    have hDI : D ⊆ closure S.U ×ˢ Ici 0 := Set.prod_mono subset_rfl Icc_subset_Ici_self
    have huD : ContinuousOn u D := hcont.mono hDI
    have hvD : ContinuousOn (fun q : E d × ℝ ↦ v q.1) D :=
      hv.1.comp continuousOn_fst fun q hq ↦ hq.1
    have hED : Eset ⊆ D :=
      closure_minimal (sep_subset _ _) (isClosed_closure.prod isClosed_Icc)
    -- `g ≥ 0` on `closure {v > 0}`
    have hEg : Eset ⊆ {q | 0 ≤ g q.1} := by
      refine closure_minimal ?_ (isClosed_le continuous_const (hgc.comp continuous_fst))
      rintro q ⟨hqD, hqpos⟩
      have hle : v q.1 ≤ max (g q.1) 0 := hv.2.2 q.1 hqD.1
      by_contra hneg
      rw [max_eq_right (le_of_lt (not_le.1 hneg))] at hle
      exact absurd hqpos (not_lt.2 hle)
    have hstrict : ∀ q ∈ parBdry S.U 0 T ∩ Eset, v q.1 < u q := by
      rintro ⟨x, t⟩ ⟨hq, hqE⟩
      have hxcl : x ∈ closure S.U := by
        rcases hq with ⟨hx, -⟩ | ⟨hx, -⟩
        exacts [hx, frontier_subset_closure hx]
      have hq' : (x, t) ∈ parBdryInf S.U := by
        rcases hq with ⟨hx, ht⟩ | ⟨hx, ht⟩
        · exact Or.inl ⟨hx, ht⟩
        · exact Or.inr ⟨hx, ht.1⟩
      rw [hbdry _ hq']
      have hgx : 0 ≤ g x := hEg hqE
      have hvx : v x ≤ g x := (hv.2.2 x hxcl).trans_eq (max_eq_left hgx)
      exact hvx.trans_lt ((lt_add_of_pos_right _ ha₁).trans_le (le_max_left _ _))
    have hN := mem_nhdsSet_precOn isClosed_closure hED hvD huD hstrict
    have hres := Registry.para_strict_comparison S.isOpen S.isBounded S.isConnected S.lip
      ⟨S.Qmin, S.Qmin_pos, fun x hx ↦ (S.Q_mem x hx).1⟩ hT hvD huD
      (hv.2.1.isParaSub_const _) (hrel.1.mono_time Ioc_subset_Ioi_self) hN
      (fun q hq ↦ hq.2 hq.1)
    have hpD : p ∈ D := ⟨hp.1, hp2, by linarith⟩
    by_cases hpE : p ∈ Eset
    · exact (hres p ⟨hpE, hpD⟩).le
    · have : ¬ 0 < v p.1 := fun h ↦ hpE (subset_closure ⟨hpD, h⟩)
      exact (not_lt.1 this).trans (hbd p hp).1
  -- the long-time limit (Thm 3.10)
  have hantiU : AntitoneInTime u S.U (Ioi 0) := fun x hx ↦
    (hanti x (subset_closure hx)).mono Ioi_subset_Ici_self
  have hbddU : ∀ p ∈ UInf S.U, u p ≤ M := fun p hp ↦
    (hbd p ⟨subset_closure hp.1, mem_Ici.2 (le_of_lt hp.2)⟩).2
  obtain ⟨uInf, hconv, -, χInf, -, -, -, hinf, hLip, hPer⟩ :=
    hCV u w χ hinner hheat hbddU (Or.inr hantiU) hdiss hlip hper
  have hev : ∀ x ∈ S.U, ∀ᶠ t : ℝ in atTop, (x, t) ∈ closure S.U ×ˢ Ici 0 := fun x hx ↦
    (eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦ ⟨subset_closure hx, ht⟩
  refine ⟨uInf, χInf, hinf, longtime_super S.isOpen S.continuousOn_Q hrel.1 hconv, ?_, ?_, ?_,
    hLip, hPer, ?_⟩
  · intro x hx
    exact ⟨ge_of_tendsto (hconv.tendsto_at hx) ((hev x hx).mono fun t ht ↦ (hbd _ ht).1),
      le_of_tendsto (hconv.tendsto_at hx) ((hev x hx).mono fun t ht ↦ (hbd _ ht).2)⟩
  · intro x hx
    have h0 : u (x, 0) = max (g x + a) 0 := hbdry (x, 0) (Or.inl ⟨subset_closure hx, rfl⟩)
    refine le_of_tendsto (hconv.tendsto_at hx) ((eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦ ?_)
    rw [← h0]
    exact hanti x (subset_closure hx) (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  · intro v hv x hx
    exact ge_of_tendsto (hconv.tendsto_at hx) ((hev x hx).mono fun t ht ↦ hcomp v hv _ ht)
  · -- boundary values: `𝔲^a(x, t) ≥ 𝔲^a(x₀, t) - ϖ(|x - x₀|) = (g + a)₊(x₀) - ϖ(|x - x₀|)`
    intro x hx x₀ hx₀
    refine ge_of_tendsto (hconv.tendsto_at hx) ((eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦ ?_)
    have h1 := hmodu (x, t) ⟨subset_closure hx, ht⟩ (x₀, t) ⟨frontier_subset_closure hx₀, ht⟩
    have h2 : u (x₀, t) = max (g x₀ + a) 0 := hbdry _ (Or.inr ⟨hx₀, ht⟩)
    simp only [sub_self, abs_zero, add_zero] at h1
    have h3 : max (g x₀) 0 ≤ max (g x₀ + a) 0 := max_le_max (by linarith) le_rfl
    linarith [(abs_le.1 h1).1]

/-- **Proposition 6.2**, from Theorem 3.9 (`ParabolicExistenceBddStatement`, the version of
`ParabolicExistenceStatement` with the bound `0 ≤ u ≤ M`) and Theorem 3.10
(`LongtimeInnerStatement`). -/
theorem inner_largest_of (h38 : ParabolicExistenceBddStatement)
    (h310 : LongtimeInnerStatement) : InnerLargestStatement := by
  intro d S g hg
  obtain ⟨a₁, M, C, CV, ϖ, ha₁, hϖ, hshift⟩ := largest_shift h38 h310 S hg
  -- shifts `a_k = a₁/(k+1) ↓ 0`
  set a : ℕ → ℝ := fun k ↦ a₁ / ((k : ℝ) + 1) with hadef
  have ha : ∀ k, 0 < a k ∧ a k ≤ a₁ := by
    intro k
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    refine ⟨by positivity, ?_⟩
    rw [hadef, div_le_iff₀ (by positivity)]
    nlinarith
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul a₁
    simpa [hadef, mul_one_div] using this
  choose uk χk hk using fun k ↦ hshift (a k) (ha k).1 (ha k).2
  -- the limit `a → 0` along a subsequence (Lemma 2.10)
  obtain ⟨φ, û, χh, hφ, hconv, hinner⟩ := exists_innerVar_limit S uk χk (fun k ↦ (hk k).1)
    (fun k ↦ (hk k).2.2.1) (fun k ↦ (hk k).2.2.2.2.2.1) (fun k ↦ (hk k).2.2.2.2.2.2.1)
  -- Lemma 2.4 (stability of supersolutions) and Lemma 2.9 (inner variational ⇒ subsolution)
  have hsuper : IsViscSuper S.U S.Q û :=
    isViscSuper_of_tendstoLocallyUniformlyOn S.isOpen S.continuousOn_Q
      (Eventually.of_forall fun j ↦ (hk (φ j)).2.1) hconv
  have hsub : IsViscSub S.U S.Q û :=
    hinner.isViscSub S.two_le S.isOpen S.isConnected S.lipschitzOn_U S.exists_pos_le_Q S.exists_Q_le
  -- the sandwich `v ≤ ǔ ≤ g₊`, `v ∈ 𝒮^g`
  have hup : ∀ x ∈ S.U, û x ≤ max (g x) 0 := by
    intro x hx
    have hlim : Tendsto (fun j ↦ max (g x + a (φ j)) 0) atTop (𝓝 (max (g x) 0)) := by
      simpa using ((tendsto_const_nhds (x := g x)).add
        (ha0.comp hφ.tendsto_atTop)).max tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' (hconv.tendsto_at hx) hlim fun j ↦ (hk (φ j)).2.2.2.1 x hx
  have hlow : ∀ v ∈ perronSubClass S.U S.Q g, ∀ x ∈ S.U, v x ≤ û x := fun v hv x hx ↦
    ge_of_tendsto' (hconv.tendsto_at hx) fun j ↦ (hk (φ j)).2.2.2.2.1 v hv x hx
  -- boundary values of `ǔ` from the modulus of Prop A.8, uniform in the shift
  have hbdry : ∀ x ∈ S.U, ∀ x₀ ∈ frontier S.U, max (g x₀) 0 - ϖ ‖x - x₀‖ ≤ û x :=
    fun x hx x₀ hx₀ ↦ ge_of_tendsto' (hconv.tendsto_at hx) fun j ↦
      (hk (φ j)).2.2.2.2.2.2.2 x hx x₀ hx₀
  obtain ⟨heq, hcontP⟩ := eqOn_perronLargest_of_le S hg.1.continuous hsub hup hlow hϖ hbdry
  exact ⟨⟨hsuper.congr heq.symm, hsub.congr heq.symm⟩, ⟨χh, hinner.congr S.isOpen heq.symm⟩,
    hcontP⟩

end PerronVariational

end
