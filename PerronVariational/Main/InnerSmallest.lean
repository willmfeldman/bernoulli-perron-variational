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
# Proposition 6.1: the smallest supersolution is an inner variational and viscosity solution

**Proposition 6.1** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. If `g` is a smooth
strict subsolution with `g > 0` on `∂U`, Perron's smallest supersolution above `g` is both an
inner variational and a viscosity solution of (1.1) in `U`, and it is continuous on `Ū`.

Proof:
1. (`smallest_shift`) For `-a₁ ≤ a < 0` the shift `g + a` is a strict subsolution with uniform
   constants; Theorem 3.9 (`ParabolicExistenceBddStatement`, with bounds uniform in `a`) gives the
   increasing flow `𝔲_a`. For `v ∈ 𝒮_g` the strict comparison principle (Theorem 3.6) on
   `U × (0, T]` gives `𝔲_a ≤ v`. Its hypothesis "`𝔲_a ≺ v` on a neighbourhood of `∂_P`" is
   verified in full; the paper checks the ordering only on `∂_P` itself. It holds on the lateral
   boundary since `g > 0` on `∂U`, at `t = 0` where `v > 0` by continuity, and at `t = 0` where
   `v = 0` because the positivity set of the flow does not jump outward at `t = 0` (a conclusion
   of Theorem 3.9). Theorem 3.10 (`LongtimeInnerStatement`) gives the long-time limit `u_{a,∞}`,
   inner variational, with (3.14), (3.15) uniform in `a`; Lemma 5.6 (`longtime_super`) makes it a
   viscosity supersolution.
2. (`inner_smallest_of`) Along `a_k ↑ 0`, the compactness of inner variational solutions
   (Lemma 2.10) gives a locally uniform limit `û` along a subsequence which is an inner
   variational solution; Lemma 2.4 makes it a viscosity supersolution and Lemma 2.9 a viscosity
   subsolution. (The paper attributes the subsolution property to stability, but viscosity
   subsolutions are not stable under uniform limits; Lemma 2.9 is what applies, as in the
   paper's proof of Proposition 6.2.) The sandwich `g₊ ≤ û ≤ v` (`v ∈ 𝒮_g`) identifies `û` with
   Perron's solution (`eqOn_perronSmallest_of_le`). For this `û`, extended by `g₊`, must lie in
   `𝒮_g`, i.e. attain `g₊` continuously at `∂U`, which the paper does not check. Theorem 3.9
   exports the attainment modulus `ϖ` of Proposition A.8, which depends on the data only through
   `(Lip g, M)` and so is uniform in `a`; hence
   `u_{a,∞}(x) ≤ (g + a)₊(x₀) + ϖ(|x - x₀|) ≤ g₊(x₀) + ϖ(|x - x₀|)` for `x₀ ∈ ∂U`, which passes to
   `û`. As a by-product Perron's solution is continuous on `Ū`.

Theorem 3.12(i) (`LongtimeViscIncreasingStatement`) is not needed: only the supersolution property
of `u_{a,∞}` is used, and the subsolution property of the final limit comes from Lemma 2.9.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- **Step 1 of Proposition 6.1**: the long-time limits `u_{a,∞}` of the flows with data
`(g + a)₊`, `-a₁ ≤ a < 0`, with all constants (`M`, `C`, `CV`) uniform in `a`. -/
theorem smallest_shift (h38 : ParabolicExistenceBddStatement) (h310 : LongtimeInnerStatement)
    (S : Setting d) {g : E d → ℝ} (hg : IsStrictSub S.U S.Q g)
    (hgb : ∀ x ∈ frontier S.U, 0 < g x) :
    ∃ (a₁ M C : ℝ) (CV : Set (E d) → ℝ) (ϖ : ℝ → ℝ), 0 < a₁ ∧ Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ a : ℝ, -a₁ ≤ a → a < 0 →
      ∃ uInf χInf : E d → ℝ, IsInnerVarSolution S.U S.Q uInf χInf ∧ IsViscSuper S.U S.Q uInf ∧
        (∀ x ∈ S.U, 0 ≤ uInf x ∧ uInf x ≤ M) ∧ (∀ x ∈ S.U, max (g x + a) 0 ≤ uInf x) ∧
        (∀ v ∈ perronSuperClass S.U S.Q g, ∀ x ∈ S.U, uInf x ≤ v x) ∧
        (∀ (x : E d) (r : ℝ), 0 < r → r ≤ 1 → ball x (2 * r) ⊆ S.U →
            ∀ M' : ℝ, (∀ y ∈ ball x (2 * r), |uInf y| ≤ M') →
              ∀ y ∈ ball x r, ‖∇ uInf y‖ ≤ C * (M' / r + 1)) ∧
        (∀ V : Set (E d), CompactlyContained V S.U →
          totalVariationOn V χInf ≤ ENNReal.ofReal (CV V)) ∧
        ∀ x ∈ S.U, ∀ x₀ ∈ frontier S.U, uInf x ≤ max (g x₀) 0 + ϖ ‖x - x₀‖ := by
  obtain ⟨a₀, δ₀, hw⟩ := isStrictSub_iff.1 hg
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
  have hga : IsStrictSub S.U S.Q (fun x ↦ g x + a) :=
    isStrictSub_iff.2 ⟨_, _, hw.add_const (abs_le.2 ⟨ha₁, by linarith [hw.2.1]⟩)⟩
  have hgaM : ∀ x ∈ S.U, |g x + a| ≤ M := fun x hx ↦ by
    have h1 := hMg x (subset_closure hx)
    rw [Real.norm_eq_abs] at h1
    calc |g x + a| ≤ |g x| + |a| := abs_add_le _ _
      _ ≤ M := add_le_add h1 (abs_le.2 ⟨ha₁, by linarith [hw.2.1]⟩)
  have hgaE : energyBound S (∇ fun x ↦ g x + a) ≤ E0 := by rw [gradient_add_const']
  obtain ⟨u, w, χ, hcom, hmono, hsol, hjump, hbd, hmodu⟩ := (hCperL _ hgaM hgaE hLa).1 hga
  obtain ⟨hcont, hbdry, hinner, hheat, hdiss, hlip, hper⟩ := hcom
  rw [gradient_add_const'] at hdiss
  -- comparison with `v ∈ 𝒮_g` (Theorem 3.6 on `U × (0, T]`, Remark 3.3)
  have hcomp : ∀ v ∈ perronSuperClass S.U S.Q g, ∀ p ∈ closure S.U ×ˢ Ici 0, u p ≤ v p.1 := by
    intro v hv p hp
    have hp2 : (0 : ℝ) ≤ p.2 := hp.2
    set T := p.2 + 1 with hTdef
    have hT : 0 < T := by linarith
    set D := closure S.U ×ˢ Icc 0 T with hDdef
    set Eset := closure (posSetP u D) with hEdef
    have hDI : D ⊆ closure S.U ×ˢ Ici 0 := Set.prod_mono subset_rfl Icc_subset_Ici_self
    have huD : ContinuousOn u D := hcont.mono hDI
    have hvD : ContinuousOn (fun q : E d × ℝ ↦ v q.1) D :=
      hv.1.comp continuousOn_fst fun q hq ↦ hq.1
    have hED : Eset ⊆ D :=
      closure_minimal (sep_subset _ _) (isClosed_closure.prod isClosed_Icc)
    -- strict ordering at the points of `∂_P ∩ E`
    have hstrict : ∀ q ∈ parBdry S.U 0 T ∩ Eset, u q < v q.1 := by
      rintro ⟨x, t⟩ ⟨hq, hqE⟩
      have hxcl : x ∈ closure S.U := by
        rcases hq with ⟨hx, -⟩ | ⟨hx, -⟩
        exacts [hx, frontier_subset_closure hx]
      have hq' : (x, t) ∈ parBdryInf S.U := by
        rcases hq with ⟨hx, ht⟩ | ⟨hx, ht⟩
        · exact Or.inl ⟨hx, ht⟩
        · exact Or.inr ⟨hx, ht.1⟩
      rw [hbdry _ hq']
      have hvx : max (g x) 0 ≤ v x := hv.2.2 x hxcl
      rcases hq with ⟨-, ht⟩ | ⟨hx, -⟩
      · -- bottom `t = 0`
        by_contra hcon
        replace hcon := not_lt.1 hcon
        have hgx : g x + a < 0 := by
          by_contra h'
          replace h' := not_lt.1 h'
          rw [max_eq_left h'] at hcon
          have : g x ≤ v x := (le_max_left _ _).trans hvx
          linarith
        have ht0 : t = 0 := ht
        subst ht0
        -- no outward jump of `{𝔲_a > 0}` at `t = 0` near `x` (conclusion of Thm 3.9)
        have hopen : IsOpen {y : E d | g y + a < 0} :=
          isOpen_lt (hg.1.continuous.add continuous_const) continuous_const
        obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen x hgx
        have hr : 0 < ρ / 2 := half_pos hρ
        have hKc : IsCompact (closedBall x (ρ / 2) ∩ closure S.U) :=
          (isCompact_closedBall x _).inter_right isClosed_closure
        have hKsub : closedBall x (ρ / 2) ∩ closure S.U ⊆
            closure S.U \ closure (posSet (fun y ↦ g y + a) (closure S.U)) := by
          intro y hy
          refine ⟨hy.2, fun hycl ↦ ?_⟩
          obtain ⟨z, hz, hzy⟩ := Metric.mem_closure_iff.1 hycl (ρ / 2) hr
          have hyx : dist y x ≤ ρ / 2 := mem_closedBall.1 hy.1
          have hzx : dist z x < ρ := by
            calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
              _ < ρ / 2 + ρ / 2 := by rw [dist_comm] at hzy; linarith
              _ = ρ := by ring
          have hneg : g z + a < 0 := hball (mem_ball.2 hzx)
          have hpos : 0 < g z + a := hz.2
          linarith
        obtain ⟨τ, hτ, hzero⟩ := hjump _ hKc hKsub
        have hO : IsOpen (ball x (ρ / 2) ×ˢ Ioo (-τ) τ) := isOpen_ball.prod isOpen_Ioo
        have hxO : (x, (0 : ℝ)) ∈ ball x (ρ / 2) ×ˢ Ioo (-τ) τ :=
          ⟨mem_ball_self hr, neg_lt_zero.2 hτ, hτ⟩
        obtain ⟨z, hzO, hzpos⟩ := mem_closure_iff.1 hqE _ hO hxO
        have hz0 : u (z.1, z.2) = 0 :=
          hzero z.1 ⟨mem_closedBall.2 (mem_ball.1 hzO.1).le, hzpos.1.1⟩ z.2
            ⟨hzpos.1.2.1, hzO.2.2.le⟩
        have hzpos' : 0 < u z := hzpos.2
        rw [show z = (z.1, z.2) from rfl, hz0] at hzpos'
        exact lt_irrefl 0 hzpos'
      · -- lateral boundary: `g > 0` on `∂U`
        exact (max_lt (by linarith [hgb x hx]) (hgb x hx)).trans_le ((le_max_left _ _).trans hvx)
    have hN := mem_nhdsSet_precOn isClosed_closure hED huD hvD hstrict
    have hres := Registry.para_strict_comparison S.isOpen S.isBounded S.isConnected S.lip
      ⟨S.Qmin, S.Qmin_pos, fun x hx ↦ (S.Q_mem x hx).1⟩ hT huD hvD
      (hsol.2.Ioc_of_Ioi S.isOpen S.continuousOn_Q) (hv.2.1.isParaSuper_const _) hN
      (fun q hq ↦ hq.2 hq.1)
    have hpD : p ∈ D := ⟨hp.1, hp2, by linarith⟩
    by_cases hpE : p ∈ Eset
    · exact (hres p ⟨hpE, hpD⟩).le
    · have : ¬ 0 < u p := fun h ↦ hpE (subset_closure ⟨hpD, h⟩)
      exact (not_lt.1 this).trans ((le_max_right _ _).trans (hv.2.2 p.1 hp.1))
  -- the long-time limit (Thm 3.10)
  have hmonoU : MonotoneInTime u S.U (Ioi 0) := fun x hx ↦
    (hmono x (subset_closure hx)).mono Ioi_subset_Ici_self
  have hbddU : ∀ p ∈ UInf S.U, u p ≤ M := fun p hp ↦
    (hbd p ⟨subset_closure hp.1, mem_Ici.2 (le_of_lt hp.2)⟩).2
  obtain ⟨uInf, hconv, -, χInf, -, -, -, hinf, hLip, hPer⟩ :=
    hCV u w χ hinner hheat hbddU (Or.inl hmonoU) hdiss hlip hper
  have hev : ∀ x ∈ S.U, ∀ᶠ t : ℝ in atTop, (x, t) ∈ closure S.U ×ˢ Ici 0 := fun x hx ↦
    (eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦ ⟨subset_closure hx, ht⟩
  refine ⟨uInf, χInf, hinf, longtime_super S.isOpen S.continuousOn_Q hsol.1 hconv, ?_, ?_, ?_,
    hLip, hPer, ?_⟩
  · intro x hx
    exact ⟨ge_of_tendsto (hconv.tendsto_at hx) ((hev x hx).mono fun t ht ↦ (hbd _ ht).1),
      le_of_tendsto (hconv.tendsto_at hx) ((hev x hx).mono fun t ht ↦ (hbd _ ht).2)⟩
  · intro x hx
    have h0 : u (x, 0) = max (g x + a) 0 := hbdry (x, 0) (Or.inl ⟨subset_closure hx, rfl⟩)
    refine ge_of_tendsto (hconv.tendsto_at hx) ((eventually_ge_atTop 0).mono fun t ht ↦ ?_)
    rw [← h0]
    exact hmono x (subset_closure hx) (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  · intro v hv x hx
    exact le_of_tendsto (hconv.tendsto_at hx) ((hev x hx).mono fun t ht ↦ hcomp v hv _ ht)
  · -- boundary values: `𝔲_a(x, t) ≤ 𝔲_a(x₀, t) + ϖ(|x - x₀|) = (g + a)₊(x₀) + ϖ(|x - x₀|)`
    intro x hx x₀ hx₀
    refine le_of_tendsto (hconv.tendsto_at hx) ((eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦ ?_)
    have h1 := hmodu (x, t) ⟨subset_closure hx, ht⟩ (x₀, t) ⟨frontier_subset_closure hx₀, ht⟩
    have h2 : u (x₀, t) = max (g x₀ + a) 0 := hbdry _ (Or.inr ⟨hx₀, ht⟩)
    simp only [sub_self, abs_zero, add_zero] at h1
    have h3 : max (g x₀ + a) 0 ≤ max (g x₀) 0 := max_le_max (by linarith) le_rfl
    linarith [(abs_le.1 h1).2]

/-- **Proposition 6.1**, from Theorem 3.9 (`ParabolicExistenceBddStatement`, the version of
`ParabolicExistenceStatement` with the bound `0 ≤ u ≤ M`) and Theorem 3.10
(`LongtimeInnerStatement`). -/
theorem inner_smallest_of (h38 : ParabolicExistenceBddStatement)
    (h310 : LongtimeInnerStatement) : InnerSmallestStatement := by
  intro d S g hg hgb
  obtain ⟨a₁, M, C, CV, ϖ, ha₁, hϖ, hshift⟩ := smallest_shift h38 h310 S hg hgb
  -- shifts `a_k = -a₁/(k+1) ↑ 0`
  set a : ℕ → ℝ := fun k ↦ -(a₁ / ((k : ℝ) + 1)) with hadef
  have ha : ∀ k, -a₁ ≤ a k ∧ a k < 0 := by
    intro k
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    have hpos : 0 < a₁ / ((k : ℝ) + 1) := by positivity
    refine ⟨neg_le_neg ?_, neg_lt_zero.2 hpos⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul a₁).neg
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
  -- the sandwich `g₊ ≤ û ≤ v`, `v ∈ 𝒮_g`
  have hlow : ∀ x ∈ S.U, max (g x) 0 ≤ û x := by
    intro x hx
    have hlim : Tendsto (fun j ↦ max (g x + a (φ j)) 0) atTop (𝓝 (max (g x) 0)) := by
      simpa using ((tendsto_const_nhds (x := g x)).add
        (ha0.comp hφ.tendsto_atTop)).max tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' hlim (hconv.tendsto_at hx) fun j ↦ (hk (φ j)).2.2.2.1 x hx
  have hup : ∀ v ∈ perronSuperClass S.U S.Q g, ∀ x ∈ S.U, û x ≤ v x := fun v hv x hx ↦
    le_of_tendsto' (hconv.tendsto_at hx) fun j ↦ (hk (φ j)).2.2.2.2.1 v hv x hx
  -- boundary values of `û` from the modulus of Prop A.8, uniform in the shift
  have hbdry : ∀ x ∈ S.U, ∀ x₀ ∈ frontier S.U, û x ≤ max (g x₀) 0 + ϖ ‖x - x₀‖ :=
    fun x hx x₀ hx₀ ↦ le_of_tendsto' (hconv.tendsto_at hx) fun j ↦
      (hk (φ j)).2.2.2.2.2.2.2 x hx x₀ hx₀
  obtain ⟨heq, hcontP⟩ := eqOn_perronSmallest_of_le S hg.1.continuous hsuper hlow hup hϖ hbdry
  exact ⟨⟨hsuper.congr heq.symm, hsub.congr heq.symm⟩, ⟨χh, hinner.congr S.isOpen heq.symm⟩,
    hcontP⟩

end PerronVariational

end
