/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import Mathlib.Algebra.Order.Ring.Star
import PerronVariational.Inner.GoodTimes
import PerronVariational.Inner.LongTimeSteps
import PerronVariational.Inner.LongTimeUniform
import PerronVariational.Registry.FunctionalAnalysis

/-!
# Theorem 3.10: long-time limit, variational form (assembly)

**Theorem 3.10** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

## The added weak heat equation hypothesis

The paper assumes only that `(u, χ)` is a parabolic inner variational solution (Definition 3.7);
here we assume in addition the weak heat equation (4.5) in `{u > 0}` (`WeakHeatInPos S.U u w`),
because the theorem is false without it. Take `u(x, t) = 1 + |x₁|`, `w = 0`, `χ ≡ 1`, `Q`
constant. This is a time-independent parabolic inner variational solution (the integrand of (3.3)
is `(Q² + 1) div ξ - 2 ∂₁ξ₁` a.e., whose integral vanishes), bounded, monotone in time, and
satisfies (3.11)–(3.13) for suitable constants; but `u_∞ = 1 + |x₁|` is not `C²` in
`{u_∞ > 0} = U`, so `(u_∞, χ_∞)` is not an inner variational solution (Definition 2.8(i)). The
paper's proof uses (4.5) for the flow (Step 2: "in the same way that one shows `u` satisfies the
heat equation in its positivity set"), but (4.5) is proved in §4 only for the `ε → 0` limit and
is not part of Definition 3.7. The flows to which the paper applies the theorem (Theorem 3.9)
satisfy (4.5).

The other differences from the paper's statement are recorded at `LongtimeInnerStatement`: the
flow is assumed monotone in time (the paper's Step 1 claims that `u(·, t)` is Cauchy in `L²`,
which does not follow from `∂ₜu ∈ L²(U_∞)`; the flows in Propositions 6.1 and 6.2 are monotone),
and the strong gradient convergence is stated along a sequence of good times `tᵢ → ∞`.

## Main results

* `PerronVariational.LongTime.LongtimeInnerHeatStatement`: the statement with the weak heat
  equation hypothesis (the same as `LongtimeInnerStatement`).
* `PerronVariational.LongTime.longtime_innerVar_of_weakHeat`: its proof from the sub-lemmas of
  `Inner/LongTimeUniform.lean` (Step 1), `Inner/TimeLocalize.lean`, `Inner/GoodTimes.lean` and
  `Inner/LongTimeSteps.lean` (Steps 2–4).
-/

open Set Filter Topology MeasureTheory Metric
open scoped Gradient ENNReal

@[expose] public section

namespace PerronVariational

namespace LongTime

/-- **Theorem 3.10**, with the additional hypothesis (4.5) `WeakHeatInPos S.U u w` (weak heat
equation in `{u > 0}`), which the paper's proof uses (Step 2) and which holds for the flows of
Theorem 3.9 (proof of Lemma 4.2). See the module docstring. -/
def LongtimeInnerHeatStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (M : ℝ) (E0 : ℝ≥0∞) (C : ℝ) (Cper : ℝ → ℝ → ℝ), E0 ≠ ⊤ →
    ∃ CV : Set (E d) → ℝ, ∀ u w χ : E d × ℝ → ℝ,
      IsParaInnerVarSolution S.U S.Q u w χ → WeakHeatInPos S.U u w →
      (∀ p ∈ UInf S.U, u p ≤ M) →
      (MonotoneInTime u S.U (Ioi 0) ∨ AntitoneInTime u S.U (Ioi 0)) →
      DissipationIneq S.U S.Q u w χ E0 → InteriorLipEst S.U u C →
      WeightedPerimeterEst S.U χ Cper →
      ∃ uInf : E d → ℝ, TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop S.U ∧
        ∃ (t : ℕ → ℝ) (χInf : E d → ℝ), Tendsto t atTop atTop ∧
          TendstoLpLoc 2 volume S.U (fun i x ↦ gradₓ u (x, t i)) (∇ uInf) atTop ∧
          TendstoLpLoc 1 volume S.U (fun i x ↦ χ (x, t i)) χInf atTop ∧
          IsInnerVarSolution S.U S.Q uInf χInf ∧
          (∀ (x : E d) (r : ℝ), 0 < r → r ≤ 1 → ball x (2 * r) ⊆ S.U →
            ∀ M' : ℝ, (∀ y ∈ ball x (2 * r), |uInf y| ≤ M') →
              ∀ y ∈ ball x r, ‖∇ uInf y‖ ≤ C * (M' / r + 1)) ∧
          ∀ V : Set (E d), CompactlyContained V S.U →
            totalVariationOn V χInf ≤ ENNReal.ofReal (CV V)

private theorem two_pow_mul_ofReal (k : ℕ) (c : ℝ) :
    (2 : ℝ≥0∞) ^ (k + 3) * ENNReal.ofReal c = ENNReal.ofReal (2 ^ (k + 3) * max c 0) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  congr 1
  rcases le_total c 0 with hc | hc
  · rw [max_eq_right hc, ENNReal.ofReal_of_nonpos hc, ENNReal.ofReal_zero]
  · rw [max_eq_left hc]

/-- The complement of the domain is nonempty (`U` is bounded, `d ≥ 2`). -/
theorem setting_compl_nonempty {d : ℕ} (S : Setting d) : S.Uᶜ.Nonempty := by
  haveI : Nonempty (Fin d) := ⟨⟨0, by have := S.two_le; omega⟩⟩
  by_contra h
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
  exact NormedSpace.unbounded_univ ℝ (E d) (h ▸ S.isBounded)

/-- **Theorem 3.10** (with the weak heat equation hypothesis), assembled from Steps 1–4. -/
theorem longtime_innerVar_of_weakHeat : LongtimeInnerHeatStatement := by
  intro d S M E0 C Cper _hE0
  obtain ⟨R, Cχ, hR, hperim⟩ := perimeter_slices S Cper
  classical
  let kOf : Set (E d) → ℕ := fun V ↦ if h : ∃ k, V ⊆ innerSet S.U k then Nat.find h else 0
  refine ⟨fun V ↦ 2 ^ (kOf V + 3) * max (Cχ (kOf V)) 0, ?_⟩
  intro u w χ hsol hheat hM hmono hdiss hlip hper
  -- Step 1: the locally uniform limit
  obtain ⟨uInf, hconv, hnn, hlocLip⟩ :=
    exists_tendstoLocallyUniformlyOn S.isOpen hsol hM hmono hlip
  refine ⟨uInf, hconv, ?_⟩
  -- the null set of bad times
  obtain ⟨-, G, hGm, hGfin, hGeq⟩ := ae_memL2_slice_and_exists_wSlice hsol
  have hae := (ae_isGoodSlice S.isOpen hsol (locallyLipschitzOn_Q_sq S) hdiss hheat).and hGeq
  rw [ae_restrict_iff' measurableSet_Ioi] at hae
  set N := {t : ℝ | ¬ (t ∈ Ioi 0 → IsGoodSlice S.U S.Q u w χ E0 t ∧
    ∫⁻ x in S.U, ENNReal.ofReal (w (x, t) ^ 2) = G t)} with hN_def
  have hN : volume N = 0 := ae_iff.1 hae
  -- Step 3: selection of good times
  choose F hFm hFle hFint using hperim u w χ hsol hper
  let f : ℕ → ℝ → ℝ≥0∞ := fun k ↦ if k = 0 then G else F (k - 1)
  have hfm : ∀ k, AEMeasurable (f k) := fun k ↦ by
    by_cases hk : k = 0
    · simpa [f, hk] using hGm.aemeasurable
    · simpa [f, hk] using (hFm (k - 1)).aemeasurable
  obtain ⟨s, hsI, hsN, hsf⟩ :=
    GoodTimes.exists_good_times_seq (fun i : ℕ ↦ (i : ℝ) + R) hN f hfm
  have hsge : ∀ i : ℕ, (i : ℝ) < s i := fun i ↦ by linarith [(hsI i).1]
  have hspos : ∀ i, 0 < s i := fun i ↦ lt_of_le_of_lt (Nat.cast_nonneg i) (hsge i)
  have hsgood : ∀ i, IsGoodSlice S.U S.Q u w χ E0 (s i) ∧
      ∫⁻ x in S.U, ENNReal.ofReal (w (x, s i) ^ 2) = G (s i) := fun i ↦ by
    have := hsN i
    simp only [hN_def, mem_setOf_eq, not_not] at this
    exact this (hspos i)
  have hstend : Tendsto s atTop atTop :=
    tendsto_atTop_mono (fun i ↦ (hsge i).le) tendsto_natCast_atTop_atTop
  have hw0 : Tendsto (fun i ↦ ∫⁻ x in S.U, ENNReal.ofReal (w (x, s i) ^ 2)) atTop (𝓝 0) := by
    have h1 := GoodTimes.tendsto_setLIntegral_Ioo_zero hGfin (a := fun i : ℕ ↦ (i : ℝ) + R)
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.pow_ne_top
      ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ^ (0 + 2) ≠ ⊤))
    rw [mul_zero] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun i ↦ bot_le)
      fun i ↦ ?_
    rw [(hsgood i).2]
    simpa [f] using hsf i 0
  have hseq : IsGoodSeq S.U S.Q u w χ E0 uInf s := ⟨hstend, fun i ↦ (hsgood i).1, hw0, hconv⟩
  -- perimeter bounds along the good times
  have hTVk : ∀ i k, totalVariationOn (innerSet S.U k) (fun x ↦ χ (x, s i)) ≤
      2 ^ (k + 3) * ENNReal.ofReal (Cχ k) := by
    intro i k
    calc _ ≤ F k (s i) := hFle k (s i) (hspos i)
      _ ≤ 2 ^ (k + 1 + 2) * ∫⁻ t in Ioo ((i : ℝ) + R) ((i : ℝ) + R + 1), F k t := by
        simpa [f] using hsf i (k + 1)
      _ ≤ 2 ^ (k + 3) * ENNReal.ofReal (Cχ k) := by
        rw [show k + 1 + 2 = k + 3 by ring]
        gcongr
        exact hFint k i
  have hne := setting_compl_nonempty S
  have hmeasχ : ∀ t, Measurable (fun x ↦ χ (x, t)) := fun t ↦
    hsol.meas.comp (measurable_id.prodMk measurable_const)
  -- BV compactness
  obtain ⟨φ, hφ, χ₀, hχ₀m, hχ₀⟩ := bv_select S.isOpen (fun n x ↦ χ (x, s n))
    (fun n ↦ hmeasχ _)
    (fun n x hx ↦ by
      rcases hsol.zero_one (x, s n) (mk_mem_prod hx (hspos n)) with h | h <;> simp [h])
    fun V _ hV ↦ by
      obtain ⟨k, hk⟩ := exists_subset_innerSet S.isOpen hne hV
      exact ⟨2 ^ (k + 3) * max (Cχ k) 0, fun n ↦ (totalVariationOn_mono hk _).trans
        ((hTVk n k).trans (two_pow_mul_ofReal k (Cχ k)).le)⟩
  -- `χ_∞`: a `{0, 1}`-valued Borel representative
  have hvals := ae_zero_or_one_of_tendstoLpLoc S.isOpen (fun n x ↦ χ (x, s (φ n)))
    (fun n ↦ hmeasχ _) (fun n x hx ↦ hsol.zero_one _ (mk_mem_prod hx (hspos _))) hχ₀m hχ₀
  set χInf : E d → ℝ := fun x ↦ if χ₀ x = 1 then 1 else 0 with hχInf_def
  have hχInfm : Measurable χInf :=
    Measurable.ite (hχ₀m (measurableSet_singleton 1)) measurable_const measurable_const
  have hχae : ∀ᵐ x ∂(volume.restrict S.U), χInf x = χ₀ x :=
    hvals.mono fun x hx ↦ by rcases hx with h | h <;> simp [χInf, h]
  have hχconv : TendstoLpLoc 1 volume S.U (fun n x ↦ χ (x, s (φ n))) χInf atTop :=
    fun K hK hKc ↦ (hχ₀ K hK hKc).congr' (Eventually.of_forall fun n ↦ eLpNorm_congr_ae
      ((ae_restrict_of_ae_restrict_of_subset hK hχae).mono fun x hx ↦ by simp [hx]))
  have hχInfb : ∀ x, |χInf x| ≤ 1 := fun x ↦ by by_cases h : χ₀ x = 1 <;> simp [χInf, h]
  -- Steps 2 and 4 along the subsequence
  have hseq' : IsGoodSeq S.U S.Q u w χ E0 uInf (s ∘ φ) :=
    ⟨hstend.comp hφ.tendsto_atTop, fun n ↦ hseq.good _, hw0.comp hφ.tendsto_atTop, hconv⟩
  have hharm := harmonic_limit S hsol hlocLip hseq'
  have hgrad := strong_grad S hsol hlip hM hlocLip hseq'
  refine ⟨s ∘ φ, χInf, hseq'.tendsto, hgrad, hχconv, ?_,
    norm_gradient_le_of_tendsto S.isOpen hsol hmono hlip hconv, ?_⟩
  · exact
      { nonneg := hnn
        locLip := hlocLip
        c2 := hharm.1
        harmonic := hharm.2
        meas := hχInfm
        zero_one := fun x _ ↦ by by_cases h : χ₀ x = 1 <;> simp [χInf, h]
        pos_le := pos_le_limit S hseq' hlocLip hχconv hχInfm
        stationary := innerVar_lipschitz S hlocLip hχInfm hχInfb
          (innerVar_limit S hsol hlip hM hseq' hgrad hχconv hχInfm) }
  · -- (3.15): lower semicontinuity of the total variation
    intro V hV
    have hex : ∃ k, V ⊆ innerSet S.U k := exists_subset_innerSet S.isOpen hne hV
    have hk : kOf V = Nat.find hex := dif_pos hex
    have hVk : V ⊆ innerSet S.U (Nat.find hex) := Nat.find_spec hex
    have hΩ := isOpen_innerSet S.isOpen (Nat.find hex)
    have hloc : ∀ n, LocallyIntegrableOn (fun x ↦ χ (x, s (φ n))) (innerSet S.U (Nat.find hex))
        volume := fun n ↦ locallyIntegrableOn_of_bounded hΩ.measurableSet (hmeasχ _) 1
      fun x hx ↦ by
        rcases hsol.zero_one (x, s (φ n)) (mk_mem_prod (innerSet_subset _ _ hx) (hspos _))
          with h | h <;> simp [h]
    calc totalVariationOn V χInf ≤ totalVariationOn (innerSet S.U (Nat.find hex)) χInf :=
          totalVariationOn_mono hVk _
      _ ≤ liminf (fun n ↦ totalVariationOn (innerSet S.U (Nat.find hex))
            (fun x ↦ χ (x, s (φ n)))) atTop :=
          Registry.weightedTV_le_liminf hΩ 1 _ _ hloc
            (locallyIntegrableOn_of_bounded hΩ.measurableSet hχInfm 1 fun x _ ↦ hχInfb x)
            (tendstoLpLoc_mono hχconv (innerSet_subset _ _))
      _ ≤ 2 ^ (Nat.find hex + 3) * ENNReal.ofReal (Cχ (Nat.find hex)) :=
          liminf_le_of_frequently_le' (Frequently.of_forall fun n ↦ hTVk (φ n) _)
      _ = ENNReal.ofReal (2 ^ (kOf V + 3) * max (Cχ (kOf V)) 0) := by
          rw [hk]; exact two_pow_mul_ofReal _ _

end LongTime

/-- **Theorem 3.10**, in the form `LongtimeInnerStatement` (with the weak heat equation
hypothesis (4.5), see the module docstring of `Inner/LongTime.lean`). -/
theorem longtime_innerVar : LongtimeInnerStatement :=
  LongTime.longtime_innerVar_of_weakHeat

end PerronVariational

end
