/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.TimeLocalize
import GMTFoundations.Sobolev.Cutoff
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import PerronVariational.Inner.LongTimeUniform
import PerronVariational.Inner.PerimeterSlices
import PerronVariational.Inner.StationaryLimit
import PerronVariational.Inner.Truncation
import PerronVariational.Inner.WeakHarmonic
import PerronVariational.Registry.Elliptic
import PerronVariational.Registry.FunctionalAnalysis

/-!
# Long-time limit, Steps 2–4: sub-lemmas

Proof of **Theorem 3.10** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. The statements
below are the named sub-lemmas of the assembly
`PerronVariational.LongTime.longtime_innerVar_of_weakHeat` (file `Inner/LongTime.lean`).

## Main definitions

* `PerronVariational.LongTime.innerSet`: the exhaustion `U_k = {x ∈ U : dist(x, ∂U) > 1/(k+1)}`
  (the paper's Step 3 uses `1/k`).
* `PerronVariational.LongTime.IsGoodSeq`: a sequence of good times `sₙ → ∞` (Step 3) along which
  `∫_U |∂ₜu(sₙ)|² → 0` ((4.13)).

## Main results

* `perimeter_slices` (Step 3, from (3.13)): bounds `∫_{(i,i+1)} ∫_{U_k} |∇χ(t)| dt ≤ C_k`
  (slicing of the partial variation, `Inner/PerimeterSlices.lean`).
* `bv_select` (Step 3): BV compactness with a measurable limit (from gmt-foundations v0.1.0).
* `ae_zero_or_one_of_tendstoLpLoc`: `L¹_loc` limits of `{0, 1}`-valued functions are
  `{0, 1}`-valued a.e.
* `weakHarmonic_limit`, `harmonic_limit` (Step 2): `u_∞` is harmonic in `{u_∞ > 0}` (weak form
  by integration by parts and uniform convergence, then Weyl's lemma, from
  viscosity-solution-theory v0.2.0).
* `strong_grad` (Step 2): `∇u(sₙ) → ∇u_∞` in `L²_loc(U)`.
* `pos_le_limit` (Step 4): `1_{u_∞ > 0} ≤ χ_∞` a.e.
* `innerVar_limit` (Step 4): (2.5) for `ξ ∈ C¹_c(U)`.
* `innerVar_lipschitz` (Definition 2.8(iv) needs Lipschitz `ξ`): density of translated bumps.

The time-independent parts of `strong_grad`, `pos_le_limit`, `innerVar_limit`,
`innerVar_lipschitz` and `locallyLipschitzOn_Q_sq` are the stationary core lemmas of
`Inner/StationaryLimit.lean`, shared with the compactness of inner variational solutions
(Lemma 2.10, `Inner/InnerVarCompactness.lean`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped Gradient Laplacian ENNReal ContDiff

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-! ### The exhaustion `U_k` and elementary facts -/

/-- The exhaustion `U_k = {x ∈ U : dist(x, Uᶜ) > 1/(k+1)}` (Step 3 of the proof of
Theorem 3.10). -/
def innerSet (U : Set (E d)) (k : ℕ) : Set (E d) := {x ∈ U | ((k : ℝ) + 1)⁻¹ < infDist x Uᶜ}

theorem innerSet_subset (U : Set (E d)) (k : ℕ) : innerSet U k ⊆ U := fun _ hx ↦ hx.1

theorem isOpen_innerSet {U : Set (E d)} (hU : IsOpen U) (k : ℕ) : IsOpen (innerSet U k) :=
  hU.inter (isOpen_lt continuous_const (continuous_infDist_pt _))

/-- Every `V ⊂⊂ U` lies in some `U_k`. -/
theorem exists_subset_innerSet {U V : Set (E d)} (hU : IsOpen U) (hne : Uᶜ.Nonempty)
    (hV : CompactlyContained V U) : ∃ k, V ⊆ innerSet U k := by
  rcases (closure V).eq_empty_or_nonempty with h | h
  · exact ⟨0, fun x hx ↦ absurd (h ▸ subset_closure hx : x ∈ (∅ : Set (E d))) (notMem_empty x)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hV.1.exists_isMinOn h (continuous_infDist_pt Uᶜ).continuousOn
  have hpos : 0 < infDist x₀ Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 fun h' ↦ h' (hV.2 hx₀)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  refine ⟨k, fun x hx ↦ ⟨hV.2 (subset_closure hx), ?_⟩⟩
  calc ((k : ℝ) + 1)⁻¹ = 1 / ((k : ℝ) + 1) := (one_div _).symm
    _ < infDist x₀ Uᶜ := hk
    _ ≤ infDist x Uᶜ := hmin (subset_closure hx)

/-- Monotonicity of the total variation in the domain. -/
theorem totalVariationOn_mono {V W : Set (E d)} (hVW : V ⊆ W) (χ : E d → ℝ) :
    totalVariationOn V χ ≤ totalVariationOn W χ := by
  unfold totalVariationOn weightedTV
  refine iSup₂_le fun ψ hψ ↦ le_iSup₂_of_le (f := fun ψ (_ : IsTVTestField W 1 ψ) ↦
    ENNReal.ofReal (∫ x in W, χ x * divergence ψ x)) ψ
    ⟨hψ.1, hψ.2.1, hψ.2.2.1.trans hVW, hψ.2.2.2⟩ (le_of_eq ?_)
  have hvan : ∀ A : Set (E d), tsupport ψ ⊆ A → ∀ x, x ∉ A → χ x * divergence ψ x = 0 :=
    fun A hA x hx ↦ by
      simp [divergence, fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hA h))]
  beta_reduce
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hvan V hψ.2.2.1),
    setIntegral_eq_integral_of_forall_compl_eq_zero (hvan W (hψ.2.2.1.trans hVW))]

theorem tendstoLpLoc_mono {X F ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [NormedAddCommGroup F] {p : ℝ≥0∞} {μ : Measure X} {Ω Ω' : Set X} {f : ι → X → F}
    {f₀ : X → F} {l : Filter ι} (h : TendstoLpLoc p μ Ω f f₀ l) (hsub : Ω' ⊆ Ω) :
    TendstoLpLoc p μ Ω' f f₀ l :=
  fun K hK hKc ↦ h K (hK.trans hsub) hKc

/-- A measurable function bounded on a measurable set `s` is locally integrable on `s`. -/
theorem locallyIntegrableOn_of_bounded {s : Set (E d)} (hs : MeasurableSet s) {f : E d → ℝ}
    (hf : Measurable f) (B : ℝ) (hB : ∀ x ∈ s, |f x| ≤ B) : LocallyIntegrableOn f s volume :=
  fun x _ ↦ ⟨s ∩ ball x 1, inter_mem_nhdsWithin s (ball_mem_nhds x one_pos),
    IntegrableOn.of_bound ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top)
      hf.aestronglyMeasurable B
      ((ae_restrict_mem (hs.inter measurableSet_ball)).mono fun y hy ↦ hB y hy.1)⟩

/-! ### Step 3: perimeter bounds on time slices and BV compactness -/

/-- **Perimeter bounds on unit time intervals** (Step 3, from (3.13)). The paper lets the constant
of (3.13) depend on `T_η = sup {t : (x, t) ∈ spt η}`, which is too weak for the bound "independent
of `t`" claimed in Step 3; here (3.13) is used in the form `WeightedPerimeterEst`, where the
constant depends on the time length `ℓ_η` of `spt η` instead, which is what the proof of (3.13)
gives. Depending only on the setting and on the function `Cper` of (3.13), there are a time offset
`R ≥ 0` and constants `C_k` such that for every parabolic inner variational solution satisfying
(3.13), and every `k`, the function `t ↦ ∫_{U_k} |∇χ(·, t)|` is dominated on `(0, ∞)` by a
measurable `F` with `∫_{(i+R, i+R+1)} F ≤ C_k` for all `i ∈ ℕ`.

Proof sketch: apply (3.13) to `η(x, t) = φ_k(x) ψ(t - i - R)` with `φ_k ∈ C¹_c(U)`, `φ_k = 1`
on `U_k`, `ψ ∈ C¹_c((-3/2, 5/2))`, `ψ = 1` on `[-1/2, 3/2]`; for `R = diam U + 2` the quantities
`d_η` (the lateral distance of `spt φ_k`), `ℓ_η` and `‖η‖_{L²H¹}` do not depend on `i`. Then
`∫ ψ(t) ∫_{U_k} |∇χ(t)| dt ≤ ∫ η |∇ₓχ|` (slicing of the partial variation, with `F` the
supremum over a countable dense family of test fields). -/
theorem perimeter_slices (S : Setting d) (Cper : ℝ → ℝ → ℝ) :
    ∃ (R : ℝ) (Cχ : ℕ → ℝ), 0 ≤ R ∧ ∀ u w χ : E d × ℝ → ℝ,
      IsParaInnerVarSolution S.U S.Q u w χ → WeightedPerimeterEst S.U χ Cper →
      ∀ k : ℕ, ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
        (∀ t, 0 < t → totalVariationOn (innerSet S.U k) (fun x ↦ χ (x, t)) ≤ F t) ∧
        ∀ i : ℕ, ∫⁻ t in Ioo ((i : ℝ) + R) ((i : ℝ) + R + 1), F t ≤ ENNReal.ofReal (Cχ k) := by
  classical
  set U := S.U
  have hUc : Uᶜ.Nonempty := by
    have : Nonempty (Fin d) := ⟨⟨0, by have := S.two_le; omega⟩⟩
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    exact NormedSpace.unbounded_univ ℝ (E d) (h ▸ S.isBounded)
  have hKc : ∀ k, IsCompact (closure (innerSet U k)) := fun k ↦
    (S.isBounded.subset (innerSet_subset U k)).isCompact_closure
  have hKU : ∀ k, closure (innerSet U k) ⊆ U := by
    intro k
    refine (closure_minimal (fun x hx ↦ hx.2.le)
      (isClosed_le continuous_const (continuous_infDist_pt _))).trans fun x hx ↦ ?_
    by_contra hxU
    have h0 : infDist x Uᶜ = 0 := infDist_zero_of_mem hxU
    have : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    simp only [Set.mem_ofPred_eq] at hx
    linarith
  choose θ hθ using fun k ↦ GMTFoundations.exists_smooth_cutoff (hKc k) S.isOpen (hKU k)
  have hθ1 : ∀ k, ContDiff ℝ 1 (θ k) := fun k ↦ (hθ k).1.of_le (by exact_mod_cast le_top)
  set R : ℝ := Metric.diam U + 2 with hR
  have hdiam : 0 ≤ Metric.diam U := Metric.diam_nonneg
  set c₀ : ℝ := R + 1 / 2 with hc₀
  refine ⟨R, fun k ↦ Cper (weightDist U (prodWeight (θ k) c₀))
    (weightTimeLength (prodWeight (θ k) c₀)) * l2H1Norm U (prodWeight (θ k) c₀), by positivity,
    ?_⟩
  intro u w χ hsol hper k
  obtain ⟨φ, hφ0, hφ, hdense⟩ := exists_TV_family (innerSet U k)
  have hχ1 : ∀ p ∈ UInf U, |χ p| ≤ 1 := fun p hp ↦ by
    rcases hsol.zero_one p hp with h | h <;> simp [h]
  refine ⟨sliceTV χ φ, measurable_sliceTV hsol.meas fun j ↦ (hφ j).1, fun t ht ↦
    totalVariationOn_le_sliceTV (isOpen_innerSet S.isOpen k).measurableSet
      (innerSet_subset U k) hsol.meas hχ1 hφ hdense ht, fun i ↦ ?_⟩
  have hi : (0 : ℝ) ≤ i := i.cast_nonneg
  set c : ℝ := (i : ℝ) + R + 1 / 2 with hc
  have hη : ∀ x ∈ innerSet U k, ∀ t ∈ Icc ((i : ℝ) + R - 1 / 4) ((i : ℝ) + R + 1 + 1 / 4),
      1 ≤ prodWeight (θ k) c (x, t) := by
    intro x hx t ht
    have h1 : θ k x = 1 := (hθ k).2.2.2.2 x (subset_closure hx)
    have h2 : timeCut c t = 1 := by
      refine (timeCut c).one_of_mem_closedBall ?_
      change t ∈ closedBall c 1
      rw [Real.closedBall_eq_Icc]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp [prodWeight, h1, h2]
  calc ∫⁻ t in Ioo ((i : ℝ) + R) ((i : ℝ) + R + 1), sliceTV χ φ t
      ≤ weightedTVₓ (UInf U) (prodWeight (θ k) c) χ :=
        setLIntegral_sliceTV_le (innerSet_subset U k) hsol.meas hχ1 hφ hφ0 (by linarith)
          (fun p ↦ mul_nonneg ((hθ k).2.2.2.1 _).1 (timeCut c).nonneg) hη
    _ ≤ ENNReal.ofReal (Cper (weightDist U (prodWeight (θ k) c))
          (weightTimeLength (prodWeight (θ k) c)) * l2H1Norm U (prodWeight (θ k) c)) :=
        hper _ (isPerimeterWeight_prodWeight (hθ1 k) (hθ k).2.1 (hθ k).2.2.1
          (fun x ↦ ((hθ k).2.2.2.1 x).1) (by linarith))
    _ = _ := by
      beta_reduce
      rw [weightDist_prodWeight (U := U) S.isBounded hUc (hθ k).2.2.1 (by linarith),
        weightDist_prodWeight (U := U) S.isBounded hUc (hθ k).2.2.1 (by linarith),
        weightTimeLength_prodWeight, weightTimeLength_prodWeight,
        l2H1Norm_prodWeight (U := U) ((hθ1 k).differentiable one_ne_zero) (by linarith),
        l2H1Norm_prodWeight (U := U) ((hθ1 k).differentiable one_ne_zero) (by linarith)]

/-- **BV compactness in `L¹_loc` with a measurable limit** (Step 3; BV compactness from
gmt-foundations v0.1.0, see L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation
and Free Discontinuity Problems*, Oxford Univ. Press, 2000, Theorem 3.23),
specialized to measurable `χₙ` with `|χₙ| ≤ 1` on `U`. -/
theorem bv_select {U : Set (E d)} (hU : IsOpen U) (χ : ℕ → E d → ℝ)
    (hmeas : ∀ n, Measurable (χ n)) (hbdd : ∀ n, ∀ x ∈ U, |χ n x| ≤ 1)
    (hTV : ∀ V, IsOpen V → CompactlyContained V U → ∃ P : ℝ, ∀ n,
      totalVariationOn V (χ n) ≤ ENNReal.ofReal P) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀ : E d → ℝ, Measurable χ₀ ∧
      TendstoLpLoc 1 volume U (fun n ↦ χ (φ n)) χ₀ atTop :=
  Registry.exists_tendstoLpLoc_subseq_of_TV hU χ (fun n ↦ (hmeas n).aestronglyMeasurable)
    ⟨1, hbdd⟩ hTV

/-- `L¹_loc` limits of `{0, 1}`-valued functions are `{0, 1}`-valued a.e. (a.e. convergence of
a subsequence on each compact set). -/
theorem ae_zero_or_one_of_tendstoLpLoc {U : Set (E d)} (hU : IsOpen U) (χ : ℕ → E d → ℝ)
    (_hmeas : ∀ n, Measurable (χ n)) (hval : ∀ n, ∀ x ∈ U, χ n x = 0 ∨ χ n x = 1)
    {χ₀ : E d → ℝ} (_hχ₀ : Measurable χ₀) (hconv : TendstoLpLoc 1 volume U χ χ₀ atTop) :
    ∀ᵐ x ∂(volume.restrict U), χ₀ x = 0 ∨ χ₀ x = 1 := by
  refine StationaryLimit.ae_restrict_of_forall_isCompact hU fun K hKU hK ↦ ?_
  have hm : TendstoInMeasure (volume.restrict K) χ atTop χ₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (hconv K hKU hK)
  obtain ⟨ns, -, hae⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hae, ae_restrict_mem hK.measurableSet] with x hx hxK
  have hclosed : IsClosed ({0, 1} : Set ℝ) := (Set.toFinite _).isClosed
  have := hclosed.mem_of_tendsto hx (Eventually.of_forall fun n ↦ hval (ns n) x (hKU hxK))
  simpa using this

/-! ### Good sequences of times -/

/-- A sequence of good times `sₙ → ∞` (Step 3) along which `∫_U |∂ₜu(sₙ)|² → 0`
((4.13)), for a flow converging locally uniformly to `u_∞`. -/
structure IsGoodSeq (U : Set (E d)) (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (E0 : ℝ≥0∞)
    (uInf : E d → ℝ) (s : ℕ → ℝ) : Prop where
  tendsto : Tendsto s atTop atTop
  good : ∀ n, IsGoodSlice U Q u w χ E0 (s n)
  w_zero : Tendsto (fun n ↦ ∫⁻ x in U, ENNReal.ofReal (w (x, s n) ^ 2)) atTop (𝓝 0)
  conv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U

section Steps

variable {u w χ : E d × ℝ → ℝ} {E0 : ℝ≥0∞} {uInf : E d → ℝ} {s : ℕ → ℝ} {C M : ℝ}

/-- **`u_∞` is weakly harmonic in `{u_∞ > 0}`** (Step 2). For `φ ∈ C_c^∞` with
support in `{u_∞ > 0}`, eventually `spt φ ⊆ {u(·, sₙ) > 0}` (local uniform convergence), so the
slice heat equation gives `∫ ∂ₜu(sₙ) φ = -∫ ∇u(sₙ) · ∇φ`; the left side tends to `0` by (4.13) and
the right side to `-∫ ∇u_∞ · ∇φ`: integrating by parts, `∫ ∇u(sₙ) · ∇φ = -∫ u(sₙ) Δφ`, which
converges by the uniform convergence `u(sₙ) → u_∞` on `spt φ`. -/
theorem weakHarmonic_limit (S : Setting d) (h : IsParaInnerVarSolution S.U S.Q u w χ)
    (huInf : LocallyLipschitzOn S.U uInf) (hs : IsGoodSeq S.U S.Q u w χ E0 uInf s) :
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ posSet uInf S.U →
      ∫ x in posSet uInf S.U, inner ℝ (∇ uInf x) (∇ φ x) = 0 := by
  intro φ hφ hφc hφW
  set K := tsupport φ
  have hWU : posSet uInf S.U ⊆ S.U := fun x hx ↦ hx.1
  have hKU : K ⊆ S.U := hφW.trans hWU
  have hUm : MeasurableSet S.U := S.isOpen.measurableSet
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hunif : TendstoUniformlyOn (fun n x ↦ u (x, s n)) uInf atTop K :=
    TendstoUniformlyOn.comp_seq ((tendstoLocallyUniformlyOn_iff_forall_isCompact S.isOpen).1
      hs.conv K hKU hφc.isCompact) hs.tendsto
  have hposev : ∀ᶠ n in atTop, ∀ x ∈ K, 0 < u (x, s n) :=
    eventually_forall_pos_of_tendstoUniformlyOn hφc.isCompact (huInf.continuousOn.mono hKU)
      (fun x hx ↦ (hφW hx).2) hunif
  -- eventually, `∫_U u(sₙ) Δφ = ∫_U ∂ₜu(sₙ) φ`
  have hkey : ∀ᶠ n in atTop, ∫ x in S.U, u (x, s n) * coordLap φ x =
      ∫ x in S.U, w (x, s n) * φ x := by
    filter_upwards [hposev] with n hn
    have hg := hs.good n
    have hheat := hg.heat φ (ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)) hφc
      fun x hx ↦ ⟨hKU hx, hn x hx⟩
    have hibp := integral_inner_gradient_eq_neg S.isOpen (locallyLipschitzOn_slice h hg.pos)
      hφ2 hφc hKU
    change ∫ x in S.U, inner ℝ (gradₓ u (x, s n)) (∇ φ x) = _ at hibp
    rw [hheat, hibp, neg_neg]
  -- the two limits
  have hlim1 : Tendsto (fun n ↦ ∫ x in S.U, w (x, s n) * φ x) atTop (𝓝 0) :=
    tendsto_integral_mul_of_lintegral_sq (fun n ↦ (hs.good n).memL2.aestronglyMeasurable) hs.w_zero
      ((hφ.continuous.memLp_of_hasCompactSupport hφc).restrict _)
  have hlim2 : Tendsto (fun n ↦ ∫ x in S.U, u (x, s n) * coordLap φ x) atTop
      (𝓝 (∫ x in S.U, uInf x * coordLap φ x)) := by
    have hLK : tsupport (coordLap φ) ⊆ K := tsupport_coordLap_subset φ
    refine tendsto_setIntegral_mul_of_tendstoUniformlyOn hUm (continuous_coordLap hφ2)
      (hasCompactSupport_coordLap hφc) (hLK.trans hKU) (Eventually.of_forall fun n ↦ ?_)
      (huInf.continuousOn.mono (hLK.trans hKU)) (hunif.mono hLK)
    exact (continuousOn_slice h (hs.good n).pos).mono (hLK.trans hKU)
  have hzero : ∫ x in S.U, uInf x * coordLap φ x = 0 :=
    tendsto_nhds_unique hlim2 (hlim1.congr' (hkey.mono fun n hn ↦ hn.symm))
  rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUm hWU fun x hx ↦ by
      simp [gradient, fderiv_of_notMem_tsupport ℝ fun h' ↦ hx.2 (hφW h')],
    integral_inner_gradient_eq_neg S.isOpen huInf hφ2 hφc hKU, hzero, neg_zero]

/-- **`u_∞` is harmonic in `{u_∞ > 0}`** (Step 2 and Definition 2.8(i)): from the weak form by
Weyl's lemma (from viscosity-solution-theory v0.2.0), with the weak gradient of a locally
Lipschitz function given by its a.e. gradient (from gmt-foundations v0.1.0). -/
theorem harmonic_limit (S : Setting d) (h : IsParaInnerVarSolution S.U S.Q u w χ)
    (huInf : LocallyLipschitzOn S.U uInf) (hs : IsGoodSeq S.U S.Q u w χ E0 uInf s) :
    ContDiffOn ℝ 2 uInf (posSet uInf S.U) ∧ ∀ x ∈ posSet uInf S.U, Δ uInf x = 0 := by
  have hopen : IsOpen (posSet uInf S.U) :=
    huInf.continuousOn.isOpen_inter_preimage S.isOpen isOpen_Ioi
  have hsub : posSet uInf S.U ⊆ S.U := fun x hx ↦ hx.1
  have hG := (Registry.memH1Loc_gradient_of_locallyLipschitzOn hopen (huInf.mono hsub)).1
  obtain ⟨h1, h2⟩ := Registry.harmonic_of_weakly_harmonic hopen (huInf.continuousOn.mono hsub)
    hG (weakHarmonic_limit S h huInf hs)
  exact ⟨h1.of_le (WithTop.coe_le_coe.2 le_top), h2⟩

/-- **Strong convergence of the gradients** (Step 2): along a good sequence,
`∇u(·, sₙ) → ∇u_∞` in `L²_loc(U)`. Proof: (4.12) with `ζ = η (u(sₙ) - δ)₊` (for `δ` avoiding the
countably many levels of positive measure; `∇u(sₙ) = 0` on `{u(sₙ) = 0}` since `u ≥ 0`) gives
`∫ |∇u(sₙ)|² η = -∫ ∂ₜu(sₙ) u(sₙ) η - ∫ u(sₙ) ∇u(sₙ) · ∇η`; by (4.13), uniform convergence and weak
`L²` convergence of the gradients, the right side tends to `-∫ u_∞ ∇u_∞ · ∇η`, which equals
`∫ |∇u_∞|² η` by the harmonicity of `u_∞` in `{u_∞ > 0}` (same truncation,
`integral_truncation_identity`). With the weak convergence of the cross term
(`tendsto_integral_inner_gradient`), `∫ |∇u(sₙ) - ∇u_∞|² η → 0` for a cutoff `η = 1` on `K`. -/
theorem strong_grad (S : Setting d) (h : IsParaInnerVarSolution S.U S.Q u w χ)
    (hlip : InteriorLipEst S.U u C) (hM : ∀ p ∈ UInf S.U, u p ≤ M)
    (huInf : LocallyLipschitzOn S.U uInf) (hs : IsGoodSeq S.U S.Q u w χ E0 uInf s) :
    TendstoLpLoc 2 volume S.U (fun n x ↦ gradₓ u (x, s n)) (∇ uInf) atTop := by
  have hU := S.isOpen
  have hpos : ∀ n, 0 < s n := fun n ↦ (hs.good n).pos
  let v : ℕ → E d → ℝ := fun n x ↦ u (x, s n)
  have hvL : ∀ n, LocallyLipschitzOn S.U (v n) := fun n ↦ locallyLipschitzOn_slice h (hpos n)
  have hv0 : ∀ n, ∀ x ∈ S.U, 0 ≤ v n x := fun n x hx ↦ h.nonneg _ ⟨hx, hpos n⟩
  have hvM : ∀ n, ∀ x ∈ S.U, v n x ≤ M := fun n x hx ↦ hM _ ⟨hx, hpos n⟩
  -- `u_∞ ≥ 0`
  have hInf0 : ∀ x ∈ S.U, 0 ≤ uInf x := fun x hx ↦
    ge_of_tendsto (hs.conv.tendsto_at hx) ((eventually_gt_atTop 0).mono fun t ht ↦
      h.nonneg _ ⟨hx, ht⟩)
  have hconvK : ∀ K', IsCompact K' → K' ⊆ S.U → TendstoUniformlyOn v uInf atTop K' :=
    fun K' hK' hK'U ↦ TendstoUniformlyOn.comp_seq
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hs.conv K' hK'U hK') hs.tendsto
  have hBF : ∀ K', IsCompact K' → K' ⊆ S.U → ∃ B, ∀ᶠ n in atTop, ∀ x ∈ K', ‖∇ (v n) x‖ ≤ B :=
    fun K' hK' hK'U ↦ by
      obtain ⟨B, T, hB⟩ := exists_bound_gradₓ_of_interiorLipEst hU hlip h.nonneg hM hK' hK'U
      exact ⟨B, (hs.tendsto.eventually (eventually_gt_atTop T)).mono fun n hn x hx ↦
        hB _ hn x hx⟩
  change TendstoLpLoc 2 volume S.U (fun n ↦ ∇ (v n)) (∇ uInf) atTop
  refine StationaryLimit.tendstoLpLoc_gradient_of_energy (v := v) (u₀ := uInf) hU hvL huInf
    hconvK hBF
    (fun K' _ hK'U ↦ ⟨M, fun n x hx ↦ abs_le.2
      ⟨by linarith [hv0 n x (hK'U hx), hvM n x (hK'U hx)], hvM n x (hK'U hx)⟩⟩)
    (fun η hηs hηc hηU hη01 ↦ ?_)
    (fun η hηs hηc hηU _ ↦ StationaryLimit.integral_energy_eq_zero hU huInf hInf0
      (weakHarmonic_limit S h huInf hs) (hηs.of_le (by simp)) hηc hηU)
  -- the energy identity for `u(sₙ)` (truncation, from the slice heat equation)
  have hη1' : ContDiff ℝ 1 η := hηs.of_le (by simp)
  set K'' := tsupport η
  have hK'' : IsCompact K'' := hηc.isCompact
  have hK''m : MeasurableSet K'' := hK''.measurableSet
  have : IsFiniteMeasure (volume.restrict K'') :=
    isFiniteMeasure_restrict.2 hK''.measure_lt_top.ne
  have hid : ∀ n, ∫ x in S.U, w (x, s n) * (v n x * η x) =
      -∫ x in S.U, (‖∇ (v n) x‖ ^ 2 * η x + v n x * inner ℝ (∇ (v n) x) (∇ η x)) := fun n ↦
    integral_truncation_identity hU (hvL n) (hv0 n)
      (fun K' hK' hK'U ↦ by
        have : IsFiniteMeasure (volume.restrict K') :=
          isFiniteMeasure_restrict.2 hK'.measure_lt_top.ne
        exact ((hs.good n).memL2.mono_measure (Measure.restrict_mono hK'U le_rfl)).integrable
          one_le_two)
      (fun ζ hζ hζc hζW ↦ (hs.good n).heat ζ hζ hζc hζW) hη1' hηc hηU
  have hη0 : ∀ x ∉ K'', η x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hηb : ∀ x, ‖η x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_of_nonneg (hη01 x).1]; exact (hη01 x).2
  have hvb : ∀ n, ∀ x ∈ K'', ‖v n x‖ ≤ M := fun n x hx ↦ by
    rw [Real.norm_of_nonneg (hv0 n x (hηU hx))]; exact hvM n x (hηU hx)
  -- `∫ ∂ₜu(sₙ) u(sₙ) η → 0`
  have hlimW : Tendsto (fun n ↦ ∫ x in S.U, w (x, s n) * (v n x * η x)) atTop (𝓝 0) := by
    have hred : ∀ n, ∫ x in S.U, w (x, s n) * (v n x * η x) =
        ∫ x in K'', w (x, s n) * (v n x * η x) := fun n ↦
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hηU fun x hx ↦ by
        simp [hη0 x hx.2]
    simp only [hred]
    refine tendsto_integral_mul_of_lintegral_sq_of_bdd (μ := volume.restrict K'')
      (W := fun n x ↦ w (x, s n)) (Φ := fun n x ↦ v n x * η x)
      (fun n ↦ ((hs.good n).memL2.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono hηU le_rfl)))
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs.w_zero
        (fun _ ↦ bot_le) fun n ↦ lintegral_mono_set hηU) (c := M)
      (Eventually.of_forall fun n ↦ (ae_restrict_mem hK''m).mono fun x hx ↦ ?_)
    rw [norm_mul]
    calc ‖v n x‖ * ‖η x‖ ≤ M * 1 := mul_le_mul (hvb n x hx) (hηb x) (norm_nonneg _)
          ((norm_nonneg _).trans (hvb n x hx))
      _ = M := mul_one M
  have h := hlimW.neg
  rw [neg_zero] at h
  exact h.congr fun n ↦ by rw [hid n, neg_neg]

/-- **`1_{u_∞ > 0} ≤ χ_∞`** (Step 4): on compact subsets of `{u_∞ > 0}`, eventually
`u(·, sₙ) > 0`, hence `χ(·, sₙ) = 1` a.e.; pass to the `L¹` limit. -/
theorem pos_le_limit (S : Setting d)
    (hs : IsGoodSeq S.U S.Q u w χ E0 uInf s) (huInf : LocallyLipschitzOn S.U uInf)
    {χInf : E d → ℝ} (hχ : TendstoLpLoc 1 volume S.U (fun n x ↦ χ (x, s n)) χInf atTop)
    (hχm : Measurable χInf) :
    ∀ᵐ x ∂(volume.restrict S.U), 0 < uInf x → χInf x = 1 :=
  StationaryLimit.ae_pos_imp_eq_one S.isOpen huInf.continuousOn
    (StationaryLimit.tendstoLocallyUniformlyOn_comp hs.conv hs.tendsto)
    (fun n ↦ (hs.good n).pos_le) hχ hχm

/-- `Q²` is locally Lipschitz on `U` (`Q` is Lipschitz and bounded on `Ū`). -/
theorem locallyLipschitzOn_Q_sq (S : Setting d) :
    LocallyLipschitzOn S.U fun y ↦ S.Q y ^ 2 := by
  obtain ⟨L, hL⟩ := S.lip
  exact fun x _ ↦ ⟨_, S.U, self_mem_nhdsWithin, (StationaryLimit.lipschitzOnWith_sq hL
    (fun y hy ↦ S.Qmin_pos.le.trans (S.Q_mem y hy).1) fun y hy ↦ (S.Q_mem y hy).2).mono
    subset_closure⟩

/-- **Passage to the limit in (4.17)** (Step 4): along a good sequence with
`∇u(sₙ) → ∇u_∞` in `L²_loc`, `χ(sₙ) → χ_∞` in `L¹_loc` and `∂ₜu(sₙ) → 0` in `L²(U)`, the
stationary inner variation identity (2.5) holds for `ξ ∈ C¹_c(U; ℝᵈ)`.

Proof: the slice identity (4.17) at `sₙ` reads `∫_K Fₙ = ∫_K 2 ξ · ∇u(sₙ) ∂ₜu(sₙ)` (`K = spt ξ`),
where `Fₙ` is the stationary integrand of `(u(sₙ), χ(sₙ))`. The right side tends to `0`
(Cauchy–Schwarz, with `∇u(sₙ)` bounded on `K` for large times by (3.12)). Along a subsequence,
`∇u(sₙ) → ∇u_∞` and `χ(sₙ) → χ_∞` a.e. on `K`, and `Fₙ` is uniformly bounded on `K`, so
`∫_K Fₙ → ∫_K F_∞` by dominated convergence. -/
theorem innerVar_limit (S : Setting d) (h : IsParaInnerVarSolution S.U S.Q u w χ)
    (hlip : InteriorLipEst S.U u C) (hM : ∀ p ∈ UInf S.U, u p ≤ M)
    (hs : IsGoodSeq S.U S.Q u w χ E0 uInf s) {χInf : E d → ℝ}
    (hgrad : TendstoLpLoc 2 volume S.U (fun n x ↦ gradₓ u (x, s n)) (∇ uInf) atTop)
    (hχ : TendstoLpLoc 1 volume S.U (fun n x ↦ χ (x, s n)) χInf atTop)
    (hχm : Measurable χInf) :
    ∀ ξ : E d → E d, ContDiff ℝ 1 ξ → HasCompactSupport ξ → tsupport ξ ⊆ S.U →
      ∫ x in S.U, innerVarIntegrand S.Q uInf χInf ξ x = 0 := by
  intro ξ hξ hξc hξU
  set K := tsupport ξ with hKdef
  have hK : IsCompact K := hξc.isCompact
  have hKm : MeasurableSet K := hK.measurableSet
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hUm : MeasurableSet S.U := S.isOpen.measurableSet
  have hpos : ∀ n, 0 < s n := fun n ↦ (hs.good n).pos
  have hχsm : ∀ t, Measurable fun x ↦ χ (x, t) := fun t ↦
    h.meas.comp (measurable_id.prodMk measurable_const)
  -- gradient bounds on compact sets for large times, from (3.12)
  have hBF : ∀ K', IsCompact K' → K' ⊆ S.U →
      ∃ B, ∀ᶠ n in atTop, ∀ x ∈ K', ‖gradₓ u (x, s n)‖ ≤ B := fun K' hK' hK'U ↦ by
    obtain ⟨B, T, hB⟩ := exists_bound_gradₓ_of_interiorLipEst S.isOpen hlip h.nonneg hM hK' hK'U
    exact ⟨B, (hs.tendsto.eventually (eventually_gt_atTop T)).mono fun n hn ↦ hB _ hn⟩
  obtain ⟨Cξ, hCξ⟩ := hK.exists_bound_of_continuousOn hξ.continuous.continuousOn
  -- the slice identity (4.17): `∫_U Fₙ = ∫_K Gₙ`
  set F : ℕ → E d → ℝ := fun n x ↦
    innerVarIntegrand S.Q (fun y ↦ u (y, s n)) (fun y ↦ χ (y, s n)) ξ x
  set G : ℕ → E d → ℝ := fun n x ↦ 2 * inner ℝ (ξ x) (gradₓ u (x, s n)) * w (x, s n)
  have hwK : ∀ n, MemLp (fun x ↦ w (x, s n)) 2 (volume.restrict K) := fun n ↦
    (hs.good n).memL2.mono_measure (Measure.restrict_mono hξU le_rfl)
  have hGi : ∀ n, Integrable (G n) (volume.restrict K) := by
    intro n
    obtain ⟨Bn, hBn⟩ := exists_bound_gradₓ_slice h (hpos n) hK hξU
    refine ((hwK n).integrable one_le_two).bdd_mul (c := 2 * (Cξ * Bn)) ?_
      ((ae_restrict_mem hKm).mono fun x hx ↦ ?_)
    · exact (measurable_const.mul (hξ.continuous.measurable.inner
        (measurable_gradₓ_slice u _))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_two]
      gcongr
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hCξ x hx) (hBn x hx) (norm_nonneg _)
        ((norm_nonneg _).trans (hCξ x hx)))
  have hvanS : ∀ n, ∀ x ∈ S.U \ K, sliceInnerVarIntegrand S.Q u w χ (s n) ξ x = 0 :=
    fun n x hx ↦ sliceInnerVarIntegrand_eq_zero _ _ _ _ _ hx.2
  have hFi : ∀ n, Integrable (F n) (volume.restrict K) := by
    intro n
    have hsl := ((hs.good n).innerVar ξ hξ hξc hξU).1.mono_measure
      (Measure.restrict_mono hξU le_rfl)
    exact (hsl.add (hGi n)).congr (Eventually.of_forall fun x ↦ by
      simp [F, G, sliceInnerVarIntegrand])
  have hFG : ∀ n, ∫ x in S.U, F n x = ∫ x in K, G n x := by
    intro n
    have h0 := ((hs.good n).innerVar ξ hξ hξc hξU).2
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUm hξU (hvanS n)] at h0
    have : ∫ x in K, (F n x - G n x) = 0 := h0
    rw [integral_sub (hFi n) (hGi n)] at this
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUm hξU fun x hx ↦
      innerVarIntegrand_eq_zero_of_notMem _ _ _ hx.2]
    linarith
  -- `∫_K Gₙ → 0`
  have hlimG : Tendsto (fun n ↦ ∫ x in K, G n x) atTop (𝓝 0) := by
    obtain ⟨B, hB⟩ := hBF K hK hξU
    have hw0 : Tendsto (fun n ↦ ∫⁻ x in K, ENNReal.ofReal (w (x, s n) ^ 2)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs.w_zero
        (fun _ ↦ bot_le) fun n ↦ lintegral_mono_set hξU
    have hc : ∀ᶠ n in atTop, ∀ᵐ x ∂(volume.restrict K),
        ‖2 * inner ℝ (ξ x) (gradₓ u (x, s n))‖ ≤ 2 * (Cξ * B) := by
      filter_upwards [hB] with n hn
      filter_upwards [ae_restrict_mem hKm] with x hx
      rw [norm_mul, Real.norm_two]
      gcongr
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hCξ x hx) (hn x hx) (norm_nonneg _)
        ((norm_nonneg _).trans (hCξ x hx)))
    refine (tendsto_integral_mul_of_lintegral_sq_of_bdd (fun n ↦ (hwK n).aestronglyMeasurable)
      hw0 hc).congr
      fun n ↦ integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [G]
    ring
  -- `∫_U Fₙ → ∫_U F_∞` (the stationary core)
  have hlimF := StationaryLimit.tendsto_integral_innerVarIntegrand S.isOpen
    (locallyLipschitzOn_Q_sq S) (v := fun n y ↦ u (y, s n)) (χ := fun n y ↦ χ (y, s n))
    (fun n ↦ hχsm (s n)) hχm (fun n x hx ↦ abs_chi_slice_le_one h (hpos n) hx) hBF hgrad hχ
    hξ hξc hξU
  exact tendsto_nhds_unique hlimF (hlimG.congr fun n ↦ (hFG n).symm)

/-- **From `C¹` to Lipschitz test fields** (Definition 2.8(iv) is stated for `ξ ∈ C^{0,1}_c(U)`): if
(2.5) holds for all `ξ ∈ C¹_c(U; ℝᵈ)`, `v` is locally Lipschitz and `χ` is bounded measurable,
then it holds for Lipschitz `ξ` with compact support in `U` (mollify `ξ`: `Dξ_ε → Dξ` a.e. and
boundedly, dominated convergence). -/
theorem innerVar_lipschitz (S : Setting d) {v χ₁ : E d → ℝ} (hv : LocallyLipschitzOn S.U v)
    (hχm : Measurable χ₁) (hχb : ∀ x, |χ₁ x| ≤ 1)
    (hC1 : ∀ ξ : E d → E d, ContDiff ℝ 1 ξ → HasCompactSupport ξ → tsupport ξ ⊆ S.U →
      ∫ x in S.U, innerVarIntegrand S.Q v χ₁ ξ x = 0) :
    ∀ ξ : E d → E d, (∃ K, LipschitzWith K ξ) → HasCompactSupport ξ → tsupport ξ ⊆ S.U →
      ∫ x in S.U, innerVarIntegrand S.Q v χ₁ ξ x = 0 :=
  StationaryLimit.innerVar_lipschitz S.isOpen (locallyLipschitzOn_Q_sq S) hv hχm hχb hC1

end Steps

end LongTime

end PerronVariational

end
