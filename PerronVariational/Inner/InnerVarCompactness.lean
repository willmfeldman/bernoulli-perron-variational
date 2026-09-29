/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.DirectionalStable.Lemma211
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.Algebra.Order.Ring.Star
import PerronVariational.Inner.Compactness
import PerronVariational.Inner.LongTimeSteps
import PerronVariational.Inner.StationaryLimit
import PerronVariational.Main.Directional

/-!
# Compactness of inner variational solutions (Lemma 2.10)

**Lemma 2.10** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. The paper refers its
proof to the first paragraph of the proof of Theorem 9.3 in D. Kriventsov, G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), 545–591, arXiv:2306.10131 (see also Proposition 4.2
in D. Jerison, N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math. Res.
Not. IMRN 2016, no. 19, 5922–5987, doi:10.1093/imrn/rnv339).

The paper assumes bounds on `∇u_k` and on the perimeters of `χ_k` only; here we also assume a
local uniform bound on `u_k`, because without it the lemma is false: `u_k ≡ k`, `χ_k ≡ 1` are
inner variational solutions with `∇u_k = 0` and `∇χ_k = 0` and no convergent subsequence. The
bound holds at every place the paper uses the lemma (see `Registry.innerVar_compactness`).

Proof outline.
1. *Uniform local Lipschitz bounds.* `u_k ≥ 0` is differentiable on `{u_k > 0}` (it is `C²`
   there), so the pointwise bound `|∇u_k| ≤ L` on a ball gives the Lipschitz bound `L` on the
   ball: on a segment from a point of `{u_k > 0}`, apply the mean value inequality up to the first
   zero of `u_k` (`sub_le_of_nonneg_of_norm_fderiv_le`). No Rademacher theorem is needed.
2. *Extraction.* Arzelà–Ascoli (`Inner.exists_tendstoLocallyUniformlyOn_subseq`) for `u_k`, then
   BV compactness (`LongTime.bv_select`, from gmt-foundations v0.1.0) for `χ_k`. The `L¹_loc`
   limit is `{0,1}`-valued a.e.; we modify it on a null set so that it is `{0,1}`-valued everywhere.
3. *Harmonicity* of the limit in its positivity set: `DirectionalStable.harmonic_of_tendsto`
   (weak harmonicity passes to the limit, then Weyl's lemma, from viscosity-solution-theory
   v0.2.0).
4. *Strong `L²_loc` convergence of the gradients* from the energy identities
   `∫ |∇v|² η + v ∇v · ∇η = 0` of `u_k` and of the limit (truncation at small levels,
   `integral_truncation_identity`), by `StationaryLimit.tendstoLpLoc_gradient_of_energy`.
5. *`1_{u > 0} ≤ χ`* from the local uniform convergence and the `L¹_loc` convergence
   (`StationaryLimit.ae_pos_imp_eq_one`).
6. *Inner variation identity* for `C¹_c` fields by dominated convergence
   (`StationaryLimit.tendsto_integral_innerVarIntegrand`), then for Lipschitz fields by density
   (`StationaryLimit.innerVar_lipschitz`).

## Main results

* `InnerVarCompactness.sub_le_of_nonneg_of_norm_fderiv_le`: the Lipschitz bound of step 1.
* `InnerVarCompactness.innerVar_compactness`: the statement of `Registry.innerVar_compactness`
  (Lemma 2.10 with the added bound on `u_k`), verbatim.
-/

open Set Filter Topology MeasureTheory Metric
open scoped Gradient ENNReal ContDiff NNReal Laplacian

@[expose] public section

namespace PerronVariational

namespace InnerVarCompactness

variable {d : ℕ}

/-! ### Step 1: Lipschitz bounds from gradient bounds on the positivity set -/

/-- **Lipschitz bound from the gradient on the positivity set.** Let `u ≥ 0` be continuous on the
convex set `s`, differentiable at every point of `s` where `u > 0`, with `‖Du‖ ≤ L` there. Then
`u x - u y ≤ L ‖x - y‖` for `x, y ∈ s`. (Along the segment from `x ∈ {u > 0}` towards `y`, apply
the mean value inequality up to the first zero of `u`, or up to `y` if there is none.) -/
theorem sub_le_of_nonneg_of_norm_fderiv_le {s : Set (E d)} (hs : Convex ℝ s) {u : E d → ℝ}
    (hc : ContinuousOn u s) (h0 : ∀ x ∈ s, 0 ≤ u x) {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x ∈ s, 0 < u x → DifferentiableAt ℝ u x ∧ ‖fderiv ℝ u x‖ ≤ L) {x y : E d}
    (hx : x ∈ s) (hy : y ∈ s) : u x - u y ≤ L * ‖x - y‖ := by
  have hLxy : 0 ≤ L * ‖x - y‖ := mul_nonneg hL (norm_nonneg _)
  rcases (h0 x hx).eq_or_lt with hx0 | hxpos
  · rw [← hx0]; linarith [h0 y hy]
  set γ : ℝ → E d := fun t ↦ x + t • (y - x) with hγdef
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ s := fun t ht ↦ hs.add_smul_sub_mem hx hy ht
  have hγc : Continuous γ := by fun_prop
  set f : ℝ → ℝ := fun t ↦ u (γ t) with hfdef
  have hfc : ContinuousOn f (Icc 0 1) := hc.comp hγc.continuousOn fun t ht ↦ hγ t ht
  have hf0 : f 0 = u x := by simp [f, γ]
  have hf1 : f 1 = u y := by simp [f, γ]
  have hyx : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
  -- the mean value inequality on `[0, b]` if `f > 0` on `[0, b)`
  have key : ∀ b ∈ Icc (0 : ℝ) 1, (∀ t ∈ Ico 0 b, 0 < f t) →
      |f b - f 0| ≤ L * ‖x - y‖ * b := by
    intro b hb hpos
    have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment (f := f)
      (f' := fun t ↦ fderiv ℝ u (γ t) (y - x)) (C := L * ‖x - y‖)
      (hfc.mono (Icc_subset_Icc le_rfl hb.2)) ?_ ?_ b (right_mem_Icc.2 hb.1)
    · simpa [Real.norm_eq_abs] using hmv
    · intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans hb.2⟩
      have hdiff := (hd _ (hγ t htI) (hpos t ht)).1
      have hγd : HasDerivAt γ (y - x) t := by
        convert ((hasDerivAt_id t).smul_const (y - x)).const_add x using 1
        simp
      exact (hdiff.hasFDerivAt.comp_hasDerivAt t hγd).hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans hb.2⟩
      have hbd := (hd _ (hγ t htI) (hpos t ht)).2
      rw [← hyx]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hbd (norm_nonneg _))
  by_cases hT : ∃ t ∈ Icc (0 : ℝ) 1, f t = 0
  · -- the first zero `t₀` of `f`
    set T := Icc (0 : ℝ) 1 ∩ f ⁻¹' {0} with hTdef
    have hTne : T.Nonempty := by
      obtain ⟨t, ht, hft⟩ := hT
      exact ⟨t, ht, hft⟩
    have hTc : IsClosed T := hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hTb : BddBelow T := ⟨0, fun t ht ↦ ht.1.1⟩
    set t₀ := sInf T
    have ht₀ : t₀ ∈ T := hTc.csInf_mem hTne hTb
    have hpos : ∀ t ∈ Ico 0 t₀, 0 < f t := fun t ht ↦ by
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans ht₀.1.2⟩
      rcases (h0 _ (hγ t htI)).eq_or_lt with h | h
      · exact absurd (csInf_le hTb ⟨htI, h.symm⟩) (not_le.2 ht.2)
      · exact h
    have hk := key t₀ ht₀.1 hpos
    have hft₀ : f t₀ = 0 := ht₀.2
    rw [hft₀, hf0, zero_sub, abs_neg, abs_of_pos hxpos] at hk
    have : L * ‖x - y‖ * t₀ ≤ L * ‖x - y‖ := mul_le_of_le_one_right hLxy ht₀.1.2
    linarith [h0 y hy]
  · push Not at hT
    have hk := key 1 (right_mem_Icc.2 zero_le_one) fun t ht ↦
      lt_of_le_of_ne (h0 _ (hγ t ⟨ht.1, ht.2.le⟩)) (hT t ⟨ht.1, ht.2.le⟩).symm
    rw [hf0, hf1, mul_one] at hk
    linarith [neg_abs_le (u y - u x)]

/-- `|u x - u y| ≤ L ‖x - y‖` under the hypotheses of `sub_le_of_nonneg_of_norm_fderiv_le`. -/
theorem abs_sub_le_of_nonneg_of_norm_fderiv_le {s : Set (E d)} (hs : Convex ℝ s) {u : E d → ℝ}
    (hc : ContinuousOn u s) (h0 : ∀ x ∈ s, 0 ≤ u x) {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x ∈ s, 0 < u x → DifferentiableAt ℝ u x ∧ ‖fderiv ℝ u x‖ ≤ L) {x y : E d}
    (hx : x ∈ s) (hy : y ∈ s) : |u x - u y| ≤ L * ‖x - y‖ := by
  refine abs_le.2 ⟨?_, sub_le_of_nonneg_of_norm_fderiv_le hs hc h0 hL hd hx hy⟩
  have := sub_le_of_nonneg_of_norm_fderiv_le hs hc h0 hL hd hy hx
  rw [norm_sub_rev] at this
  linarith

/-- A compact subset of `U` is compactly contained in `U`. -/
theorem compactlyContained_of_isCompact {U K : Set (E d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    CompactlyContained K U := by
  refine ⟨?_, ?_⟩ <;> rw [hK.isClosed.closure_eq]
  exacts [hK, hKU]

/-- **Uniform local Lipschitz bounds** (step 1): inner variational solutions with locally
uniformly bounded gradients are uniformly locally Lipschitz. -/
theorem unifLocLip {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ} {u χ : ℕ → E d → ℝ}
    (h : ∀ k, IsInnerVarSolution U Q (u k) (χ k))
    (hLip : ∀ V, CompactlyContained V U → ∃ L : ℝ, ∀ k, ∀ x ∈ V, ‖∇ (u k) x‖ ≤ L) :
    DirectionalStable.UnifLocLip U u := by
  intro y hy
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hy
  have hcl : closedBall y (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  obtain ⟨L, hL⟩ := hLip _ (compactlyContained_ball hcl)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 y (mem_ball_self (by linarith)))
  refine ⟨r / 2, by linarith, ball_subset_closedBall.trans hcl, Real.toNNReal L, fun k ↦ ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL0]
  have hBU : ball y (r / 2) ⊆ U := ball_subset_closedBall.trans hcl
  refine abs_sub_le_of_nonneg_of_norm_fderiv_le (convex_ball y (r / 2))
    ((h k).locLip.continuousOn.mono hBU) (fun z hz ↦ (h k).nonneg z (hBU hz)) hL0
    (fun z hz hpos ↦ ⟨?_, ?_⟩) ha hb
  · have hzW : z ∈ posSet (u k) U := ⟨hBU hz, hpos⟩
    exact ((h k).c2.contDiffAt ((isOpen_posSet hU (h k).locLip.continuousOn).mem_nhds
      hzW)).differentiableAt (by norm_num)
  · rw [← GMTFoundations.norm_gradient_eq_norm_fderiv]
    exact hL k z hz

/-! ### Energy identity -/

/-- **Energy identity** for `f ≥ 0`, locally Lipschitz on `U` and (classically) harmonic in
`{f > 0}`: `∫_U |∇f|² η + f ∇f · ∇η = 0` for `η ∈ C¹_c(U)`. -/
theorem integral_energy_eq_zero {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : LocallyLipschitzOn U f) (hf0 : ∀ x ∈ U, 0 ≤ f x)
    (hc2 : ContDiffOn ℝ 2 f (posSet f U)) (hΔ : ∀ x ∈ posSet f U, Δ f x = 0)
    {η : E d → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, (‖∇ f x‖ ^ 2 * η x + f x * inner ℝ (∇ f x) (∇ η x)) = 0 :=
  StationaryLimit.integral_energy_eq_zero hU hf hf0
    (fun _ hφ hφc hφW ↦ DirectionalStable.integral_inner_gradient_eq_zero_of_harmonic
      (hf.continuousOn.isOpen_inter_preimage hU isOpen_Ioi) hc2 hΔ hφ hφc hφW) hη hηc hηU

/-! ### The compactness theorem -/

/-- **Lemma 2.10** (`Registry.innerVar_compactness`), statement verbatim:
compactness of inner variational solutions with locally uniformly bounded values, gradients and
perimeters. -/
theorem innerVar_compactness {U : Set (E d)} {Q : E d → ℝ} (_hd : 2 ≤ d) (hU : IsOpen U)
    (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (u χ : ℕ → E d → ℝ)
    (h : ∀ k, IsInnerVarSolution U Q (u k) (χ k))
    (hbdd : ∀ V, CompactlyContained V U → ∃ M : ℝ, ∀ k, ∀ x ∈ V, |u k x| ≤ M)
    (hLip : ∀ V, CompactlyContained V U → ∃ L : ℝ, ∀ k, ∀ x ∈ V, ‖∇ (u k) x‖ ≤ L)
    (hPer : ∀ V, CompactlyContained V U → ∃ P : ℝ, ∀ k,
      totalVariationOn V (χ k) ≤ ENNReal.ofReal P) :
    ∃ (φ : ℕ → ℕ) (u₀ χ₀ : E d → ℝ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun j ↦ u (φ j)) u₀ atTop U ∧
      TendstoLpLoc 2 volume U (fun j ↦ ∇ (u (φ j))) (∇ u₀) atTop ∧
      TendstoLpLoc 1 volume U (fun j ↦ χ (φ j)) χ₀ atTop ∧
      IsInnerVarSolution U Q u₀ χ₀ := by
  have hUm : MeasurableSet U := hU.measurableSet
  have hULL := unifLocLip hU h hLip
  -- Step 2a: Arzelà–Ascoli for `u_k`
  obtain ⟨φ₁, hφ₁, u₀, -, hconv₁⟩ := Inner.exists_tendstoLocallyUniformlyOn_subseq hU u
    (fun k ↦ (h k).locLip.continuousOn)
    (fun x hx ↦ (hbdd {x} (compactlyContained_of_isCompact isCompact_singleton
      (singleton_subset_iff.2 hx))).imp fun M hM k ↦ hM k x rfl)
    (fun x hx η hη ↦ by
      obtain ⟨ε, hε, -, L, hL⟩ := hULL x hx
      have hδ : 0 < η / (L + 1) := by positivity
      filter_upwards [ball_mem_nhds x (lt_min hε hδ)] with y hy k
      have hy1 : y ∈ ball x ε := ball_subset_ball (min_le_left _ _) hy
      have hy2 : dist y x < η / (L + 1) := lt_of_lt_of_le hy (min_le_right _ _)
      have h1 := (hL k).dist_le_mul y hy1 x (mem_ball_self hε)
      rw [Real.dist_eq] at h1
      calc |u k y - u k x| ≤ L * dist y x := h1
        _ ≤ (L + 1) * dist y x := by gcongr; linarith
        _ < (L + 1) * (η / (L + 1)) := by gcongr
        _ = η := by field_simp)
  -- Step 2b: BV compactness for `χ_k` along the subsequence
  have hχb : ∀ k, ∀ x ∈ U, |χ k x| ≤ 1 := fun k x hx ↦ by
    rcases (h k).zero_one x hx with h0 | h1 <;> simp [*]
  obtain ⟨φ₂, hφ₂, χ₁, hχ₁m, hχ₁⟩ := LongTime.bv_select hU (fun n ↦ χ (φ₁ n))
    (fun n ↦ (h (φ₁ n)).meas) (fun n ↦ hχb (φ₁ n))
    (fun V _ hV ↦ (hPer V hV).imp fun P hP n ↦ hP (φ₁ n))
  set φ := fun j ↦ φ₁ (φ₂ j) with hφdef
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  have hconv : TendstoLocallyUniformlyOn (fun j ↦ u (φ j)) u₀ atTop U :=
    Inner.TendstoLocallyUniformlyOn.comp_tendsto hconv₁ hφ₂.tendsto_atTop
  -- the limit `χ₀`, `{0, 1}`-valued everywhere
  set χ₀ : E d → ℝ := fun x ↦ if χ₁ x = 1 then 1 else 0 with hχ₀def
  have hχ₀m : Measurable χ₀ :=
    Measurable.ite (measurableSet_eq_fun hχ₁m measurable_const) measurable_const
      measurable_const
  have h01 := LongTime.ae_zero_or_one_of_tendstoLpLoc hU (fun n ↦ χ (φ n))
    (fun n ↦ (h (φ n)).meas) (fun n x hx ↦ (h (φ n)).zero_one x hx) hχ₁m hχ₁
  have hχae : ∀ᵐ x ∂(volume.restrict U), χ₁ x = χ₀ x := by
    filter_upwards [h01] with x hx
    rcases hx with h0 | h1
    · simp [χ₀, h0]
    · simp [χ₀, h1]
  have hχconv : TendstoLpLoc 1 volume U (fun j ↦ χ (φ j)) χ₀ atTop := by
    intro K hKU hK
    refine (hχ₁ K hKU hK).congr fun n ↦ eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKU hχae] with x hx
    simp [hx, φ]
  have hχ₀01 : ∀ x, χ₀ x = 0 ∨ χ₀ x = 1 := fun x ↦ by
    by_cases hx : χ₁ x = 1 <;> simp [χ₀, hx]
  have hχ₀b : ∀ x, |χ₀ x| ≤ 1 := fun x ↦ by
    rcases hχ₀01 x with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  -- properties of the limit `u₀`
  have hvL : ∀ n, LocallyLipschitzOn U (u (φ n)) := fun n ↦ (h (φ n)).locLip
  have hULLφ : DirectionalStable.UnifLocLip U fun n ↦ u (φ n) := fun y hy ↦ by
    obtain ⟨ε, hε, hεU, L, hL⟩ := hULL y hy
    exact ⟨ε, hε, hεU, L, fun n ↦ hL (φ n)⟩
  have hu₀L : LocallyLipschitzOn U u₀ := hULLφ.locallyLipschitzOn_limit hconv
  have hu₀0 : ∀ x ∈ U, 0 ≤ u₀ x := fun x hx ↦
    ge_of_tendsto (hconv.tendsto_at hx) (Eventually.of_forall fun n ↦ (h (φ n)).nonneg x hx)
  -- Step 3: harmonicity
  obtain ⟨hc2, hΔ⟩ := DirectionalStable.harmonic_of_tendsto hU hvL hu₀L hconv
    (fun n ↦ (h (φ n)).c2) (fun n ↦ (h (φ n)).harmonic)
  -- Step 4: strong convergence of the gradients
  have hconvK : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn (fun n ↦ u (φ n)) u₀ atTop K :=
    fun K hK hKU ↦ (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv K hKU hK
  have hBF : ∀ K, IsCompact K → K ⊆ U →
      ∃ B, ∀ᶠ n in atTop, ∀ x ∈ K, ‖∇ (u (φ n)) x‖ ≤ B := fun K hK hKU ↦ by
    obtain ⟨L, hL⟩ := hULLφ.exists_gradient_bound hK hKU
    exact ⟨L, Eventually.of_forall hL⟩
  have hgrad : TendstoLpLoc 2 volume U (fun j ↦ ∇ (u (φ j))) (∇ u₀) atTop :=
    StationaryLimit.tendstoLpLoc_gradient_of_energy hU hvL hu₀L hconvK hBF
      (fun K hK hKU ↦ (hbdd K (compactlyContained_of_isCompact hK hKU)).imp
        fun M hM n x hx ↦ hM (φ n) x hx)
      (fun η hη hηc hηU _ ↦ tendsto_const_nhds.congr fun n ↦ (integral_energy_eq_zero hU
        (hvL n) (h (φ n)).nonneg (h (φ n)).c2 (h (φ n)).harmonic (hη.of_le (by simp)) hηc
        hηU).symm)
      (fun η hη hηc hηU _ ↦ integral_energy_eq_zero hU hu₀L hu₀0 hc2 hΔ (hη.of_le (by simp))
        hηc hηU)
  -- Step 6: the inner variation identity
  obtain ⟨C, hC⟩ := hQb
  obtain ⟨c, hc, hcQ⟩ := hQpos
  have hQ2 : LocallyLipschitzOn U fun y ↦ Q y ^ 2 :=
    StationaryLimit.locallyLipschitzOn_sq hQ (fun x hx ↦ hc.le.trans (hcQ x hx)) hC
  have hC1 : ∀ ξ : E d → E d, ContDiff ℝ 1 ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
      ∫ x in U, innerVarIntegrand Q u₀ χ₀ ξ x = 0 := fun ξ hξ hξc hξU ↦
    tendsto_nhds_unique (StationaryLimit.tendsto_integral_innerVarIntegrand hU hQ2
      (fun n ↦ (h (φ n)).meas) hχ₀m (fun n ↦ hχb (φ n)) hBF hgrad hχconv hξ hξc hξU)
      (tendsto_const_nhds.congr fun n ↦ ((h (φ n)).stationary ξ
        (hξ.lipschitzWith_of_hasCompactSupport hξc one_ne_zero) hξc hξU).symm)
  refine ⟨φ, u₀, χ₀, hφ, hconv, hgrad, hχconv, ?_⟩
  exact
    { nonneg := hu₀0
      locLip := hu₀L
      c2 := hc2
      harmonic := hΔ
      meas := hχ₀m
      zero_one := fun x _ ↦ hχ₀01 x
      pos_le := StationaryLimit.ae_pos_imp_eq_one hU hu₀L.continuousOn hconv
        (fun n ↦ (h (φ n)).pos_le) hχconv hχ₀m
      stationary := StationaryLimit.innerVar_lipschitz hU hQ2 hu₀L hχ₀m hχ₀b hC1 }

end InnerVarCompactness

end PerronVariational

end
