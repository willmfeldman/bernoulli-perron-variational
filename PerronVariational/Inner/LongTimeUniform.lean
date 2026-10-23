/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Long-time limit: real-analysis helpers and the monotone case

Helpers for Step 1 of the proof of **[Theorem 3.14](#AFS:t.longtime-inner)** of F. Abedin, W. M.
Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (equi-Lipschitz bounds for the time slices from [(3.13)](#AFS:eqn:LipEst)), and the
full limit as `t → ∞` for flows **monotone in time** (the remark after
[Lemma 5.8](#AFS:l.subsolution-inner-limit) of the paper, used for
`LongtimeInnerMonotoneStatement`): the limit exists pointwise by monotonicity, and locally uniformly
by [(3.13)](#AFS:eqn:LipEst). Step 1 without monotonicity, along a sequence, is in
`Inner/LongTimeSubseq.lean`.

## Main results

* `PerronVariational.LongTime.lipschitzOnWith_of_norm_gradient_le`: a locally Lipschitz function
  on an open convex set whose (pointwise) gradient is bounded by `L` is `L`-Lipschitz there
  (Rademacher + Fubini on translated segments + FTC for absolutely continuous functions).
* `PerronVariational.LongTime.tendstoUniformlyOn_of_lipschitzOnWith`: equi-Lipschitz functions
  converging pointwise on a totally bounded set converge uniformly there.
* `PerronVariational.LongTime.exists_tendstoLocallyUniformlyOn`: for a bounded, time-monotone
  parabolic inner variational solution satisfying [(3.13)](#AFS:eqn:LipEst), `u(·, t) → u_∞` locally
  uniformly in `U` as `t → ∞`, and `u_∞ ≥ 0` is locally Lipschitz in `U`.
-/

open Set Filter Topology Metric MeasureTheory
open scoped Gradient NNReal Interval

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-! ### Real-analysis helpers -/

/-- **Gradient bound implies Lipschitz bound.** If `f` is locally Lipschitz on the open convex set
`s` and its pointwise gradient (`0` at points of non-differentiability) satisfies `‖∇f‖ ≤ L` on
`s`, then `f` is `L`-Lipschitz on `s`.

Proof: by Rademacher's theorem `f` is differentiable a.e. in `s`; by Fubini, for a.e. small
translation `y`, a.e. point of the segment `[a + y, b + y]` is a differentiability point, so the
restriction of `f` to it is Lipschitz with derivative `≤ L ‖b - a‖` a.e., hence (FTC for
absolutely continuous functions) `|f(b + y) - f(a + y)| ≤ L ‖b - a‖`; let `y → 0`. Used to turn
the pointwise bound [(3.13)](#AFS:eqn:LipEst) (a statement about `gradₓ`) into equi-Lipschitz bounds
on time slices. -/
theorem lipschitzOnWith_of_norm_gradient_le {s : Set (E d)} {f : E d → ℝ} {L : ℝ}
    (hs : IsOpen s) (hsc : Convex ℝ s) (hf : LocallyLipschitzOn s f)
    (hL : ∀ x ∈ s, ‖∇ f x‖ ≤ L) : LipschitzOnWith L.toNNReal f s := by
  -- `f` is differentiable at a.e. point of `s` (Rademacher, applied locally)
  have hN : volume {x | x ∈ s ∧ ¬ DifferentiableAt ℝ f x} = 0 := by
    refine measure_null_of_locally_null _ fun x hx ↦ ?_
    obtain ⟨K, t, ht, hK⟩ := hf hx.1
    rw [hs.nhdsWithin_eq hx.1] at ht
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht
    refine ⟨{x | x ∈ s ∧ ¬ DifferentiableAt ℝ f x} ∩ ball x r,
      inter_mem_nhdsWithin _ (ball_mem_nhds x hr), ?_⟩
    have hd := (hK.mono hrt).ae_differentiableWithinAt_of_mem (μ := volume)
    rw [ae_iff] at hd
    refine measure_mono_null (fun y hy ↦ ?_) hd
    simp only [Set.mem_ofPred_eq, Classical.not_imp]
    exact ⟨hy.2, fun h' ↦ hy.1.2 (h'.differentiableAt (isOpen_ball.mem_nhds hy.2))⟩
  obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
  refine LipschitzOnWith.of_dist_le_mul fun b hb a ha ↦ ?_
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL a ha)
  rw [Real.coe_toNNReal _ hL0]
  set v := b - a with hv
  -- a compact thickening of the segment `[a, b]` inside `s`, on which `f` is Lipschitz
  set Kseg := (fun τ : ℝ ↦ a + τ • v) '' Icc 0 1
  have hKseg : IsCompact Kseg := isCompact_Icc.image (by fun_prop)
  have hsub : Kseg ⊆ s := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact hsc.add_smul_sub_mem ha hb hτ
  obtain ⟨δ, hδ, hδs⟩ := hKseg.exists_cthickening_subset_open hs hsub
  obtain ⟨C, hC⟩ := (hf.mono hδs).exists_lipschitzOnWith_of_compact hKseg.cthickening
  have hmemK : ∀ y : E d, ‖y‖ ≤ δ → ∀ τ ∈ Icc (0 : ℝ) 1,
      a + y + τ • v ∈ cthickening δ Kseg := fun y hy τ hτ ↦
    mem_cthickening_of_dist_le _ (a + τ • v) δ Kseg ⟨τ, hτ, rfl⟩ (by
      rw [dist_eq_norm, show a + y + τ • v - (a + τ • v) = y by abel]; exact hy)
  -- for a.e. translation `y`, a.e. point of the translated line is a differentiability point
  have hprod : ∀ᵐ y : E d, ∀ᵐ τ : ℝ, a + y + τ • v ∉ N' := by
    have hΦ : Measurable fun p : E d × ℝ ↦ a + p.1 + p.2 • v := by fun_prop
    have h0 : ((volume : Measure (E d)).prod (volume : Measure ℝ))
        ((fun p : E d × ℝ ↦ a + p.1 + p.2 • v) ⁻¹' N') = 0 := by
      rw [Measure.prod_apply_symm (hΦ hN'm)]
      have hslice : ∀ τ : ℝ, volume ((fun y : E d ↦ (y, τ)) ⁻¹'
          ((fun p : E d × ℝ ↦ a + p.1 + p.2 • v) ⁻¹' N')) = 0 := fun τ ↦ by
        have : (fun y : E d ↦ (y, τ)) ⁻¹' ((fun p : E d × ℝ ↦ a + p.1 + p.2 • v) ⁻¹' N') =
            (fun y ↦ y + (a + τ • v)) ⁻¹' N' := by
          ext y; simp only [mem_preimage]; rw [show a + y + τ • v = y + (a + τ • v) by abel]
        rw [this, measure_preimage_add_right]
        exact hN'0
      simp [hslice]
    exact Measure.ae_ae_of_ae_prod (measure_eq_zero_iff_ae_notMem.1 h0)
  -- the estimate along a good translated segment
  have hkey : ∀ y : E d, ‖y‖ ≤ δ → (∀ᵐ τ : ℝ, a + y + τ • v ∉ N') →
      dist (f (b + y)) (f (a + y)) ≤ L * dist b a := by
    intro y hy hyτ
    set g : ℝ → ℝ := fun τ ↦ f (a + y + τ • v) with hg
    have hline : LipschitzWith ‖v‖₊ (fun τ : ℝ ↦ a + y + τ • v) :=
      LipschitzWith.of_dist_le_mul fun τ σ ↦ by
        rw [dist_eq_norm, dist_eq_norm, show a + y + τ • v - (a + y + σ • v) = (τ - σ) • v by
          rw [sub_smul]; abel, norm_smul, mul_comm, coe_nnnorm]
    have hgL : LipschitzOnWith (C * ‖v‖₊) g (uIcc 0 1) :=
      hC.comp hline.lipschitzOnWith fun τ hτ ↦
        hmemK y hy τ (by simpa [uIcc_of_le zero_le_one] using hτ)
    have hFTC := hgL.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    have hderiv : ∀ᵐ τ, τ ∈ Ι (0 : ℝ) 1 → ‖deriv g τ‖ ≤ L * ‖v‖ := by
      filter_upwards [hyτ] with τ hτN hτI
      have hτ : τ ∈ Icc (0 : ℝ) 1 :=
        Ioc_subset_Icc_self (by simpa [uIoc_of_le zero_le_one] using hτI)
      have hmem_s : a + y + τ • v ∈ s := hδs (hmemK y hy τ hτ)
      have hdiff : DifferentiableAt ℝ f (a + y + τ • v) := by
        by_contra hnd
        exact hτN (hNN' ⟨hmem_s, hnd⟩)
      have hl : HasDerivAt (fun τ : ℝ ↦ a + y + τ • v) v τ := by
        simpa using ((hasDerivAt_id τ).smul_const v).const_add (a + y)
      have hg' : HasDerivAt g (fderiv ℝ f (a + y + τ • v) v) τ :=
        hdiff.hasFDerivAt.comp_hasDerivAt τ hl
      rw [hg'.deriv]
      calc ‖fderiv ℝ f (a + y + τ • v) v‖ ≤ ‖fderiv ℝ f (a + y + τ • v)‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖v‖ := by
          gcongr
          simpa [gradient] using hL _ hmem_s
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const_ae hderiv
    rw [hFTC] at hint
    have hg1 : g 1 = f (b + y) := by
      simp only [hg, one_smul, hv]; congr 1; abel
    have hg0 : g 0 = f (a + y) := by simp [hg]
    rw [Real.dist_eq, dist_eq_norm, ← hg1, ← hg0]
    simpa using hint
  -- let the translation tend to `0`
  have hex : ∀ n : ℕ, ∃ y : E d, ‖y‖ < min δ (1 / ((n : ℝ) + 1)) ∧
      ∀ᵐ τ : ℝ, a + y + τ • v ∉ N' := by
    intro n
    set ρ := min δ (1 / ((n : ℝ) + 1)) with hρ_def
    have hρ : 0 < ρ := lt_min hδ (by positivity)
    have : (ae (volume.restrict (ball (0 : E d) ρ))).NeBot :=
      ae_neBot.2 (by
        rw [Ne, Measure.restrict_eq_zero]
        exact (measure_ball_pos volume 0 hρ).ne')
    obtain ⟨y, hy, hyg⟩ := ((ae_restrict_mem measurableSet_ball).and
      (ae_restrict_of_ae (s := ball (0 : E d) ρ) hprod)).exists
    exact ⟨y, by rw [mem_ball, dist_zero_right] at hy; exact hy, hyg⟩
  choose y hy hyg using hex
  have hy0 : Tendsto y atTop (𝓝 0) :=
    squeeze_zero_norm (fun n ↦ (hy n).le.trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont : ContinuousOn f s := hf.continuousOn
  have hfa : Tendsto (fun n ↦ f (a + y n)) atTop (𝓝 (f a)) :=
    (hcont.continuousAt (hs.mem_nhds ha)).tendsto.comp (by simpa using tendsto_const_nhds.add hy0)
  have hfb : Tendsto (fun n ↦ f (b + y n)) atTop (𝓝 (f b)) :=
    (hcont.continuousAt (hs.mem_nhds hb)).tendsto.comp (by simpa using tendsto_const_nhds.add hy0)
  exact le_of_tendsto (hfb.dist hfa) (Eventually.of_forall fun n ↦
    hkey (y n) ((hy n).le.trans (min_le_left _ _)) (hyg n))

section Uniform

variable {ι X : Type*} [PseudoMetricSpace X] {l : Filter ι} {F : ι → X → ℝ} {f : X → ℝ}
  {s : Set X} {K : ℝ≥0}

/-- A pointwise limit of eventually `K`-Lipschitz functions is `K`-Lipschitz. -/
theorem lipschitzOnWith_of_tendsto [l.NeBot] (hF : ∀ᶠ i in l, LipschitzOnWith K (F i) s)
    (hconv : ∀ x ∈ s, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) : LipschitzOnWith K f s :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦
    le_of_tendsto ((hconv x hx).dist (hconv y hy))
      (hF.mono fun _ hi ↦ hi.dist_le_mul x hx y hy)

/-- Equi-Lipschitz functions converging pointwise on a totally bounded set converge uniformly
there (the Arzelà–Ascoli step of [Theorem 3.14](#AFS:t.longtime-inner), Step 1). -/
theorem tendstoUniformlyOn_of_lipschitzOnWith (hs : TotallyBounded s)
    (hF : ∀ᶠ i in l, LipschitzOnWith K (F i) s) (hf : LipschitzOnWith K f s)
    (hconv : ∀ x ∈ s, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) : TendstoUniformlyOn F f l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hK : (0 : ℝ) ≤ K := K.2
  set δ := ε / (3 * (K + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hKδ : (K : ℝ) * δ < ε / 3 := by
    have h1 : (K : ℝ) * δ = ε / 3 * (K / (K + 1)) := by
      rw [hδ]; field_simp
    rw [h1]
    have h2 : (K : ℝ) / (K + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  obtain ⟨T, hTs, hTfin, hcover⟩ := Metric.finite_approx_of_totallyBounded hs δ hδ0
  have hnet : ∀ᶠ i in l, ∀ y ∈ T, dist (f y) (F i y) < ε / 3 :=
    (eventually_all_finite hTfin).2 fun y hy ↦
      ((Metric.tendsto_nhds.1 (hconv y (hTs hy))) (ε / 3) (by positivity)).mono
        fun i hi ↦ by rw [dist_comm]; exact hi
  filter_upwards [hnet, hF] with i hi hFi x hx
  obtain ⟨y, hyT, hxy⟩ := mem_iUnion₂.1 (hcover hx)
  have hy : y ∈ s := hTs hyT
  have hxy' : dist x y < δ := hxy
  have h1 : dist (f x) (f y) < ε / 3 :=
    lt_of_le_of_lt ((hf.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_left hxy'.le hK)) hKδ
  have h3 : dist (F i y) (F i x) < ε / 3 := by
    rw [dist_comm (F i y)]
    exact lt_of_le_of_lt ((hFi.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_left hxy'.le hK)) hKδ
  calc dist (f x) (F i x) ≤ dist (f x) (f y) + dist (f y) (F i y) + dist (F i y) (F i x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr; exact hi y hyT
    _ = ε := by ring

end Uniform

/-! ### Time slices -/

section Slices

variable {U : Set (E d)} {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ}

/-- Time slices of a parabolic inner variational solution are locally Lipschitz
([Definition 3.8(i)](#AFS:d.parabolic-inner); the paper's `∇u ∈ L^∞_loc(U_∞)` is encoded as local
spatial Lipschitz bounds). -/
theorem locallyLipschitzOn_slice (h : IsParaInnerVarSolution U Q u w χ) {t : ℝ} (ht : 0 < t) :
    LocallyLipschitzOn U (fun x ↦ u (x, t)) := by
  intro x hx
  obtain ⟨K, N, hN, hK⟩ := h.locLipₓ (x, t) (mk_mem_prod hx ht)
  refine ⟨K.toNNReal, {y | (y, t) ∈ N}, mem_nhdsWithin_of_mem_nhds ?_, ?_⟩
  · exact (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hN
  · refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
    rw [Real.dist_eq, dist_eq_norm]
    calc |u (y, t) - u (z, t)| ≤ K * ‖(y, t).1 - (z, t).1‖ := hK _ hy _ hz rfl
      _ ≤ K.toNNReal * ‖y - z‖ := by
        gcongr
        exact Real.le_coe_toNNReal K

/-- The interior Lipschitz estimate [(3.13)](#AFS:eqn:LipEst) on a cylinder `Q_{2r}(x, t) ⊆ U_∞`
makes the time slice `u(·, t)` Lipschitz on `B_r(x)` with constant `C (M/r + 1)`. -/
theorem lipschitzOnWith_slice_of_interiorLipEst {C : ℝ} (hlip : InteriorLipEst U u C)
    (h : IsParaInnerVarSolution U Q u w χ) {x : E d} {t r M : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hcyl : parCyl x t (2 * r) ⊆ UInf U) (hM : ∀ q ∈ parCyl x t (2 * r), |u q| ≤ M) :
    LipschitzOnWith (C * (M / r + 1)).toNNReal (fun y ↦ u (y, t)) (ball x r) := by
  have hmem : ∀ y ∈ ball x r, (y, t) ∈ parCyl x t (2 * r) := fun y hy ↦
    ⟨ball_subset_ball (by linarith) hy, by simp only [mem_Ioc]; constructor <;> nlinarith⟩
  have ht : 0 < t := (hcyl (hmem x (mem_ball_self hr))).2
  have hsub : ball x r ⊆ U := fun y hy ↦ (hcyl (hmem y hy)).1
  refine lipschitzOnWith_of_norm_gradient_le isOpen_ball (convex_ball x r)
    ((locallyLipschitzOn_slice h ht).mono hsub) fun y hy ↦ ?_
  exact hlip x t r hr hr1 hcyl M hM (y, t)
    ⟨hy, by simp only [mem_Ioc]; constructor <;> nlinarith⟩

/-- A bounded time-monotone function has a limit as `t → ∞` at every point of `U`. -/
theorem exists_tendsto_atTop_of_monotoneInTime {M : ℝ} (h0 : ∀ p ∈ UInf U, 0 ≤ u p)
    (hM : ∀ p ∈ UInf U, u p ≤ M)
    (hmono : MonotoneInTime u U (Ioi 0) ∨ AntitoneInTime u U (Ioi 0)) {x : E d} (hx : x ∈ U) :
    ∃ L, Tendsto (fun t ↦ u (x, t)) atTop (𝓝 L) := by
  set f : ℝ → ℝ := fun t ↦ u (x, max t 1)
  have hmem : ∀ t, (x, max t 1) ∈ UInf U := fun t ↦
    mk_mem_prod hx (lt_of_lt_of_le one_pos (le_max_right t 1))
  have hev : f =ᶠ[atTop] fun t ↦ u (x, t) :=
    (eventually_ge_atTop 1).mono fun t ht ↦ by simp [f, max_eq_left ht]
  have hmax : Monotone fun t : ℝ ↦ max t 1 := fun s t hst ↦ max_le_max hst le_rfl
  have hpos : ∀ t : ℝ, max t 1 ∈ Ioi (0 : ℝ) := fun t ↦ lt_of_lt_of_le one_pos (le_max_right t 1)
  rcases hmono with hmono | hmono
  · have hf : Monotone f := fun s t hst ↦ hmono x hx (hpos s) (hpos t) (hmax hst)
    exact ⟨_, (tendsto_atTop_ciSup hf ⟨M, by rintro _ ⟨t, rfl⟩; exact hM _ (hmem t)⟩).congr' hev⟩
  · have hf : Antitone f := fun s t hst ↦ hmono x hx (hpos s) (hpos t) (hmax hst)
    exact ⟨_, (tendsto_atTop_ciInf hf ⟨0, by rintro _ ⟨t, rfl⟩; exact h0 _ (hmem t)⟩).congr' hev⟩

end Slices

/-! ### The full limit for monotone flows -/

section Step1

variable {U : Set (E d)} {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ} {M C : ℝ}

/-- **The full limit for monotone flows** (remark after
[Lemma 5.8](#AFS:l.subsolution-inner-limit)): for a bounded, time-monotone parabolic inner
variational solution satisfying [(3.13)](#AFS:eqn:LipEst), `u(·, t)` converges locally uniformly in
`U` as `t → ∞` to a nonnegative locally Lipschitz function `u_∞`. -/
theorem exists_tendstoLocallyUniformlyOn (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hM : ∀ p ∈ UInf U, u p ≤ M)
    (hmono : MonotoneInTime u U (Ioi 0) ∨ AntitoneInTime u U (Ioi 0))
    (hlip : InteriorLipEst U u C) :
    ∃ uInf : E d → ℝ, TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U ∧
      (∀ x ∈ U, 0 ≤ uInf x) ∧ LocallyLipschitzOn U uInf := by
  set uInf : E d → ℝ := fun x ↦ limUnder atTop (fun t ↦ u (x, t))
  have hpt : ∀ x ∈ U, Tendsto (fun t ↦ u (x, t)) atTop (𝓝 (uInf x)) := fun x hx ↦
    tendsto_nhds_limUnder (exists_tendsto_atTop_of_monotoneInTime h.nonneg hM hmono hx)
  -- local equi-Lipschitz bounds on balls
  have hloc : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ K : ℝ≥0,
      ∀ᶠ t in atTop, LipschitzOnWith K (fun y ↦ u (y, t)) (ball x r) := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    set r := min (ε / 2) 1 with hr_def
    have hr : 0 < r := lt_min (by linarith) one_pos
    have hr1 : r ≤ 1 := min_le_right _ _
    have h2r : 2 * r ≤ ε := by have := min_le_left (ε / 2) 1; linarith
    refine ⟨r, hr, (ball_subset_ball (by linarith)).trans hball, (C * (M / r + 1)).toNNReal,
      (eventually_gt_atTop ((2 * r) ^ 2)).mono fun t ht ↦ ?_⟩
    have hcyl : parCyl x t (2 * r) ⊆ UInf U := fun q hq ↦
      ⟨hball (ball_subset_ball h2r hq.1), show 0 < q.2 by have := hq.2.1; linarith⟩
    exact lipschitzOnWith_slice_of_interiorLipEst hlip h hr hr1 hcyl fun q hq ↦
      abs_le.2 ⟨by linarith [h.nonneg q (hcyl hq), hM q (hcyl hq)], hM q (hcyl hq)⟩
  have hlipInf : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ K : ℝ≥0,
      (∀ᶠ t in atTop, LipschitzOnWith K (fun y ↦ u (y, t)) (ball x r)) ∧
        LipschitzOnWith K uInf (ball x r) := by
    intro x hx
    obtain ⟨r, hr, hsub, K, hK⟩ := hloc x hx
    exact ⟨r, hr, hsub, K, hK, lipschitzOnWith_of_tendsto hK fun y hy ↦ hpt y (hsub hy)⟩
  refine ⟨uInf, tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx ↦ ?_,
    fun x hx ↦ ge_of_tendsto (hpt x hx) ((eventually_gt_atTop 0).mono fun t ht ↦
      h.nonneg _ (mk_mem_prod hx ht)), fun x hx ↦ ?_⟩
  · obtain ⟨r, hr, hsub, K, hK, hKInf⟩ := hlipInf x hx
    exact ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),
      tendstoUniformlyOn_of_lipschitzOnWith
        ((isCompact_closedBall x r).totallyBounded.subset ball_subset_closedBall) hK hKInf
        fun y hy ↦ hpt y (hsub hy)⟩
  · obtain ⟨r, hr, hsub, K, -, hKInf⟩ := hlipInf x hx
    exact ⟨K, ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr), hKInf⟩

end Step1

end LongTime

end PerronVariational

end
