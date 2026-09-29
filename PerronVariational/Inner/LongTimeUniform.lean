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
# Long-time limit, Step 1: existence of the locally uniform limit

Step 1 of the proof of **Theorem 3.10** of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.
The paper argues that `u(·, t)` is Cauchy in `L²(U)` as `t → ∞`; this does not follow from
`∂ₜu ∈ L²(U_∞)`, which only gives `‖u(t) - u(s)‖_{L²} ≤ |t - s|^{1/2} ‖∂ₜu‖_{L²}`. Here we assume
instead that the flow is monotone in time (as it is in Propositions 6.1 and 6.2): the limit exists
pointwise by **time monotonicity**, and locally uniformly by the interior Lipschitz estimate
(3.12).

## Main results

* `PerronVariational.LongTime.lipschitzOnWith_of_norm_gradient_le`: a locally Lipschitz function
  on an open convex set whose (pointwise) gradient is bounded by `L` is `L`-Lipschitz there
  (Rademacher + Fubini on translated segments + FTC for absolutely continuous functions).
* `PerronVariational.LongTime.tendstoUniformlyOn_of_lipschitzOnWith`: equi-Lipschitz functions
  converging pointwise on a totally bounded set converge uniformly there.
* `PerronVariational.LongTime.exists_tendstoLocallyUniformlyOn`: **Step 1**: for a bounded,
  time-monotone parabolic inner variational solution satisfying (3.12), `u(·, t) → u_∞` locally
  uniformly in `U` as `t → ∞`, and `u_∞ ≥ 0` is locally Lipschitz in `U`.
* `PerronVariational.LongTime.norm_gradient_le_of_tendsto`: the limit inherits (3.12), in the
  form `‖∇u_∞‖ ≤ C (r⁻¹ ‖u_∞‖_{L^∞(B_{2r}(x))} + 1)` on `B_r(x)`. The paper states (3.14) with
  `B_r` on both sides and a constant depending on `V`, which is nearly vacuous; here we state it
  as the limit of (3.12), with the same constant `C`, because Propositions 6.1 and 6.2 need this
  form, uniformly over the shifted data.
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
the pointwise bound (3.12) (a statement about `gradₓ`) into equi-Lipschitz bounds on time
slices. -/
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
    simp only [mem_setOf_eq, Classical.not_imp]
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
    haveI : (ae (volume.restrict (ball (0 : E d) ρ))).NeBot :=
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
there (the Arzelà–Ascoli step of Theorem 3.10, Step 1). -/
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
(Definition 3.7(i); the paper's `∇u ∈ L^∞_loc(U_∞)` is encoded as local spatial Lipschitz
bounds). -/
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

/-- The interior Lipschitz estimate (3.12) on a cylinder `Q_{2r}(x, t) ⊆ U_∞` makes the time
slice `u(·, t)` Lipschitz on `B_r(x)` with constant `C (M/r + 1)`. -/
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

/-! ### Step 1 -/

section Step1

variable {U : Set (E d)} {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ} {M C : ℝ}

/-- **Theorem 3.10, Step 1** (with time monotonicity in place of the paper's `L²` Cauchy
argument, see the module docstring): for a bounded, time-monotone parabolic inner variational
solution satisfying (3.12), `u(·, t)` converges locally uniformly in `U` as `t → ∞` to
a nonnegative locally Lipschitz function `u_∞`. -/
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

/-- A time-monotone function lies on the correct side of its limit: `u(z, s) ≤ u_∞(z)` if `u`
is nondecreasing in time. -/
theorem le_of_monotoneInTime {uInf : E d → ℝ} (hmono : MonotoneInTime u U (Ioi 0)) {z : E d}
    (hz : z ∈ U) (hconv : Tendsto (fun t ↦ u (z, t)) atTop (𝓝 (uInf z))) {s : ℝ} (hs : 0 < s) :
    u (z, s) ≤ uInf z :=
  ge_of_tendsto hconv ((eventually_ge_atTop s).mono fun _ hst ↦
    hmono z hz hs (lt_of_lt_of_le hs hst) hst)

/-- **(3.14)** (in the form stated in the module docstring): the locally uniform limit of a
bounded time-monotone solution satisfying (3.12) with constant `C` satisfies, for `B_{2r}(x) ⊆ U`,
`r ≤ 1` and `|u_∞| ≤ M'` on `B_{2r}(x)`, the bound `‖∇u_∞‖ ≤ C (M'/r + 1)` on `B_r(x)`. -/
theorem norm_gradient_le_of_tendsto (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hmono : MonotoneInTime u U (Ioi 0) ∨ AntitoneInTime u U (Ioi 0))
    (hlip : InteriorLipEst U u C) {uInf : E d → ℝ}
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U)
    (x : E d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hball : ball x (2 * r) ⊆ U) (M' : ℝ)
    (hM' : ∀ y ∈ ball x (2 * r), |uInf y| ≤ M') (y : E d) (hy : y ∈ ball x r) :
    ‖∇ uInf y‖ ≤ C * (M' / r + 1) := by
  have hpt : ∀ z ∈ U, Tendsto (fun t ↦ u (z, t)) atTop (𝓝 (uInf z)) := fun z hz ↦
    hconv.tendsto_at hz
  -- the bound at every smaller radius `r' ∈ (dist y x, r)`, with slack `δ = r - r'`
  have key : ∀ r' ∈ Ioo (max (dist y x) (r / 2)) r,
      ‖∇ uInf y‖ ≤ C * ((M' + (r - r')) / r' + 1) := by
    intro r' hr'
    have hr'0 : 0 < r' := lt_of_lt_of_le (by linarith) (le_max_right _ _ |>.trans hr'.1.le)
    have hyr' : y ∈ ball x r' := lt_of_le_of_lt (le_max_left _ _) hr'.1
    have hr'1 : r' ≤ 1 := hr'.2.le.trans hr1
    set δ := r - r' with hδ
    have hδ0 : 0 < δ := by linarith [hr'.2]
    have hKsub : closedBall x (2 * r') ⊆ U :=
      (closedBall_subset_ball (by linarith [hr'.2])).trans hball
    have hunif : TendstoUniformlyOn (fun t x ↦ u (x, t)) uInf atTop (closedBall x (2 * r')) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hKsub
        (isCompact_closedBall x (2 * r'))
    have hclose : ∀ᶠ t in atTop, ∀ z ∈ closedBall x (2 * r'), u (z, t) < uInf z + δ := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif δ hδ0] with t ht z hz
      have := ht z hz
      rw [Real.dist_eq] at this
      linarith [le_abs_self (uInf z - u (z, t)), neg_abs_le (uInf z - u (z, t))]
    -- eventually the sup bound `M' + δ` holds on the cylinder `Q_{2r'}(x, t)`
    have hbound : ∀ᶠ t in atTop, parCyl x t (2 * r') ⊆ UInf U ∧
        ∀ q ∈ parCyl x t (2 * r'), |u q| ≤ M' + δ := by
      have hshift : Tendsto (fun t : ℝ ↦ t - (2 * r') ^ 2) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_id
      filter_upwards [eventually_gt_atTop ((2 * r') ^ 2), hshift.eventually hclose] with t ht
        hcl
      have hcyl : parCyl x t (2 * r') ⊆ UInf U := fun q hq ↦
        ⟨hKsub (ball_subset_closedBall hq.1), show 0 < q.2 by have := hq.2.1; linarith⟩
      refine ⟨hcyl, fun q hq ↦ abs_le.2 ⟨?_, ?_⟩⟩
      · linarith [h.nonneg q (hcyl hq), abs_nonneg (uInf q.1),
          hM' q.1 (ball_subset_ball (by linarith [hr'.2]) hq.1)]
      have hz : q.1 ∈ U := (hcyl hq).1
      have hM'z : uInf q.1 ≤ M' :=
        (le_abs_self _).trans (hM' q.1 (ball_subset_ball (by linarith [hr'.2]) hq.1))
      rcases hmono with hmono | hmono
      · have := le_of_monotoneInTime hmono hz (hpt _ hz) (hcyl hq).2
        rw [show ((q.1, q.2) : E d × ℝ) = q from rfl] at this
        linarith
      · have hs0 : 0 < t - (2 * r') ^ 2 := by linarith
        have h1 : u (q.1, q.2) ≤ u (q.1, t - (2 * r') ^ 2) :=
          hmono q.1 hz hs0 (hcyl hq).2 hq.2.1.le
        have h2 := hcl q.1 (ball_subset_closedBall hq.1)
        rw [show ((q.1, q.2) : E d × ℝ) = q from rfl] at h1
        linarith
    set g := C * ((M' + δ) / r' + 1) with hg
    have hlipt : ∀ᶠ t in atTop, LipschitzOnWith g.toNNReal (fun z ↦ u (z, t)) (ball x r') :=
      hbound.mono fun t ht ↦ lipschitzOnWith_slice_of_interiorLipEst hlip h hr'0 hr'1 ht.1 ht.2
    have hlipInf : LipschitzOnWith g.toNNReal uInf (ball x r') :=
      lipschitzOnWith_of_tendsto hlipt fun z hz ↦
        hpt z (hKsub (ball_subset_closedBall.trans (closedBall_subset_closedBall
          (by linarith)) hz))
    -- `g ≥ 0`, since (3.12) bounds a norm by `g`
    obtain ⟨t, ht⟩ := hbound.exists
    have hg0 : 0 ≤ g := (norm_nonneg _).trans
      (hlip x t r' hr'0 hr'1 ht.1 (M' + δ) ht.2 (x, t)
        ⟨mem_ball_self hr'0, by simp only [mem_Ioc]; constructor <;> nlinarith⟩)
    have hfd : ‖fderiv ℝ uInf y‖ ≤ g.toNNReal :=
      norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hyr') hlipInf
    rw [Real.coe_toNNReal _ hg0] at hfd
    simpa [gradient] using hfd
  -- let `r' ↑ r`
  have hlim : Tendsto (fun r' ↦ C * ((M' + (r - r')) / r' + 1)) (𝓝[<] r)
      (𝓝 (C * (M' / r + 1))) := by
    have hc : ContinuousAt (fun r' ↦ C * ((M' + (r - r')) / r' + 1)) r :=
      ((continuousAt_const.add (continuousAt_const.sub continuousAt_id)).div continuousAt_id
        hr.ne').add continuousAt_const |>.const_mul C
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlt : max (dist y x) (r / 2) < r := max_lt hy (by linarith)
  exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsLT hlt) fun r' hr' ↦ key r' hr')

end Step1

end LongTime

end PerronVariational

end
