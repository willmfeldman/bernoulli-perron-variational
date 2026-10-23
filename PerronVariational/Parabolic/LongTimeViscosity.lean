/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import PerronVariational.Topology.KLimit
import PerronVariational.Parabolic.StrictBarrierEquiv

/-!
# Long-time viscosity limits

Results of [Section 5](#AFS:s.viscosity-limits) of F. Abedin, W. M. Feldman, K.
Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981: Propositions [5.5](#AFS:p.subsolution-limit), [5.6](#AFS:p.supersolution-limit),
[Corollary 5.7](#AFS:c.monotone-long-time) and [Theorem 3.16(i)](#AFS:part.longtime-viscosity-1).

* `longtime_super` (**[Proposition 5.6](#AFS:p.supersolution-limit)**): the locally uniform
  `t → ∞` limit of a parabolic viscosity supersolution is a stationary viscosity supersolution.
* `longtime_relaxedSub` (**[Proposition 5.5](#AFS:p.subsolution-limit)**): the limit of a parabolic
  relaxed subsolution `(u, E)` is a stationary relaxed subsolution with the set
  `upperKLimit (timeSlice E) atTop` (the upper Kuratowski limit of the time slices `E_t`, i.e.
  `E_∞ = limsup*_{t → ∞} E_t`). `longtime_relaxedSub_of_slicesMonotone` gives the set
  `limsup*_{T → ∞} ⋂_{t ≥ T} E_t` (in general smaller) when the slices are monotone, in which case
  the two sets coincide.
* `longtime_sub_increasing` (**[Corollary 5.7](#AFS:c.monotone-long-time)**).
* `longtime_viscosity_increasing : LongtimeViscIncreasingStatement`
  (**[Theorem 3.16(i)](#AFS:part.longtime-viscosity-1)**).

## Proof strategy

The parabolic notions (Definitions [3.3](#AFS:d.parabolic-supersolution) and
[3.5](#AFS:d.parabolic-relaxed-subsolution)) are comparison-based, and both lemmas argue by
contradiction directly with the comparison property. Suppose the stationary test fails at `x₀` for a
test function `φ`, perturbed by `±δ ‖x - x₀‖⁴` so that the touching is strict. Then `φ + a` is a
strict stationary super/subsolution on a small ball `B̄_ρ(x₀)` for all `|a| ≤ a₁`
(`exists_strictSuper_shift`, `exists_strictSub_shift`). By uniform convergence on `B̄_ρ(x₀)`
([Lemma 5.2](#AFS:l.prec-ordering-convergence), `precOn_eventually_of_tendsto`), `u(·, t)` is
ordered with `φ ∓ a₁` on `∂B_ρ(x₀)` and with `φ ± a₁` on `B̄_ρ(x₀)` for all `t ≥ T`. With a smooth
nonincreasing cutoff `ζ` (`timeCutoff`, `ζ = 1` on `s ≤ 0`, `ζ = -1` on `s ≥ 1`), the barrier
`ψ(x, t) = φ(x) ± a₁ ζ(η (t - T))` is, for small `η`, a classical strict parabolic super/subsolution
on `B̄_ρ(x₀) × [T, b]` (with uniform constants: `|∂ₜψ - Δψ| ≥ η₀/2`, and `|ψ| ≤ a₁` forces
`φ + a = 0` with `|a| ≤ 2a₁`, where the gradient margin of `φ + a` gives the squared condition),
ordered with `u` on the parabolic boundary. Comparison orders it with `u` in the cylinder. Once
`b ≥ T + 1/η` we have `ψ(·, b) = φ ∓ a₁`, which contradicts `u(·, b) → u_∞` and `φ(x₀) = u_∞(x₀)`.
For [Proposition 5.5](#AFS:p.subsolution-limit) the comparison only holds on `E`, so the
contradiction is taken at points `x_j ∈ E_{t_j}` with `x_j → x₀` and `t_j → ∞`. (Upper signs for
[Proposition 5.5](#AFS:p.subsolution-limit), lower signs for
[Proposition 5.6](#AFS:p.supersolution-limit).) This is the route of the proofs of Propositions
[5.5](#AFS:p.subsolution-limit) and [5.6](#AFS:p.supersolution-limit) in the paper.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

namespace LongTime

/-! ### The limit function -/

variable {U : Set (E d)} {Q : E d → ℝ} {u : E d × ℝ → ℝ} {uInf : E d → ℝ}

theorem continuousOn_limit (hcont : ContinuousOn u (U ×ˢ Ioi 0))
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    ContinuousOn uInf U := by
  refine hconv.continuousOn (Filter.Eventually.frequently ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact hcont.comp (continuousOn_id.prodMk continuousOn_const) fun x hx => ⟨hx, ht⟩

theorem limit_nonneg (hnn : ∀ p ∈ U ×ˢ Ioi 0, 0 ≤ u p)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    ∀ x ∈ U, 0 ≤ uInf x := by
  intro x hx
  refine ge_of_tendsto (hconv.tendsto_at hx) ?_
  filter_upwards [eventually_gt_atTop 0] with t ht using hnn _ ⟨hx, ht⟩

/-- For a time-monotone `u`, the limit lies above every time slice. -/
theorem le_limit (hmono : MonotoneInTime u U (Ioi 0))
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) {x : E d} {t : ℝ}
    (hx : x ∈ U) (ht : 0 < t) : u (x, t) ≤ uInf x := by
  refine ge_of_tendsto (hconv.tendsto_at hx) ?_
  filter_upwards [eventually_ge_atTop t] with s hs
  exact hmono x hx ht (ht.trans_le hs) hs

/-- Locally uniform convergence, reindexed along times `τ j → ∞`, is uniform on compacts. -/
theorem tendstoUniformlyOn_comp_of_tendsto (hU : IsOpen U)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) {K : Set (E d)}
    (hK : IsCompact K) (hKU : K ⊆ U) {ι : Type*} {l : Filter ι} {τ : ι → ℝ}
    (hτ : Tendsto τ l atTop) : TendstoUniformlyOn (fun j x ↦ u (x, τ j)) uInf l K :=
  fun V hV =>
    hτ.eventually ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv K hKU hK V hV)

/-- A constant family converges uniformly. -/
theorem tendstoUniformlyOn_const_family {ι : Type*} {l : Filter ι} (v : E d → ℝ) (K : Set (E d)) :
    TendstoUniformlyOn (fun (_ : ι) ↦ v) v l K :=
  fun _ hV => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hV

/-! ### Smooth test functions -/

theorem two_le_infty : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

theorem continuous_laplacian {f : E d → ℝ} (hf : ContDiff ℝ ∞ f) : Continuous (Δ f) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_eval_const _).comp (hf.continuous_iteratedFDeriv two_le_infty)

theorem continuous_gradient {f : E d → ℝ} (hf : ContDiff ℝ ∞ f) : Continuous (∇ f) := by
  have : ∇ f = fun x ↦ (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp
    (hf.continuous_fderiv (by simp))

theorem contDiff_sqDist (x₀ : E d) : ContDiff ℝ ∞ (fun y : E d ↦ ‖y - x₀‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)

theorem laplacian_add_mul {φ w : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (c : ℝ)
    (x : E d) : Δ (fun y ↦ φ y + c * w y) x = Δ φ x + c * Δ w x := by
  have h2 : ∀ f : E d → ℝ, ContDiff ℝ ∞ f → ContDiffAt ℝ 2 f x := fun f hf =>
    (hf.of_le two_le_infty).contDiffAt
  have hfun : (fun y ↦ φ y + c * w y) = φ + c • w := by funext y; simp
  have hcw : ContDiffAt ℝ 2 (c • w) x := (h2 w hw).const_smul c
  rw [hfun, (h2 φ hφ).laplacian_add hcw, InnerProductSpace.laplacian_smul c (h2 w hw)]
  simp

theorem gradient_add_mul {φ w : E d → ℝ} (hφ : Differentiable ℝ φ) (hw : Differentiable ℝ w)
    (c : ℝ) (x : E d) : ∇ (fun y ↦ φ y + c * w y) x = ∇ φ x + c • ∇ w x := by
  have hfun : (fun y ↦ φ y + c * w y) = φ + c • w := by funext y; simp
  have h := ((hφ x).hasFDerivAt.add ((hw x).hasFDerivAt.const_smul c)).fderiv
  simp only [gradient, hfun]
  rw [h, map_add, map_smul]

/-- The quartic perturbation `y ↦ ‖y - x₀‖⁴` of the proofs of Propositions
[5.5](#AFS:p.subsolution-limit) and [5.6](#AFS:p.supersolution-limit). -/
theorem contDiff_quartDist (x₀ : E d) : ContDiff ℝ ∞ (fun y : E d ↦ ‖y - x₀‖ ^ 4) := by
  simpa [← pow_mul] using (contDiff_sqDist x₀).pow 2

/-- The space-time function `ψ(x, t) = φ(x) + g(t)`. -/
theorem contDiff_addTime {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun p : E d × ℝ ↦ φ p.1 + g p.2) :=
  (hφ.comp contDiff_fst).add (hg.comp contDiff_snd)

theorem dₜ_addTime (φ : E d → ℝ) (g : ℝ → ℝ) (p : E d × ℝ) :
    dₜ (fun p : E d × ℝ ↦ φ p.1 + g p.2) p = deriv g p.2 := by
  simp only [dₜ]
  exact deriv_const_add _

theorem lapₓ_addTime {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) (g : ℝ → ℝ) (p : E d × ℝ) :
    lapₓ (fun p : E d × ℝ ↦ φ p.1 + g p.2) p = Δ φ p.1 := by
  have h1 : ContDiffAt ℝ 2 φ p.1 := (hφ.of_le two_le_infty).contDiffAt
  have hfun : (fun y ↦ φ y + g p.2) = φ + fun _ ↦ g p.2 := rfl
  simp only [lapₓ]
  rw [hfun, h1.laplacian_add contDiffAt_const, InnerProductSpace.laplacian_const]
  simp

theorem gradₓ_addTime (φ : E d → ℝ) (g : ℝ → ℝ) (p : E d × ℝ) :
    gradₓ (fun p : E d × ℝ ↦ φ p.1 + g p.2) p = ∇ φ p.1 := by
  simp only [gradₓ, gradient, fderiv_add_const]

/-! ### The time cutoff `ζ` -/

/-- The time cutoff `ζ(s) = 1 - 2 smoothTransition(s)` of the proofs of Propositions
[5.5](#AFS:p.subsolution-limit) and [5.6](#AFS:p.supersolution-limit): smooth, nonincreasing,
`ζ = 1` on `s ≤ 0`, `ζ = -1` on `s ≥ 1`. -/
noncomputable def timeCutoff (s : ℝ) : ℝ := 1 - 2 * Real.smoothTransition s

theorem contDiff_timeCutoff : ContDiff ℝ ∞ timeCutoff :=
  contDiff_const.sub (contDiff_const.mul Real.smoothTransition.contDiff)

theorem timeCutoff_of_nonpos {s : ℝ} (hs : s ≤ 0) : timeCutoff s = 1 := by
  simp [timeCutoff, Real.smoothTransition.zero_of_nonpos hs]

theorem timeCutoff_of_one_le {s : ℝ} (hs : 1 ≤ s) : timeCutoff s = -1 := by
  simp [timeCutoff, Real.smoothTransition.one_of_one_le hs]; norm_num

theorem antitone_timeCutoff : Antitone timeCutoff := fun _ _ h => by
  have := Real.smoothTransition.monotone h
  simp only [timeCutoff]
  linarith

theorem abs_timeCutoff_le_one (s : ℝ) : |timeCutoff s| ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg s
  have h1 := Real.smoothTransition.le_one s
  rw [abs_le]
  constructor <;> simp only [timeCutoff] <;> linarith

theorem deriv_timeCutoff_eq_zero {s : ℝ} (hs : s ∉ Icc 0 1) : deriv timeCutoff s = 0 := by
  rcases not_and_or.1 hs with h | h
  · have : timeCutoff =ᶠ[𝓝 s] fun _ ↦ 1 :=
      (show ∀ᶠ x in 𝓝 s, x < 0 from Iio_mem_nhds (not_le.1 h)).mono fun x hx =>
        timeCutoff_of_nonpos hx.le
    rw [this.deriv_eq, deriv_const]
  · have : timeCutoff =ᶠ[𝓝 s] fun _ ↦ -1 :=
      (show ∀ᶠ x in 𝓝 s, 1 < x from Ioi_mem_nhds (not_le.1 h)).mono fun x hx =>
        timeCutoff_of_one_le hx.le
    rw [this.deriv_eq, deriv_const]

/-- `|ζ'| ≤ C`: `ζ'` is continuous and vanishes off `[0, 1]`. -/
theorem exists_abs_deriv_timeCutoff_le : ∃ C, ∀ s, |deriv timeCutoff s| ≤ C := by
  have hc : Continuous (deriv timeCutoff) := contDiff_timeCutoff.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv timeCutoff) :=
    HasCompactSupport.intro isCompact_Icc fun s hs => deriv_timeCutoff_eq_zero hs
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, fun s => by simpa [Real.norm_eq_abs] using hC s⟩

/-- The time part `t ↦ a₁ ζ(η (t - T))` of the barriers of Propositions
[5.5](#AFS:p.subsolution-limit) and [5.6](#AFS:p.supersolution-limit). -/
theorem contDiff_cutoffTime (a₁ η T : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ a₁ * timeCutoff (η * (t - T))) :=
  contDiff_const.mul
    (contDiff_timeCutoff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))

/-- `|∂ₜ (a₁ ζ(η (t - T)))| ≤ a₁ η C` (the paper's `C η a₁`). -/
theorem abs_deriv_cutoffTime_le {a₁ η C : ℝ} (ha₁ : 0 ≤ a₁) (hη : 0 ≤ η)
    (hC : ∀ s, |deriv timeCutoff s| ≤ C) (T t : ℝ) :
    |deriv (fun t : ℝ ↦ a₁ * timeCutoff (η * (t - T))) t| ≤ a₁ * (η * C) := by
  have hd : HasDerivAt (fun t : ℝ ↦ a₁ * timeCutoff (η * (t - T)))
      (a₁ * (deriv timeCutoff (η * (t - T)) * (η * 1))) t :=
    ((contDiff_timeCutoff.differentiable (by simp) _).hasDerivAt.comp t
      (((hasDerivAt_id t).sub_const T).const_mul η)).const_mul a₁
  rw [hd.deriv, abs_mul, abs_mul, abs_of_nonneg ha₁, mul_one, abs_of_nonneg hη]
  exact mul_le_mul_of_nonneg_left (by nlinarith [hC (η * (t - T)), abs_nonneg (deriv timeCutoff
    (η * (t - T)))]) ha₁

/-! ### `φ + a` is a strict stationary super/subsolution for small `|a|` -/

/-- A closed ball on which an eventual property holds, of radius at most `r`. -/
theorem exists_closedBall_of_eventually {x₀ : E d} {P : E d → Prop} (h : ∀ᶠ y in 𝓝 x₀, P y)
    {r : ℝ} (hr : 0 < r) : ∃ ρ > 0, ρ ≤ r ∧ ∀ y ∈ closedBall x₀ ρ, P y := by
  obtain ⟨ε, hε, hP⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 h
  exact ⟨min r ε, lt_min hr hε, min_le_left _ _,
    fun y hy => hP (closedBall_subset_closedBall (min_le_right _ _) hy)⟩

/-- The step "`φ + a` is a strict supersolution of [(1.1)](#AFS:e.bernoulli-basic) in `B̄_ρ(x₀)` for
all `|a| ≤ a₁`" of the proof of **[Proposition 5.5](#AFS:p.subsolution-limit)**, with explicit
margins: `Δφ < -η₀` on `B̄_ρ(x₀)`, and `‖∇φ‖ + η₀ < Q` on `{φ + a = 0} ∩ B̄_ρ(x₀)` for
`|a| ≤ a₁`. -/
theorem exists_strictSuper_shift (hU : IsOpen U) (hQ : ContinuousOn Q U) {φ : E d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀U : x₀ ∈ U) {r : ℝ} (hr : 0 < r)
    (hΔ : Δ φ x₀ < 0) (hfb : 0 < φ x₀ ∨ ‖∇ φ x₀‖ < Q x₀) :
    ∃ ρ > 0, ρ ≤ r ∧ closedBall x₀ ρ ⊆ U ∧ ∃ a₁ > 0, ∃ η₀ > 0, ∀ y ∈ closedBall x₀ ρ,
      Δ φ y < -η₀ ∧ ∀ a, |a| ≤ a₁ → φ y + a = 0 → ‖∇ φ y‖ + η₀ < Q y := by
  have hΔev (η₀ : ℝ) (h : η₀ < -Δ φ x₀) : ∀ᶠ y in 𝓝 x₀, Δ φ y < -η₀ :=
    (continuous_laplacian hφ).continuousAt.eventually_lt continuousAt_const (by linarith)
  rcases hfb with hpos | hgrad
  · -- `φ > φ(x₀)/2` near `x₀`: the gradient condition is vacuous for `|a| ≤ φ(x₀)/4`
    have hφev : ∀ᶠ y in 𝓝 x₀, φ x₀ / 2 < φ y :=
      continuousAt_const.eventually_lt hφ.continuous.continuousAt (by linarith)
    obtain ⟨ρ, hρ, hρr, hP⟩ := exists_closedBall_of_eventually
      (((hΔev (-Δ φ x₀ / 2) (by linarith)).and hφev).and (hU.mem_nhds hx₀U)) hr
    refine ⟨ρ, hρ, hρr, fun y hy => (hP y hy).2, φ x₀ / 4, by linarith, -Δ φ x₀ / 2,
      by linarith, fun y hy => ⟨(hP y hy).1.1, fun a ha h0 => ?_⟩⟩
    have := (hP y hy).1.2
    linarith [neg_abs_le a]
  · set η₀ := min (-Δ φ x₀ / 2) ((Q x₀ - ‖∇ φ x₀‖) / 2) with hη₀_def
    have hη₀ : 0 < η₀ := lt_min (by linarith) (by linarith)
    have h1 : η₀ ≤ -Δ φ x₀ / 2 := min_le_left _ _
    have h2 : η₀ ≤ (Q x₀ - ‖∇ φ x₀‖) / 2 := min_le_right _ _
    have hgev : ∀ᶠ y in 𝓝 x₀, ‖∇ φ y‖ + η₀ < Q y :=
      ((continuous_gradient hφ).continuousAt.norm.add continuousAt_const).eventually_lt
        (hQ.continuousAt (hU.mem_nhds hx₀U)) (by simp only [Pi.add_apply]; linarith)
    obtain ⟨ρ, hρ, hρr, hP⟩ := exists_closedBall_of_eventually
      (((hΔev η₀ (by linarith)).and hgev).and (hU.mem_nhds hx₀U)) hr
    exact ⟨ρ, hρ, hρr, fun y hy => (hP y hy).2, 1, one_pos, η₀, hη₀,
      fun y hy => ⟨(hP y hy).1.1, fun _ _ _ => (hP y hy).1.2⟩⟩

/-- The mirror of `exists_strictSuper_shift` for the proof
of **[Proposition 5.6](#AFS:p.supersolution-limit)**: `φ + a` is a strict subsolution of
[(1.1)](#AFS:e.bernoulli-basic) in `B̄_ρ(x₀)` for all `|a| ≤ a₁`, with explicit margins: `η₀ < Δφ`
on `B̄_ρ(x₀)`, and `Q + η₀ < ‖∇φ‖` on `{φ + a = 0} ∩ B̄_ρ(x₀)` for `|a| ≤ a₁`. -/
theorem exists_strictSub_shift (hU : IsOpen U) (hQ : ContinuousOn Q U) {φ : E d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀U : x₀ ∈ U) {r : ℝ} (hr : 0 < r)
    (hΔ : 0 < Δ φ x₀) (hfb : 0 < φ x₀ ∨ Q x₀ < ‖∇ φ x₀‖) :
    ∃ ρ > 0, ρ ≤ r ∧ closedBall x₀ ρ ⊆ U ∧ ∃ a₁ > 0, ∃ η₀ > 0, ∀ y ∈ closedBall x₀ ρ,
      η₀ < Δ φ y ∧ ∀ a, |a| ≤ a₁ → φ y + a = 0 → Q y + η₀ < ‖∇ φ y‖ := by
  have hΔev (η₀ : ℝ) (h : η₀ < Δ φ x₀) : ∀ᶠ y in 𝓝 x₀, η₀ < Δ φ y :=
    continuousAt_const.eventually_lt (continuous_laplacian hφ).continuousAt h
  rcases hfb with hpos | hgrad
  · have hφev : ∀ᶠ y in 𝓝 x₀, φ x₀ / 2 < φ y :=
      continuousAt_const.eventually_lt hφ.continuous.continuousAt (by linarith)
    obtain ⟨ρ, hρ, hρr, hP⟩ := exists_closedBall_of_eventually
      (((hΔev (Δ φ x₀ / 2) (by linarith)).and hφev).and (hU.mem_nhds hx₀U)) hr
    refine ⟨ρ, hρ, hρr, fun y hy => (hP y hy).2, φ x₀ / 4, by linarith, Δ φ x₀ / 2,
      by linarith, fun y hy => ⟨(hP y hy).1.1, fun a ha h0 => ?_⟩⟩
    have := (hP y hy).1.2
    linarith [neg_abs_le a]
  · set η₀ := min (Δ φ x₀ / 2) ((‖∇ φ x₀‖ - Q x₀) / 2) with hη₀_def
    have hη₀ : 0 < η₀ := lt_min (by linarith) (by linarith)
    have h1 : η₀ ≤ Δ φ x₀ / 2 := min_le_left _ _
    have h2 : η₀ ≤ (‖∇ φ x₀‖ - Q x₀) / 2 := min_le_right _ _
    have hgev : ∀ᶠ y in 𝓝 x₀, Q y + η₀ < ‖∇ φ y‖ :=
      ((hQ.continuousAt (hU.mem_nhds hx₀U)).add continuousAt_const).eventually_lt
        (continuous_gradient hφ).continuousAt.norm (by simp only [Pi.add_apply]; linarith)
    obtain ⟨ρ, hρ, hρr, hP⟩ := exists_closedBall_of_eventually
      (((hΔev η₀ (by linarith)).and hgev).and (hU.mem_nhds hx₀U)) hr
    exact ⟨ρ, hρ, hρr, fun y hy => (hP y hy).2, 1, one_pos, η₀, hη₀,
      fun y hy => ⟨(hP y hy).1.1, fun _ _ _ => (hP y hy).1.2⟩⟩

/-! ### The comparison cores -/

/-- Core of **[Proposition 5.5](#AFS:p.subsolution-limit)**, following the proof in the paper: a
touching from above of `u_∞` in `E_∞ = limsup*_t E_t` at `x₀` by a smooth `φ`, strict like
`δ ‖y - x₀‖⁴`, where `φ` is a strict stationary supersolution at `x₀`, contradicts the parabolic
relaxed subsolution property ([Definition 3.5](#AFS:d.parabolic-relaxed-subsolution)). -/
theorem relaxedSub_core (hU : IsOpen U) (hQ : ContinuousOn Q U) {Eset : Set (E d × ℝ)}
    (hu : IsParaRelaxedSub U Q (Ioi 0) u Eset)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀U : x₀ ∈ U)
    (hx₀E : x₀ ∈ upperKLimit (timeSlice Eset) atTop) (hφx₀ : φ x₀ = uInf x₀)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hstrict : ∀ y ∈ closedBall x₀ r, y ∈ upperKLimit (timeSlice Eset) atTop →
      uInf y ≤ φ y - δ * ‖y - x₀‖ ^ 4)
    (hΔ : Δ φ x₀ < 0) (hfb : 0 < φ x₀ ∨ ‖∇ φ x₀‖ < Q x₀) : False := by
  obtain ⟨hucont, -, -, -, -, hcomp⟩ := hu
  have huInf : ContinuousOn uInf U := continuousOn_limit hucont hconv
  set Einf := upperKLimit (timeSlice Eset) atTop
  -- `φ + a` is a strict supersolution of [(1.1)](#AFS:e.bernoulli-basic) in `B̄_ρ(x₀)` for all
  -- `|a| ≤ a₁`, and
  -- `u_∞ ≺_{E_∞} φ - a₁` on `∂B_ρ(x₀)` (strictness of the quartic perturbation)
  obtain ⟨ρ, hρ, hρr, hρU, a₀, ha₀, η₀, hη₀, hshift⟩ :=
    exists_strictSuper_shift hU hQ hφ hx₀U hr hΔ hfb
  set a₁ := min (a₀ / 2) (δ * ρ ^ 4 / 2) with ha₁_def
  have ha₁ : 0 < a₁ := lt_min (by positivity) (by positivity)
  have ha₁a₀ : 2 * a₁ ≤ a₀ := by linarith [min_le_left (a₀ / 2) (δ * ρ ^ 4 / 2)]
  have hbdInf : PrecOn uInf (fun y ↦ φ y - a₁) Einf (sphere x₀ ρ) := by
    rintro y ⟨hyE, hy⟩
    have h1 := hstrict y (closedBall_subset_closedBall hρr (sphere_subset_closedBall hy)) hyE
    rw [mem_sphere_iff_norm.1 hy] at h1
    have h2 : a₁ ≤ δ * ρ ^ 4 / 2 := min_le_right _ _
    have h3 : 0 < δ * ρ ^ 4 := by positivity
    linarith
  -- `u_∞ ≺_{E_∞} φ + a₁` on `B̄_ρ(x₀)`, since `u_∞ ≤ φ` on `E_∞ ∩ B̄_ρ(x₀)` (TR-170)
  have hinInf : PrecOn uInf (fun y ↦ φ y + a₁) Einf (closedBall x₀ ρ) := by
    rintro y ⟨hyE, hy⟩
    have h1 := hstrict y (closedBall_subset_closedBall hρr hy) hyE
    have h2 : 0 ≤ δ * ‖y - x₀‖ ^ 4 := by positivity
    linarith
  -- (e.prec-br-bd) and (e.prec-br-in): [Lemma 5.2](#AFS:l.prec-ordering-convergence) along `t → ∞`,
  -- with `E' = (E_t)_t`, whose
  -- `limsup*` is `E_∞` (TR-172)
  have ebd := precOn_eventually_of_tendsto (v := fun y ↦ φ y - a₁) (isCompact_sphere x₀ ρ)
    (huInf.mono (sphere_subset_closedBall.trans hρU))
    (hφ.continuous.sub continuous_const).continuousOn
    hbdInf (tendstoUniformlyOn_comp_of_tendsto hU hconv (isCompact_sphere x₀ ρ)
      (sphere_subset_closedBall.trans hρU) tendsto_id)
    (tendstoUniformlyOn_const_family _ _) (E' := timeSlice Eset) subset_rfl
  have ein := precOn_eventually_of_tendsto (v := fun y ↦ φ y + a₁) (isCompact_closedBall x₀ ρ)
    (huInf.mono hρU)
    (hφ.continuous.add continuous_const).continuousOn hinInf
    (tendstoUniformlyOn_comp_of_tendsto hU hconv (isCompact_closedBall x₀ ρ) hρU tendsto_id)
    (tendstoUniformlyOn_const_family _ _) (E' := timeSlice Eset) subset_rfl
  -- fix `T > 0`
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((ebd.and ein).and (eventually_gt_atTop 0))
  have hT0 : 0 < T := (hT T le_rfl).2
  -- the barrier `ψ(x, t) = φ(x) + a₁ ζ(η (t - T))`, `η` small
  obtain ⟨C, hC⟩ := exists_abs_deriv_timeCutoff_le
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set η := η₀ / (2 * (a₁ * C + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hηC : a₁ * (η * C) < η₀ := by
    have hden : 0 < 2 * (a₁ * C + 1) := by positivity
    have : a₁ * (η * C) = η₀ * (a₁ * C) / (2 * (a₁ * C + 1)) := by rw [hη_def]; ring
    rw [this, div_lt_iff₀ hden]
    nlinarith [mul_nonneg ha₁.le hC0]
  set g : ℝ → ℝ := fun t ↦ a₁ * timeCutoff (η * (t - T)) with hg_def
  have hg : ContDiff ℝ ∞ g := contDiff_cutoffTime a₁ η T
  have hgabs : ∀ t, |g t| ≤ a₁ := fun t => by
    rw [hg_def, abs_mul, abs_of_pos ha₁]
    exact mul_le_of_le_one_right ha₁.le (abs_timeCutoff_le_one _)
  have hgT : g T = a₁ := by simp [hg_def, timeCutoff_of_nonpos]
  set ψ : E d × ℝ → ℝ := fun p ↦ φ p.1 + g p.2 with hψ_def
  -- `ψ` is a classical strict supersolution on `B̄_ρ(x₀) × [T, b]`, for every `b`, with the
  -- uniform constants `min a₁ (1/2)` and `δ₀`: since `|∂ₜ(a₁ ζ(η (t - T)))| ≤ C η a₁ ≤ η₀ / 2`,
  -- `∂ₜψ - Δψ ≥ η₀ / 2`; where `|ψ| ≤ a₁`, `φ + a = 0` with `|a| ≤ 2 a₁ ≤ a₀`, so
  -- `|∇ψ| + η₀ < Q`
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ ρ).exists_bound_of_continuousOn (hQ.mono hρU)
  have hηC' : a₁ * (η * C) ≤ η₀ / 2 := by
    have hden : 0 < 2 * (a₁ * C + 1) := by positivity
    have : a₁ * (η * C) = η₀ * (a₁ * C) / (2 * (a₁ * C + 1)) := by rw [hη_def]; ring
    rw [this, div_le_iff₀ hden]
    nlinarith [mul_nonneg ha₁.le hC0]
  set δ₀ := min (min (η₀ / 2) (η₀ / (|M| + 1))) (1 / 2) with hδ₀_def
  have hδ₀ : 0 < δ₀ := lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hδ₀η : δ₀ ≤ η₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₀M : δ₀ * (|M| + 1) ≤ η₀ := by
    have : δ₀ ≤ η₀ / (|M| + 1) := (min_le_left _ _).trans (min_le_right _ _)
    calc δ₀ * (|M| + 1) ≤ η₀ / (|M| + 1) * (|M| + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = η₀ := by field_simp
  have hsuper : ∀ b, IsClassicalStrictParaSuper Q ψ (ball x₀ ρ) T b := fun b => by
    refine ⟨min a₁ (1 / 2), δ₀, contDiff_addTime hφ hg, lt_min ha₁ (by norm_num),
      min_le_right _ _, hδ₀, min_le_right _ _, ?_, ?_⟩
    · rintro ⟨y, t⟩ ⟨-, hy, -⟩
      rw [closure_ball x₀ hρ.ne'] at hy
      rw [hψ_def, dₜ_addTime, lapₓ_addTime hφ]
      have h1 := (hshift y hy).1
      have h2 := neg_abs_le (deriv g t)
      have h3 := abs_deriv_cutoffTime_le ha₁.le hη.le hC T t
      simp only at h1 h2 h3 ⊢
      linarith
    · rintro ⟨y, t⟩ ⟨hψy, hy, -⟩
      rw [closure_ball x₀ hρ.ne'] at hy
      have hψy' : |φ y + g t| ≤ min a₁ (1 / 2) := hψy
      have ha : |-φ y| ≤ a₀ := by
        have := abs_sub (g t) (φ y + g t)
        rw [show g t - (φ y + g t) = -φ y by ring] at this
        linarith [hgabs t, min_le_left a₁ (1 / 2)]
      have h := (hshift y hy).2 (-φ y) ha (by ring)
      have hQM : Q y ≤ |M| + 1 := by
        have := hM y hy
        rw [Real.norm_eq_abs] at this
        linarith [le_abs_self (Q y), le_abs_self M]
      rw [hψ_def, gradₓ_addTime]
      exact sq_le_one_sub_mul_sq (norm_nonneg _) h.le hη₀ hQM hδ₀.le hδ₀M
  -- points `x_j ∈ E_{t_j}` with `x_j → x₀`, `t_j → ∞` (TR-168)
  obtain ⟨τ, hτ, x, hxE, hx⟩ := mem_upperKLimit_iff_exists_seq.1 hx₀E
  have hcontra : ∀ᶠ j in atTop, u (x j, τ j) < φ (x j) - a₁ := by
    filter_upwards [hτ.eventually (eventually_ge_atTop (T + 1 / η)),
      hx.eventually (ball_mem_nhds x₀ hρ)] with j hj hxj
    set b := τ j with hb
    have hTb : T < b := by linarith [one_div_pos.2 hη]
    have hadm : AdmissibleCyl U (Ioi 0) (ball x₀ ρ) T b := by
      refine ⟨isOpen_ball, isBounded_ball, hTb, ?_⟩
      rw [closure_ball x₀ hρ.ne']
      rintro ⟨y, t⟩ ⟨hy, ht⟩
      exact ⟨hρU hy, lt_of_lt_of_le hT0 ht.1⟩
    -- `u ≺_E ψ` on `∂_P(B_ρ(x₀) × (T, t_j])`, by (e.prec-br-bd) and (e.prec-br-in)
    have hbdry : PrecOn u ψ Eset (parBdry (ball x₀ ρ) T b) := by
      rintro ⟨y, t⟩ ⟨hE, hB⟩
      rw [parBdry, closure_ball x₀ hρ.ne', frontier_ball x₀ hρ.ne'] at hB
      rcases hB with ⟨hy, ht⟩ | ⟨hy, ht⟩
      · have ht' : t = T := ht
        subst ht'
        have := (hT t le_rfl).1.2 y ⟨hE, hy⟩
        simp only [hψ_def, hgT] at this ⊢
        exact this
      · have h1 := (hT t ht.1).1.1 y ⟨hE, hy⟩
        have h2 := (abs_le.1 (hgabs t)).1
        simp only [hψ_def, id] at h1 h2 ⊢
        linarith
    -- so `u ≺_E ψ` in the cylinder; at `(x_j, t_j) ∈ E`, `ζ(η (t_j - T)) = -1`
    have hcon := hcomp (ball x₀ ρ) T b ψ hadm (hsuper b) hbdry (x j, b)
      ⟨hxE j, hxj, hTb, le_rfl⟩
    have hζ : timeCutoff (η * (b - T)) = -1 := timeCutoff_of_one_le (by
      have h := mul_le_mul_of_nonneg_left (show 1 / η ≤ b - T by linarith) hη.le
      rwa [mul_one_div_cancel hη.ne'] at h)
    simp only [hψ_def, hg_def, hζ] at hcon
    linarith
  -- let `j → ∞`
  have hlimL : Tendsto (fun j ↦ u (x j, τ j)) atTop (𝓝 (uInf x₀)) :=
    (tendstoUniformlyOn_comp_of_tendsto hU hconv (isCompact_closedBall x₀ ρ) hρU hτ).tendsto_comp
      ((huInf.mono hρU).continuousWithinAt (mem_closedBall_self hρ.le))
      (tendsto_nhdsWithin_iff.2 ⟨hx, hx.eventually (closedBall_mem_nhds x₀ hρ)⟩)
  have hlimR : Tendsto (fun j ↦ φ (x j) - a₁) atTop (𝓝 (φ x₀ - a₁)) :=
    (hφ.continuous.tendsto x₀).comp hx |>.sub_const a₁
  have := le_of_tendsto_of_tendsto hlimL hlimR (hcontra.mono fun j hj => hj.le)
  linarith

/-- Core of **[Proposition 5.6](#AFS:p.supersolution-limit)**, following the proof in the paper: a
touching from below of `u_∞` at `x₀` by a smooth `φ`, strict like `δ ‖y - x₀‖⁴`, where `φ` is a
strict stationary subsolution at `x₀`, contradicts the parabolic supersolution property
([Definition 3.3](#AFS:d.parabolic-supersolution)). -/
theorem super_core (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x)
    (hu : IsParaSuper U Q (Ioi 0) u)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀U : x₀ ∈ U) (hφx₀ : φ x₀ = uInf x₀)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hstrict : ∀ y ∈ closedBall x₀ r, φ y + δ * ‖y - x₀‖ ^ 4 ≤ uInf y)
    (hΔ : 0 < Δ φ x₀) (hfb : 0 < φ x₀ ∨ Q x₀ < ‖∇ φ x₀‖) : False := by
  obtain ⟨hucont, hunn, hcomp⟩ := hu
  have huInf : ContinuousOn uInf U := continuousOn_limit hucont hconv
  have hx₀nn : 0 ≤ uInf x₀ := limit_nonneg hunn hconv x₀ hx₀U
  -- (TR-174) `φ + a` is a strict subsolution of [(1.1)](#AFS:e.bernoulli-basic) in `B̄_ρ(x₀)` for
  -- all `|a| ≤ a₁`, with
  -- `φ + a₁ < u_∞` on `∂B_ρ(x₀)` and `φ - a₁ < u_∞` on `B̄_ρ(x₀)`
  obtain ⟨ρ, hρ, hρr, hρU, a₀, ha₀, η₀, hη₀, hshift⟩ :=
    exists_strictSub_shift hU hQ hφ hx₀U hr hΔ hfb
  set a₁ := min (a₀ / 2) (δ * ρ ^ 4 / 2) with ha₁_def
  have ha₁ : 0 < a₁ := lt_min (by positivity) (by positivity)
  have ha₁a₀ : 2 * a₁ ≤ a₀ := by linarith [min_le_left (a₀ / 2) (δ * ρ ^ 4 / 2)]
  have hbdInf : PrecOn (fun y ↦ φ y + a₁) uInf univ (sphere x₀ ρ) := by
    rintro y ⟨-, hy⟩
    have h1 := hstrict y (closedBall_subset_closedBall hρr (sphere_subset_closedBall hy))
    rw [mem_sphere_iff_norm.1 hy] at h1
    have h2 : a₁ ≤ δ * ρ ^ 4 / 2 := min_le_right _ _
    have h3 : 0 < δ * ρ ^ 4 := by positivity
    linarith
  have hinInf : PrecOn (fun y ↦ φ y - a₁) uInf univ (closedBall x₀ ρ) := by
    rintro y ⟨-, hy⟩
    have h1 := hstrict y (closedBall_subset_closedBall hρr hy)
    have h2 : 0 ≤ δ * ‖y - x₀‖ ^ 4 := by positivity
    linarith
  -- by uniform convergence on `B̄_ρ(x₀)`, both inequalities hold for `u(·, t)`, `t ≥ T`
  have ebd := precOn_eventually_of_tendsto (u := fun y ↦ φ y + a₁) (isCompact_sphere x₀ ρ)
    (hφ.continuous.add continuous_const).continuousOn
    (huInf.mono (sphere_subset_closedBall.trans hρU)) hbdInf
    (tendstoUniformlyOn_const_family _ _)
    (tendstoUniformlyOn_comp_of_tendsto hU hconv (isCompact_sphere x₀ ρ)
      (sphere_subset_closedBall.trans hρU) tendsto_id) (E' := fun _ ↦ univ) (subset_univ _)
  have ein := precOn_eventually_of_tendsto (u := fun y ↦ φ y - a₁) (isCompact_closedBall x₀ ρ)
    (hφ.continuous.sub continuous_const).continuousOn (huInf.mono hρU) hinInf
    (tendstoUniformlyOn_const_family _ _)
    (tendstoUniformlyOn_comp_of_tendsto hU hconv (isCompact_closedBall x₀ ρ) hρU tendsto_id)
    (E' := fun _ ↦ univ) (subset_univ _)
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((ebd.and ein).and (eventually_gt_atTop 0))
  have hT0 : 0 < T := (hT T le_rfl).2
  -- the barrier `ψ(x, t) = φ(x) - a₁ ζ(η (t - T))`, `η` small
  obtain ⟨C, hC⟩ := exists_abs_deriv_timeCutoff_le
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set η := η₀ / (2 * (a₁ * C + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hηC : a₁ * (η * C) < η₀ := by
    have hden : 0 < 2 * (a₁ * C + 1) := by positivity
    have : a₁ * (η * C) = η₀ * (a₁ * C) / (2 * (a₁ * C + 1)) := by rw [hη_def]; ring
    rw [this, div_lt_iff₀ hden]
    nlinarith [mul_nonneg ha₁.le hC0]
  set g : ℝ → ℝ := fun t ↦ (-a₁) * timeCutoff (η * (t - T)) with hg_def
  have hg : ContDiff ℝ ∞ g := contDiff_cutoffTime (-a₁) η T
  have hgabs : ∀ t, |g t| ≤ a₁ := fun t => by
    rw [hg_def, abs_mul, abs_neg, abs_of_pos ha₁]
    exact mul_le_of_le_one_right ha₁.le (abs_timeCutoff_le_one _)
  have hgT : g T = -a₁ := by simp [hg_def, timeCutoff_of_nonpos]
  have hgd : ∀ t, deriv g t ≤ a₁ * (η * C) := fun t => by
    have h := abs_deriv_cutoffTime_le (a₁ := a₁) ha₁.le hη.le hC T t
    have hneg : g = -fun t ↦ a₁ * timeCutoff (η * (t - T)) := by
      funext t; simp [hg_def, neg_mul]
    rw [hneg, deriv.neg]
    exact (neg_le_abs _).trans h
  set ψ : E d × ℝ → ℝ := fun p ↦ φ p.1 + g p.2 with hψ_def
  -- `ψ` is a classical strict subsolution on `B̄_ρ(x₀) × [T, b]`, for every `b`, with the
  -- uniform constants `min a₁ (1/2)` and `δ₀` (as in the proof of
  -- [Proposition 5.5](#AFS:p.subsolution-limit))
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ ρ).exists_bound_of_continuousOn (hQ.mono hρU)
  have hηC' : a₁ * (η * C) ≤ η₀ / 2 := by
    have hden : 0 < 2 * (a₁ * C + 1) := by positivity
    have : a₁ * (η * C) = η₀ * (a₁ * C) / (2 * (a₁ * C + 1)) := by rw [hη_def]; ring
    rw [this, div_le_iff₀ hden]
    nlinarith [mul_nonneg ha₁.le hC0]
  set δ₀ := min (min (η₀ / 2) (η₀ / (|M| + 1))) (1 / 2) with hδ₀_def
  have hδ₀ : 0 < δ₀ := lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hδ₀η : δ₀ ≤ η₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₀M : δ₀ * (|M| + 1) ≤ η₀ := by
    have : δ₀ ≤ η₀ / (|M| + 1) := (min_le_left _ _).trans (min_le_right _ _)
    calc δ₀ * (|M| + 1) ≤ η₀ / (|M| + 1) * (|M| + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = η₀ := by field_simp
  have hsub : ∀ b, IsClassicalStrictParaSub Q ψ (ball x₀ ρ) T b := fun b => by
    refine ⟨min a₁ (1 / 2), δ₀, contDiff_addTime hφ hg, lt_min ha₁ (by norm_num),
      min_le_right _ _, hδ₀, min_le_right _ _, ?_, ?_⟩
    · rintro ⟨y, t⟩ ⟨-, hy, -⟩
      rw [closure_ball x₀ hρ.ne'] at hy
      rw [hψ_def, dₜ_addTime, lapₓ_addTime hφ]
      have h1 := (hshift y hy).1
      have h2 := hgd t
      simp only at h1 h2 ⊢
      linarith
    · rintro ⟨y, t⟩ ⟨hψy, hy, -⟩
      rw [closure_ball x₀ hρ.ne'] at hy
      have hψy' : |φ y + g t| ≤ min a₁ (1 / 2) := hψy
      have ha : |-φ y| ≤ a₀ := by
        have := abs_sub (g t) (φ y + g t)
        rw [show g t - (φ y + g t) = -φ y by ring] at this
        linarith [hgabs t, min_le_left a₁ (1 / 2)]
      have h := (hshift y hy).2 (-φ y) ha (by ring)
      have hQM : Q y ≤ |M| + 1 := by
        have := hM y hy
        rw [Real.norm_eq_abs] at this
        linarith [le_abs_self (Q y), le_abs_self M]
      rw [hψ_def, gradₓ_addTime]
      exact one_add_mul_sq_le (hQ0 y (hρU hy)) h.le hη₀ hQM hδ₀.le hδ₀M
  -- for every `b ≥ T + 1/η`: `u(x₀, b) > φ(x₀) + a₁` (no set `E` and no sequence needed)
  have hcontra : ∀ᶠ b in atTop, φ x₀ + a₁ < u (x₀, b) := by
    filter_upwards [eventually_ge_atTop (T + 1 / η)] with b hb
    have hTb : T < b := by linarith [one_div_pos.2 hη]
    have hadm : AdmissibleCyl U (Ioi 0) (ball x₀ ρ) T b := by
      refine ⟨isOpen_ball, isBounded_ball, hTb, ?_⟩
      rw [closure_ball x₀ hρ.ne']
      rintro ⟨y, t⟩ ⟨hy, ht⟩
      exact ⟨hρU hy, lt_of_lt_of_le hT0 ht.1⟩
    -- `ψ < u` on `∂_P(B_ρ(x₀) × (T, b])`, in particular `ψ ≺ u` there
    have hbdry : Prec ψ u univ (parBdry (ball x₀ ρ) T b) := by
      rintro ⟨y, t⟩ ⟨-, hB⟩
      rw [parBdry, closure_ball x₀ hρ.ne', frontier_ball x₀ hρ.ne'] at hB
      rcases hB with ⟨hy, ht⟩ | ⟨hy, ht⟩
      · have ht' : t = T := ht
        subst ht'
        have := (hT t le_rfl).1.2 y ⟨mem_univ _, hy⟩
        simp only [hψ_def, hgT, id] at this ⊢
        linarith
      · have h1 := (hT t ht.1).1.1 y ⟨mem_univ _, hy⟩
        have h2 := (abs_le.1 (hgabs t)).2
        simp only [hψ_def, id] at h1 h2 ⊢
        linarith
    have hζ : timeCutoff (η * (b - T)) = -1 := timeCutoff_of_one_le (by
      have h := mul_le_mul_of_nonneg_left (show 1 / η ≤ b - T by linarith) hη.le
      rwa [mul_one_div_cancel hη.ne'] at h)
    have hψb : ψ (x₀, b) = φ x₀ + a₁ := by simp [hψ_def, hg_def, hζ]
    -- `ψ(x₀, b) = u_∞(x₀) + a₁ > 0`, so `(x₀, b) ∈ \overline{{ψ > 0}}`
    have hmem : (x₀, b) ∈ closure (posSetP ψ univ) ∩ cyl (ball x₀ ρ) T b := by
      refine ⟨subset_closure ⟨mem_univ _, ?_⟩, mem_ball_self hρ, hTb, le_rfl⟩
      rw [hψb]
      linarith
    have hcon := hcomp (ball x₀ ρ) T b ψ hadm (hsub b) hbdry (x₀, b) hmem
    rwa [hψb] at hcon
  -- let `b → ∞`
  have := ge_of_tendsto (hconv.tendsto_at hx₀U) (hcontra.mono fun b hb => hb.le)
  linarith

/-! ### Relaxed subsolutions contained in the closure of the positivity set -/

/-- A relaxed subsolution `(v, F)` with `F ⊆ \overline{{v > 0}}` is a viscosity subsolution (the
remark after [Definition 2.4](#AFS:d.relaxed-sub-stationary)). The test in
[Definition 2.1(ii)](#AFS:d.stationary-viscosity) is by `φ₊`; by density of `{v > 0}` in
`\overline{{v > 0}}`, if `φ₊` touches `v` from above in `\overline{{v > 0}} ∩ U` then so does
`φ`. -/
theorem isViscSub_of_isRelaxedSub {v : E d → ℝ} {F : Set (E d)} (hU : IsOpen U)
    (hv : IsRelaxedSub U Q v F) (hF : F ⊆ closure (posSet v U)) : IsViscSub U Q v := by
  obtain ⟨hvc, hvnn, hFcl, -, hFpos, htest⟩ := hv
  refine ⟨hvc, hvnn, fun φ hφ x htouch => htest φ hφ x ?_⟩
  obtain ⟨⟨hxcl, hxU⟩, hx_eq, hle⟩ := htouch
  have hxF : x ∈ F := (hFcl.closure_subset_iff.2 hFpos) hxcl
  rw [eventually_nhdsWithin_iff] at hle
  obtain ⟨W, hW, hWo, hxW⟩ := _root_.eventually_nhds_iff.1 hle
  have key : ∀ y ∈ W, y ∈ closure (posSet v U) → y ∈ U → v y ≤ φ y := by
    intro y hyW hycl hyU
    by_contra hlt
    push Not at hlt
    have hcy : ContinuousAt (fun z ↦ v z - φ z) y :=
      (hvc.continuousAt (hU.mem_nhds hyU)).sub hφ.continuous.continuousAt
    have hN : {z | 0 < v z - φ z} ∩ W ∈ 𝓝 y :=
      inter_mem (hcy.eventually (lt_mem_nhds (by linarith))) (hWo.mem_nhds hyW)
    obtain ⟨z, ⟨hz1, hzW⟩, hzU, hzpos⟩ := mem_closure_iff_nhds.1 hycl _ hN
    have hz := hW z hzW ⟨subset_closure ⟨hzU, hzpos⟩, hzU⟩
    have hz1' : 0 < v z - φ z := hz1
    have : max (φ z) 0 < v z := max_lt (by linarith) hzpos
    linarith
  have hxle := key x hxW hxcl hxU
  refine ⟨⟨hxF, hxU⟩, ?_, ?_⟩
  · have h0 : 0 ≤ φ x := by
      have := le_max_right (φ x) 0
      linarith
    rw [← hx_eq]
    exact (max_eq_left h0).symm
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [hWo.mem_nhds hxW] with y hyW hy
    exact key y hyW (hF hy.1) hy.2

/-- A parabolic subsolution is a relaxed subsolution with `E = \overline{{u > 0}}` (the remark after
[Definition 3.5](#AFS:d.parabolic-relaxed-subsolution)). -/
theorem isParaRelaxedSub_of_isParaSub {I : Set ℝ} (hu : IsParaSub U Q I u) :
    IsParaRelaxedSub U Q I u (closure (posSetP u (U ×ˢ I))) := by
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨h1, h2, isClosed_closure, ?_, subset_closure, h3⟩
  rw [← closure_prod_eq]
  exact closure_mono fun p hp => hp.1

/-- For a time-increasing `u`, the upper Kuratowski limit of the slices of `\overline{{u > 0}}`
lies in `\overline{{u_∞ > 0}}` (proof of [Corollary 5.7](#AFS:c.monotone-long-time)). -/
theorem upperKLimit_subset_closure_posSet (hmono : MonotoneInTime u U (Ioi 0))
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    upperKLimit (timeSlice (closure (posSetP u (U ×ˢ Ioi 0)))) atTop ⊆
      closure (posSet uInf U) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨V, hVN, hVo, hxV⟩ := _root_.mem_nhds_iff.1 hN
  obtain ⟨t, y, hyE, hyV⟩ := (hx V (hVo.mem_nhds hxV)).exists
  obtain ⟨⟨y', t'⟩, ⟨hV', -⟩, ⟨hy'U, ht'⟩, hpos⟩ := mem_closure_iff_nhds.1 hyE (V ×ˢ univ)
    (prod_mem_nhds (hVo.mem_nhds hyV) univ_mem)
  exact ⟨y', hVN hV', hy'U, hpos.trans_le (le_limit hmono hconv hy'U ht')⟩

end LongTime

open LongTime

variable {U : Set (E d)} {Q : E d → ℝ} {u : E d × ℝ → ℝ} {uInf : E d → ℝ}

/-- **[Proposition 5.6](#AFS:p.supersolution-limit)**. If `u` is a parabolic viscosity
supersolution in `U × (0, ∞)` and `u(·, t) → u_∞` locally uniformly in `U` as `t → ∞`, then `u_∞`
is a viscosity supersolution of [(1.1)](#AFS:e.bernoulli-basic) in `U`. (The paper's boundedness
assumption is not needed; `Q` is assumed continuous and nonnegative on `U`, as in the standing
assumptions; nonnegativity enters through the squared gradient condition of the classical strict
subsolutions.) -/
theorem longtime_super (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x)
    (hu : IsParaSuper U Q (Ioi 0) u)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    IsViscSuper U Q uInf := by
  refine ⟨continuousOn_limit hu.1 hconv, limit_nonneg hu.2.1 hconv, ?_⟩
  intro φ hφ x₀ hx₀U htouch
  obtain ⟨-, hφx₀, hle⟩ := htouch
  rw [hU.nhdsWithin_eq hx₀U] at hle
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.eventually_nhds_iff_ball.1 hle
  have hr : 0 < r₁ / 2 := half_pos hr₁
  have hsub : closedBall x₀ (r₁ / 2) ⊆ ball x₀ r₁ := closedBall_subset_ball (half_lt_self hr₁)
  by_contra hcon
  push Not at hcon
  obtain ⟨hΔ, hfb0⟩ := hcon
  have hx₀nn : 0 ≤ uInf x₀ := limit_nonneg hu.2.1 hconv x₀ hx₀U
  have hfb : 0 < φ x₀ ∨ Q x₀ < ‖∇ φ x₀‖ := by
    rcases (hφx₀ ▸ hx₀nn : 0 ≤ φ x₀).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr (hfb0 h.symm)
  -- perturb by `-δ ‖y - x₀‖⁴`; the paper takes any `C > 0` (`Δ` and `∇` of the quartic
  -- vanish at `x₀`), here `δ` small suffices and `Δ w x₀` is never computed
  set w : E d → ℝ := fun y ↦ ‖y - x₀‖ ^ 4 with hw_def
  have hw : ContDiff ℝ ∞ w := contDiff_quartDist x₀
  have hlim1 : Tendsto (fun δ : ℝ ↦ Δ φ x₀ + (-δ) * Δ w x₀) (𝓝 0) (𝓝 (Δ φ x₀)) := by
    have : Continuous (fun δ : ℝ ↦ Δ φ x₀ + (-δ) * Δ w x₀) := by fun_prop
    simpa using this.tendsto 0
  have hlim2 : Tendsto (fun δ : ℝ ↦ ‖∇ φ x₀ + (-δ) • ∇ w x₀‖) (𝓝 0) (𝓝 ‖∇ φ x₀‖) := by
    have : Continuous (fun δ : ℝ ↦ ‖∇ φ x₀ + (-δ) • ∇ w x₀‖) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ 0 < Δ φ x₀ + (-δ) * Δ w x₀ ∧
      (0 < φ x₀ ∨ Q x₀ < ‖∇ φ x₀ + (-δ) • ∇ w x₀‖) := by
    refine (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ from self_mem_nhdsWithin).and ?_
    refine nhdsWithin_le_nhds ?_
    rcases hfb with hpos | hgrad
    · filter_upwards [hlim1.eventually (lt_mem_nhds hΔ)] with δ h1 using ⟨h1, Or.inl hpos⟩
    · filter_upwards [hlim1.eventually (lt_mem_nhds hΔ), hlim2.eventually (lt_mem_nhds hgrad)]
        with δ h1 h2 using ⟨h1, Or.inr h2⟩
  obtain ⟨δ, hδ, hΔδ, hfbδ⟩ := hev.exists
  have hφδ : ContDiff ℝ ∞ (fun y ↦ φ y + (-δ) * w y) := hφ.add (contDiff_const.mul hw)
  refine super_core hU hQ hQ0 hu hconv hφδ hx₀U (by simp [hw_def, hφx₀]) hδ hr
    (fun y hy => ?_) ?_ ?_
  · have := hr₁' y (hsub hy)
    simp only [hw_def]
    linarith
  · rwa [laplacian_add_mul hφ hw]
  · rw [gradient_add_mul (hφ.differentiable (by simp)) (hw.differentiable (by simp))]
    simpa [hw_def] using hfbδ

/-- **[Proposition 5.5](#AFS:p.subsolution-limit)**, with `E_∞ := limsup*_{t → ∞} E_t`. If
`(u, E)` is a parabolic relaxed subsolution in `U × (0, ∞)` and `u(·, t) → u_∞` locally uniformly
in `U`, then `(u_∞, limsup*_{t → ∞} E_t)` is a relaxed subsolution of
[(1.1)](#AFS:e.bernoulli-basic) in `U`. (The paper's boundedness assumption is not needed.) -/
theorem longtime_relaxedSub (hU : IsOpen U) (hQ : ContinuousOn Q U) {Eset : Set (E d × ℝ)}
    (hu : IsParaRelaxedSub U Q (Ioi 0) u Eset)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    IsRelaxedSub U Q uInf (upperKLimit (timeSlice Eset) atTop) := by
  have hu' := hu
  obtain ⟨hucont, hunn, -, hEsub, hEpos, -⟩ := hu'
  refine ⟨continuousOn_limit hucont hconv, limit_nonneg hunn hconv, isClosed_upperKLimit,
    ?_, ?_, ?_⟩
  · intro x hx
    by_contra hxU
    obtain ⟨t, z, hzE, hzU⟩ :=
      (hx (closure U)ᶜ (isClosed_closure.isOpen_compl.mem_nhds hxU)).exists
    exact hzU (hEsub hzE).1
  · rintro x ⟨hxU, hxpos⟩ N hN
    have hev : ∀ᶠ t in atTop, 0 < u (x, t) :=
      (hconv.tendsto_at hxU).eventually (lt_mem_nhds hxpos)
    refine Eventually.frequently ?_
    filter_upwards [hev, eventually_gt_atTop 0] with t ht ht0
    exact ⟨x, hEpos ⟨⟨hxU, ht0⟩, ht⟩, mem_of_mem_nhds hN⟩
  · intro φ hφ x₀ htouch
    obtain ⟨⟨hx₀E, hx₀U⟩, hφx₀, hle⟩ := htouch
    obtain ⟨r₁, hr₁, h1⟩ := Metric.mem_nhdsWithin_iff.1 hle
    obtain ⟨r₂, hr₂, h2⟩ := Metric.isOpen_iff.1 hU x₀ hx₀U
    set r := min r₁ r₂ / 2 with hr_def
    have hr12 : 0 < min r₁ r₂ := lt_min hr₁ hr₂
    have hr : 0 < r := half_pos hr12
    have hsub : closedBall x₀ r ⊆ ball x₀ (min r₁ r₂) := closedBall_subset_ball (half_lt_self hr12)
    have hrU : closedBall x₀ r ⊆ U :=
      hsub.trans ((ball_subset_ball (min_le_right _ _)).trans h2)
    by_contra hcon
    push Not at hcon
    obtain ⟨hΔ, hfb0⟩ := hcon
    have hx₀nn : 0 ≤ uInf x₀ := limit_nonneg hunn hconv x₀ hx₀U
    have hfb : 0 < φ x₀ ∨ ‖∇ φ x₀‖ < Q x₀ := by
      rcases (hφx₀ ▸ hx₀nn : 0 ≤ φ x₀).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr (hfb0 h.symm)
    -- perturb by `+δ ‖y - x₀‖⁴`; the paper takes any `C > 0` (`Δ` and `∇` of the quartic
    -- vanish at `x₀`), here `δ` small suffices and `Δ w x₀` is never computed
    set w : E d → ℝ := fun y ↦ ‖y - x₀‖ ^ 4 with hw_def
    have hw : ContDiff ℝ ∞ w := contDiff_quartDist x₀
    have hlim1 : Tendsto (fun δ : ℝ ↦ Δ φ x₀ + δ * Δ w x₀) (𝓝 0) (𝓝 (Δ φ x₀)) := by
      have : Continuous (fun δ : ℝ ↦ Δ φ x₀ + δ * Δ w x₀) := by fun_prop
      simpa using this.tendsto 0
    have hlim2 : Tendsto (fun δ : ℝ ↦ ‖∇ φ x₀ + δ • ∇ w x₀‖) (𝓝 0) (𝓝 ‖∇ φ x₀‖) := by
      have : Continuous (fun δ : ℝ ↦ ‖∇ φ x₀ + δ • ∇ w x₀‖) := by fun_prop
      simpa using this.tendsto 0
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ Δ φ x₀ + δ * Δ w x₀ < 0 ∧
        (0 < φ x₀ ∨ ‖∇ φ x₀ + δ • ∇ w x₀‖ < Q x₀) := by
      refine (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ from self_mem_nhdsWithin).and ?_
      refine nhdsWithin_le_nhds ?_
      rcases hfb with hpos | hgrad
      · filter_upwards [hlim1.eventually (gt_mem_nhds hΔ)] with δ h1 using ⟨h1, Or.inl hpos⟩
      · filter_upwards [hlim1.eventually (gt_mem_nhds hΔ), hlim2.eventually (gt_mem_nhds hgrad)]
          with δ h1 h2 using ⟨h1, Or.inr h2⟩
    obtain ⟨δ, hδ, hΔδ, hfbδ⟩ := hev.exists
    have hφδ : ContDiff ℝ ∞ (fun y ↦ φ y + δ * w y) := hφ.add (contDiff_const.mul hw)
    refine relaxedSub_core hU hQ hu hconv hφδ hx₀U hx₀E (by simp [hw_def, hφx₀]) hδ hr
      (fun y hy hyE => ?_) ?_ ?_
    · have hyU : y ∈ U := hrU hy
      have := h1 ⟨(hsub.trans (ball_subset_ball (min_le_left _ _))) hy, hyE, hyU⟩
      simp only [hw_def, Set.mem_ofPred_eq] at this ⊢
      linarith
    · rwa [laplacian_add_mul hφ hw]
    · rw [gradient_add_mul (hφ.differentiable (by simp)) (hw.differentiable (by simp))]
      simpa [hw_def] using hfbδ

/-- **[Proposition 5.5](#AFS:p.subsolution-limit)** with the set `limsup*_{T → ∞} ⋂_{t ≥ T} E_t`,
under the extra hypothesis that the slices `E_t` are monotone in `t` (then the two candidate sets
coincide). -/
theorem longtime_relaxedSub_of_slicesMonotone (hU : IsOpen U) (hQ : ContinuousOn Q U)
    {Eset : Set (E d × ℝ)} (hu : IsParaRelaxedSub U Q (Ioi 0) u Eset)
    (hmono : SlicesMonotone Eset (Ioi 0))
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    IsRelaxedSub U Q uInf (upperKLimit (fun T ↦ ⋂ t ≥ T, timeSlice Eset t) atTop) := by
  have : upperKLimit (fun T ↦ ⋂ t ≥ T, timeSlice Eset t) atTop =
      upperKLimit (timeSlice Eset) atTop := by
    refine upperKLimit_congr ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact Subset.antisymm (iInter₂_subset T le_rfl)
      (subset_iInter₂ fun t ht => hmono T hT t (hT.trans_le ht) ht)
  rw [this]
  exact longtime_relaxedSub hU hQ hu hconv

/-- **[Corollary 5.7](#AFS:c.monotone-long-time)**. If `u` is a parabolic viscosity subsolution in
`U × (0, ∞)`, monotonically increasing in time, with `u(·, t) → u_∞` locally uniformly in `U`,
then `u_∞` is a viscosity subsolution of [(1.1)](#AFS:e.bernoulli-basic) in `U`. (Boundedness is not
needed.) -/
theorem longtime_sub_increasing (hU : IsOpen U) (hQ : ContinuousOn Q U)
    (hu : IsParaSub U Q (Ioi 0) u) (hmono : MonotoneInTime u U (Ioi 0))
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    IsViscSub U Q uInf :=
  isViscSub_of_isRelaxedSub hU (longtime_relaxedSub hU hQ (isParaRelaxedSub_of_isParaSub hu) hconv)
    (upperKLimit_subset_closure_posSet hmono hconv)

/-- **[Theorem 3.16(i)](#AFS:part.longtime-viscosity-1)**: a bounded, time-increasing parabolic
viscosity solution converges (locally uniformly) to a stationary viscosity solution. -/
theorem longtime_viscosity_increasing : LongtimeViscIncreasingStatement := by
  intro d S u uInf hu _ hmono hconv
  have hQ : ContinuousOn S.Q S.U := by
    obtain ⟨K, hK⟩ := S.lip
    exact hK.continuousOn.mono subset_closure
  exact ⟨longtime_super S.isOpen hQ
      (fun x hx ↦ S.Qmin_pos.le.trans (S.Q_mem x (subset_closure hx)).1) hu.1 hconv,
    longtime_sub_increasing S.isOpen hQ hu.2 hmono hconv⟩

end PerronVariational

end
