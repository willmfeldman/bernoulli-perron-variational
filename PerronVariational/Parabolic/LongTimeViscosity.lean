/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Long-time viscosity limits (Lemmas 5.5, 5.6, Corollary 5.7, Theorem 3.12(i))

Results of Section 5 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

* `longtime_super` (**Lemma 5.6**): the locally uniform
  `t → ∞` limit of a parabolic viscosity supersolution is a stationary viscosity supersolution.
* `longtime_relaxedSub` (**Lemma 5.5**): the limit of a parabolic relaxed subsolution `(u, E)` is a
  stationary relaxed subsolution with the set `upperKLimit (timeSlice E) atTop` (the upper
  Kuratowski limit of the time slices `E_t`). `longtime_relaxedSub_of_slicesMonotone` gives the
  paper's set `limsup*_{T → ∞} ⋂_{t ≥ T} E_t` when the slices are monotone (see the section on the
  limit set below).
* `longtime_sub_increasing` (**Corollary 5.7**).
* `longtime_viscosity_increasing : LongtimeViscIncreasingStatement`
  (**Theorem 3.12(i)**).

## Proof strategy

The parabolic notions (Definitions 3.2 and 3.4) are comparison-based. Instead of first deriving
pointwise touching properties at first-touching points (the paper's route, which needs to rule out
"outward jumps" of `E`), we argue by contradiction directly with the comparison property: if the
stationary test fails at `x₀` for a (strictly perturbed) test function `φ`, then
`ψ(x, t) = φ(x) ± c' ∓ η (t - a)` is a classical strict parabolic super/subsolution on a small
cylinder `B_ρ(x₀) × (a, b]` at a large time `a`, strictly ordered with `u` on the parabolic
boundary (by locally uniform convergence and the strict touching), but not at the top time `b`.

## The limit set in Lemma 5.5 (deviation from the paper)

The paper's `E_∞ := limsup*_{T → ∞} ⋂_{t ≥ T} E_t` is contained in
`upperKLimit (timeSlice E) atTop = limsup*_{t → ∞} E_t`; the proof of Lemma 5.5 applies Lemma 5.1
to the sets `E_{t_n}`, which requires `limsup*_n E_{t_n} ⊆ E_∞`: this holds for the larger
set but not in general for the paper's one. The two sets coincide when the slices `E_t` are
monotone (the case used in Corollary 5.7). We therefore prove Lemma 5.5 with the larger (weaker)
set, and the paper's form under `SlicesMonotone`.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

namespace LongTime

/-! ### Topological helpers -/

/-- The upper Kuratowski limit is closed. -/
theorem isClosed_upperKLimit {X ι : Type*} [TopologicalSpace X] (A : ι → Set X)
    (l : Filter ι) : IsClosed (upperKLimit A l) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, upperKLimit, mem_setOf_eq, not_forall] at hx
  obtain ⟨N, hN, hfreq⟩ := hx
  obtain ⟨V, hVN, hVo, hxV⟩ := mem_nhds_iff.1 hN
  refine mem_of_superset (hVo.mem_nhds hxV) fun y hy hyA => hfreq ?_
  exact (hyA V (hVo.mem_nhds hy)).mono fun i hi => hi.mono (inter_subset_inter_right _ hVN)

/-- Upper Kuratowski limits of eventually equal families agree. -/
theorem upperKLimit_congr {X ι : Type*} [TopologicalSpace X] {A B : ι → Set X} {l : Filter ι}
    (h : ∀ᶠ i in l, A i = B i) : upperKLimit A l = upperKLimit B l := by
  ext x
  simp only [upperKLimit, mem_setOf_eq]
  refine forall₂_congr fun N _ => ⟨fun hA => ?_, fun hB => ?_⟩
  · exact (hA.and_eventually h).mono fun i hi => hi.2 ▸ hi.1
  · exact (hB.and_eventually h).mono fun i hi => hi.2 ▸ hi.1

/-- A compactness principle: a property holding eventually (uniformly on a neighbourhood of each
point of a compact set `K`) holds eventually uniformly on `K`. -/
theorem eventually_forall_of_isCompact {X ι : Type*} [TopologicalSpace X] {l : Filter ι}
    {K : Set X} (hK : IsCompact K) {P : ι → X → Prop}
    (h : ∀ y ∈ K, ∃ N ∈ 𝓝 y, ∀ᶠ i in l, ∀ z ∈ N, P i z) :
    ∀ᶠ i in l, ∀ z ∈ K, P i z := by
  have : {q : ι × X | P q.1 q.2} ∈ l ×ˢ 𝓝ˢ K := by
    refine hK.mem_prod_nhdsSet_of_forall fun y hy => ?_
    obtain ⟨N, hN, hev⟩ := h y hy
    exact mem_of_superset (prod_mem_prod hev hN) fun q hq => hq.1 q.2 hq.2
  exact (Filter.Eventually.curry this).mono fun i hi => hi.self_of_nhdsSet

/-! ### The limit function -/

variable {U : Set (E d)} {Q : E d → ℝ} {u : E d × ℝ → ℝ} {uInf : E d → ℝ}

/-- Locally uniform convergence gives uniform convergence on compact subsets. -/
theorem eventually_abs_sub_lt (hU : IsOpen U)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) {K : Set (E d)}
    (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ y ∈ K, |u (y, t) - uInf y| < ε := by
  have h := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at h
  filter_upwards [h ε hε] with t ht y hy
  simpa [Real.dist_eq, abs_sub_comm] using ht y hy

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

/-- The strict-ordering lemma (compare Lemmas 5.1–5.2): if `u_∞ - φ < κ` on
`K ∩ limsup*_t E_t`, then eventually `u(·, t) - φ < κ` on `K ∩ E_t`. -/
theorem eventually_sub_lt_of_upperKLimit (hU : IsOpen U) (huInf : ContinuousOn uInf U)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) {φ : E d → ℝ}
    (hφ : Continuous φ) {Eset : Set (E d × ℝ)} {K : Set (E d)} (hK : IsCompact K)
    (hKU : K ⊆ U) {κ : ℝ}
    (h : ∀ y ∈ K, y ∈ upperKLimit (timeSlice Eset) atTop → uInf y - φ y < κ) :
    ∀ᶠ t in atTop, ∀ y ∈ K, (y, t) ∈ Eset → u (y, t) - φ y < κ := by
  have key : ∀ᶠ t in atTop, ∀ z ∈ K, z ∈ K → (z, t) ∈ Eset → u (z, t) - φ z < κ := by
    refine eventually_forall_of_isCompact hK fun y hy => ?_
    by_cases hyE : y ∈ upperKLimit (timeSlice Eset) atTop
    · have hlt := h y hy hyE
      set ε := (κ - (uInf y - φ y)) / 2 with hε_def
      have hε : 0 < ε := by rw [hε_def]; linarith
      have hcy : ContinuousAt (fun z ↦ uInf z - φ z) y :=
        (huInf.continuousAt (hU.mem_nhds (hKU hy))).sub hφ.continuousAt
      have hN : {z | uInf z - φ z < κ - ε} ∈ 𝓝 y :=
        hcy.preimage_mem_nhds (Iio_mem_nhds (by rw [hε_def]; linarith))
      refine ⟨_, hN, ?_⟩
      filter_upwards [eventually_abs_sub_lt hU hconv hK hKU hε] with t ht z hz hzK _
      have := (abs_lt.1 (ht z hzK)).2
      have hz' : uInf z - φ z < κ - ε := hz
      linarith
    · simp only [upperKLimit, mem_setOf_eq, not_forall, not_frequently] at hyE
      obtain ⟨N, hN, hev⟩ := hyE
      refine ⟨N, hN, ?_⟩
      filter_upwards [hev] with t ht z hz _ hzE
      exact absurd ⟨z, hzE, hz⟩ ht
  filter_upwards [key] with t ht y hy using ht y hy hy

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

/-- The space-time test function `ψ(x, t) = φ(x) + α + β t`. -/
theorem contDiff_affineTime {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) (α β : ℝ) :
    ContDiff ℝ ∞ (fun p : E d × ℝ ↦ φ p.1 + α + β * p.2) :=
  ((hφ.comp contDiff_fst).add contDiff_const).add (contDiff_const.mul contDiff_snd)

theorem dₜ_affineTime (φ : E d → ℝ) (α β : ℝ) (p : E d × ℝ) :
    dₜ (fun p : E d × ℝ ↦ φ p.1 + α + β * p.2) p = β := by
  have : HasDerivAt (fun s ↦ φ p.1 + α + β * s) β p.2 := by
    simpa using HasDerivAt.const_add (φ p.1 + α) (HasDerivAt.const_mul β (hasDerivAt_id p.2))
  exact this.deriv

theorem lapₓ_affineTime {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) (α β : ℝ) (p : E d × ℝ) :
    lapₓ (fun p : E d × ℝ ↦ φ p.1 + α + β * p.2) p = Δ φ p.1 := by
  have h1 : ContDiffAt ℝ 2 φ p.1 := (hφ.of_le two_le_infty).contDiffAt
  have hfun : (fun y ↦ φ y + α + β * p.2) = φ + fun _ ↦ α + β * p.2 := by
    funext y; simp [add_assoc]
  simp only [lapₓ]
  rw [hfun, h1.laplacian_add contDiffAt_const, InnerProductSpace.laplacian_const]
  simp

theorem gradₓ_affineTime (φ : E d → ℝ) (α β : ℝ) (p : E d × ℝ) :
    gradₓ (fun p : E d × ℝ ↦ φ p.1 + α + β * p.2) p = ∇ φ p.1 := by
  have hfun : (fun y ↦ φ y + α + β * p.2) = fun y ↦ φ y + (α + β * p.2) := by
    funext y; ring
  simp only [gradₓ, hfun, gradient, fderiv_add_const]

/-! ### The comparison cores -/

/-- Core of **Lemma 5.5**: a strict touching from above of `u_∞` in `limsup*_t E_t` at `x₀` by a
smooth `φ` which is a strict stationary supersolution at `x₀` contradicts the parabolic relaxed
subsolution property (Definition 3.4). -/
theorem relaxedSub_core (hU : IsOpen U) (hQ : ContinuousOn Q U) {Eset : Set (E d × ℝ)}
    (hu : IsParaRelaxedSub U Q (Ioi 0) u Eset)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀U : x₀ ∈ U)
    (hx₀E : x₀ ∈ upperKLimit (timeSlice Eset) atTop) (hφx₀ : φ x₀ = uInf x₀)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hrU : closedBall x₀ r ⊆ U)
    (hstrict : ∀ y ∈ closedBall x₀ r, y ∈ upperKLimit (timeSlice Eset) atTop →
      uInf y ≤ φ y - δ * ‖y - x₀‖ ^ 2)
    (hΔ : Δ φ x₀ < 0) (hfb : 0 < φ x₀ ∨ ‖∇ φ x₀‖ < Q x₀) : False := by
  obtain ⟨hucont, -, -, -, -, hcomp⟩ := hu
  have huInf : ContinuousOn uInf U := continuousOn_limit hucont hconv
  set η := -Δ φ x₀ / 2 with hη_def
  have hη : 0 < η := by rw [hη_def]; linarith
  -- a neighbourhood of `x₀` on which `φ` is a strict supersolution
  have hG : ∀ᶠ y in 𝓝 x₀,
      Δ φ y < -η ∧ ((0 < φ x₀ ∧ φ x₀ / 2 < φ y) ∨ ‖∇ φ y‖ < Q y) := by
    have h1 : ∀ᶠ y in 𝓝 x₀, Δ φ y < -η :=
      (continuous_laplacian hφ).continuousAt.eventually_lt continuousAt_const
        (by rw [hη_def]; linarith)
    rcases hfb with hpos | hgrad
    · have h2 : ∀ᶠ y in 𝓝 x₀, φ x₀ / 2 < φ y :=
        continuousAt_const.eventually_lt hφ.continuous.continuousAt (by linarith)
      filter_upwards [h1, h2] with y hy1 hy2 using ⟨hy1, Or.inl ⟨hpos, hy2⟩⟩
    · have h2 : ∀ᶠ y in 𝓝 x₀, ‖∇ φ y‖ < Q y :=
        (continuous_gradient hφ).continuousAt.norm.eventually_lt
          (hQ.continuousAt (hU.mem_nhds hx₀U)) hgrad
      filter_upwards [h1, h2] with y hy1 hy2 using ⟨hy1, Or.inr hy2⟩
  obtain ⟨ε₁, hε₁, hG'⟩ := Metric.eventually_nhds_iff_ball.1 hG
  set ρ := min r (ε₁ / 2) with hρ_def
  have hρ : 0 < ρ := lt_min hr (half_pos hε₁)
  have hρr : ρ ≤ r := min_le_left _ _
  have hGρ : ∀ y ∈ closedBall x₀ ρ,
      Δ φ y < -η ∧ ((0 < φ x₀ ∧ φ x₀ / 2 < φ y) ∨ ‖∇ φ y‖ < Q y) := fun y hy =>
    hG' y (closedBall_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hε₁)) hy)
  have hρU : closedBall x₀ ρ ⊆ U := (closedBall_subset_closedBall hρr).trans hrU
  set c := δ * ρ ^ 2 with hc_def
  have hc : 0 < c := by positivity
  obtain ⟨c', hc', hc'c, hc'φ⟩ : ∃ c' > 0, c' ≤ c / 2 ∧ (0 < φ x₀ → c' ≤ φ x₀ / 2) := by
    by_cases h : 0 < φ x₀
    · exact ⟨min (c / 2) (φ x₀ / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
        fun _ => min_le_right _ _⟩
    · exact ⟨c / 2, by linarith, le_rfl, fun h' => absurd h' h⟩
  -- eventual estimates on the bottom and the lateral boundary
  have e1 := eventually_sub_lt_of_upperKLimit hU huInf hconv hφ.continuous
    (isCompact_closedBall x₀ ρ) hρU (κ := c') (Eset := Eset) (fun y hy hyE => by
      have := hstrict y (closedBall_subset_closedBall hρr hy) hyE
      have : 0 ≤ δ * ‖y - x₀‖ ^ 2 := by positivity
      linarith)
  have e2 := eventually_sub_lt_of_upperKLimit hU huInf hconv hφ.continuous
    (isCompact_sphere x₀ ρ) (sphere_subset_closedBall.trans hρU) (κ := -(c / 2)) (Eset := Eset)
    (fun y hy hyE => by
      have := hstrict y (closedBall_subset_closedBall hρr (sphere_subset_closedBall hy)) hyE
      rw [mem_sphere_iff_norm.1 hy] at this
      linarith)
  have e3 := eventually_abs_sub_lt hU hconv (isCompact_closedBall x₀ ρ) hρU
    (ε := c' / 4) (by linarith)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (((e1.and e2).and e3).and (eventually_gt_atTop 0))
  -- points of `E_b` near `x₀` at a large time `b`
  have hcx₀ : ContinuousAt (fun y ↦ uInf y - φ y) x₀ :=
    (huInf.continuousAt (hU.mem_nhds hx₀U)).sub hφ.continuous.continuousAt
  have hnear : ∀ᶠ y in 𝓝 x₀, -(c' / 4) < uInf y - φ y :=
    hcx₀.eventually (lt_mem_nhds (by simp only [hφx₀, sub_self]; linarith))
  obtain ⟨ε₂, hε₂, hnear'⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  set L := 2 * c' / η with hL_def
  have hL : 0 < L := by positivity
  have hηL : η * L = 2 * c' := by rw [hL_def]; field_simp
  obtain ⟨b, ⟨y₀, hy₀E, hy₀B⟩, hb⟩ :=
    ((hx₀E _ (ball_mem_nhds x₀ (lt_min hε₂ hρ))).and_eventually
      (eventually_ge_atTop (T₀ + L))).exists
  set a := b - L with ha_def
  have ha : T₀ ≤ a := by rw [ha_def]; linarith
  have ha0 : 0 < a := (hT₀ a ha).2
  have hab : a < b := by rw [ha_def]; linarith
  -- the barrier `ψ(y, t) = φ(y) + c' - η (t - a)`
  set ψ : E d × ℝ → ℝ := fun p ↦ φ p.1 + (c' + η * a) + (-η) * p.2 with hψ_def
  have hψ : ∀ p : E d × ℝ, ψ p = φ p.1 + c' - η * (p.2 - a) := fun p => by
    simp only [hψ_def]; ring
  have hψcont : Continuous ψ := (contDiff_affineTime hφ _ _).continuous
  have hadm : AdmissibleCyl U (Ioi 0) (ball x₀ ρ) a b := by
    refine ⟨isOpen_ball, isBounded_ball, hab, ?_⟩
    rw [closure_ball x₀ hρ.ne']
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    exact ⟨hρU hy, lt_of_lt_of_le ha0 ht.1⟩
  have hsuper : IsClassicalStrictParaSuper Q ψ (ball x₀ ρ) a b := by
    refine ⟨contDiff_affineTime hφ _ _, ?_, ?_⟩
    · rintro ⟨y, t⟩ ⟨-, hy, -⟩
      rw [closure_ball x₀ hρ.ne'] at hy
      rw [hψ_def, dₜ_affineTime, lapₓ_affineTime hφ]
      linarith [(hGρ y hy).1]
    · rintro ⟨y, t⟩ ⟨hfr, hy, ht⟩
      rw [closure_ball x₀ hρ.ne'] at hy
      rcases (hGρ y hy).2 with ⟨hpos, hφy⟩ | hgrad
      · exfalso
        have hψpos : 0 < ψ (y, t) := by
          rw [hψ]
          have : η * (t - a) ≤ η * L := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hη.le
          have := hc'φ hpos
          simp only at this ⊢
          linarith
        rw [(isOpen_lt continuous_const hψcont).frontier_eq] at hfr
        exact hfr.2 hψpos
      · rw [hψ_def, gradₓ_affineTime]; exact hgrad
  have hbdry : PrecOn u ψ Eset (parBdry (ball x₀ ρ) a b) := by
    rintro ⟨y, t⟩ ⟨hE, hB⟩
    rw [parBdry, closure_ball x₀ hρ.ne', frontier_ball x₀ hρ.ne'] at hB
    rcases hB with ⟨hy, ht⟩ | ⟨hy, ht⟩
    · have ht' : t = a := ht
      subst ht'
      have := (hT₀ a ha).1.1.1 y hy hE
      rw [hψ]; simp only [sub_self, mul_zero, sub_zero]; linarith
    · have := (hT₀ t (ha.trans ht.1)).1.1.2 y hy hE
      rw [hψ]
      have : η * (t - a) ≤ η * L := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hη.le
      simp only
      linarith
  have hy₀ρ : y₀ ∈ ball x₀ ρ := ball_subset_ball (min_le_right _ _) hy₀B
  have hcon := hcomp (ball x₀ ρ) a b ψ hadm hsuper hbdry (y₀, b) ⟨hy₀E, hy₀ρ, hab, le_rfl⟩
  rw [hψ] at hcon
  have h3 := (abs_lt.1 ((hT₀ b (ha.trans hab.le)).1.2 y₀ (ball_subset_closedBall hy₀ρ))).1
  have h4 := hnear' y₀ (ball_subset_ball (min_le_left _ _) hy₀B)
  have h5 : η * (b - a) = 2 * c' := by rw [ha_def, sub_sub_cancel]; exact hηL
  simp only at hcon h4
  linarith

/-- Core of **Lemma 5.6**: a strict touching from below of `u_∞` at `x₀` by a smooth `φ` which
is a strict stationary subsolution at `x₀` contradicts the parabolic supersolution property
(Definition 3.2). -/
theorem super_core (hU : IsOpen U) (hQ : ContinuousOn Q U) (hu : IsParaSuper U Q (Ioi 0) u)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀U : x₀ ∈ U) (hφx₀ : φ x₀ = uInf x₀)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hrU : closedBall x₀ r ⊆ U)
    (hstrict : ∀ y ∈ closedBall x₀ r, φ y + δ * ‖y - x₀‖ ^ 2 ≤ uInf y)
    (hΔ : 0 < Δ φ x₀) (hfb : 0 < φ x₀ ∨ Q x₀ < ‖∇ φ x₀‖) : False := by
  obtain ⟨-, hunn, hcomp⟩ := hu
  have hx₀nn : 0 ≤ uInf x₀ := limit_nonneg hunn hconv x₀ hx₀U
  set η := Δ φ x₀ / 2 with hη_def
  have hη : 0 < η := by rw [hη_def]; linarith
  have hG : ∀ᶠ y in 𝓝 x₀,
      η < Δ φ y ∧ ((0 < φ x₀ ∧ φ x₀ / 2 < φ y) ∨ Q y < ‖∇ φ y‖) := by
    have h1 : ∀ᶠ y in 𝓝 x₀, η < Δ φ y :=
      continuousAt_const.eventually_lt (continuous_laplacian hφ).continuousAt
        (by rw [hη_def]; linarith)
    rcases hfb with hpos | hgrad
    · have h2 : ∀ᶠ y in 𝓝 x₀, φ x₀ / 2 < φ y :=
        continuousAt_const.eventually_lt hφ.continuous.continuousAt (by linarith)
      filter_upwards [h1, h2] with y hy1 hy2 using ⟨hy1, Or.inl ⟨hpos, hy2⟩⟩
    · have h2 : ∀ᶠ y in 𝓝 x₀, Q y < ‖∇ φ y‖ :=
        (hQ.continuousAt (hU.mem_nhds hx₀U)).eventually_lt
          (continuous_gradient hφ).continuousAt.norm hgrad
      filter_upwards [h1, h2] with y hy1 hy2 using ⟨hy1, Or.inr hy2⟩
  obtain ⟨ε₁, hε₁, hG'⟩ := Metric.eventually_nhds_iff_ball.1 hG
  set ρ := min r (ε₁ / 2) with hρ_def
  have hρ : 0 < ρ := lt_min hr (half_pos hε₁)
  have hρr : ρ ≤ r := min_le_left _ _
  have hGρ : ∀ y ∈ closedBall x₀ ρ,
      η < Δ φ y ∧ ((0 < φ x₀ ∧ φ x₀ / 2 < φ y) ∨ Q y < ‖∇ φ y‖) := fun y hy =>
    hG' y (closedBall_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hε₁)) hy)
  have hρU : closedBall x₀ ρ ⊆ U := (closedBall_subset_closedBall hρr).trans hrU
  set c := δ * ρ ^ 2 with hc_def
  have hc : 0 < c := by positivity
  obtain ⟨c', hc', hc'c, hc'φ⟩ : ∃ c' > 0, c' ≤ c / 2 ∧ (0 < φ x₀ → c' ≤ φ x₀ / 2) := by
    by_cases h : 0 < φ x₀
    · exact ⟨min (c / 2) (φ x₀ / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
        fun _ => min_le_right _ _⟩
    · exact ⟨c / 2, by linarith, le_rfl, fun h' => absurd h' h⟩
  have e3 := eventually_abs_sub_lt hU hconv (isCompact_closedBall x₀ ρ) hρU
    (ε := c' / 2) (by linarith)
  obtain ⟨a, ha⟩ := eventually_atTop.1 (e3.and (eventually_gt_atTop 0))
  set L := 2 * c' / η with hL_def
  have hL : 0 < L := by positivity
  have hηL : η * L = 2 * c' := by rw [hL_def]; field_simp
  set b := a + L with hb_def
  have hab : a < b := by rw [hb_def]; linarith
  have ha0 : 0 < a := (ha a le_rfl).2
  -- the barrier `ψ(y, t) = φ(y) - c' + η (t - a)`
  set ψ : E d × ℝ → ℝ := fun p ↦ φ p.1 + (-c' - η * a) + η * p.2 with hψ_def
  have hψ : ∀ p : E d × ℝ, ψ p = φ p.1 - c' + η * (p.2 - a) := fun p => by
    simp only [hψ_def]; ring
  have hψcont : Continuous ψ := (contDiff_affineTime hφ _ _).continuous
  have hadm : AdmissibleCyl U (Ioi 0) (ball x₀ ρ) a b := by
    refine ⟨isOpen_ball, isBounded_ball, hab, ?_⟩
    rw [closure_ball x₀ hρ.ne']
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    exact ⟨hρU hy, lt_of_lt_of_le ha0 ht.1⟩
  have hsub : IsClassicalStrictParaSub Q ψ (ball x₀ ρ) a b := by
    refine ⟨contDiff_affineTime hφ _ _, ?_, ?_⟩
    · rintro ⟨y, t⟩ ⟨-, hy, -⟩
      rw [closure_ball x₀ hρ.ne'] at hy
      rw [hψ_def, dₜ_affineTime, lapₓ_affineTime hφ]
      linarith [(hGρ y hy).1]
    · rintro ⟨y, t⟩ ⟨hfr, hy, ht⟩
      rw [closure_ball x₀ hρ.ne'] at hy
      rcases (hGρ y hy).2 with ⟨hpos, hφy⟩ | hgrad
      · exfalso
        have hψpos : 0 < ψ (y, t) := by
          rw [hψ]
          have : 0 ≤ η * (t - a) := mul_nonneg hη.le (by linarith [ht.1])
          have := hc'φ hpos
          simp only at this ⊢
          linarith
        rw [(isOpen_lt continuous_const hψcont).frontier_eq] at hfr
        exact hfr.2 hψpos
      · rw [hψ_def, gradₓ_affineTime]; exact hgrad
  have hbdry : Prec ψ u univ (parBdry (ball x₀ ρ) a b) := by
    rintro ⟨y, t⟩ ⟨-, hB⟩
    rw [parBdry, closure_ball x₀ hρ.ne', frontier_ball x₀ hρ.ne'] at hB
    rcases hB with ⟨hy, ht⟩ | ⟨hy, ht⟩
    · have ht' : t = a := ht
      subst ht'
      have h1 := (abs_lt.1 ((ha t le_rfl).1 y hy)).1
      have h2 := hstrict y (closedBall_subset_closedBall hρr hy)
      have h3 : 0 ≤ δ * ‖y - x₀‖ ^ 2 := by positivity
      rw [hψ]; simp only [sub_self, mul_zero, add_zero]; linarith
    · have h1 := (abs_lt.1 ((ha t ht.1).1 y (sphere_subset_closedBall hy))).1
      have h2 := hstrict y (closedBall_subset_closedBall hρr (sphere_subset_closedBall hy))
      rw [mem_sphere_iff_norm.1 hy] at h2
      rw [hψ]
      have : η * (t - a) ≤ η * L := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hη.le
      simp only
      linarith
  have hmem : (x₀, b) ∈ closure (posSetP ψ univ) ∩ cyl (ball x₀ ρ) a b := by
    refine ⟨subset_closure ⟨mem_univ _, ?_⟩, mem_ball_self hρ, hab, le_rfl⟩
    rw [hψ]
    have : 0 ≤ η * (b - a) := mul_nonneg hη.le (by linarith)
    simp only
    linarith
  have hcon := hcomp (ball x₀ ρ) a b ψ hadm hsub hbdry (x₀, b) hmem
  rw [hψ] at hcon
  have h3 := (abs_lt.1 ((ha b hab.le).1 x₀ (mem_closedBall_self hρ.le))).2
  have h5 : η * (b - a) = 2 * c' := by rw [hb_def, add_sub_cancel_left]; exact hηL
  simp only at hcon
  linarith

/-! ### Relaxed subsolutions contained in the closure of the positivity set -/

/-- A relaxed subsolution `(v, F)` with `F ⊆ \overline{{v > 0}}` is a viscosity subsolution (the
remark after Definition 2.3). The test in Definition 2.1(ii) is by `φ₊`; by density of `{v > 0}` in
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
Definition 3.4). -/
theorem isParaRelaxedSub_of_isParaSub {I : Set ℝ} (hu : IsParaSub U Q I u) :
    IsParaRelaxedSub U Q I u (closure (posSetP u (U ×ˢ I))) := by
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨h1, h2, isClosed_closure, ?_, subset_closure, h3⟩
  rw [← closure_prod_eq]
  exact closure_mono fun p hp => hp.1

/-- For a time-increasing `u`, the upper Kuratowski limit of the slices of `\overline{{u > 0}}`
lies in `\overline{{u_∞ > 0}}` (proof of Corollary 5.7). -/
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

/-- **Lemma 5.6**. If `u` is a parabolic viscosity
supersolution in `U × (0, ∞)` and `u(·, t) → u_∞` locally uniformly in `U` as `t → ∞`, then `u_∞`
is a viscosity supersolution of (1.1) in `U`. (The paper's boundedness assumption is not needed;
`Q` is assumed continuous on `U`, as in the standing assumptions.) -/
theorem longtime_super (hU : IsOpen U) (hQ : ContinuousOn Q U) (hu : IsParaSuper U Q (Ioi 0) u)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    IsViscSuper U Q uInf := by
  refine ⟨continuousOn_limit hu.1 hconv, limit_nonneg hu.2.1 hconv, ?_⟩
  intro φ hφ x₀ hx₀U htouch
  obtain ⟨-, hφx₀, hle⟩ := htouch
  rw [hU.nhdsWithin_eq hx₀U] at hle
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.eventually_nhds_iff_ball.1 (hle.and (hU.mem_nhds hx₀U))
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
  -- strict perturbation `φ - δ |y - x₀|²`
  set w : E d → ℝ := fun y ↦ ‖y - x₀‖ ^ 2 with hw_def
  have hw : ContDiff ℝ ∞ w := contDiff_sqDist x₀
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
  refine super_core hU hQ hu hconv hφδ hx₀U (by simp [hw_def, hφx₀]) hδ hr
    (hsub.trans fun y hy => (hr₁' y hy).2) (fun y hy => ?_) ?_ ?_
  · have := (hr₁' y (hsub hy)).1
    simp only [hw_def]
    linarith
  · rwa [laplacian_add_mul hφ hw]
  · rw [gradient_add_mul (hφ.differentiable (by simp)) (hw.differentiable (by simp))]
    simpa [hw_def] using hfbδ

/-- **Lemma 5.5**, with `E_∞ := limsup*_{t → ∞} E_t`. If
`(u, E)` is a parabolic relaxed subsolution in `U × (0, ∞)` and `u(·, t) → u_∞` locally uniformly
in `U`, then `(u_∞, limsup*_{t → ∞} E_t)` is a relaxed subsolution of (1.1) in `U`. The paper's
`E_∞ = limsup*_{T → ∞} ⋂_{t ≥ T} E_t` is smaller (so the paper's conclusion is stronger); see the
module docstring and `longtime_relaxedSub_of_slicesMonotone`. (Boundedness of `u` is not
needed.) -/
theorem longtime_relaxedSub (hU : IsOpen U) (hQ : ContinuousOn Q U) {Eset : Set (E d × ℝ)}
    (hu : IsParaRelaxedSub U Q (Ioi 0) u Eset)
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    IsRelaxedSub U Q uInf (upperKLimit (timeSlice Eset) atTop) := by
  have hu' := hu
  obtain ⟨hucont, hunn, -, hEsub, hEpos, -⟩ := hu'
  refine ⟨continuousOn_limit hucont hconv, limit_nonneg hunn hconv, isClosed_upperKLimit _ _,
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
    set w : E d → ℝ := fun y ↦ ‖y - x₀‖ ^ 2 with hw_def
    have hw : ContDiff ℝ ∞ w := contDiff_sqDist x₀
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
    refine relaxedSub_core hU hQ hu hconv hφδ hx₀U hx₀E (by simp [hw_def, hφx₀]) hδ hr hrU
      (fun y hy hyE => ?_) ?_ ?_
    · have hyU : y ∈ U := hrU hy
      have := h1 ⟨(hsub.trans (ball_subset_ball (min_le_left _ _))) hy, hyE, hyU⟩
      simp only [hw_def, mem_setOf_eq] at this ⊢
      linarith
    · rwa [laplacian_add_mul hφ hw]
    · rw [gradient_add_mul (hφ.differentiable (by simp)) (hw.differentiable (by simp))]
      simpa [hw_def] using hfbδ

/-- **Lemma 5.5** in the paper's form, `E_∞ = limsup*_{T → ∞} ⋂_{t ≥ T} E_t`, under the extra
hypothesis that the slices `E_t` are monotone in `t` (then the two candidate sets coincide). -/
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

/-- **Corollary 5.7**. If `u` is a parabolic viscosity subsolution in
`U × (0, ∞)`, monotonically increasing in time, with `u(·, t) → u_∞` locally uniformly in `U`,
then `u_∞` is a viscosity subsolution of (1.1) in `U`. (Boundedness is not needed.) -/
theorem longtime_sub_increasing (hU : IsOpen U) (hQ : ContinuousOn Q U)
    (hu : IsParaSub U Q (Ioi 0) u) (hmono : MonotoneInTime u U (Ioi 0))
    (hconv : TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop U) :
    IsViscSub U Q uInf :=
  isViscSub_of_isRelaxedSub hU (longtime_relaxedSub hU hQ (isParaRelaxedSub_of_isParaSub hu) hconv)
    (upperKLimit_subset_closure_posSet hmono hconv)

/-- **Theorem 3.12(i)**: a bounded, time-increasing parabolic viscosity solution converges
(locally uniformly) to a stationary viscosity solution. -/
theorem longtime_viscosity_increasing : LongtimeViscIncreasingStatement := by
  intro d S u uInf hu _ hmono hconv
  have hQ : ContinuousOn S.Q S.U := by
    obtain ⟨K, hK⟩ := S.lip
    exact hK.continuousOn.mono subset_closure
  exact ⟨longtime_super S.isOpen hQ hu.1 hconv,
    longtime_sub_increasing S.isOpen hQ hu.2 hmono hconv⟩

end PerronVariational

end
