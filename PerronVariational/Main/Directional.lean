/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import PerronVariational.Registry.FunctionalAnalysis
import PerronVariational.Registry.Obstacle
import PerronVariational.Regularity.ObstacleBoundary
import PerronVariational.Stationary.ViscosityLocal
import PerronVariational.Stationary.ViscosityStability

/-!
# Lemma 6.3: extremal solutions are directional minimizers

**Lemma 6.3** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, in the form
`DirectionalStatement`.

The paper states Lemma 6.3 for local extremal solutions (Definition 2.6), but its proof uses that
`u` is harmonic in `{u > 0}`, citing Propositions 6.1/6.2, which apply only to Perron solutions;
it also needs `u ∈ H¹`. Here we assume in addition that `u` is locally Lipschitz, `C²` and harmonic
in `{u > 0}`. Theorem 1.1(iii) supplies these hypotheses from Theorem 1.1(ii) and Definition 2.8.

* `downwardMinimizer_of_localSmallest`: a local smallest supersolution (Definition 2.6(i))
  which is locally Lipschitz and harmonic in its positivity set is a downward minimizer
  (Definition 2.11).
* `upwardMinimizer_of_localLargest`: the dual statement for local largest subsolutions.
* `directional : DirectionalStatement`.

Ingredients: the one-sided obstacle problems (`Registry.obstacle_below_exists`,
`Registry.obstacle_above_exists`), the energy-decreasing perturbations of W. M. Feldman, I. C. Kim,
N. Požár, *On the geometry of rate independent droplet evolution*, arXiv:2310.03656
(`Registry.energy_decrease_of_not_super`, `Registry.energy_decrease_of_not_sub`), the weak gradient
of a Lipschitz function (`Registry.memH1Loc_gradient_of_locallyLipschitzOn`), the quartic
strict-touching perturbation `jet_add_quartic`, and two elementary Sobolev facts proved here:
uniqueness of weak gradients (`HasWeakGradient.ae_eq_of_eqOn`) and the energy splitting of
`energyJ`.

Two facts not covered by the paper's citations are proved in `Regularity/`:
* continuity on `U` of the obstacle minimizers extended by `u` (the paper cites interior
  regularity only), `obstacle_below_continuousOn`, `obstacle_above_continuousOn`, by a De Giorgi
  argument (`Regularity.obstacle_below_continuousOn`,
  `Regularity.obstacle_above_continuousOn`);
* `v₊ ∈ H¹_loc` with weak gradient `1_{v>0} ∇v` (standard lattice property of Sobolev functions,
  used implicitly by the paper to reduce downward competitors `v ≤ u` to nonnegative ones,
  `0 ≤ v₊ ≤ u`), `memH1Loc_posPart` (`GMTFoundations.memH1Loc_posPart`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Elementary Sobolev facts -/

section Sobolev

theorem locallyIntegrableOn_inner_const {U : Set (E d)} {G : E d → E d}
    (hG : LocallyIntegrableOn G U) (v : E d) :
    LocallyIntegrableOn (fun x ↦ inner ℝ (G x) v) U := by
  intro x hx
  obtain ⟨t, ht, hi⟩ := hG x hx
  refine ⟨t, ht, ?_⟩
  have := (innerSL ℝ v).integrable_comp hi
  refine this.congr (ae_of_all _ fun y ↦ ?_)
  simp [real_inner_comm]

/-- A function locally integrable on an open `U`, multiplied by a continuous function with compact
support in `U`, is integrable on `U`. -/
theorem integrableOn_mul_of_tsupport_subset {U : Set (E d)} (hU : IsOpen U) {F φ : E d → ℝ}
    (hF : LocallyIntegrableOn F U) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) : IntegrableOn (fun x ↦ F x * φ x) U := by
  have hK : IsCompact (tsupport φ) := hφc
  have h1 : IntegrableOn F (tsupport φ) := hF.integrableOn_compact_subset hφU hK
  exact (h1.mul_continuousOn hφ.continuousOn hK).of_forall_sdiff_eq_zero hU.measurableSet
    fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx.2]

theorem eq_zero_of_forall_inner_single {z : E d}
    (h : ∀ i : Fin d, inner ℝ z (EuclideanSpace.single i (1 : ℝ)) = 0) : z = 0 := by
  ext i
  simpa [EuclideanSpace.inner_single_right] using h i

/-- **Uniqueness of weak gradients.** If `G₁` is a weak gradient of `f` and `G₂` one of `g` in the
open set `U`, and `f = g` on an open `W ⊆ U`, then `G₁ = G₂` a.e. on `W`. -/
theorem HasWeakGradient.ae_eq_of_eqOn {U W : Set (E d)} (hU : IsOpen U) (hW : IsOpen W)
    (hWU : W ⊆ U) {f g : E d → ℝ} {G₁ G₂ : E d → E d} (hf : HasWeakGradient U f G₁)
    (hg : HasWeakGradient U g G₂) (hfg : EqOn f g W) :
    ∀ᵐ x ∂(volume.restrict W), G₁ x = G₂ x := by
  have key : ∀ v : E d, ∀ᵐ x ∂(volume : Measure (E d)),
      x ∈ W → inner ℝ (G₁ x) v - inner ℝ (G₂ x) v = 0 := by
    intro v
    have hl1 := locallyIntegrableOn_inner_const hf.2.1 v
    have hl2 := locallyIntegrableOn_inner_const hg.2.1 v
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hl1.sub hl2).mono_set hWU) fun φ hφ hφc hφW ↦ ?_
    have hφU := hφW.trans hWU
    have h1 := hf.2.2 φ hφ hφc hφU v
    have h2 := hg.2.2 φ hφ hφc hφU v
    have hlhs : ∫ x in U, f x * fderiv ℝ φ x v = ∫ x in U, g x * fderiv ℝ φ x v := by
      refine setIntegral_congr_fun hU.measurableSet fun x _ ↦ ?_
      by_cases hxW : x ∈ W
      · simp [hfg hxW]
      · have hx : x ∉ tsupport φ := fun h ↦ hxW (hφW h)
        have : fderiv ℝ φ x = 0 :=
          Function.notMem_support.1 fun h ↦ hx (support_fderiv_subset ℝ h)
        simp [this]
    have hφc' : Continuous φ := hφ.continuous
    have i1 := integrableOn_mul_of_tsupport_subset hU hl1 hφc' hφc hφU
    have i2 := integrableOn_mul_of_tsupport_subset hU hl2 hφc' hφc hφU
    have hzero : ∀ x, x ∉ U → φ x • (inner ℝ (G₁ x) v - inner ℝ (G₂ x) v) = 0 := by
      intro x hx
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφU h)]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have : ∫ x in U, φ x • (inner ℝ (G₁ x) v - inner ℝ (G₂ x) v) =
        (∫ x in U, inner ℝ (G₁ x) v * φ x) - ∫ x in U, inner ℝ (G₂ x) v * φ x := by
      rw [← integral_sub i1 i2]
      congr 1; funext x; simp only [smul_eq_mul]; ring
    rw [this]
    linarith
  have hall : ∀ᵐ x ∂(volume : Measure (E d)), ∀ i : Fin d,
      x ∈ W → inner ℝ (G₁ x) (EuclideanSpace.single i (1 : ℝ)) -
        inner ℝ (G₂ x) (EuclideanSpace.single i (1 : ℝ)) = 0 :=
    ae_all_iff.2 fun i ↦ key _
  rw [ae_restrict_iff' hW.measurableSet]
  filter_upwards [hall] with x hx hxW
  have := eq_zero_of_forall_inner_single (z := G₁ x - G₂ x) fun i ↦ by
    rw [inner_sub_left]; exact hx i hxW
  exact sub_eq_zero.1 this

/-- `energyJ` only depends on the function on `V` and on the gradient a.e. on `V`. -/
theorem energyJ_congr {V : Set (E d)} {Q f₁ f₂ : E d → ℝ}
    {G₁ G₂ : E d → E d} (hf : EqOn f₁ f₂ V) (hG : ∀ᵐ x ∂(volume.restrict V), G₁ x = G₂ x) :
    energyJ V Q f₁ G₁ = energyJ V Q f₂ G₂ := by
  have hpos : posSet f₁ V = posSet f₂ V := by
    ext y; simp only [posSet, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨h.1, hf h.1 ▸ h.2⟩, fun h ↦ ⟨h.1, (hf h.1).symm ▸ h.2⟩⟩
  unfold energyJ
  rw [hpos]
  refine lintegral_congr_ae ?_
  filter_upwards [hG] with x hx
  rw [hx]

/-- Positive part: `J_Q(v₊; V) ≤ J_Q(v; V)` with `∇v₊ = 1_{v > 0} ∇v`. -/
theorem energyJ_posPart_le (V : Set (E d)) (Q v : E d → ℝ) (G : E d → E d) :
    energyJ V Q (fun y ↦ max (v y) 0) ({y | 0 < v y}.indicator G) ≤ energyJ V Q v G := by
  have hpos : posSet (fun y ↦ max (v y) 0) V = posSet v V := by
    ext y; simp [posSet]
  unfold energyJ
  rw [hpos]
  refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_
  gcongr
  by_cases hx : 0 < v x
  · simp [hx]
  · simp [hx]

/-- Splitting `energyJ` over `B ⊆ B'`. -/
theorem energyJ_split {B B' : Set (E d)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hBB' : B ⊆ B')
    (Q f : E d → ℝ) (G : E d → E d) :
    energyJ B' Q f G = energyJ B Q f G + energyJ (B' \ B) Q f G := by
  unfold energyJ
  rw [← MeasureTheory.lintegral_inter_add_sdiff _ B' hB, inter_eq_right.2 hBB']
  congr 1
  · refine setLIntegral_congr_fun hB fun x hx ↦ ?_
    have : x ∈ posSet f B' ↔ x ∈ posSet f B := by
      simp only [posSet, Set.mem_ofPred_eq]; exact ⟨fun h ↦ ⟨hx, h.2⟩, fun h ↦ ⟨hBB' hx, h.2⟩⟩
    have hind : (posSet f B').indicator (1 : E d → ℝ) x = (posSet f B).indicator 1 x := by
      by_cases h : x ∈ posSet f B
      · rw [indicator_of_mem h, indicator_of_mem (this.2 h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (mt this.1 h)]
    rw [hind]
  · refine setLIntegral_congr_fun (hB'.diff hB) fun x hx ↦ ?_
    have : x ∈ posSet f B' ↔ x ∈ posSet f (B' \ B) := by
      simp only [posSet, Set.mem_ofPred_eq]; exact ⟨fun h ↦ ⟨hx, h.2⟩, fun h ↦ ⟨hx.1, h.2⟩⟩
    have hind : (posSet f B').indicator (1 : E d → ℝ) x = (posSet f (B' \ B)).indicator 1 x := by
      by_cases h : x ∈ posSet f (B' \ B)
      · rw [indicator_of_mem h, indicator_of_mem (this.2 h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (mt this.1 h)]
    rw [hind]

/-- **`v₊ ∈ H¹_loc`.** If `v ∈ H¹_loc(U)` with weak gradient `G`,
then `v₊ = max(v, 0) ∈ H¹_loc(U)` with weak gradient `1_{v > 0} G`.

Standard lattice property of Sobolev functions (D. Gilbarg, N. S. Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Springer, 2001, doi:10.1007/978-3-642-61798-0,
Lemma 7.6). The paper uses it implicitly in Lemma 6.3, Step 1: Definition 2.11 allows downward
competitors `v ≤ u` of any sign, while the obstacle problem (6.1) only admits `0 ≤ v ≤ u`; the
reduction is `J_Q(v₊; B) ≤ J_Q(v; B)` (`energyJ_posPart_le`). Proved in
`GMTFoundations.memH1Loc_posPart` (gmt-foundations v0.1.0). -/
theorem memH1Loc_posPart {U : Set (E d)} {v : E d → ℝ} {G : E d → E d} (hU : IsOpen U)
    (hv : MemH1Loc U v G) :
    MemH1Loc U (fun y ↦ max (v y) 0) ({y | 0 < v y}.indicator G) :=
  GMTFoundations.memH1Loc_posPart hU hv

end Sobolev

/-! ### Continuity of the obstacle minimizers across `∂B` -/

section BoundaryContinuity

/-- **Continuity across `∂B` of the obstacle-from-above minimizer.** Let `w` be a minimizer of
`J_Q(·; B)` over `{v ∈ u + H¹₀(B) : 0 ≤ v ≤ u}` (the output of `Registry.obstacle_below_exists`,
`B = B_r(x₀)`, `B̄ ⊆ U`), continuous in `B` and equal to `u` on `U \ B`. Then `w` is continuous on
`U`.

Paper: Lemma 6.3, Step 1 uses that `w` (extended by `u`) is a viscosity supersolution in `U`, and
Definition 2.1 requires `w ∈ C(U)`; the regularity the paper cites (W. M. Feldman, I. C. Kim, N.
Požár, *An obstacle approach to rate-independent droplet evolution*, Forum Math. Sigma 14 (2026),
e38, doi:10.1017/fms.2026.10189, §3) gives at most continuity in `B`, and does not treat this
obstacle problem. Here we prove continuity up to `∂B`. Since `0 ≤ w ≤ u` and `w = u` on `∂B`,
continuity at a point `z ∈ ∂B` is automatic when `u(z) = 0` and upper semicontinuity always holds;
the missing statement is the lower bound `liminf_{y → z, y ∈ B} w(y) ≥ u(z)` at points `z ∈ ∂B` with
`u(z) > 0`, a boundary-regularity (barrier / energy) property of the obstacle minimizer with
Lipschitz boundary data.

Why it cannot be localized away: the argument concludes via Definition 2.6(i)
(`IsLocalSmallestSuper`), which only accepts competitors that are viscosity supersolutions — in
particular continuous — on all of `U`; testing only at interior points of `B` does not help, because
the extended `w` must itself be an admissible competitor, and `w ≠ u` near `∂B` in general. -/
theorem obstacle_below_continuousOn {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U)
    (hGw : MemH1Loc U w Gw) (hwc : ContinuousOn w (ball x₀ r))
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv) :
    ContinuousOn w U :=
  Regularity.obstacle_below_continuousOn hU hQ hQpos hQb hu hu0 hr hB hGw hwc hwout hwu hmin

/-- **Continuity across `∂B` of the obstacle-from-below minimizer.** Let `w` be a minimizer of
`J_Q(·; B)` over `{v ∈ u + H¹₀(B) : v ≥ u}` (the output of `Registry.obstacle_above_exists`),
continuous in `B` and equal to `u` on `U \ B`. Then `w` is continuous on `U`.

Paper: Lemma 6.3, Step 2 ("exists and is continuous as before"). Here lower
semicontinuity at `∂B` is automatic (`w ≥ u`, `w = u` on `∂B`); the missing statement is the
upper bound `limsup_{y → z, y ∈ B} w(y) ≤ u(z)` for `z ∈ ∂B`. -/
theorem obstacle_above_continuousOn {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U)
    (hGw : MemH1Loc U w Gw) (hwc : ContinuousOn w (ball x₀ r))
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, u y ≤ w y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv) :
    ContinuousOn w U :=
  Regularity.obstacle_above_continuousOn hU hQ hQpos hQb hu hu0 hr hB hGw hwc hwout hwu hmin

end BoundaryContinuity

/-! ### Lemma 6.3 -/

section Directional

variable {U : Set (E d)} {Q u : E d → ℝ}

theorem compactlyContained_ball {x : E d} {r : ℝ} (hB : closedBall x r ⊆ U) :
    CompactlyContained (ball x r) U :=
  ⟨(isCompact_closedBall x r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
    closure_ball_subset_closedBall.trans hB⟩

/-- The positivity set of a function continuous on an open set is open. -/
theorem isOpen_posSet {f : E d → ℝ} (hU : IsOpen U) (hf : ContinuousOn f U) :
    IsOpen (posSet f U) :=
  hf.isOpen_inter_preimage hU isOpen_Ioi

/-- **Lemma 6.3, Step 1**, with the added regularity hypotheses (see the module docstring). A local
smallest supersolution (Definition 2.6(i)) `u` in the open set `U`, locally Lipschitz, `C²` and
harmonic in `{u > 0}`, is a downward minimizer of `J_Q` (Definition 2.11, as encoded in
`IsDownwardMinimizer`).

Proof: for a ball `B ⊂⊂ U` let `w` minimize `J_Q(·; B)` with `u` as upper obstacle. Then
`w` is a viscosity supersolution in `U`: at a touching point with `w = u` use that `u` is one;
otherwise `w < u` near the point, which lies in `B`, and a violation would give an admissible
competitor of smaller energy (the energy-decreasing perturbation, after making the touching strict
with a quartic). Since `u`
is a local smallest supersolution, `w ≥ u`, so `w = u`; a competitor `v ≤ u` is reduced to
`v₊`, which is admissible for the obstacle problem. -/
theorem downwardMinimizer_of_localSmallest (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : LocallyLipschitzOn U u) (hc2 : ContDiffOn ℝ 2 u (posSet u U))
    (hharm : ∀ x ∈ posSet u U, Δ u x = 0) (hls : IsLocalSmallestSuper U Q u) :
    IsDownwardMinimizer U Q u := by
  have hu0 : ∀ x ∈ U, 0 ≤ u x := hls.1.2.1
  have hucont : ContinuousOn u U := hls.1.1
  refine ⟨⟨_, Registry.memH1Loc_gradient_of_locallyLipschitzOn hU hu⟩, isOpen_posSet hU hucont,
    hc2, hharm, ?_⟩
  intro x r hr hB Gu v Gv hGu hGv hvu hvout
  have hbU : ball x r ⊆ U := ball_subset_closedBall.trans hB
  obtain ⟨w, Gw, hGw, hwc, hwout, hwu, hmin⟩ :=
    Registry.obstacle_below_exists hU hQ hQpos hQb hu hu0 hGu hr hB
  have hwcU : ContinuousOn w U :=
    obstacle_below_continuousOn hU hQ hQpos hQb hu hu0 hr hB hGw hwc hwout hwu hmin
  -- `w` is a viscosity supersolution in `U`
  have hwsuper : IsViscSuper U Q w := by
    refine ⟨hwcU, fun y hy ↦ (hwu y hy).1, fun φ hφ x₀ hx₀ htouch ↦ ?_⟩
    by_cases heq : w x₀ = u x₀
    · refine hls.1.2.2 φ hφ x₀ hx₀ ⟨hx₀, htouch.2.1.trans heq, ?_⟩
      filter_upwards [htouch.2.2, self_mem_nhdsWithin] with y hy hyU
      exact hy.trans (hwu y hyU).2
    have hlt : w x₀ < u x₀ := lt_of_le_of_ne (hwu x₀ hx₀).2 heq
    have hx₀B : x₀ ∈ ball x r := by
      by_contra h; exact heq (hwout x₀ ⟨hx₀, h⟩)
    by_contra hfail
    simp only [not_or, not_le, not_and] at hfail
    obtain ⟨hψ, hψx, hψg, hψl⟩ := jet_add_quartic hφ x₀ (-1)
    set ψ : E d → ℝ := fun y ↦ φ y + (-1) * (‖y - x₀‖ ^ 2) ^ 2 with hψ_def
    have hle : ∀ᶠ y in 𝓝 x₀, φ y ≤ w y := htouch.eventually_le_of_isOpen hU
    have hstrict : ψ x₀ = w x₀ ∧ ∀ᶠ y in 𝓝[≠] x₀, ψ y < w y := by
      refine ⟨hψx.trans htouch.2.1, ?_⟩
      filter_upwards [nhdsWithin_le_nhds hle, self_mem_nhdsWithin] with y hy hne
      have : 0 < (‖y - x₀‖ ^ 2) ^ 2 := by
        have : y - x₀ ≠ 0 := sub_ne_zero.2 hne
        positivity
      simp only [hψ_def]; linarith
    have hfail' : 0 < Δ ψ x₀ ∧ (ψ x₀ = 0 → Q x₀ < ‖∇ ψ x₀‖) := by
      rw [hψl, hψg, hψx]
      exact hfail
    set η := (u x₀ - w x₀) / 2 with hη_def
    have hη : 0 < η := by rw [hη_def]; linarith
    have hev : ∀ᶠ y in 𝓝 x₀, ψ y - u y < -η := by
      have hc : ContinuousAt (fun y ↦ ψ y - u y) x₀ :=
        hψ.continuous.continuousAt.sub (hucont.continuousAt (hU.mem_nhds hx₀))
      refine hc.eventually (gt_mem_nhds ?_)
      simp only [hstrict.1]; rw [hη_def]; linarith
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff_ball.1
      (hev.and (isOpen_ball.mem_nhds hx₀B))
    have hρB : ball x₀ ρ ⊆ ball x r := fun y hy ↦ (hρ' y hy).2
    obtain ⟨w', Gw', hGw', hw'out, hw'bd, hlt'⟩ := Registry.energy_decrease_of_not_super hU hQ
      hQpos hQb hwcU (fun y hy ↦ (hwu y hy).1) hGw isOpen_ball (compactlyContained_ball hB) hψ
      hx₀B hstrict hfail' ρ hρ hρB η hη
    have hmeas : MeasurableSet (U \ ball x r) := hU.measurableSet.diff measurableSet_ball
    have key := hmin w' Gw' hGw'
      ((ae_restrict_iff' hmeas).2 (Eventually.of_forall fun y hy ↦ by
        rw [hw'out y ⟨hy.1, fun h ↦ hy.2 (hρB h)⟩, hwout y hy]))
      ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun y hy ↦ by
        refine ⟨(hwu y hy).1.trans (hw'bd y hy).1, ?_⟩
        by_cases hyρ : y ∈ ball x₀ ρ
        · refine (hw'bd y hy).2.trans (max_le (hwu y hy).2 ?_)
          have := (hρ' y hyρ).1; linarith
        · rw [hw'out y ⟨hy, hyρ⟩]; exact (hwu y hy).2))
    exact absurd (key.trans_lt hlt') (lt_irrefl _)
  -- hence `w = u`
  have hwu_eq : ∀ y ∈ U, w y = u y := fun y hy ↦
    le_antisymm (hwu y hy).2 (hls.2 x r hr hB w hwsuper hwout y hy)
  -- the energy comparison
  have hJu : energyJ (ball x r) Q u Gu = energyJ (ball x r) Q w Gw :=
    energyJ_congr (fun y hy ↦ (hwu_eq y (hbU hy)).symm)
      (HasWeakGradient.ae_eq_of_eqOn hU isOpen_ball hbU hGu.1 hGw.1
        fun y hy ↦ (hwu_eq y (hbU hy)).symm)
  have hmeas : MeasurableSet (U \ ball x r) := hU.measurableSet.diff measurableSet_ball
  rw [hJu]
  refine le_trans (hmin _ _ (memH1Loc_posPart hU hGv) ?_ ?_) (energyJ_posPart_le _ _ _ _)
  · filter_upwards [hvout, ae_restrict_mem hmeas] with y hy hyU
    rw [hy]; exact max_eq_left (hu0 y hyU.1)
  · filter_upwards [hvu, ae_restrict_mem hU.measurableSet] with y hy hyU
    exact ⟨le_max_right _ _, max_le hy (hu0 y hyU)⟩

/-- **Lemma 6.3, Step 2**, with the added regularity hypotheses (see the module docstring). A local
largest subsolution (Definition 2.6(ii)) `u` in the open set `U`, locally Lipschitz, `C²` and
harmonic in `{u > 0}`, is an upward minimizer of `J_Q` (Definition 2.11, as encoded in
`IsUpwardMinimizer`).

Proof: for a ball `B ⊂⊂ U` let `w` minimize `J_Q(·; B)` with `u` as lower obstacle. Then `w` is a
viscosity subsolution in `U`: at a touching point `x₀ ∈ \overline{{u > 0}}` with `w(x₀) = u(x₀)` use
that `u` is one; otherwise (i) `w(x₀) > u(x₀)` or (ii) `u ≡ 0` near `x₀`, and in both cases
`x₀ ∈ B̄`. A violation gives, by the energy-decreasing perturbation applied in a slightly larger
ball `B' = B_{r'}(x) ⊂⊂ U`, a competitor `w'` with `u ≤ w' ≤ w`, `w' = w` off a small ball around
`x₀` and `J_Q(w'; B') < J_Q(w; B')`; since `w' = w = u` on `B' \ B`, this contradicts minimality of
`w` on `B` (this handles the paper's case `x₀ ∈ ∂B`). Since `u` is a local largest subsolution,
`w ≤ u`, so `w = u`. The strict touching needed by the perturbation comes from the quartic
perturbation `φ + |y - x₀|⁴` and the observation that `φ ≥ 0` on `\overline{{w > 0}}` near `x₀`. -/
theorem upwardMinimizer_of_localLargest (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : LocallyLipschitzOn U u) (hc2 : ContDiffOn ℝ 2 u (posSet u U))
    (hharm : ∀ x ∈ posSet u U, Δ u x = 0) (hll : IsLocalLargestSub U Q u) :
    IsUpwardMinimizer U Q u := by
  have hu0 : ∀ x ∈ U, 0 ≤ u x := hll.1.2.1
  have hucont : ContinuousOn u U := hll.1.1
  refine ⟨⟨_, Registry.memH1Loc_gradient_of_locallyLipschitzOn hU hu⟩, isOpen_posSet hU hucont,
    hc2, hharm, ?_⟩
  intro x r hr hB Gu v Gv hGu hGv huv hvout
  have hbU : ball x r ⊆ U := ball_subset_closedBall.trans hB
  obtain ⟨w, Gw, hGw, hwc, hwout, huw, hmin⟩ :=
    Registry.obstacle_above_exists hU hQ hQpos hQb hu hu0 hGu hr hB
  have hwcU : ContinuousOn w U :=
    obstacle_above_continuousOn hU hQ hQpos hQb hu hu0 hr hB hGw hwc hwout huw hmin
  have hw0 : ∀ y ∈ U, 0 ≤ w y := fun y hy ↦ (hu0 y hy).trans (huw y hy)
  -- a larger ball `B' = B_{r'}(x) ⊂⊂ U`
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open hU hB
  rw [cthickening_closedBall hδ.le hr.le] at hδU
  have hrr' : r < δ + r := by linarith
  have hB'U : CompactlyContained (ball x (δ + r)) U := compactlyContained_ball hδU
  have hB'U' : ball x (δ + r) ⊆ U := ball_subset_closedBall.trans hδU
  have hmeas : MeasurableSet (U \ ball x r) := hU.measurableSet.diff measurableSet_ball
  -- `w` is a viscosity subsolution in `U`
  have hwsub : IsViscSub U Q w := by
    refine ⟨hwcU, hw0, fun φ hφ x₀ htouch ↦ ?_⟩
    have hx₀U : x₀ ∈ U := htouch.1.2
    have hx₀cl : x₀ ∈ closure (posSet w U) := htouch.1.1
    have hposuw : posSet u U ⊆ posSet w U := fun y hy ↦ ⟨hy.1, hy.2.trans_le (huw y hy.1)⟩
    by_cases hA : x₀ ∈ closure (posSet u U) ∧ w x₀ = u x₀
    · refine hll.1.2.2 φ hφ x₀ ⟨⟨hA.1, hx₀U⟩, htouch.2.1.trans hA.2, ?_⟩
      have hsub : closure (posSet u U) ∩ U ⊆ closure (posSet w U) ∩ U :=
        inter_subset_inter_left _ (closure_mono hposuw)
      filter_upwards [nhdsWithin_mono _ hsub htouch.2.2, self_mem_nhdsWithin] with y hy hyS
      exact (huw y hyS.2).trans hy
    by_contra hfail
    simp only [not_or, not_le, not_and] at hfail
    obtain ⟨hψ, hψx, hψg, hψl⟩ := jet_add_quartic hφ x₀ 1
    set ψ : E d → ℝ := fun y ↦ φ y + 1 * (‖y - x₀‖ ^ 2) ^ 2 with hψ_def
    -- an open neighbourhood `N ⊆ U` of `x₀` on which the touching holds
    obtain ⟨N₀, hN₀o, hx₀N₀, hN₀⟩ := mem_nhdsWithin.1 htouch.2.2
    have hNo : IsOpen (N₀ ∩ U) := hN₀o.inter hU
    have hN : ∀ y ∈ N₀ ∩ U, y ∈ closure (posSet w U) → w y ≤ max (φ y) 0 :=
      fun y hy hycl ↦ hN₀ ⟨hy.1, hycl, hy.2⟩
    -- `φ ≥ 0` on `\overline{{w > 0}}` near `x₀`
    have hφnn : ∀ y ∈ N₀ ∩ U, y ∈ closure (posSet w U) → 0 ≤ φ y := by
      have hsub : N₀ ∩ U ∩ posSet w U ⊆ {y | 0 ≤ φ y} := by
        rintro y ⟨hyN, hyU, hy⟩
        have h1 := hN y hyN (subset_closure ⟨hyU, hy⟩)
        by_contra hneg
        simp only [Set.mem_ofPred_eq, not_le] at hneg
        rw [max_eq_right hneg.le] at h1
        linarith
      intro y hyN hycl
      exact closure_minimal hsub (isClosed_le continuous_const hφ.continuous)
        (hNo.inter_closure ⟨hyN, hycl⟩)
    have hstrict : max (ψ x₀) 0 = w x₀ ∧
        ∀ᶠ y in 𝓝[(closure (posSet w U) ∩ U) \ {x₀}] x₀, w y < max (ψ y) 0 := by
      refine ⟨by rw [hψx]; exact htouch.2.1, mem_nhdsWithin.2 ⟨N₀ ∩ U, hNo, ⟨hx₀N₀, hx₀U⟩, ?_⟩⟩
      rintro y ⟨hyN, ⟨hycl, -⟩, hne⟩
      have hne' : y ≠ x₀ := fun h ↦ hne (mem_singleton_iff.2 h)
      have hpos : 0 < (‖y - x₀‖ ^ 2) ^ 2 := by
        have : y - x₀ ≠ 0 := sub_ne_zero.2 hne'
        positivity
      have h1 := hN y hyN hycl
      rw [max_eq_left (hφnn y hyN hycl)] at h1
      change w y < max (ψ y) 0
      refine lt_of_lt_of_le ?_ (le_max_left _ _)
      simp only [hψ_def]; linarith
    have hfail' : Δ ψ x₀ < 0 ∧ (ψ x₀ = 0 → ‖∇ ψ x₀‖ < Q x₀) := by
      rw [hψl, hψg, hψx]; exact hfail
    -- `x₀ ∈ B̄`
    have hx₀cb : x₀ ∈ closedBall x r := by
      by_contra hout
      apply hA
      have hW : IsOpen (U \ closedBall x r) := hU.sdiff isClosed_closedBall
      have heqW : EqOn w u (U \ closedBall x r) := fun y hy ↦
        hwout y ⟨hy.1, fun h ↦ hy.2 (ball_subset_closedBall h)⟩
      have hmem : x₀ ∈ closure (posSet w U) ∩ U ∩ (U \ closedBall x r) :=
        ⟨⟨hx₀cl, hx₀U⟩, hx₀U, hout⟩
      rw [closure_posSet_inter_eq hW Set.sdiff_subset heqW] at hmem
      have hsub : posSet u (U \ closedBall x r) ⊆ posSet u U := fun y hy ↦ ⟨hy.1.1, hy.2⟩
      exact ⟨closure_mono hsub hmem.1, heqW ⟨hx₀U, hout⟩⟩
    have hx₀B' : x₀ ∈ ball x (δ + r) := closedBall_subset_ball hrr' hx₀cb
    -- the perturbation stays above the obstacle near `x₀`
    obtain ⟨ρ, η, hρ, hη, hρB', hP⟩ : ∃ ρ η : ℝ, 0 < ρ ∧ 0 < η ∧ ball x₀ ρ ⊆ ball x (δ + r) ∧
        ∀ y ∈ ball x₀ ρ, u y ≤ min (w y) (max (ψ y - η) 0) := by
      by_cases hi : u x₀ < w x₀
      · -- case (i)
        have hψw : ψ x₀ = w x₀ := by
          have h := hstrict.1
          rcases le_total (ψ x₀) 0 with h' | h'
          · rw [max_eq_right h'] at h; linarith [hu0 x₀ hx₀U]
          · rwa [max_eq_left h'] at h
        have hc : ContinuousAt (fun y ↦ ψ y - u y) x₀ :=
          hψ.continuous.continuousAt.sub (hucont.continuousAt (hU.mem_nhds hx₀U))
        have hev : ∀ᶠ y in 𝓝 x₀, (w x₀ - u x₀) / 2 < ψ y - u y :=
          hc.eventually (lt_mem_nhds (by simp only [hψw]; linarith))
        obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff_ball.1
          (hev.and (isOpen_ball.mem_nhds hx₀B'))
        refine ⟨ρ, (w x₀ - u x₀) / 2, hρ, by linarith, fun y hy ↦ (hρ' y hy).2, fun y hy ↦
          le_min (huw y (hB'U' (hρ' y hy).2)) ?_⟩
        have := (hρ' y hy).1
        exact le_trans (by linarith) (le_max_left _ _)
      · -- case (ii): `u ≡ 0` near `x₀`
        have hweq : w x₀ = u x₀ := le_antisymm (not_lt.1 hi) (huw x₀ hx₀U)
        have hncl : x₀ ∉ closure (posSet u U) := fun h ↦ hA ⟨h, hweq⟩
        have hev : ∀ᶠ y in 𝓝 x₀, y ∉ posSet u U := by
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hncl] with y hy h
          exact hy (subset_closure h)
        obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff_ball.1
          (hev.and (isOpen_ball.mem_nhds hx₀B'))
        refine ⟨ρ, 1, hρ, one_pos, fun y hy ↦ (hρ' y hy).2, fun y hy ↦ ?_⟩
        have hyU : y ∈ U := hB'U' (hρ' y hy).2
        have hu_y : u y = 0 :=
          le_antisymm (not_lt.1 fun h ↦ (hρ' y hy).1 ⟨hyU, h⟩) (hu0 y hyU)
        rw [hu_y]
        exact le_min (hw0 y hyU) (le_max_right _ _)
    obtain ⟨w', Gw', hGw', hw'out, hw'bd, hlt'⟩ := Registry.energy_decrease_of_not_sub hU hQ
      hQpos hQb hwcU hw0 hGw isOpen_ball hB'U hψ hx₀B' hx₀cl hstrict hfail' ρ hρ hρB' η hη
    -- admissibility of `w'`
    have hw'u : ∀ y ∈ U, u y ≤ w' y := fun y hy ↦ by
      by_cases hyρ : y ∈ ball x₀ ρ
      · exact (hP y hyρ).trans (hw'bd y hy).1
      · rw [hw'out y ⟨hy, hyρ⟩]; exact huw y hy
    have hw'eq : ∀ y ∈ U \ ball x r, w' y = u y := fun y hy ↦
      le_antisymm ((hw'bd y hy.1).2.trans (hwout y hy).le) (hw'u y hy.1)
    have key := hmin w' Gw' hGw' ((ae_restrict_iff' hmeas).2 (Eventually.of_forall hw'eq))
      ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall hw'u))
    -- the energies of `w'` and `w` on `B' \ B` agree
    have hext : energyJ (ball x (δ + r) \ ball x r) Q w' Gw' =
        energyJ (ball x (δ + r) \ ball x r) Q w Gw := by
      refine energyJ_congr (fun y hy ↦ by
        rw [hw'eq y ⟨hB'U' hy.1, hy.2⟩, hwout y ⟨hB'U' hy.1, hy.2⟩]) ?_
      have hW : IsOpen (U \ closure (ball x r)) := hU.sdiff isClosed_closure
      have hae := HasWeakGradient.ae_eq_of_eqOn hU hW Set.sdiff_subset hGw'.1 hGw.1 (fun y hy ↦ by
        have hy' : y ∈ U \ ball x r := ⟨hy.1, fun h ↦ hy.2 (subset_closure h)⟩
        rw [hw'eq y hy', hwout y hy'])
      have hfr : volume (frontier (ball x r)) = 0 :=
        Convex.addHaar_frontier volume (convex_ball x r)
      rw [ae_restrict_iff' (measurableSet_ball.diff measurableSet_ball)]
      rw [ae_restrict_iff' hW.measurableSet] at hae
      filter_upwards [hae, measure_eq_zero_iff_ae_notMem.1 hfr] with y hy hyfr hyB
      refine hy ⟨hB'U' hyB.1, fun hcl ↦ ?_⟩
      rw [closure_eq_interior_union_frontier, isOpen_ball.interior_eq] at hcl
      rcases hcl with h | h
      · exact hyB.2 h
      · exact hyfr h
    have hsplit := energyJ_split measurableSet_ball measurableSet_ball
      (ball_subset_ball (x := x) hrr'.le) Q
    rw [hsplit w' Gw', hsplit w Gw, hext] at hlt'
    exact absurd hlt' (not_lt.2 (add_le_add key le_rfl))
  -- hence `w = u`
  have hwu_eq : ∀ y ∈ U, w y = u y := fun y hy ↦
    le_antisymm (hll.2 x r hr hB w hwsub hwout y hy) (huw y hy)
  have hJu : energyJ (ball x r) Q u Gu = energyJ (ball x r) Q w Gw :=
    energyJ_congr (fun y hy ↦ (hwu_eq y (hbU hy)).symm)
      (HasWeakGradient.ae_eq_of_eqOn hU isOpen_ball hbU hGu.1 hGw.1
        fun y hy ↦ (hwu_eq y (hbU hy)).symm)
  rw [hJu]
  exact hmin v Gv hGv hvout huv

/-- **Lemma 6.3** in the standing setting, with the added hypotheses that `u` is locally Lipschitz,
`C²` and harmonic in `{u > 0}` (see the module docstring). -/
theorem directional : DirectionalStatement := by
  intro d S u hu hc2 hharm
  have hQ : ∃ K, LipschitzOnWith K S.Q S.U :=
    let ⟨K, hK⟩ := S.lip; ⟨K, hK.mono subset_closure⟩
  have hQpos : ∃ c > 0, ∀ x ∈ S.U, c ≤ S.Q x :=
    ⟨S.Qmin, S.Qmin_pos, fun x hx ↦ (S.Q_mem x (subset_closure hx)).1⟩
  have hQb : ∃ C, ∀ x ∈ S.U, S.Q x ≤ C :=
    ⟨S.Qmax, fun x hx ↦ (S.Q_mem x (subset_closure hx)).2⟩
  exact ⟨downwardMinimizer_of_localSmallest S.isOpen hQ hQpos hQb hu hc2 hharm,
    upwardMinimizer_of_localLargest S.isOpen hQ hQpos hQb hu hc2 hharm⟩

end Directional

end PerronVariational

end
