/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.MeasureTheory.Integral.CircleAverage
public import PerronVariational.Basic.Setting -- shake: keep
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Circle means in the plane and the Riesz measure (Appendix B, Lemma B.3)

Planar tools for the proof of **Thm B.1** of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981
("the paper"): the non-degeneracy of largest subsolutions in the plane, due to B. Orcan-Ekmekci, *On
the geometry and regularity of largest subsolutions for a free boundary problem in ℝ²: elliptic
case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3-4, 937–962,
doi:10.1007/s00526-013-0606-8.

* `toE2 : ℂ ≃ₗᵢ[ℝ] E 2` and `circleMean u x r`, the average of `u : E 2 → ℝ` over `∂B_r(x)`,
  defined through Mathlib's `Real.circleAverage`.
* `laplacian_comp_toE2`: the Laplacian commutes with the isometry. Consequently harmonic
  functions on `E 2` have the mean value property (`circleMean_eq_of_harmonic`), and a
  non-negative harmonic function vanishing at the centre of a ball vanishes on the ball
  (`eqOn_zero_of_harmonic_of_eq_zero`, a strong minimum principle).
* `le_circleMean_of_lipschitz`: a lower bound for the circle mean of a Lipschitz non-negative
  function in terms of its value at one point of the circle (Lemma B.3, (ii) ⇒ (i); the paper
  says this follows "from the Lipschitz estimate", which implicitly uses the arc on which
  `u ≥ M/2`).
* `IsRieszMeasure Ω u μ`: `μ` is the Riesz measure `Δu` of `u` in `Ω`, in the form of the
  Riesz–Jensen formula
  `⨍_{∂B_r(x)} u - u(x) = (1/2π) ∫₀^r μ(B_s(x)) / s ds`
  (the integrated form of the paper's identity
  `d/dr ⨍_{∂B_r} u = |∂B_1|⁻¹ r^{1-d} ∫_{B_r} Δu` in the proof of Lemma B.3, for `d = 2`).
* The existence of the Riesz measure (`exists_isRieszMeasure`, the paper's "since `Δu` is a
  non-negative measure" in the proof of Lemma B.3, used there without proof) is proved in
  `PerronVariational.Appendix.RieszMeasure`.
* The two directions of **Lemma B.3** used in Thm B.1, in single-radius form:
  `mass_lower_bound` ((ii) ⇒ (iii) at one radius) and `circleMean_lower_bound` ((iii) ⇒ (i)).
  The paper states Lemma B.3 for bounds at all radii but applies it with the bound of Lemma B.2
  at a single scale; here we state the single-radius version, which is what the proof of Thm B.1
  needs and which holds.
-/

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Laplacian Real ENNReal

@[expose] public section

namespace PerronVariational

/-! ### The plane as `ℂ` -/

/-- The linear isometry `ℂ ≃ E 2` (the coordinates in the basis `1, i`). -/
noncomputable def toE2 : ℂ ≃ₗᵢ[ℝ] E 2 := Complex.orthonormalBasisOneI.repr

/-- The Laplacian commutes with the isometry `ℂ ≃ E 2`. -/
theorem laplacian_comp_toE2 (f : E 2 → ℝ) (z : ℂ) : Δ (f ∘ toE2) z = Δ f (toE2 z) := by
  set b := Complex.orthonormalBasisOneI
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ toE2) b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map toE2)]
  simp only
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := toE2.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := z) (mem_univ _) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  rw [show (f ∘ toE2) = f ∘ toE2.toContinuousLinearEquiv from rfl, h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, OrthonormalBasis.map_apply]
  congr 1
  ext j
  fin_cases j <;> rfl

/-! ### Circle means -/

/-- The mean of `u` over the circle `∂B_r(x)` in `E 2`. -/
noncomputable def circleMean (u : E 2 → ℝ) (x : E 2) (r : ℝ) : ℝ :=
  Real.circleAverage (u ∘ toE2) (toE2.symm x) r

theorem norm_toE2_circleMap_sub (x : E 2) (r θ : ℝ) :
    ‖toE2 (circleMap (toE2.symm x) r θ) - x‖ = |r| := by
  have : toE2 (circleMap (toE2.symm x) r θ) - x =
      toE2 (circleMap (toE2.symm x) r θ - toE2.symm x) := by
    rw [map_sub, LinearIsometryEquiv.apply_symm_apply]
  rw [this, LinearIsometryEquiv.norm_map, circleMap_sub_center, norm_circleMap_zero]

theorem toE2_circleMap_mem_sphere (x : E 2) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    toE2 (circleMap (toE2.symm x) r θ) ∈ sphere x r := by
  rw [mem_sphere, dist_eq_norm, norm_toE2_circleMap_sub, abs_of_nonneg hr]

/-- Every point of `∂B_r(x)` is `toE2 (circleMap _ r θ)` for some `θ ∈ (0, 2π]`. -/
theorem exists_toE2_circleMap_eq {x y : E 2} {r : ℝ} (hr : 0 ≤ r) (hy : y ∈ sphere x r) :
    ∃ θ ∈ Ioc 0 (2 * π), toE2 (circleMap (toE2.symm x) r θ) = y := by
  have : toE2.symm y ∈ sphere (toE2.symm x) |r| := by
    rw [mem_sphere, LinearIsometryEquiv.dist_map, abs_of_nonneg hr]; exact hy
  rw [← image_circleMap_Ioc] at this
  obtain ⟨θ, hθ, h⟩ := this
  exact ⟨θ, hθ, by rw [h, LinearIsometryEquiv.apply_symm_apply]⟩

theorem continuous_comp_circleMap {u : E 2 → ℝ} {x : E 2} {r : ℝ} (hr : 0 ≤ r)
    (hu : ContinuousOn u (sphere x r)) :
    Continuous fun θ ↦ u (toE2 (circleMap (toE2.symm x) r θ)) :=
  hu.comp_continuous (toE2.continuous.comp (continuous_circleMap _ _))
    fun θ ↦ toE2_circleMap_mem_sphere x hr θ

theorem circleIntegrable_of_continuousOn {u : E 2 → ℝ} {x : E 2} {r : ℝ} (hr : 0 ≤ r)
    (hu : ContinuousOn u (sphere x r)) : CircleIntegrable (u ∘ toE2) (toE2.symm x) r := by
  refine ContinuousOn.circleIntegrable' ?_
  refine hu.comp toE2.continuous.continuousOn fun z hz ↦ ?_
  rw [mem_sphere, abs_of_nonneg hr] at hz
  rw [mem_sphere, ← hz, ← LinearIsometryEquiv.dist_map toE2, LinearIsometryEquiv.apply_symm_apply]

theorem circleMean_le {u : E 2 → ℝ} {x : E 2} {r a : ℝ} (hr : 0 ≤ r)
    (hu : ContinuousOn u (sphere x r)) (h : ∀ y ∈ sphere x r, u y ≤ a) : circleMean u x r ≤ a := by
  refine Real.circleAverage_mono_on_of_le_circle (circleIntegrable_of_continuousOn hr hu)
    fun z hz ↦ h _ ?_
  rw [mem_sphere, abs_of_nonneg hr] at hz
  rw [mem_sphere, ← hz, ← LinearIsometryEquiv.dist_map toE2, LinearIsometryEquiv.apply_symm_apply]

/-- The circle mean as an interval integral. -/
theorem circleMean_eq_integral (u : E 2 → ℝ) (x : E 2) (r : ℝ) (η : ℝ) :
    circleMean u x r =
      (2 * π)⁻¹ * ∫ θ in 0..2 * π, u (toE2 (circleMap (toE2.symm x) r (θ + η))) := by
  rw [circleMean, Real.circleAverage_eq_integral_add η, smul_eq_mul]
  rfl

/-- If a continuous non-negative `u` is positive at one point of `∂B_r(x)`, its circle mean is
positive. -/
theorem circleMean_pos {u : E 2 → ℝ} {x : E 2} {r : ℝ} (hr : 0 ≤ r)
    (hu : ContinuousOn u (sphere x r)) (hnn : ∀ y ∈ sphere x r, 0 ≤ u y) {y : E 2}
    (hy : y ∈ sphere x r) (hpos : 0 < u y) : 0 < circleMean u x r := by
  obtain ⟨θ₀, hθ₀, rfl⟩ := exists_toE2_circleMap_eq hr hy
  rw [circleMean_eq_integral u x r 0]
  refine mul_pos (inv_pos.2 Real.two_pi_pos) (intervalIntegral.integral_pos Real.two_pi_pos
    ((continuous_comp_circleMap hr hu).comp (continuous_add_const 0)).continuousOn
    (fun θ _ ↦ hnn _ (toE2_circleMap_mem_sphere x hr _)) ⟨θ₀, Ioc_subset_Icc_self hθ₀, ?_⟩)
  simpa using hpos

/-! ### Mean value property -/

/-- A `C²` function with vanishing Laplacian on `B_t(x)` is harmonic (in Mathlib's sense) after
transport to `ℂ`. -/
theorem harmonicAt_comp_toE2 {h : E 2 → ℝ} {W : Set (E 2)} (hW : IsOpen W)
    (hC2 : ContDiffOn ℝ 2 h W) (hΔ : ∀ y ∈ W, Δ h y = 0) {z : ℂ} (hz : toE2 z ∈ W) :
    InnerProductSpace.HarmonicAt (h ∘ toE2) z := by
  refine ⟨(hC2.contDiffAt (hW.mem_nhds hz)).comp z toE2.contDiff.contDiffAt, ?_⟩
  have hev : ∀ᶠ w in 𝓝 z, toE2 w ∈ W := toE2.continuous.continuousAt.eventually (hW.mem_nhds hz)
  filter_upwards [hev] with w hw
  rw [laplacian_comp_toE2, Pi.zero_apply, hΔ _ hw]

/-- **Mean value property** for harmonic functions on `E 2`. -/
theorem circleMean_eq_of_harmonic {h : E 2 → ℝ} {x : E 2} {t s : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (hC2 : ContDiffOn ℝ 2 h (ball x t)) (hΔ : ∀ y ∈ ball x t, Δ h y = 0) :
    circleMean h x s = h x := by
  have hH : InnerProductSpace.HarmonicOnNhd (h ∘ toE2) (closedBall (toE2.symm x) |s|) := by
    intro z hz
    refine harmonicAt_comp_toE2 isOpen_ball hC2 hΔ ?_
    rw [mem_closedBall, abs_of_nonneg hs] at hz
    rw [mem_ball, ← LinearIsometryEquiv.apply_symm_apply toE2 x, LinearIsometryEquiv.dist_map]
    exact hz.trans_lt hst
  rw [circleMean, HarmonicOnNhd.circleAverage_eq hH]
  simp

/-- **Strong minimum principle.** A non-negative harmonic function on `B_t(x)` vanishing at `x`
vanishes on `B_t(x)`. -/
theorem eqOn_zero_of_harmonic_of_eq_zero {h : E 2 → ℝ} {x : E 2} {t : ℝ}
    (hC2 : ContDiffOn ℝ 2 h (ball x t)) (hΔ : ∀ y ∈ ball x t, Δ h y = 0)
    (hnn : ∀ y ∈ ball x t, 0 ≤ h y) (h0 : h x = 0) : ∀ y ∈ ball x t, h y = 0 := by
  intro y hy
  by_contra hne
  have hpos : 0 < h y := lt_of_le_of_ne (hnn y hy) (Ne.symm hne)
  set s := dist y x
  have hs : 0 ≤ s := dist_nonneg
  have hst : s < t := hy
  have hsph : sphere x s ⊆ ball x t := sphere_subset_ball hst
  have hmean := circleMean_eq_of_harmonic hs hst hC2 hΔ
  have := circleMean_pos hs (hC2.continuousOn.mono hsph) (fun z hz ↦ hnn z (hsph hz))
    (show y ∈ sphere x s from rfl) hpos
  linarith

/-! ### Lower bound for circle means of Lipschitz functions -/

/-- **Lemma B.3, (ii) ⇒ (i).** If `u ≥ 0` is `L`-Lipschitz on `B̄_r(x)` and
`u(z) ≥ M > 0` at a point `z ∈ ∂B_r(x)`, then
`⨍_{∂B_r(x)} u ≥ min(M / (2 L r), π) M / (2π)`: `u ≥ M/2` on an arc of half-length
`min(M/(2Lr), π)` around `z`. -/
theorem le_circleMean_of_lipschitz {u : E 2 → ℝ} {x z : E 2} {r L M : ℝ} (hr : 0 < r)
    (hL : 0 < L) (hM : 0 < M) (hLip : LipschitzOnWith (Real.toNNReal L) u (closedBall x r))
    (hnn : ∀ y ∈ sphere x r, 0 ≤ u y) (hz : z ∈ sphere x r) (hMz : M ≤ u z) :
    min (M / (2 * L * r)) π * M / (2 * π) ≤ circleMean u x r := by
  obtain ⟨θ₀, -, rfl⟩ := exists_toE2_circleMap_eq hr.le hz
  set c := toE2.symm x
  have hcont : ContinuousOn u (sphere x r) :=
    hLip.continuousOn.mono sphere_subset_closedBall
  set g : ℝ → ℝ := fun θ ↦ u (toE2 (circleMap c r (θ + (θ₀ - π)))) with hg
  have hgc : Continuous g :=
    (continuous_comp_circleMap hr.le hcont).comp (continuous_add_const _)
  have hgnn : ∀ θ, 0 ≤ g θ := fun θ ↦ hnn _ (toE2_circleMap_mem_sphere x hr.le _)
  set δ := min (M / (2 * L * r)) π with hδ
  have hδpos : 0 < δ := lt_min (by positivity) Real.pi_pos
  have hδπ : δ ≤ π := min_le_right _ _
  have hδM : δ ≤ M / (2 * L * r) := min_le_left _ _
  -- `g ≥ M/2` on `[π - δ, π + δ]`
  have hgM : ∀ θ ∈ Icc (π - δ) (π + δ), M / 2 ≤ g θ := by
    intro θ hθ
    have hdist : dist (toE2 (circleMap c r (θ + (θ₀ - π)))) (toE2 (circleMap c r θ₀)) ≤
        M / (2 * L) := by
      rw [LinearIsometryEquiv.dist_map]
      have h1 := (lipschitzWith_circleMap c r).dist_le_mul (θ + (θ₀ - π)) θ₀
      have h2 : dist (θ + (θ₀ - π)) θ₀ ≤ δ := by
        rw [Real.dist_eq, abs_le]; constructor <;> linarith [hθ.1, hθ.2]
      rw [Real.coe_nnabs, abs_of_pos hr] at h1
      calc _ ≤ r * dist (θ + (θ₀ - π)) θ₀ := h1
        _ ≤ r * (M / (2 * L * r)) := by gcongr; exact h2.trans hδM
        _ = M / (2 * L) := by field_simp
    have hlip := hLip.dist_le_mul _ (sphere_subset_closedBall
      (toE2_circleMap_mem_sphere x hr.le (θ + (θ₀ - π))))
      _ (sphere_subset_closedBall (toE2_circleMap_mem_sphere x hr.le θ₀))
    rw [Real.coe_toNNReal _ hL.le, Real.dist_eq] at hlip
    have h3 : L * dist (toE2 (circleMap c r (θ + (θ₀ - π)))) (toE2 (circleMap c r θ₀)) ≤
        M / 2 := by
      calc _ ≤ L * (M / (2 * L)) := by gcongr
        _ = M / 2 := by field_simp
    have := (abs_le.1 (hlip.trans h3)).1
    simp only [hg]
    linarith
  rw [circleMean_eq_integral u x r (θ₀ - π)]
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b ↦ hgc.intervalIntegrable a b
  have hsub : ∫ θ in (π - δ)..(π + δ), g θ ≤ ∫ θ in (0 : ℝ)..2 * π, g θ :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Eventually.of_forall fun θ ↦ hgnn θ) (hint _ _)
  have hlow : ∫ θ in (π - δ)..(π + δ), (M / 2) ≤ ∫ θ in (π - δ)..(π + δ), g θ :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const (hint _ _) hgM
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  have hπ := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  have : δ * M = (π + δ - (π - δ)) * (M / 2) := by ring
  calc δ * M = (π + δ - (π - δ)) * (M / 2) := this
    _ ≤ ∫ θ in (0 : ℝ)..2 * π, g θ := hlow.trans hsub
    _ = (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, g θ) * (2 * π) := by field_simp

/-! ### The Riesz measure -/

/-- `μ` is the **Riesz measure** `Δu` of `u` in `Ω ⊆ E 2`, in the integrated form of the identity
for `d/dr ⨍_{∂B_r} u` in the proof of Lemma B.3 (Riesz–Jensen formula): for every closed disc
`B̄_r(x) ⊆ Ω`, `∫₀^r μ(B_s(x)) / s ds < ∞` and `⨍_{∂B_r(x)} u - u(x) = (1/2π) ∫₀^r μ(B_s(x)) / s
ds`. -/
def IsRieszMeasure (Ω : Set (E 2)) (u : E 2 → ℝ) (μ : Measure (E 2)) : Prop :=
  ∀ x r, 0 < r → closedBall x r ⊆ Ω →
    (∫⁻ s in Ioo 0 r, μ (ball x s) / ENNReal.ofReal s) ≠ (⊤ : ℝ≥0∞) ∧
      circleMean u x r - u x = (∫⁻ s in Ioo 0 r, μ (ball x s) / ENNReal.ofReal s).toReal / (2 * π)

/-! ### Lemma B.3: the two directions used in Thm B.1 -/

section RieszConsequences

variable {Ω : Set (E 2)} {u : E 2 → ℝ} {μ : Measure (E 2)}

/-- Increment of the circle mean between radii `a < r`, bounded by the mass of `B_r(x)`:
`2π (⨍_{∂B_r} u - ⨍_{∂B_a} u) ≤ μ(B_r) (r - a) / a`. -/
theorem IsRieszMeasure.circleMean_sub_le (hμ : IsRieszMeasure Ω u μ) {x : E 2} {a r : ℝ}
    (ha : 0 < a) (har : a < r) (hr : closedBall x r ⊆ Ω) :
    ENNReal.ofReal (2 * π * (circleMean u x r - circleMean u x a)) ≤
      μ (ball x r) / ENNReal.ofReal a * ENNReal.ofReal (r - a) := by
  set F : ℝ → ℝ≥0∞ := fun s ↦ μ (ball x s) / ENNReal.ofReal s with hF
  obtain ⟨hfr, hr'⟩ := hμ x r (ha.trans har) hr
  obtain ⟨hfa, ha'⟩ := hμ x a ha ((closedBall_subset_closedBall har.le).trans hr)
  have hsplit : ∫⁻ s in Ioo 0 r, F s = (∫⁻ s in Ioo 0 a, F s) + ∫⁻ s in Ioo a r, F s := by
    have h1 : Ioo 0 r = Ioc 0 a ∪ Ioo a r := (Ioc_union_Ioo_eq_Ioo ha.le har).symm
    rw [h1, lintegral_union measurableSet_Ioo
      (Ioc_disjoint_Ioi_same.mono_right Ioo_subset_Ioi_self)]
    congr 1
    exact setLIntegral_congr Ioo_ae_eq_Ioc.symm
  have hfar : (∫⁻ s in Ioo a r, F s) ≠ (⊤ : ℝ≥0∞) := by
    intro h; rw [hsplit, h, add_top] at hfr; exact hfr rfl
  have hdiff : 2 * π * (circleMean u x r - circleMean u x a) = (∫⁻ s in Ioo a r, F s).toReal := by
    have e1 : circleMean u x r - circleMean u x a =
        (circleMean u x r - u x) - (circleMean u x a - u x) := by ring
    rw [e1, hr', ha', hsplit, ENNReal.toReal_add (by rwa [← hF] at hfa) hfar]
    field_simp
    ring
  rw [hdiff, ENNReal.ofReal_toReal hfar]
  calc ∫⁻ s in Ioo a r, F s ≤ ∫⁻ _ in Ioo a r, μ (ball x r) / ENNReal.ofReal a := by
        refine setLIntegral_mono measurable_const fun s hs ↦ ?_
        exact ENNReal.div_le_div (measure_mono (ball_subset_ball hs.2.le))
          (ENNReal.ofReal_le_ofReal hs.1.le)
    _ = μ (ball x r) / ENNReal.ofReal a * ENNReal.ofReal (r - a) := by
        rw [setLIntegral_const, Real.volume_Ioo]

/-- **Lemma B.3, (i) ⇒ (iii)** at one radius, for `u(x) = 0` and `u` `L`-Lipschitz: if
`⨍_{∂B_r(x)} u ≥ A r` then `μ(B_r(x)) ≥ κ π A r` with `κ = min(A/(2L), 1/2)`. -/
theorem IsRieszMeasure.mass_lower_bound (hμ : IsRieszMeasure Ω u μ) {x : E 2} {r A L : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hL : 0 < L) (hrΩ : closedBall x r ⊆ Ω) (hux : u x = 0)
    (hLip : LipschitzOnWith (Real.toNNReal L) u (closedBall x r))
    (hmean : A * r ≤ circleMean u x r) :
    ENNReal.ofReal (min (A / (2 * L)) (1 / 2) * π * A * r) ≤ μ (ball x r) := by
  set κ := min (A / (2 * L)) (1 / 2) with hκ
  have hκpos : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκA : κ ≤ A / (2 * L) := min_le_left _ _
  have hκ1 : κ ≤ 1 / 2 := min_le_right _ _
  set a := κ * r
  have ha : 0 < a := by positivity
  have har : a < r := by
    have : κ * r ≤ 1 / 2 * r := by gcongr
    linarith
  -- `⨍_{∂B_a} u ≤ L a`
  have hma : circleMean u x a ≤ L * a := by
    refine circleMean_le ha.le (hLip.continuousOn.mono
      (sphere_subset_closedBall.trans (closedBall_subset_closedBall har.le))) fun y hy ↦ ?_
    have := hLip.dist_le_mul y ((closedBall_subset_closedBall har.le) (sphere_subset_closedBall hy))
      x (mem_closedBall_self hr.le)
    rw [Real.coe_toNNReal _ hL.le, Real.dist_eq, hux, sub_zero, mem_sphere.1 hy] at this
    exact (le_abs_self _).trans this
  have hLa : L * a ≤ A * r / 2 := by
    calc L * a = L * κ * r := by ring
      _ ≤ L * (A / (2 * L)) * r := by gcongr
      _ = A * r / 2 := by field_simp
  have hinc := hμ.circleMean_sub_le ha har hrΩ
  have hlow : ENNReal.ofReal (π * A * r) ≤
      ENNReal.ofReal (2 * π * (circleMean u x r - circleMean u x a)) :=
    ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])
  have key := hlow.trans hinc
  -- `μ(B_r) (r - a)/a ≥ π A r` and `(r - a)/a ≤ 1/κ`
  have hra : ENNReal.ofReal (r - a) ≤ ENNReal.ofReal a * ENNReal.ofReal κ⁻¹ := by
    rw [← ENNReal.ofReal_mul ha.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : a * κ⁻¹ = r := by simp only [a]; field_simp
    rw [this]; linarith
  have hμa : μ (ball x r) / ENNReal.ofReal a * ENNReal.ofReal (r - a) ≤
      μ (ball x r) * ENNReal.ofReal κ⁻¹ := by
    calc μ (ball x r) / ENNReal.ofReal a * ENNReal.ofReal (r - a)
        ≤ μ (ball x r) / ENNReal.ofReal a * (ENNReal.ofReal a * ENNReal.ofReal κ⁻¹) := by gcongr
      _ = μ (ball x r) * ENNReal.ofReal κ⁻¹ := by
        rw [← mul_assoc, ENNReal.div_mul_cancel (by simpa using ha) ENNReal.ofReal_ne_top]
  have key2 := key.trans hμa
  -- divide by `κ⁻¹`
  have e : ENNReal.ofReal (κ * π * A * r) =
      ENNReal.ofReal (π * A * r) * ENNReal.ofReal κ := by
    rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
  rw [e]
  calc ENNReal.ofReal (π * A * r) * ENNReal.ofReal κ
      ≤ μ (ball x r) * ENNReal.ofReal κ⁻¹ * ENNReal.ofReal κ := by gcongr
    _ = μ (ball x r) := by
      rw [mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hκpos.ne',
        ENNReal.ofReal_one, mul_one]

/-- **Lemma B.3, (iii) ⇒ (i)**: if `μ(B_s(x)) ≥ c s` for `0 < s < r`, then
`⨍_{∂B_r(x)} u - u(x) ≥ c r / (2π)`. -/
theorem IsRieszMeasure.circleMean_lower_bound (hμ : IsRieszMeasure Ω u μ) {x : E 2} {r c : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hrΩ : closedBall x r ⊆ Ω)
    (hmass : ∀ s ∈ Ioo 0 r, ENNReal.ofReal (c * s) ≤ μ (ball x s)) :
    c * r / (2 * π) ≤ circleMean u x r - u x := by
  obtain ⟨hfin, hid⟩ := hμ x r hr hrΩ
  rw [hid]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (ENNReal.ofReal_le_iff_le_toReal hfin).1 ?_
  calc ENNReal.ofReal (c * r) = ∫⁻ _ in Ioo 0 r, ENNReal.ofReal c := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul hc]
    _ ≤ ∫⁻ s in Ioo 0 r, μ (ball x s) / ENNReal.ofReal s := by
        refine setLIntegral_mono' measurableSet_Ioo fun s hs ↦ ?_
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hs.1))
          (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul hc]
        exact hmass s hs

end RieszConsequences

end PerronVariational

end
