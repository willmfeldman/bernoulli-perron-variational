/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import GMTFoundations.BV.TotalVariation
import GMTFoundations.Sobolev.Cutoff
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.MeasureTheory.Function.L2Space
import PerronVariational.Inner.EnergyConv
import PerronVariational.Inner.EpsIdentity
import PerronVariational.Inner.InnerVarEps
import PerronVariational.Inner.ReactionBound
import PerronVariational.Inner.SemilinearEstimates
import PerronVariational.Inner.WeakGrad
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Profiles

/-!
# The weighted perimeter bound at level `ε` ((4.7))

The perimeter estimate (4.7) (Section 4.3) of F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981. For a solution `u` of (3.4) and `χ_ε = 2 𝓑_ε(u)`, for every admissible weight
`η` and test field `ψ` with `|ψ| ≤ η`:
`∫ χ_ε div ψ = -∫ ∇χ_ε · ψ ≤ 2 L ∫ η β_ε(u) ≤ (2L / Q_min²) ∫ η Q² β_ε(u)
  = (2L / Q_min²) ∫ (-∇η · ∇u - η ∂ₜu) ≤ C(d_η, ℓ_η) ‖η‖_{L²H¹}`,
where `L = L(d_η)` is the interior Lipschitz bound (3.9) on `spt η` and the last step uses
Cauchy–Schwarz and the dissipation estimate (3.8).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-- Cauchy–Schwarz for nonnegative functions. -/
theorem integral_mul_le_sqrt_mul_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all _ hf0) (ae_of_all _ hg0) (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

/-- Parabolic cylinders around points far from the parabolic boundary lie in `U_∞`. -/
theorem parCyl_subset_UInf_of_infDist {U : Set (E d)} {p : E d × ℝ} (hp : p ∈ UInf U)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hd : 4 * r ≤ infDist p (parBdryInf U)) :
    parCyl p.1 p.2 (2 * r) ⊆ UInf U := by
  rintro ⟨y, s⟩ ⟨hy, hs⟩
  have hp2 : (0 : ℝ) < p.2 := hp.2
  have hp0 : (p.1, (0 : ℝ)) ∈ parBdryInf U := Or.inl ⟨subset_closure hp.1, rfl⟩
  have ht : infDist p (parBdryInf U) ≤ p.2 := by
    refine (infDist_le_dist_of_mem hp0).trans (le_of_eq ?_)
    rw [Prod.dist_eq]
    simp [abs_of_pos hp2, hp2.le]
  refine ⟨?_, ?_⟩
  · by_contra hyU
    have hUne : U ≠ univ := fun h ↦ hyU (h ▸ mem_univ y)
    obtain ⟨z, hz, hzd⟩ := exists_mem_frontier_infDist_compl_eq_dist hp.1 hUne
    have h1 : infDist p.1 Uᶜ ≤ dist p.1 y := infDist_le_dist_of_mem hyU
    have hzp : (z, p.2) ∈ parBdryInf U := Or.inr ⟨hz, mem_Ici.2 hp2.le⟩
    have h2 : infDist p (parBdryInf U) ≤ dist p (z, p.2) := infDist_le_dist_of_mem hzp
    have h3 : dist p (z, p.2) = dist p.1 z := by
      rw [Prod.dist_eq]
      simp
    have hy' : dist p.1 y < 2 * r := by
      rw [dist_comm]
      exact hy
    linarith
  · change 0 < s
    have := hs.1
    nlinarith

/-- A point of `spt η` is at distance `≥ d_η` from `∂_P U_∞`. -/
theorem weightDist_le_infDist {U : Set (E d)} {η : E d × ℝ → ℝ} {p : E d × ℝ}
    (hp : p ∈ tsupport η) : weightDist U η ≤ infDist p (parBdryInf U) :=
  csInf_le ⟨0, fun _ ⟨_, _, h⟩ ↦ h ▸ infDist_nonneg⟩ (mem_image_of_mem _ hp)

theorem isClosed_parBdryInf (U : Set (E d)) : IsClosed (parBdryInf U) :=
  (isClosed_closure.prod isClosed_singleton).union (isClosed_frontier.prod isClosed_Ici)

theorem weightDist_pos {U : Set (E d)} (hU : IsOpen U) {η : E d × ℝ → ℝ}
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ UInf U) (hne : (tsupport η).Nonempty) :
    0 < weightDist U η := by
  obtain ⟨p, hp, hmin⟩ := hηc.isCompact.exists_isMinOn hne
    (continuous_infDist_pt (parBdryInf U)).continuousOn
  have hpU := hηU hp
  have hne' : (parBdryInf U).Nonempty := ⟨(p.1, 0), Or.inl ⟨subset_closure hpU.1, rfl⟩⟩
  have heq : weightDist U η = infDist p (parBdryInf U) :=
    IsLeast.csInf_eq ⟨mem_image_of_mem _ hp, fun _ ⟨q, hq, h⟩ ↦ h ▸ isMinOn_iff.1 hmin q hq⟩
  rw [heq]
  refine ((isClosed_parBdryInf U).notMem_iff_infDist_pos hne').1 ?_
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · have : (0 : ℝ) < p.2 := hpU.2
    rw [mem_singleton_iff] at h
    linarith
  · have h' : p.1 ∈ U ∩ frontier U := ⟨hpU.1, h⟩
    rw [hU.inter_frontier_eq] at h'
    exact h'

/-- The interior Lipschitz bound on `spt η`, with a constant depending on `η` only through
`d_η`. -/
theorem norm_gradₓ_le_of_weightDist {U : Set (E d)} {u : E d × ℝ → ℝ} {C M' : ℝ}
    (hlip : InteriorLipEst U u C) (hbd : ∀ q ∈ UInf U, |u q| ≤ M') {η : E d × ℝ → ℝ}
    (hηU : tsupport η ⊆ UInf U) {p : E d × ℝ} (hp : p ∈ tsupport η)
    (hd : 0 < weightDist U η) :
    ‖gradₓ u p‖ ≤ C * (M' / min 1 (weightDist U η / 4) + 1) := by
  set r := min 1 (weightDist U η / 4) with hrdef
  have hr : 0 < r := lt_min one_pos (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have h4 : 4 * r ≤ infDist p (parBdryInf U) := by
    have : r ≤ weightDist U η / 4 := min_le_right _ _
    linarith [weightDist_le_infDist (U := U) hp]
  have hcyl := parCyl_subset_UInf_of_infDist (hηU hp) hr hr1 h4
  exact hlip p.1 p.2 r hr hr1 hcyl M' (fun q hq ↦ hbd q (hcyl hq)) p
    ⟨mem_ball_self hr, by simp only [mem_Ioc]; constructor <;> nlinarith⟩

theorem tsupport_slice_subset' {F : Type*} [Zero F] [TopologicalSpace F] (f : E d × ℝ → F)
    (t : ℝ) : tsupport (fun x ↦ f (x, t)) ⊆ {x | (x, t) ∈ tsupport f} :=
  closure_minimal (fun _ hx ↦ subset_tsupport f hx)
    ((isClosed_tsupport f).preimage (continuous_id.prodMk continuous_const))

theorem hasCompactSupport_slice' {F : Type*} [Zero F] [TopologicalSpace F] {f : E d × ℝ → F}
    (hf : HasCompactSupport f) (t : ℝ) : HasCompactSupport (fun x ↦ f (x, t)) :=
  IsCompact.of_isClosed_subset (hf.isCompact.image continuous_fst) (isClosed_tsupport _)
    fun x hx ↦ ⟨(x, t), tsupport_slice_subset' f t hx, rfl⟩

theorem hasFDerivAt_chiEps_slice {U : Set (E d)} (hU : IsOpen U) {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) (ε : ℝ) {u : E d × ℝ → ℝ} {t : ℝ}
    (hC : ContDiffOn ℝ 2 (fun y ↦ u (y, t)) U) {x : E d} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ chiEps β ε u (y, t))
      ((2 : ℝ) • (betaEps β ε (u (x, t)) • fderiv ℝ (fun y ↦ u (y, t)) x)) x := by
  have hd : DifferentiableAt ℝ (fun y ↦ u (y, t)) x :=
    (hC.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  exact ((hβ.hasDerivAt_bigBEps ε (u (x, t))).comp_hasFDerivAt x hd.hasFDerivAt).const_mul 2

set_option maxHeartbeats 800000 in
-- many integrability side conditions
/-- **The perimeter computation on a time slice** ((4.7)). -/
theorem integral_chiEps_divₓ_slice_le {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ}
    (hQ : ContinuousOn Q U) {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ} (hε : 0 < ε)
    {u : E d × ℝ → ℝ} (hsol : IsSemilinearSolOn U Q β ε (Ioi 0) u) {m : ℝ} (hm : 0 < m)
    (hQm : ∀ x ∈ U, m ≤ Q x ^ 2) {η : E d × ℝ → ℝ} (hη : IsPerimeterWeight U η)
    {ψ : E d × ℝ → E d} (hψ : IsTVTestFieldₓ (UInf U) η ψ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ p ∈ tsupport η, ‖gradₓ u p‖ ≤ L) (t : ℝ) :
    ∫ x, chiEps β ε u (x, t) * divₓ ψ (x, t) ≤
      2 * L / m * ∫ x, (-⟪gradₓ u (x, t), gradₓ η (x, t)⟫ - η (x, t) * dₜ u (x, t)) := by
  obtain ⟨hηC, hηc, hηU, hη0⟩ := hη
  obtain ⟨hψC, hψc, hψU, hψη⟩ := hψ
  rcases le_or_gt t 0 with ht | ht
  · have hn : ∀ {x : E d} {S : Set (E d × ℝ)}, S ⊆ UInf U → (x, t) ∉ S := fun hS h ↦
      (not_lt.2 ht) (hS h).2
    have h1 : ∀ x, divₓ ψ (x, t) = 0 := fun x ↦ divₓ_eq_zero_of_notMem (hn hψU)
    have h2 : ∀ x, η (x, t) = 0 := fun x ↦ image_eq_zero_of_notMem_tsupport (hn hηU)
    have h3 : ∀ x, gradₓ η (x, t) = 0 := fun x ↦ gradₓ_eq_zero_of_notMem (hn hηU)
    simp [h1, h2, h3]
  set θ : E d → ℝ := fun x ↦ η (x, t) with hθdef
  set Y : E d → E d := fun x ↦ ψ (x, t) with hYdef
  set h : E d → ℝ := fun x ↦ chiEps β ε u (x, t) with hhdef
  have hθC : ContDiff ℝ 1 θ := hηC.comp (contDiff_id.prodMk contDiff_const)
  have hYC : ContDiff ℝ 1 Y := hψC.comp (contDiff_id.prodMk contDiff_const)
  have hθc : HasCompactSupport θ := hasCompactSupport_slice hηc t
  have hYc : HasCompactSupport Y := hasCompactSupport_slice' hψc t
  have hθU : tsupport θ ⊆ U := fun x hx ↦ (hηU (tsupport_slice_subset η t hx)).1
  have hYU : tsupport Y ⊆ U := fun x hx ↦ (hψU (tsupport_slice_subset' ψ t hx)).1
  have hθ0 : ∀ x ∉ tsupport θ, θ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hY0 : ∀ x ∉ tsupport Y, Y x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hgθ0 : ∀ x ∉ tsupport θ, gradₓ η (x, t) = 0 := fun x hx ↦ by
    change ∇ θ x = 0
    simp only [gradient]
    rw [fderiv_of_notMem_tsupport ℝ hx, map_zero]
  obtain ⟨CY, hYL⟩ := hYC.lipschitzWith_of_hasCompactSupport hYc one_ne_zero
  have hC2 := hsol.2.1 t ht
  have hhC : ContDiffOn ℝ 1 h U :=
    contDiffOn_const.mul ((contDiff_bigBEps hβ ε).comp_contDiffOn (hC2.of_le (by norm_num)))
  have hibp := integral_fderiv_apply_eq_neg hU hhC hYL hYc hYU
  have hβ0 : ∀ x, 0 ≤ betaEps β ε (u (x, t)) := fun x ↦ hβ.betaEps_nonneg ε _ hε.le
  have hβc : ContinuousOn (fun x ↦ betaEps β ε (u (x, t))) U :=
    (hβ.continuous_betaEps ε).comp_continuousOn (continuousOn_slice_of_prod hsol.1 ht)
  -- pointwise bound
  have hpt : ∀ x, -(fderiv ℝ h x (Y x)) ≤ 2 * L * (betaEps β ε (u (x, t)) * θ x) := by
    intro x
    by_cases hY : Y x = 0
    · rw [hY, map_zero, neg_zero]
      have := hη0 (x, t)
      have := hβ0 x
      positivity
    · have hpos : 0 < η (x, t) := (norm_pos_iff.2 hY).trans_le (hψη (x, t))
      have hxη : (x, t) ∈ tsupport η := subset_tsupport η (ne_of_gt hpos)
      have hxU : x ∈ U := (hηU hxη).1
      rw [(hasFDerivAt_chiEps_slice hU hβ ε hC2 hxU).fderiv]
      have hD : ‖fderiv ℝ (fun y ↦ u (y, t)) x‖ ≤ L := by
        rw [← norm_gradient_eq_norm_fderiv]
        exact hL (x, t) hxη
      have hYx : ‖Y x‖ ≤ θ x := hψη (x, t)
      calc -(((2 : ℝ) • (betaEps β ε (u (x, t)) • fderiv ℝ (fun y ↦ u (y, t)) x)) (Y x))
          ≤ |((2 : ℝ) • (betaEps β ε (u (x, t)) • fderiv ℝ (fun y ↦ u (y, t)) x)) (Y x)| :=
            neg_le_abs _
        _ = 2 * betaEps β ε (u (x, t)) * |fderiv ℝ (fun y ↦ u (y, t)) x (Y x)| := by
            simp only [smul_apply, smul_eq_mul, abs_mul, abs_two,
              abs_of_nonneg (hβ0 x)]
            ring
        _ ≤ 2 * betaEps β ε (u (x, t)) * (L * θ x) := by
            refine mul_le_mul_of_nonneg_left ?_ (by have := hβ0 x; positivity)
            rw [← Real.norm_eq_abs]
            exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hD hYx (norm_nonneg _) hL0)
        _ = 2 * L * (betaEps β ε (u (x, t)) * θ x) := by ring
  -- integrability
  have iA : Integrable fun x ↦ -(fderiv ℝ h x (Y x)) := by
    refine GMTFoundations.integrable_of_continuousOn_of_zero hYc ?_ fun x hx ↦ by simp [hY0 x hx]
    exact (((hhC.continuousOn_fderiv_of_isOpen hU le_rfl).mono hYU).clm_apply
      hYC.continuous.continuousOn).neg
  have iB : Integrable fun x ↦ 2 * L * (betaEps β ε (u (x, t)) * θ x) := by
    refine GMTFoundations.integrable_of_continuousOn_of_zero hθc ?_ fun x hx ↦ by simp [hθ0 x hx]
    exact (continuousOn_const.mul ((hβc.mono hθU).mul hθC.continuous.continuousOn))
  have iC : Integrable fun x ↦ θ x * (Q x ^ 2 * betaEps β ε (u (x, t))) := by
    refine GMTFoundations.integrable_of_continuousOn_of_zero hθc ?_ fun x hx ↦ by simp [hθ0 x hx]
    exact (hθC.continuous.continuousOn.mul ((hQ.pow 2).mul hβc)).mono hθU
  have iD : Integrable fun x ↦ ⟪gradₓ u (x, t), gradₓ η (x, t)⟫ := by
    refine GMTFoundations.integrable_of_continuousOn_of_zero hθc ?_ fun x hx ↦ by simp [hgθ0 x hx]
    exact ((continuousOn_slice_of_prod hsol.2.2.1 ht).mono hθU).inner
      ((continuous_gradₓ hηC).comp (continuous_id.prodMk continuous_const)).continuousOn
  have iE : Integrable fun x ↦ η (x, t) * dₜ u (x, t) := by
    refine GMTFoundations.integrable_of_continuousOn_of_zero hθc ?_ fun x hx ↦ by
      rw [show η (x, t) = 0 from hθ0 x hx, zero_mul]
    exact (hθC.continuous.continuousOn.mul
      (continuousOn_slice_of_prod hsol.2.2.2.2.2.1 ht)).mono hθU
  have hstep1 : ∫ x, chiEps β ε u (x, t) * divₓ ψ (x, t) = ∫ x, -(fderiv ℝ h x (Y x)) := by
    rw [integral_neg, hibp, neg_neg]
    rfl
  have hstep2 : ∫ x, 2 * L * (betaEps β ε (u (x, t)) * θ x) ≤
      2 * L / m * ∫ x, θ x * (Q x ^ 2 * betaEps β ε (u (x, t))) := by
    rw [← integral_const_mul]
    refine integral_mono iB (iC.const_mul _) fun x ↦ ?_
    by_cases hx : x ∈ U
    · have hq := hQm x hx
      have h0 : 0 ≤ θ x := hη0 (x, t)
      have hb := hβ0 x
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]
      have : betaEps β ε (u (x, t)) * θ x * m ≤ θ x * (Q x ^ 2 * betaEps β ε (u (x, t))) := by
        nlinarith [mul_nonneg h0 hb]
      nlinarith
    · have : θ x = 0 := hθ0 x fun h ↦ hx (hθU h)
      simp [this]
  have hstep3 := integral_cutoff_reaction_eq hU hβ hsol hQ hθC hθc hθU ht
  have hstep4 : ∫ x, (-⟪gradₓ u (x, t), gradₓ η (x, t)⟫ - η (x, t) * dₜ u (x, t)) =
      -(∫ x, ⟪gradₓ u (x, t), gradₓ η (x, t)⟫) - ∫ x, η (x, t) * dₜ u (x, t) := by
    have iDn : Integrable fun x ↦ -⟪gradₓ u (x, t), gradₓ η (x, t)⟫ := iD.neg
    rw [integral_sub iDn iE, integral_neg]
  rw [hstep1, hstep4]
  calc ∫ x, -(fderiv ℝ h x (Y x)) ≤ ∫ x, 2 * L * (betaEps β ε (u (x, t)) * θ x) :=
        integral_mono iA iB hpt
    _ ≤ _ := hstep2
    _ = _ := by rw [hstep3]; rfl

/-- A function continuous on a compact set and vanishing off it is in `L²`. -/
theorem memLp_two_of_continuousOn_of_zero {K : Set (E d × ℝ)} (hK : IsCompact K)
    {g : E d × ℝ → ℝ} (hg : ContinuousOn g K) (h0 : ∀ p ∉ K, g p = 0) : MemLp g 2 volume := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have heq : K.indicator g = g := indicator_eq_self.2 fun p hp ↦ by_contra fun h ↦ hp (h0 p h)
  rw [← heq, memLp_indicator_iff_restrict hKm]
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  exact MemLp.of_bound (hg.aestronglyMeasurable hKm) C ((ae_restrict_iff' hKm).2 (ae_of_all _ hC))

/-- **Weighted perimeter bound at level `ε`** ((4.7)): there are `ε₁ > 0` and, for every `M` and
finite energy bound `E0`, a function `Cper` (depending only on the setting, `β`, `M`, `E0`) such
that `χ_ε = 2 𝓑_ε(u)` satisfies (3.13) with `Cper` for every solution with data `0 ≤ gε ≤ M`,
`gε ∈ H¹(U)`, `∫_U |Gε|² + Q_max² |U| ≤ E0`, `0 < ε < ε₁`.

The paper's (3.13) lets the constant `C_η` depend on `T_η = sup {t : (x, t) ∈ spt η}`; here it
depends on `d_η` and on the time-length `ℓ_η` of `spt η`, because Step 3 of the proof of
Theorem 3.10 needs a bound uniform in time, and the paper's proof of (4.7) gives this form. -/
theorem semilinear_weightedPerimeterEst (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (M : ℝ) (E0 : ℝ≥0∞), E0 ≠ ⊤ → ∃ Cper : ℝ → ℝ → ℝ,
      ∀ ε ∈ Ioo 0 ε₁, ∀ (gε : E d → ℝ) (Gε : E d → E d) (u : E d × ℝ → ℝ),
        MemH1 S.U gε Gε → energyBound S Gε ≤ E0 → IsSemilinearSolution S.U S.Q β ε gε u →
        (∀ x ∈ S.U, 0 ≤ gε x ∧ gε x ≤ M) → WeightedPerimeterEst S.U (chiEps β ε u) Cper := by
  classical
  obtain ⟨KQ, hKQ⟩ := S.lip
  have hQc : ContinuousOn S.Q S.U := hKQ.continuousOn.mono subset_closure
  obtain ⟨C, ε₁, hε₁, hLip⟩ := semilinear_interiorLipEst S hβ
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, fun M E0 hE0 ↦ ?_⟩
  set C' := max C 0 with hC'def
  set m := S.Qmin ^ 2 with hmdef
  have hm : 0 < m := by have := S.Qmin_pos; positivity
  set Lf : ℝ → ℝ := fun dd ↦ C' * (max M 1 / min 1 (dd / 4) + 1) with hLfdef
  set VU := (volume S.U).toReal with hVUdef
  refine ⟨fun dd ℓ ↦ 2 * Lf dd / m * (Lf dd * Real.sqrt (VU * ℓ) + Real.sqrt (E0.toReal / 2)),
    ?_⟩
  intro ε hε gε Gε u hH1 hEn hu hg η hη
  refine iSup₂_le fun ψ hψ ↦ ENNReal.ofReal_le_ofReal ?_
  have hεpos : 0 < ε := hε.1
  have hsol := hu.2.1
  have hΩ : IsOpen (UInf S.U) := S.isOpen.prod isOpen_Ioi
  set dd := weightDist S.U η with hdddef
  set ℓ := weightTimeLength η with hℓdef
  set N := l2H1Norm S.U η with hNdef
  set K := tsupport η with hKdef
  obtain ⟨hηC, hηc, hηU, hη0⟩ := hη
  obtain ⟨hψC, hψc, hψU, hψη⟩ := hψ
  have hdd0 : 0 ≤ dd := Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ infDist_nonneg
  have hLf0 : 0 ≤ Lf dd := mul_nonneg (le_max_right _ _) (by
    have : 0 ≤ min 1 (dd / 4) := le_min zero_le_one (by positivity)
    have : 0 ≤ max M 1 / min 1 (dd / 4) := div_nonneg (le_max_right _ _ |>.trans' zero_le_one) this
    linarith)
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hRHS0 : 0 ≤ 2 * Lf dd / m * (Lf dd * Real.sqrt (VU * ℓ) + Real.sqrt (E0.toReal / 2)) * N :=
    by positivity
  have hψ0 : ∀ p ∉ K, ψ p = 0 := fun p hp ↦ by
    have h1 := hψη p
    rw [image_eq_zero_of_notMem_tsupport hp] at h1
    exact norm_le_zero_iff.1 h1
  have hψK : tsupport ψ ⊆ K :=
    closure_minimal (fun p hp ↦ by_contra fun h ↦ hp (hψ0 p h)) (isClosed_tsupport η)
  rcases K.eq_empty_or_nonempty with hK0 | hne
  · have : ∀ p, divₓ ψ p = 0 := fun p ↦ divₓ_eq_zero_of_notMem (fun h ↦ by
      have := hψK h
      rw [hK0] at this
      exact this)
    simp only [this, mul_zero, integral_zero]
    exact hRHS0
  -- the Lipschitz bound on `spt η`
  have hd : 0 < dd := weightDist_pos S.isOpen hηc hηU hne
  set L := Lf dd with hLdef
  have hbd : ∀ q ∈ UInf S.U, |u q| ≤ max M 1 := fun q hq ↦ by
    have h := semilinear_nonneg_le_max S hβ hεpos hu hg q
      ⟨subset_closure hq.1, mem_Ici.2 (le_of_lt hq.2)⟩
    rw [abs_of_nonneg h.1]
    exact h.2.trans (max_le_max le_rfl (hε.2.trans_le (min_le_right _ _)).le)
  have hlip := hLip ε ⟨hεpos, hε.2.trans_le (min_le_left _ _)⟩ M gε u hu hg
  have hLu : ∀ p ∈ K, ‖gradₓ u p‖ ≤ L := fun p hp ↦ by
    refine (norm_gradₓ_le_of_weightDist hlip hbd hηU hp hd).trans ?_
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    have : 0 < min 1 (dd / 4) := lt_min one_pos (by positivity)
    have : 0 ≤ max M 1 / min 1 (dd / 4) := div_nonneg (le_max_right _ _ |>.trans' zero_le_one)
      this.le
    linarith
  have hQm : ∀ x ∈ S.U, m ≤ S.Q x ^ 2 := fun x hx ↦
    pow_le_pow_left₀ S.Qmin_pos.le (S.Q_mem x (subset_closure hx)).1 2
  have hKc : IsCompact K := hηc
  have hKm : MeasurableSet K := (isClosed_tsupport η).measurableSet
  have hKU : K ⊆ UInf S.U := hηU
  have hη0' : ∀ p ∉ K, η p = 0 := fun p hp ↦ image_eq_zero_of_notMem_tsupport hp
  have hgη0 : ∀ p ∉ K, gradₓ η p = 0 := fun p hp ↦ gradₓ_eq_zero_of_notMem hp
  have hχc : ContinuousOn (chiEps β ε u) (UInf S.U) :=
    continuousOn_const.mul ((continuous_iff_continuousAt.2 fun z ↦
      (hβ.hasDerivAt_bigBEps ε z).continuousAt).comp_continuousOn hsol.1)
  -- the integrands on space-time
  set F : E d × ℝ → ℝ := fun p ↦ chiEps β ε u p * divₓ ψ p with hFdef
  set G : E d × ℝ → ℝ := fun p ↦ -⟪gradₓ u p, gradₓ η p⟫ - η p * dₜ u p with hGdef
  have hF0 : ∀ p ∉ K, F p = 0 := fun p hp ↦ by
    simp [hFdef, divₓ_eq_zero_of_notMem (fun h ↦ hp (hψK h))]
  have hG0 : ∀ p ∉ K, G p = 0 := fun p hp ↦ by simp [hGdef, hη0' p hp, hgη0 p hp]
  have hFi : Integrable F := GMTFoundations.integrable_of_continuousOn_of_zero hKc
    ((hχc.mono hKU).mul (GMTFoundations.continuous_divₓ hψC).continuousOn) hF0
  have hGi : Integrable G := GMTFoundations.integrable_of_continuousOn_of_zero hKc
    ((((hsol.2.2.1.mono hKU).inner (continuous_gradₓ hηC).continuousOn).neg).sub
      (hηC.continuous.continuousOn.mul (hsol.2.2.2.2.2.1.mono hKU))) hG0
  -- Steps (1)–(4): integration by parts on slices and Fubini
  have hstep1 : ∫ p in UInf S.U, chiEps β ε u p * divₓ ψ p = ∫ p, F p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ hF0 p fun h ↦ hp (hKU h)
  have hFi' : Integrable F ((volume : Measure (E d)).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]; exact hFi
  have hGi' : Integrable G ((volume : Measure (E d)).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]; exact hGi
  have hstep2 : ∫ p, F p ≤ 2 * L / m * ∫ p, G p := by
    rw [Measure.volume_eq_prod, integral_prod_symm _ hFi', integral_prod_symm _ hGi',
      ← integral_const_mul]
    exact integral_mono hFi'.integral_prod_right (hGi'.integral_prod_right.const_mul _)
      fun t ↦ integral_chiEps_divₓ_slice_le S.isOpen hQc hβ hεpos hsol hm hQm
        ⟨hηC, hηc, hηU, hη0⟩ ⟨hψC, hψc, hψU, hψη⟩ hLf0 hLu t
  -- Step (5): pointwise bound of `G`
  set A : E d × ℝ → ℝ := K.indicator (fun _ ↦ (1 : ℝ)) with hAdef
  set g₁ : E d × ℝ → ℝ := fun p ↦ ‖gradₓ η p‖ with hg₁def
  set g₂ : E d × ℝ → ℝ := K.indicator (fun p ↦ |dₜ u p|) with hg₂def
  have hA : MemLp A 2 volume := memLp_indicator_const 2 hKm 1 (Or.inr hKc.measure_lt_top.ne)
  have hg₁ : MemLp g₁ 2 volume := memLp_two_of_continuousOn_of_zero hKc
    (continuous_gradₓ hηC).norm.continuousOn fun p hp ↦ by simp [hg₁def, hgη0 p hp]
  have hηm : MemLp η 2 volume :=
    memLp_two_of_continuousOn_of_zero hKc hηC.continuous.continuousOn hη0'
  have hg₂ : MemLp g₂ 2 volume := memLp_two_of_continuousOn_of_zero hKc
    ((hsol.2.2.2.2.2.1.mono hKU).abs.congr fun p hp ↦ by simp [hg₂def, indicator_of_mem hp])
    fun p hp ↦ by simp [hg₂def, indicator_of_notMem hp]
  have hpt : ∀ p, G p ≤ L * (A p * g₁ p) + η p * g₂ p := by
    intro p
    by_cases hp : p ∈ K
    · simp only [hGdef, hAdef, hg₁def, hg₂def, indicator_of_mem hp, one_mul]
      have h1 : -⟪gradₓ u p, gradₓ η p⟫ ≤ L * ‖gradₓ η p‖ :=
        (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hLu p hp) (norm_nonneg _)))
      have h2 : -(η p * dₜ u p) ≤ η p * |dₜ u p| := by
        rw [← abs_of_nonneg (hη0 p), ← abs_mul, abs_of_nonneg (hη0 p)]
        exact neg_le_abs _
      linarith
    · simp [hGdef, hAdef, hg₁def, hg₂def, indicator_of_notMem hp, hη0' p hp, hgη0 p hp]
  have hi1 := integrable_mul_of_memLp hA hg₁
  have hi2 := integrable_mul_of_memLp hηm hg₂
  have hstep5 : ∫ p, G p ≤ L * (∫ p, A p * g₁ p) + ∫ p, η p * g₂ p := by
    rw [← integral_const_mul, ← integral_add (hi1.const_mul L) hi2]
    exact integral_mono hGi ((hi1.const_mul L).add hi2) hpt
  -- Step (6): Cauchy–Schwarz
  have hA0 : ∀ p, 0 ≤ A p := fun p ↦ by by_cases hp : p ∈ K <;> simp [hAdef, hp]
  have hg₂0 : ∀ p, 0 ≤ g₂ p := fun p ↦ by by_cases hp : p ∈ K <;> simp [hg₂def, hp]
  have hCS1 := integral_mul_le_sqrt_mul_sqrt hA0 (fun p ↦ norm_nonneg _) hA hg₁
  have hCS2 := integral_mul_le_sqrt_mul_sqrt hη0 hg₂0 hηm hg₂
  have hA2 : ∫ p, A p ^ 2 = (volume K).toReal := by
    have : (fun p ↦ A p ^ 2) = A := funext fun p ↦ by by_cases hp : p ∈ K <;> simp [hAdef, hp]
    rw [this, hAdef, integral_indicator_const _ hKm, measureReal_def, smul_eq_mul, mul_one]
  -- Step (7): the `L²H¹` norm
  have hNsq : ∫ p in UInf S.U, η p ^ 2 + ‖gradₓ η p‖ ^ 2 = ∫ p, η p ^ 2 + ‖gradₓ η p‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ by
      have : p ∉ K := fun h ↦ hp (hKU h)
      simp [hη0' p this, hgη0 p this]
  have hsq_int : Integrable (fun p ↦ η p ^ 2 + ‖gradₓ η p‖ ^ 2) :=
    hηm.integrable_sq.add hg₁.integrable_sq
  have hN1 : Real.sqrt (∫ p, g₁ p ^ 2) ≤ N := by
    rw [hNdef, l2H1Norm, hNsq]
    exact Real.sqrt_le_sqrt (integral_mono hg₁.integrable_sq hsq_int fun p ↦ by
      simp only [hg₁def]
      nlinarith [sq_nonneg (η p)])
  have hN2 : Real.sqrt (∫ p, η p ^ 2) ≤ N := by
    rw [hNdef, l2H1Norm, hNsq]
    exact Real.sqrt_le_sqrt (integral_mono hηm.integrable_sq hsq_int fun p ↦ by
      nlinarith [sq_nonneg ‖gradₓ η p‖])
  -- Step (8): the dissipation estimate
  obtain ⟨K₁, hK₁c, hK₁U, T₁, T₂, hT₁, hT₁₂, hKB⟩ := exists_box hKU hKc hne
  have hdis := semilinear_dissipation S hβ hεpos hH1 hu T₂ (by linarith)
  have hKsub : K ⊆ S.U ×ˢ Ioc 0 T₂ := fun p hp ↦ ⟨(hKU hp).1, (hKU hp).2, (hKB hp).2.2⟩
  have hg₂sq : ∫ p, g₂ p ^ 2 ≤ E0.toReal / 2 := by
    have heq : (fun p ↦ g₂ p ^ 2) = K.indicator (fun p ↦ dₜ u p ^ 2) := funext fun p ↦ by
      by_cases hp : p ∈ K <;> simp [hg₂def, hp, sq_abs]
    rw [heq, integral_indicator hKm, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun p ↦ sq_nonneg _)
      (((hsol.2.2.2.2.2.1.mono hKU).pow 2).aestronglyMeasurable hKm)]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc ∫⁻ p in K, ENNReal.ofReal (dₜ u p ^ 2)
        ≤ ∫⁻ p in S.U ×ˢ Ioc 0 T₂, ENNReal.ofReal (dₜ u p ^ 2) := lintegral_mono_set hKsub
      _ ≤ energyBound S Gε / 2 := le_add_self.trans hdis
      _ ≤ E0 / 2 := ENNReal.div_le_div_right hEn 2
      _ = ENNReal.ofReal (E0.toReal / 2) := by
          rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hE0, ENNReal.ofReal_ofNat]
  -- Step (9): the measure of `spt η`
  have hbddb : BddBelow (Prod.snd '' K) := (hKc.image continuous_snd).bddBelow
  have hbdda : BddAbove (Prod.snd '' K) := (hKc.image continuous_snd).bddAbove
  obtain ⟨p₀, hp₀⟩ := hne
  have hab : sInf (Prod.snd '' K) ≤ sSup (Prod.snd '' K) :=
    (csInf_le hbddb (mem_image_of_mem _ hp₀)).trans (le_csSup hbdda (mem_image_of_mem _ hp₀))
  have hKsub2 : K ⊆ S.U ×ˢ Icc (sInf (Prod.snd '' K)) (sSup (Prod.snd '' K)) := fun p hp ↦
    ⟨(hKU hp).1, csInf_le hbddb (mem_image_of_mem _ hp), le_csSup hbdda (mem_image_of_mem _ hp)⟩
  have hvolU : volume S.U ≠ ⊤ := S.isBounded.measure_lt_top.ne
  have hvolK : (volume K).toReal ≤ VU * ℓ := by
    have h := measure_mono (μ := volume) hKsub2
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, ← Measure.volume_eq_prod] at h
    have hne' : volume S.U * ENNReal.ofReal (sSup (Prod.snd '' K) - sInf (Prod.snd '' K)) ≠ ⊤ :=
      ENNReal.mul_ne_top hvolU ENNReal.ofReal_ne_top
    refine (ENNReal.toReal_mono hne' h).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), hVUdef, hℓdef, weightTimeLength]
  -- Step (10): conclusion
  have e1 : ∫ p, A p * g₁ p ≤ Real.sqrt (VU * ℓ) * N :=
    hCS1.trans (mul_le_mul (Real.sqrt_le_sqrt (hA2 ▸ hvolK)) hN1 (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))
  have e2 : ∫ p, η p * g₂ p ≤ N * Real.sqrt (E0.toReal / 2) :=
    hCS2.trans (mul_le_mul hN2 (Real.sqrt_le_sqrt hg₂sq) (Real.sqrt_nonneg _) hN0)
  have e3 : ∫ p, G p ≤ L * (Real.sqrt (VU * ℓ) * N) + N * Real.sqrt (E0.toReal / 2) :=
    hstep5.trans (add_le_add (mul_le_mul_of_nonneg_left e1 hLf0) e2)
  rw [hstep1]
  calc ∫ p, F p ≤ 2 * L / m * ∫ p, G p := hstep2
    _ ≤ 2 * L / m * (L * (Real.sqrt (VU * ℓ) * N) + N * Real.sqrt (E0.toReal / 2)) :=
        mul_le_mul_of_nonneg_left e3 (by positivity)
    _ = _ := by ring



end Inner

end PerronVariational

end
