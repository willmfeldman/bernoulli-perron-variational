/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.DirectionalStable.DownStep
public import PerronVariational.Inner.WeakHarmonic
import GMTFoundations.Sobolev.Lattice
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.Algebra.Order.Ring.Star
import PerronVariational.Main.Directional
import PerronVariational.Registry.Elliptic
import PerronVariational.Registry.FunctionalAnalysis

/-!
# Stability of directional minimality: Lemma 2.12

**Lemma 2.12** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: the limit `s → R`, harmonicity of
the limit (`harmonic_of_tendsto`), `isDownwardMinimizer_of_tendsto`, `isUpwardMinimizer_of_tendsto`,
and the version on domains exhausting `ℝᵈ` (`isDownwardMinimizer_of_exhaust`, used for Corollary
2.13).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal NNReal

@[expose] public section

namespace PerronVariational

namespace DirectionalStable

variable {d : ℕ}

/-! ### Letting `s → R` -/

section Limit

variable {U : Set (E d)} {x : E d} {R t : ℝ} {u Q : E d → ℝ} {un Qn : ℕ → E d → ℝ}
  {Un : ℕ → Set (E d)} {L : ℝ≥0} {Qmax : ℝ}

/-- The Poincaré inequality on annuli (from gmt-foundations v0.1.0) for `u - v` on
`B_R \ B_s`. -/
theorem poincare_sub {U : Set (E d)} (hU : IsOpen U) {x : E d} {R : ℝ} (hR : 0 < R)
    (hK : closedBall x R ⊆ U) {u v : E d → ℝ} {Gu Gv : E d → E d} (hu : MemH1Loc U u Gu)
    (hv : MemH1Loc U v Gv) (hvu' : ∀ᵐ y ∂(volume.restrict (U \ ball x R)), v y = u y) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ s, R / 2 ≤ s → s < R →
      ∫⁻ y in ball x R \ ball x s, ENNReal.ofReal ((u y - v y) ^ 2) ≤
        ENNReal.ofReal (CP * (R - s) ^ 2) *
          ∫⁻ y in ball x R \ ball x s, ENNReal.ofReal (‖Gu y - Gv y‖ ^ 2) := by
  obtain ⟨CP, hCP, hP⟩ := Registry.poincare_annulus_zero_outer d
  exact ⟨CP, hCP, fun s hs hsR ↦ hP U (fun y ↦ u y - v y) (fun y ↦ Gu y - Gv y) x R s hU
    (hu.sub hv) hR hK hs hsR (hvu'.mono fun y hy ↦ by simp [hy])⟩

/-- The error terms, all of the form `∫_{B_R \ B_{s_k}} g` with `∫_{B_R} g < ∞`, tend to `0`. -/
theorem tendsto_errors (hR : 0 < R) {Gu Gv : E d → E d} {CP : ℝ}
    (hGu : MemLp Gu 2 (volume.restrict (ball x R)))
    (hGv : MemLp Gv 2 (volume.restrict (ball x R))) :
    Tendsto (fun k ↦ annBound x R (annRad R k) L Qmax CP Gu Gv +
      ((∫⁻ y in ball x R \ ball x (annRad R k), ENNReal.ofReal (‖Gu y‖ ^ 2)) +
        ∫⁻ _ in ball x R \ ball x (annRad R k), ENNReal.ofReal (Qmax ^ 2))) atTop (𝓝 0) := by
  have hconst : ∀ a : ℝ, ∫⁻ _ in ball x R, ENNReal.ofReal a ≠ ⊤ := fun a ↦ by
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have h3 : ∫⁻ y in ball x R, ENNReal.ofReal (3 * ‖Gv y‖ ^ 2) ≠ ⊤ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_norm_sq_ne_top hGv)
  have t1 := tendsto_lintegral_annulus hR (hconst (annConst L Qmax))
  have t2 := tendsto_lintegral_annulus hR h3
  have t3 := ENNReal.Tendsto.const_mul
    (tendsto_lintegral_annulus hR (lintegral_norm_sq_ne_top (hGu.sub hGv)))
    (a := ENNReal.ofReal (6 * GMTFoundations.cutoffConst ^ 2 * CP)) (Or.inr ENNReal.ofReal_ne_top)
  have t4 := tendsto_lintegral_annulus hR (lintegral_norm_sq_ne_top hGu)
  have t5 := tendsto_lintegral_annulus hR (hconst (Qmax ^ 2))
  simp only [mul_zero] at t3
  have := ((t1.add t2).add t3).add (t4.add t5)
  simp only [add_zero] at this
  simpa only [annBound, Pi.sub_apply] using this

/-- **Lemma 2.12, Step 1 (downward case), on one ball.** -/
theorem energyJ_le_of_down (D : StabData U x R t u Q un Qn Un L Qmax) {Gu : E d → E d}
    (hu : MemH1Loc U u Gu) {v : E d → ℝ} {Gv : E d → E d} (hv : MemH1Loc U v Gv)
    (hvu : ∀ᵐ y ∂(volume.restrict U), v y ≤ u y)
    (hvu' : ∀ᵐ y ∂(volume.restrict (U \ ball x R)), v y = u y)
    (hmin : ∀ n, ∀ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc (Un n) w Gw →
      (∀ᵐ y ∂(volume.restrict (Un n)), w y ≤ un n y) →
      (∀ᵐ y ∂(volume.restrict (Un n \ ball x R)), w y = un n y) →
      energyJ (ball x R) (Qn n) (un n) (∇ (un n)) ≤ energyJ (ball x R) (Qn n) w Gw) :
    energyJ (ball x R) Q u Gu ≤ energyJ (ball x R) Q v Gv := by
  have hR := D.pos
  have hK : closedBall x R ⊆ U := D.closedBall_subset_ball.trans D.ball_subset
  obtain ⟨CP, -, hP⟩ := poincare_sub D.isOpen hR hK hu hv hvu'
  have huK := hu.2 _ hK (isCompact_closedBall x R)
  have hvK := hv.2 _ hK (isCompact_closedBall x R)
  have hr : volume.restrict (ball x R) ≤ volume.restrict (closedBall x R) :=
    Measure.restrict_mono ball_subset_closedBall le_rfl
  have hlim := tendsto_errors (L := L) (Qmax := Qmax) (CP := CP) hR (huK.2.mono_measure hr)
    (hvK.2.mono_measure hr)
  have hlim' := (tendsto_const_nhds (x := energyJ (ball x R) Q v Gv)).add hlim
  rw [add_zero] at hlim'
  refine ge_of_tendsto hlim' (Eventually.of_forall fun k ↦ ?_)
  set s := annRad R k
  have hs := half_le_annRad hR k
  have hsR := annRad_lt hR k
  have hBsR : ball x s ⊆ ball x R := ball_subset_ball hsR.le
  have hAK : ball x R \ ball x s ⊆ closedBall x R := diff_subset.trans ball_subset_closedBall
  have hstep := down_step D hu hv hvu hmin hP hs hsR
  have hA : energyJ (ball x R \ ball x s) Q u Gu ≤
      (∫⁻ y in ball x R \ ball x s, ENNReal.ofReal (‖Gu y‖ ^ 2)) +
        ∫⁻ _ in ball x R \ ball x s, ENNReal.ofReal (Qmax ^ 2) := by
    rw [energyJ_eq_add (huK.2.1.mono_measure (Measure.restrict_mono hAK le_rfl))]
    refine add_le_add le_rfl (lintegral_mono_ae ?_)
    filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_ball)] with y hy
    exact ENNReal.ofReal_le_ofReal (sq_mul_indicator_le (D.abs_Q_le (hAK hy)) _ y)
  rw [energyJ_split measurableSet_ball measurableSet_ball hBsR]
  calc energyJ (ball x s) Q u Gu + energyJ (ball x R \ ball x s) Q u Gu
      ≤ (energyJ (ball x R) Q v Gv + annBound x R s L Qmax CP Gu Gv) +
          ((∫⁻ y in ball x R \ ball x s, ENNReal.ofReal (‖Gu y‖ ^ 2)) +
            ∫⁻ _ in ball x R \ ball x s, ENNReal.ofReal (Qmax ^ 2)) := add_le_add hstep hA
    _ = _ := add_assoc _ _ _

/-- **Lemma 2.12, Step 2 (upward case), on one ball.** Unlike the paper, no inner-variational
hypothesis is needed (lattice identity instead of `1_{uₙ>0} → 1_{u>0}` in `L¹`). -/
theorem energyJ_le_of_up (D : StabData U x R t u Q un Qn Un L Qmax) {Gu : E d → E d}
    (hu : MemH1Loc U u Gu) {v : E d → ℝ} {Gv : E d → E d} (hv : MemH1Loc U v Gv)
    (hvu : ∀ᵐ y ∂(volume.restrict U), u y ≤ v y)
    (hvu' : ∀ᵐ y ∂(volume.restrict (U \ ball x R)), v y = u y)
    (hmin : ∀ n, ∀ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc (Un n) w Gw →
      (∀ᵐ y ∂(volume.restrict (Un n)), un n y ≤ w y) →
      (∀ᵐ y ∂(volume.restrict (Un n \ ball x R)), w y = un n y) →
      energyJ (ball x R) (Qn n) (un n) (∇ (un n)) ≤ energyJ (ball x R) (Qn n) w Gw) :
    energyJ (ball x R) Q u Gu ≤ energyJ (ball x R) Q v Gv := by
  have hR := D.pos
  have hK : closedBall x R ⊆ U := D.closedBall_subset_ball.trans D.ball_subset
  obtain ⟨CP, -, hP⟩ := poincare_sub D.isOpen hR hK hu hv hvu'
  have huK := hu.2 _ hK (isCompact_closedBall x R)
  have hvK := hv.2 _ hK (isCompact_closedBall x R)
  have hr : volume.restrict (ball x R) ≤ volume.restrict (closedBall x R) :=
    Measure.restrict_mono ball_subset_closedBall le_rfl
  have hlim := tendsto_errors (L := L) (Qmax := Qmax) (CP := CP) hR (huK.2.mono_measure hr)
    (hvK.2.mono_measure hr)
  have hlim' := (tendsto_const_nhds (x := energyJ (ball x R) Q v Gv)).add hlim
  rw [add_zero] at hlim'
  refine ge_of_tendsto hlim' (Eventually.of_forall fun k ↦ ?_)
  set s := annRad R k
  have hs := half_le_annRad hR k
  have hsR := annRad_lt hR k
  have hBsR : ball x s ⊆ ball x R := ball_subset_ball hsR.le
  have hAK : ball x R \ ball x s ⊆ closedBall x R := diff_subset.trans ball_subset_closedBall
  have hstep := up_step D hu hv hvu hmin hP hs hsR
  have hA : energyJ (ball x R \ ball x s) Q u Gu ≤
      (∫⁻ y in ball x R \ ball x s, ENNReal.ofReal (‖Gu y‖ ^ 2)) +
        ∫⁻ _ in ball x R \ ball x s, ENNReal.ofReal (Qmax ^ 2) := by
    rw [energyJ_eq_add (huK.2.1.mono_measure (Measure.restrict_mono hAK le_rfl))]
    refine add_le_add le_rfl (lintegral_mono_ae ?_)
    filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_ball)] with y hy
    exact ENNReal.ofReal_le_ofReal (sq_mul_indicator_le (D.abs_Q_le (hAK hy)) _ y)
  rw [energyJ_split measurableSet_ball measurableSet_ball hBsR]
  calc energyJ (ball x s) Q u Gu + energyJ (ball x R \ ball x s) Q u Gu
      ≤ (energyJ (ball x R) Q v Gv + annBound x R s L Qmax CP Gu Gv) +
          ((∫⁻ y in ball x R \ ball x s, ENNReal.ofReal (‖Gu y‖ ^ 2)) +
            ∫⁻ _ in ball x R \ ball x s, ENNReal.ofReal (Qmax ^ 2)) := add_le_add hstep hA
    _ = _ := add_assoc _ _ _

end Limit

/-! ### Lemma 2.12 -/

section Lemma211

/-- Uniformly locally Lipschitz sequences (the hypothesis (2.8) of Lemma 2.12,
in the equivalent form of uniform Lipschitz bounds on small balls). -/
def UnifLocLip (U : Set (E d)) (un : ℕ → E d → ℝ) : Prop :=
  ∀ y ∈ U, ∃ ε > 0, ball y ε ⊆ U ∧ ∃ L : ℝ≥0, ∀ n, LipschitzOnWith L (un n) (ball y ε)

theorem exists_closedBall_subset {U : Set (E d)} (hU : IsOpen U) {x : E d} {R : ℝ}
    (hR : 0 ≤ R) (hB : closedBall x R ⊆ U) : ∃ t > R, closedBall x t ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall x R).exists_cthickening_subset_open hU hB
  refine ⟨δ + R, by linarith, ?_⟩
  rw [← cthickening_closedBall hδ.le hR]
  exact hδU

namespace UnifLocLip

variable {U : Set (E d)} {un : ℕ → E d → ℝ} (h : UnifLocLip U un)
include h

theorem locallyLipschitzOn (n : ℕ) : LocallyLipschitzOn U (un n) := by
  intro y hy
  obtain ⟨ε, hε, -, L, hL⟩ := h y hy
  exact ⟨L, ball y ε, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hε), hL n⟩

theorem exists_gradient_bound {K : Set (E d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ≥0, ∀ n, ∀ y ∈ K, ‖∇ (un n) y‖ ≤ L := by
  choose ε hε _ L hL using h
  obtain ⟨T, hT⟩ := hK.elim_nhds_subcover' (fun y hy ↦ ball y (ε y (hKU hy)))
    fun y hy ↦ ball_mem_nhds y (hε y (hKU hy))
  refine ⟨T.sup fun z ↦ L z.1 (hKU z.2), fun n y hy ↦ ?_⟩
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hT hy)
  rw [GMTFoundations.norm_gradient_eq]
  refine (norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hyz) (hL _ _ n)).trans ?_
  exact_mod_cast Finset.le_sup (f := fun z : K ↦ L z.1 (hKU z.2)) hz

theorem locallyLipschitzOn_limit {u : E d → ℝ} (hconv : TendstoLocallyUniformlyOn un u atTop U) :
    LocallyLipschitzOn U u := by
  intro y hy
  obtain ⟨ε, hε, hεU, L, hL⟩ := h y hy
  refine ⟨L, ball y ε, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hε), ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  exact le_of_tendsto' ((hconv.tendsto_at (hεU ha)).dist (hconv.tendsto_at (hεU hb)))
    fun n ↦ (hL n).dist_le_mul a ha b hb

end UnifLocLip

/-- `C¹` functions on an open set are locally Lipschitz there. -/
theorem locallyLipschitzOn_of_contDiffOn {V : Set (E d)} (hV : IsOpen V) {f : E d → ℝ}
    (hf : ContDiffOn ℝ 1 f V) : LocallyLipschitzOn V f := by
  intro y hy
  obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (hV.mem_nhds hy)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- The coordinate Laplacian `coordLap` agrees with `Δ` for `C²` functions. -/
theorem coordLap_eq_laplacian {f : E d → ℝ} {y : E d} (hf : ContDiffAt ℝ 2 f y) :
    LongTime.coordLap f y = Δ f y := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [LongTime.coordLap, iteratedFDeriv_two_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp [LongTime.coordVec, EuclideanSpace.basisFun_apply]

/-- A `C²` function harmonic in the open set `V` satisfies `∫_V ∇w · ∇φ = 0` for
`φ ∈ C_c^∞(V)`. -/
theorem integral_inner_gradient_eq_zero_of_harmonic {V : Set (E d)} (hV : IsOpen V)
    {w : E d → ℝ} (hw : ContDiffOn ℝ 2 w V) (hΔ : ∀ y ∈ V, Δ w y = 0) {φ : E d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∫ x in V, inner ℝ (∇ w x) (∇ φ x) = 0 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  have hw' : ContDiffOn ℝ 1 (fderiv ℝ w) V := hw.fderiv_of_isOpen hV (by norm_num)
  have hwi : ∀ i : Fin d, ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ w y (LongTime.coordVec i)) V :=
    fun i ↦ hw'.clm_apply contDiffOn_const
  have hφi : ∀ i : Fin d, Continuous fun y ↦ fderiv ℝ φ y (LongTime.coordVec i) :=
    fun i ↦ (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφic : ∀ i : Fin d, HasCompactSupport fun y ↦ fderiv ℝ φ y (LongTime.coordVec i) :=
    fun i ↦ hφc.fderiv_apply (𝕜 := ℝ) _
  have hφiV : ∀ i : Fin d, tsupport (fun y ↦ fderiv ℝ φ y (LongTime.coordVec i)) ⊆ V :=
    fun i ↦ (tsupport_fderiv_apply_subset ℝ _).trans hφV
  simp_rw [LongTime.inner_eq_sum_fderiv_coord]
  rw [integral_finsetSum _ fun i _ ↦ integrableOn_mul_of_tsupport_subset hV
    ((hwi i).continuousOn.locallyIntegrableOn hV.measurableSet) (hφi i) (hφic i) (hφiV i)]
  -- integrate by parts in each coordinate
  have hibp : ∀ i : Fin d, ∫ x in V, fderiv ℝ w x (LongTime.coordVec i) *
      fderiv ℝ φ x (LongTime.coordVec i) = -∫ x in V, fderiv ℝ (fun y ↦ fderiv ℝ w y
        (LongTime.coordVec i)) x (LongTime.coordVec i) * φ x := fun i ↦ by
    rw [GMTFoundations.integral_fderiv_mul_eq_neg hV (locallyLipschitzOn_of_contDiffOn hV (hwi i))
      hφ1 hφc hφV, neg_neg]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, neg_eq_zero, ← integral_finsetSum]
  · refine setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ ?_
    rw [← Finset.sum_mul]
    have := coordLap_eq_laplacian (hw.contDiffAt (hV.mem_nhds hy))
    simp only [LongTime.coordLap] at this
    rw [this, hΔ y hy, zero_mul]
  · intro i _
    have hc : ContinuousOn (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ w y (LongTime.coordVec i)) x
        (LongTime.coordVec i)) V :=
      ((hwi i).continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
    exact integrableOn_mul_of_tsupport_subset hV (hc.locallyIntegrableOn hV.measurableSet)
      hφ.continuous hφc hφV

/-- **Harmonicity of the limit in its positivity set** (proof of Lemma 2.12: "It is clear from the
locally uniform convergence that `u` is harmonic in its positivity set"): weak harmonicity passes to
the limit, then Weyl's lemma (from viscosity-solution-theory v0.2.0). -/
theorem harmonic_of_tendsto {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ} {un : ℕ → E d → ℝ}
    (hunL : ∀ n, LocallyLipschitzOn U (un n)) (huL : LocallyLipschitzOn U u)
    (hconv : TendstoLocallyUniformlyOn un u atTop U)
    (hc2 : ∀ n, ContDiffOn ℝ 2 (un n) (posSet (un n) U))
    (hharm : ∀ n, ∀ y ∈ posSet (un n) U, Δ (un n) y = 0) :
    ContDiffOn ℝ 2 u (posSet u U) ∧ ∀ y ∈ posSet u U, Δ u y = 0 := by
  set W := posSet u U
  have hW : IsOpen W := huL.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hWU : W ⊆ U := fun y hy ↦ hy.1
  have hUm : MeasurableSet U := hU.measurableSet
  have hG := (Registry.memH1Loc_gradient_of_locallyLipschitzOn hW (huL.mono hWU)).1
  refine (Registry.harmonic_of_weakly_harmonic hW (huL.continuousOn.mono hWU) hG
    fun φ hφ hφc hφW ↦ ?_).imp (fun h ↦ h.of_le (by norm_cast)) id
  set K := tsupport φ
  have hKU : K ⊆ U := hφW.trans hWU
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hunif : TendstoUniformlyOn un u atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv K hKU hφc.isCompact
  have hposev : ∀ᶠ n in atTop, ∀ y ∈ K, 0 < un n y :=
    LongTime.eventually_forall_pos_of_tendstoUniformlyOn hφc.isCompact
      (huL.continuousOn.mono hKU) (fun y hy ↦ (hφW hy).2) hunif
  have hLK : tsupport (LongTime.coordLap φ) ⊆ K := LongTime.tsupport_coordLap_subset φ
  have hkey : ∀ᶠ n in atTop, ∫ x in U, un n x * LongTime.coordLap φ x = 0 := by
    filter_upwards [hposev] with n hn
    set V := posSet (un n) U
    have hV : IsOpen V := (hunL n).continuousOn.isOpen_inter_preimage hU isOpen_Ioi
    have hVU : V ⊆ U := fun y hy ↦ hy.1
    have hKV : K ⊆ V := fun y hy ↦ ⟨hKU hy, hn y hy⟩
    have h1 := LongTime.integral_inner_gradient_eq_neg hV ((hunL n).mono hVU) hφ2 hφc hKV
    rw [integral_inner_gradient_eq_zero_of_harmonic hV (hc2 n) (hharm n) hφ hφc hKV,
      zero_eq_neg] at h1
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hUm hVU fun y hy ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy.2 (hKV (hLK h))]]
    exact h1
  have hlim : Tendsto (fun n ↦ ∫ x in U, un n x * LongTime.coordLap φ x) atTop
      (𝓝 (∫ x in U, u x * LongTime.coordLap φ x)) :=
    LongTime.tendsto_setIntegral_mul_of_tendstoUniformlyOn hUm
      (LongTime.continuous_coordLap hφ2) (LongTime.hasCompactSupport_coordLap hφc)
      (hLK.trans hKU) (Eventually.of_forall fun n ↦ (hunL n).continuousOn.mono (hLK.trans hKU))
      (huL.continuousOn.mono (hLK.trans hKU)) (hunif.mono hLK)
  have hzero : ∫ x in U, u x * LongTime.coordLap φ x = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hkey.mono fun n hn ↦ hn.symm))
  rw [LongTime.integral_inner_gradient_eq_neg hW (huL.mono hWU) hφ2 hφc hφW,
    ← setIntegral_eq_of_subset_of_forall_diff_eq_zero hUm hWU fun y hy ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy.2 (hφW (hLK h))], hzero, neg_zero]

/-- The data `StabData` for a ball `B̄_R(x) ⊆ U` and a fixed domain `Uₙ = U`. -/
theorem stabData_of {U : Set (E d)} (hU : IsOpen U) {u Q : E d → ℝ} {un Qn : ℕ → E d → ℝ}
    {Qmax : ℝ} (hlip : UnifLocLip U un) (hconv : TendstoLocallyUniformlyOn un u atTop U)
    (hQc : ∀ n, ContinuousOn (Qn n) U) (hQb : ∀ n, ∀ y ∈ U, |Qn n y| ≤ Qmax)
    (hQconv : ∀ y ∈ U, Tendsto (fun n ↦ Qn n y) atTop (𝓝 (Q y))) {x : E d} {R : ℝ}
    (hR : 0 < R) (hB : closedBall x R ⊆ U) :
    ∃ t : ℝ, ∃ L : ℝ≥0, StabData U x R t u Q un Qn (fun _ ↦ U) L Qmax := by
  obtain ⟨t, hRt, htU⟩ := exists_closedBall_subset hU hR.le hB
  obtain ⟨L, hL⟩ := hlip.exists_gradient_bound (isCompact_closedBall x t) htU
  exact ⟨t, L, hU, hR, hRt, htU, fun _ ↦ hU, fun _ ↦ htU,
    fun n y hy ↦ hL n y (ball_subset_closedBall hy), hlip.locallyLipschitzOn,
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hB (isCompact_closedBall x R),
    fun n ↦ (hQc n).mono hB, fun n y hy ↦ hQb n y (hB hy), fun y hy ↦ hQconv y (hB hy)⟩

/-- **Lemma 2.12 (i)**. Let `uₙ` be uniformly locally
Lipschitz on the open set `U` ((2.8)), `uₙ → u` locally uniformly in `U`, and let `Qₙ` be
continuous on `U` with `|Qₙ| ≤ Q_max`, `Qₙ → Q` pointwise in `U` (the paper assumes locally
uniform convergence and `Q_min ≤ Qₙ ≤ Q_max`). If the `uₙ` are downward minimizers of `J_{Qₙ}` in
`U`, then `u` is a downward minimizer of `J_Q` in `U`. -/
theorem isDownwardMinimizer_of_tendsto {U : Set (E d)} (hU : IsOpen U) {u Q : E d → ℝ}
    {un Qn : ℕ → E d → ℝ} {Qmax : ℝ} (hlip : UnifLocLip U un)
    (hconv : TendstoLocallyUniformlyOn un u atTop U)
    (hQc : ∀ n, ContinuousOn (Qn n) U) (hQb : ∀ n, ∀ y ∈ U, |Qn n y| ≤ Qmax)
    (hQconv : ∀ y ∈ U, Tendsto (fun n ↦ Qn n y) atTop (𝓝 (Q y)))
    (hmin : ∀ n, IsDownwardMinimizer U (Qn n) (un n)) : IsDownwardMinimizer U Q u := by
  have huL := hlip.locallyLipschitzOn_limit hconv
  obtain ⟨hc2, hΔ⟩ := harmonic_of_tendsto hU hlip.locallyLipschitzOn huL hconv
    (fun n ↦ (hmin n).2.2.1) (fun n ↦ (hmin n).2.2.2.1)
  refine ⟨⟨_, Registry.memH1Loc_gradient_of_locallyLipschitzOn hU huL⟩,
    huL.continuousOn.isOpen_inter_preimage hU isOpen_Ioi, hc2, hΔ, ?_⟩
  intro x R hR hB Gu v Gv hGu hGv hvu hvu'
  obtain ⟨t, L, D⟩ := stabData_of hU hlip hconv hQc hQb hQconv hR hB
  exact energyJ_le_of_down D hGu hGv hvu hvu' fun n w Gw hw h1 h2 ↦
    (hmin n).2.2.2.2 x R hR hB _ w Gw (D.memH1Loc_n n) hw h1 h2

/-- **Lemma 2.12 (ii)**, without the inner-variational hypothesis (see the module docstring). -/
theorem isUpwardMinimizer_of_tendsto' {U : Set (E d)} (hU : IsOpen U) {u Q : E d → ℝ}
    {un Qn : ℕ → E d → ℝ} {Qmax : ℝ} (hlip : UnifLocLip U un)
    (hconv : TendstoLocallyUniformlyOn un u atTop U)
    (hQc : ∀ n, ContinuousOn (Qn n) U) (hQb : ∀ n, ∀ y ∈ U, |Qn n y| ≤ Qmax)
    (hQconv : ∀ y ∈ U, Tendsto (fun n ↦ Qn n y) atTop (𝓝 (Q y)))
    (hmin : ∀ n, IsUpwardMinimizer U (Qn n) (un n)) : IsUpwardMinimizer U Q u := by
  have huL := hlip.locallyLipschitzOn_limit hconv
  obtain ⟨hc2, hΔ⟩ := harmonic_of_tendsto hU hlip.locallyLipschitzOn huL hconv
    (fun n ↦ (hmin n).2.2.1) (fun n ↦ (hmin n).2.2.2.1)
  refine ⟨⟨_, Registry.memH1Loc_gradient_of_locallyLipschitzOn hU huL⟩,
    huL.continuousOn.isOpen_inter_preimage hU isOpen_Ioi, hc2, hΔ, ?_⟩
  intro x R hR hB Gu v Gv hGu hGv hvu hvu'
  obtain ⟨t, L, D⟩ := stabData_of hU hlip hconv hQc hQb hQconv hR hB
  exact energyJ_le_of_up D hGu hGv hvu hvu' fun n w Gw hw h1 h2 ↦
    (hmin n).2.2.2.2 x R hR hB _ w Gw (D.memH1Loc_n n) hw h1 h2

/-- **Lemma 2.12 (ii)**, with the paper's hypotheses: if the `uₙ`
are upward minimizers of `J_{Qₙ}` in `U` and inner variational solutions (the latter hypothesis
is not needed by our proof, `isUpwardMinimizer_of_tendsto'`), then `u` is an upward minimizer of
`J_Q` in `U`. -/
theorem isUpwardMinimizer_of_tendsto {U : Set (E d)} (hU : IsOpen U) {u Q : E d → ℝ}
    {un Qn : ℕ → E d → ℝ} {Qmax : ℝ} (hlip : UnifLocLip U un)
    (hconv : TendstoLocallyUniformlyOn un u atTop U)
    (hQc : ∀ n, ContinuousOn (Qn n) U) (hQb : ∀ n, ∀ y ∈ U, |Qn n y| ≤ Qmax)
    (hQconv : ∀ y ∈ U, Tendsto (fun n ↦ Qn n y) atTop (𝓝 (Q y)))
    (hmin : ∀ n, IsUpwardMinimizer U (Qn n) (un n)) {χn : ℕ → E d → ℝ}
    (_hinner : ∀ n, IsInnerVarSolution U (Qn n) (un n) (χn n)) : IsUpwardMinimizer U Q u :=
  isUpwardMinimizer_of_tendsto' hU hlip hconv hQc hQb hQconv hmin

end Lemma211

/-! ### Lemma 2.12 on exhausting domains (used for Corollary 2.13) -/

section Exhaust

/-- Hypotheses of Lemma 2.12 for a sequence of functions `uₙ` defined on open sets `Uₙ`
exhausting `ℝᵈ` (every compact set lies in `Uₙ` for large `n`), with uniform Lipschitz bounds on
small balls for large `n`, converging locally uniformly on `ℝᵈ`. -/
structure ExhaustData (un Qn : ℕ → E d → ℝ) (Un : ℕ → Set (E d)) (v Q : E d → ℝ) (Qmax : ℝ) :
    Prop where
  isOpen : ∀ n, IsOpen (Un n)
  exhaust : ∀ K, IsCompact K → ∀ᶠ n in atTop, K ⊆ Un n
  lip : ∀ y, ∃ ε > 0, ∃ L : ℝ≥0, ∀ᶠ n in atTop, LipschitzOnWith L (un n) (ball y ε)
  locLip : ∀ n, LocallyLipschitzOn (Un n) (un n)
  conv : TendstoLocallyUniformly un v atTop
  Qcont : ∀ n, ContinuousOn (Qn n) (Un n)
  Qbd : ∀ n, ∀ y ∈ Un n, |Qn n y| ≤ Qmax
  Qconv : ∀ y, Tendsto (fun n ↦ Qn n y) atTop (𝓝 (Q y))

namespace ExhaustData

variable {un Qn : ℕ → E d → ℝ} {Un : ℕ → Set (E d)} {v Q : E d → ℝ} {Qmax : ℝ}
  (D : ExhaustData un Qn Un v Q Qmax)
include D

theorem eventually_gradient_bound {K : Set (E d)} (hK : IsCompact K) :
    ∃ L : ℝ≥0, ∀ᶠ n in atTop, ∀ y ∈ K, ‖∇ (un n) y‖ ≤ L := by
  choose ε hε L hL using D.lip
  obtain ⟨T, hT⟩ := hK.elim_nhds_subcover (fun y ↦ ball y (ε y)) fun y _ ↦ ball_mem_nhds y (hε y)
  refine ⟨T.sup L, ?_⟩
  filter_upwards [(Filter.eventually_all_finset T).2 fun y _ ↦ hL y] with n hn y hy
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hT.2 hy)
  rw [GMTFoundations.norm_gradient_eq]
  refine (norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hyz) (hn z hz)).trans ?_
  exact_mod_cast Finset.le_sup (f := L) hz

theorem locallyLipschitz_limit : LocallyLipschitzOn univ v := by
  intro y _
  obtain ⟨ε, hε, L, hL⟩ := D.lip y
  refine ⟨L, ball y ε, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hε), ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  have hc := TendstoLocallyUniformly.tendstoLocallyUniformlyOn (s := univ) D.conv
  exact le_of_tendsto ((hc.tendsto_at (mem_univ a)).dist (hc.tendsto_at (mem_univ b)))
    (hL.mono fun n hn ↦ hn.dist_le_mul a ha b hb)

theorem tendstoUniformlyOn_shift {K : Set (E d)} (hK : IsCompact K) (N : ℕ) :
    TendstoUniformlyOn (fun k ↦ un (k + N)) v atTop K :=
  LongTime.TendstoUniformlyOn.comp_seq
    (tendstoLocallyUniformly_iff_forall_isCompact.1 D.conv K hK) (tendsto_add_atTop_nat N)

/-- The data `StabData` on a ball, after discarding finitely many terms. -/
theorem exists_stabData {x : E d} {R : ℝ} (hR : 0 < R) : ∃ (t : ℝ) (L : ℝ≥0) (N : ℕ),
    StabData univ x R t v Q (fun k ↦ un (k + N)) (fun k ↦ Qn (k + N)) (fun k ↦ Un (k + N))
      L Qmax ∧ ∀ k, closedBall x R ⊆ Un (k + N) := by
  obtain ⟨L, hL⟩ := D.eventually_gradient_bound (isCompact_closedBall x (R + 1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hL.and (D.exhaust _ (isCompact_closedBall x (R + 1))))
  have hsub : ∀ k, closedBall x (R + 1) ⊆ Un (k + N) := fun k ↦ (hN _ (by omega)).2
  have hRsub : ∀ k, closedBall x R ⊆ Un (k + N) := fun k ↦
    (closedBall_subset_closedBall (by linarith)).trans (hsub k)
  refine ⟨R + 1, L, N, ⟨isOpen_univ, hR, by linarith, subset_univ _, fun k ↦ D.isOpen _, hsub,
    fun k y hy ↦ (hN _ (by omega)).1 y (ball_subset_closedBall hy), fun k ↦ D.locLip _,
    D.tendstoUniformlyOn_shift (isCompact_closedBall x R) N,
    fun k ↦ (D.Qcont _).mono (hRsub k), fun k y hy ↦ D.Qbd _ y (hRsub k hy),
    fun y _ ↦ (D.Qconv y).comp (tendsto_add_atTop_nat N)⟩, hRsub⟩

/-- Harmonicity of the limit in its positivity set, on exhausting domains. -/
theorem harmonic (hc2 : ∀ n, ContDiffOn ℝ 2 (un n) (posSet (un n) (Un n)))
    (hharm : ∀ n, ∀ y ∈ posSet (un n) (Un n), Δ (un n) y = 0) :
    ContDiffOn ℝ 2 v (posSet v univ) ∧ ∀ y ∈ posSet v univ, Δ v y = 0 := by
  have hloc : ∀ y, ContDiffOn ℝ 2 v (posSet v (ball y 1)) ∧
      ∀ z ∈ posSet v (ball y 1), Δ v z = 0 := by
    intro y
    obtain ⟨N, hN⟩ := eventually_atTop.1 (D.exhaust _ (isCompact_closedBall y 1))
    have hsub : ∀ k, ball y 1 ⊆ Un (k + N) := fun k ↦
      ball_subset_closedBall.trans (hN _ (by omega))
    have hpos : ∀ k, posSet (un (k + N)) (ball y 1) ⊆ posSet (un (k + N)) (Un (k + N)) :=
      fun k z hz ↦ ⟨hsub k hz.1, hz.2⟩
    refine harmonic_of_tendsto isOpen_ball (un := fun k ↦ un (k + N))
      (fun k ↦ (D.locLip _).mono (hsub k)) (D.locallyLipschitz_limit.mono (subset_univ _))
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).2 fun K _ hK ↦
        D.tendstoUniformlyOn_shift hK N)
      (fun k ↦ (hc2 _).mono (hpos k)) fun k z hz ↦ hharm _ z (hpos k hz)
  have hset : ∀ y, posSet v univ ∩ ball y 1 = posSet v (ball y 1) := fun y ↦ by
    ext z; simp only [posSet, mem_inter_iff, mem_setOf_eq, mem_univ, true_and]; tauto
  refine ⟨contDiffOn_of_locally_contDiffOn fun y _ ↦ ⟨ball y 1, isOpen_ball,
    mem_ball_self one_pos, by rw [hset]; exact (hloc y).1⟩, fun y hy ↦ ?_⟩
  exact (hloc y).2 y ⟨mem_ball_self one_pos, hy.2⟩

end ExhaustData

/-- **Lemma 2.12 (i) on exhausting domains.** -/
theorem isDownwardMinimizer_of_exhaust {un Qn : ℕ → E d → ℝ} {Un : ℕ → Set (E d)}
    {v Q : E d → ℝ} {Qmax : ℝ} (D : ExhaustData un Qn Un v Q Qmax)
    (hmin : ∀ n, IsDownwardMinimizer (Un n) (Qn n) (un n)) : IsDownwardMinimizer univ Q v := by
  obtain ⟨hc2, hΔ⟩ := D.harmonic (fun n ↦ (hmin n).2.2.1) fun n ↦ (hmin n).2.2.2.1
  have hvL := D.locallyLipschitz_limit
  refine ⟨⟨_, Registry.memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ hvL⟩,
    hvL.continuousOn.isOpen_inter_preimage isOpen_univ isOpen_Ioi, hc2, hΔ, ?_⟩
  intro x R hR _ Gu w Gw hGu hGw hwu hwu'
  obtain ⟨t, L, N, S, hRsub⟩ := D.exists_stabData (x := x) hR
  exact energyJ_le_of_down S hGu hGw hwu hwu' fun k w' Gw' hw' h1 h2 ↦
    (hmin (k + N)).2.2.2.2 x R hR (hRsub k) _ w' Gw' (S.memH1Loc_n k) hw' h1 h2

/-- **Lemma 2.12 (ii) on exhausting domains** (no inner-variational hypothesis needed). -/
theorem isUpwardMinimizer_of_exhaust {un Qn : ℕ → E d → ℝ} {Un : ℕ → Set (E d)}
    {v Q : E d → ℝ} {Qmax : ℝ} (D : ExhaustData un Qn Un v Q Qmax)
    (hmin : ∀ n, IsUpwardMinimizer (Un n) (Qn n) (un n)) : IsUpwardMinimizer univ Q v := by
  obtain ⟨hc2, hΔ⟩ := D.harmonic (fun n ↦ (hmin n).2.2.1) fun n ↦ (hmin n).2.2.2.1
  have hvL := D.locallyLipschitz_limit
  refine ⟨⟨_, Registry.memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ hvL⟩,
    hvL.continuousOn.isOpen_inter_preimage isOpen_univ isOpen_Ioi, hc2, hΔ, ?_⟩
  intro x R hR _ Gu w Gw hGu hGw hwu hwu'
  obtain ⟨t, L, N, S, hRsub⟩ := D.exists_stabData (x := x) hR
  exact energyJ_le_of_up S hGu hGw hwu hwu' fun k w' Gw' hw' h1 h2 ↦
    (hmin (k + N)).2.2.2.2 x R hR (hRsub k) _ w' Gw' (S.memH1Loc_n k) hw' h1 h2

end Exhaust

end DirectionalStable

end PerronVariational

end
