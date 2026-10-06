/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.DirectionalStable.Basic
public import GMTFoundations.Sobolev.Cutoff
import GMTFoundations.Sobolev.Lattice
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Main.Directional

/-!
# Stability of directional minimality: the estimate for fixed `s`

Part of the proof of **Lemma 2.12** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: the energy
estimate on one ball `B_R(x)` for a fixed inner radius `s < R`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal NNReal

@[expose] public section

namespace PerronVariational

namespace DirectionalStable

variable {d : ℕ}

/-! ### Lemma 2.12, downward case: the estimate for fixed `s` -/

section DownStep

variable {U : Set (E d)} {x : E d} {R t : ℝ} {u Q : E d → ℝ} {un Qn : ℕ → E d → ℝ}
  {Un : ℕ → Set (E d)} {L : ℝ≥0} {Qmax : ℝ}

theorem sq_mul_indicator_le {q Qmax : ℝ} (hq : |q| ≤ Qmax) (S : Set (E d)) (y : E d) :
    q ^ 2 * S.indicator (1 : E d → ℝ) y ≤ Qmax ^ 2 := by
  have hi : S.indicator (1 : E d → ℝ) y ≤ 1 := indicator_le_self' (fun _ _ ↦ zero_le_one) y
  have hi0 : 0 ≤ S.indicator (1 : E d → ℝ) y := indicator_nonneg (fun _ _ ↦ zero_le_one) y
  have hQ2 : q ^ 2 ≤ Qmax ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hq 2
  nlinarith [sq_nonneg q]

/-- The constant of the annulus estimate. -/
noncomputable def annConst (L : ℝ≥0) (Qmax : ℝ) : ℝ := 12 * (L : ℝ) ^ 2 + Qmax ^ 2 + 6

theorem annConst_nonneg (L : ℝ≥0) (Qmax : ℝ) : 0 ≤ annConst L Qmax := by
  unfold annConst; positivity

/-- The right-hand side of the annulus estimate on `B_R(x) \ B_s(x)`. -/
noncomputable def annBound (x : E d) (R s : ℝ) (L : ℝ≥0) (Qmax CP : ℝ) (Gu Gv : E d → E d) :
    ℝ≥0∞ :=
  (∫⁻ _ in ball x R \ ball x s, ENNReal.ofReal (annConst L Qmax)) +
    (∫⁻ y in ball x R \ ball x s, ENNReal.ofReal (3 * ‖Gv y‖ ^ 2)) +
      ENNReal.ofReal (6 * GMTFoundations.cutoffConst ^ 2 * CP) *
        ∫⁻ y in ball x R \ ball x s, ENNReal.ofReal (‖Gu y - Gv y‖ ^ 2)

theorem gradient_eq_zero_of_eqOn_ball {φ : E d → ℝ} {s : ℝ}
    (hφ1 : ∀ y ∈ closedBall x s, φ y = 1) {y : E d} (hy : y ∈ ball x s) : ∇ φ y = 0 := by
  have : φ =ᶠ[𝓝 y] fun _ ↦ (1 : ℝ) := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact hφ1 z (ball_subset_closedBall hz)
  simp [gradient, this.fderiv_eq]

/-- **Lemma 2.12, Step 1, for fixed `s`.** With the data `D`, a downward competitor `v` of `u`
in `B_R(x)`, and downward minimality of `uₙ` in `B_R(x)`, for `R/2 ≤ s < R`:
`J_Q(u; B_s) ≤ J_Q(v; B_R) + annBound`. -/
theorem down_step (D : StabData U x R t u Q un Qn Un L Qmax) {Gu : E d → E d}
    (hu : MemH1Loc U u Gu) {v : E d → ℝ} {Gv : E d → E d} (hv : MemH1Loc U v Gv)
    (hvu : ∀ᵐ y ∂(volume.restrict U), v y ≤ u y)
    (hmin : ∀ n, ∀ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc (Un n) w Gw →
      (∀ᵐ y ∂(volume.restrict (Un n)), w y ≤ un n y) →
      (∀ᵐ y ∂(volume.restrict (Un n \ ball x R)), w y = un n y) →
      energyJ (ball x R) (Qn n) (un n) (∇ (un n)) ≤ energyJ (ball x R) (Qn n) w Gw)
    {CP : ℝ} (hP : ∀ s, R / 2 ≤ s → s < R →
      ∫⁻ y in ball x R \ ball x s, ENNReal.ofReal ((u y - v y) ^ 2) ≤
        ENNReal.ofReal (CP * (R - s) ^ 2) *
          ∫⁻ y in ball x R \ ball x s, ENNReal.ofReal (‖Gu y - Gv y‖ ^ 2))
    {s : ℝ} (hs : R / 2 ≤ s) (hsR : s < R) :
    energyJ (ball x s) Q u Gu ≤ energyJ (ball x R) Q v Gv + annBound x R s L Qmax CP Gu Gv := by
  classical
  have hR := D.pos
  have hs0 : 0 ≤ s := by linarith
  obtain ⟨φ, hφ, hφ01, hφ1, hφ0, -, -, hφg⟩ := GMTFoundations.exists_cutoff x hs0 hsR
  set c := GMTFoundations.cutoffConst with hc
  have hcpos : 0 < c := GMTFoundations.cutoffConst_pos
  set A := ball x R \ ball x s with hA
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have hBsR : ball x s ⊆ ball x R := ball_subset_ball hsR.le
  have hBs_cl : ball x s ⊆ closedBall x R := hBsR.trans ball_subset_closedBall
  have hBs_t : ball x s ⊆ ball x t := hBs_cl.trans D.closedBall_subset_ball
  have hA_t : A ⊆ ball x t :=
    Set.sdiff_subset.trans (ball_subset_closedBall.trans D.closedBall_subset_ball)
  have hφg0 : ∀ y ∈ ball x s, ∇ φ y = 0 := fun y hy ↦ gradient_eq_zero_of_eqOn_ball hφ1 hy
  have hvt := memH1Loc_mono hv D.ball_subset
  have hK : closedBall x R ⊆ U := D.closedBall_subset_ball.trans D.ball_subset
  have huK := hu.2 _ hK (isCompact_closedBall x R)
  have hvK := hv.2 _ hK (isCompact_closedBall x R)
  have hAK : A ⊆ closedBall x R := Set.sdiff_subset.trans ball_subset_closedBall
  have hrA : volume.restrict A ≤ volume.restrict (closedBall x R) :=
    Measure.restrict_mono hAK le_rfl
  have hrBs : volume.restrict (ball x s) ≤ volume.restrict (closedBall x R) :=
    Measure.restrict_mono hBs_cl le_rfl
  -- the sequences
  set mn : ℕ → E d → ℝ := fun n y ↦ v y + max (un n y - v y) 0 with hmn_def
  set Gmn : ℕ → E d → E d := fun n y ↦
    Gv y + {y | 0 < un n y - v y}.indicator (fun y ↦ ∇ (un n) y - Gv y) y with hGmn_def
  have hmn : ∀ n, MemH1Loc (ball x t) (mn n) (Gmn n) := fun n ↦
    hvt.add (memH1Loc_posPart isOpen_ball ((D.memH1Loc_ball n).sub hvt))
  -- (ii) minimality and the lattice identity
  have hstep : ∀ n, energyJ (ball x s) (Qn n) (mn n) (Gmn n) ≤
      energyJ (ball x s) (Qn n) v Gv +
        energyJ A (Qn n) (downComp (un n) v φ) (downCompGrad (un n) v φ Gv) := by
    intro n
    have hmin_n := hmin n _ _ (downComp_memH1Loc D hv hφ hφ0 n)
      (Eventually.of_forall fun y ↦ by
        have := mul_nonneg (hφ01 y).1 (le_max_right (un n y - v y) 0)
        simp only [downComp]; linarith)
      ((ae_restrict_mem ((D.isOpen_n n).measurableSet.diff measurableSet_ball)).mono
        fun y hy ↦ by simp [downComp, (hφ0 y hy.2).1])
    rw [energyJ_split measurableSet_ball measurableSet_ball hBsR,
      energyJ_split measurableSet_ball measurableSet_ball hBsR] at hmin_n
    -- the lattice identity on `B_s`
    have hlat : energyJ (ball x s) (Qn n) (mn n) (Gmn n) +
        energyJ (ball x s) (Qn n) (downComp (un n) v φ) (downCompGrad (un n) v φ Gv) ≤
          energyJ (ball x s) (Qn n) (un n) (∇ (un n)) + energyJ (ball x s) (Qn n) v Gv := by
      refine energyJ_add_le_of_swap measurableSet_ball (fun y hy ↦ ?_) ?_
      · have hφy : φ y = 1 := hφ1 y (ball_subset_closedBall hy)
        have hgy := hφg0 y hy
        by_cases hlt : 0 < un n y - v y
        · left
          have hmax : max (un n y - v y) 0 = un n y - v y := max_eq_left hlt.le
          have hin : y ∈ {y | 0 < un n y - v y} := hlt
          simp only [hmn_def, hGmn_def, downComp, downCompGrad, hmax, hφy, hgy,
            indicator_of_mem hin, one_smul, smul_zero, add_zero, one_mul]
          refine ⟨by ring, by abel, by ring, by abel⟩
        · right
          have hmax : max (un n y - v y) 0 = 0 := max_eq_right (not_lt.1 hlt)
          have hin : y ∉ {y | 0 < un n y - v y} := hlt
          simp only [hmn_def, hGmn_def, downComp, downCompGrad, hmax, hφy, hgy,
            indicator_of_notMem hin, smul_zero, add_zero, mul_zero, sub_zero]
          exact ⟨trivial, trivial, trivial, trivial⟩
      · have hopen : IsOpen (posSet (un n) (ball x s)) :=
          ((D.continuousOn_n n).mono hBs_t).isOpen_inter_preimage isOpen_ball isOpen_Ioi
        exact ENNReal.measurable_ofReal.comp_aemeasurable
          ((GMTFoundations.measurable_gradient _).norm.pow_const 2 |>.aemeasurable |>.add
            ((((D.Qcont n).mono hBs_cl).aemeasurable measurableSet_ball).pow_const 2 |>.mul
              (measurable_const.indicator hopen.measurableSet).aemeasurable))
    -- finiteness of `J_{Qₙ}(uₙ; B_s)`
    have hfin : energyJ (ball x s) (Qn n) (un n) (∇ (un n)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _ in ball x s, ENNReal.ofReal ((L : ℝ) ^ 2 + Qmax ^ 2))
        ?_ (lintegral_mono_ae ?_)
      · rw [setLIntegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
      · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        refine ENNReal.ofReal_le_ofReal (add_le_add ?_ ?_)
        · exact pow_le_pow_left₀ (norm_nonneg _) (D.norm_gradient_le n (hBs_t hy)) 2
        · have hQ := D.Qbd n y (hBs_cl hy)
          have hi : (posSet (un n) (ball x s)).indicator (1 : E d → ℝ) y ≤ 1 :=
            indicator_le_self' (fun _ _ ↦ zero_le_one) y
          have hi0 : 0 ≤ (posSet (un n) (ball x s)).indicator (1 : E d → ℝ) y :=
            indicator_nonneg (fun _ _ ↦ zero_le_one) y
          have hQ2 : Qn n y ^ 2 ≤ Qmax ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hQ 2
          nlinarith [sq_nonneg (Qn n y)]
    refine ENNReal.le_of_add_le_add_right hfin ?_
    calc energyJ (ball x s) (Qn n) (mn n) (Gmn n) + energyJ (ball x s) (Qn n) (un n) (∇ (un n))
        ≤ energyJ (ball x s) (Qn n) (mn n) (Gmn n) +
            (energyJ (ball x s) (Qn n) (un n) (∇ (un n)) + energyJ A (Qn n) (un n) (∇ (un n))) :=
          by gcongr; exact le_self_add
      _ ≤ energyJ (ball x s) (Qn n) (mn n) (Gmn n) +
            (energyJ (ball x s) (Qn n) (downComp (un n) v φ) (downCompGrad (un n) v φ Gv) +
              energyJ A (Qn n) (downComp (un n) v φ) (downCompGrad (un n) v φ Gv)) := by
          gcongr
      _ = (energyJ (ball x s) (Qn n) (mn n) (Gmn n) +
            energyJ (ball x s) (Qn n) (downComp (un n) v φ) (downCompGrad (un n) v φ Gv)) +
              energyJ A (Qn n) (downComp (un n) v φ) (downCompGrad (un n) v φ Gv) :=
          (add_assoc _ _ _).symm
      _ ≤ (energyJ (ball x s) (Qn n) (un n) (∇ (un n)) + energyJ (ball x s) (Qn n) v Gv) +
              energyJ A (Qn n) (downComp (un n) v φ) (downCompGrad (un n) v φ Gv) := by
          gcongr
      _ = _ := by ring
  -- (v) the annulus
  have hann : ∀ᶠ n in atTop,
      energyJ A (Qn n) (downComp (un n) v φ) (downCompGrad (un n) v φ Gv) ≤
        annBound x R s L Qmax CP Gu Gv := by
    set M := c / (R - s) with hM
    have hRs : 0 < R - s := by linarith
    have hM0 : 0 ≤ M := div_nonneg hcpos.le hRs.le
    have hδ : 0 < (R - s) / c := div_pos hRs hcpos
    have hMδ : M * ((R - s) / c) = 1 := by rw [hM]; field_simp
    have hvuA : ∀ᵐ y ∂(volume.restrict A), v y ≤ u y :=
      ae_restrict_of_ae_restrict_of_subset (hAK.trans hK) hvu
    filter_upwards [D.eventually_abs_sub_le hδ] with n hn
    have hGvA : AEStronglyMeasurable Gv (volume.restrict A) :=
      hvK.2.aestronglyMeasurable.mono_measure hrA
    have hhA : AEMeasurable (fun y ↦ u y - v y) (volume.restrict A) :=
      (huK.1.aestronglyMeasurable.mono_measure hrA).aemeasurable.sub
        (hvK.1.aestronglyMeasurable.mono_measure hrA).aemeasurable
    refine (energyJ_le_of_pointwise hGvA hhA (annConst_nonneg L Qmax)
      (by positivity : (0 : ℝ) ≤ 6 * M ^ 2) ?_).trans ?_
    · filter_upwards [ae_restrict_mem hAm, hvuA] with y hy hyvu
      have hyt := hA_t hy
      have hz0 : 0 ≤ max (un n y - v y) 0 := le_max_right _ _
      have hN := norm_comp_grad_le (a := ∇ (un n) y) (b := Gv y)
        (c := {y | 0 < un n y - v y}.indicator (fun y ↦ ∇ (un n) y - Gv y) y) (p := ∇ φ y)
        (e := downCompGrad (un n) v φ Gv y) (hφ01 y).1 (hφ01 y).2 hz0
        ((norm_indicator_le_norm_self _ _).trans (norm_sub_le _ _)) (Or.inl rfl)
      have hp : max (un n y - v y) 0 * ‖∇ φ y‖ ≤ max (un n y - v y) 0 * M :=
        mul_le_mul_of_nonneg_left (hφg y) hz0
      have hzw : max (un n y - v y) 0 ≤ (u y - v y) + (R - s) / c := by
        have h1 := hn y (hAK hy)
        rw [abs_le] at h1
        exact max_le (by linarith) (by linarith)
      have hq : Qn n y ^ 2 * (posSet (downComp (un n) v φ) A).indicator 1 y ≤ Qmax ^ 2 := by
        have hQ := D.Qbd n y (hAK hy)
        have hi : (posSet (downComp (un n) v φ) A).indicator (1 : E d → ℝ) y ≤ 1 :=
          indicator_le_self' (fun _ _ ↦ zero_le_one) y
        have hi0 : 0 ≤ (posSet (downComp (un n) v φ) A).indicator (1 : E d → ℝ) y :=
          indicator_nonneg (fun _ _ ↦ zero_le_one) y
        have hQ2 : Qn n y ^ 2 ≤ Qmax ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hQ 2
        nlinarith [sq_nonneg (Qn n y)]
      exact annulus_real_bound (norm_nonneg _) (hN.trans (by linarith)) (norm_nonneg _)
        (D.norm_gradient_le n hyt) hz0 hM0 hzw hMδ.le hq
    · unfold annBound
      refine add_le_add le_rfl ?_
      calc ENNReal.ofReal (6 * M ^ 2) *
            ∫⁻ y in A, ENNReal.ofReal ((u y - v y) ^ 2)
          ≤ ENNReal.ofReal (6 * M ^ 2) * (ENNReal.ofReal (CP * (R - s) ^ 2) *
              ∫⁻ y in A, ENNReal.ofReal (‖Gu y - Gv y‖ ^ 2)) := by
            gcongr; exact hP s hs hsR
        _ = _ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            rw [hM, hc]; field_simp
  -- (iii) convergence of `J_{Qₙ}(v; B_s)`
  have hvlim : Tendsto (fun n ↦ energyJ (ball x s) (Qn n) v Gv) atTop
      (𝓝 (energyJ (ball x s) Q v Gv)) := by
    have hGvBs : AEStronglyMeasurable Gv (volume.restrict (ball x s)) :=
      hvK.2.aestronglyMeasurable.mono_measure hrBs
    simp_rw [energyJ_eq_add hGvBs]
    refine tendsto_const_nhds.add (tendsto_lintegral_of_dominated_convergence'
      (fun _ ↦ ENNReal.ofReal (Qmax ^ 2)) (fun n ↦ ?_) (fun n ↦ ?_) ?_ ?_)
    · have hsv : NullMeasurableSet (posSet v (ball x s)) (volume.restrict (ball x s)) :=
        measurableSet_ball.nullMeasurableSet.inter
          ((hvK.1.aestronglyMeasurable.mono_measure hrBs).aemeasurable.nullMeasurable
            measurableSet_Ioi)
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        (((((D.Qcont n).mono hBs_cl).aemeasurable measurableSet_ball).pow_const 2).mul
          (aemeasurable_const.indicator₀ hsv))
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact ENNReal.ofReal_le_ofReal (sq_mul_indicator_le (D.Qbd n y (hBs_cl hy)) _ y)
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (((D.Qconv y (hBs_cl hy)).pow 2).mul_const _)
  -- (i) lower semicontinuity
  have hlsc : energyJ (ball x s) Q u Gu ≤
      liminf (fun n ↦ energyJ (ball x s) (Qn n) (mn n) (Gmn n)) atTop := by
    have hcl_t : closedBall x s ⊆ ball x t :=
      (closedBall_subset_closedBall hsR.le).trans D.closedBall_subset_ball
    have hr : volume.restrict (ball x s) ≤ volume.restrict (closedBall x s) :=
      Measure.restrict_mono ball_subset_closedBall le_rfl
    have hvuBs : ∀ᵐ y ∂(volume.restrict (ball x s)), v y ≤ u y :=
      ae_restrict_of_ae_restrict_of_subset (hBs_t.trans D.ball_subset) hvu
    have hvm : AEMeasurable v (volume.restrict (ball x s)) :=
      (hvK.1.aestronglyMeasurable.mono_measure hrBs).aemeasurable
    have hmn_eq : ∀ n y, mn n y = max (un n y) (v y) := by
      intro n y
      simp only [hmn_def]
      rcases le_total (un n y) (v y) with h | h
      · rw [max_eq_right (by linarith : un n y - v y ≤ 0), max_eq_right h, add_zero]
      · rw [max_eq_left (by linarith : 0 ≤ un n y - v y), max_eq_left h]; ring
    refine energyJ_le_liminf isOpen_ball measure_ball_lt_top.ne
      (fun n ↦ hasWeakGradient_mono (hmn n).1 hBs_t)
      (fun n ↦ ((hmn n).2 _ hcl_t (isCompact_closedBall _ _)).2.mono_measure hr)
      (hasWeakGradient_mono hu.1 (hBs_t.trans D.ball_subset))
      (huK.2.aestronglyMeasurable.mono_measure hrBs)
      (fun δ hδ ↦ ?_) (fun n ↦ ?_)
      (fun n ↦ ((D.Qcont n).mono hBs_cl).aemeasurable measurableSet_ball)
      (fun y hy ↦ D.Qconv y (hBs_cl hy)) ?_
    · filter_upwards [D.eventually_abs_sub_le hδ] with n hn
      filter_upwards [ae_restrict_mem measurableSet_ball, hvuBs] with y hy hyv
      rw [hmn_eq, ← max_eq_left hyv]
      exact (abs_max_sub_max_le_abs _ _ _).trans (hn y (hBs_cl hy))
    · exact hvm.add ((((D.continuousOn_n n).mono hBs_t).aemeasurable measurableSet_ball).sub
        hvm |>.max aemeasurable_const)
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy hu0
      filter_upwards [D.eventually_pos (hBs_cl hy) hu0] with n hn
      rw [hmn_eq]
      exact hn.trans_le (le_max_left _ _)
  -- conclusion
  have hvs : energyJ (ball x s) Q v Gv ≤ energyJ (ball x R) Q v Gv := by
    rw [energyJ_split measurableSet_ball measurableSet_ball hBsR Q v Gv]
    exact le_self_add
  calc energyJ (ball x s) Q u Gu
      ≤ liminf (fun n ↦ energyJ (ball x s) (Qn n) (mn n) (Gmn n)) atTop := hlsc
    _ ≤ liminf (fun n ↦ energyJ (ball x s) (Qn n) v Gv + annBound x R s L Qmax CP Gu Gv)
          atTop := by
        refine liminf_le_liminf ?_
        filter_upwards [hann] with n hn
        exact (hstep n).trans (by gcongr)
    _ = energyJ (ball x s) Q v Gv + annBound x R s L Qmax CP Gu Gv :=
        (hvlim.add tendsto_const_nhds).liminf_eq
    _ ≤ energyJ (ball x R) Q v Gv + annBound x R s L Qmax CP Gu Gv := by gcongr

/-- **Lemma 2.12, Step 2, for fixed `s`.** With the data `D`, an upward competitor `v` of `u`
in `B_R(x)`, and upward minimality of `uₙ` in `B_R(x)`, for `R/2 ≤ s < R`:
`J_Q(u; B_s) ≤ J_Q(v; B_R) + annBound`. -/
theorem up_step (D : StabData U x R t u Q un Qn Un L Qmax) {Gu : E d → E d}
    (hu : MemH1Loc U u Gu) {v : E d → ℝ} {Gv : E d → E d} (hv : MemH1Loc U v Gv)
    (hvu : ∀ᵐ y ∂(volume.restrict U), u y ≤ v y)
    (hmin : ∀ n, ∀ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc (Un n) w Gw →
      (∀ᵐ y ∂(volume.restrict (Un n)), un n y ≤ w y) →
      (∀ᵐ y ∂(volume.restrict (Un n \ ball x R)), w y = un n y) →
      energyJ (ball x R) (Qn n) (un n) (∇ (un n)) ≤ energyJ (ball x R) (Qn n) w Gw)
    {CP : ℝ} (hP : ∀ s, R / 2 ≤ s → s < R →
      ∫⁻ y in ball x R \ ball x s, ENNReal.ofReal ((u y - v y) ^ 2) ≤
        ENNReal.ofReal (CP * (R - s) ^ 2) *
          ∫⁻ y in ball x R \ ball x s, ENNReal.ofReal (‖Gu y - Gv y‖ ^ 2))
    {s : ℝ} (hs : R / 2 ≤ s) (hsR : s < R) :
    energyJ (ball x s) Q u Gu ≤ energyJ (ball x R) Q v Gv + annBound x R s L Qmax CP Gu Gv := by
  classical
  have hR := D.pos
  have hs0 : 0 ≤ s := by linarith
  obtain ⟨φ, hφ, hφ01, hφ1, hφ0, -, -, hφg⟩ := GMTFoundations.exists_cutoff x hs0 hsR
  set c := GMTFoundations.cutoffConst with hc
  have hcpos : 0 < c := GMTFoundations.cutoffConst_pos
  set A := ball x R \ ball x s with hA
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have hBsR : ball x s ⊆ ball x R := ball_subset_ball hsR.le
  have hBs_cl : ball x s ⊆ closedBall x R := hBsR.trans ball_subset_closedBall
  have hBs_t : ball x s ⊆ ball x t := hBs_cl.trans D.closedBall_subset_ball
  have hA_t : A ⊆ ball x t :=
    Set.sdiff_subset.trans (ball_subset_closedBall.trans D.closedBall_subset_ball)
  have hφg0 : ∀ y ∈ ball x s, ∇ φ y = 0 := fun y hy ↦ gradient_eq_zero_of_eqOn_ball hφ1 hy
  have hvt := memH1Loc_mono hv D.ball_subset
  have hK : closedBall x R ⊆ U := D.closedBall_subset_ball.trans D.ball_subset
  have huK := hu.2 _ hK (isCompact_closedBall x R)
  have hvK := hv.2 _ hK (isCompact_closedBall x R)
  have hAK : A ⊆ closedBall x R := Set.sdiff_subset.trans ball_subset_closedBall
  have hrA : volume.restrict A ≤ volume.restrict (closedBall x R) :=
    Measure.restrict_mono hAK le_rfl
  have hrBs : volume.restrict (ball x s) ≤ volume.restrict (closedBall x R) :=
    Measure.restrict_mono hBs_cl le_rfl
  -- the sequences
  set mn : ℕ → E d → ℝ := fun n y ↦ v y - max (v y - un n y) 0 with hmn_def
  set Gmn : ℕ → E d → E d := fun n y ↦
    Gv y - {y | 0 < v y - un n y}.indicator (fun y ↦ Gv y - ∇ (un n) y) y with hGmn_def
  have hmn : ∀ n, MemH1Loc (ball x t) (mn n) (Gmn n) := fun n ↦
    hvt.sub (memH1Loc_posPart isOpen_ball (hvt.sub (D.memH1Loc_ball n)))
  -- (ii) minimality and the lattice identity
  have hstep : ∀ n, energyJ (ball x s) (Qn n) (mn n) (Gmn n) ≤
      energyJ (ball x s) (Qn n) v Gv +
        energyJ A (Qn n) (upComp (un n) v φ) (upCompGrad (un n) v φ Gv) := by
    intro n
    have hmin_n := hmin n _ _ (upComp_memH1Loc D hv hφ hφ0 n)
      (Eventually.of_forall fun y ↦ by
        have := mul_nonneg (hφ01 y).1 (le_max_right (v y - un n y) 0)
        simp only [upComp]; linarith)
      ((ae_restrict_mem ((D.isOpen_n n).measurableSet.diff measurableSet_ball)).mono
        fun y hy ↦ by simp [upComp, (hφ0 y hy.2).1])
    rw [energyJ_split measurableSet_ball measurableSet_ball hBsR,
      energyJ_split measurableSet_ball measurableSet_ball hBsR] at hmin_n
    -- the lattice identity on `B_s`
    have hlat : energyJ (ball x s) (Qn n) (mn n) (Gmn n) +
        energyJ (ball x s) (Qn n) (upComp (un n) v φ) (upCompGrad (un n) v φ Gv) ≤
          energyJ (ball x s) (Qn n) (un n) (∇ (un n)) + energyJ (ball x s) (Qn n) v Gv := by
      refine energyJ_add_le_of_swap measurableSet_ball (fun y hy ↦ ?_) ?_
      · have hφy : φ y = 1 := hφ1 y (ball_subset_closedBall hy)
        have hgy := hφg0 y hy
        by_cases hlt : 0 < v y - un n y
        · left
          have hmax : max (v y - un n y) 0 = v y - un n y := max_eq_left hlt.le
          have hin : y ∈ {y | 0 < v y - un n y} := hlt
          simp only [hmn_def, hGmn_def, upComp, upCompGrad, hmax, hφy, hgy,
            indicator_of_mem hin, one_smul, smul_zero, add_zero, one_mul]
          refine ⟨by ring, by abel, by ring, by abel⟩
        · right
          have hmax : max (v y - un n y) 0 = 0 := max_eq_right (not_lt.1 hlt)
          have hin : y ∉ {y | 0 < v y - un n y} := hlt
          simp only [hmn_def, hGmn_def, upComp, upCompGrad, hmax, hφy, hgy,
            indicator_of_notMem hin, smul_zero, add_zero, mul_zero, sub_zero]
          exact ⟨trivial, trivial, trivial, trivial⟩
      · have hopen : IsOpen (posSet (un n) (ball x s)) :=
          ((D.continuousOn_n n).mono hBs_t).isOpen_inter_preimage isOpen_ball isOpen_Ioi
        exact ENNReal.measurable_ofReal.comp_aemeasurable
          ((GMTFoundations.measurable_gradient _).norm.pow_const 2 |>.aemeasurable |>.add
            ((((D.Qcont n).mono hBs_cl).aemeasurable measurableSet_ball).pow_const 2 |>.mul
              (measurable_const.indicator hopen.measurableSet).aemeasurable))
    -- finiteness of `J_{Qₙ}(uₙ; B_s)`
    have hfin : energyJ (ball x s) (Qn n) (un n) (∇ (un n)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _ in ball x s, ENNReal.ofReal ((L : ℝ) ^ 2 + Qmax ^ 2))
        ?_ (lintegral_mono_ae ?_)
      · rw [setLIntegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
      · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        refine ENNReal.ofReal_le_ofReal (add_le_add ?_ ?_)
        · exact pow_le_pow_left₀ (norm_nonneg _) (D.norm_gradient_le n (hBs_t hy)) 2
        · have hQ := D.Qbd n y (hBs_cl hy)
          have hi : (posSet (un n) (ball x s)).indicator (1 : E d → ℝ) y ≤ 1 :=
            indicator_le_self' (fun _ _ ↦ zero_le_one) y
          have hi0 : 0 ≤ (posSet (un n) (ball x s)).indicator (1 : E d → ℝ) y :=
            indicator_nonneg (fun _ _ ↦ zero_le_one) y
          have hQ2 : Qn n y ^ 2 ≤ Qmax ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hQ 2
          nlinarith [sq_nonneg (Qn n y)]
    refine ENNReal.le_of_add_le_add_right hfin ?_
    calc energyJ (ball x s) (Qn n) (mn n) (Gmn n) + energyJ (ball x s) (Qn n) (un n) (∇ (un n))
        ≤ energyJ (ball x s) (Qn n) (mn n) (Gmn n) +
            (energyJ (ball x s) (Qn n) (un n) (∇ (un n)) + energyJ A (Qn n) (un n) (∇ (un n))) :=
          by gcongr; exact le_self_add
      _ ≤ energyJ (ball x s) (Qn n) (mn n) (Gmn n) +
            (energyJ (ball x s) (Qn n) (upComp (un n) v φ) (upCompGrad (un n) v φ Gv) +
              energyJ A (Qn n) (upComp (un n) v φ) (upCompGrad (un n) v φ Gv)) := by
          gcongr
      _ = (energyJ (ball x s) (Qn n) (mn n) (Gmn n) +
            energyJ (ball x s) (Qn n) (upComp (un n) v φ) (upCompGrad (un n) v φ Gv)) +
              energyJ A (Qn n) (upComp (un n) v φ) (upCompGrad (un n) v φ Gv) :=
          (add_assoc _ _ _).symm
      _ ≤ (energyJ (ball x s) (Qn n) (un n) (∇ (un n)) + energyJ (ball x s) (Qn n) v Gv) +
              energyJ A (Qn n) (upComp (un n) v φ) (upCompGrad (un n) v φ Gv) := by
          gcongr
      _ = _ := by ring
  -- (v) the annulus
  have hann : ∀ᶠ n in atTop,
      energyJ A (Qn n) (upComp (un n) v φ) (upCompGrad (un n) v φ Gv) ≤
        annBound x R s L Qmax CP Gu Gv := by
    set M := c / (R - s) with hM
    have hRs : 0 < R - s := by linarith
    have hM0 : 0 ≤ M := div_nonneg hcpos.le hRs.le
    have hδ : 0 < (R - s) / c := div_pos hRs hcpos
    have hMδ : M * ((R - s) / c) = 1 := by rw [hM]; field_simp
    have hvuA : ∀ᵐ y ∂(volume.restrict A), u y ≤ v y :=
      ae_restrict_of_ae_restrict_of_subset (hAK.trans hK) hvu
    filter_upwards [D.eventually_abs_sub_le hδ] with n hn
    have hGvA : AEStronglyMeasurable Gv (volume.restrict A) :=
      hvK.2.aestronglyMeasurable.mono_measure hrA
    have hhA : AEMeasurable (fun y ↦ u y - v y) (volume.restrict A) :=
      (huK.1.aestronglyMeasurable.mono_measure hrA).aemeasurable.sub
        (hvK.1.aestronglyMeasurable.mono_measure hrA).aemeasurable
    refine (energyJ_le_of_pointwise hGvA hhA (annConst_nonneg L Qmax)
      (by positivity : (0 : ℝ) ≤ 6 * M ^ 2) ?_).trans ?_
    · filter_upwards [ae_restrict_mem hAm, hvuA] with y hy hyvu
      have hyt := hA_t hy
      have hz0 : 0 ≤ max (v y - un n y) 0 := le_max_right _ _
      have hN := norm_comp_grad_le (a := ∇ (un n) y) (b := Gv y)
        (c := {y | 0 < v y - un n y}.indicator (fun y ↦ Gv y - ∇ (un n) y) y) (p := ∇ φ y)
        (e := upCompGrad (un n) v φ Gv y) (hφ01 y).1 (hφ01 y).2 hz0
        ((norm_indicator_le_norm_self _ _).trans ((norm_sub_le _ _).trans_eq (add_comm _ _)))
        (Or.inr rfl)
      have hp : max (v y - un n y) 0 * ‖∇ φ y‖ ≤ max (v y - un n y) 0 * M :=
        mul_le_mul_of_nonneg_left (hφg y) hz0
      have hzw : max (v y - un n y) 0 ≤ (v y - u y) + (R - s) / c := by
        have h1 := hn y (hAK hy)
        rw [abs_le] at h1
        exact max_le (by linarith) (by linarith)
      have hq : Qn n y ^ 2 * (posSet (upComp (un n) v φ) A).indicator 1 y ≤ Qmax ^ 2 := by
        have hQ := D.Qbd n y (hAK hy)
        have hi : (posSet (upComp (un n) v φ) A).indicator (1 : E d → ℝ) y ≤ 1 :=
          indicator_le_self' (fun _ _ ↦ zero_le_one) y
        have hi0 : 0 ≤ (posSet (upComp (un n) v φ) A).indicator (1 : E d → ℝ) y :=
          indicator_nonneg (fun _ _ ↦ zero_le_one) y
        have hQ2 : Qn n y ^ 2 ≤ Qmax ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hQ 2
        nlinarith [sq_nonneg (Qn n y)]
      have hb := annulus_real_bound (N := ‖upCompGrad (un n) v φ Gv y‖) (a := ‖∇ (un n) y‖)
        (g := ‖Gv y‖) (L := L) (norm_nonneg _) (hN.trans (by linarith)) (norm_nonneg _)
        (D.norm_gradient_le n hyt) hz0 hM0 hzw hMδ.le hq
      refine hb.trans_eq ?_
      unfold annConst; ring
    · unfold annBound
      refine add_le_add le_rfl ?_
      calc ENNReal.ofReal (6 * M ^ 2) *
            ∫⁻ y in A, ENNReal.ofReal ((u y - v y) ^ 2)
          ≤ ENNReal.ofReal (6 * M ^ 2) * (ENNReal.ofReal (CP * (R - s) ^ 2) *
              ∫⁻ y in A, ENNReal.ofReal (‖Gu y - Gv y‖ ^ 2)) := by
            gcongr; exact hP s hs hsR
        _ = _ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            rw [hM, hc]; field_simp
  -- (iii) convergence of `J_{Qₙ}(v; B_s)`
  have hvlim : Tendsto (fun n ↦ energyJ (ball x s) (Qn n) v Gv) atTop
      (𝓝 (energyJ (ball x s) Q v Gv)) := by
    have hGvBs : AEStronglyMeasurable Gv (volume.restrict (ball x s)) :=
      hvK.2.aestronglyMeasurable.mono_measure hrBs
    simp_rw [energyJ_eq_add hGvBs]
    refine tendsto_const_nhds.add (tendsto_lintegral_of_dominated_convergence'
      (fun _ ↦ ENNReal.ofReal (Qmax ^ 2)) (fun n ↦ ?_) (fun n ↦ ?_) ?_ ?_)
    · have hsv : NullMeasurableSet (posSet v (ball x s)) (volume.restrict (ball x s)) :=
        measurableSet_ball.nullMeasurableSet.inter
          ((hvK.1.aestronglyMeasurable.mono_measure hrBs).aemeasurable.nullMeasurable
            measurableSet_Ioi)
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        (((((D.Qcont n).mono hBs_cl).aemeasurable measurableSet_ball).pow_const 2).mul
          (aemeasurable_const.indicator₀ hsv))
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact ENNReal.ofReal_le_ofReal (sq_mul_indicator_le (D.Qbd n y (hBs_cl hy)) _ y)
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (((D.Qconv y (hBs_cl hy)).pow 2).mul_const _)
  -- (i) lower semicontinuity
  have hlsc : energyJ (ball x s) Q u Gu ≤
      liminf (fun n ↦ energyJ (ball x s) (Qn n) (mn n) (Gmn n)) atTop := by
    have hcl_t : closedBall x s ⊆ ball x t :=
      (closedBall_subset_closedBall hsR.le).trans D.closedBall_subset_ball
    have hr : volume.restrict (ball x s) ≤ volume.restrict (closedBall x s) :=
      Measure.restrict_mono ball_subset_closedBall le_rfl
    have hvuBs : ∀ᵐ y ∂(volume.restrict (ball x s)), u y ≤ v y :=
      ae_restrict_of_ae_restrict_of_subset (hBs_t.trans D.ball_subset) hvu
    have hvm : AEMeasurable v (volume.restrict (ball x s)) :=
      (hvK.1.aestronglyMeasurable.mono_measure hrBs).aemeasurable
    have hmn_eq : ∀ n y, mn n y = min (un n y) (v y) := by
      intro n y
      simp only [hmn_def]
      rcases le_total (un n y) (v y) with h | h
      · rw [max_eq_left (by linarith : 0 ≤ v y - un n y), min_eq_left h]; ring
      · rw [max_eq_right (by linarith : v y - un n y ≤ 0), min_eq_right h, sub_zero]
    refine energyJ_le_liminf isOpen_ball measure_ball_lt_top.ne
      (fun n ↦ hasWeakGradient_mono (hmn n).1 hBs_t)
      (fun n ↦ ((hmn n).2 _ hcl_t (isCompact_closedBall _ _)).2.mono_measure hr)
      (hasWeakGradient_mono hu.1 (hBs_t.trans D.ball_subset))
      (huK.2.aestronglyMeasurable.mono_measure hrBs)
      (fun δ hδ ↦ ?_) (fun n ↦ ?_)
      (fun n ↦ ((D.Qcont n).mono hBs_cl).aemeasurable measurableSet_ball)
      (fun y hy ↦ D.Qconv y (hBs_cl hy)) ?_
    · filter_upwards [D.eventually_abs_sub_le hδ] with n hn
      filter_upwards [ae_restrict_mem measurableSet_ball, hvuBs] with y hy hyv
      rw [hmn_eq, ← min_eq_left hyv]
      refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (hn y (hBs_cl hy)) ?_)
      rw [sub_self, abs_zero]; exact hδ.le
    · exact hvm.sub ((hvm.sub
        (((D.continuousOn_n n).mono hBs_t).aemeasurable measurableSet_ball)).max
          aemeasurable_const)
    · filter_upwards [ae_restrict_mem measurableSet_ball, hvuBs] with y hy hyv hu0
      filter_upwards [D.eventually_pos (hBs_cl hy) hu0] with n hn
      rw [hmn_eq]
      exact lt_min hn (hu0.trans_le hyv)
  -- conclusion
  have hvs : energyJ (ball x s) Q v Gv ≤ energyJ (ball x R) Q v Gv := by
    rw [energyJ_split measurableSet_ball measurableSet_ball hBsR Q v Gv]
    exact le_self_add
  calc energyJ (ball x s) Q u Gu
      ≤ liminf (fun n ↦ energyJ (ball x s) (Qn n) (mn n) (Gmn n)) atTop := hlsc
    _ ≤ liminf (fun n ↦ energyJ (ball x s) (Qn n) v Gv + annBound x R s L Qmax CP Gu Gv)
          atTop := by
        refine liminf_le_liminf ?_
        filter_upwards [hann] with n hn
        exact (hstep n).trans (by gcongr)
    _ = energyJ (ball x s) Q v Gv + annBound x R s L Qmax CP Gu Gv :=
        (hvlim.add tendsto_const_nhds).liminf_eq
    _ ≤ energyJ (ball x R) Q v Gv + annBound x R s L Qmax CP Gu Gv := by gcongr

end DownStep

end DirectionalStable

end PerronVariational

end
