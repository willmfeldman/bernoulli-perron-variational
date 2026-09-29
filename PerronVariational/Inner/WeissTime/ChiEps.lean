/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.SemilinearEstimates
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Inner.ChiCompact
import PerronVariational.Inner.ChiConverge
import PerronVariational.Inner.ReactionBound
import PerronVariational.Inner.WeakGrad
import PerronVariational.Inner.WeissTime.Translation
import PerronVariational.Semilinear.Profiles

/-!
# Lemma 4.3: temporal translations of `χ_ε`

**Lemma 4.3** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: the temporal
translation estimate `chiEps_time_translation` and the compactness statement
`exists_tendstoLpLoc_chiEps_subseq`. The translation estimate is the paper's localization of the
argument of G. S. Weiss, *A singular limit arising in combustion theory: fine properties of the
free boundary*, Calc. Var. Partial Differential Equations 17 (2003), 311–340,
doi:10.1007/s00526-002-0171-z, Proposition 4.1.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-! ### Lemma 4.3: temporal translations of `χ_ε` -/

section ChiEps

variable {β : ℝ → ℝ}

set_option maxHeartbeats 1000000 in
-- long assembly proof with many compact sets, constants and estimates
/-- **Temporal translation estimate for `χ_ε`** (proof of Lemma 4.3, (4.8)–(4.10)): uniformly in `n`
(large), `∫_A |χ_n(x, t + s) - χ_n(x, t)|` is small for small `s`. Uses the time derivative of the
mollified energy density `e_n = |∇v_n|² + Q² χ_n`, the spatial estimate, and the strong convergence
of `∇v_n` (Lemma 4.2). -/
theorem chiEps_time_translation (S : Setting d) (hβ : IsReactionProfile β)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) {g : ℕ → E d → ℝ}
    {G : ℕ → E d → E d} {v : ℕ → E d × ℝ → ℝ} {u : E d × ℝ → ℝ} {M : ℝ} {E0 : ℝ≥0∞}
    (hE0 : E0 ≠ ⊤) (hv : ∀ n, IsSemilinearSolution S.U S.Q β (ε n) (g n) (v n))
    (hg : ∀ n, MemH1 S.U (g n) (G n)) (hgE : ∀ n, energyBound S (G n) ≤ E0)
    (hgM : ∀ n, ∀ x ∈ S.U, 0 ≤ g n x ∧ g n x ≤ M)
    (_hconv : TendstoLocallyUniformlyOn v u atTop (UInf S.U))
    (hgrad : TendstoLpLoc 2 volume (UInf S.U) (fun n ↦ gradₓ (v n)) (gradₓ u) atTop)
    (hucont : ContinuousOn u (UInf S.U)) (hulip : LocLipₓ (UInf S.U) u) :
    ∃ N : ℕ, ∀ A ⊆ UInf S.U, IsCompact A → ∀ η > 0, ∃ ρ > 0, ∀ n ≥ N, ∀ s : ℝ, |s| < ρ →
      ∫⁻ p in A, ‖chiEps β (ε n) (v n) (p + (0, s)) - chiEps β (ε n) (v n) p‖ₑ ≤
        ENNReal.ofReal η := by
  classical
  have hΩ : IsOpen (UInf S.U) := S.isOpen.prod isOpen_Ioi
  obtain ⟨KQ, hKQ⟩ := S.lip
  have hQc : ContinuousOn S.Q S.U := hKQ.continuousOn.mono subset_closure
  have hsol : ∀ n, IsSemilinearSolOn S.U S.Q β (ε n) (Ioi 0) (v n) := fun n ↦ (hv n).2.1
  obtain ⟨C, ε₁, hε₁, hLip⟩ := semilinear_interiorLipEst S hβ
  obtain ⟨N₁, hN₁⟩ := chiEps_space_translation S hβ hε hε0 hE0 hv hg hgE hgM
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hε0.eventually (gt_mem_nhds (lt_min hε₁ one_pos)))
  set N := max N₀ N₁ with hNdef
  refine ⟨N, time_translation_of_nonneg hΩ ?_⟩
  intro A hA hAc η hη
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun n _ s _ _ ↦ by simp⟩
  obtain ⟨K₁, hK₁c, hK₁U, T₁, T₂, hT₁, hT₁₂, hAB⟩ := exists_box hA hAc hne
  suffices H : ∃ ρ > 0, ∀ n ≥ N, ∀ s : ℝ, 0 ≤ s → s < ρ →
      ∫⁻ p in K₁ ×ˢ Icc T₁ T₂, ‖chiEps β (ε n) (v n) (p + (0, s)) - chiEps β (ε n) (v n) p‖ₑ ≤
        ENNReal.ofReal η by
    obtain ⟨ρ, hρ, h⟩ := H
    exact ⟨ρ, hρ, fun n hn s hs hsρ ↦ (lintegral_mono_set hAB).trans (h n hn s hs hsρ)⟩
  -- geometry
  obtain ⟨r, hr, hrU⟩ := hK₁c.exists_cthickening_subset_open S.isOpen hK₁U
  set K₂ := cthickening r K₁ with hK₂def
  have hK₂c : IsCompact K₂ := hK₁c.cthickening
  have hK₁m : MeasurableSet K₁ := hK₁c.isClosed.measurableSet
  set B := K₁ ×ˢ Icc T₁ T₂ with hBdef
  set B' := K₁ ×ˢ Icc T₁ (T₂ + 1) with hB'def
  set Kb := K₂ ×ˢ Icc (T₁ / 2) (T₂ + 2) with hKbdef
  have hBm : MeasurableSet B := hK₁m.prod measurableSet_Icc
  have hB'm : MeasurableSet B' := hK₁m.prod measurableSet_Icc
  have hB'c : IsCompact B' := hK₁c.prod isCompact_Icc
  have hKbc : IsCompact Kb := hK₂c.prod isCompact_Icc
  have hKbm : MeasurableSet Kb := hKbc.isClosed.measurableSet
  have hKbΩ : Kb ⊆ UInf S.U := prod_mono hrU fun t ht ↦
    (by positivity : (0 : ℝ) < T₁ / 2).trans_le ht.1
  have hB'Kb : B' ⊆ Kb := prod_mono (self_subset_cthickening _) fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hB'Ω : B' ⊆ UInf S.U := hB'Kb.trans hKbΩ
  have hBB' : B ⊆ B' := prod_mono le_rfl fun t ht ↦ ⟨ht.1, by linarith [ht.2]⟩
  set r₀ := min r (min (T₁ / 2) 1) with hr₀def
  have hr₀ : 0 < r₀ := by positivity
  have hnear : ∀ p ∈ B', ∀ w : E d × ℝ, ‖w‖ < r₀ → p + w ∈ Kb := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩ w hw
    have h1 : ‖w.1‖ < r₀ := (norm_fst_le w).trans_lt hw
    have h2 : |w.2| < r₀ := by
      have := (norm_snd_le w).trans_lt hw
      rwa [Real.norm_eq_abs] at this
    have hr₀r : r₀ ≤ r := min_le_left _ _
    have hr₀T : r₀ ≤ T₁ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hr₀1 : r₀ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    have h2' := abs_lt.1 h2
    refine ⟨mem_cthickening_of_dist_le _ x r K₁ hx ?_, ?_, ?_⟩
    · simp only [Prod.fst_add, dist_eq_norm, add_sub_cancel_left]
      linarith
    · simp only [Prod.snd_add]
      linarith [ht.1]
    · simp only [Prod.snd_add]
      linarith [ht.2]
  have hnearE : ∀ᶠ w in 𝓝 (0 : E d × ℝ), ∀ p ∈ B', p + w ∈ Kb := by
    filter_upwards [ball_mem_nhds (0 : E d × ℝ) hr₀] with w hw p hp
    exact hnear p hp w (mem_ball_zero_iff.1 hw)
  -- thresholds and the gradient bound
  have hεN : ∀ n ≥ N, ε n < ε₁ ∧ ε n < 1 := fun n hn ↦ by
    have := hN₀ n ((le_max_left _ _).trans hn)
    exact ⟨this.trans_le (min_le_left _ _), this.trans_le (min_le_right _ _)⟩
  obtain ⟨L, hL⟩ := exists_bound_gradₓ_of_interiorLipEst S.isOpen C (max M 1) hKbc hKbΩ
  set L' := max L 0 with hL'def
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hLn : ∀ n ≥ N, ∀ q ∈ Kb, ‖gradₓ (v n) q‖ ≤ L' := fun n hn q hq ↦
    (hL (v n) (hLip (ε n) ⟨hε n, (hεN n hn).1⟩ M (g n) (v n) (hv n) (hgM n))
      (fun t ht ↦ ((hv n).2.1.2.1 t ht).differentiableOn (by norm_num))
      (fun q hq ↦ by
        have h := semilinear_nonneg_le_max S hβ (hε n) (hv n) (hgM n) q
          ⟨subset_closure hq.1, mem_Ici.2 (le_of_lt hq.2)⟩
        rw [abs_of_nonneg h.1]
        exact h.2.trans (max_le_max le_rfl (hεN n hn).2.le)) q hq).trans (le_max_left _ _)
  -- the energy density
  set Fn : ℕ → E d × ℝ → ℝ := fun n p ↦ ‖gradₓ (v n) p‖ ^ 2 with hFndef
  set e : ℕ → E d × ℝ → ℝ := fun n p ↦
    ‖gradₓ (v n) p‖ ^ 2 + S.Q p.1 ^ 2 * chiEps β (ε n) (v n) p with hedef
  have hBc : ∀ e', Continuous (bigBEps β e') := fun e' ↦
    continuous_iff_continuousAt.2 fun z ↦ (hβ.hasDerivAt_bigBEps e' z).continuousAt
  have hχc : ∀ n, ContinuousOn (chiEps β (ε n) (v n)) (UInf S.U) := fun n ↦
    continuousOn_const.mul ((hBc _).comp_continuousOn (hv n).2.1.1)
  have hgc : ∀ n, ContinuousOn (gradₓ (v n)) (UInf S.U) := fun n ↦ (hsol n).2.2.1
  have hQ2c : ContinuousOn (fun p : E d × ℝ ↦ S.Q p.1 ^ 2) (UInf S.U) :=
    (hQc.comp continuousOn_fst fun p hp ↦ hp.1).pow 2
  have hec : ∀ n, ContinuousOn (e n) (UInf S.U) := fun n ↦
    ((hgc n).norm.pow 2).add (hQ2c.mul (hχc n))
  have hFc : ∀ n, ContinuousOn (Fn n) (UInf S.U) := fun n ↦ (hgc n).norm.pow 2
  -- constants
  set m := S.Qmin ^ 2 with hmdef
  have hm : 0 < m := by have := S.Qmin_pos; positivity
  set η₁ := η * m / 4 with hη₁def
  have hη₁ : 0 < η₁ := by positivity
  set Qm := S.Qmax ^ 2 with hQmdef
  have hQm : 0 ≤ Qm := sq_nonneg _
  have hQmem : ∀ x ∈ S.U, 0 ≤ S.Q x ^ 2 ∧ m ≤ S.Q x ^ 2 ∧ S.Q x ^ 2 ≤ Qm := by
    intro x hx
    have h := S.Q_mem x (subset_closure hx)
    have h0 := S.Qmin_pos
    refine ⟨sq_nonneg _, pow_le_pow_left₀ h0.le h.1 2, pow_le_pow_left₀ (h0.le.trans h.1) h.2 2⟩
  -- translations of `|∇v_n|²`, of `Q²` and of `χ_n`
  have hgi := locallyIntegrableOn_gradₓ hΩ hucont hulip
  have hgradL1 := tendstoLpLoc_one_of_two hgc hgi hgrad
  have hFtr := eventually_translation_normSq hΩ hgc hgi hgradL1 hB'Ω hB'c hnearE hB'Kb
    (N := N) hLn (η := η₁ / 3) (div_pos hη₁ three_pos)
  have hQtr := eventually_lintegral_translate_le hΩ hQ2c hB'Ω hB'c (η := η₁ / 3)
    (div_pos hη₁ three_pos)
  obtain ⟨ρχ, hρχ, hχtr⟩ := hN₁ B' hB'Ω hB'c (η₁ / (3 * (Qm + 1)))
    (div_pos hη₁ (mul_pos three_pos (add_pos_of_nonneg_of_pos hQm one_pos)))
  obtain ⟨ρs, hρs, hρsP⟩ := Metric.eventually_nhds_iff.1 (hFtr.and (hQtr.and hnearE))
  obtain ⟨k, hk⟩ := (LongTime.tendsto_bumpRad.eventually
    (gt_mem_nhds (lt_min (lt_min hρs hρχ) hr₀))).exists
  set δ := LongTime.bumpRad k with hδdef
  have hδ0 : 0 < δ := LongTime.bumpRad_pos k
  have hδs : δ < ρs := hk.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδχ : δ < ρχ := hk.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδr₀ : δ < r₀ := hk.trans_le (min_le_right _ _)
  have hδr : δ ≤ r := hδr₀.le.trans (min_le_left _ _)
  have hnorm : ∀ y : E d, ‖((y, 0) : E d × ℝ)‖ = ‖y‖ := fun y ↦ by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  -- spatial translations of the energy density on `B'`
  have hesp : ∀ n ≥ N, ∀ y ∈ closedBall (0 : E d) δ,
      ∫⁻ p in B', ‖e n (p + (y, 0)) - e n p‖ₑ ≤ ENNReal.ofReal η₁ := by
    intro n hn y hy
    have hy' : ‖y‖ ≤ δ := by rwa [mem_closedBall_zero_iff] at hy
    obtain ⟨hF, hQ, hnear'⟩ := hρsP (y := ((y, 0) : E d × ℝ))
      (by rw [dist_zero_right, hnorm]; linarith)
    have hχ := hχtr n (le_max_right _ _ |>.trans hn) y (by linarith)
    have hmaps : ∀ p ∈ B', p + ((y, 0) : E d × ℝ) ∈ UInf S.U := fun p hp ↦ hKbΩ (hnear' p hp)
    have hpt : ∀ p ∈ B', ‖e n (p + (y, 0)) - e n p‖ₑ ≤
        ‖Fn n (p + (y, 0)) - Fn n p‖ₑ + ‖S.Q (p + ((y, 0) : E d × ℝ)).1 ^ 2 - S.Q p.1 ^ 2‖ₑ +
          ENNReal.ofReal Qm *
            ‖chiEps β (ε n) (v n) (p + (y, 0)) - chiEps β (ε n) (v n) p‖ₑ := by
      intro p hp
      have hc := chiEps_mem_Icc hβ (hε n) (v n) (p + (y, 0))
      have hq := hQmem p.1 (hK₁U hp.1)
      have h := abs_energy_sub_le (F₁ := Fn n (p + (y, 0))) (F₂ := Fn n p)
        (q₁ := S.Q (p + ((y, 0) : E d × ℝ)).1 ^ 2) (c₂ := chiEps β (ε n) (v n) p) hc.1 hc.2
        hq.1 hq.2.2
      simp only [Real.enorm_eq_ofReal_abs]
      rw [← ENNReal.ofReal_mul hQm, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
        ← ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (abs_nonneg _))
          (mul_nonneg hQm (abs_nonneg _))]
      exact ENNReal.ofReal_le_ofReal h
    have hm1 : AEMeasurable (fun p ↦ ‖Fn n (p + (y, 0)) - Fn n p‖ₑ) (volume.restrict B') :=
      (((hFc n).comp (continuous_add_const _).continuousOn hmaps).sub
        ((hFc n).mono hB'Ω)).enorm.aemeasurable hB'm
    have hm2 : AEMeasurable (fun p : E d × ℝ ↦
        ‖S.Q (p + ((y, 0) : E d × ℝ)).1 ^ 2 - S.Q p.1 ^ 2‖ₑ) (volume.restrict B') :=
      ((hQ2c.comp (continuous_add_const _).continuousOn hmaps).sub
        (hQ2c.mono hB'Ω)).enorm.aemeasurable hB'm
    calc ∫⁻ p in B', ‖e n (p + (y, 0)) - e n p‖ₑ
        ≤ ∫⁻ p in B', (‖Fn n (p + (y, 0)) - Fn n p‖ₑ +
            ‖S.Q (p + ((y, 0) : E d × ℝ)).1 ^ 2 - S.Q p.1 ^ 2‖ₑ + ENNReal.ofReal Qm *
            ‖chiEps β (ε n) (v n) (p + (y, 0)) - chiEps β (ε n) (v n) p‖ₑ) :=
          setLIntegral_mono' hB'm hpt
      _ = (∫⁻ p in B', ‖Fn n (p + (y, 0)) - Fn n p‖ₑ) +
            (∫⁻ p in B', ‖S.Q (p + ((y, 0) : E d × ℝ)).1 ^ 2 - S.Q p.1 ^ 2‖ₑ) +
            ENNReal.ofReal Qm * ∫⁻ p in B',
              ‖chiEps β (ε n) (v n) (p + (y, 0)) - chiEps β (ε n) (v n) p‖ₑ := by
          rw [lintegral_add_left' (hm1.add hm2), lintegral_add_left' hm1,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (η₁ / 3) + ENNReal.ofReal (η₁ / 3) +
            ENNReal.ofReal Qm * ENNReal.ofReal (η₁ / (3 * (Qm + 1))) := by
          gcongr
          exact hF n hn
      _ ≤ ENNReal.ofReal η₁ := by
          have h3Q : 0 < 3 * (Qm + 1) := mul_pos three_pos (add_pos_of_nonneg_of_pos hQm one_pos)
          have hη3 : 0 ≤ η₁ / 3 := (div_pos hη₁ three_pos).le
          rw [← ENNReal.ofReal_mul hQm, ← ENNReal.ofReal_add hη3 hη3,
            ← ENNReal.ofReal_add (add_nonneg hη3 hη3) (mul_nonneg hQm (div_pos hη₁ h3Q).le)]
          refine ENNReal.ofReal_le_ofReal ?_
          have : Qm * (η₁ / (3 * (Qm + 1))) ≤ η₁ / 3 := by
            rw [mul_div_assoc', div_le_div_iff₀ h3Q (by norm_num)]
            nlinarith
          linarith
  -- the mollified energy density
  set mt : ℕ → E d × ℝ → ℝ := fun n p ↦ ∫ z, e n (z, p.2) * LongTime.mollAt k p.1 z
    with hmtdef
  have hmoll : ∀ n ≥ N, ∫⁻ p in B', ‖e n p - mt n p‖ₑ ≤ ENNReal.ofReal η₁ := fun n hn ↦
    lintegral_sub_mollify_le (hec n) hB'm (fun p hp y hy ↦ hKbΩ (hnear p hp _ (by
      rw [hnorm]
      rw [mem_closedBall_zero_iff] at hy
      linarith))) (hesp n hn)
  set et : ℕ → E d × ℝ → ℝ := fun n ↦ Kb.indicator (e n) with hetdef
  have hetm : ∀ n, Measurable (et n) := fun n ↦ by
    change Measurable (Kb.indicator (e n))
    rw [← piecewise_eq_indicator]
    exact ContinuousOn.measurable_piecewise ((hec n).mono hKbΩ) continuousOn_const hKbm
  set mm : ℕ → E d × ℝ → ℝ := fun n p ↦ ∫ z, et n (z, p.2) * LongTime.mollAt k p.1 z
    with hmmdef
  have hmmm : ∀ n, Measurable (mm n) := fun n ↦
    (stronglyMeasurable_mollify (hetm n) k).measurable
  have hmm_eq : ∀ n, ∀ p ∈ B', mm n p = mt n p := by
    intro n p hp
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    by_cases hz : z ∈ closedBall p.1 δ
    · have hzK : (z, p.2) ∈ Kb := ⟨(closedBall_subset_cthickening hp.1 δ).trans
        (cthickening_mono hδr _) hz, by linarith [hp.2.1], by linarith [hp.2.2]⟩
      simp only [hetdef, indicator_of_mem hzK]
    · simp [LongTime.mollAt_eq_zero hz]
  -- time translations of the mollified density
  obtain ⟨Cψ, hCψ⟩ := exists_bound_mollAt' (d := d) k
  have hCψ0 : 0 ≤ Cψ := (abs_nonneg _).trans (hCψ 0 0).1
  set K₃ := K₂ ×ˢ Icc T₁ (T₂ + 1) with hK₃def
  have hK₃c : IsCompact K₃ := hK₂c.prod isCompact_Icc
  set Dr : ℝ := E0.toReal / 2 + (volume K₃).toReal with hDrdef
  have hDr : 0 ≤ Dr :=
    add_nonneg (div_nonneg ENNReal.toReal_nonneg zero_le_two) ENNReal.toReal_nonneg
  have hD : ∀ n, ∫⁻ q in K₃, (ENNReal.ofReal (dₜ (v n) q ^ 2) + 1) ≤ ENNReal.ofReal Dr := by
    intro n
    have hdis := semilinear_dissipation S hβ (hε n) (hg n) (hv n) (T₂ + 1) (by linarith)
    have hsub : K₃ ⊆ S.U ×ˢ Ioc 0 (T₂ + 1) := prod_mono hrU fun t ht ↦ ⟨hT₁.trans_le ht.1, ht.2⟩
    have h1 : ∫⁻ q in K₃, ENNReal.ofReal (dₜ (v n) q ^ 2) ≤ E0 / 2 :=
      (lintegral_mono_set hsub).trans (le_add_self.trans (hdis.trans
        (ENNReal.div_le_div_right (hgE n) 2)))
    rw [lintegral_add_right _ measurable_const, setLIntegral_const, one_mul, hDrdef,
      ENNReal.ofReal_add (div_nonneg ENNReal.toReal_nonneg zero_le_two) ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hK₃c.measure_lt_top.ne, ENNReal.ofReal_div_of_pos two_pos,
      ENNReal.ofReal_toReal hE0, ENNReal.ofReal_ofNat]
    gcongr
  set c₀ := 2 * Cψ * (1 + L') * (volume K₁).toReal * Dr with hc₀def
  have hCL : 0 ≤ 2 * Cψ * (1 + L') :=
    mul_nonneg (mul_nonneg zero_le_two hCψ0) (add_nonneg zero_le_one hL'0)
  have hc₀ : 0 ≤ c₀ := mul_nonneg (mul_nonneg hCL ENNReal.toReal_nonneg) hDr
  set ρt := η₁ / (c₀ + 1) with hρtdef
  have hρt : 0 < ρt := div_pos hη₁ (add_pos_of_nonneg_of_pos hc₀ one_pos)
  have htime : ∀ n ≥ N, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → s < ρt →
      ∫⁻ p in B, ‖mt n (p + (0, s)) - mt n p‖ₑ ≤ ENNReal.ofReal η₁ := by
    intro n hn s hs hs1 hsρ
    have h := lintegral_energyMoment_time_translate_le S.isOpen hQc hβ (hsol n) k hK₁m hK₂c hrU
      (fun x hx ↦ (closedBall_subset_cthickening hx δ).trans (cthickening_mono hδr _)) hT₁ hs
      measurableSet_Icc (a := T₁) (b := T₂ + 1) (J := Icc T₁ T₂)
      (fun t ht ↦ ⟨ht.1, by linarith [ht.2]⟩) hCψ hL'0
      (fun x hx τ hτ ↦ hLn n hn (x, τ) ⟨hx, by linarith [hτ.1], by linarith [hτ.2]⟩)
    have heq : ∀ p : E d × ℝ, mt n (p + (0, s)) - mt n p =
        energyMoment S.Q β (ε n) (v n) (LongTime.mollAt k p.1) (p.2 + s) -
          energyMoment S.Q β (ε n) (v n) (LongTime.mollAt k p.1) p.2 := fun p ↦ by
      simp only [hmtdef, hedef, energyMoment, Prod.fst_add, Prod.snd_add, add_zero]
    simp_rw [heq]
    refine h.trans ?_
    calc ENNReal.ofReal (2 * Cψ * (1 + L')) * volume K₁ * ENNReal.ofReal s *
          ∫⁻ q in K₂ ×ˢ Icc T₁ (T₂ + 1), (ENNReal.ofReal (dₜ (v n) q ^ 2) + 1)
        ≤ ENNReal.ofReal (2 * Cψ * (1 + L')) * ENNReal.ofReal (volume K₁).toReal *
            ENNReal.ofReal s * ENNReal.ofReal Dr := by
          rw [ENNReal.ofReal_toReal (hK₁c.measure_lt_top.ne)]
          gcongr
          exact hD n
      _ = ENNReal.ofReal (c₀ * s) := by
          rw [← ENNReal.ofReal_mul hCL, ← ENNReal.ofReal_mul (mul_nonneg hCL ENNReal.toReal_nonneg),
            ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCL ENNReal.toReal_nonneg) hs), hc₀def]
          ring_nf
      _ ≤ ENNReal.ofReal η₁ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : c₀ * s ≤ c₀ * ρt := mul_le_mul_of_nonneg_left hsρ.le hc₀
          have h2 : (c₀ + 1) * ρt = η₁ := by
            rw [hρtdef]
            field_simp
          linarith
  -- time translations of `|∇v_n|²`
  obtain ⟨ρF, hρF, hρFP⟩ := Metric.eventually_nhds_iff.1 hFtr
  refine ⟨min 1 (min ρt ρF), lt_min one_pos (lt_min hρt hρF), fun n hn s hs hsρ ↦ ?_⟩
  have hs1 : s < 1 := hsρ.trans_le (min_le_left _ _)
  have hsρt : s < ρt := hsρ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsρF : s < ρF := hsρ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hnormt : ‖(((0 : E d), s) : E d × ℝ)‖ = s := by
    rw [Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_of_nonneg hs, max_eq_right hs]
  have hmemB' : ∀ p ∈ B, p + ((0 : E d), s) ∈ B' := fun p hp ↦ by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hp.1
    · simp only [Prod.snd_add]
      linarith [hp.2.1]
    · simp only [Prod.snd_add]
      linarith [hp.2.2]
  have hB'' : B ⊆ UInf S.U := hBB'.trans hB'Ω
  have hmapsB : ∀ p ∈ B, p + ((0 : E d), s) ∈ UInf S.U := fun p hp ↦ hB'Ω (hmemB' p hp)
  have hI4 : ∫⁻ p in B, ‖Fn n (p + (0, s)) - Fn n p‖ₑ ≤ ENNReal.ofReal η₁ := by
    have := (hρFP (y := (((0 : E d), s) : E d × ℝ)) (by rw [dist_zero_right, hnormt]; exact hsρF))
      n hn
    exact (lintegral_mono_set hBB').trans (this.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have h := lintegral_time_translate_of_energy hBm hB'm hBB' hmemB' hm hη₁.le
    (Q2 := fun x ↦ S.Q x ^ 2) (fun p hp ↦ (hQmem p.1 (hK₁U hp.1)).2.1) (fun p ↦ rfl)
    (hmm_eq n) (((hec n).comp (continuous_add_const _).continuousOn hmapsB).aemeasurable hBm)
    (((hec n).mono hB'').aemeasurable hBm) (hmmm n) (hmoll n hn) (htime n hn s hs hs1.le hsρt)
    hI4
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [hη₁def]
  field_simp

/-- **Lemma 4.3, compactness part** (proof: time regularity of the mollified energy density plus
the Fréchet–Kolmogorov compactness criterion, from gmt-foundations v0.1.0). For solutions
`v_n` of (3.4) with `ε_n → 0⁺`, data `0 ≤ g_n ≤ M`, `g_n ∈ H¹(U)` with energy bound `E0 < ∞`,
`v_n → u` locally uniformly on `U_∞` (`u` continuous, locally Lipschitz in space) and
`∇v_n → ∇u` in `L²_loc(U_∞)`: along a subsequence
`χ_{ε_n}(v_n) → χ₀` in `L¹_loc(U_∞)`, for some measurable `χ₀`. -/
theorem exists_tendstoLpLoc_chiEps_subseq (S : Setting d) (hβ : IsReactionProfile β)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) {g : ℕ → E d → ℝ}
    {G : ℕ → E d → E d} {v : ℕ → E d × ℝ → ℝ} {u : E d × ℝ → ℝ} {M : ℝ} {E0 : ℝ≥0∞}
    (hE0 : E0 ≠ ⊤) (hv : ∀ n, IsSemilinearSolution S.U S.Q β (ε n) (g n) (v n))
    (hg : ∀ n, MemH1 S.U (g n) (G n)) (hgE : ∀ n, energyBound S (G n) ≤ E0)
    (hgM : ∀ n, ∀ x ∈ S.U, 0 ≤ g n x ∧ g n x ≤ M)
    (hconv : TendstoLocallyUniformlyOn v u atTop (UInf S.U))
    (hgrad : TendstoLpLoc 2 volume (UInf S.U) (fun n ↦ gradₓ (v n)) (gradₓ u) atTop)
    (hucont : ContinuousOn u (UInf S.U)) (hulip : LocLipₓ (UInf S.U) u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀ : E d × ℝ → ℝ, Measurable χ₀ ∧
      TendstoLpLoc 1 volume (UInf S.U) (fun n ↦ chiEps β (ε (φ n)) (v (φ n))) χ₀ atTop := by
  obtain ⟨N₁, hN₁⟩ := chiEps_space_translation S hβ hε hε0 hE0 hv hg hgE hgM
  obtain ⟨N₂, hN₂⟩ := chiEps_time_translation S hβ hε hε0 hE0 hv hg hgE hgM hconv hgrad hucont hulip
  set N := max N₁ N₂ with hNdef
  set f : ℕ → E d × ℝ → ℝ := fun k ↦ chiEps β (ε (k + N)) (v (k + N)) with hfdef
  have hΩ : IsOpen (UInf S.U) := S.isOpen.prod isOpen_Ioi
  have hΩc : (UInf S.U)ᶜ.Nonempty := ⟨(0, -1), fun h ↦ by
    have := h.2
    simp only [mem_Ioi] at this
    linarith⟩
  have hBc : ∀ e, Continuous (bigBEps β e) := fun e ↦
    continuous_iff_continuousAt.2 fun z ↦ (hβ.hasDerivAt_bigBEps e z).continuousAt
  have hfc : ∀ k, ContinuousOn (f k) (UInf S.U) := fun k ↦
    continuousOn_const.mul ((hBc _).comp_continuousOn (hv _).2.1.1)
  have hfb : ∀ k, ∀ p ∈ UInf S.U, |f k p| ≤ 1 := fun k p _ ↦ by
    have h := chiEps_mem_Icc hβ (hε (k + N)) (v (k + N)) p
    rw [abs_of_nonneg h.1]
    exact h.2
  have htrans := translation_of_space_time hΩ hfc
    (fun A hA hAc η hη ↦ by
      obtain ⟨ρ, hρ, h⟩ := hN₁ A hA hAc η hη
      exact ⟨ρ, hρ, fun k ↦ h (k + N) ((le_max_left N₁ N₂).trans (Nat.le_add_left N k))⟩)
    (fun A hA hAc η hη ↦ by
      obtain ⟨ρ, hρ, h⟩ := hN₂ A hA hAc η hη
      exact ⟨ρ, hρ, fun k ↦ h (k + N) ((le_max_right N₁ N₂).trans (Nat.le_add_left N k))⟩)
  obtain ⟨φ, hφ, χ₀, hχ₀, hconvχ⟩ :=
    exists_tendstoLpLoc_subseq_of_translation hΩ hΩc hfc hfb htrans
  exact ⟨fun k ↦ φ k + N, fun a b hab ↦ Nat.add_lt_add_right (hφ hab) N, χ₀, hχ₀, hconvχ⟩

end ChiEps

end Inner

end PerronVariational

end
