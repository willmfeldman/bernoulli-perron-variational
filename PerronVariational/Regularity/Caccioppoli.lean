/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Sobolev

/-!
# From the energy inequality to a gradient inequality

* `integral_norm_sq_le_of_energyJ_le`: from `J_Q(w; B) ≤ J_Q(v; B)` and
  `{v > 0} ⊆ {w > 0} ∪ A` to `∫_B |∇w|² ≤ ∫_B |∇v|² + sup Q² |A|`.

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper"). It
is used for the continuity of one-sided obstacle minimizers in the proof of Lemma 6.3 (see
`Regularity/ObstacleBoundary.lean`).

The hole-filling lemma `caccioppoli_of_step` and the De Giorgi class `IsDeGiorgiAt` come from the
dependency gmt-foundations v0.1.0 (`GMTFoundations.DeGiorgi.Caccioppoli`); this module keeps only
the lemma above, which uses the energy `energyJ` of this library.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public section

namespace PerronVariational.Regularity

variable {d : ℕ}

/-! ### From the energy inequality to a gradient inequality -/

/-- If `J_Q(w; B) ≤ J_Q(v; B)`, `Q² ≤ Cq` on `B` and `{v > 0} ⊆ {w > 0} ∪ A`, then
`∫_B |∇w|² ≤ ∫_B |∇v|² + Cq |A|`. -/
theorem integral_norm_sq_le_of_energyJ_le {B A : Set (E d)} (hB : MeasurableSet B)
    (hBf : volume B ≠ ⊤) (hA : volume A ≠ ⊤) {Q w v : E d → ℝ} {Gw Gv : E d → E d} {Cq : ℝ}
    (hCq : 0 ≤ Cq) (hQ : ∀ x ∈ B, Q x ^ 2 ≤ Cq)
    (hw : IntegrableOn (fun x ↦ ‖Gw x‖ ^ 2) B) (hv : IntegrableOn (fun x ↦ ‖Gv x‖ ^ 2) B)
    (hJ : energyJ B Q w Gw ≤ energyJ B Q v Gv) (hpos : posSet v B ⊆ posSet w B ∪ A) :
    ∫ x in B, ‖Gw x‖ ^ 2 ≤ (∫ x in B, ‖Gv x‖ ^ 2) + Cq * (volume A).toReal := by
  set Yw : ℝ≥0∞ := ∫⁻ x in B, ENNReal.ofReal (Q x ^ 2 * (posSet w B).indicator 1 x) with hYw
  set Yv : ℝ≥0∞ := ∫⁻ x in B, ENNReal.ofReal (Q x ^ 2 * (posSet v B).indicator 1 x) with hYv
  set Iw : ℝ≥0∞ := ∫⁻ x in B, ENNReal.ofReal (‖Gw x‖ ^ 2) with hIw
  set Iv : ℝ≥0∞ := ∫⁻ x in B, ENNReal.ofReal (‖Gv x‖ ^ 2) with hIv
  have hind : ∀ (S : Set (E d)) x, 0 ≤ Q x ^ 2 * S.indicator (1 : E d → ℝ) x := fun S x ↦
    mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  have eJ : ∀ (f : E d → ℝ) (G : E d → E d), IntegrableOn (fun x ↦ ‖G x‖ ^ 2) B →
      energyJ B Q f G = (∫⁻ x in B, ENNReal.ofReal (‖G x‖ ^ 2)) +
        ∫⁻ x in B, ENNReal.ofReal (Q x ^ 2 * (posSet f B).indicator 1 x) := by
    intro f G hG
    unfold energyJ
    rw [← lintegral_add_left' hG.1.aemeasurable.ennreal_ofReal]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_add (sq_nonneg _) (hind _ x)]
  set A' := toMeasurable volume A with hA'
  have hA'm : MeasurableSet A' := measurableSet_toMeasurable _ _
  have hYv : Yv ≤ Yw + ENNReal.ofReal Cq * volume A := by
    calc Yv ≤ ∫⁻ x in B, (ENNReal.ofReal (Q x ^ 2 * (posSet w B).indicator 1 x) +
          A'.indicator (fun _ ↦ ENNReal.ofReal Cq) x) := by
          refine lintegral_mono_ae ((ae_restrict_iff' hB).2 (Eventually.of_forall fun x hx ↦ ?_))
          by_cases hv' : x ∈ posSet v B
          · rcases hpos hv' with hw' | hA''
            · rw [indicator_of_mem hv', indicator_of_mem hw']
              exact le_self_add
            · rw [indicator_of_mem hv', indicator_of_mem (subset_toMeasurable _ _ hA''),
                Pi.one_apply, mul_one]
              exact le_add_left (ENNReal.ofReal_le_ofReal (hQ x hx))
          · rw [indicator_of_notMem hv', mul_zero, ENNReal.ofReal_zero]
            exact bot_le
      _ = Yw + ∫⁻ x in B, A'.indicator (fun _ ↦ ENNReal.ofReal Cq) x := by
          rw [lintegral_add_right' _ (measurable_const.indicator hA'm).aemeasurable]
      _ ≤ Yw + ENNReal.ofReal Cq * volume A := by
          gcongr
          rw [lintegral_indicator_const hA'm, Measure.restrict_apply hA'm]
          exact mul_le_mul_right ((measure_mono inter_subset_left).trans
            (measure_toMeasurable A).le) _
  have hYw_fin : Yw ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in B, ENNReal.ofReal Cq) ?_ ?_
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBf
    · refine lintegral_mono_ae ((ae_restrict_iff' hB).2 (Eventually.of_forall fun x hx ↦ ?_))
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hx' : x ∈ posSet w B
      · rw [indicator_of_mem hx', Pi.one_apply, mul_one]; exact hQ x hx
      · rw [indicator_of_notMem hx', mul_zero]; exact hCq
  have hmain : Iw ≤ Iv + ENNReal.ofReal Cq * volume A := by
    have h1 : Iw + Yw ≤ Iv + ENNReal.ofReal Cq * volume A + Yw := by
      calc Iw + Yw = energyJ B Q w Gw := (eJ w Gw hw).symm
        _ ≤ energyJ B Q v Gv := hJ
        _ = Iv + Yv := eJ v Gv hv
        _ ≤ Iv + (Yw + ENNReal.ofReal Cq * volume A) := by gcongr
        _ = Iv + ENNReal.ofReal Cq * volume A + Yw := by ring
    exact (ENNReal.add_le_add_iff_right hYw_fin).1 h1
  have eIw : Iw = ENNReal.ofReal (∫ x in B, ‖Gw x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall fun x ↦ sq_nonneg _)).symm
  have eIv : Iv = ENNReal.ofReal (∫ x in B, ‖Gv x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hv (Eventually.of_forall fun x ↦ sq_nonneg _)).symm
  have eA : ENNReal.ofReal Cq * volume A = ENNReal.ofReal (Cq * (volume A).toReal) := by
    rw [ENNReal.ofReal_mul hCq, ENNReal.ofReal_toReal hA]
  have hIv0 : 0 ≤ ∫ x in B, ‖Gv x‖ ^ 2 := setIntegral_nonneg hB fun x _ ↦ sq_nonneg _
  have hA0 : 0 ≤ Cq * (volume A).toReal := mul_nonneg hCq ENNReal.toReal_nonneg
  rw [eIw, eIv, eA, ← ENNReal.ofReal_add hIv0 hA0] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hIv0 hA0)).1 hmain

end PerronVariational.Regularity

end
