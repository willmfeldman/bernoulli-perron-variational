/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.SliceInnerVar
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Time localization of the parabolic identities (proof of Theorem 3.10, Steps 2 and 4)

The proof of **Theorem 3.10** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, uses, at almost
every time `t`, the spatial ("time-sliced") versions of the space-time relations satisfied by
`(u, χ)`:

* the weak heat equation in the positivity set, slice form of (4.5) (used for (4.12));
* the inner variation identity, slice form (4.17);
* `1_{u(·,t) > 0} ≤ χ(·, t)` a.e. (Step 4);
* the energy bound `J(u(t), χ(t); U) ≤ E₀` from (3.11);
* `∂ₜu(·, t) ∈ L²(U)`, with `t ↦ ∫_U |∂ₜu(t)|²` integrable on `(0, ∞)`.

## Deviation: the weak heat equation is a hypothesis

The paper's Definition 3.7 does **not** contain the weak heat equation (4.5) in `{u > 0}`; the
paper proves (4.5) only for the `ε → 0` limit (proof of Lemma 4.2), but the proof of Theorem 3.10
(Step 2) uses it for the given `(u, χ)`. Without it Theorem 3.10 is false: `u(x, t) = 1 + |x₁|`,
`χ ≡ 1`, `Q` constant satisfies all hypotheses of `LongtimeInnerStatement`, but
`u_∞ = 1 + |x₁|` is not `C²` in `{u_∞ > 0} = U`. Here we therefore assume (4.5) as the
hypothesis `WeakHeatInPos`; Proposition 4.1 and Theorem 3.9 provide it for the flows used in
Propositions 6.1 and 6.2.

## Main definitions

* `PerronVariational.LongTime.WeakHeatInPos`: the weak heat equation (4.5) in `{u > 0} ∩ U_∞`.
* `PerronVariational.LongTime.IsGoodSlice`: all slice properties at a time `t`.

## Main results

* `PerronVariational.LongTime.ae_isGoodSlice`: a.e. `t > 0` is a good slice.
* `PerronVariational.LongTime.exists_wSlice`: `t ↦ ∫_U |∂ₜu(·, t)|²` agrees a.e. with a
  measurable function with finite integral over `(0, ∞)`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped Gradient ENNReal

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}


/-- A **good slice** `t`: the time-sliced relations used in Steps 2–4 of the proof of Theorem 3.10
hold at `t`. -/
structure IsGoodSlice (U : Set (E d)) (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (E0 : ℝ≥0∞)
    (t : ℝ) : Prop where
  pos : 0 < t
  /-- The energy bound from (3.11). -/
  energy : energyJχ U Q (fun x ↦ gradₓ u (x, t)) (fun x ↦ χ (x, t)) ≤ E0
  /-- `∂ₜu(·, t) ∈ L²(U)`. -/
  memL2 : MemLp (fun x ↦ w (x, t)) 2 (volume.restrict U)
  /-- `1_{u(·,t) > 0} ≤ χ(·, t)` a.e. in `U`. -/
  pos_le : ∀ᵐ x ∂(volume.restrict U), 0 < u (x, t) → χ (x, t) = 1
  /-- Slice form of (4.5): `∫_U ∂ₜu(t) ζ = -∫_U ∇u(t) · ∇ζ` for Lipschitz `ζ` with compact
  support in `{u(·, t) > 0} ∩ U`. -/
  heat : ∀ ζ : E d → ℝ, (∃ K, LipschitzWith K ζ) → HasCompactSupport ζ →
    tsupport ζ ⊆ posSet (fun y ↦ u (y, t)) U →
    ∫ x in U, w (x, t) * ζ x = -∫ x in U, inner ℝ (gradₓ u (x, t)) (∇ ζ x)
  /-- (4.17) for `ξ ∈ C¹_c(U; ℝᵈ)`. -/
  innerVar : ∀ ξ : E d → E d, ContDiff ℝ 1 ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
    Integrable (sliceInnerVarIntegrand Q u w χ t ξ) (volume.restrict U) ∧
      ∫ x in U, sliceInnerVarIntegrand Q u w χ t ξ x = 0

section Slices

variable {U : Set (E d)} {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ} {E0 : ℝ≥0∞}

/-- The energy bound `J(u(t), χ(t); U) ≤ E₀` for a.e. `t > 0`, from (3.11). -/
theorem ae_energy_le (hdiss : DissipationIneq U Q u w χ E0) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      energyJχ U Q (fun x ↦ gradₓ u (x, t)) (fun x ↦ χ (x, t)) ≤ E0 := by
  filter_upwards [hdiss] with t ht
  set J := energyJχ U Q (fun x ↦ gradₓ u (x, t)) (fun x ↦ χ (x, t))
  have h1 : J / 2 ≤ E0 / 2 := le_trans le_self_add ht
  calc J = J / 2 * 2 := (ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
    _ ≤ E0 / 2 * 2 := by gcongr
    _ = E0 := ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- **Fubini for null sets on a product domain**: a property holding a.e. on `U × I` holds, for
a.e. `t ∈ I`, a.e. on the slice `U × {t}`. No measurability of the property is needed. -/
theorem ae_slice_of_ae {I : Set ℝ} {P : E d × ℝ → Prop}
    (h : ∀ᵐ p ∂(volume.restrict (U ×ˢ I)), P p) :
    ∀ᵐ t ∂(volume.restrict I), ∀ᵐ x ∂(volume.restrict U), P (x, t) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  obtain ⟨M, hNM, hMm, hM0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have hswap : ((volume.restrict I).prod (volume.restrict U)) (Prod.swap ⁻¹' M) = 0 := by
    rw [(Measure.measurePreserving_swap (μ := volume.restrict I)
      (ν := volume.restrict U)).measure_preimage hMm.nullMeasurableSet]
    exact hM0
  filter_upwards [Measure.ae_ae_of_ae_prod (measure_eq_zero_iff_ae_notMem.1 hswap)] with t ht
  filter_upwards [ht] with x hx
  by_contra hP
  exact hx (hNM hP)

/-- **Fubini for `∂ₜu`** (bookkeeping): `∂ₜu(·, t) ∈ L²(U)` for a.e. `t > 0`, and
`t ↦ ∫_U |∂ₜu(·, t)|²` agrees a.e. on `(0, ∞)` with a measurable function whose integral over
`(0, ∞)` is finite (it equals `∫_{U_∞} |∂ₜu|²`). Tonelli applied to a measurable modification
of `w` (`w ∈ L²(U_∞)` is only a.e.-strongly measurable). -/
theorem ae_memL2_slice_and_exists_wSlice (h : IsParaInnerVarSolution U Q u w χ) :
    (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), MemLp (fun x ↦ w (x, t)) 2 (volume.restrict U)) ∧
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧ ∫⁻ t in Ioi 0, G t ≠ ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∫⁻ x in U, ENNReal.ofReal (w (x, t) ^ 2) = G t := by
  have hw := h.timeDeriv_memL2
  set w' := hw.1.mk w
  have hw'm : StronglyMeasurable w' := hw.1.stronglyMeasurable_mk
  have hweq : w =ᵐ[volume.restrict (UInf U)] w' := hw.1.ae_eq_mk
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ x ∂(volume.restrict U),
      w (x, t) = w' (x, t) := ae_slice_of_ae hweq
  have hfm : Measurable fun p : E d × ℝ ↦ ENNReal.ofReal (w' p ^ 2) :=
    ENNReal.measurable_ofReal.comp (hw'm.measurable.pow_const 2)
  set G : ℝ → ℝ≥0∞ := fun t ↦ ∫⁻ x in U, ENNReal.ofReal (w' (x, t) ^ 2)
  have hGm : Measurable G := hfm.lintegral_prod_left'
  have hint : ∫⁻ t in Ioi 0, G t = ∫⁻ p in UInf U, ENNReal.ofReal (w' p ^ 2) := by
    rw [UInf, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm' _ hfm]
  have hfin : ∫⁻ t in Ioi 0, G t ≠ ⊤ := by
    rw [hint]
    have hw' : MemLp w' 2 (volume.restrict (UInf U)) := hw.ae_eq hweq
    exact ((memLp_two_iff_integrable_sq hw'.1).1 hw').lintegral_lt_top.ne
  refine ⟨?_, G, hGm, hfin, ?_⟩
  · filter_upwards [hslice, ae_lt_top hGm hfin] with t ht hGt
    have hm : AEStronglyMeasurable (fun x ↦ w' (x, t)) (volume.restrict U) :=
      (hw'm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have hmem : MemLp (fun x ↦ w' (x, t)) 2 (volume.restrict U) := by
      rw [memLp_two_iff_integrable_sq hm]
      exact ⟨hm.pow 2, (hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall fun x ↦ sq_nonneg (w' (x, t)))).2 hGt⟩
    exact hmem.ae_eq (by filter_upwards [ht] with x hx using hx.symm)
  · filter_upwards [hslice] with t ht
    exact lintegral_congr_ae (ht.mono fun x hx ↦ by simp [hx])

/-- **Fubini for `1_{u>0} ≤ χ`**: the space-time a.e. inequality of Definition 3.7(iii) holds on
a.e. time slice. -/
theorem ae_pos_le_slice (h : IsParaInnerVarSolution U Q u w χ) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ x ∂(volume.restrict U), 0 < u (x, t) → χ (x, t) = 1 :=
  ae_slice_of_ae h.pos_le

/-- **Time localization of (4.5)** (as in (4.12)): for a.e. `t > 0`,
`∫_U ∂ₜu(t) ζ = -∫_U ∇u(t) · ∇ζ` for every Lipschitz `ζ` with compact support in
`{u(·, t) > 0} ∩ U`.

Proof: (4.5) tested with `ρₙ(x - q) ψ(s)` (`q` in a countable dense set) and du Bois-Reymond in
time give the slice identity for all translated bumps outside a common null set of times
(`ae_heat_slice_bump`); the density of translated bumps (`heat_slice_of_bumps`) concludes, using
`∂ₜu(t) ∈ L²(U)` and the local boundedness of `∇u(t)`. -/
theorem ae_heat_slice (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hheat : WeakHeatInPos U u w) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ ζ : E d → ℝ, (∃ K, LipschitzWith K ζ) → HasCompactSupport ζ →
        tsupport ζ ⊆ posSet (fun y ↦ u (y, t)) U →
        ∫ x in U, w (x, t) * ζ x = -∫ x in U, inner ℝ (gradₓ u (x, t)) (∇ ζ x) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (E d)
  have hall : ∀ᵐ s, ∀ n, ∀ q ∈ D, s ∈ bumpTimes U u n q →
      ∫ x in U, (w (x, s) * mollAt n q x + inner ℝ (gradₓ u (x, s)) (∇ (mollAt n q) x)) = 0 :=
    ae_all_iff.2 fun n ↦ (ae_ball_iff hDc).2 fun q _ ↦ ae_heat_slice_bump hU h hheat n q
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hall,
    (ae_memL2_slice_and_exists_wSlice h).1] with s hs hb hmem
  exact heat_slice_of_bumps hU h hDd hs hmem hb

/-- **Time localization of (3.3)** ((4.17)): for a.e.
`t > 0`, the slice integrand is integrable and has zero integral for every Lipschitz `ξ` with
compact support in `U` (in particular for `ξ ∈ C¹_c(U; ℝᵈ)`).

Proof: (3.3) tested with `ψ(s) ρₙ(x - q) eᵢ` (`q` in a countable dense set) and du Bois-Reymond
in time give the slice identity for all translated bumps times coordinate vectors outside a
common null set of times (`ae_innerVar_slice_bump`); the coordinate decomposition of the
integrand and the density of translated bumps (`innerVar_slice_of_bumps`) conclude, using
`∂ₜu(t) ∈ L²(U)`, the local boundedness of `∇u(t)` and the local Lipschitz continuity of `Q²`. -/
theorem ae_innerVar_slice (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hQ : LocallyLipschitzOn U fun y ↦ Q y ^ 2) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ ξ : E d → E d, (∃ K, LipschitzWith K ξ) → HasCompactSupport ξ → tsupport ξ ⊆ U →
        Integrable (sliceInnerVarIntegrand Q u w χ t ξ) (volume.restrict U) ∧
          ∫ x in U, sliceInnerVarIntegrand Q u w χ t ξ x = 0 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (E d)
  have hall : ∀ᵐ s, ∀ n, ∀ q ∈ D, closedBall q (bumpRad n) ⊆ U → ∀ i : Fin d,
      s ∈ Ioi (0 : ℝ) →
      ∫ x in U, sliceInnerVarIntegrand Q u w χ s (fun y ↦ mollAt n q y • coordVec i) x = 0 := by
    refine ae_all_iff.2 fun n ↦ (ae_ball_iff hDc).2 fun q _ ↦ ?_
    by_cases hB : closedBall q (bumpRad n) ⊆ U
    · filter_upwards [ae_all_iff.2 fun i : Fin d ↦
        ae_innerVar_slice_bump hU h n q hB (coordVec i)] with s hs _ i hsI using hs i hsI
    · exact Eventually.of_forall fun s hB' ↦ absurd hB' hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hall,
    (ae_memL2_slice_and_exists_wSlice h).1] with s hs hb hmem
  exact innerVar_slice_of_bumps hU h hQ hDd hs hmem fun n q hq hB i ↦ hb n q hq hB i hs

/-- Almost every `t > 0` is a good slice. -/
theorem ae_isGoodSlice (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hQ : LocallyLipschitzOn U fun y ↦ Q y ^ 2) (hdiss : DissipationIneq U Q u w χ E0)
    (hheat : WeakHeatInPos U u w) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), IsGoodSlice U Q u w χ E0 t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_energy_le hdiss,
    (ae_memL2_slice_and_exists_wSlice h).1, ae_pos_le_slice h, ae_heat_slice hU h hheat,
    ae_innerVar_slice hU h hQ] with t ht h1 h2 h3 h4 h5
  exact ⟨ht, h1, h2, h3, h4, fun ξ hξ hξc hξU ↦
    h5 ξ (ContDiff.lipschitzWith_of_hasCompactSupport hξc hξ one_ne_zero) hξc hξU⟩

end Slices

end LongTime

end PerronVariational

end
