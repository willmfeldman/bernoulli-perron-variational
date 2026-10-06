/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.SliceHeat
public import PerronVariational.Inner.InnerVarLinear
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import PerronVariational.Inner.SliceFubini

/-!
# Time localization of the parabolic inner variation identity (3.3)

Proof of **Theorem 3.10**, Step 4 ((4.17)), of F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981: for a parabolic inner variational solution, for a.e. `t > 0`, the time-sliced
integrand of (3.3) is integrable over `U` with zero integral for every `ξ ∈ C¹_c(U; ℝᵈ)`.

Proof: (3.3) tested with `ψ(s) ρₙ(x - q) eᵢ` and du Bois-Reymond in time give the slice identity
for all translated bumps times coordinate vectors outside a common null set of times; the
coordinate decomposition of the integrand (`Inner/InnerVarLinear.lean`) and the density of
translated bumps (`firstOrderFunctional_eq_zero_of_bumps`) conclude.

## Main definitions

* `PerronVariational.LongTime.sliceInnerVarIntegrand`: the integrand of (4.17).

## Main results

* `PerronVariational.LongTime.ae_innerVar_slice_bump`
* `PerronVariational.LongTime.innerVar_slice_of_bumps`
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient ContDiff

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-- The integrand of the time-localized inner variation identity (4.17) at time `t`, for a
spatial vector field `ξ`. -/
noncomputable def sliceInnerVarIntegrand (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (t : ℝ)
    (ξ : E d → E d) (x : E d) : ℝ :=
  innerVarIntegrand Q (fun y ↦ u (y, t)) (fun y ↦ χ (y, t)) ξ x
    - 2 * inner ℝ (ξ x) (gradₓ u (x, t)) * w (x, t)

/-- The zeroth-order coefficient of the slice integrand in direction `e`. -/
noncomputable def sliceCoeffA (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (t : ℝ) (e : E d)
    (x : E d) : ℝ :=
  ivCoeffA Q (fun y ↦ χ (y, t)) e x - 2 * inner ℝ e (gradₓ u (x, t)) * w (x, t)

theorem sliceInnerVarIntegrand_smul_const (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (t : ℝ)
    {ζ : E d → ℝ} {x : E d} (hζ : DifferentiableAt ℝ ζ x) (e : E d) :
    sliceInnerVarIntegrand Q u w χ t (fun y ↦ ζ y • e) x =
      sliceCoeffA Q u w χ t e x * ζ x +
        fderiv ℝ ζ x (ivCoeffG Q (fun y ↦ u (y, t)) (fun y ↦ χ (y, t)) e x) := by
  rw [sliceInnerVarIntegrand, innerVarIntegrand_smul_const _ _ _ hζ, sliceCoeffA,
    inner_smul_left]
  simp only [conj_trivial]
  ring

theorem sliceInnerVarIntegrand_eq_sum_coord (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (t : ℝ)
    {ξ : E d → E d} {x : E d} (hξ : DifferentiableAt ℝ ξ x) :
    sliceInnerVarIntegrand Q u w χ t ξ x = ∑ i, (sliceCoeffA Q u w χ t (coordVec i) x * ξ x i +
      fderiv ℝ (fun y ↦ ξ y i) x
        (ivCoeffG Q (fun y ↦ u (y, t)) (fun y ↦ χ (y, t)) (coordVec i) x)) := by
  have hin : inner ℝ (ξ x) (gradₓ u (x, t)) =
      ∑ i, ξ x i * inner ℝ (coordVec i) (gradₓ u (x, t)) := by
    conv_lhs => rw [← sum_coord_smul (ξ x)]
    simp [sum_inner, inner_smul_left]
  rw [sliceInnerVarIntegrand, innerVarIntegrand_eq_sum_coord _ _ _ hξ, hin]
  simp only [sliceCoeffA, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- The slice integrand vanishes where `ξ` vanishes near `x`. -/
theorem sliceInnerVarIntegrand_eq_zero (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (t : ℝ)
    {ξ : E d → E d} {x : E d} (hx : x ∉ tsupport ξ) :
    sliceInnerVarIntegrand Q u w χ t ξ x = 0 := by
  simp [sliceInnerVarIntegrand, innerVarIntegrand, divergence,
    fderiv_of_notMem_tsupport ℝ hx, image_eq_zero_of_notMem_tsupport hx]

/-- The space-time integrand of (3.3) for `ξ(x, s) = ψ(s) η(x)`. -/
theorem paraInnerVarIntegrand_timeProd (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (ψ : ℝ → ℝ)
    {η : E d → E d} (hη : Differentiable ℝ η) (x : E d) (s : ℝ) :
    paraInnerVarIntegrand Q u w χ (fun p ↦ ψ p.2 • η p.1) (x, s) =
      ψ s * sliceInnerVarIntegrand Q u w χ s η x := by
  have hD : fderivₓ (fun p : E d × ℝ ↦ ψ p.2 • η p.1) (x, s) = ψ s • fderiv ℝ η x :=
    fderiv_fun_const_smul (hη x) (ψ s)
  simp only [paraInnerVarIntegrand, divₓ, hD, sliceInnerVarIntegrand, innerVarIntegrand,
    divergence, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul,
    smul_apply, inner_smul_right, inner_smul_left, conj_trivial]
  change _ = ψ s * ((‖gradₓ u (x, s)‖ ^ 2 + _) * _ - 2 * inner ℝ (gradₓ u (x, s))
    (fderiv ℝ η x (gradₓ u (x, s))) + _ - _)
  ring

/-- A smooth time cutoff equal to `1` on a compact `J ⊆ (0, ∞)` with support in `(0, ∞)`. -/
theorem exists_time_cutoff {J : Set ℝ} (hJ : IsCompact J) (hJ0 : J ⊆ Ioi 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioi 0 ∧
      ∀ s ∈ J, ψ s = 1 := by
  rcases J.eq_empty_or_nonempty with hJe | hJne
  · exact ⟨0, contDiff_const, HasCompactSupport.zero, by simp, by simp [hJe]⟩
  obtain ⟨a, haJ, ha⟩ := hJ.exists_isLeast hJne
  obtain ⟨b, hbJ, hb⟩ := hJ.exists_isGreatest hJne
  have ha0 : 0 < a := hJ0 haJ
  have hab : a ≤ b := hb haJ
  let f : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 2 + a / 4, (b - a) / 2 + a / 2, by linarith, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, fun s hs ↦ f.one_of_mem_closedBall ?_⟩
  · rw [f.tsupport_eq]
    intro s hs
    rw [mem_closedBall, Real.dist_eq, abs_le] at hs
    change 0 < s
    have : f.rOut = (b - a) / 2 + a / 2 := rfl
    linarith [hs.1]
  · have h1 := ha hs
    have h2 := hb hs
    rw [mem_closedBall, Real.dist_eq, abs_le]
    have : f.rIn = (b - a) / 2 + a / 4 := rfl
    constructor <;> linarith

theorem tsupport_mollAt_subset (n : ℕ) (q : E d) :
    tsupport (mollAt n q) ⊆ closedBall q (bumpRad n) :=
  closure_minimal (fun _ hy ↦ by_contra fun h' ↦ hy (mollAt_eq_zero h')) isClosed_closedBall

theorem tsupport_mollAt_smul_subset (n : ℕ) (q e : E d) :
    tsupport (fun y ↦ mollAt n q y • e) ⊆ closedBall q (bumpRad n) :=
  (tsupport_smul_subset_left _ _).trans (tsupport_mollAt_subset n q)

section InnerVar

variable {U : Set (E d)} {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ}

/-- The slice identity (4.17) for one translated bump times a fixed vector, for a.e. time. -/
theorem ae_innerVar_slice_bump (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ) (n : ℕ)
    (q : E d) (hB : closedBall q (bumpRad n) ⊆ U) (e : E d) :
    ∀ᵐ s, s ∈ Ioi (0 : ℝ) →
      ∫ x in U, sliceInnerVarIntegrand Q u w χ s (fun y ↦ mollAt n q y • e) x = 0 := by
  set η : E d → E d := fun y ↦ mollAt n q y • e
  set B := closedBall q (bumpRad n)
  have hηs : ContDiff ℝ ∞ η := (contDiff_mollAt n q).smul contDiff_const
  have hηd : Differentiable ℝ η := hηs.differentiable (by simp)
  set H : E d × ℝ → ℝ := fun p ↦ sliceInnerVarIntegrand Q u w χ p.2 η p.1
  -- the fields `ψ(s) η(x)`
  have hfield : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 →
      ContDiff ℝ 1 (fun p : E d × ℝ ↦ ψ p.2 • η p.1) ∧
      HasCompactSupport (fun p : E d × ℝ ↦ ψ p.2 • η p.1) ∧
      tsupport (fun p : E d × ℝ ↦ ψ p.2 • η p.1) ⊆ UInf U := by
    intro ψ hψs hψc hψT
    have hKc : IsCompact (B ×ˢ tsupport ψ) := (isCompact_closedBall q _).prod hψc
    have hvan : ∀ p ∉ B ×ˢ tsupport ψ, ψ p.2 • η p.1 = 0 := fun p hp ↦ by
      rcases not_and_or.1 hp with h1 | h1
      · simp [η, mollAt_eq_zero h1]
      · simp [image_eq_zero_of_notMem_tsupport h1]
    refine ⟨((hψs.comp contDiff_snd).smul (hηs.comp contDiff_fst)).of_le (by simp),
      HasCompactSupport.intro hKc hvan, ?_⟩
    have hts : tsupport (fun p : E d × ℝ ↦ ψ p.2 • η p.1) ⊆ B ×ˢ tsupport ψ :=
      closure_minimal (fun p hp ↦ by_contra fun h' ↦ hp (hvan p h')) hKc.isClosed
    exact hts.trans fun p hp ↦ ⟨hB hp.1, hψT hp.2⟩
  have hpara : ∀ ψ : ℝ → ℝ, ∀ p : E d × ℝ,
      paraInnerVarIntegrand Q u w χ (fun p ↦ ψ p.2 • η p.1) p = ψ p.2 * H p :=
    fun ψ p ↦ paraInnerVarIntegrand_timeProd Q u w χ ψ hηd p.1 p.2
  refine ae_setIntegral_slice_eq_zero (h := H) hU.measurableSet measurableSet_Ioi isOpen_Ioi
    subset_rfl (fun J hJT hJ ↦ ?_) fun ψ hψs hψc hψT ↦ ?_
  · obtain ⟨ψ, hψs, hψc, hψT, hψ1⟩ := exists_time_cutoff hJ hJT
    obtain ⟨h1, h2, h3⟩ := hfield ψ hψs hψc hψT
    have hi := h.integrable _ h1 h2 h3
    rw [show paraInnerVarIntegrand Q u w χ (fun p ↦ ψ p.2 • η p.1) = fun p ↦ ψ p.2 * H p
      from funext (hpara ψ)] at hi
    have hi' : IntegrableOn (fun p ↦ ψ p.2 * H p) (UInf U) volume := hi
    refine (hi'.mono_set (Set.prod_mono le_rfl hJT)).congr_fun (fun p hp ↦ ?_)
      (hU.measurableSet.prod hJ.measurableSet)
    simp [hψ1 p.2 hp.2]
  · obtain ⟨h1, h2, h3⟩ := hfield ψ hψs hψc hψT
    have hst := h.stationary _ h1 h2 h3
    simp_rw [hpara ψ] at hst
    exact hst

/-- Integrability of `a ζ + Dζ(g)` for Lipschitz bounded `ζ`. -/
theorem integrable_firstOrder_integrand {μ : Measure (E d)} {a : E d → ℝ} {g : E d → E d}
    (ha : Integrable a μ) (hg : Integrable g μ) {ζ : E d → ℝ} {K : NNReal}
    (hζ : LipschitzWith K ζ) {Cζ : ℝ} (hCζ : ∀ x, ‖ζ x‖ ≤ Cζ) :
    Integrable (fun x ↦ a x * ζ x + fderiv ℝ ζ x (g x)) μ := by
  refine (ha.mul_bdd hζ.continuous.aestronglyMeasurable (Eventually.of_forall hCζ)).add ?_
  refine (hg.norm.const_mul K).mono'
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((measurable_fderiv ℝ ζ).aestronglyMeasurable.prodMk hg.aestronglyMeasurable))
    (Eventually.of_forall fun x ↦ ?_)
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_fderiv_le_of_lipschitz ℝ hζ) (norm_nonneg _))

/-- The coordinates `y ↦ ξ(y)ᵢ` of a Lipschitz field are Lipschitz. -/
theorem lipschitz_coord {ξ : E d → E d} {K : NNReal} (hξ : LipschitzWith K ξ) (i : Fin d) :
    ∃ K', LipschitzWith K' fun y ↦ ξ y i :=
  ⟨_, (EuclideanSpace.proj i : E d →L[ℝ] ℝ).lipschitzWith.comp hξ⟩

theorem tsupport_coord_subset (ξ : E d → E d) (i : Fin d) :
    tsupport (fun y ↦ ξ y i) ⊆ tsupport ξ :=
  closure_mono fun y hy h0 ↦ hy (by simp [h0])

/-- **Coordinatewise density of translated bumps.** Let `Aᵢ`, `Gᵢ` be integrable on compact
subsets of the open set `U`, and suppose that `∫_U Aᵢ ρ + Dρ(Gᵢ) = 0` for every translated bump
`ρ = ρₙ(· - q)` (`q` in a dense set `D`) supported in `U`. Then for every Lipschitz field `ξ`
with compact support in `U`, `x ↦ ∑ᵢ Aᵢ ξᵢ + Dξᵢ(Gᵢ)` is integrable on `U` with zero integral. -/
theorem sum_coord_firstOrder_eq_zero {U : Set (E d)} (hU : IsOpen U) {D : Set (E d)}
    (hD : Dense D) {A : Fin d → E d → ℝ} {G : Fin d → E d → E d}
    (hA : ∀ i, ∀ K, IsCompact K → K ⊆ U → IntegrableOn (A i) K)
    (hG : ∀ i, ∀ K, IsCompact K → K ⊆ U → IntegrableOn (G i) K)
    (hb : ∀ i n, ∀ q ∈ D, closedBall q (bumpRad n) ⊆ U →
      ∫ x in U, (A i x * mollAt n q x + fderiv ℝ (mollAt n q) x (G i x)) = 0)
    {ξ : E d → E d} (hξ : ∃ K, LipschitzWith K ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ U) :
    IntegrableOn (fun x ↦ ∑ i, (A i x * ξ x i + fderiv ℝ (fun y ↦ ξ y i) x (G i x))) U ∧
      ∫ x in U, ∑ i, (A i x * ξ x i + fderiv ℝ (fun y ↦ ξ y i) x (G i x)) = 0 := by
  obtain ⟨δ, hδ, hδU⟩ := hξc.isCompact.exists_cthickening_subset_open hU hξU
  set V := cthickening (δ / 2) (tsupport ξ)
  have hVc : IsCompact V := hξc.isCompact.cthickening
  have hVU : V ⊆ U := (cthickening_mono (by linarith) _).trans hδU
  have hVm : MeasurableSet V := hVc.measurableSet
  set W' := thickening (δ / 2) (tsupport ξ)
  have hW'V : W' ⊆ V := thickening_subset_cthickening _ _
  have hξW' : tsupport ξ ⊆ W' := self_subset_thickening (half_pos hδ) _
  have hμ : volume.restrict V ≪ volume :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  obtain ⟨K, hK⟩ := hξ
  have hvan : ∀ x ∉ V, ∀ i, ξ x i = 0 ∧ fderiv ℝ (fun y ↦ ξ y i) x = 0 := fun x hx i ↦
    have hx' : x ∉ tsupport ξ := fun h' ↦ hx (self_subset_cthickening _ h')
    ⟨by simp [image_eq_zero_of_notMem_tsupport hx'],
      fderiv_of_notMem_tsupport ℝ fun h' ↦ hx' (tsupport_coord_subset ξ i h')⟩
  -- each coordinate
  have hcoord : ∀ i, Integrable (fun x ↦ A i x * ξ x i + fderiv ℝ (fun y ↦ ξ y i) x (G i x))
      (volume.restrict V) ∧
      ∫ x in V, (A i x * ξ x i + fderiv ℝ (fun y ↦ ξ y i) x (G i x)) = 0 := by
    intro i
    obtain ⟨Ki, hKi⟩ := lipschitz_coord hK i
    have hci : HasCompactSupport fun y ↦ ξ y i :=
      hξc.comp_left (g := fun v : E d ↦ v i) (by simp)
    obtain ⟨Ci, hCi⟩ := hci.exists_bound_of_continuous hKi.continuous
    have ha := hA i V hVc hVU
    have hg := hG i V hVc hVU
    refine ⟨integrable_firstOrder_integrand ha hg hKi hCi, ?_⟩
    have hH : ∀ n, ∀ q ∈ D, closedBall q (bumpRad n) ⊆ W' →
        firstOrderFunctional (volume.restrict V) (A i) (G i) (fun x ↦ moll d n (x - q)) = 0 := by
      intro n q hq hball
      rw [← hb i n q hq ((hball.trans hW'V).trans hVU), firstOrderFunctional,
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hVU ?_]
      · rfl
      · intro x hx
        have hxB : x ∉ closedBall q (bumpRad n) := fun h' ↦ hx.2 (hW'V (hball h'))
        have h0 : fderiv ℝ (mollAt n q) x = 0 :=
          fderiv_of_notMem_tsupport ℝ fun h' ↦ hxB (tsupport_mollAt_subset n q h')
        simp [mollAt_eq_zero hxB, h0]
    exact firstOrderFunctional_eq_zero_of_bumps hμ ha hg isOpen_thickening hD hH ⟨Ki, hKi⟩ hci
      ((tsupport_coord_subset ξ i).trans hξW')
  have hIV : IntegrableOn
      (fun x ↦ ∑ i, (A i x * ξ x i + fderiv ℝ (fun y ↦ ξ y i) x (G i x))) V :=
    integrable_finsetSum _ fun i _ ↦ (hcoord i).1
  have hzero : ∀ x ∈ U \ V,
      ∑ i, (A i x * ξ x i + fderiv ℝ (fun y ↦ ξ y i) x (G i x)) = 0 := fun x hx ↦
    Finset.sum_eq_zero fun i _ ↦ by simp [(hvan x hx.2 i).1, (hvan x hx.2 i).2]
  refine ⟨hIV.of_forall_sdiff_eq_zero hU.measurableSet hzero, ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hVU hzero,
    integral_finsetSum _ fun i _ ↦ (hcoord i).1]
  exact Finset.sum_eq_zero fun i _ ↦ (hcoord i).2

/-- `|χ(x, s)| ≤ 1` on `U`, `s > 0`. -/
theorem abs_chi_slice_le_one (h : IsParaInnerVarSolution U Q u w χ) {s : ℝ} (hs : 0 < s)
    {x : E d} (hx : x ∈ U) : |χ (x, s)| ≤ 1 := by
  rcases h.zero_one (x, s) ⟨hx, hs⟩ with h0 | h1 <;> simp [*]

/-- The coefficient `ivCoeffA Q χ e` is integrable on a compact set `K` on which `D(Q²)` is
bounded and `|χ| ≤ 1`. -/
theorem integrableOn_ivCoeffA {Q χ : E d → ℝ} {K : Set (E d)} (hK : IsCompact K) {CQ : ℝ}
    (hCQ : ∀ x ∈ K, ‖fderiv ℝ (fun y ↦ Q y ^ 2) x‖ ≤ CQ) (hχm : Measurable χ)
    (hχ : ∀ x ∈ K, |χ x| ≤ 1) (e : E d) : IntegrableOn (ivCoeffA Q χ e) K := by
  refine IntegrableOn.of_bound hK.measure_lt_top
    ((measurable_fderiv_apply_const ℝ _ e).mul hχm).aestronglyMeasurable (CQ * ‖e‖)
    ((ae_restrict_mem hK.measurableSet).mono fun x hx ↦ ?_)
  rw [ivCoeffA, norm_mul, Real.norm_eq_abs (χ x)]
  calc ‖fderiv ℝ (fun y ↦ Q y ^ 2) x e‖ * |χ x| ≤ CQ * ‖e‖ * 1 := by
        refine mul_le_mul ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hCQ x hx) (norm_nonneg _))) (hχ x hx) (abs_nonneg _) ?_
        exact mul_nonneg ((norm_nonneg _).trans (hCQ x hx)) (norm_nonneg _)
    _ = CQ * ‖e‖ := mul_one _

/-- The coefficient `ivCoeffG Q v χ e` is integrable on a compact set `K` on which `Q²` is
continuous, `∇v` is bounded and `|χ| ≤ 1`. -/
theorem integrableOn_ivCoeffG {Q v χ : E d → ℝ} {K : Set (E d)} (hK : IsCompact K)
    (hQc : ContinuousOn (fun y ↦ Q y ^ 2) K) (hχm : Measurable χ) (hχ : ∀ x ∈ K, |χ x| ≤ 1)
    {B : ℝ} (hB : ∀ x ∈ K, ‖∇ v x‖ ≤ B) (e : E d) : IntegrableOn (ivCoeffG Q v χ e) K := by
  have hKm := hK.measurableSet
  obtain ⟨CQ, hCQ⟩ := hK.exists_bound_of_continuousOn hQc
  have hgm : Measurable fun x ↦ ∇ v x :=
    (toDual ℝ (E d)).symm.continuous.measurable.comp (measurable_fderiv ℝ v)
  have hm : AEStronglyMeasurable (ivCoeffG Q v χ e) (volume.restrict K) := by
    unfold ivCoeffG
    refine AEStronglyMeasurable.sub ?_ ?_
    · refine AEStronglyMeasurable.smul_const ?_ e
      exact (hgm.norm.pow_const 2).aestronglyMeasurable.add
        ((hQc.aestronglyMeasurable hKm).mul hχm.aestronglyMeasurable)
    · exact ((measurable_const.mul (hgm.inner_const (𝕜 := ℝ) (c := e))).smul
        hgm).aestronglyMeasurable
  refine IntegrableOn.of_bound hK.measure_lt_top hm ((B ^ 2 + CQ) * ‖e‖ + 2 * (B * ‖e‖) * B)
    ((ae_restrict_mem hKm).mono fun x hx ↦ ?_)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x hx)
  have hgx : ‖∇ v x‖ ≤ B := hB x hx
  have hχx := hχ x hx
  have hQx : ‖Q x ^ 2‖ ≤ CQ := hCQ x hx
  unfold ivCoeffG
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_pow, norm_norm]; gcongr
    · rw [norm_mul, Real.norm_eq_abs (χ x)]
      calc ‖Q x ^ 2‖ * |χ x| ≤ CQ * 1 := by gcongr; exact (norm_nonneg _).trans hQx
        _ = CQ := mul_one _
  · rw [norm_smul, norm_mul, Real.norm_two]
    gcongr
    exact (norm_inner_le_norm _ _).trans (by gcongr)

/-- The coefficient `sliceCoeffA` is integrable on compact subsets of `U`. -/
theorem integrableOn_sliceCoeffA (h : IsParaInnerVarSolution U Q u w χ) (hU : IsOpen U)
    (hQ : LocallyLipschitzOn U fun y ↦ Q y ^ 2) {s : ℝ} (hs : 0 < s)
    (hmem : MemLp (fun x ↦ w (x, s)) 2 (volume.restrict U)) (e : E d) {K : Set (E d)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IntegrableOn (sliceCoeffA Q u w χ s e) K := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hKm := hK.measurableSet
  obtain ⟨CQ, hCQ⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hQ hK hKU
  obtain ⟨B, hB⟩ := exists_bound_gradₓ_slice h hs hK hKU
  have hχm : Measurable fun y ↦ χ (y, s) := h.meas.comp (measurable_id.prodMk measurable_const)
  have h1 : IntegrableOn (ivCoeffA Q (fun y ↦ χ (y, s)) e) K :=
    integrableOn_ivCoeffA hK hCQ hχm (fun x hx ↦ abs_chi_slice_le_one h hs (hKU hx)) e
  have hw : Integrable (fun x ↦ w (x, s)) (volume.restrict K) :=
    (hmem.mono_measure (Measure.restrict_mono hKU le_rfl)).integrable one_le_two
  have h2 : IntegrableOn (fun x ↦ 2 * inner ℝ e (gradₓ u (x, s)) * w (x, s)) K := by
    refine hw.bdd_mul (c := 2 * (‖e‖ * B)) ?_ ((ae_restrict_mem hKm).mono fun x hx ↦ ?_)
    · exact (measurable_const.mul
        ((measurable_gradₓ_slice u s).const_inner (c := e))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_two]
      gcongr
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hB x hx) (norm_nonneg _))
  exact h1.sub h2

/-- The coefficient `ivCoeffG` of the time slice is integrable on compact subsets of `U`. -/
theorem integrableOn_ivCoeffG_slice (h : IsParaInnerVarSolution U Q u w χ)
    (hQ : LocallyLipschitzOn U fun y ↦ Q y ^ 2) {s : ℝ} (hs : 0 < s) (e : E d)
    {K : Set (E d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    IntegrableOn (ivCoeffG Q (fun y ↦ u (y, s)) (fun y ↦ χ (y, s)) e) K := by
  obtain ⟨B, hB⟩ := exists_bound_gradₓ_slice h hs hK hKU
  have hχm : Measurable fun y ↦ χ (y, s) := h.meas.comp (measurable_id.prodMk measurable_const)
  have hB' : ∀ x ∈ K, ‖∇ (fun y ↦ u (y, s)) x‖ ≤ B := hB
  exact integrableOn_ivCoeffG (Q := Q) hK (hQ.continuousOn.mono hKU) hχm
    (fun x hx ↦ abs_chi_slice_le_one h hs (hKU hx)) hB' e

/-- **The slice identity (4.17) at a fixed time `s`**, from the identities for translated bumps
times coordinate vectors; for Lipschitz fields `ξ` with compact support in `U`. -/
theorem innerVar_slice_of_bumps (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hQ : LocallyLipschitzOn U fun y ↦ Q y ^ 2) {D : Set (E d)} (hD : Dense D) {s : ℝ}
    (hs : 0 < s) (hmem : MemLp (fun x ↦ w (x, s)) 2 (volume.restrict U))
    (hb : ∀ n, ∀ q ∈ D, closedBall q (bumpRad n) ⊆ U → ∀ i : Fin d,
      ∫ x in U, sliceInnerVarIntegrand Q u w χ s (fun y ↦ mollAt n q y • coordVec i) x = 0)
    (ξ : E d → E d) (hξ : ∃ K, LipschitzWith K ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ U) :
    Integrable (sliceInnerVarIntegrand Q u w χ s ξ) (volume.restrict U) ∧
      ∫ x in U, sliceInnerVarIntegrand Q u w χ s ξ x = 0 := by
  set A : Fin d → E d → ℝ := fun i ↦ sliceCoeffA Q u w χ s (coordVec i)
  set G : Fin d → E d → E d := fun i ↦
    ivCoeffG Q (fun y ↦ u (y, s)) (fun y ↦ χ (y, s)) (coordVec i)
  have hb' : ∀ i n, ∀ q ∈ D, closedBall q (bumpRad n) ⊆ U →
      ∫ x in U, (A i x * mollAt n q x + fderiv ℝ (mollAt n q) x (G i x)) = 0 := by
    intro i n q hq hB
    rw [← hb n q hq hB i]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    exact (sliceInnerVarIntegrand_smul_const Q u w χ s
      ((contDiff_mollAt n q).differentiable (by simp) x) _).symm
  obtain ⟨hI, h0⟩ := sum_coord_firstOrder_eq_zero hU hD
    (fun i K hK hKU ↦ integrableOn_sliceCoeffA h hU hQ hs hmem _ hK hKU)
    (fun i K hK hKU ↦ integrableOn_ivCoeffG_slice h hQ hs _ hK hKU) hb' hξ hξc hξU
  obtain ⟨K, hK⟩ := hξ
  have hae : (fun x ↦ ∑ i, (A i x * ξ x i + fderiv ℝ (fun y ↦ ξ y i) x (G i x)))
      =ᵐ[volume.restrict U] sliceInnerVarIntegrand Q u w χ s ξ :=
    ae_restrict_of_ae (hK.ae_differentiableAt.mono fun x hx ↦
      (sliceInnerVarIntegrand_eq_sum_coord Q u w χ s hx).symm)
  exact ⟨hI.congr hae, (integral_congr_ae hae).symm.trans h0⟩

end InnerVar

end LongTime

end PerronVariational

end
