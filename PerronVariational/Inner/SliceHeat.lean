/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.Mollify
public import PerronVariational.Defs.Parabolic
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import PerronVariational.Inner.SliceFubini
import PerronVariational.Inner.SliceTools

/-!
# Time localization of the weak heat equation (4.5)

Proof of **Theorem 3.10**, Step 2 ((4.12)), of F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981: for a parabolic inner variational solution satisfying the weak heat equation
(4.5) in `{u > 0}` (`WeakHeatInPos`), for a.e. `t > 0`,
`∫_U ∂ₜu(t) ζ = -∫_U ∇u(t) · ∇ζ` for every Lipschitz `ζ` with compact support in
`{u(·, t) > 0} ∩ U`.

Definition 3.7 of the paper does not include (4.5); here the flow is assumed to satisfy it, because
Theorem 3.10 is false without it (a time-independent `u = 1 + |x₁|` with `χ ≡ 1` is a parabolic
inner variational solution whose limit is not harmonic in `{u > 0}`), and Step 2 of the paper's
proof uses it.

Proof: test (4.5) with `ρₙ(x - q) ψ(s)` (`q` in a countable dense set, `ψ ∈ C_c^∞` in time) and
apply du Bois-Reymond in time (`ae_setIntegral_slice_eq_zero`); this gives the slice identity for
all translated bumps outside a common null set of times. Conclude by the density of translated
bumps (`firstOrderFunctional_eq_zero_of_bumps`).

## Main results

* `PerronVariational.LongTime.ae_heat_slice`.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient ContDiff

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ}

/-- `∇(f · c) = c ∇f`. -/
theorem gradient_mul_const_eq {f : E d → ℝ} {x : E d} (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    ∇ (fun y ↦ f y * c) x = c • ∇ f x := by
  simp only [gradient, fderiv_mul_const hf c, map_smul]

/-- `⟨v, ∇ζ(x)⟩ = Dζ(x) v`. -/
theorem inner_gradient_eq_fderiv (ζ : E d → ℝ) (x v : E d) :
    inner ℝ v (∇ ζ x) = fderiv ℝ ζ x v := by
  rw [real_inner_comm, gradient, toDual_symm_apply]

/-- The translated mollifier `ρₙ(· - q)`. -/
noncomputable def mollAt (n : ℕ) (q : E d) : E d → ℝ := fun x ↦ moll d n (x - q)

theorem contDiff_mollAt (n : ℕ) (q : E d) : ContDiff ℝ ∞ (mollAt n q) :=
  (contDiff_moll n).comp (contDiff_id.sub contDiff_const)

theorem mollAt_eq_zero {n : ℕ} {q x : E d} (hx : x ∉ closedBall q (bumpRad n)) :
    mollAt n q x = 0 :=
  translate_moll_eq_zero_of_notMem hx

theorem gradient_mollAt_eq_zero {n : ℕ} {q x : E d} (hx : x ∉ closedBall q (bumpRad n)) :
    ∇ (mollAt n q) x = 0 := by
  have hts : tsupport (mollAt n q) ⊆ closedBall q (bumpRad n) :=
    closure_minimal (fun y hy ↦ by_contra fun h' ↦ hy (mollAt_eq_zero h')) isClosed_closedBall
  simp [gradient, fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hts h))]

theorem exists_bound_mollAt (n : ℕ) (q : E d) :
    ∃ C, ∀ x, |mollAt n q x| ≤ C ∧ ‖∇ (mollAt n q) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_moll (d := d) n
  refine ⟨C, fun x ↦ ⟨(hC (x - q)).1, ?_⟩⟩
  have : fderiv ℝ (mollAt n q) x = fderiv ℝ (moll d n) (x - q) := by
    rw [show mollAt n q = fun x ↦ moll d n (x - q) from rfl, fderiv_comp_sub]
  simpa [gradient, this] using (hC (x - q)).2

section Heat

variable {U : Set (E d)} {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ}

/-- Integrability of `w f + ⟨∇u, G⟩` on compact subsets of `U_∞`, for continuous `f`, `G`. -/
theorem integrableOn_heat_integrand (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    {K : Set (E d × ℝ)} (hK : IsCompact K) (hKU : K ⊆ UInf U) {f : E d × ℝ → ℝ}
    {G : E d × ℝ → E d} (hf : Continuous f) (hG : Continuous G) :
    IntegrableOn (fun p ↦ w p * f p + inner ℝ (gradₓ u p) (G p)) K := by
  obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨CG, hCG⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have hw : IntegrableOn w K := h.timeDeriv.2.1.integrableOn_compact_subset hKU hK
  have hg : IntegrableOn (gradₓ u) K :=
    (IsParaInnerVarSolution.locallyIntegrableOn_gradₓ hU h).integrableOn_compact_subset hKU hK
  refine Integrable.add ?_ ?_
  · exact hw.mul_bdd hf.aestronglyMeasurable
      ((ae_restrict_mem hK.measurableSet).mono fun p hp ↦ hCf p hp)
  · refine (hg.norm.mul_const CG).mono' (hg.aestronglyMeasurable.inner
      hG.aestronglyMeasurable) ((ae_restrict_mem hK.measurableSet).mono fun p hp ↦ ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hCG p hp) (norm_nonneg _))

/-- The set of times `s` with `B̄(q, rₙ) × {s} ⊆ {u > 0} ∩ U_∞`. -/
def bumpTimes (U : Set (E d)) (u : E d × ℝ → ℝ) (n : ℕ) (q : E d) : Set ℝ :=
  {s | ∀ x ∈ closedBall q (bumpRad n), (x, s) ∈ posSetP u (UInf U)}

theorem isOpen_posSetP (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ) :
    IsOpen (posSetP u (UInf U)) :=
  h.continuousOn.isOpen_inter_preimage (hU.prod isOpen_Ioi) isOpen_Ioi

theorem bumpTimes_subset (n : ℕ) (q : E d) : bumpTimes U u n q ⊆ Ioi 0 := fun _ hs ↦
  (hs q (mem_closedBall_self (bumpRad_pos n).le)).1.2

/-- The slice identity for one translated bump, for a.e. time. -/
theorem ae_heat_slice_bump (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hheat : WeakHeatInPos U u w) (n : ℕ) (q : E d) :
    ∀ᵐ s, s ∈ bumpTimes U u n q →
      ∫ x in U, (w (x, s) * mollAt n q x + inner ℝ (gradₓ u (x, s)) (∇ (mollAt n q) x)) = 0 := by
  set T := bumpTimes U u n q
  set B := closedBall q (bumpRad n)
  have hT : IsOpen T := isOpen_setOf_forall_prod_mem (isCompact_closedBall q _)
    (isOpen_posSetP hU h)
  have hcm := (contDiff_mollAt n q).continuous
  have hcg : Continuous (∇ (mollAt n q)) :=
    (toDual ℝ (E d)).symm.continuous.comp ((contDiff_mollAt n q).continuous_fderiv (by simp))
  set H : E d × ℝ → ℝ := fun p ↦ w p * mollAt n q p.1 + inner ℝ (gradₓ u p) (∇ (mollAt n q) p.1)
  have hvan : ∀ p : E d × ℝ, p.1 ∉ B → H p = 0 := fun p hp ↦ by
    simp only [H, mollAt_eq_zero hp, gradient_mollAt_eq_zero hp, mul_zero, inner_zero_right,
      add_zero]
  -- `H` is integrable on `U × J` for compact `J ⊆ T`
  have hint : ∀ J ⊆ T, IsCompact J → IntegrableOn H (U ×ˢ J) := by
    intro J hJT hJ
    have hsub : B ×ˢ J ⊆ UInf U := fun p hp ↦ (hJT hp.2 p.1 hp.1).1
    have h1 := integrableOn_heat_integrand hU h ((isCompact_closedBall q _).prod hJ) hsub
      (hcm.comp continuous_fst) (hcg.comp continuous_fst)
    refine h1.of_forall_sdiff_eq_zero (hU.measurableSet.prod hJ.measurableSet) fun p hp ↦
      hvan p fun hB ↦ hp.2 ⟨hB, hp.1.2⟩
  refine ae_setIntegral_slice_eq_zero hU.measurableSet measurableSet_Ioi hT
    (bumpTimes_subset n q) hint fun ψ hψs hψc hψT ↦ ?_
  -- test (4.5) with `φ(x, s) = ρ(x - q) ψ(s)`
  set φ : E d × ℝ → ℝ := fun p ↦ mollAt n q p.1 * ψ p.2
  have hφs : ContDiff ℝ ∞ φ :=
    ((contDiff_mollAt n q).comp contDiff_fst).mul (hψs.comp contDiff_snd)
  have hsuppφ : ∀ p ∉ B ×ˢ tsupport ψ, φ p = 0 := fun p hp ↦ by
    rcases not_and_or.1 hp with h1 | h1
    · simp [φ, mollAt_eq_zero h1]
    · simp [φ, image_eq_zero_of_notMem_tsupport h1]
  have hKc : IsCompact (B ×ˢ tsupport ψ) := (isCompact_closedBall q _).prod hψc
  have hφc : HasCompactSupport φ := HasCompactSupport.intro hKc hsuppφ
  have htsφ : tsupport φ ⊆ B ×ˢ tsupport ψ :=
    closure_minimal (fun p hp ↦ by_contra fun h' ↦ hp (hsuppφ p h')) hKc.isClosed
  have hKU : B ×ˢ tsupport ψ ⊆ posSetP u (UInf U) := fun p hp ↦ hψT hp.2 p.1 hp.1
  obtain ⟨Kφ, hKφ⟩ := hφs.lipschitzWith_of_hasCompactSupport hφc (by simp)
  have hW := hheat φ ⟨Kφ, hKφ⟩ hφc (htsφ.trans hKU)
  have hgφ : ∀ p : E d × ℝ, gradₓ φ p = ψ p.2 • ∇ (mollAt n q) p.1 := fun p ↦
    gradient_mul_const_eq ((contDiff_mollAt n q).differentiable (by simp) p.1) (ψ p.2)
  have hfun : (fun p : E d × ℝ ↦ ψ p.2 * H p) =
      fun p ↦ w p * φ p + inner ℝ (gradₓ u p) (gradₓ φ p) := by
    ext p
    simp only [H, φ, hgφ, inner_smul_right]
    ring
  -- integrability on `U_∞`
  have hKsub : B ×ˢ tsupport ψ ⊆ UInf U := hKU.trans fun p hp ↦ hp.1
  have hI1 : IntegrableOn (fun p ↦ w p * φ p) (UInf U) := by
    have := integrableOn_heat_integrand hU h hKc hKsub hφs.continuous
      (continuous_const : Continuous fun _ : E d × ℝ ↦ (0 : E d))
    simp only [inner_zero_right, add_zero] at this
    exact this.of_forall_sdiff_eq_zero (hU.measurableSet.prod measurableSet_Ioi) fun p hp ↦ by
      rw [hsuppφ p hp.2, mul_zero]
  have hI2 : IntegrableOn (fun p ↦ inner ℝ (gradₓ u p) (gradₓ φ p)) (UInf U) := by
    have := integrableOn_heat_integrand hU h hKc hKsub
      (continuous_const : Continuous fun _ : E d × ℝ ↦ (0 : ℝ))
      (show Continuous fun p : E d × ℝ ↦ ψ p.2 • ∇ (mollAt n q) p.1 from
        (hψs.continuous.comp continuous_snd).smul (hcg.comp continuous_fst))
    simp only [mul_zero, zero_add, ← hgφ] at this
    refine this.of_forall_sdiff_eq_zero (hU.measurableSet.prod measurableSet_Ioi) fun p hp ↦ ?_
    rcases not_and_or.1 hp.2 with h1 | h1
    · simp [hgφ, gradient_mollAt_eq_zero h1]
    · simp [hgφ, image_eq_zero_of_notMem_tsupport h1]
  change ∫ p in UInf U, ψ p.2 * H p = 0
  rw [hfun, integral_add hI1 hI2, hW, neg_add_cancel]

/-- The time slice `x ↦ ∇u(x, s)` is measurable. -/
theorem measurable_gradₓ_slice (u : E d × ℝ → ℝ) (s : ℝ) :
    Measurable fun x ↦ gradₓ u (x, s) :=
  (toDual ℝ (E d)).symm.continuous.measurable.comp (measurable_fderiv ℝ (fun y ↦ u (y, s)))

/-- The time slice `x ↦ ∇u(x, s)` is bounded on compact subsets of `U` (`s > 0`). -/
theorem exists_bound_gradₓ_slice (h : IsParaInnerVarSolution U Q u w χ) {s : ℝ} (hs : 0 < s)
    {V : Set (E d)} (hV : IsCompact V) (hVU : V ⊆ U) :
    ∃ B, ∀ x ∈ V, ‖gradₓ u (x, s)‖ ≤ B := by
  refine GMTFoundations.exists_bound_of_isCompact hV fun x hx ↦ ?_
  obtain ⟨K, N, hN, hK⟩ := h.locLipₓ (x, s) ⟨hVU hx, hs⟩
  obtain ⟨r, hr, hbound⟩ := norm_gradₓ_le_of_lip hN hK
  refine ⟨max K 0, ?_⟩
  have : ∀ᶠ y in 𝓝 x, (y, s) ∈ ball (x, s) r :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr)
  exact this.mono fun y hy ↦ hbound _ hy

/-- The time slice `y ↦ u(y, s)` is continuous on `U` (`s > 0`). -/
theorem continuousOn_slice (h : IsParaInnerVarSolution U Q u w χ) {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun y ↦ u (y, s)) U :=
  h.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
    fun _ hx ↦ ⟨hx, hs⟩

/-- **The slice identity at a fixed time `s`**, from the identities for translated bumps. -/
theorem heat_slice_of_bumps (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    {D : Set (E d)} (hD : Dense D) {s : ℝ} (hs : 0 < s)
    (hmem : MemLp (fun x ↦ w (x, s)) 2 (volume.restrict U))
    (hb : ∀ n, ∀ q ∈ D, s ∈ bumpTimes U u n q →
      ∫ x in U, (w (x, s) * mollAt n q x + inner ℝ (gradₓ u (x, s)) (∇ (mollAt n q) x)) = 0)
    (ζ : E d → ℝ) (hζ : ∃ K, LipschitzWith K ζ) (hζc : HasCompactSupport ζ)
    (hζW : tsupport ζ ⊆ posSet (fun y ↦ u (y, s)) U) :
    ∫ x in U, w (x, s) * ζ x = -∫ x in U, inner ℝ (gradₓ u (x, s)) (∇ ζ x) := by
  set W := posSet (fun y ↦ u (y, s)) U
  have hWo : IsOpen W := (continuousOn_slice h hs).isOpen_inter_preimage hU isOpen_Ioi
  have hWU : W ⊆ U := fun x hx ↦ hx.1
  obtain ⟨δ, hδ, hδW⟩ := hζc.isCompact.exists_cthickening_subset_open hWo hζW
  set V := cthickening (δ / 2) (tsupport ζ)
  have hVc : IsCompact V := hζc.isCompact.cthickening
  have hVW : V ⊆ W := (cthickening_mono (by linarith) _).trans hδW
  have hVU : V ⊆ U := hVW.trans hWU
  have hVm : MeasurableSet V := hVc.measurableSet
  set W' := thickening (δ / 2) (tsupport ζ)
  have hW'V : W' ⊆ V := thickening_subset_cthickening _ _
  have hζW' : tsupport ζ ⊆ W' := self_subset_thickening (half_pos hδ) _
  have : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.2 hVc.measure_lt_top.ne
  set a : E d → ℝ := fun x ↦ w (x, s)
  set g : E d → E d := fun x ↦ gradₓ u (x, s)
  have ha : Integrable a (volume.restrict V) :=
    (hmem.mono_measure (Measure.restrict_mono hVU le_rfl)).integrable one_le_two
  obtain ⟨B, hB⟩ := exists_bound_gradₓ_slice h hs hVc hVU
  have hg : Integrable g (volume.restrict V) :=
    IntegrableOn.of_bound hVc.measure_lt_top (measurable_gradₓ_slice u s).aestronglyMeasurable B
      ((ae_restrict_mem hVm).mono fun x hx ↦ hB x hx)
  have hμ : volume.restrict V ≪ volume :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hH : ∀ n, ∀ q ∈ D, closedBall q (bumpRad n) ⊆ W' →
      firstOrderFunctional (volume.restrict V) a g (fun x ↦ moll d n (x - q)) = 0 := by
    intro n q hq hball
    have hT : s ∈ bumpTimes U u n q := fun x hx ↦
      ⟨⟨hVU (hW'V (hball hx)), hs⟩, (hVW (hW'V (hball hx))).2⟩
    rw [← hb n q hq hT, firstOrderFunctional,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hVU ?_]
    · refine setIntegral_congr_fun hVm fun x _ ↦ ?_
      simp only [a, g, inner_gradient_eq_fderiv]
      rfl
    · intro x hx
      have hxB : x ∉ closedBall q (bumpRad n) := fun h' ↦ hx.2 (hW'V (hball h'))
      simp [mollAt_eq_zero hxB, gradient_mollAt_eq_zero hxB]
  have hΨ := firstOrderFunctional_eq_zero_of_bumps hμ ha hg isOpen_thickening hD hH hζ hζc hζW'
  obtain ⟨K, hK⟩ := hζ
  obtain ⟨Cζ, hCζ⟩ := hζc.exists_bound_of_continuous hK.continuous
  have hvan : ∀ x ∉ V, ζ x = 0 ∧ fderiv ℝ ζ x = 0 := fun x hx ↦
    have hx' : x ∉ tsupport ζ := fun h' ↦ hx (self_subset_cthickening _ h')
    ⟨image_eq_zero_of_notMem_tsupport hx', fderiv_of_notMem_tsupport ℝ hx'⟩
  have hI1 : Integrable (fun x ↦ a x * ζ x) (volume.restrict V) :=
    ha.mul_bdd hK.continuous.aestronglyMeasurable (Eventually.of_forall hCζ)
  have hI2 : Integrable (fun x ↦ fderiv ℝ ζ x (g x)) (volume.restrict V) := by
    refine (hg.norm.const_mul K).mono'
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((measurable_fderiv ℝ ζ).aestronglyMeasurable.prodMk hg.aestronglyMeasurable))
      (Eventually.of_forall fun x ↦ ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hK) (norm_nonneg _))
  unfold firstOrderFunctional at hΨ
  rw [integral_add hI1 hI2] at hΨ
  have e1 : ∫ x in U, w (x, s) * ζ x = ∫ x in V, a x * ζ x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hVU fun x hx ↦ by
      simp [(hvan x hx.2).1]
  have e2 : ∫ x in U, inner ℝ (gradₓ u (x, s)) (∇ ζ x) = ∫ x in V, fderiv ℝ ζ x (g x) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hVU fun x hx ↦ by
      simp [(hvan x hx.2).2]]
    exact setIntegral_congr_fun hVm fun x _ ↦ inner_gradient_eq_fderiv ζ x _
  rw [e1, e2]
  linarith

end Heat

end LongTime

end PerronVariational

end
