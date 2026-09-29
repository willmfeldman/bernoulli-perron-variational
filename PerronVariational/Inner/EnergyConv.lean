/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.WeakHeat
public import PerronVariational.Inner.Common
public import PerronVariational.Statements.Intermediate
import GMTFoundations.Sobolev.Cutoff
import GMTFoundations.Sobolev.L2Inner
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Inner.StrongGrad
import PerronVariational.Inner.WeakGrad
import PerronVariational.Semilinear.Profiles

/-!
# Lemma 4.2: strong convergence of the spatial gradients

Tools for the energy argument of Lemma 4.2 of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981:
* test functions `F η` with `F` locally Lipschitz in space and `η ∈ C¹_c` (`isSliceLipTest_mul`);
* the gradient of `F η` and of functions with a local minimum;
* strong × weak products of vector fields in `L²`;
* smooth cut-offs.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient RealInnerProductSpace Manifold

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-! ### Generic helpers -/

/-- A function locally bounded above near every point of a compact set is bounded above on it. -/
theorem exists_bound_of_forall_nhds {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → ℝ} (h : ∀ p ∈ K, ∃ c : ℝ, ∃ V ∈ 𝓝 p, ∀ q ∈ V, f q ≤ c) :
    ∃ C : ℝ, ∀ q ∈ K, f q ≤ C := by
  choose c V hV hc using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' V hV
  refine ⟨∑ i ∈ t, |c i i.2|, fun q hq ↦ ?_⟩
  obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.1 (ht hq)
  exact (hc _ _ q hqi).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j : K ↦ |c j j.2|) (fun j _ ↦ abs_nonneg _) hi))

/-- `F η` is continuous if `F` is continuous on an open set containing `spt η`. -/
theorem continuous_mul_of_tsupport_subset {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (hΩ : IsOpen Ω) {F η : X → ℝ} (hF : ContinuousOn F Ω) (hη : Continuous η)
    (hηs : tsupport η ⊆ Ω) : Continuous fun p ↦ F p * η p := by
  refine continuous_iff_continuousAt.2 fun q ↦ ?_
  by_cases hq : q ∈ Ω
  · exact (hF.continuousAt (hΩ.mem_nhds hq)).mul hη.continuousAt
  · have hq' : q ∉ tsupport η := fun h ↦ hq (hηs h)
    have hev : (fun p ↦ F p * η p) =ᶠ[𝓝 q] fun _ ↦ 0 := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hq'] with p hp
      simp [image_eq_zero_of_notMem_tsupport hp]
    exact continuousAt_const.congr hev.symm

theorem dist_prodMk_right {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (y z : α)
    (t : β) : dist (y, t) (z, t) = dist y z := by
  simp [Prod.dist_eq]

/-- `‖∇ₓφ(q)‖ ≤ C` if the time slice of `φ` is `C`-Lipschitz near `q`. -/
theorem norm_gradₓ_le_of_lipschitzOn {φ : E d × ℝ → ℝ} {q : E d × ℝ} {s : Set (E d)}
    (hs : s ∈ 𝓝 q.1) {C : ℝ≥0} (h : LipschitzOnWith C (fun y ↦ φ (y, q.2)) s) :
    ‖gradₓ φ q‖ ≤ C := by
  rw [gradₓ, gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitzOn ℝ hs h

/-- `∇ₓφ(q) = 0` at a local minimum of the time slice. -/
theorem gradₓ_eq_zero_of_isLocalMin {φ : E d × ℝ → ℝ} {q : E d × ℝ}
    (h : IsLocalMin (fun y ↦ φ (y, q.2)) q.1) : gradₓ φ q = 0 := by
  rw [gradₓ, gradient, h.fderiv_eq_zero, map_zero]

/-- Product rule for `∇ₓ`. -/
theorem gradₓ_mul {F η : E d × ℝ → ℝ} {q : E d × ℝ}
    (hF : DifferentiableAt ℝ (fun y ↦ F (y, q.2)) q.1)
    (hη : DifferentiableAt ℝ (fun y ↦ η (y, q.2)) q.1) :
    gradₓ (fun p ↦ F p * η p) q = η q • gradₓ F q + F q • gradₓ η q := by
  simp only [gradₓ, gradient]
  rw [fderiv_fun_mul hF hη, map_add, map_smul, map_smul, add_comm]

/-- The time slice of a `C¹` function is differentiable. -/
theorem differentiableAt_slice {η : E d × ℝ → ℝ} (hη : ContDiff ℝ 1 η) (q : E d × ℝ) :
    DifferentiableAt ℝ (fun y ↦ η (y, q.2)) q.1 :=
  ((hη.differentiable one_ne_zero) (q.1, q.2)).comp q.1
    ((differentiableAt_id).prodMk (differentiableAt_const _))

/-! ### Local Lipschitz bounds in space -/

/-- Spatial local Lipschitz bound from a continuous spatial gradient (mean value theorem). -/
theorem locLipₓ_of_gradₓ {U : Set (E d)} (hU : IsOpen U) {F : E d × ℝ → ℝ}
    (hd : ∀ t > 0, DifferentiableOn ℝ (fun x ↦ F (x, t)) U)
    (hg : ContinuousOn (gradₓ F) (UInf U)) : LocLipₓ (UInf U) F := by
  intro p hp
  have hΩ : IsOpen (UInf U) := hU.prod isOpen_Ioi
  have hW : ∀ᶠ q in 𝓝 p, ‖gradₓ F q‖ < ‖gradₓ F p‖ + 1 :=
    (continuous_norm.continuousAt.comp (hg.continuousAt (hΩ.mem_nhds hp))).eventually
      (gt_mem_nhds (lt_add_one _))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hW (hΩ.mem_nhds hp))
  refine ⟨‖gradₓ F p‖ + 1, ball p r, ball_mem_nhds p hr, fun q hq q' hq' ht ↦ ?_⟩
  set t := q.2
  have hB : ∀ y ∈ ball p.1 r, (y, t) ∈ ball p r := fun y hy ↦ by
    rw [← ball_prod_same]
    exact ⟨hy, by rw [← ball_prod_same] at hq; exact hq.2⟩
  have hdiff : ∀ y ∈ ball p.1 r, DifferentiableAt ℝ (fun x ↦ F (x, t)) y := fun y hy ↦ by
    have h := (hball (hB y hy)).2
    exact ((hd t h.2).differentiableAt (hU.mem_nhds h.1))
  have hbd : ∀ y ∈ ball p.1 r, ‖fderiv ℝ (fun x ↦ F (x, t)) y‖ ≤ ‖gradₓ F p‖ + 1 := by
    intro y hy
    have h := (hball (hB y hy)).1
    have : ‖gradₓ F (y, t)‖ = ‖fderiv ℝ (fun x ↦ F (x, t)) y‖ := by
      rw [gradₓ, gradient, LinearIsometryEquiv.norm_map]
    exact this ▸ (le_of_lt h)
  have hq1 : q.1 ∈ ball p.1 r := by
    rw [← ball_prod_same] at hq
    exact hq.1
  have hq'1 : q'.1 ∈ ball p.1 r := by
    rw [← ball_prod_same] at hq'
    exact hq'.1
  have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbd (convex_ball _ _) hq'1 hq1
  have hq'eq : q' = (q'.1, t) := by rw [ht]
  rw [hq'eq, ← Real.norm_eq_abs]
  exact this

/-- The positive part `(u - δ)₊` inherits spatial local Lipschitz bounds. -/
theorem LocLipₓ.posPart_sub {Ω : Set (E d × ℝ)} {u : E d × ℝ → ℝ} (h : LocLipₓ Ω u) (δ : ℝ) :
    LocLipₓ Ω (fun p ↦ max (u p - δ) 0) := by
  intro p hp
  obtain ⟨K, N, hN, hK⟩ := h p hp
  refine ⟨K, N, hN, fun q hq q' hq' ht ↦ ?_⟩
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have := hK q hq q' hq' ht
  calc |u q - δ - (u q' - δ)| = |u q - u q'| := by ring_nf
    _ ≤ _ := this

/-- **Products `F η` are admissible test functions**: `F` continuous and locally Lipschitz in
space on an open `Ω`, `η ∈ C¹_c(Ω)`. -/
theorem isSliceLipTest_mul {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {F η : E d × ℝ → ℝ}
    (hF : ContinuousOn F Ω) (hFl : LocLipₓ Ω F) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω) :
    IsSliceLipTest (fun p ↦ F p * η p) := by
  obtain ⟨Kη, hKη⟩ := hη.lipschitzWith_of_hasCompactSupport hηc one_ne_zero
  obtain ⟨Mη, hMη⟩ := hηc.exists_bound_of_continuous hη.continuous
  set φ : E d × ℝ → ℝ := fun p ↦ F p * η p with hφdef
  have hcont : Continuous φ := continuous_mul_of_tsupport_subset hΩ hF hη.continuous hηs
  have hsl : ∀ q : E d × ℝ, Continuous fun y : E d ↦ (y, q.2) := fun q ↦
    continuous_id.prodMk continuous_const
  have hloc : ∀ p, ∃ c : ℝ, ∃ V : Set (E d × ℝ), IsOpen V ∧ p ∈ V ∧ ∀ q ∈ V,
      LipschitzOnWith (Real.toNNReal c) (fun y ↦ φ (y, q.2)) {y | (y, q.2) ∈ V} := by
    intro p
    by_cases hp : p ∈ Ω
    · obtain ⟨L, N, hN, hL⟩ := hFl p hp
      have hFb : ∀ᶠ q in 𝓝 p, |F q| < |F p| + 1 :=
        (continuous_abs.continuousAt.comp (hF.continuousAt (hΩ.mem_nhds hp))).eventually
          (gt_mem_nhds (lt_add_one _))
      set V := interior (N ∩ {q | |F q| < |F p| + 1}) with hVdef
      refine ⟨max L 0 * max Mη 0 + (|F p| + 1) * Kη, V, isOpen_interior,
        mem_interior_iff_mem_nhds.2 (inter_mem hN hFb), fun q hq ↦ ?_⟩
      refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
      have hy' := interior_subset hy
      have hz' := interior_subset hz
      have h1 : |F (y, q.2) - F (z, q.2)| ≤ max L 0 * ‖y - z‖ :=
        (hL _ hy'.1 _ hz'.1 rfl).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (norm_nonneg _))
      have h2 : |η (y, q.2) - η (z, q.2)| ≤ Kη * ‖y - z‖ := by
        have := hKη.dist_le_mul (y, q.2) (z, q.2)
        rwa [dist_prodMk_right, Real.dist_eq, dist_eq_norm] at this
      have h3 : |η (y, q.2)| ≤ max Mη 0 := by
        have := hMη (y, q.2)
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)
      have h4 : |F (z, q.2)| ≤ |F p| + 1 := le_of_lt hz'.2
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
      calc |F (y, q.2) * η (y, q.2) - F (z, q.2) * η (z, q.2)|
          = |(F (y, q.2) - F (z, q.2)) * η (y, q.2) +
              F (z, q.2) * (η (y, q.2) - η (z, q.2))| := by ring_nf
        _ ≤ |F (y, q.2) - F (z, q.2)| * |η (y, q.2)| +
              |F (z, q.2)| * |η (y, q.2) - η (z, q.2)| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul]
        _ ≤ (max L 0 * ‖y - z‖) * max Mη 0 + (|F p| + 1) * (Kη * ‖y - z‖) := by
            gcongr
        _ = (max L 0 * max Mη 0 + (|F p| + 1) * Kη) * ‖y - z‖ := by ring
    · have hp' : p ∉ tsupport η := fun h ↦ hp (hηs h)
      refine ⟨0, (tsupport η)ᶜ, (isClosed_tsupport η).isOpen_compl, hp', fun q _ ↦ ?_⟩
      refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
      simp only [mem_setOf_eq, mem_compl_iff] at hy hz
      simp [φ, image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hz]
  refine ⟨hcont, fun t x ↦ ?_, ?_⟩
  · obtain ⟨c, V, hVo, hpV, hV⟩ := hloc (x, t)
    exact ⟨_, _, (hVo.preimage (hsl (x, t))).mem_nhds hpV, hV (x, t) hpV⟩
  · have hK : IsCompact (tsupport η) := hηc
    obtain ⟨C, hC⟩ := exists_bound_of_forall_nhds hK (f := fun q ↦ ‖gradₓ φ q‖)
      fun p _ ↦ by
        obtain ⟨c, V, hVo, hpV, hV⟩ := hloc p
        refine ⟨Real.toNNReal c, V, hVo.mem_nhds hpV, fun q hq ↦ ?_⟩
        exact norm_gradₓ_le_of_lipschitzOn ((hVo.preimage (hsl q)).mem_nhds hq) (hV q hq)
    refine ⟨max C 0, fun q ↦ ?_⟩
    by_cases hq : q ∈ tsupport η
    · exact (hC q hq).trans (le_max_left _ _)
    · have hq' : q ∉ tsupport φ := fun h ↦ hq ((tsupport_mul_subset_right) h)
      rw [gradₓ_eq_zero_of_notMem hq', norm_zero]
      exact le_max_right _ _

/-! ### Strong × weak products of vector fields -/

/-- Strong × weak: `∫ ⟪a_n, b_n⟫ → ∫ ⟪a, b⟫` if `a_n ⇀ a` (tested against `b`), `‖a_n‖ ≤ B`, and
`b_n → b` strongly in `L²`. -/
theorem tendsto_integral_inner_of_weak_strong {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {μ : Measure X} {a b : ℕ → X → F}
    {a₀ b₀ : X → F} (ha : ∀ n, MemLp (a n) 2 μ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ n, eLpNorm (a n) 2 μ ≤ ENNReal.ofReal B)
    (hweak : Tendsto (fun n ↦ ∫ x, ⟪a n x, b₀ x⟫ ∂μ) atTop (𝓝 (∫ x, ⟪a₀ x, b₀ x⟫ ∂μ)))
    (hb : ∀ n, MemLp (b n) 2 μ) (hb₀ : MemLp b₀ 2 μ)
    (hbc : Tendsto (fun n ↦ eLpNorm (b n - b₀) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ⟪a n x, b n x⟫ ∂μ) atTop (𝓝 (∫ x, ⟪a₀ x, b₀ x⟫ ∂μ)) := by
  have hsplit : ∀ n, ∫ x, ⟪a n x, b n x⟫ ∂μ =
      ∫ x, ⟪a n x, (b n - b₀) x⟫ ∂μ + ∫ x, ⟪a n x, b₀ x⟫ ∂μ := by
    intro n
    rw [← integral_add (GMTFoundations.integrable_inner_of_memLp (ha n) ((hb n).sub hb₀))
      (GMTFoundations.integrable_inner_of_memLp (ha n) hb₀)]
    congr 1
    ext x
    rw [← inner_add_right, Pi.sub_apply, sub_add_cancel]
  have hsmall : Tendsto (fun n ↦ ∫ x, ⟪a n x, (b n - b₀) x⟫ ∂μ) atTop (𝓝 0) := by
    have hbd : ∀ n, |∫ x, ⟪a n x, (b n - b₀) x⟫ ∂μ| ≤ B * (eLpNorm (b n - b₀) 2 μ).toReal := by
      intro n
      refine (GMTFoundations.abs_integral_inner_le (ha n) ((hb n).sub hb₀)).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
      exact ENNReal.toReal_le_of_le_ofReal hB0 (hB n)
    have hto : Tendsto (fun n ↦ B * (eLpNorm (b n - b₀) 2 μ).toReal) atTop (𝓝 0) := by
      have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hbc).const_mul B
      simpa using this
    exact squeeze_zero_norm (fun n ↦ by rw [Real.norm_eq_abs]; exact hbd n) hto
  have := hsmall.add hweak
  rw [zero_add] at this
  exact this.congr fun n ↦ (hsplit n).symm

/-! ### Smooth cut-offs -/

/-- A `C¹` cut-off `0 ≤ η ≤ 1`, `η = 1` on a compact `K`, with compact support in an open `Ω`
(the `C¹` weakening of `GMTFoundations.exists_smooth_cutoff`). -/
theorem exists_cutoff {K Ω : Set (E d × ℝ)} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ η : E d × ℝ → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧ tsupport η ⊆ Ω ∧
      (∀ p, 0 ≤ η p ∧ η p ≤ 1) ∧ ∀ p ∈ K, η p = 1 := by
  obtain ⟨η, hη, h⟩ := GMTFoundations.exists_smooth_cutoff hK hΩ hKΩ
  exact ⟨η, hη.of_le (by exact_mod_cast le_top), h⟩

/-! ### `C¹` test functions -/

theorem gradₓ_eq_of_contDiff {η : E d × ℝ → ℝ} (hη : ContDiff ℝ 1 η) (p : E d × ℝ) :
    gradₓ η p = (InnerProductSpace.toDual ℝ (E d)).symm
      ((fderiv ℝ η p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) := by
  have h1 : HasFDerivAt (fun y : E d ↦ (y, p.2)) (ContinuousLinearMap.inl ℝ (E d) ℝ) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have h2 : HasFDerivAt η (fderiv ℝ η p) (p.1, p.2) :=
    (hη.differentiable one_ne_zero p).hasFDerivAt
  have h3 : HasFDerivAt (fun y ↦ η (y, p.2))
      ((fderiv ℝ η p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) p.1 := h2.comp p.1 h1
  rw [gradₓ, gradient, h3.fderiv]

theorem continuous_gradₓ {η : E d × ℝ → ℝ} (hη : ContDiff ℝ 1 η) : Continuous (gradₓ η) := by
  rw [show gradₓ η = _ from funext (gradₓ_eq_of_contDiff hη)]
  exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp
    ((hη.continuous_fderiv one_ne_zero).clm_comp continuous_const)

/-! ### The `ε`-level energy inequality -/

/-- Time integration by parts for `v²/2`: `∫ ∂ₜv (v η) = -∫ (v²/2) ∂ₜη`. -/
theorem integral_dₜ_mul_self {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ} {β : ℝ → ℝ}
    {ε : ℝ} {v η : E d × ℝ → ℝ} (hv : IsSemilinearSolOn U Q β ε (Ioi 0) v)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ UInf U) :
    ∫ p in UInf U, dₜ v p * (v p * η p) = -∫ p in UInf U, v p ^ 2 / 2 * dₜ η p := by
  have hm : MeasurableSet (UInf U) := (hU.prod isOpen_Ioi).measurableSet
  set f : E d × ℝ → ℝ := fun p ↦ v p ^ 2 / 2 with hf
  have hd : ∀ p ∈ UInf U, HasDerivAt (fun s ↦ f (p.1, s)) (v p * dₜ v p) p.2 := by
    intro p hp
    have h := (hv.2.2.2.2.1 p hp).hasDerivAt
    have h2 := (h.pow 2).div_const 2
    convert h2 using 1
    simp only [dₜ, Prod.mk.eta]
    push_cast
    ring
  have hdf : ∀ p ∈ UInf U, dₜ f p = v p * dₜ v p := fun p hp ↦ (hd p hp).deriv
  have key := integral_mul_dₜ_eq_neg (U := U) (f := f)
    (fun p hp ↦ (hdf p hp).symm ▸ hd p hp) ((hv.1.pow 2).div_const 2)
    ((hv.1.mul hv.2.2.2.2.2.1).congr fun p hp ↦ hdf p hp) hη hηc hηs
  rw [key, neg_neg]
  refine setIntegral_congr_fun hm fun p hp ↦ ?_
  rw [hdf p hp]
  ring

/-- **The `ε`-level energy inequality** (proof of Lemma 4.2, before (4.3)): for a nonnegative
classical solution `v` of (3.4) and `0 ≤ η ∈ C¹_c(U_∞)`,
`∫ η |∇v|² ≤ ∫ (v²/2) ∂ₜη - ∫ v ∇v · ∇η` (multiply by `v η`, drop `Q² β_ε(v) v η ≥ 0`). -/
theorem energy_ineq_semilinear (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ}
    (hε : 0 < ε) {v η : E d × ℝ → ℝ} (hv : IsSemilinearSolOn S.U S.Q β ε (Ioi 0) v)
    (hv0 : ∀ p ∈ UInf S.U, 0 ≤ v p) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ UInf S.U) (hη0 : ∀ p, 0 ≤ η p) :
    ∫ p in UInf S.U, η p * ‖gradₓ v p‖ ^ 2 ≤
      (∫ p in UInf S.U, v p ^ 2 / 2 * dₜ η p) -
        ∫ p in UInf S.U, v p * ⟪gradₓ v p, gradₓ η p⟫ := by
  have hU := S.isOpen
  set Ω := UInf S.U with hΩdef
  have hΩ : IsOpen Ω := hU.prod isOpen_Ioi
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  set K := tsupport η with hKdef
  have hK : IsCompact K := hηc
  have hη0' : ∀ p ∉ K, η p = 0 := fun p hp ↦ image_eq_zero_of_notMem_tsupport hp
  have hgη0 : ∀ p ∉ K, gradₓ η p = 0 := fun p hp ↦ gradₓ_eq_zero_of_notMem hp
  have hdη0 : ∀ p ∉ K, dₜ η p = 0 := fun p hp ↦ dₜ_eq_zero_of_notMem hη hp
  have hvc : ContinuousOn v Ω := hv.1
  have hgv : ContinuousOn (gradₓ v) Ω := hv.2.2.1
  have hdv : ContinuousOn (dₜ v) Ω := hv.2.2.2.2.2.1
  obtain ⟨LQ, hLQ⟩ := S.lip
  have hQc : ContinuousOn (fun p : E d × ℝ ↦ S.Q p.1) Ω :=
    hLQ.continuousOn.comp continuous_fst.continuousOn (fun p hp ↦ subset_closure hp.1)
  have hRc : ContinuousOn (fun p ↦ S.Q p.1 ^ 2 * betaEps β ε (v p)) Ω :=
    (hQc.pow 2).mul ((hβ.continuous_betaEps ε).comp_continuousOn hvc)
  have hlapc : ContinuousOn (lapₓ v) Ω :=
    (hdv.add hRc).congr fun p hp ↦ by simp only [Pi.add_apply]; rw [hv.2.2.2.2.2.2 p hp]; ring
  have hint : ∀ g : E d × ℝ → ℝ, ContinuousOn g K → (∀ p ∉ K, g p = 0) →
      Integrable g (volume.restrict Ω) := fun g hg h0 ↦
    (GMTFoundations.integrable_of_continuousOn_of_zero hK hg h0).restrict
  have hηK := hη.continuous.continuousOn (s := K)
  have hgηK := (continuous_gradₓ hη).continuousOn (s := K)
  have hdηK := (continuous_dₜ hη).continuousOn (s := K)
  -- the test function `v η`
  set φ : E d × ℝ → ℝ := fun p ↦ v p * η p with hφdef
  have hφ : IsSliceLipTest φ := isSliceLipTest_mul hΩ hvc
    (locLipₓ_of_gradₓ hU (fun t ht ↦ (hv.2.1 t ht).differentiableOn (by norm_num)) hgv)
    hη hηc hηs
  have hφK : tsupport φ ⊆ K := tsupport_mul_subset_right
  have hφc : HasCompactSupport φ := hηc.mul_left
  have hibp := integral_lapₓ_mul_eq_neg hU hv.2.1 (hlapc.mono (hφK.trans hηs))
    (hgv.mono (hφK.trans hηs)) hφ hφc (hφK.trans hηs)
  have htime := integral_dₜ_mul_self hU hv hη hηc hηs
  -- pointwise identities on `Ω`
  have hgφ : ∀ p ∈ Ω, ⟪gradₓ v p, gradₓ φ p⟫ =
      η p * ‖gradₓ v p‖ ^ 2 + v p * ⟪gradₓ v p, gradₓ η p⟫ := by
    intro p hp
    have hvd : DifferentiableAt ℝ (fun y ↦ v (y, p.2)) p.1 :=
      ((hv.2.1 p.2 hp.2).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp.1)
    rw [gradₓ_mul hvd (differentiableAt_slice hη p), inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_self_eq_norm_sq]
  have hpde : ∀ p ∈ Ω, dₜ v p * φ p =
      lapₓ v p * φ p - S.Q p.1 ^ 2 * betaEps β ε (v p) * (v p * η p) := by
    intro p hp
    simp only [φ]
    rw [hv.2.2.2.2.2.2 p hp]
    ring
  -- integrability
  have i1 : Integrable (fun p ↦ lapₓ v p * φ p) (volume.restrict Ω) :=
    hint _ ((hlapc.mono hηs).mul ((hvc.mono hηs).mul hηK)) fun p hp ↦ by simp [φ, hη0' p hp]
  have i2 : Integrable (fun p ↦ S.Q p.1 ^ 2 * betaEps β ε (v p) * (v p * η p))
      (volume.restrict Ω) :=
    hint _ ((hRc.mono hηs).mul ((hvc.mono hηs).mul hηK)) fun p hp ↦ by simp [hη0' p hp]
  have i3 : Integrable (fun p ↦ η p * ‖gradₓ v p‖ ^ 2) (volume.restrict Ω) :=
    hint _ (hηK.mul ((hgv.mono hηs).norm.pow 2)) fun p hp ↦ by simp [hη0' p hp]
  have i4 : Integrable (fun p ↦ v p * ⟪gradₓ v p, gradₓ η p⟫) (volume.restrict Ω) :=
    hint _ ((hvc.mono hηs).mul ((hgv.mono hηs).inner hgηK)) fun p hp ↦ by simp [hgη0 p hp]
  have e1 : ∫ p in Ω, dₜ v p * φ p = (∫ p in Ω, lapₓ v p * φ p) -
      ∫ p in Ω, S.Q p.1 ^ 2 * betaEps β ε (v p) * (v p * η p) := by
    rw [← integral_sub i1 i2]
    exact setIntegral_congr_fun hΩm fun p hp ↦ hpde p hp
  have e2 : ∫ p in Ω, ⟪gradₓ v p, gradₓ φ p⟫ = (∫ p in Ω, η p * ‖gradₓ v p‖ ^ 2) +
      ∫ p in Ω, v p * ⟪gradₓ v p, gradₓ η p⟫ := by
    rw [← integral_add i3 i4]
    exact setIntegral_congr_fun hΩm fun p hp ↦ hgφ p hp
  have e3 : 0 ≤ ∫ p in Ω, S.Q p.1 ^ 2 * betaEps β ε (v p) * (v p * η p) :=
    setIntegral_nonneg hΩm fun p hp ↦ mul_nonneg (mul_nonneg (sq_nonneg _)
      (hβ.betaEps_nonneg ε _ hε.le)) (mul_nonneg (hv0 p hp) (hη0 p))
  have htime' : ∫ p in Ω, dₜ v p * φ p = -∫ p in Ω, v p ^ 2 / 2 * dₜ η p := htime
  have hibp' : ∫ p in Ω, lapₓ v p * φ p = -∫ p in Ω, ⟪gradₓ v p, gradₓ φ p⟫ := hibp
  have h1 := htime'.symm.trans e1
  rw [hibp', e2] at h1
  set A := ∫ p in Ω, v p ^ 2 / 2 * dₜ η p
  set B := ∫ p in Ω, S.Q p.1 ^ 2 * betaEps β ε (v p) * (v p * η p)
  set I := ∫ p in Ω, η p * ‖gradₓ v p‖ ^ 2
  set J := ∫ p in Ω, v p * ⟪gradₓ v p, gradₓ η p⟫
  linarith

end Inner

end PerronVariational

end
