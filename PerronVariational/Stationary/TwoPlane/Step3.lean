/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.TwoPlane.Step2
import GMTFoundations.Sobolev.Lattice
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import PerronVariational.Main.Directional
import PerronVariational.Stationary.TwoPlane.OneDim

/-!
# Two-plane functions: Step 3 and Proposition 2.14

**Proposition 2.14** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: slices and
marginals, the ACL property of Sobolev functions along `e` (`ae_slice_hasPrimitive`), Step 3
(`energyJ_ge_of_downward`) and the three statements `twoPlane_not_upwardMinimizer`,
`twoPlane_not_downwardMinimizer_of_lt`, `twoPlane_downwardMinimizer_of_le` (with
`twoPlane_downwardMinimizer_iff`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal Convolution

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

section Slices

variable {n : ℕ}

/-- Slices of a locally integrable function along the first coordinate are locally integrable
for a.e. transversal parameter. -/
theorem ae_locallyIntegrable_slice (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1)))
    {f : E (n + 1) → ℝ} (hf : LocallyIntegrable f) :
    ∀ᵐ y : Fin n → ℝ, LocallyIntegrable fun s ↦ f ((coordEquiv b).symm (s, y)) := by
  set Θ := coordEquiv b
  have hR : ∀ R : ℕ, ∀ᵐ y : Fin n → ℝ, y ∈ closedBall (0 : Fin n → ℝ) R →
      IntegrableOn (fun s ↦ f (Θ.symm (s, y))) (Icc (-(R : ℝ)) R) := by
    intro R
    set S : Set (ℝ × (Fin n → ℝ)) := Icc (-(R : ℝ)) R ×ˢ closedBall 0 R
    have hSc : IsCompact S := isCompact_Icc.prod (isCompact_closedBall 0 R)
    have hC : IsCompact (Θ.symm '' S) := hSc.image (continuous_coordEquiv_symm b)
    have hi : Integrable ((Θ.symm '' S).indicator f) :=
      (hf.integrableOn_isCompact hC).integrable_indicator hC.measurableSet
    have hi' : Integrable (((Θ.symm '' S).indicator f) ∘ Θ.symm)
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
      rw [← Measure.volume_eq_prod]
      exact ((measurePreserving_coordEquiv b).symm.integrable_comp_emb
        Θ.symm.measurableEmbedding).2 hi
    filter_upwards [hi'.prod_left_ae] with y hy hyR
    have heq : (fun s ↦ ((Θ.symm '' S).indicator f ∘ Θ.symm) (s, y)) =
        (Icc (-(R : ℝ)) R).indicator fun s ↦ f (Θ.symm (s, y)) := by
      funext s
      simp only [Function.comp]
      by_cases hs : s ∈ Icc (-(R : ℝ)) R
      · rw [indicator_of_mem hs, indicator_of_mem (Θ.symm.injective.mem_set_image.2
          (show (s, y) ∈ S from ⟨hs, hyR⟩))]
      · rw [indicator_of_notMem hs, indicator_of_notMem fun h ↦
          hs (show (s, y) ∈ S from Θ.symm.injective.mem_set_image.1 h).1]
    rw [heq] at hy
    exact (integrable_indicator_iff measurableSet_Icc).1 hy
  rw [← ae_all_iff] at hR
  filter_upwards [hR] with y hy
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R₁, hR₁⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨R₂, hR₂⟩ := exists_nat_ge (max R₁ ‖y‖)
  refine (hy R₂ (mem_closedBall_zero_iff.2 ((le_max_right _ _).trans hR₂))).mono_set ?_
  intro s hs
  have := hR₁ hs
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  rw [mem_Icc, ← abs_le]
  exact this.trans ((le_max_left _ _).trans hR₂)

end Slices

section Marginals

variable {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1)))

/-- First coordinate `x ↦ b₀ · x`. -/
noncomputable def coordFst : E (n + 1) →L[ℝ] ℝ := innerSL ℝ (b 0)

/-- Transversal coordinates `x ↦ (b_{j+1} · x)_j`. -/
noncomputable def coordSnd : E (n + 1) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ innerSL ℝ (b j.succ)

theorem coordEquiv_eq (x : E (n + 1)) : coordEquiv b x = (coordFst b x, coordSnd b x) := by
  rw [coordEquiv_apply]; rfl

theorem coordFst_symm (p : ℝ × (Fin n → ℝ)) : coordFst b ((coordEquiv b).symm p) = p.1 := by
  have := congrArg Prod.fst ((coordEquiv b).apply_symm_apply p)
  rwa [coordEquiv_eq] at this

theorem coordSnd_symm (p : ℝ × (Fin n → ℝ)) : coordSnd b ((coordEquiv b).symm p) = p.2 := by
  have := congrArg Prod.snd ((coordEquiv b).apply_symm_apply p)
  rwa [coordEquiv_eq] at this

theorem hasCompactSupport_coord_mul {φ₁ : ℝ → ℝ} {θ : (Fin n → ℝ) → ℝ}
    (h₁ : HasCompactSupport φ₁) (h₂ : HasCompactSupport θ) :
    HasCompactSupport fun x ↦ φ₁ (coordFst b x) * θ (coordSnd b x) := by
  refine HasCompactSupport.intro ((h₁.isCompact.prod h₂.isCompact).image
    (continuous_coordEquiv_symm b)) fun x hx ↦ ?_
  by_contra hne
  have h1 : φ₁ (coordFst b x) ≠ 0 := left_ne_zero_of_mul hne
  have h2 : θ (coordSnd b x) ≠ 0 := right_ne_zero_of_mul hne
  refine hx ⟨coordEquiv b x, ?_, (coordEquiv b).symm_apply_apply x⟩
  rw [coordEquiv_eq]
  exact ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩

/-- Fubini for `u(x) φ₁(x · b₀) θ(x')`. -/
theorem marginal_integral {u : E (n + 1) → ℝ} (hu : LocallyIntegrable u) {φ₁ : ℝ → ℝ}
    {θ : (Fin n → ℝ) → ℝ} (hφ₁ : Continuous φ₁) (hφ₁c : HasCompactSupport φ₁)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    Integrable (fun y ↦ θ y * ∫ s, u ((coordEquiv b).symm (s, y)) * φ₁ s) ∧
      ∫ y, θ y * (∫ s, u ((coordEquiv b).symm (s, y)) * φ₁ s) =
        ∫ x, u x * (φ₁ (coordFst b x) * θ (coordSnd b x)) := by
  set F : E (n + 1) → ℝ := fun x ↦ u x * (φ₁ (coordFst b x) * θ (coordSnd b x))
  have hF : Integrable F := by
    have := GMTFoundations.integrable_mul_of_locallyIntegrableOn (U := univ)
      (hu.locallyIntegrableOn _)
      ((hφ₁.comp (coordFst b).continuous).mul (hθ.comp (coordSnd b).continuous))
      (hasCompactSupport_coord_mul b hφ₁c hθc) (subset_univ _)
    exact this
  have hF' : Integrable (F ∘ (coordEquiv b).symm)
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    rw [← Measure.volume_eq_prod]
    exact ((measurePreserving_coordEquiv b).symm.integrable_comp_emb
      (coordEquiv b).symm.measurableEmbedding).2 hF
  have hpt : ∀ s y, (F ∘ (coordEquiv b).symm) (s, y) =
      θ y * (u ((coordEquiv b).symm (s, y)) * φ₁ s) := by
    intro s y
    simp only [F, Function.comp, coordFst_symm, coordSnd_symm]
    ring
  have hmarg : ∀ y, ∫ s, (F ∘ (coordEquiv b).symm) (s, y) =
      θ y * ∫ s, u ((coordEquiv b).symm (s, y)) * φ₁ s := by
    intro y
    simp_rw [hpt]
    exact integral_const_mul _ _
  refine ⟨?_, ?_⟩
  · have := hF'.integral_prod_right
    simp_rw [hmarg] at this
    exact this
  · have h1 := (measurePreserving_coordEquiv b).symm.integral_comp
      (coordEquiv b).symm.measurableEmbedding F
    rw [Measure.volume_eq_prod] at h1
    rw [← h1, show (fun x ↦ F ((coordEquiv b).symm x)) = F ∘ (coordEquiv b).symm from rfl,
      integral_prod_symm _ hF']
    simp_rw [hmarg]

/-- The marginal `y ↦ ∫ u(s, y) φ₁(s) ds` is locally integrable. -/
theorem locallyIntegrable_marginal {u : E (n + 1) → ℝ} (hu : LocallyIntegrable u) {φ₁ : ℝ → ℝ}
    (hφ₁ : Continuous φ₁) (hφ₁c : HasCompactSupport φ₁) :
    LocallyIntegrable fun y ↦ ∫ s, u ((coordEquiv b).symm (s, y)) * φ₁ s := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨θ, hθ1, -, hθc, -⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty
    (disjoint_empty K)
  have hi := (marginal_integral b hu hφ₁ hφ₁c θ.continuous hθc).1
  refine (hi.integrableOn (s := K)).congr_fun (fun y hy ↦ ?_) hK.measurableSet
  beta_reduce
  rw [hθ1 hy, Pi.one_apply, one_mul]

end Marginals

section ACL

variable {n : ℕ} {e : E (n + 1)} {b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1))}

/-- For a fixed test function `χ`, a.e. slice of `v` along `e` has weak derivative `G · e`
against `χ`. -/
theorem ae_slice_weakDeriv (hb : b 0 = e) (he : ‖e‖ = 1) {v : E (n + 1) → ℝ}
    {G : E (n + 1) → E (n + 1)} (hv : HasWeakGradient univ v G) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∀ᵐ y : Fin n → ℝ, ∫ s, v ((coordEquiv b).symm (s, y)) * deriv χ s =
      -∫ s, inner ℝ (G ((coordEquiv b).symm (s, y))) e * χ s := by
  have hvl : LocallyIntegrable v := locallyIntegrableOn_univ.1 hv.1
  have hgl : LocallyIntegrable fun x ↦ inner ℝ (G x) e :=
    locallyIntegrableOn_univ.1 (locallyIntegrableOn_inner_const hv.2.1 e)
  have hdχ : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have hdχc : HasCompactSupport (deriv χ) := hχc.deriv
  set A : (Fin n → ℝ) → ℝ := fun y ↦ ∫ s, v ((coordEquiv b).symm (s, y)) * deriv χ s
  set B : (Fin n → ℝ) → ℝ := fun y ↦ ∫ s, inner ℝ (G ((coordEquiv b).symm (s, y))) e * χ s
  have hloc : LocallyIntegrable (fun y ↦ A y + B y) :=
    (locallyIntegrable_marginal b hvl hdχ hdχc).add
      (locallyIntegrable_marginal b hgl hχ.continuous hχc)
  have h0 : ∀ᵐ y, A y + B y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun θ hθ hθc ↦ ?_
    obtain ⟨iA, eA⟩ := marginal_integral b hvl hdχ hdχc hθ.continuous hθc
    obtain ⟨iB, eB⟩ := marginal_integral b hgl hχ.continuous hχc hθ.continuous hθc
    -- the test function `ψ(x) = χ(x · e) θ(x')`
    set ψ : E (n + 1) → ℝ := fun x ↦ χ (coordFst b x) * θ (coordSnd b x) with hψ
    have hψs : ContDiff ℝ ∞ ψ :=
      (hχ.comp (coordFst b).contDiff).mul (hθ.comp (coordSnd b).contDiff)
    have hψc : HasCompactSupport ψ := hasCompactSupport_coord_mul b hχc hθc
    have hfst : coordFst b e = 1 := by
      simp [coordFst, hb, he]
    have hsnd : coordSnd b e = 0 := by
      funext j
      simp only [coordSnd, ContinuousLinearMap.pi_apply, innerSL_apply_apply, ← hb]
      exact b.orthonormal.2 (Fin.succ_ne_zero j)
    have hdψ : ∀ x, fderiv ℝ ψ x e = deriv χ (coordFst b x) * θ (coordSnd b x) := by
      intro x
      have h1 : HasFDerivAt (fun x ↦ χ (coordFst b x))
          (deriv χ (coordFst b x) • (coordFst b : E (n + 1) →L[ℝ] ℝ)) x :=
        ((hχ.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt x
          (coordFst b).hasFDerivAt
      have h2 : HasFDerivAt (fun x ↦ θ (coordSnd b x))
          ((fderiv ℝ θ (coordSnd b x)).comp (coordSnd b : E (n + 1) →L[ℝ] (Fin n → ℝ))) x :=
        ((hθ.differentiable (by simp)) _).hasFDerivAt.comp x (coordSnd b).hasFDerivAt
      rw [(show HasFDerivAt ψ _ x from h1.mul h2).fderiv]
      simp [hfst, hsnd, mul_comm]
    have hw := hv.integral_eq hψs hψc (subset_univ _) e
    simp_rw [hdψ] at hw
    rw [← eA, show (fun x ↦ inner ℝ (G x) e * ψ x) =
      fun x ↦ inner ℝ (G x) e * (χ (coordFst b x) * θ (coordSnd b x)) from rfl, ← eB] at hw
    simp only [smul_eq_mul, mul_add]
    rw [integral_add iA iB, hw]
    ring
  filter_upwards [h0] with y hy
  linarith

/-- **ACL property of Sobolev functions along `e`.** -/
theorem ae_slice_hasPrimitive' (hb : b 0 = e) (he : ‖e‖ = 1)
    {v : E (n + 1) → ℝ} {G : E (n + 1) → E (n + 1)} (hv : MemH1Loc univ v G) :
    ∀ᵐ y : Fin n → ℝ, ∃ w : ℝ → ℝ, (∀ᵐ s : ℝ, w s = v ((coordEquiv b).symm (s, y))) ∧
      ∀ a c, IntervalIntegrable (fun s ↦ inner ℝ (G ((coordEquiv b).symm (s, y))) e) volume a c ∧
        w c - w a = ∫ s in a..c, inner ℝ (G ((coordEquiv b).symm (s, y))) e := by
  have hvl : LocallyIntegrable v := locallyIntegrableOn_univ.1 hv.1.1
  have hgl : LocallyIntegrable fun x ↦ inner ℝ (G x) e :=
    locallyIntegrableOn_univ.1 (locallyIntegrableOn_inner_const hv.1.2.1 e)
  have hall : ∀ᵐ y : Fin n → ℝ, ∀ p : ℕ × ℚ,
      ∫ s, v ((coordEquiv b).symm (s, y)) * deriv (testR p.1 p.2) s =
        -∫ s, inner ℝ (G ((coordEquiv b).symm (s, y))) e * testR p.1 p.2 s := by
    rw [ae_all_iff]
    intro p
    exact ae_slice_weakDeriv hb he hv.1 (contDiff_testR p.1 p.2) (hasCompactSupport_testR p.1 p.2)
  filter_upwards [hall, ae_locallyIntegrable_slice b hvl, ae_locallyIntegrable_slice b hgl]
    with y hy hvy hgy
  obtain ⟨w, hw, hwg⟩ := exists_primitive_of_weakDeriv hvy hgy fun k a ↦ hy (k, a)
  exact ⟨w, hw, hwg⟩

end ACL

section Step3

variable {n : ℕ} {e : E (n + 1)} {b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1))}

/-- Null sets in `E` have null slices along `e` for a.e. transversal parameter. -/
theorem ae_ae_coord (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1)))
    {P : E (n + 1) → Prop} (h : ∀ᵐ x, P x) :
    ∀ᵐ y : Fin n → ℝ, ∀ᵐ s : ℝ, P ((coordEquiv b).symm (s, y)) := by
  have hmp : MeasurePreserving (fun p : (Fin n → ℝ) × ℝ ↦ (coordEquiv b).symm (p.2, p.1))
      (volume.prod volume) volume :=
    (measurePreserving_coordEquiv b).symm.comp (Measure.measurePreserving_swap
      (μ := (volume : Measure (Fin n → ℝ))) (ν := (volume : Measure ℝ)))
  exact Measure.ae_ae_of_ae_prod (hmp.quasiMeasurePreserving.ae h)

/-- **ACL property of Sobolev functions along `e`.** If `v ∈ H¹_loc(ℝᵈ)` with weak gradient `G`,
then for a.e. line `s ↦ Θ⁻¹(s, y)` parallel to `e`, the restriction of `v` has an absolutely
continuous representative `w` with `w' = G · e` (L. C. Evans, R. F. Gariepy, *Measure Theory and
Fine Properties of Functions*, revised ed., CRC Press, 2015, doi:10.1201/b18333, Theorem 4.21).
Used by the paper implicitly in Step 3 of the proof of Proposition 2.14 ("any
competitor for `d > 1` will pay the 1-dimensional energy along slices"). Proof:
`ae_slice_hasPrimitive'` (test functions `χ(x · e) θ(x')`, Fubini, and the one-dimensional
`exists_primitive_of_weakDeriv`). -/
theorem ae_slice_hasPrimitive (b : OrthonormalBasis (Fin (n + 1)) ℝ (E (n + 1))) (hb : b 0 = e)
    {v : E (n + 1) → ℝ} {G : E (n + 1) → E (n + 1)} (hv : MemH1Loc univ v G) :
    ∀ᵐ y : Fin n → ℝ, ∃ w : ℝ → ℝ, (∀ᵐ s : ℝ, w s = v ((coordEquiv b).symm (s, y))) ∧
      ∀ a c, IntervalIntegrable (fun s ↦ inner ℝ (G ((coordEquiv b).symm (s, y))) e) volume a c ∧
        w c - w a = ∫ s in a..c, inner ℝ (G ((coordEquiv b).symm (s, y))) e :=
  ae_slice_hasPrimitive' hb (hb ▸ b.orthonormal.1 0) hv

/-- Slices of a ball along `e` are open intervals. -/
theorem exists_Ioo_eq_slice_ball (hb : b 0 = e) (he : ‖e‖ = 1) (y : Fin n → ℝ)
    (x₀ : E (n + 1)) (r : ℝ) :
    ∃ a c, a ≤ c ∧ {s : ℝ | (coordEquiv b).symm (s, y) ∈ ball x₀ r} = Ioo a c := by
  set z := (coordEquiv b).symm (0, y) - x₀ with hz
  set p := inner ℝ z e with hp
  have hdist : ∀ s, dist ((coordEquiv b).symm (s, y)) x₀ ^ 2 = (s + p) ^ 2 + (‖z‖ ^ 2 - p ^ 2) := by
    intro s
    rw [dist_eq_norm, coordEquiv_symm_eq hb, show (coordEquiv b).symm (0, y) + s • e - x₀ =
      z + s • e by rw [hz]; abel, norm_add_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, he, mul_one, sq_abs, ← hp]
    ring
  by_cases hH : r ≤ 0 ∨ r ^ 2 - ‖z‖ ^ 2 + p ^ 2 ≤ 0
  · refine ⟨0, 0, le_rfl, ?_⟩
    rw [Ioo_self]
    ext s
    simp only [Set.mem_ofPred_eq, mem_ball, mem_empty_iff_false, iff_false, not_lt]
    rcases hH with hr | hH
    · exact hr.trans dist_nonneg
    · by_contra h
      push Not at h
      have h1 := hdist s
      have h2 : dist ((coordEquiv b).symm (s, y)) x₀ ^ 2 < r ^ 2 := by
        have := dist_nonneg (x := (coordEquiv b).symm (s, y)) (y := x₀)
        nlinarith
      nlinarith [sq_nonneg (s + p)]
  · push Not at hH
    obtain ⟨hr, hH⟩ := hH
    set H := r ^ 2 - ‖z‖ ^ 2 + p ^ 2
    refine ⟨-p - √H, -p + √H, by linarith [Real.sqrt_nonneg H], ?_⟩
    ext s
    simp only [Set.mem_ofPred_eq, mem_ball, mem_Ioo]
    rw [← sq_lt_sq₀ dist_nonneg hr.le, hdist]
    have : (s + p) ^ 2 + (‖z‖ ^ 2 - p ^ 2) < r ^ 2 ↔ |s + p| < √H := by
      rw [Real.lt_sqrt (abs_nonneg _), sq_abs]; constructor <;> intro h <;> linarith
    rw [this, abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Proposition 2.14, Step 3**, lower bound for measurable downward competitors in
dimension `n + 1`: `J_q(v; B) ≥ (α² + q²)|B| = J_q(φ_α; B)`. -/
theorem energyJ_ge_of_downward {α q : ℝ} (hq : 0 < q) (hqα : q ≤ α) (he : ‖e‖ = 1)
    {x₀ : E (n + 1)} {r : ℝ} {v : E (n + 1) → ℝ} {G : E (n + 1) → E (n + 1)}
    (hvm : Measurable v) (hGm : Measurable G) (hv : MemH1Loc univ v G)
    (hle : ∀ᵐ x, v x ≤ twoPlane α e x) (hout : ∀ᵐ x, x ∉ ball x₀ r → v x = twoPlane α e x) :
    ENNReal.ofReal (α ^ 2 + q ^ 2) * volume (ball x₀ r) ≤
      energyJ (ball x₀ r) (fun _ ↦ q) v G := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_zero he
  set Θ := coordEquiv b with hΘ
  set B := ball x₀ r with hB
  have hBm : MeasurableSet B := measurableSet_ball
  set F : E (n + 1) → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal (inner ℝ (G x) e ^ 2 + q ^ 2 * {x | 0 < v x}.indicator 1 x) with hFdef
  have hFm : Measurable F := by
    refine Measurable.ennreal_ofReal (Measurable.add ?_ (measurable_const.mul
      (measurable_const.indicator (measurableSet_lt measurable_const hvm))))
    exact ((Measurable.inner (𝕜 := ℝ) hGm measurable_const).pow_const 2)
  -- `J ≥ ∫_B F`
  have h1 : ∫⁻ x in B, F x ≤ energyJ B (fun _ ↦ q) v G := by
    refine setLIntegral_mono' hBm fun x hx ↦ ENNReal.ofReal_le_ofReal (add_le_add ?_ ?_)
    · have h := abs_real_inner_le_norm (G x) e
      rw [he, mul_one] at h
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    · by_cases hx' : 0 < v x
      · rw [indicator_of_mem (show x ∈ {x | 0 < v x} from hx'),
          indicator_of_mem (show x ∈ posSet v B from ⟨hx, hx'⟩)]
      · rw [indicator_of_notMem (show x ∉ {x | 0 < v x} from hx')]
        simp only [mul_zero]
        exact mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  refine le_trans ?_ h1
  -- slices
  have hslice : ∀ y : Fin n → ℝ, MeasurableSet {s : ℝ | Θ.symm (s, y) ∈ B} := fun y ↦
    measurableSet_ball.preimage ((continuous_coordEquiv_symm b).comp
      (continuous_id.prodMk continuous_const)).measurable
  have hvol : volume B = ∫⁻ y, volume {s : ℝ | Θ.symm (s, y) ∈ B} := by
    rw [← lintegral_indicator_one hBm, lintegral_eq_lintegral_coord b
      (measurable_one.indicator hBm)]
    congr 1; funext y
    rw [← lintegral_indicator_one (hslice y)]
    rfl
  rw [← lintegral_indicator hBm, lintegral_eq_lintegral_coord b (hFm.indicator hBm), hvol,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_slice_hasPrimitive b hb hv, ae_ae_coord b hle, ae_ae_coord b hout]
    with y ⟨w, hwv, hwg⟩ hle_y hout_y
  obtain ⟨a, c, hac, hS⟩ := exists_Ioo_eq_slice_ball hb he y x₀ r
  have hφ : ∀ s, twoPlane α e (Θ.symm (s, y)) = α * |s| := fun s ↦ by
    rw [twoPlane, inner_coordEquiv_symm hb]
  have hle_w : ∀ᵐ s : ℝ, w s ≤ α * |s| := by
    filter_upwards [hwv, hle_y] with s h1 h2
    rw [h1, ← hφ s]; exact h2
  have hout_w : ∀ᵐ s : ℝ, s ∉ Ioo a c → w s = α * |s| := by
    filter_upwards [hwv, hout_y] with s h1 h2 hs
    rw [h1, ← hφ s]
    refine h2 fun hmem ↦ hs ?_
    rw [← hS]; exact hmem
  have key := oneDim_downward hq hqα hac hwg hle_w hout_w
  have hind : (fun s ↦ B.indicator F (Θ.symm (s, y))) =
      (Ioo a c).indicator (fun s ↦ F (Θ.symm (s, y))) := by
    funext s
    rw [← hS]
    by_cases hs : Θ.symm (s, y) ∈ B
    · rw [indicator_of_mem hs, indicator_of_mem (show s ∈ {s : ℝ | Θ.symm (s, y) ∈ B} from hs)]
    · rw [indicator_of_notMem hs,
        indicator_of_notMem (show s ∉ {s : ℝ | Θ.symm (s, y) ∈ B} from hs)]
  rw [hind, lintegral_indicator measurableSet_Ioo, hS, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by positivity)]
  refine key.trans (le_of_eq ?_)
  refine setLIntegral_congr_fun_ae measurableSet_Ioo ?_
  filter_upwards [hwv] with s hs _
  simp only [hFdef]
  congr 3
  have hs' : v (Θ.symm (s, y)) = w s := hs.symm
  by_cases h : 0 < w s
  · rw [indicator_of_mem (show s ∈ {s | 0 < w s} from h),
      indicator_of_mem (show Θ.symm (s, y) ∈ {x | 0 < v x} by
        rw [Set.mem_ofPred_eq, hs']; exact h)]
    rfl
  · rw [indicator_of_notMem (show s ∉ {s | 0 < w s} from h),
      indicator_of_notMem (show Θ.symm (s, y) ∉ {x | 0 < v x} by
        rw [Set.mem_ofPred_eq, hs']; exact h)]
/-- The energy of the two-plane function on a ball: `J_q(φ_α; B) = (α² + q²)|B|` (any weak
gradient of `φ_α`). -/
theorem energyJ_twoPlane {d : ℕ} {α q : ℝ} (hα : 0 < α) {e : E d} (he : ‖e‖ = 1)
    {x₀ : E d} {r : ℝ} {Gu : E d → E d} (hu : MemH1Loc univ (twoPlane α e) Gu) :
    energyJ (ball x₀ r) (fun _ ↦ q) (twoPlane α e) Gu =
      ENNReal.ofReal (α ^ 2 + q ^ 2) * volume (ball x₀ r) := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hG : ∀ᵐ x ∂(volume.restrict univ), Gu x = twoPlaneGrad α e x :=
    HasWeakGradient.ae_eq_of_eqOn isOpen_univ isOpen_univ subset_rfl hu.1
      (memH1Loc_twoPlane isOpen_univ α e).1 (eqOn_refl _ _)
  rw [Measure.restrict_univ] at hG
  have hℓ : ∀ᵐ x : E d, inner ℝ x e ≠ 0 := by
    rw [ae_iff]; simpa using volume_inner_eq_zero he0
  rw [← setLIntegral_const]
  unfold energyJ
  refine setLIntegral_congr_fun_ae measurableSet_ball ?_
  filter_upwards [hG, hℓ] with x h1 h2 hx
  have hp : x ∈ posSet (twoPlane α e) (ball x₀ r) := by
    rw [posSet_twoPlane hα]; exact ⟨hx, h2⟩
  rw [h1, norm_twoPlaneGrad_of_ne α he h2, indicator_of_mem hp, sq_abs, Pi.one_apply, mul_one]

/-- **Proposition 2.14 (2), `α ≥ q`** in dimension `n + 1`. -/
theorem twoPlane_downwardMinimizer_of_le_aux {α q : ℝ} (hq : 0 < q) (hqα : q ≤ α)
    (he : ‖e‖ = 1) : IsDownwardMinimizer univ (fun _ ↦ q) (twoPlane α e) := by
  have hα : 0 < α := hq.trans_le hqα
  refine ⟨⟨_, memH1Loc_twoPlane isOpen_univ α e⟩, isOpen_posSet_twoPlane hα isOpen_univ,
    contDiffOn_twoPlane hα univ, fun x hx ↦ laplacian_twoPlane hα hx, ?_⟩
  intro x₀ r _ _ Gu v Gv hu hv hle heq
  rw [energyJ_twoPlane hα he hu]
  -- measurable representatives
  have hvm : AEStronglyMeasurable v volume :=
    (locallyIntegrableOn_univ.1 hv.1.1).aestronglyMeasurable
  have hGm : AEStronglyMeasurable Gv volume :=
    (locallyIntegrableOn_univ.1 hv.1.2.1).aestronglyMeasurable
  set v' := hvm.mk v
  set G' := hGm.mk Gv
  have hvv' : v =ᵐ[volume] v' := hvm.ae_eq_mk
  have hGG' : Gv =ᵐ[volume] G' := hGm.ae_eq_mk
  have hv' : MemH1Loc univ v' G' := by
    refine ⟨(hv.1.congr_fun_ae (by rwa [Measure.restrict_univ])).congr_ae
      (by rwa [Measure.restrict_univ]), fun K hK hKc ↦
        ⟨(hv.2 K hK hKc).1.ae_eq (ae_restrict_of_ae hvv'),
          (hv.2 K hK hKc).2.ae_eq (ae_restrict_of_ae hGG')⟩⟩
  have hE : energyJ (ball x₀ r) (fun _ ↦ q) v Gv = energyJ (ball x₀ r) (fun _ ↦ q) v' G' := by
    unfold energyJ
    refine setLIntegral_congr_fun_ae measurableSet_ball ?_
    filter_upwards [hvv', hGG'] with x h1 h2 hx
    have hpos : x ∈ posSet v (ball x₀ r) ↔ x ∈ posSet v' (ball x₀ r) := by
      simp only [posSet, Set.mem_ofPred_eq, h1]
    have hind : (posSet v (ball x₀ r)).indicator (1 : E (n + 1) → ℝ) x =
        (posSet v' (ball x₀ r)).indicator 1 x := by
      by_cases h : x ∈ posSet v (ball x₀ r)
      · rw [indicator_of_mem h, indicator_of_mem (hpos.1 h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (mt hpos.2 h)]
    rw [h2, hind]
  rw [hE]
  refine energyJ_ge_of_downward hq hqα he hvm.stronglyMeasurable_mk.measurable
    hGm.stronglyMeasurable_mk.measurable hv' ?_ ?_
  · rw [Measure.restrict_univ] at hle
    filter_upwards [hle, hvv'] with x h1 h2
    rw [← h2]; exact h1
  · rw [ae_restrict_iff' (MeasurableSet.univ.diff measurableSet_ball)] at heq
    filter_upwards [heq, hvv'] with x h1 h2 hx
    rw [← h2]; exact h1 ⟨mem_univ _, hx⟩

end Step3

/-! ### Proposition 2.14 -/

/-- **Proposition 2.14 (1)**: for `α > 0`, the two-plane solution `φ_α(x) = α |x · e|` is not
an upward minimizer of `J_q` in `ℝᵈ` (any `q`). Proof by first variation (see module doc). -/
theorem twoPlane_not_upwardMinimizer {α : ℝ} (hα : 0 < α) {e : E d} (he : ‖e‖ = 1) (q : ℝ) :
    ¬ IsUpwardMinimizer univ (fun _ ↦ q) (twoPlane α e) := by
  rintro ⟨-, -, -, -, hmin⟩
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  set G := twoPlaneGrad α e with hGdef
  set B : Set (E d) := ball 0 2 with hBdef
  have : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hBm : MeasurableSet B := measurableSet_ball
  set P : E d → ℝ := fun x ↦ max (1 - ‖x‖ ^ 2) 0 * (α * |inner ℝ x e|) with hPdef
  have hPc : Continuous P := by
    have := continuous_inner_const e
    fun_prop
  have hPnn : 0 ≤ P := fun x ↦
    mul_nonneg (le_max_right _ _) (mul_nonneg hα.le (abs_nonneg _))
  have hP0 : ∀ x, x ∉ closedBall (0 : E d) 1 → P x = 0 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    have : 1 - ‖x‖ ^ 2 ≤ 0 := by nlinarith
    simp [hPdef, max_eq_right this]
  -- `A = ∫_B (1-|x|²)₊ α |x·e| > 0`
  set A := ∫ x in B, P x with hAdef
  have hA : 0 < A := by
    have hsupp : HasCompactSupport P :=
      HasCompactSupport.intro (isCompact_closedBall 0 1) hP0
    have hpos : 0 < ∫ x, P x :=
      hPc.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hPnn
        (x := (1 / 2 : ℝ) • e) (by
          have : ‖(1 / 2 : ℝ) • e‖ = 1 / 2 := by rw [norm_smul, he]; norm_num
          simp only [hPdef, this, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
          norm_num
          exact hα.ne')
    rwa [hAdef, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ hP0 x fun h ↦ hx
      (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 h) (by norm_num)))]
  set C := ∫ x in B, ‖∇ twoPlaneBump x‖ ^ 2 with hCdef
  have hC : 0 ≤ C := setIntegral_nonneg hBm fun _ _ ↦ sq_nonneg _
  set t := 4 * A / (C + 1) with htdef
  have ht : 0 < t := div_pos (mul_pos (by norm_num) hA) (by linarith)
  have htC : t * C < 4 * A := by
    rw [htdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  set v : E d → ℝ := fun x ↦ twoPlane α e x + t * twoPlaneBump x with hvdef
  set Gv : E d → E d := fun x ↦ G x + t • ∇ twoPlaneBump x with hGvdef
  have hu := memH1Loc_twoPlane isOpen_univ α e
  have hv : MemH1Loc univ v Gv :=
    hu.add ((memH1Loc_of_contDiff_one contDiff_twoPlaneBump).const_mul' t)
  have hle : ∀ᵐ y ∂(volume.restrict univ), twoPlane α e y ≤ v y :=
    Eventually.of_forall fun y ↦ le_add_of_nonneg_right (mul_nonneg ht.le (twoPlaneBump_nonneg y))
  have heq : ∀ᵐ y ∂(volume.restrict (univ \ B)), v y = twoPlane α e y := by
    refine (ae_restrict_iff' (MeasurableSet.univ.diff hBm)).2 (Eventually.of_forall fun y hy ↦ ?_)
    have : 1 ≤ ‖y‖ := by
      simp only [hBdef, Set.mem_sdiff, mem_univ, mem_ball, dist_zero_right, not_lt, true_and] at hy
      linarith
    simp [hvdef, twoPlaneBump_eq_zero this]
  have key := hmin 0 2 two_pos (subset_univ _) G v Gv hu hv hle heq
  refine absurd key (not_le.2 ?_)
  -- the energy comparison
  set a : E d → ℝ := fun x ↦ q ^ 2 * (posSet (twoPlane α e) B).indicator 1 x with hadef
  have hGm : Measurable G := measurable_twoPlaneGrad α e
  have hgradc := continuous_gradient_twoPlaneBump (d := d)
  have hposm : MeasurableSet (posSet (twoPlane α e) B) := by
    rw [posSet_twoPlane hα]
    exact hBm.inter (measurableSet_eq_fun (continuous_inner_const e).measurable
      measurable_const).compl
  have ham : Measurable a := measurable_const.mul (measurable_const.indicator hposm)
  have hab : ∀ x, ‖a x‖ ≤ q ^ 2 := by
    intro x
    simp only [hadef, Real.norm_eq_abs]
    by_cases hx : x ∈ posSet (twoPlane α e) B
    · simp [indicator_of_mem hx, abs_of_nonneg (sq_nonneg q)]
    · simp [indicator_of_notMem hx, sq_nonneg]
  have hGb : ∀ x, ‖‖G x‖ ^ 2‖ ≤ α ^ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := norm_twoPlaneGrad_le α he x
    rw [abs_of_pos hα] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have iG : IntegrableOn (fun x ↦ ‖G x‖ ^ 2) B :=
    Integrable.of_bound (hGm.norm.pow_const 2).aestronglyMeasurable (α ^ 2)
      (Eventually.of_forall hGb)
  have ia : IntegrableOn a B :=
    Integrable.of_bound ham.aestronglyMeasurable (q ^ 2) (Eventually.of_forall hab)
  have iP : IntegrableOn P B :=
    (hPc.continuousOn.integrableOn_compact (isCompact_closedBall 0 2)).mono_set
      ball_subset_closedBall
  have iC : IntegrableOn (fun x ↦ ‖∇ twoPlaneBump x‖ ^ 2) B :=
    ((hgradc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 2)).mono_set
      ball_subset_closedBall
  -- pointwise expansion of `|∇v|²`
  have hexp : ∀ x, ‖Gv x‖ ^ 2 + a x =
      (‖G x‖ ^ 2 + a x) + (-(8 * t) * P x + t ^ 2 * ‖∇ twoPlaneBump x‖ ^ 2) := by
    intro x
    simp only [hGvdef]
    rw [norm_add_sq_real, real_inner_smul_right, hGdef, inner_twoPlaneGrad_gradient_twoPlaneBump,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow]
    simp only [hPdef]
    ring
  have hint : ∫ x in B, (‖Gv x‖ ^ 2 + a x) =
      (∫ x in B, (‖G x‖ ^ 2 + a x)) + (-(8 * t) * A + t ^ 2 * C) := by
    simp_rw [hexp]
    rw [integral_add (f := fun x ↦ ‖G x‖ ^ 2 + a x)
      (g := fun x ↦ -(8 * t) * P x + t ^ 2 * ‖∇ twoPlaneBump x‖ ^ 2) ?_ ?_,
      integral_add (f := fun x ↦ -(8 * t) * P x) ?_ ?_, integral_const_mul, integral_const_mul]
    · exact iP.const_mul _
    · exact iC.const_mul _
    · exact iG.add ia
    · exact (iP.const_mul _).add (iC.const_mul _)
  have hneg : -(8 * t) * A + t ^ 2 * C < 0 := by
    have : t ^ 2 * C = t * (t * C) := by ring
    rw [this]
    nlinarith [mul_lt_mul_of_pos_left htC ht, mul_pos ht hA]
  -- energies as real integrals
  have hnnG : 0 ≤ᵐ[volume.restrict B] fun x ↦ ‖G x‖ ^ 2 + a x :=
    Eventually.of_forall fun x ↦ add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _))
  have hEu : energyJ B (fun _ ↦ q) (twoPlane α e) G =
      ENNReal.ofReal (∫ x in B, (‖G x‖ ^ 2 + a x)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (f := fun x ↦ ‖G x‖ ^ 2 + a x)
      (by exact iG.add ia) hnnG]
    rfl
  have hnull : ∀ᵐ x ∂(volume.restrict B), x ∈ posSet (twoPlane α e) B := by
    rw [ae_restrict_iff' hBm]
    have : ∀ᵐ x ∂(volume : Measure (E d)), inner ℝ x e ≠ 0 := by
      rw [ae_iff]
      simpa using volume_inner_eq_zero he0
    filter_upwards [this] with x hx hxB
    rw [posSet_twoPlane hα]
    exact ⟨hxB, hx⟩
  have hEv : energyJ B (fun _ ↦ q) v Gv ≤ ENNReal.ofReal (∫ x in B, (‖Gv x‖ ^ 2 + a x)) := by
    have iGv : IntegrableOn (fun x ↦ ‖Gv x‖ ^ 2 + a x) B := by
      simp_rw [hexp]
      exact (iG.add ia).add ((iP.const_mul _).add (iC.const_mul _))
    rw [ofReal_integral_eq_lintegral_ofReal (f := fun x ↦ ‖Gv x‖ ^ 2 + a x) iGv
      (Eventually.of_forall fun x ↦ add_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)))]
    unfold energyJ
    refine lintegral_mono_ae ?_
    filter_upwards [hnull] with x hx
    refine ENNReal.ofReal_le_ofReal (add_le_add le_rfl ?_)
    simp only [hadef, indicator_of_mem hx, Pi.one_apply]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    by_cases h : x ∈ posSet v B
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  rw [hEu]
  refine lt_of_le_of_lt hEv ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ?_).2 ?_)
  · exact integral_nonneg fun x ↦ add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _))
  · rw [hint]; linarith

/-- **Proposition 2.14 (2), `α < q`** (Steps 1–2): for `0 < α < q`, `φ_α` is not a
downward minimizer of `J_q` in `ℝᵈ`. -/
theorem twoPlane_not_downwardMinimizer_of_lt {α q : ℝ} (hα : 0 < α) (hαq : α < q) {e : E d}
    (he : ‖e‖ = 1) : ¬ IsDownwardMinimizer univ (fun _ ↦ q) (twoPlane α e) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := by
    rcases d with _ | n
    · exfalso
      have : e = 0 := Subsingleton.elim _ _
      simp [this] at he
    · exact ⟨n, rfl⟩
  exact twoPlane_not_downwardMinimizer_of_lt_aux hα hαq he

/-- **Proposition 2.14 (2), `α ≥ q`** (Step 3): for `0 < q ≤ α`, `φ_α` is a
downward minimizer of `J_q` in `ℝᵈ`. -/
theorem twoPlane_downwardMinimizer_of_le {α q : ℝ} (hq : 0 < q) (hqα : q ≤ α) {e : E d}
    (he : ‖e‖ = 1) : IsDownwardMinimizer univ (fun _ ↦ q) (twoPlane α e) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := by
    rcases d with _ | n
    · exfalso
      have : e = 0 := Subsingleton.elim _ _
      simp [this] at he
    · exact ⟨n, rfl⟩
  exact twoPlane_downwardMinimizer_of_le_aux hq hqα he

/-- **Proposition 2.14 (2)**: for `α, q > 0`, `φ_α` is a downward minimizer of `J_q` in `ℝᵈ`
iff `q ≤ α`. -/
theorem twoPlane_downwardMinimizer_iff {α q : ℝ} (hα : 0 < α) (hq : 0 < q) {e : E d}
    (he : ‖e‖ = 1) : IsDownwardMinimizer univ (fun _ ↦ q) (twoPlane α e) ↔ q ≤ α :=
  ⟨fun h ↦ not_lt.1 fun hlt ↦ twoPlane_not_downwardMinimizer_of_lt hα hlt he h,
    fun h ↦ twoPlane_downwardMinimizer_of_le hq h he⟩

end PerronVariational

end
