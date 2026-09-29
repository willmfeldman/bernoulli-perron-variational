/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Semilinear
import GMTFoundations.Sobolev.Cutoff
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Inner.Common
import PerronVariational.Inner.WeakHeat
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Profiles

/-!
# Time regularity of the energy density: the energy moment

Part of the proof of **Lemma 4.3** (the computation leading to (4.8)) of F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981: integration by parts for the difference of two Dirichlet
energy densities (`integral_norm_grad_sq_sub_mul`), the spatial moment `energyMoment` of the
energy density, its time derivative (`hasDerivAt_energyMoment`) and the increment bound
`enorm_energyMoment_sub_le`. The paper localizes an argument of G. S. Weiss, *A singular limit
arising in combustion theory: fine properties of the free boundary*, Calc. Var. Partial
Differential Equations 17 (2003), 311–340, doi:10.1007/s00526-002-0171-z, Proposition 4.1
[Weiss 2003].
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

theorem continuousOn_gradient_of_contDiffOn {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : ContDiffOn ℝ 1 f U) : ContinuousOn (∇ f) U :=
  (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp_continuousOn
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl)

theorem continuousOn_laplacian_of_contDiffOn {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : ContDiffOn ℝ 2 f U) : ContinuousOn (Δ f) U := by
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  rw [show Δ f = fun x ↦ ∑ i, fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ (E d) i)
      (stdOrthonormalBasis ℝ (E d) i) from funext (laplacian_eq_sum_fderiv_fderiv f)]
  exact continuousOn_finsetSum _ fun i _ ↦
    ((hf1.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).clm_apply
      continuousOn_const

theorem gradient_eq_zero_of_notMem_tsupport {f : E d → ℝ} {x : E d} (hx : x ∉ tsupport f) :
    ∇ f x = 0 := by
  simp only [gradient]
  rw [fderiv_of_notMem_tsupport ℝ hx, map_zero]

/-- **Integration by parts for the difference of two Dirichlet energy densities.** For
`f₁, f₂ ∈ C²(U)` and `ψ ∈ C¹_c(U)`:
`∫ (|∇f₁|² - |∇f₂|²) ψ = -∫ (f₁ - f₂) (ψ (Δf₁ + Δf₂) + (∇f₁ + ∇f₂) · ∇ψ)`. -/
theorem integral_norm_grad_sq_sub_mul {U : Set (E d)} (hU : IsOpen U) {f₁ f₂ ψ : E d → ℝ}
    (hf₁ : ContDiffOn ℝ 2 f₁ U) (hf₂ : ContDiffOn ℝ 2 f₂ U) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    ∫ x, (‖∇ f₁ x‖ ^ 2 - ‖∇ f₂ x‖ ^ 2) * ψ x =
      -∫ x, (f₁ x - f₂ x) * (ψ x * (Δ f₁ x + Δ f₂ x) + ⟪∇ f₁ x + ∇ f₂ x, ∇ ψ x⟫) := by
  set K := tsupport ψ with hKdef
  have hK : IsCompact K := hψc
  have hψ0 : ∀ x ∉ K, ψ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hgψ0 : ∀ x ∉ K, ∇ ψ x = 0 := fun x hx ↦ gradient_eq_zero_of_notMem_tsupport hx
  have hd₁ : ∀ x ∈ U, DifferentiableAt ℝ f₁ x := fun x hx ↦
    (hf₁.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have hd₂ : ∀ x ∈ U, DifferentiableAt ℝ f₂ x := fun x hx ↦
    (hf₂.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  -- the Lipschitz test function `g = ψ (f₁ - f₂)`
  have hgC : ContDiff ℝ 1 fun y ↦ ψ y * (f₁ y - f₂ y) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hψ.contDiffAt.mul (((hf₁.contDiffAt (hU.mem_nhds hx)).sub
        (hf₂.contDiffAt (hU.mem_nhds hx))).of_le (by norm_num))
    · have hxK : x ∉ K := fun h ↦ hx (hψU h)
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxK] with y hy
      simp [show ψ y = 0 from hy]
  have hgc : HasCompactSupport fun y ↦ ψ y * (f₁ y - f₂ y) := hψc.mul_right
  have hgK : tsupport (fun y ↦ ψ y * (f₁ y - f₂ y)) ⊆ K := tsupport_mul_subset_left
  obtain ⟨Cg, hgL⟩ := hgC.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  have h1 := integral_laplacian_mul_eq_neg hU hf₁ hgL hgc (hgK.trans hψU)
  have h2 := integral_laplacian_mul_eq_neg hU hf₂ hgL hgc (hgK.trans hψU)
  -- continuity facts
  have hg₁c := continuousOn_gradient_of_contDiffOn hU (hf₁.of_le (by norm_num))
  have hg₂c := continuousOn_gradient_of_contDiffOn hU (hf₂.of_le (by norm_num))
  have hl₁c := continuousOn_laplacian_of_contDiffOn hU hf₁
  have hl₂c := continuousOn_laplacian_of_contDiffOn hU hf₂
  have hgψc : Continuous (∇ ψ) := (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp
    (hψ.continuous_fderiv one_ne_zero)
  have hggc : Continuous (∇ fun y ↦ ψ y * (f₁ y - f₂ y)) :=
    (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp (hgC.continuous_fderiv one_ne_zero)
  have hgg0 : ∀ x ∉ K, ∇ (fun y ↦ ψ y * (f₁ y - f₂ y)) x = 0 := fun x hx ↦
    gradient_eq_zero_of_notMem_tsupport fun h ↦ hx (hgK h)
  -- pointwise identity
  have hpt : ∀ x, (‖∇ f₁ x‖ ^ 2 - ‖∇ f₂ x‖ ^ 2) * ψ x =
      (⟪∇ f₁ x, ∇ (fun y ↦ ψ y * (f₁ y - f₂ y)) x⟫ +
        ⟪∇ f₂ x, ∇ (fun y ↦ ψ y * (f₁ y - f₂ y)) x⟫) -
      (f₁ x - f₂ x) * ⟪∇ f₁ x + ∇ f₂ x, ∇ ψ x⟫ := by
    intro x
    by_cases hx : x ∈ K
    · have hxU := hψU hx
      have hψd : DifferentiableAt ℝ ψ x := hψ.differentiable one_ne_zero x
      have hgd : ∀ w, fderiv ℝ (fun y ↦ ψ y * (f₁ y - f₂ y)) x w =
          ψ x * (fderiv ℝ f₁ x w - fderiv ℝ f₂ x w) + (f₁ x - f₂ x) * fderiv ℝ ψ x w := by
        intro w
        have h : HasFDerivAt (fun y ↦ ψ y * (f₁ y - f₂ y)) _ x :=
          hψd.hasFDerivAt.mul ((hd₁ x hxU).hasFDerivAt.sub (hd₂ x hxU).hasFDerivAt)
        rw [h.fderiv]
        simp
      have hg' : ∀ w, ⟪∇ (fun y ↦ ψ y * (f₁ y - f₂ y)) x, w⟫ =
          ψ x * (⟪∇ f₁ x, w⟫ - ⟪∇ f₂ x, w⟫) + (f₁ x - f₂ x) * ⟪∇ ψ x, w⟫ := by
        intro w
        rw [inner_gradient_eq_fderiv, inner_gradient_eq_fderiv, inner_gradient_eq_fderiv,
          inner_gradient_eq_fderiv, hgd]
      rw [real_inner_comm (∇ (fun y ↦ ψ y * (f₁ y - f₂ y)) x) (∇ f₁ x),
        real_inner_comm (∇ (fun y ↦ ψ y * (f₁ y - f₂ y)) x) (∇ f₂ x), hg', hg', inner_add_left,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm (∇ f₂ x) (∇ f₁ x),
        real_inner_comm (∇ f₁ x) (∇ ψ x), real_inner_comm (∇ f₂ x) (∇ ψ x)]
      ring
    · simp [hψ0 x hx, hgψ0 x hx, hgg0 x hx]
  -- integrability
  have i1 : ∀ f : E d → ℝ, ContinuousOn (∇ f) U →
      Integrable fun x ↦ ⟪∇ f x, ∇ (fun y ↦ ψ y * (f₁ y - f₂ y)) x⟫ := fun f hf ↦
    GMTFoundations.integrable_of_continuousOn_of_zero hK ((hf.mono hψU).inner hggc.continuousOn)
      fun x hx ↦ by simp [hgg0 x hx]
  have i2 : Integrable fun x ↦ (f₁ x - f₂ x) * ⟪∇ f₁ x + ∇ f₂ x, ∇ ψ x⟫ :=
    GMTFoundations.integrable_of_continuousOn_of_zero hK
      (((hf₁.continuousOn.mono hψU).sub (hf₂.continuousOn.mono hψU)).mul
        (((hg₁c.mono hψU).add (hg₂c.mono hψU)).inner hgψc.continuousOn))
      fun x hx ↦ by simp [hgψ0 x hx]
  have i3 : ∀ f : E d → ℝ, ContinuousOn (Δ f) U →
      Integrable fun x ↦ Δ f x * (ψ x * (f₁ x - f₂ x)) := fun f hf ↦
    GMTFoundations.integrable_of_continuousOn_of_zero hK
      ((hf.mono hψU).mul hgC.continuous.continuousOn)
      fun x hx ↦ by simp [hψ0 x hx]
  have j1 : Integrable fun x ↦ ⟪∇ f₁ x, ∇ (fun y ↦ ψ y * (f₁ y - f₂ y)) x⟫ +
      ⟪∇ f₂ x, ∇ (fun y ↦ ψ y * (f₁ y - f₂ y)) x⟫ := (i1 f₁ hg₁c).add (i1 f₂ hg₂c)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub j1 i2, integral_add (i1 f₁ hg₁c)
    (i1 f₂ hg₂c), ← neg_eq_iff_eq_neg.2 h1, ← neg_eq_iff_eq_neg.2 h2]
  have hR : ∀ x, (f₁ x - f₂ x) * (ψ x * (Δ f₁ x + Δ f₂ x) + ⟪∇ f₁ x + ∇ f₂ x, ∇ ψ x⟫) =
      Δ f₁ x * (ψ x * (f₁ x - f₂ x)) + Δ f₂ x * (ψ x * (f₁ x - f₂ x)) +
        (f₁ x - f₂ x) * ⟪∇ f₁ x + ∇ f₂ x, ∇ ψ x⟫ := fun x ↦ by ring
  have i4 : Integrable fun x ↦ Δ f₁ x * (ψ x * (f₁ x - f₂ x)) + Δ f₂ x * (ψ x * (f₁ x - f₂ x)) :=
    (i3 f₁ hl₁c).add (i3 f₂ hl₂c)
  rw [integral_congr_ae (ae_of_all _ hR), integral_add i4 i2,
    integral_add (i3 f₁ hl₁c) (i3 f₂ hl₂c)]
  ring

/-- Mean value bound for a slope. -/
theorem abs_slope_le_of_hasDerivAt_Icc {f f' : ℝ → ℝ} {a b C : ℝ}
    (hd : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s) (hC : ∀ s ∈ Icc a b, |f' s| ≤ C)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : |slope f s t| ≤ C := by
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx ↦ (hd x hx).hasDerivWithinAt) (fun x hx ↦ by rw [Real.norm_eq_abs]; exact hC x hx)
    hs ht
  simp only [Real.norm_eq_abs] at h
  rw [slope_def_field]
  by_cases hts : t = s
  · subst hts
    simpa using (abs_nonneg _).trans (hC _ ht)
  · rw [abs_div, div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 hts))]
    exact h

/-- The spatial moment `∫ (|∇v|² + Q² χ_ε(v))(x, t) ψ(x) dx` of the energy density. -/
noncomputable def energyMoment (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ) (v : E d × ℝ → ℝ)
    (ψ : E d → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (‖gradₓ v (x, t)‖ ^ 2 + Q x ^ 2 * chiEps β ε v (x, t)) * ψ x

/-- **Time derivative of the energy moment** (proof of Lemma 4.3, after [Weiss 2003]):
`d/dt ∫ e_ε ψ = ∫ (-2 ψ (∂ₜv)² - 2 ∂ₜv ∇v · ∇ψ)` for a classical solution `v` and
`ψ ∈ C¹_c(U)`. The reaction terms cancel since the weight `Q²` in `e_ε` matches the equation. -/
theorem hasDerivAt_energyMoment {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ}
    (hQ : ContinuousOn Q U) {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ}
    {v : E d × ℝ → ℝ} (hv : IsSemilinearSolOn U Q β ε (Ioi 0) v) {ψ : E d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) {t₀ : ℝ}
    (ht₀ : 0 < t₀) :
    HasDerivAt (energyMoment Q β ε v ψ)
      (∫ x, (-2 * ψ x * dₜ v (x, t₀) ^ 2 - 2 * dₜ v (x, t₀) * ⟪gradₓ v (x, t₀), ∇ ψ x⟫)) t₀ := by
  have hlc := IsSemilinearSolOn.continuousOn_lapₓ hβ hv hQ
  obtain ⟨hvc, hvC2, hgc, -, hvd, hdc, heq⟩ := hv
  set K := tsupport ψ with hKdef
  have hK : IsCompact K := hψc
  have hψ0 : ∀ x ∉ K, ψ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hgψ0 : ∀ x ∉ K, ∇ ψ x = 0 := fun x hx ↦ gradient_eq_zero_of_notMem_tsupport hx
  have hgψc : Continuous (∇ ψ) := (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp
    (hψ.continuous_fderiv one_ne_zero)
  set I := Icc (t₀ / 2) (3 * t₀ / 2) with hIdef
  have hI : I ⊆ Ioi 0 := fun s hs ↦ by
    simp only [hIdef, mem_Icc, mem_Ioi] at hs ⊢
    linarith [hs.1]
  have ht₀I : t₀ ∈ I := ⟨by linarith, by linarith⟩
  have hKt : IsCompact (K ×ˢ I) := hK.prod isCompact_Icc
  have hKtU : K ×ˢ I ⊆ U ×ˢ Ioi 0 := prod_mono hψU hI
  have hβc := (hβ.continuous_betaEps ε).comp_continuousOn hvc
  obtain ⟨Cd, hCd⟩ := hKt.exists_bound_of_continuousOn (hdc.mono hKtU)
  obtain ⟨Cl, hCl⟩ := hKt.exists_bound_of_continuousOn (hlc.mono hKtU)
  obtain ⟨Cg, hCg⟩ := hKt.exists_bound_of_continuousOn (hgc.mono hKtU)
  obtain ⟨Cb, hCb⟩ := hKt.exists_bound_of_continuousOn (hβc.mono hKtU)
  obtain ⟨CQ, hCQ⟩ := hK.exists_bound_of_continuousOn (hQ.mono hψU)
  obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  obtain ⟨Cψ', hCψ'⟩ := hK.exists_bound_of_continuousOn hgψc.continuousOn
  set C := max Cd (max Cl (max Cg (max Cb (max CQ (max Cψ (max Cψ' 0)))))) with hCdef
  have hC0 : 0 ≤ C := by simp [hCdef]
  have hbd : ∀ p ∈ K ×ˢ I, |dₜ v p| ≤ C ∧ |lapₓ v p| ≤ C ∧ ‖gradₓ v p‖ ≤ C ∧
      |betaEps β ε (v p)| ≤ C := by
    intro p hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (Real.norm_eq_abs _ ▸ hCd p hp).trans (by simp [hCdef])
    · exact (Real.norm_eq_abs _ ▸ hCl p hp).trans (by simp [hCdef])
    · exact (hCg p hp).trans (by simp [hCdef])
    · exact (Real.norm_eq_abs _ ▸ hCb p hp).trans (by simp [hCdef])
  have hQb : ∀ x ∈ K, |Q x| ≤ C := fun x hx ↦
    (Real.norm_eq_abs _ ▸ hCQ x hx).trans (by simp [hCdef])
  have hψb : ∀ x, |ψ x| ≤ C := fun x ↦ (Real.norm_eq_abs _ ▸ hCψ x).trans (by simp [hCdef])
  have hgψb : ∀ x, ‖∇ ψ x‖ ≤ C := fun x ↦ by
    by_cases hx : x ∈ K
    · exact (hCψ' x hx).trans (by simp [hCdef])
    · simp [hgψ0 x hx, hC0]
  -- time derivatives along vertical lines
  have hdv : ∀ x ∈ U, ∀ s, 0 < s → HasDerivAt (fun s ↦ v (x, s)) (dₜ v (x, s)) s :=
    fun x hx s hs ↦ (hvd (x, s) ⟨hx, hs⟩).hasDerivAt
  have hdχ : ∀ x ∈ U, ∀ s, 0 < s → HasDerivAt (fun s ↦ chiEps β ε v (x, s))
      (2 * (betaEps β ε (v (x, s)) * dₜ v (x, s))) s := by
    intro x hx s hs
    have h := ((hβ.hasDerivAt_bigBEps ε (v (x, s))).comp s (hdv x hx s hs)).const_mul 2
    simpa only [chiEps, Function.comp_def] using h
  -- the slope integrand
  set S : ℝ → E d → ℝ := fun t x ↦
    -(slope (fun s ↦ v (x, s)) t₀ t) * (ψ x * (lapₓ v (x, t) + lapₓ v (x, t₀)) +
      ⟪gradₓ v (x, t) + gradₓ v (x, t₀), ∇ ψ x⟫) +
      Q x ^ 2 * slope (fun s ↦ chiEps β ε v (x, s)) t₀ t * ψ x with hSdef
  have hS0 : ∀ t, ∀ x ∉ K, S t x = 0 := fun t x hx ↦ by simp [hSdef, hψ0 x hx, hgψ0 x hx]
  have hχc : ContinuousOn (chiEps β ε v) (U ×ˢ Ioi 0) :=
    continuousOn_const.mul ((continuous_iff_continuousAt.2 fun z ↦
      (hβ.hasDerivAt_bigBEps ε z).continuousAt).comp_continuousOn hvc)
  have hSc : ∀ t ∈ I, ContinuousOn (S t) K := by
    intro t ht
    have h1 := continuousOn_slice_of_prod hvc (hI ht)
    have h2 := continuousOn_slice_of_prod hvc (hI ht₀I)
    have h3 := continuousOn_slice_of_prod hlc (hI ht)
    have h4 := continuousOn_slice_of_prod hlc (hI ht₀I)
    have h5 := continuousOn_slice_of_prod hgc (hI ht)
    have h6 := continuousOn_slice_of_prod hgc (hI ht₀I)
    have h7 := continuousOn_slice_of_prod hχc (hI ht)
    have h8 := continuousOn_slice_of_prod hχc (hI ht₀I)
    simp only [hSdef, slope_def_field]
    exact ((((h1.sub h2).div_const _).neg.mul ((hψ.continuous.continuousOn.mul (h3.add h4)).add
      ((h5.add h6).inner hgψc.continuousOn))).add (((hQ.pow 2).mul ((h7.sub h8).div_const _)).mul
      hψ.continuous.continuousOn)).mono hψU
  have hSi : ∀ t ∈ I, Integrable (S t) := fun t ht ↦
    GMTFoundations.integrable_of_continuousOn_of_zero hK (hSc t ht) (hS0 t)
  -- representation of the slope of the moment
  have hrepr : ∀ t ∈ I, t ≠ t₀ → slope (energyMoment Q β ε v ψ) t₀ t = ∫ x, S t x := by
    intro t ht htt
    have htU := hI ht
    have ht₀U := hI ht₀I
    have hC2 : ∀ s ∈ Ioi (0 : ℝ), ContDiffOn ℝ 2 (fun x ↦ v (x, s)) U := hvC2
    have hibp := integral_norm_grad_sq_sub_mul hU (hC2 t htU) (hC2 t₀ ht₀U) hψ hψc hψU
    have hint : ∀ s ∈ Ioi (0 : ℝ), Integrable fun x ↦
        (‖gradₓ v (x, s)‖ ^ 2 + Q x ^ 2 * chiEps β ε v (x, s)) * ψ x := by
      intro s hs
      refine GMTFoundations.integrable_of_continuousOn_of_zero hK ?_ fun x hx ↦ by simp [hψ0 x hx]
      exact ((((continuousOn_slice_of_prod hgc hs).norm.pow 2).add ((hQ.pow 2).mul
        (continuousOn_slice_of_prod hχc hs))).mul hψ.continuous.continuousOn).mono hψU
    have hintA : Integrable fun x ↦ (v (x, t) - v (x, t₀)) *
        (ψ x * (lapₓ v (x, t) + lapₓ v (x, t₀)) + ⟪gradₓ v (x, t) + gradₓ v (x, t₀), ∇ ψ x⟫) := by
      refine GMTFoundations.integrable_of_continuousOn_of_zero hK ?_ fun x hx ↦ by
        simp [hψ0 x hx, hgψ0 x hx]
      exact (((continuousOn_slice_of_prod hvc htU).sub (continuousOn_slice_of_prod hvc ht₀U)).mul
        ((hψ.continuous.continuousOn.mul ((continuousOn_slice_of_prod hlc htU).add
          (continuousOn_slice_of_prod hlc ht₀U))).add (((continuousOn_slice_of_prod hgc htU).add
            (continuousOn_slice_of_prod hgc ht₀U)).inner hgψc.continuousOn))).mono hψU
    have hintB : Integrable fun x ↦ Q x ^ 2 * (chiEps β ε v (x, t) - chiEps β ε v (x, t₀)) *
        ψ x := by
      refine GMTFoundations.integrable_of_continuousOn_of_zero hK ?_ fun x hx ↦ by simp [hψ0 x hx]
      exact (((hQ.pow 2).mul ((continuousOn_slice_of_prod hχc htU).sub
        (continuousOn_slice_of_prod hχc ht₀U))).mul hψ.continuous.continuousOn).mono hψU
    have hintD : Integrable fun x ↦ (‖gradₓ v (x, t)‖ ^ 2 - ‖gradₓ v (x, t₀)‖ ^ 2) * ψ x := by
      refine GMTFoundations.integrable_of_continuousOn_of_zero hK ?_ fun x hx ↦ by simp [hψ0 x hx]
      exact ((((continuousOn_slice_of_prod hgc htU).norm.pow 2).sub
        ((continuousOn_slice_of_prod hgc ht₀U).norm.pow 2)).mul
          hψ.continuous.continuousOn).mono hψU
    have hdiff : energyMoment Q β ε v ψ t - energyMoment Q β ε v ψ t₀ =
        -(∫ x, (v (x, t) - v (x, t₀)) * (ψ x * (lapₓ v (x, t) + lapₓ v (x, t₀)) +
          ⟪gradₓ v (x, t) + gradₓ v (x, t₀), ∇ ψ x⟫)) +
        ∫ x, Q x ^ 2 * (chiEps β ε v (x, t) - chiEps β ε v (x, t₀)) * ψ x := by
      simp only [energyMoment]
      rw [← integral_sub (hint t htU) (hint t₀ ht₀U)]
      have hpt : ∀ x, (‖gradₓ v (x, t)‖ ^ 2 + Q x ^ 2 * chiEps β ε v (x, t)) * ψ x -
          (‖gradₓ v (x, t₀)‖ ^ 2 + Q x ^ 2 * chiEps β ε v (x, t₀)) * ψ x =
          (‖gradₓ v (x, t)‖ ^ 2 - ‖gradₓ v (x, t₀)‖ ^ 2) * ψ x +
            Q x ^ 2 * (chiEps β ε v (x, t) - chiEps β ε v (x, t₀)) * ψ x := fun x ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hpt), integral_add hintD hintB]
      congr 1
    have hSpt : ∀ x, S t x = (-((v (x, t) - v (x, t₀)) * (ψ x * (lapₓ v (x, t) + lapₓ v (x, t₀)) +
          ⟪gradₓ v (x, t) + gradₓ v (x, t₀), ∇ ψ x⟫)) +
        Q x ^ 2 * (chiEps β ε v (x, t) - chiEps β ε v (x, t₀)) * ψ x) / (t - t₀) := by
      intro x
      have : t - t₀ ≠ 0 := sub_ne_zero.2 htt
      simp only [hSdef, slope_def_field]
      field_simp
    have hintA' := hintA.neg
    simp only [Pi.neg_def] at hintA'
    rw [slope_def_field, hdiff, integral_congr_ae (ae_of_all _ hSpt), integral_div,
      integral_add hintA' hintB, integral_neg]
  -- the limit
  set S₀ : E d → ℝ := fun x ↦
    -2 * ψ x * dₜ v (x, t₀) ^ 2 - 2 * dₜ v (x, t₀) * ⟪gradₓ v (x, t₀), ∇ ψ x⟫ with hS₀def
  have hlim : ∀ x, Tendsto (fun t ↦ S t x) (𝓝[≠] t₀) (𝓝 (S₀ x)) := by
    intro x
    by_cases hx : x ∈ K
    · have hxU := hψU hx
      have hpt : (x, t₀) ∈ U ×ˢ Ioi 0 := ⟨hxU, ht₀⟩
      have hopen : U ×ˢ Ioi (0 : ℝ) ∈ 𝓝 (x, t₀) := (hU.prod isOpen_Ioi).mem_nhds hpt
      have hpath : Tendsto (fun t : ℝ ↦ (x, t)) (𝓝[≠] t₀) (𝓝 (x, t₀)) :=
        ((continuous_const.prodMk continuous_id).tendsto t₀).mono_left nhdsWithin_le_nhds
      have T1 := (hdv x hxU t₀ ht₀).tendsto_slope
      have T2 := (hdχ x hxU t₀ ht₀).tendsto_slope
      have Tl := ((hlc.continuousAt hopen).tendsto).comp hpath
      have Tg := ((hgc.continuousAt hopen).tendsto).comp hpath
      have hL := (T1.neg.mul (((tendsto_const_nhds (x := ψ x)).mul
        (Tl.add (tendsto_const_nhds (x := lapₓ v (x, t₀))))).add
        ((Tg.add (tendsto_const_nhds (x := gradₓ v (x, t₀)))).inner
          (tendsto_const_nhds (x := ∇ ψ x))))).add
        (((tendsto_const_nhds (x := Q x ^ 2)).mul T2).mul (tendsto_const_nhds (x := ψ x)))
      convert hL using 2
      simp only [hS₀def]
      rw [heq (x, t₀) hpt, inner_add_left]
      ring
    · simp only [hS0 _ x hx]
      have : S₀ x = 0 := by simp [hS₀def, hψ0 x hx, hgψ0 x hx]
      rw [this]
      exact tendsto_const_nhds
  set B := C * (C * (C + C) + (C + C) * C) + C ^ 2 * (2 * (C * C)) * C with hBdef
  have hbound : ∀ t ∈ I, ∀ x, ‖S t x‖ ≤ K.indicator (fun _ ↦ B) x := by
    intro t ht x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Real.norm_eq_abs]
      have hxU := hψU hx
      have hs1 : |slope (fun s ↦ v (x, s)) t₀ t| ≤ C :=
        abs_slope_le_of_hasDerivAt_Icc (fun s hs ↦ hdv x hxU s (hI hs))
          (fun s hs ↦ (hbd (x, s) ⟨hx, hs⟩).1) ht₀I ht
      have hs2 : |slope (fun s ↦ chiEps β ε v (x, s)) t₀ t| ≤ 2 * (C * C) :=
        abs_slope_le_of_hasDerivAt_Icc (fun s hs ↦ hdχ x hxU s (hI hs))
          (fun s hs ↦ by
            rw [abs_mul, abs_two, abs_mul]
            gcongr
            · exact (hbd (x, s) ⟨hx, hs⟩).2.2.2
            · exact (hbd (x, s) ⟨hx, hs⟩).1) ht₀I ht
      have hb := hbd (x, t) ⟨hx, ht⟩
      have hb₀ := hbd (x, t₀) ⟨hx, ht₀I⟩
      have hin : |⟪gradₓ v (x, t) + gradₓ v (x, t₀), ∇ ψ x⟫| ≤ (C + C) * C :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul ((norm_add_le _ _).trans
          (add_le_add hb.2.2.1 hb₀.2.2.1)) (hgψb x) (norm_nonneg _) (by linarith))
      have hlap : |ψ x * (lapₓ v (x, t) + lapₓ v (x, t₀))| ≤ C * (C + C) := by
        rw [abs_mul]
        exact mul_le_mul (hψb x) ((abs_add_le _ _).trans (add_le_add hb.2.1 hb₀.2.1))
          (abs_nonneg _) hC0
      simp only [hSdef]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_neg]
        exact mul_le_mul hs1 ((abs_add_le _ _).trans (add_le_add hlap hin)) (abs_nonneg _) hC0
      · rw [abs_mul, abs_mul, abs_pow]
        refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hQb x hx) 2) hs2
          (abs_nonneg _) (by positivity)) (hψb x) (abs_nonneg _) (by positivity)
    · rw [indicator_of_notMem hx, hS0 t x hx, norm_zero]
  have hev : ∀ᶠ t in 𝓝[≠] t₀, t ∈ I ∧ t ≠ t₀ := by
    have h1 : ∀ᶠ t in 𝓝[≠] t₀, t ∈ I :=
      nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
    filter_upwards [h1, self_mem_nhdsWithin] with t ht htt using ⟨ht, htt⟩
  have hDCT : Tendsto (fun t ↦ ∫ x, S t x) (𝓝[≠] t₀) (𝓝 (∫ x, S₀ x)) :=
    tendsto_integral_filter_of_dominated_convergence (K.indicator fun _ ↦ B)
      (hev.mono fun t ht ↦ (hSi t ht.1).aestronglyMeasurable)
      (hev.mono fun t ht ↦ ae_of_all _ (hbound t ht.1))
      ((integrable_indicator_iff hK.measurableSet).2
        (continuousOn_const.integrableOn_compact hK)) (ae_of_all _ hlim)
  rw [hasDerivAt_iff_tendsto_slope]
  exact hDCT.congr' (hev.mono fun t ht ↦ (hrepr t ht.1 ht.2).symm)

/-- Pointwise bound for the integrand of the derivative of the energy moment. -/
theorem abs_energyMomentDeriv_le {ψ : E d → ℝ} {Cψ L a : ℝ} {g : E d} {x : E d}
    (hψ : |ψ x| ≤ Cψ) (hgψ : ‖∇ ψ x‖ ≤ Cψ) (hg : ‖g‖ ≤ L) (hL : 0 ≤ L) :
    |-2 * ψ x * a ^ 2 - 2 * a * ⟪g, ∇ ψ x⟫| ≤ 2 * Cψ * (1 + L) * (a ^ 2 + 1) := by
  have hC : 0 ≤ Cψ := (abs_nonneg _).trans hψ
  have h1 : |-2 * ψ x * a ^ 2| ≤ 2 * Cψ * a ^ 2 := by
    rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_nonneg (sq_nonneg a)]
    gcongr
  have h2 : |2 * a * ⟪g, ∇ ψ x⟫| ≤ 2 * |a| * (L * Cψ) := by
    rw [abs_mul, abs_mul, abs_two]
    gcongr
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hg hgψ (norm_nonneg _) hL)
  have h3 : |a| ≤ a ^ 2 + 1 := by
    rcases le_total (|a|) 1 with h | h
    · nlinarith [sq_nonneg a, abs_nonneg a]
    · nlinarith [sq_abs a, abs_nonneg a]
  have h4 : 2 * |a| * (L * Cψ) ≤ 2 * (a ^ 2 + 1) * (L * Cψ) := by gcongr
  calc |-2 * ψ x * a ^ 2 - 2 * a * ⟪g, ∇ ψ x⟫|
      ≤ |-2 * ψ x * a ^ 2| + |2 * a * ⟪g, ∇ ψ x⟫| := abs_sub _ _
    _ ≤ 2 * Cψ * a ^ 2 + 2 * (a ^ 2 + 1) * (L * Cψ) := by linarith
    _ ≤ 2 * Cψ * (1 + L) * (a ^ 2 + 1) := by nlinarith [sq_nonneg a, mul_nonneg hC hL]

/-- **Increment of the energy moment** ((4.8)): with
`|ψ|, |∇ψ| ≤ Cψ`, `|∇v| ≤ L` on `spt ψ × [t₁, t₂]` and `spt ψ ⊆ K`,
`|∫ e(t₂) ψ - ∫ e(t₁) ψ| ≤ 2 Cψ (1 + L) ∫_{t₁}^{t₂} ∫_K ((∂ₜv)² + 1)`. -/
theorem enorm_energyMoment_sub_le {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ}
    (hQ : ContinuousOn Q U) {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ}
    {v : E d × ℝ → ℝ} (hv : IsSemilinearSolOn U Q β ε (Ioi 0) v) {ψ : E d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) {K : Set (E d)}
    (hKm : MeasurableSet K) (hψK : tsupport ψ ⊆ K) {Cψ L : ℝ} (hψb : ∀ x, |ψ x| ≤ Cψ)
    (hgψb : ∀ x, ‖∇ ψ x‖ ≤ Cψ) (hL0 : 0 ≤ L) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂)
    (hL : ∀ x ∈ tsupport ψ, ∀ τ ∈ Icc t₁ t₂, ‖gradₓ v (x, τ)‖ ≤ L) :
    ‖energyMoment Q β ε v ψ t₂ - energyMoment Q β ε v ψ t₁‖ₑ ≤
      ENNReal.ofReal (2 * Cψ * (1 + L)) *
        ∫⁻ τ in Ioc t₁ t₂, ∫⁻ x in K, (ENNReal.ofReal (dₜ v (x, τ) ^ 2) + 1) := by
  set a := energyMoment Q β ε v ψ with hadef
  set c := 2 * Cψ * (1 + L) with hcdef
  have hC : 0 ≤ Cψ := (abs_nonneg _).trans (hψb 0)
  have hc0 : 0 ≤ c := by positivity
  set S₀ : ℝ → E d → ℝ := fun τ x ↦
    -2 * ψ x * dₜ v (x, τ) ^ 2 - 2 * dₜ v (x, τ) * ⟪gradₓ v (x, τ), ∇ ψ x⟫ with hS₀def
  have hder : ∀ τ ∈ Icc t₁ t₂, HasDerivAt a (∫ x, S₀ τ x) τ := fun τ hτ ↦
    hasDerivAt_energyMoment hU hQ hβ hv hψ hψc hψU (ht₁.trans_le hτ.1)
  have hψ0 : ∀ x ∉ tsupport ψ, ψ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hgψ0 : ∀ x ∉ tsupport ψ, ∇ ψ x = 0 := fun x hx ↦ gradient_eq_zero_of_notMem_tsupport hx
  have hpt : ∀ τ ∈ Icc t₁ t₂, ∀ x, |S₀ τ x| ≤
      (tsupport ψ).indicator (fun x ↦ c * (dₜ v (x, τ) ^ 2 + 1)) x := by
    intro τ hτ x
    by_cases hx : x ∈ tsupport ψ
    · rw [indicator_of_mem hx]
      exact abs_energyMomentDeriv_le (hψb x) (hgψb x) (hL x hx τ hτ) hL0
    · rw [indicator_of_notMem hx]
      simp [hS₀def, hψ0 x hx, hgψ0 x hx]
  -- a bound for the derivative on `[t₁, t₂]`
  have hKc : IsCompact (tsupport ψ ×ˢ Icc t₁ t₂) := hψc.prod isCompact_Icc
  have hKcU : tsupport ψ ×ˢ Icc t₁ t₂ ⊆ U ×ˢ Ioi 0 :=
    prod_mono hψU fun τ hτ ↦ ht₁.trans_le hτ.1
  obtain ⟨Cd, hCd⟩ := hKc.exists_bound_of_continuousOn (hv.2.2.2.2.2.1.mono hKcU)
  set M := ∫ x, (tsupport ψ).indicator (fun _ ↦ c * (Cd ^ 2 + 1)) x with hMdef
  have hMi : Integrable ((tsupport ψ).indicator (fun _ : E d ↦ c * (Cd ^ 2 + 1))) :=
    (integrable_indicator_iff (isClosed_tsupport ψ).measurableSet).2
      (continuousOn_const.integrableOn_compact hψc)
  have hbd : ∀ τ ∈ Icc t₁ t₂, ‖∫ x, S₀ τ x‖ ≤ M := by
    intro τ hτ
    refine norm_integral_le_of_norm_le hMi (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    refine (hpt τ hτ x).trans ?_
    by_cases hx : x ∈ tsupport ψ
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      have h := hCd (x, τ) ⟨hx, hτ⟩
      rw [Real.norm_eq_abs] at h
      have : dₜ v (x, τ) ^ 2 ≤ Cd ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      gcongr
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  have hderiv' : ∀ τ ∈ Icc t₁ t₂, deriv a τ = ∫ x, S₀ τ x := fun τ hτ ↦ (hder τ hτ).deriv
  have hint : IntervalIntegrable (deriv a) volume t₁ t₂ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h12]
    refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (measurable_deriv a).aestronglyMeasurable (M := M) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun τ hτ ↦ ?_)
    rw [hderiv' τ (Ioc_subset_Icc_self hτ)]
    exact hbd τ (Ioc_subset_Icc_self hτ)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := a) (f' := deriv a)
    (fun τ hτ ↦ by
      rw [uIcc_of_le h12] at hτ
      exact (hder τ hτ).differentiableAt.hasDerivAt) hint
  rw [← hftc, intervalIntegral.integral_of_le h12, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (enorm_integral_le_lintegral_enorm _).trans (setLIntegral_mono' measurableSet_Ioc
    fun τ hτ ↦ ?_)
  have hτ' := Ioc_subset_Icc_self hτ
  rw [hderiv' τ hτ', ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_indicator hKm]
  refine lintegral_mono fun x ↦ ?_
  by_cases hx : x ∈ tsupport ψ
  · rw [indicator_of_mem (hψK hx), Real.enorm_eq_ofReal_abs]
    have h := hpt τ hτ' x
    rw [indicator_of_mem hx] at h
    calc ENNReal.ofReal |S₀ τ x| ≤ ENNReal.ofReal (c * (dₜ v (x, τ) ^ 2 + 1)) :=
          ENNReal.ofReal_le_ofReal h
      _ = _ := by
          rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_add (sq_nonneg _) zero_le_one,
            ENNReal.ofReal_one]
  · have : S₀ τ x = 0 := by simp [hS₀def, hψ0 x hx, hgψ0 x hx]
    rw [this, enorm_zero]
    exact zero_le

end Inner

end PerronVariational

end
