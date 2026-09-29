/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.Bernstein
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Bernstein change of variables as a smooth diffeomorphism of `ℝ`

Steps 1 and 4 of the joint proof of Propositions A.5 and A.6 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.4).
The change of variables `u = φ(v)` is used on `[0, v_max]` only; to invert it globally and
smoothly we extend `φ` outside `[-1, v_max + 1]` by adding `g(v - v_max - 1) - g(-1 - v)`,
`g(x) = x e^{-1/x}` (`x > 0`), which makes it a smooth increasing bijection `Φ` of `ℝ` with
`Φ = φ` on `[-1, v_max + 1]`. We use the smooth cutoff `ψ₀(x) = smoothTransition(1 - x)`.

## Main definitions

* `Bernstein.psi0`, `Bernstein.bigPhi` (`Φ`), `Bernstein.bigPsi` (`Φ⁻¹`).

## Main results

* `contDiff_ell`, `contDiff_phiDeriv`, `contDiff_phi` (for `ψ = ψ₀`);
* `contDiff_bigPhi`, `strictMono_bigPhi`, `deriv_bigPhi_pos`, `contDiff_bigPsi`,
  `bigPhi_bigPsi`, `bigPsi_bigPhi`;
* `bigPhi_eventuallyEq`: `Φ = φ` near every point of `(-1, v_max + 1)`.
-/

open Set Filter Topology intervalIntegral Real
open scoped ContDiff

@[expose] public section

namespace PerronVariational

namespace Bernstein

/-- The smooth cutoff `ψ₀(x) = smoothTransition(1 - x)` of Step 4. -/
noncomputable def psi0 (x : ℝ) : ℝ := smoothTransition (1 - x)

theorem isBernsteinCutoff_psi0 : IsBernsteinCutoff psi0 := isBernsteinCutoff_smoothTransition

theorem contDiff_psi0 : ContDiff ℝ ∞ psi0 :=
  smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

variable {ε M : ℝ}

theorem contDiff_ellIntegrand : ContDiff ℝ ∞ (ellIntegrand psi0 ε M) := by
  unfold ellIntegrand
  exact (contDiff_const.mul (contDiff_psi0.comp
    ((contDiff_id.sub contDiff_const).div_const _))).add contDiff_const

theorem contDiff_ell : ContDiff ℝ ∞ (ell psi0 ε M) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun v ↦ (hasDerivAt_ell isBernsteinCutoff_psi0 v).differentiableAt, ?_⟩
  have : deriv (ell psi0 ε M) = fun v ↦ -ellIntegrand psi0 ε M v :=
    funext fun v ↦ (hasDerivAt_ell isBernsteinCutoff_psi0 v).deriv
  rw [this]
  exact contDiff_ellIntegrand.neg

theorem deriv_ell (v : ℝ) : deriv (ell psi0 ε M) v = ellDeriv psi0 ε M v :=
  (hasDerivAt_ell isBernsteinCutoff_psi0 v).deriv

/-- `F(v) = ∫₀^v ℓ` is smooth. -/
theorem contDiff_integral_ell : ContDiff ℝ ∞ (fun v ↦ ∫ s in (0 : ℝ)..v, ell psi0 ε M s) := by
  have hd : ∀ v, HasDerivAt (fun v ↦ ∫ s in (0 : ℝ)..v, ell psi0 ε M s) (ell psi0 ε M v) v :=
    fun v ↦ ((continuous_ell isBernsteinCutoff_psi0).integral_hasStrictDerivAt 0 v).hasDerivAt
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun v ↦ (hd v).differentiableAt, ?_⟩
  rw [show deriv (fun v ↦ ∫ s in (0 : ℝ)..v, ell psi0 ε M s) = ell psi0 ε M from
    funext fun v ↦ (hd v).deriv]
  exact contDiff_ell

theorem contDiff_phiDeriv : ContDiff ℝ ∞ (phiDeriv psi0 ε M) :=
  contDiff_integral_ell.exp

theorem contDiff_phi : ContDiff ℝ ∞ (phi psi0 ε M) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun v ↦ (hasDerivAt_phi isBernsteinCutoff_psi0 v).differentiableAt, ?_⟩
  rw [show deriv (phi psi0 ε M) = phiDeriv psi0 ε M from
    funext fun v ↦ (hasDerivAt_phi isBernsteinCutoff_psi0 v).deriv]
  exact contDiff_phiDeriv

theorem strictMono_phi : StrictMono (phi psi0 ε M) :=
  strictMono_of_deriv_pos fun v ↦ by
    rw [(hasDerivAt_phi isBernsteinCutoff_psi0 v).deriv]; exact phiDeriv_pos v

/-! ### The gluing function `g(x) = x e^{-1/x}` -/

/-- `g(x) = x e^{-1/x}` for `x > 0`, `0` for `x ≤ 0`. -/
noncomputable def glue (x : ℝ) : ℝ := expNegInvGlue x * x

theorem glue_of_nonpos {x : ℝ} (hx : x ≤ 0) : glue x = 0 := by
  simp [glue, expNegInvGlue.zero_of_nonpos hx]

theorem glue_nonneg (x : ℝ) : 0 ≤ glue x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [glue_of_nonpos hx]
  · exact mul_nonneg (expNegInvGlue.nonneg x) hx.le

theorem monotone_glue : Monotone glue := by
  intro x y hxy
  rcases le_or_gt x 0 with hx | hx
  · rw [glue_of_nonpos hx]; exact glue_nonneg y
  · exact mul_le_mul (expNegInvGlue.monotone hxy) hxy hx.le (expNegInvGlue.nonneg y)

theorem contDiff_glue : ContDiff ℝ ∞ glue :=
  expNegInvGlue.contDiff.mul contDiff_id

theorem le_glue {x : ℝ} (hx : 1 ≤ x) : exp (-1) * x ≤ glue x := by
  have hx0 : 0 < x := by linarith
  refine mul_le_mul_of_nonneg_right ?_ hx0.le
  simp only [expNegInvGlue, not_le.2 hx0, if_false]
  exact exp_le_exp.2 (by rw [neg_le_neg_iff]; exact inv_le_one_of_one_le₀ hx)

/-! ### The global diffeomorphism `Φ` -/

variable (ε M) in
/-- `Φ(v) = φ(v) + g(v - v_max - 1) - g(-1 - v)`: equal to `φ` on `[-1, v_max + 1]`, and a smooth
increasing bijection of `ℝ`. -/
noncomputable def bigPhi (v : ℝ) : ℝ :=
  phi psi0 ε M v + glue (v - (vmax ε M + 1)) - glue (-1 - v)

theorem bigPhi_eq {v : ℝ} (hv : v ∈ Icc (-1) (vmax ε M + 1)) : bigPhi ε M v = phi psi0 ε M v := by
  rw [bigPhi, glue_of_nonpos (by linarith [hv.2]), glue_of_nonpos (by linarith [hv.1])]
  ring

theorem bigPhi_eventuallyEq {v : ℝ} (hv : v ∈ Ioo (-1) (vmax ε M + 1)) :
    bigPhi ε M =ᶠ[𝓝 v] phi psi0 ε M := by
  filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw using bigPhi_eq (Ioo_subset_Icc_self hw)

theorem contDiff_bigPhi : ContDiff ℝ ∞ (bigPhi ε M) := by
  unfold bigPhi
  exact (contDiff_phi.add (contDiff_glue.comp (contDiff_id.sub contDiff_const))).sub
    (contDiff_glue.comp (contDiff_const.sub contDiff_id))

theorem monotone_glue_neg : Monotone fun v : ℝ ↦ -glue (-1 - v) :=
  fun _ _ h ↦ neg_le_neg (monotone_glue (by linarith))

theorem strictMono_bigPhi : StrictMono (bigPhi ε M) := by
  intro x y hxy
  have h1 := strictMono_phi (ε := ε) (M := M) hxy
  have h2 := monotone_glue (show x - (vmax ε M + 1) ≤ y - (vmax ε M + 1) by linarith)
  have h3 := monotone_glue_neg hxy.le
  simp only at h3
  rw [bigPhi, bigPhi]
  linarith

theorem deriv_bigPhi_pos (v : ℝ) : 0 < deriv (bigPhi ε M) v := by
  have hd1 : DifferentiableAt ℝ (phi psi0 ε M) v :=
    (hasDerivAt_phi isBernsteinCutoff_psi0 v).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun v ↦ glue (v - (vmax ε M + 1))) v :=
    ((contDiff_glue.comp (contDiff_id.sub contDiff_const)).differentiable (by simp)) v
  have hd3 : DifferentiableAt ℝ (fun v ↦ -glue (-1 - v)) v :=
    ((contDiff_glue.comp (contDiff_const.sub contDiff_id)).neg.differentiable (by simp)) v
  have e : bigPhi ε M = (phi psi0 ε M + fun v ↦ glue (v - (vmax ε M + 1))) +
      fun v ↦ -glue (-1 - v) := funext fun v ↦ by simp only [bigPhi, Pi.add_apply]; ring
  have H := (((hasDerivAt_phi isBernsteinCutoff_psi0 (ε := ε) (M := M) v).add
    hd2.hasDerivAt).add hd3.hasDerivAt)
  rw [e, H.deriv]
  have h2 : 0 ≤ deriv (fun v ↦ glue (v - (vmax ε M + 1))) v :=
    Monotone.deriv_nonneg fun _ _ h ↦ monotone_glue (by linarith)
  have h3 : 0 ≤ deriv (fun v ↦ -glue (-1 - v)) v := monotone_glue_neg.deriv_nonneg
  linarith [phiDeriv_pos (ψ := psi0) (ε := ε) (M := M) v]

theorem phi_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ phi psi0 ε M v := by
  rw [← phi_zero (ψ := psi0) (ε := ε) (M := M)]
  exact strictMono_phi.monotone hv

theorem phi_nonpos {v : ℝ} (hv : v ≤ 0) : phi psi0 ε M v ≤ 0 := by
  rw [← phi_zero (ψ := psi0) (ε := ε) (M := M)]
  exact strictMono_phi.monotone hv

theorem surjective_bigPhi : Function.Surjective (bigPhi ε M) := by
  refine contDiff_bigPhi.continuous.surjective ?_ ?_
  · -- `Φ(v) ≥ e⁻¹ (v - v_max - 1)` for large `v`
    have hlin : Tendsto (fun v : ℝ ↦ exp (-1) * (v - (vmax ε M + 1))) atTop atTop :=
      (tendsto_atTop_add_const_right _ _ tendsto_id).const_mul_atTop (exp_pos (-1))
    refine tendsto_atTop_mono' atTop ?_ hlin
    filter_upwards [eventually_ge_atTop (vmax ε M + 2), eventually_ge_atTop 0] with v hv hv0
    have h1 := le_glue (show 1 ≤ v - (vmax ε M + 1) by linarith)
    have h2 := phi_nonneg (ε := ε) (M := M) hv0
    rw [bigPhi, glue_of_nonpos (show -1 - v ≤ 0 by linarith)]
    linarith
  · -- `Φ(v) ≤ e⁻¹ (v + 1)` for very negative `v`
    have hlin : Tendsto (fun v : ℝ ↦ exp (-1) * (v + 1)) atBot atBot :=
      (tendsto_atBot_add_const_right _ _ tendsto_id).const_mul_atBot (exp_pos (-1))
    refine tendsto_atBot_mono' atBot ?_ hlin
    filter_upwards [eventually_le_atBot (-2), eventually_le_atBot 0,
      eventually_le_atBot (vmax ε M + 1)] with v hv hv0 hv1
    have h1 := le_glue (show 1 ≤ -1 - v by linarith)
    have h2 := phi_nonpos (ε := ε) (M := M) hv0
    rw [bigPhi, glue_of_nonpos (show v - (vmax ε M + 1) ≤ 0 by linarith)]
    linarith

variable (ε M) in
/-- `Φ` as a homeomorphism of `ℝ`. -/
noncomputable def bigPhiHomeo : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (bigPhi ε M) strictMono_bigPhi surjective_bigPhi).toHomeomorph

variable (ε M) in
/-- `Ψ = Φ⁻¹`. -/
noncomputable def bigPsi : ℝ → ℝ := (bigPhiHomeo ε M).symm

theorem bigPhiHomeo_apply (v : ℝ) : bigPhiHomeo ε M v = bigPhi ε M v := rfl

theorem bigPhi_bigPsi (s : ℝ) : bigPhi ε M (bigPsi ε M s) = s :=
  (bigPhiHomeo ε M).apply_symm_apply s

theorem bigPsi_bigPhi (v : ℝ) : bigPsi ε M (bigPhi ε M v) = v :=
  (bigPhiHomeo ε M).symm_apply_apply v

theorem contDiff_bigPsi : ContDiff ℝ ∞ (bigPsi ε M) :=
  (bigPhiHomeo ε M).contDiff_symm_deriv (fun v ↦ (deriv_bigPhi_pos v).ne')
    (fun v ↦ (contDiff_bigPhi.differentiable (by simp) v).hasDerivAt) contDiff_bigPhi

theorem continuous_bigPsi : Continuous (bigPsi ε M) := (bigPhiHomeo ε M).symm.continuous

theorem monotone_bigPsi : Monotone (bigPsi ε M) := fun x y hxy ↦ by
  by_contra h
  have := strictMono_bigPhi (ε := ε) (M := M) (lt_of_not_ge h)
  rw [bigPhi_bigPsi, bigPhi_bigPsi] at this
  linarith

/-! ### `Φ` near `[0, v_max]` -/

theorem deriv_bigPhi_eq {v : ℝ} (hv : v ∈ Ioo (-1) (vmax ε M + 1)) :
    deriv (bigPhi ε M) v = phiDeriv psi0 ε M v := by
  rw [(bigPhi_eventuallyEq hv).deriv_eq, (hasDerivAt_phi isBernsteinCutoff_psi0 v).deriv]

theorem deriv_bigPhi_eventuallyEq {v : ℝ} (hv : v ∈ Ioo (-1) (vmax ε M + 1)) :
    deriv (bigPhi ε M) =ᶠ[𝓝 v] phiDeriv psi0 ε M := by
  filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw using deriv_bigPhi_eq hw

theorem deriv_deriv_bigPhi_eq {v : ℝ} (hv : v ∈ Ioo (-1) (vmax ε M + 1)) :
    deriv (deriv (bigPhi ε M)) v = ell psi0 ε M v * phiDeriv psi0 ε M v := by
  rw [(deriv_bigPhi_eventuallyEq hv).deriv_eq,
    (hasDerivAt_phiDeriv isBernsteinCutoff_psi0 v).deriv]

end Bernstein

end PerronVariational

end
