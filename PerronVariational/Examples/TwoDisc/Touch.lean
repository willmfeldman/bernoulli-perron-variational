/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
public import PerronVariational.Stationary.ViscosityJet
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Touching lemmas for explicit viscosity solutions

Tools for the two-disc model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`).

* `norm_gradient_le_of_ray`: if `φ(x) = W(x) = 0` and `φ ≤ W₊` along the ray from `x` in the
  direction `∇φ(x)`, then `|∇φ(x)| ≤ |∇W(x)|`. This is the free boundary condition for a test
  function touching `W₊` from below.
* `laplacian_le_of_touch`: a smooth function touching a `C²` function from below has smaller
  Laplacian at the touching point.
* `IsViscSuper.false_of_touch_contDiff_two`: a viscosity supersolution cannot be touched from below
  by a `C²` function with `Δ > 0` and `|∇| > Q` at the touching point (the `C²` function is
  replaced by a smooth quadratic below it with nearly the same 2-jet).
-/

open Set Filter Topology Metric InnerProductSpace
open scoped Gradient Laplacian ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace PerronVariational.TwoDisc

variable {d : ℕ}

theorem gradient_neg' (f : E d → ℝ) (x : E d) : ∇ (fun y ↦ -f y) x = -∇ f x := by
  simp [gradient]

/-- **Free boundary slope bound.** If `φ(x) = W(x) = 0`, `W` has gradient `G` at `x`, and
`φ ≤ max W 0` along the ray `t ↦ x + t ∇φ(x)`, `t → 0⁺`, then `|∇φ(x)| ≤ |G|`. -/
theorem norm_gradient_le_of_ray {φ W : E d → ℝ} {x G : E d} (hφ : DifferentiableAt ℝ φ x)
    (hW : HasGradientAt W G x) (hφx : φ x = 0) (hWx : W x = 0)
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ (x + t • ∇ φ x) ≤ max (W (x + t • ∇ φ x)) 0) :
    ‖∇ φ x‖ ≤ ‖G‖ := by
  set ξ := ∇ φ x with hξ
  rcases eq_or_ne ξ 0 with h0 | h0
  · rw [h0, norm_zero]; exact norm_nonneg _
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • ξ) ξ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add x
  have hx0 : x + (0 : ℝ) • ξ = x := by simp
  have hf : HasDerivAt (fun t : ℝ ↦ φ (x + t • ξ)) ⟪ξ, ξ⟫ 0 := by
    have hφ' : HasFDerivAt φ (toDual ℝ (E d) ξ) (x + (0 : ℝ) • ξ) := by
      rw [hx0]; exact hφ.hasGradientAt.hasFDerivAt
    have := hφ'.comp_hasDerivAt (0 : ℝ) hline
    convert this using 1 <;> rfl
  have hg : HasDerivAt (fun t : ℝ ↦ W (x + t • ξ)) ⟪G, ξ⟫ 0 := by
    have hW' : HasFDerivAt W (toDual ℝ (E d) G) (x + (0 : ℝ) • ξ) := by
      rw [hx0]; exact hW.hasFDerivAt
    have := hW'.comp_hasDerivAt (0 : ℝ) hline
    convert this using 1 <;> rfl
  have hsf := hf.tendsto_slope_zero_right
  have hsg := hg.tendsto_slope_zero_right
  simp only [zero_add, zero_smul, add_zero, hφx, hWx, sub_zero, smul_eq_mul] at hsf hsg
  -- `φ > 0` along the ray for small `t > 0`
  have hpos : 0 < ⟪ξ, ξ⟫ := by rw [real_inner_self_eq_norm_sq]; positivity
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ * φ (x + t • ξ) := hsf.eventually (lt_mem_nhds hpos)
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * φ (x + t • ξ) ≤ t⁻¹ * W (x + t • ξ) := by
    filter_upwards [hev, h, self_mem_nhdsWithin] with t ht1 ht2 ht3
    have ht3 : 0 < t := ht3
    have hφpos : 0 < φ (x + t • ξ) := by
      have := (mul_pos_iff_of_pos_left (inv_pos.2 ht3)).1 ht1; exact this
    have : φ (x + t • ξ) ≤ W (x + t • ξ) := by
      rcases le_total (W (x + t • ξ)) 0 with hW0 | hW0
      · rw [max_eq_right hW0] at ht2; linarith
      · rwa [max_eq_left hW0] at ht2
    exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 ht3.le)
  have key : ⟪ξ, ξ⟫ ≤ ⟪G, ξ⟫ := le_of_tendsto_of_tendsto hsf hsg hle
  rw [real_inner_self_eq_norm_sq] at key
  have hcs : ⟪G, ξ⟫ ≤ ‖G‖ * ‖ξ‖ := real_inner_le_norm _ _
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 h0
  nlinarith

/-- A smooth function touching a `C²` function `W` from below has smaller Laplacian. -/
theorem laplacian_le_of_touch {φ W : E d → ℝ} {x : E d} (hφ : ContDiff ℝ 2 φ)
    (hW : ContDiff ℝ 2 W) (hle : ∀ᶠ y in 𝓝 x, φ y ≤ W y) (heq : φ x = W x) :
    Δ φ x ≤ Δ W x := by
  have hmin : IsLocalMin (W - φ) x := by
    filter_upwards [hle] with y hy
    simp only [Pi.sub_apply]; rw [heq, sub_self]; linarith
  have h0 : 0 ≤ Δ (W - φ) x := IsLocalMin.laplacian_nonneg (hW.sub hφ) hmin
  rw [(hW.contDiffAt).laplacian_sub hφ.contDiffAt] at h0
  linarith

/-- At a local maximum of a differentiable function, the gradient vanishes. -/
theorem gradient_eq_zero_of_isLocalMax {φ : E d → ℝ} {x : E d} (h : IsLocalMax φ x) :
    ∇ φ x = 0 := by
  simp [gradient, h.fderiv_eq_zero]

/-- **A `C²` strict barrier cannot touch a supersolution from below.** If `V` is a viscosity
supersolution in `U`, `z ∈ U`, and a `C²` function `Φ` with `ΔΦ(z) > 0` and `|∇Φ(z)| > Q(z)`
touches `V` from below at `z`, we have a contradiction. -/
theorem IsViscSuper.false_of_touch_contDiff_two {U : Set (E d)} {Q V Φ : E d → ℝ}
    (hd : 0 < d) (hU : IsOpen U) (hV : IsViscSuper U Q V) {z : E d} (hz : z ∈ U)
    (hΦ : ContDiff ℝ 2 Φ)
    (hle : ∀ᶠ y in 𝓝 z, Φ y ≤ V y) (heq : Φ z = V z) (hlap : 0 < Δ Φ z)
    (hgrad : Q z < ‖∇ Φ z‖) : False := by
  have hd : 0 < (Module.finrank ℝ (E d) : ℝ) := by simpa using hd
  set η := Δ Φ z / (4 * (Module.finrank ℝ (E d) : ℝ)) with hη
  have hη0 : 0 < η := div_pos hlap (by positivity)
  obtain ⟨ψ', hψ's, hψ'z, hψ'g, hψ'l, hψ'le⟩ :=
    exists_smooth_ge_of_contDiff_two (H := fun y ↦ -Φ y) hΦ.neg z hη0
  set ψ : E d → ℝ := fun y ↦ -ψ' y with hψ
  have hψs : ContDiff ℝ ∞ ψ := hψ's.neg
  have hψz : ψ z = Φ z := by simp [hψ, hψ'z]
  have hψg : ∇ ψ z = ∇ Φ z := by
    rw [hψ, gradient_neg', hψ'g, gradient_neg', neg_neg]
  have hψl : Δ ψ z = Δ Φ z / 2 := by
    have h1 : Δ ψ z = -Δ ψ' z := by
      rw [show ψ = -ψ' from rfl, InnerProductSpace.laplacian_neg]; rfl
    have h2 : Δ (fun y ↦ -Φ y) z = -Δ Φ z := by
      rw [show (fun y ↦ -Φ y) = -Φ from rfl, InnerProductSpace.laplacian_neg]; rfl
    rw [h1, hψ'l, h2, hη]
    field_simp
    ring
  have htouch : TouchesBelow ψ V U z := by
    refine ⟨hz, by rw [hψz, heq], ?_⟩
    rw [hU.nhdsWithin_eq hz]
    filter_upwards [hle, hψ'le] with y hy1 hy2
    simp only [hψ]; linarith
  rcases hV.2.2 ψ hψs z hz htouch with h | ⟨-, h⟩
  · rw [hψl] at h; linarith
  · rw [hψg] at h; linarith

end PerronVariational.TwoDisc

end
