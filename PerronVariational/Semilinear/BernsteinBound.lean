/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.BernsteinMax
public import PerronVariational.Semilinear.BernsteinPhi
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Semilinear.Profiles

/-!
# The bound on `z` at its maximum (Step 3, case analysis)

Steps 2–3 of the joint proof of Propositions A.5 and A.6 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.4):
the bounds on `k_v`, `∇ₓk` and the analysis of (A.10) in the regions `{v < ε}` and `{v ≥ ε}`.

We run the argument at scale `r ≤ 1` (no rescaling) with the Bernstein function built from
`ε' = min(ε, r)`; the case `ε > r` (Step 5 of the paper, "`ε ≥ 1`" after rescaling) is covered by
the same computation: in `{v ≥ ε'}` the reaction term is bounded by `C/r²`.

## Main result

* `zmax_bound`: at a maximum point (relative to the parabolic past) of
  `z = η² |∇u|²/Φ'(Φ⁻¹(u))²`, `z ≤ max(1, ε'² C_η + 2C₁ + 2βₘₐₓN, 8 v_max² (C_η + 2C₁/r² +
  2βₘₐₓN/r))`.
-/

open Set Filter Topology Finset
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

/-! ### Facts on `β` -/

namespace IsReactionProfile

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β)
include hβ

theorem deriv_eq_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) : deriv β s = 0 := by
  have hd : DifferentiableAt ℝ β s := hβ.contDiff.differentiable (by simp) s
  rw [← hd.derivWithin (uniqueDiffOn_Ici 1 s hs)]
  rw [derivWithin_congr (f₁ := β) (f := fun _ ↦ (0 : ℝ)) (s := Ici 1)
    (fun t (ht : t ∈ Ici (1 : ℝ)) ↦ hβ.eq_zero_of_one_le ht) (hβ.eq_zero_of_one_le hs)]
  simp

theorem deriv_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : deriv β s = 0 := by
  have hd : DifferentiableAt ℝ β s := hβ.contDiff.differentiable (by simp) s
  rw [← hd.derivWithin (uniqueDiffOn_Iic 0 s hs)]
  rw [derivWithin_congr (f₁ := β) (f := fun _ ↦ (0 : ℝ)) (s := Iic 0)
    (fun t (ht : t ∈ Iic (0 : ℝ)) ↦ hβ.eq_zero_of_nonpos ht) (hβ.eq_zero_of_nonpos hs)]
  simp

/-- `|β'| ≤ Lβ`. -/
theorem exists_abs_deriv_le : ∃ Lβ : ℝ, 0 ≤ Lβ ∧ ∀ s, |deriv β s| ≤ Lβ := by
  have hc : Continuous (deriv β) := hβ.contDiff.continuous_deriv (by simp)
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨max L 0, le_max_right _ _, fun s ↦ ?_⟩
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · exact (by simpa using hL s hs : |deriv β s| ≤ L).trans (le_max_left _ _)
  · rcases not_and_or.1 hs with h | h
    · rw [hβ.deriv_eq_zero_of_nonpos (le_of_lt (not_le.1 h)), abs_zero]
      exact le_max_right _ _
    · rw [hβ.deriv_eq_zero_of_one_le (le_of_lt (not_le.1 h)), abs_zero]
      exact le_max_right _ _

theorem hasDerivAt_betaEps (ε z : ℝ) :
    HasDerivAt (betaEps β ε) (deriv β (z / ε) / ε ^ 2) z := by
  have h1 : HasDerivAt (fun z ↦ z / ε) (1 / ε) z := (hasDerivAt_id z).div_const ε
  have h2 := ((hβ.contDiff.differentiable (by simp) (z / ε)).hasDerivAt.comp z h1).div_const ε
  convert h2 using 1
  rw [sq]; field_simp

end IsReactionProfile

namespace BernsteinMax

open Bernstein

variable {d : ℕ}

/-- `w = |∇u|²/Φ'(Ψ(u))²` (global version of `|∇v|²`, `v = Ψ(u)`). -/
noncomputable def wGlob (Φ Ψ : ℝ → ℝ) (u : E d × ℝ → ℝ) (q : E d × ℝ) : ℝ :=
  ‖gradₓ u q‖ ^ 2 / deriv Φ (Ψ (u q)) ^ 2

/-- On the set where `u` is smooth, `wGlob = |∇(Ψ ∘ u)|²`. -/
theorem wOf_eq_wGlob {Φ Ψ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦ' : ∀ s, 0 < deriv Φ s)
    (hΨ : ContDiff ℝ ∞ Ψ) (hΦΨ : ∀ s, Φ (Ψ s) = s) {u : E d × ℝ → ℝ} {q : E d × ℝ}
    (hu : DifferentiableAt ℝ u q) :
    wOf (fun q ↦ Ψ (u q)) q = wGlob Φ Ψ u q := by
  have hΨd : DifferentiableAt ℝ Ψ (u q) := hΨ.differentiable (by simp) _
  -- `Ψ'(s) Φ'(Ψ s) = 1`
  have hinv : deriv Ψ (u q) * deriv Φ (Ψ (u q)) = 1 := by
    have h1 : HasDerivAt (fun s ↦ Φ (Ψ s)) (deriv Φ (Ψ (u q)) * deriv Ψ (u q)) (u q) :=
      (hΦ.differentiable (by simp) _).hasDerivAt.comp _ hΨd.hasDerivAt
    have h2 : HasDerivAt (fun s ↦ Φ (Ψ s)) 1 (u q) := by
      simp only [hΦΨ]; exact hasDerivAt_id _
    rw [mul_comm]; exact h1.unique h2
  have hpos := hΦ' (Ψ (u q))
  simp only [wOf, wGlob]
  rw [norm_gradₓ_sq hu, sum_div]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [dd_comp hΨd hu]
  field_simp
  have : deriv Ψ (u q) = 1 / deriv Φ (Ψ (u q)) := by field_simp; linarith
  rw [this]; field_simp

/-- The Bernstein function at scale `r`: built from `ε' = min(ε, r)`. -/
theorem ellOf_bigPhi_eventuallyEq {ε M v : ℝ} (hv : v ∈ Ioo (-1) (vmax ε M + 1)) :
    ellOf (bigPhi ε M) =ᶠ[𝓝 v] ell psi0 ε M := by
  filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
  rw [ellOf, deriv_deriv_bigPhi_eq hw, deriv_bigPhi_eq hw]
  have := phiDeriv_pos (ψ := psi0) (ε := ε) (M := M) w
  field_simp

theorem abs_ell_le {ε M v : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hv : v ∈ Icc 0 (vmax ε M)) :
    |ell psi0 ε M v| ≤ 2 / ε := by
  rcases le_total v ε with h | h
  · rw [abs_of_nonneg (ell_nonneg_of_le isBernsteinCutoff_psi0 hε hM h)]
    exact ell_le_of_mem isBernsteinCutoff_psi0 hε hM ⟨hv.1, h⟩
  · rw [abs_of_nonpos (ell_nonpos_of_le isBernsteinCutoff_psi0 hε hM h)]
    have h1 := (ell_bounds_of_le isBernsteinCutoff_psi0 hε hM h).2
    have h2 := rho_div_mul_vmax hε hM
    have h3 := acoef_mul_vmax_sq hε hM
    have hv0 := vmax_pos hε hM
    have hev := eps_le_vmax (ε := ε) hM
    -- `ρ/ε² + a (v - ε) ≤ 1/(64 v_max) + 1/(8 v_max) ≤ 1/ε`
    have h4 : rho ε M / ε ^ 2 ≤ 1 / (64 * vmax ε M) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h5 : acoef ε M * (v - ε) ≤ 1 / (8 * vmax ε M) := by
      rw [le_div_iff₀ (by positivity)]
      have ha := acoef_pos hε hM
      nlinarith [hv.2]
    have h6 : 1 / (64 * vmax ε M) + 1 / (8 * vmax ε M) ≤ 2 / ε := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hε]
      nlinarith
    linarith

/-- Numeric conclusion in the transition region `v < ε'`. -/
theorem zmax_caseA {z a Cη η2 X ε' C₁ βN : ℝ} (hz : 0 ≤ z) (hη2 : 0 ≤ η2) (hη21 : η2 ≤ 1)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hC₁ : 0 ≤ C₁) (hβN : 0 ≤ βN)
    (ha : (ε' ^ 2)⁻¹ ≤ a) (hmain : a * z ≤ Cη + 2 * η2 * X)
    (hX : X ≤ C₁ / ε' ^ 2 + βN / ε') : z ≤ ε' ^ 2 * Cη + 2 * C₁ + 2 * βN := by
  have hX0 : 2 * η2 * X ≤ 2 * η2 * (C₁ / ε' ^ 2 + βN / ε') :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have h3 : (ε' ^ 2)⁻¹ * z ≤ Cη + 2 * η2 * (C₁ / ε' ^ 2 + βN / ε') :=
    (mul_le_mul_of_nonneg_right ha hz).trans (hmain.trans (by linarith))
  have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg ε')
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at h4
  have e : ε' ^ 2 * (Cη + 2 * η2 * (C₁ / ε' ^ 2 + βN / ε')) =
      ε' ^ 2 * Cη + η2 * (2 * C₁ + 2 * βN * ε') := by
    field_simp
  rw [e] at h4
  have h5 : η2 * (2 * C₁ + 2 * βN * ε') ≤ 2 * C₁ + 2 * βN := by
    have h6 : 2 * C₁ + 2 * βN * ε' ≤ 2 * C₁ + 2 * βN := by
      linarith [mul_le_mul_of_nonneg_left hε'1 hβN]
    have h7 : 0 ≤ 2 * C₁ + 2 * βN * ε' := by positivity
    linarith [mul_le_mul_of_nonneg_right hη21 h7]
  linarith

/-- Numeric conclusion in the region `v ≥ ε'`. -/
theorem zmax_caseB {z a Cη η2 X vm r C₁ βN : ℝ} (hz : 0 ≤ z) (hη2 : 0 ≤ η2) (hη21 : η2 ≤ 1)
    (hvm : 0 < vm) (hr : 0 < r) (hC₁ : 0 ≤ C₁) (hβN : 0 ≤ βN)
    (ha : 1 / (8 * vm ^ 2) ≤ a) (hmain : a * z ≤ Cη + 2 * η2 * X)
    (hX : X ≤ C₁ / r ^ 2 + βN / r) :
    z ≤ 8 * vm ^ 2 * (Cη + 2 * C₁ / r ^ 2 + 2 * βN / r) := by
  have h6 : 0 ≤ C₁ / r ^ 2 + βN / r := by positivity
  have hX0 : 2 * η2 * X ≤ 2 * (C₁ / r ^ 2 + βN / r) := by
    have := mul_le_mul_of_nonneg_left hX (show 0 ≤ 2 * η2 by positivity)
    nlinarith
  have h3 : 1 / (8 * vm ^ 2) * z ≤ Cη + 2 * (C₁ / r ^ 2 + βN / r) :=
    (mul_le_mul_of_nonneg_right ha hz).trans (hmain.trans (by linarith))
  have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 8 * vm ^ 2 by positivity)
  have e : 8 * vm ^ 2 * (1 / (8 * vm ^ 2) * z) = z := by field_simp
  rw [e] at h4
  refine h4.trans (le_of_eq ?_)
  ring

/-- `C_η = 16|∇η|² + 2|∂ₜη| + 2|Δη|` at `p`. -/
noncomputable def cutoffConstAt (η : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  16 * ∑ i : Idx d, dd (spaceDir i) η p ^ 2 + 2 * |dd timeDir η p| +
    2 * |∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) η) p|

set_option maxHeartbeats 1000000 in
-- a long but elementary case analysis
/-- **The bound on `z` at its maximum** (Steps 2–3, at scale `r`). Let `u` be a
smooth solution of `∂ₜu = Δu - Q² β_ε(u)` on an open set `O`, `ε' = min(ε, r)`, `Φ`, `Ψ` the
Bernstein diffeomorphism for `(ε', M)`, and `z = η² w`, `w = |∇u|²/Φ'(Ψ(u))²`. If `z` has a
local maximum relative to the parabolic past at `p ∈ O`, with `0 ≤ u(p) ≤ M` and
`0 < η(p) ≤ 1`, then
`z(p) ≤ max(1, ε'² C_η + 2C₁ + 2βₘₐₓN, 8 v_max² (C_η + 2C₁/r² + 2βₘₐₓN/r))`, where
`C₁ = Q_max² (Lβ + 2βₘₐₓ)`. -/
theorem zmax_bound {β : ℝ → ℝ} (hβ : IsReactionProfile β) {βmax Lβ : ℝ}
    (hβmax : ∀ s, β s ≤ βmax) (hLβ : ∀ s, |deriv β s| ≤ Lβ) {ε r M Qmax N : ℝ} (hε : 0 < ε)
    (hr : 0 < r) (hr1 : r ≤ 1) (hM : 0 ≤ M) {Q : E d → ℝ} (hQ : ContDiff ℝ ∞ Q)
    (hQmax : ∀ x, |Q x| ≤ Qmax) (hN : ∀ x, ‖∇ (fun y ↦ Q y ^ 2) x‖ ≤ N)
    {O : Set (E d × ℝ)} (hO : IsOpen O) {u : E d × ℝ → ℝ} (hu : ContDiffOn ℝ ∞ u O)
    (heq : ∀ q ∈ O, dₜ u q = lapₓ u q - Q q.1 ^ 2 * betaEps β ε (u q))
    {η : E d × ℝ → ℝ} (hη : ContDiff ℝ ∞ η) {p : E d × ℝ} (hp : p ∈ O)
    (hup : 0 ≤ u p ∧ u p ≤ M) (hηp : 0 < η p) (hη1 : η p ≤ 1)
    (hmax : ∀ᶠ q in 𝓝 p, q.2 ≤ p.2 →
      η q ^ 2 * wGlob (bigPhi (min ε r) M) (bigPsi (min ε r) M) u q ≤
        η p ^ 2 * wGlob (bigPhi (min ε r) M) (bigPsi (min ε r) M) u p) :
    η p ^ 2 * wGlob (bigPhi (min ε r) M) (bigPsi (min ε r) M) u p ≤
      max 1 (max (min ε r ^ 2 * cutoffConstAt η p + 2 * (Qmax ^ 2 * (Lβ + 2 * βmax)) +
        2 * βmax * N) (8 * vmax (min ε r) M ^ 2 * (cutoffConstAt η p +
          2 * (Qmax ^ 2 * (Lβ + 2 * βmax)) / r ^ 2 + 2 * βmax * N / r))) := by
  set ε' := min ε r with hε'
  have hε'0 : 0 < ε' := lt_min hε hr
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'r : ε' ≤ r := min_le_right _ _
  set Φ := bigPhi ε' M with hΦdef
  set Ψ := bigPsi ε' M with hΨdef
  set C₁ := Qmax ^ 2 * (Lβ + 2 * βmax) with hC₁
  set Cη := cutoffConstAt η p with hCη
  have hΦs : ContDiff ℝ ∞ Φ := contDiff_bigPhi
  have hΦ' : ∀ s, 0 < deriv Φ s := deriv_bigPhi_pos
  have hΨs : ContDiff ℝ ∞ Ψ := contDiff_bigPsi
  have hΦΨ : ∀ s, Φ (Ψ s) = s := bigPhi_bigPsi
  have hβmax0 : 0 ≤ βmax := (hβ.nonneg 0).trans (hβmax 0)
  have hLβ0 : 0 ≤ Lβ := (abs_nonneg _).trans (hLβ 0)
  have hQmax0 : 0 ≤ Qmax := (abs_nonneg _).trans (hQmax 0)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have hC₁0 : 0 ≤ C₁ := by positivity
  set W := wGlob Φ Ψ u p with hW
  have hW0 : 0 ≤ W := div_nonneg (sq_nonneg _) (sq_nonneg _)
  -- the easy case `w < 1`
  by_cases hW1 : W < 1
  · have : η p ^ 2 * W ≤ 1 := by
      have : η p ^ 2 ≤ 1 := pow_le_one₀ hηp.le hη1
      linarith [mul_le_mul_of_nonneg_right this hW0]
    exact this.trans (le_max_left _ _)
  push Not at hW1
  refine le_max_of_le_right ?_
  -- `v̂ = Ψ(u(p)) ∈ [0, v_max]`
  set vh := Ψ (u p) with hvh
  have hvmax0 := vmax_pos hε'0 hM
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦdef, bigPhi_eq ⟨by norm_num, by linarith⟩, phi_zero]
  have hΦvmax : 2 * M ≤ Φ (vmax ε' M) := by
    rw [hΦdef, bigPhi_eq ⟨by linarith, by linarith⟩]
    exact two_mul_le_phi_vmax isBernsteinCutoff_psi0 hε'0 hM
  have hvh0 : 0 ≤ vh := by
    have := monotone_bigPsi (ε := ε') (M := M) hup.1
    rwa [← hΦ0, show bigPsi ε' M (Φ 0) = 0 from bigPsi_bigPhi 0] at this
  have hvh1 : vh ≤ vmax ε' M := by
    have := monotone_bigPsi (ε := ε') (M := M) (show u p ≤ Φ (vmax ε' M) by linarith)
    rwa [show bigPsi ε' M (Φ (vmax ε' M)) = vmax ε' M from bigPsi_bigPhi _] at this
  have hvhI : vh ∈ Ioo (-1) (vmax ε' M + 1) := ⟨by linarith, by linarith⟩
  have hvhIcc : vh ∈ Icc 0 (vmax ε' M) := ⟨hvh0, hvh1⟩
  have hupΦ : u p = Φ vh := (hΦΨ (u p)).symm
  -- `Φ = φ` near `v̂`
  have hΦ'vh : deriv Φ vh = phiDeriv psi0 ε' M vh := deriv_bigPhi_eq hvhI
  have hΦ''vh : deriv (deriv Φ) vh = ell psi0 ε' M vh * phiDeriv psi0 ε' M vh :=
    deriv_deriv_bigPhi_eq hvhI
  have hφ'1 : 1 ≤ phiDeriv psi0 ε' M vh := one_le_phiDeriv isBernsteinCutoff_psi0 hε'0 hM hvhIcc
  have hℓ : ellOf Φ vh = ell psi0 ε' M vh := (ellOf_bigPhi_eventuallyEq hvhI).eq_of_nhds
  have hℓ' : deriv (ellOf Φ) vh = ellDeriv psi0 ε' M vh := by
    rw [(ellOf_bigPhi_eventuallyEq hvhI).deriv_eq, deriv_ell]
  have ha : 0 < -ellDeriv psi0 ε' M vh := by
    have := ellDeriv_le_neg_a isBernsteinCutoff_psi0 (ε := ε') (M := M) vh
    linarith [acoef_pos hε'0 hM]
  have hℓ2 : ell psi0 ε' M vh ^ 2 ≤ 2 * -ellDeriv psi0 ε' M vh := by
    have := ell_sq_le isBernsteinCutoff_psi0 hε'0 hM hvhIcc
    rwa [abs_of_neg (by linarith)] at this
  have hℓabs : |ell psi0 ε' M vh| ≤ 2 / ε' := abs_ell_le hε'0 hM hvhIcc
  -- the reaction coefficient `B = β_ε(Φ)/Φ'` and its derivative at `v̂`
  set Bv := bOf β ε Φ vh with hBv
  have hBv_eq : Bv = betaEps β ε (u p) / phiDeriv psi0 ε' M vh := by
    rw [hBv, bOf, ← hupΦ, hΦ'vh]
  have hbeta_bd : ∀ z, 0 ≤ betaEps β ε z ∧ betaEps β ε z ≤ βmax / ε := fun z ↦
    ⟨hβ.betaEps_nonneg ε z hε.le, div_le_div_of_nonneg_right (hβmax _) hε.le⟩
  have hdbeta_bd : ∀ z, |deriv β (z / ε) / ε ^ 2| ≤ Lβ / ε ^ 2 := fun z ↦ by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2)]
    exact div_le_div_of_nonneg_right (hLβ _) (by positivity)
  have hBd : HasDerivAt (bOf β ε Φ) ((deriv β (u p / ε) / ε ^ 2 * deriv Φ vh * deriv Φ vh -
      betaEps β ε (u p) * deriv (deriv Φ) vh) / deriv Φ vh ^ 2) vh := by
    have h1 : HasDerivAt (fun s ↦ betaEps β ε (Φ s))
        (deriv β (Φ vh / ε) / ε ^ 2 * deriv Φ vh) vh :=
      (hβ.hasDerivAt_betaEps ε (Φ vh)).comp vh
        (hΦs.differentiable (by simp) vh).hasDerivAt
    have h2 : HasDerivAt (deriv Φ) (deriv (deriv Φ) vh) vh :=
      ((contDiff_deriv' hΦs).differentiable (by simp) vh).hasDerivAt
    have h3 := h1.div h2 (hΦ' vh).ne'
    rw [← hupΦ] at h3
    exact h3
  set dBv := deriv (bOf β ε Φ) vh with hdBv
  have hdBv_eq : dBv = deriv β (u p / ε) / ε ^ 2 -
      betaEps β ε (u p) * ell psi0 ε' M vh / phiDeriv psi0 ε' M vh := by
    rw [hdBv, hBd.deriv, hΦ''vh, hΦ'vh]
    have := phiDeriv_pos (ψ := psi0) (ε := ε') (M := M) vh
    field_simp
  -- generic bounds on `B`, `B'`
  have hBabs : |Bv| ≤ βmax / ε := by
    rw [hBv_eq, abs_div, abs_of_pos (phiDeriv_pos vh), abs_of_nonneg (hbeta_bd _).1]
    exact (div_le_self (hbeta_bd _).1 hφ'1).trans (hbeta_bd _).2
  have hdBabs : |dBv| ≤ Lβ / ε ^ 2 + βmax / ε * (2 / ε') := by
    rw [hdBv_eq]
    refine (abs_sub _ _).trans (add_le_add (hdbeta_bd _) ?_)
    rw [abs_div, abs_mul, abs_of_pos (phiDeriv_pos vh), abs_of_nonneg (hbeta_bd _).1]
    calc betaEps β ε (u p) * |ell psi0 ε' M vh| / phiDeriv psi0 ε' M vh
        ≤ betaEps β ε (u p) * |ell psi0 ε' M vh| := div_le_self (by
          have := (hbeta_bd (u p)).1; positivity) hφ'1
      _ ≤ βmax / ε * (2 / ε') := mul_le_mul (hbeta_bd _).2 hℓabs (abs_nonneg _)
          (by positivity)
  -- apply the maximum-point inequality
  set v : E d × ℝ → ℝ := fun q ↦ Ψ (u q) with hv
  have hvs : ContDiffOn ℝ ∞ v O := contDiffOn_v hu hΨs
  have hveq := veq hO hu hΦs hΦ' hΨs hΦΨ heq
  have hWeq : ∀ q ∈ O, wOf v q = wGlob Φ Ψ u q := fun q hq ↦
    wOf_eq_wGlob hΦs hΦ' hΨs hΦΨ (hu.differentiableAt' hO hq)
  have hmax' : ∀ᶠ q in 𝓝 p, q.2 ≤ p.2 → η q ^ 2 * wOf v q ≤ η p ^ 2 * wOf v p := by
    filter_upwards [hmax, hO.mem_nhds hp] with q hq hqO hle
    rw [hWeq q hqO, hWeq p hp]; exact hq hle
  have hkx : ∑ i : Idx d, (Bv * dd (spaceDir i) (fun q ↦ Q q.1 ^ 2) p) ^ 2 ≤ (|Bv| * N) ^ 2 := by
    have hQd : DifferentiableAt ℝ (fun q : E d × ℝ ↦ Q q.1 ^ 2) p :=
      ((hQ.comp contDiff_fst).pow 2).differentiable (by simp) p
    have e : ∑ i : Idx d, (Bv * dd (spaceDir i) (fun q ↦ Q q.1 ^ 2) p) ^ 2 =
        Bv ^ 2 * ‖∇ (fun y ↦ Q y ^ 2) p.1‖ ^ 2 := by
      rw [show ‖∇ (fun y ↦ Q y ^ 2) p.1‖ = ‖gradₓ (fun q : E d × ℝ ↦ Q q.1 ^ 2) p‖ from rfl,
        norm_gradₓ_sq hQd, mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    rw [e, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hN _) 2) (sq_nonneg _)
  have hmain := max_point_bound hO hvs (contDiff_ellOf hΦs hΦ') (contDiff_bOf hβ.contDiff hΦs hΦ')
    hQ hveq hη hp hηp hη1 hmax' (by rw [hWeq p hp]; exact hW1)
    (by rw [hℓ']; exact ha) (by rw [hℓ, hℓ']; exact hℓ2) (by positivity) hkx
  rw [hWeq p hp, hℓ'] at hmain
  change -ellDeriv psi0 ε' M vh * (η p ^ 2 * W) ≤
    Cη + 2 * η p ^ 2 * (|Q p.1 ^ 2 * dBv| + |Bv| * N) at hmain
  have hη2 : η p ^ 2 ≤ 1 := pow_le_one₀ hηp.le hη1
  have hQ2 : Q p.1 ^ 2 ≤ Qmax ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hQmax _) 2
  have hz0 : 0 ≤ η p ^ 2 * W := by positivity
  have hCη0 : 0 ≤ Cη := by
    rw [hCη, cutoffConstAt]
    have := sum_nonneg fun i (_ : i ∈ (univ : Finset (Idx d))) ↦ sq_nonneg (dd (spaceDir i) η p)
    positivity
  have hQdB : |Q p.1 ^ 2 * dBv| ≤ Qmax ^ 2 * (Lβ / ε ^ 2 + βmax / ε * (2 / ε')) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul hQ2 hdBabs (abs_nonneg _) (sq_nonneg _)
  have hBN : |Bv| * N ≤ βmax / ε * N := mul_le_mul_of_nonneg_right hBabs hN0
  have hε'1 : ε' ≤ 1 := hε'r.trans hr1
  have hβN : 0 ≤ βmax * N := mul_nonneg hβmax0 hN0
  rcases lt_or_ge vh ε' with hvε | hvε
  · -- the transition region `v < ε'`
    refine le_max_of_le_left ?_
    have ha' : (ε' ^ 2)⁻¹ ≤ -ellDeriv psi0 ε' M vh := by
      have := ellDeriv_le_of_le isBernsteinCutoff_psi0 hε'0 hM hvε.le; linarith
    have h1 : Qmax ^ 2 * (Lβ / ε ^ 2 + βmax / ε * (2 / ε')) ≤ C₁ / ε' ^ 2 := by
      rw [hC₁, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have e1 : Lβ / ε ^ 2 ≤ Lβ / ε' ^ 2 :=
        div_le_div_of_nonneg_left hLβ0 (by positivity) (pow_le_pow_left₀ hε'0.le hε'ε 2)
      have e2 : βmax / ε * (2 / ε') ≤ 2 * βmax / ε' ^ 2 := by
        rw [div_mul_div_comm, mul_comm βmax 2, sq]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hε'ε hε'0.le)
      rw [add_div]; linarith
    have h2 : βmax / ε * N ≤ βmax * N / ε' := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left hβN hε'0 hε'ε
    have := zmax_caseA (by positivity) (sq_nonneg _) hη2 hε'0 hε'1 hC₁0 hβN ha' hmain
      (by linarith)
    linarith
  · -- the region `v ≥ ε'`
    refine le_max_of_le_right ?_
    have ha' : 1 / (8 * vmax ε' M ^ 2) ≤ -ellDeriv psi0 ε' M vh := by
      have := ellDeriv_le_neg_a isBernsteinCutoff_psi0 (ε := ε') (M := M) vh
      change acoef ε' M ≤ _; linarith
    have hreac : |Q p.1 ^ 2 * dBv| + |Bv| * N ≤ C₁ / r ^ 2 + βmax * N / r := by
      rcases le_or_gt ε r with hεr | hεr
      · -- `ε' = ε`: the reaction vanishes on `{v ≥ ε}`
        have he : ε' = ε := min_eq_left hεr
        have hup1 : 1 ≤ u p / ε := by
          rw [le_div_iff₀ hε, one_mul, hupΦ, ← he]
          have h1 : Φ ε' = phi psi0 ε' M ε' := by
            rw [hΦdef, bigPhi_eq ⟨by linarith, by linarith [eps_le_vmax (ε := ε') hM]⟩]
          have h2 := le_phi_eps isBernsteinCutoff_psi0 hε'0 hM (ψ := psi0)
          have h3 : Φ ε' ≤ Φ vh := strictMono_bigPhi.monotone hvε
          linarith
        have hb0 : betaEps β ε (u p) = 0 := by
          rw [betaEps, hβ.eq_zero_of_one_le hup1, zero_div]
        have hdb0 : deriv β (u p / ε) = 0 := hβ.deriv_eq_zero_of_one_le hup1
        rw [hdBv_eq, hBv_eq, hb0, hdb0]
        simp only [zero_div, zero_mul, sub_zero, mul_zero, abs_zero, zero_add]
        positivity
      · have he : ε' = r := min_eq_right hεr.le
        have h1 : Qmax ^ 2 * (Lβ / ε ^ 2 + βmax / ε * (2 / ε')) ≤ C₁ / r ^ 2 := by
          rw [hC₁, mul_div_assoc, he]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have e1 : Lβ / ε ^ 2 ≤ Lβ / r ^ 2 :=
            div_le_div_of_nonneg_left hLβ0 (by positivity) (pow_le_pow_left₀ hr.le hεr.le 2)
          have e2 : βmax / ε * (2 / r) ≤ 2 * βmax / r ^ 2 := by
            rw [div_mul_div_comm, mul_comm βmax 2, sq]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_right hεr.le hr.le)
          rw [add_div]; linarith
        have h2 : βmax / ε * N ≤ βmax * N / r := by
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_left hβN hr hεr.le
        linarith
    have := zmax_caseB (by positivity) (sq_nonneg _) hη2 hvmax0 hr hC₁0 hβN ha' hmain hreac
    refine this.trans (le_of_eq ?_)
    ring

end BernsteinMax

end PerronVariational

end
