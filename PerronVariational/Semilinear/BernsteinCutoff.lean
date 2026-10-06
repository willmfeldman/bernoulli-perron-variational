/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.BernsteinBound
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# The cutoff of Step 3

Step 3 of the joint proof of Propositions A.5 and A.6 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.4):
a cutoff `η`, `0 ≤ η ≤ 1`, with
`|∇η| + |∂ₜη| + |D²η| ≤ C_d` (at unit scale).

We use the single smooth function `η = χ(σ)`, `σ(x, t) = |x - x₀|²/r² + κ (t₀ - t)/r²`, with
`χ = 1` on `(-∞, 2]` and `χ = 0` on `[3, ∞)`; `κ = 1` for Proposition A.5 (space-time cutoff)
and `κ = 0` for Proposition A.6 (space cutoff only). Then `η = 1` on `Q_r(x₀, t₀)`
(resp. `B_r(x₀) × ℝ`), `η = 0` where `σ ≥ 3`, and `C_η ≤ C_χ / r²` wherever `|x - x₀|² ≤ 3r²`.
-/

open Set Filter Topology Finset Real
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace BernsteinMax

/-- The profile `χ(s) = smoothTransition(3 - s)`: `1` for `s ≤ 2`, `0` for `s ≥ 3`. -/
noncomputable def chi (s : ℝ) : ℝ := smoothTransition (3 - s)

theorem contDiff_chi : ContDiff ℝ ∞ chi :=
  smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem chi_nonneg (s : ℝ) : 0 ≤ chi s := smoothTransition.nonneg _

theorem chi_le_one (s : ℝ) : chi s ≤ 1 := smoothTransition.le_one _

theorem chi_eq_one {s : ℝ} (hs : s ≤ 2) : chi s = 1 := smoothTransition.one_of_one_le (by linarith)

theorem chi_eq_zero {s : ℝ} (hs : 3 ≤ s) : chi s = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

theorem chi_pos {s : ℝ} (hs : s < 3) : 0 < chi s := smoothTransition.pos_of_pos (by linarith)

/-- A continuous function vanishing outside `[a, b]` is bounded. -/
theorem exists_abs_le_of_eq_zero_outside {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (h : ∀ s, s ∉ Set.Icc a b → f s = 0) : ∃ c : ℝ, 0 ≤ c ∧ ∀ s, |f s| ≤ c := by
  obtain ⟨c, hc⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hf.continuousOn (s := Set.Icc a b))
  refine ⟨max c 0, le_max_right _ _, fun s ↦ ?_⟩
  by_cases hs : s ∈ Set.Icc a b
  · exact (by simpa using hc s hs : |f s| ≤ c).trans (le_max_left _ _)
  · rw [h s hs, abs_zero]; exact le_max_right _ _

theorem chi_eventuallyEq_const {s : ℝ} (hs : s ∉ Set.Icc 2 3) :
    ∃ c : ℝ, chi =ᶠ[𝓝 s] fun _ ↦ c := by
  rcases not_and_or.1 hs with h | h
  · refine ⟨1, ?_⟩
    filter_upwards [Iio_mem_nhds (not_le.1 h)] with t ht using chi_eq_one (le_of_lt ht)
  · refine ⟨0, ?_⟩
    filter_upwards [Ioi_mem_nhds (not_le.1 h)] with t ht using chi_eq_zero (le_of_lt ht)

theorem deriv_chi_eq_zero {s : ℝ} (hs : s ∉ Set.Icc 2 3) : deriv chi s = 0 := by
  obtain ⟨c, hc⟩ := chi_eventuallyEq_const hs
  rw [hc.deriv_eq]; simp

theorem deriv_deriv_chi_eq_zero {s : ℝ} (hs : s ∉ Set.Icc 2 3) : deriv (deriv chi) s = 0 := by
  have hopen : IsOpen (Set.Icc (2 : ℝ) 3)ᶜ := isClosed_Icc.isOpen_compl
  have hev : deriv chi =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hs] with t ht using deriv_chi_eq_zero ht
  rw [hev.deriv_eq]; simp

/-- Bounds on `χ'` and `χ''`. -/
theorem exists_chi_bounds : ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
    ∀ s, |deriv chi s| ≤ c₁ ∧ |deriv (deriv chi) s| ≤ c₂ := by
  obtain ⟨c₁, hc₁0, hc₁⟩ := exists_abs_le_of_eq_zero_outside
    (contDiff_chi.continuous_deriv (by simp)) fun s hs ↦ deriv_chi_eq_zero hs
  obtain ⟨c₂, hc₂0, hc₂⟩ := exists_abs_le_of_eq_zero_outside
    ((contDiff_deriv' contDiff_chi).continuous_deriv (by simp))
    fun s hs ↦ deriv_deriv_chi_eq_zero hs
  exact ⟨c₁, c₂, hc₁0, hc₂0, fun s ↦ ⟨hc₁ s, hc₂ s⟩⟩

variable {d : ℕ}

/-- `σ(x, t) = |x - x₀|²/r² + κ (t₀ - t)/r²`. -/
noncomputable def sigmaFun (x₀ : E d) (t₀ r κ : ℝ) (q : E d × ℝ) : ℝ :=
  ‖q.1 - x₀‖ ^ 2 / r ^ 2 + κ * (t₀ - q.2) / r ^ 2

/-- The cutoff `η = χ(σ)`. -/
noncomputable def etaFun (x₀ : E d) (t₀ r κ : ℝ) (q : E d × ℝ) : ℝ := chi (sigmaFun x₀ t₀ r κ q)

variable (x₀ : E d) (t₀ r κ : ℝ)

theorem dd_sigmaFun (a q : E d × ℝ) :
    dd a (sigmaFun x₀ t₀ r κ) q = 2 * ⟪q.1 - x₀, a.1⟫ / r ^ 2 - κ * a.2 / r ^ 2 := by
  have h1 : HasFDerivAt (fun q : E d × ℝ ↦ q.1 - x₀) (ContinuousLinearMap.fst ℝ (E d) ℝ) q :=
    (hasFDerivAt_fst).sub_const x₀
  have hA := HasFDerivAt.const_mul (HasFDerivAt.norm_sq h1) (1 / r ^ 2)
  have hB := ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).const_sub t₀).const_mul (κ / r ^ 2)
  have h := hA.fun_add hB
  have e : sigmaFun x₀ t₀ r κ = fun q : E d × ℝ ↦
      1 / r ^ 2 * ‖q.1 - x₀‖ ^ 2 + κ / r ^ 2 * (t₀ - q.2) := by
    funext q; simp only [sigmaFun]; ring
  simp only [PerronVariational.dd]
  rw [e, h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', neg_apply,
    ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem contDiff_sigmaFun : ContDiff ℝ ∞ (sigmaFun x₀ t₀ r κ) := by
  unfold sigmaFun
  exact (((contDiff_fst.sub contDiff_const).norm_sq ℝ).div_const _).add
    ((contDiff_const.mul (contDiff_const.sub contDiff_snd)).div_const _)

theorem contDiff_etaFun : ContDiff ℝ ∞ (etaFun x₀ t₀ r κ) :=
  contDiff_chi.comp (contDiff_sigmaFun x₀ t₀ r κ)

theorem dd_dd_sigmaFun (a b q : E d × ℝ) :
    dd b (dd a (sigmaFun x₀ t₀ r κ)) q = 2 * ⟪a.1, b.1⟫ / r ^ 2 := by
  have e : dd a (sigmaFun x₀ t₀ r κ) = fun q : E d × ℝ ↦
      2 / r ^ 2 * innerSL ℝ a.1 (q.1 - x₀) - κ * a.2 / r ^ 2 := by
    funext q; rw [dd_sigmaFun, innerSL_apply_apply, real_inner_comm]; ring
  have h1 : HasFDerivAt (fun q : E d × ℝ ↦ q.1 - x₀) (ContinuousLinearMap.fst ℝ (E d) ℝ) q :=
    (hasFDerivAt_fst).sub_const x₀
  have h2 := (((innerSL ℝ a.1).hasFDerivAt.comp q h1).const_mul (2 / r ^ 2)).sub_const
    (κ * a.2 / r ^ 2)
  simp only [PerronVariational.dd]
  rw [e]
  rw [show (fun q : E d × ℝ ↦ 2 / r ^ 2 * innerSL ℝ a.1 (q.1 - x₀) - κ * a.2 / r ^ 2) =
    fun q ↦ 2 / r ^ 2 * ((innerSL ℝ a.1) ∘ fun q : E d × ℝ ↦ q.1 - x₀) q - κ * a.2 / r ^ 2 from rfl,
    h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', innerSL_apply_apply, smul_eq_mul]
  ring

/-- The cutoff constant `C_χ = 192 c₁² + 2c₁ + 4 d c₁ + 24 c₂`. -/
noncomputable def cutoffChiConst (d : ℕ) (c₁ c₂ : ℝ) : ℝ :=
  192 * c₁ ^ 2 + 2 * c₁ + 4 * d * c₁ + 24 * c₂

theorem sum_inner_basis_sq (y : E d) :
    ∑ i : Idx d, ⟪y, (stdOrthonormalBasis ℝ (E d) i : E d)⟫ ^ 2 = ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (stdOrthonormalBasis ℝ (E d)).sum_inner_mul_inner y y]
  exact sum_congr rfl fun i _ ↦ by rw [sq, real_inner_comm (stdOrthonormalBasis ℝ (E d) i) y]

theorem card_idx : (Fintype.card (Idx d) : ℝ) = d := by
  simp [Idx]

/-- **The cutoff bound**: `C_η ≤ C_χ/r²` where `|x - x₀|² ≤ 3r²`. -/
theorem cutoffConstAt_etaFun_le {c₁ c₂ : ℝ} (hc : ∀ s, |deriv chi s| ≤ c₁ ∧
    |deriv (deriv chi) s| ≤ c₂) (hr : 0 < r) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {q : E d × ℝ}
    (hq : ‖q.1 - x₀‖ ^ 2 ≤ 3 * r ^ 2) :
    cutoffConstAt (etaFun x₀ t₀ r κ) q ≤ cutoffChiConst d c₁ c₂ / r ^ 2 := by
  have hσs := contDiff_sigmaFun x₀ t₀ r κ
  have hχd : ∀ s, DifferentiableAt ℝ chi s := fun s ↦ contDiff_chi.differentiable (by simp) s
  have hχ'd : ∀ s, DifferentiableAt ℝ (deriv chi) s := fun s ↦
    (contDiff_deriv' contDiff_chi).differentiable (by simp) s
  have hσd : ∀ q, DifferentiableAt ℝ (sigmaFun x₀ t₀ r κ) q := fun q ↦
    hσs.differentiable (by simp) q
  set σ := sigmaFun x₀ t₀ r κ q with hσ
  set y := q.1 - x₀ with hy
  -- first derivatives
  have hdη : ∀ a q', dd a (etaFun x₀ t₀ r κ) q' =
      deriv chi (sigmaFun x₀ t₀ r κ q') * dd a (sigmaFun x₀ t₀ r κ) q' := fun a q' ↦
    dd_comp (hχd _) (hσd q') a
  have hddσ : ∀ a, ContDiff ℝ ∞ (dd a (sigmaFun x₀ t₀ r κ)) := fun a ↦
    contDiffOn_univ.1 ((hσs.contDiffOn (s := univ)).dd isOpen_univ a)
  -- second derivatives
  have hddη : ∀ a, dd a (dd a (etaFun x₀ t₀ r κ)) q =
      deriv chi σ * dd a (dd a (sigmaFun x₀ t₀ r κ)) q +
        dd a (sigmaFun x₀ t₀ r κ) q * (deriv (deriv chi) σ * dd a (sigmaFun x₀ t₀ r κ) q) := by
    intro a
    rw [show dd a (etaFun x₀ t₀ r κ) = fun q' ↦ deriv chi (sigmaFun x₀ t₀ r κ q') *
      dd a (sigmaFun x₀ t₀ r κ) q' from funext (hdη a)]
    rw [dd_mul (f := fun q' ↦ deriv chi (sigmaFun x₀ t₀ r κ q'))
      ((hχ'd _).comp q (hσd q)) ((hddσ a).differentiable (by simp) q),
      dd_comp (hχ'd _) (hσd q)]
  have hsp : ∀ i : Idx d, dd (spaceDir i) (sigmaFun x₀ t₀ r κ) q =
      2 * ⟪y, (stdOrthonormalBasis ℝ (E d) i : E d)⟫ / r ^ 2 := fun i ↦ by
    rw [dd_sigmaFun]; simp [spaceDir, hy]
  have hspsp : ∀ i : Idx d, dd (spaceDir i) (dd (spaceDir i) (sigmaFun x₀ t₀ r κ)) q =
      2 / r ^ 2 := fun i ↦ by
    rw [dd_dd_sigmaFun]; simp [spaceDir]
  have htm : dd timeDir (sigmaFun x₀ t₀ r κ) q = -κ / r ^ 2 := by
    rw [dd_sigmaFun]; simp [timeDir]; ring
  obtain ⟨h1, h2⟩ := hc σ
  have hc₁ : 0 ≤ c₁ := (abs_nonneg _).trans h1
  have hc₂ : 0 ≤ c₂ := (abs_nonneg _).trans h2
  have hr2 : 0 < r ^ 2 := by positivity
  have hS : ∑ i : Idx d, (2 * ⟪y, (stdOrthonormalBasis ℝ (E d) i : E d)⟫ / r ^ 2) ^ 2 =
      4 * ‖y‖ ^ 2 / r ^ 4 := by
    rw [← sum_inner_basis_sq y, mul_sum, sum_div]
    exact sum_congr rfl fun i _ ↦ by ring
  -- the three terms
  have t1 : ∑ i : Idx d, dd (spaceDir i) (etaFun x₀ t₀ r κ) q ^ 2 ≤ 12 * c₁ ^ 2 / r ^ 2 := by
    simp only [hdη, hsp, mul_pow]
    rw [← mul_sum, hS]
    have : deriv chi σ ^ 2 ≤ c₁ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : 4 * ‖y‖ ^ 2 / r ^ 4 ≤ 12 / r ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) hr2]; nlinarith
    calc deriv chi σ ^ 2 * (4 * ‖y‖ ^ 2 / r ^ 4) ≤ c₁ ^ 2 * (12 / r ^ 2) :=
          mul_le_mul this h3 (by positivity) (sq_nonneg _)
      _ = 12 * c₁ ^ 2 / r ^ 2 := by ring
  have t2 : |dd timeDir (etaFun x₀ t₀ r κ) q| ≤ c₁ / r ^ 2 := by
    rw [hdη, htm, abs_mul, abs_div, abs_neg, abs_of_nonneg hκ0, abs_of_pos hr2]
    calc |deriv chi σ| * (κ / r ^ 2) ≤ c₁ * (1 / r ^ 2) :=
          mul_le_mul h1 (div_le_div_of_nonneg_right hκ1 hr2.le) (by positivity) hc₁
      _ = c₁ / r ^ 2 := by ring
  have t3 : |∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) (etaFun x₀ t₀ r κ)) q| ≤
      (2 * d * c₁ + 12 * c₂) / r ^ 2 := by
    simp only [hddη, hspsp, hsp]
    have e : ∑ i : Idx d, (deriv chi σ * (2 / r ^ 2) +
        2 * ⟪y, (stdOrthonormalBasis ℝ (E d) i : E d)⟫ / r ^ 2 *
          (deriv (deriv chi) σ * (2 * ⟪y, (stdOrthonormalBasis ℝ (E d) i : E d)⟫ / r ^ 2))) =
        deriv chi σ * (2 * d / r ^ 2) + deriv (deriv chi) σ * (4 * ‖y‖ ^ 2 / r ^ 4) := by
      rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, card_idx, ← hS, mul_sum]
      congr 1
      · ring
      · exact sum_congr rfl fun i _ ↦ by ring
    rw [e]
    have h3 : 4 * ‖y‖ ^ 2 / r ^ 4 ≤ 12 / r ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) hr2]; nlinarith
    have h4 : 0 ≤ 4 * ‖y‖ ^ 2 / r ^ 4 := by positivity
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * d / r ^ 2),
      abs_of_nonneg h4]
    have h5 : |deriv chi σ| * (2 * d / r ^ 2) ≤ c₁ * (2 * d / r ^ 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h6 : |deriv (deriv chi) σ| * (4 * ‖y‖ ^ 2 / r ^ 4) ≤ c₂ * (12 / r ^ 2) :=
      mul_le_mul h2 h3 h4 hc₂
    have e2 : (2 * d * c₁ + 12 * c₂) / r ^ 2 = c₁ * (2 * d / r ^ 2) + c₂ * (12 / r ^ 2) := by ring
    rw [e2]; linarith
  rw [cutoffConstAt, cutoffChiConst]
  have e3 : (192 * c₁ ^ 2 + 2 * c₁ + 4 * d * c₁ + 24 * c₂) / r ^ 2 =
      16 * (12 * c₁ ^ 2 / r ^ 2) + 2 * (c₁ / r ^ 2) + 2 * ((2 * d * c₁ + 12 * c₂) / r ^ 2) := by
    ring
  rw [e3]
  linarith

/-! ### Facts on `Φ` used in the assembly -/

open Bernstein in
theorem bigPsi_mem_Icc {ε M s : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hs : 0 ≤ s) (hsM : s ≤ M) :
    bigPsi ε M s ∈ Icc 0 (vmax ε M) := by
  have hvmax0 := vmax_pos hε hM
  have hΦ0 : bigPhi ε M 0 = 0 := by
    rw [bigPhi_eq ⟨by norm_num, by linarith⟩, phi_zero]
  have hΦvmax : 2 * M ≤ bigPhi ε M (vmax ε M) := by
    rw [bigPhi_eq ⟨by linarith, by linarith⟩]
    exact two_mul_le_phi_vmax isBernsteinCutoff_psi0 hε hM
  constructor
  · have := monotone_bigPsi (ε := ε) (M := M) hs
    rwa [← hΦ0, bigPsi_bigPhi] at this
  · have := monotone_bigPsi (ε := ε) (M := M) (show s ≤ bigPhi ε M (vmax ε M) by linarith)
    rwa [bigPsi_bigPhi] at this

open Bernstein in
theorem deriv_bigPhi_mem {ε M v : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hv : v ∈ Icc 0 (vmax ε M)) :
    1 ≤ deriv (bigPhi ε M) v ∧ deriv (bigPhi ε M) v ≤ Real.exp 1 := by
  have hvI : v ∈ Ioo (-1) (vmax ε M + 1) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  rw [deriv_bigPhi_eq hvI]
  exact ⟨one_le_phiDeriv isBernsteinCutoff_psi0 hε hM hv,
    phiDeriv_le_exp_one isBernsteinCutoff_psi0 hε hM v⟩

open Bernstein in
/-- `|∇u|² = Φ'(Ψ(u))² w ≤ e² w` where `0 ≤ u ≤ M`. -/
theorem norm_gradₓ_sq_le_wGlob {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) {u : E d × ℝ → ℝ}
    {q : E d × ℝ} (hu0 : 0 ≤ u q) (huM : u q ≤ M) :
    ‖gradₓ u q‖ ^ 2 ≤ Real.exp 1 ^ 2 * wGlob (bigPhi ε M) (bigPsi ε M) u q := by
  obtain ⟨h1, h2⟩ := deriv_bigPhi_mem hε hM (bigPsi_mem_Icc hε hM hu0 huM)
  set D := deriv (bigPhi ε M) (bigPsi ε M (u q))
  have hD0 : 0 < D := by linarith
  have e : ‖gradₓ u q‖ ^ 2 = D ^ 2 * wGlob (bigPhi ε M) (bigPsi ε M) u q := by
    change _ = D ^ 2 * (‖gradₓ u q‖ ^ 2 / D ^ 2); field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD0.le h2 2)
    (div_nonneg (sq_nonneg _) (sq_nonneg _))

open Bernstein in
theorem wGlob_le_of_ge_one {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) {u : E d × ℝ → ℝ}
    {q : E d × ℝ} (hu0 : 0 ≤ u q) (huM : u q ≤ M) :
    wGlob (bigPhi ε M) (bigPsi ε M) u q ≤ ‖gradₓ u q‖ ^ 2 := by
  obtain ⟨h1, -⟩ := deriv_bigPhi_mem hε hM (bigPsi_mem_Icc hε hM hu0 huM)
  simp only [wGlob]
  exact div_le_self (sq_nonneg _) (one_le_pow₀ h1)

/-- The final numeric bound: the right-hand side of `zmax_bound` with `C_η ≤ C_χ/r²` is at
most `K₀ (1 + 4M/r)²`, `K₀ = 8(C_χ + 2C₁ + 2βₘₐₓN) + 1`. -/
theorem zstar_le {ε r M Cη Cχ C₁ βN : ℝ} (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1) (hM : 0 ≤ M)
    (hCχ : 0 ≤ Cχ) (hC₁ : 0 ≤ C₁) (hβN : 0 ≤ βN) (hCη : Cη ≤ Cχ / r ^ 2) :
    max 1 (max (min ε r ^ 2 * Cη + 2 * C₁ + 2 * βN)
      (8 * Bernstein.vmax (min ε r) M ^ 2 * (Cη + 2 * C₁ / r ^ 2 + 2 * βN / r))) ≤
      (8 * (Cχ + 2 * C₁ + 2 * βN) + 1) * (1 + 4 * M / r) ^ 2 := by
  set ε' := min ε r
  have hε'0 : 0 < ε' := lt_min hε hr
  have hε'r : ε' ≤ r := min_le_right _ _
  set K₀ := 8 * (Cχ + 2 * C₁ + 2 * βN) + 1
  have hS : 0 ≤ Cχ + 2 * C₁ + 2 * βN := by positivity
  have hsq : 1 ≤ (1 + 4 * M / r) ^ 2 := by
    have : 0 ≤ 4 * M / r := by positivity
    exact one_le_pow₀ (by linarith)
  have hr2 : 0 < r ^ 2 := by positivity
  refine max_le (by nlinarith) (max_le ?_ ?_)
  · have h1 : ε' ^ 2 * Cη ≤ Cχ := by
      calc ε' ^ 2 * Cη ≤ r ^ 2 * (Cχ / r ^ 2) := by
            rcases le_or_gt 0 Cη with h | h
            · exact mul_le_mul (pow_le_pow_left₀ hε'0.le hε'r 2) hCη h hr2.le
            · have : ε' ^ 2 * Cη ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h.le
              have : 0 ≤ r ^ 2 * (Cχ / r ^ 2) := by positivity
              linarith
        _ = Cχ := by field_simp
    have : ε' ^ 2 * Cη + 2 * C₁ + 2 * βN ≤ K₀ := by linarith
    nlinarith
  · have hvm : Bernstein.vmax ε' M ≤ r + 4 * M := by
      unfold Bernstein.vmax; linarith
    have hvm0 : 0 < Bernstein.vmax ε' M := Bernstein.vmax_pos hε'0 hM
    have h1 : Cη + 2 * C₁ / r ^ 2 + 2 * βN / r ≤ (Cχ + 2 * C₁ + 2 * βN) / r ^ 2 := by
      have h2 : 2 * βN / r ≤ 2 * βN / r ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) hr2
        nlinarith
      rw [add_div, add_div]
      linarith
    have h3 : 8 * Bernstein.vmax ε' M ^ 2 * (Cη + 2 * C₁ / r ^ 2 + 2 * βN / r) ≤
        8 * (r + 4 * M) ^ 2 * ((Cχ + 2 * C₁ + 2 * βN) / r ^ 2) := by
      rcases le_or_gt 0 (Cη + 2 * C₁ / r ^ 2 + 2 * βN / r) with h | h
      · exact mul_le_mul (by nlinarith) h1 h (by positivity)
      · have : 8 * Bernstein.vmax ε' M ^ 2 * (Cη + 2 * C₁ / r ^ 2 + 2 * βN / r) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le
        have : 0 ≤ 8 * (r + 4 * M) ^ 2 * ((Cχ + 2 * C₁ + 2 * βN) / r ^ 2) := by positivity
        linarith
    have e : 8 * (r + 4 * M) ^ 2 * ((Cχ + 2 * C₁ + 2 * βN) / r ^ 2) =
        8 * (Cχ + 2 * C₁ + 2 * βN) * (1 + 4 * M / r) ^ 2 := by
      field_simp
    rw [e] at h3
    linarith

end BernsteinMax

end PerronVariational

end
