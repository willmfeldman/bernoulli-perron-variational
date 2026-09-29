/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Semilinear
public import PerronVariational.Semilinear.AutonomousODE

/-!
# One-dimensional sub- and supersolution profiles (Appendix A.3.1)

Appendix A.3.1 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

* Basic properties of reaction profiles `β` ((3.5)) and of `𝓑 = 𝓑₁`, `𝓑_ε`.
* **Lemma A.2**: the sub-profile `Φ = Φ_{1,θ}` (`profileSub`),
  `Φ'' = θ β(Φ)`, `√(1-θ) ≤ Φ' ≤ 1`, `Φ(s) = s` for `s ≥ 1`, the zero `s₀ ∈ [-c_θ, 0]`, and
  `sup |Φ₊ - s₊| ≤ 1`. Constructed exactly as in the paper: `Φ(s) = G⁻¹(s - 1)` with
  `G(z) = ∫₁ᶻ dw / √((1-θ) + 2θ𝓑(w))` (via `odeSol`). `Φ ∈ C^∞`.
* **Lemma A.3**: the super-profile `Ψ = Ψ_{1,θ̂}` (`profileSuper`) and
  the level `κ` (`superKappa`).
* **(A.5)**: the rescalings `Φ_{ε,θ}`, `Ψ_{ε,θ̂}`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

@[expose] public section

namespace PerronVariational

/-! ### Reaction profiles and `𝓑` -/

section Monotone

/-- A function with nonnegative derivative everywhere is monotone. -/
theorem monotone_of_hasDerivAt_nonneg' {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h : ∀ x, 0 ≤ f' x) : Monotone f :=
  monotone_of_deriv_nonneg (fun x ↦ (hf x).differentiableAt) fun x ↦ (hf x).deriv ▸ h x

/-- A function with nonnegative derivative on `D` (convex) is monotone on `D`. -/
theorem monotoneOn_of_hasDerivAt_nonneg' {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (h : ∀ x ∈ interior D, 0 ≤ f' x) : MonotoneOn f D :=
  monotoneOn_of_deriv_nonneg hD (fun x _ ↦ (hf x).continuousAt.continuousWithinAt)
    (fun x _ ↦ (hf x).differentiableAt.differentiableWithinAt) fun x hx ↦ (hf x).deriv ▸ h x hx

end Monotone

namespace IsReactionProfile

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β)
include hβ

theorem contDiff : ContDiff ℝ ∞ β := hβ.1

theorem continuous : Continuous β := hβ.1.continuous

theorem eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : β s = 0 :=
  hβ.2.1 s fun h ↦ (not_lt.2 hs) h.1

theorem eq_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) : β s = 0 :=
  hβ.2.1 s fun h ↦ (not_lt.2 hs) h.2

theorem pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < β s := hβ.2.2.1 s ⟨h0, h1⟩

theorem nonneg (s : ℝ) : 0 ≤ β s := by
  by_cases h : s ∈ Ioo (0 : ℝ) 1
  · exact (hβ.2.2.1 s h).le
  · exact (hβ.2.1 s h).ge

/-- `β` is bounded: `β ≤ M` for some `M > 0`. -/
theorem exists_le : ∃ M : ℝ, 0 < M ∧ ∀ s, β s ≤ M := by
  obtain ⟨m, -, hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
    (hβ.continuous.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨β m + 1, by linarith [hβ.nonneg m], fun s ↦ ?_⟩
  by_cases h : s ∈ Icc (0 : ℝ) 1
  · linarith [isMaxOn_iff.1 hm s h]
  · have : β s = 0 := hβ.2.1 s fun h' ↦ h (Ioo_subset_Icc_self h')
    linarith [hβ.nonneg m]

/-- `β` has a positive lower bound on compact subintervals of `(0, 1)`. -/
theorem exists_pos_le {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Icc a b, c ≤ β s := by
  rcases lt_or_ge b a with hab | hab
  · exact ⟨1, one_pos, fun s hs ↦ absurd (hs.1.trans hs.2) (not_le.2 hab)⟩
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab)
    (hβ.continuous.continuousOn (s := Icc a b))
  exact ⟨β m, hβ.pos (ha.trans_le hm.1) (hm.2.trans_lt hb), fun s hs ↦ hmin hs⟩

theorem betaEps_nonneg (ε z : ℝ) (hε : 0 ≤ ε) : 0 ≤ betaEps β ε z :=
  div_nonneg (hβ.nonneg _) hε

theorem continuous_betaEps (ε : ℝ) : Continuous (betaEps β ε) :=
  (hβ.continuous.comp (continuous_id.div_const ε)).div_const ε

theorem hasDerivAt_bigBEps (ε z : ℝ) : HasDerivAt (bigBEps β ε) (betaEps β ε z) z :=
  ((hβ.continuous_betaEps ε).integral_hasStrictDerivAt 0 z).hasDerivAt

theorem integral_eq_half : ∫ s in (0 : ℝ)..1, β s = 1 / 2 := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← hβ.2.2.2.2.2]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ hβ.2.1 s fun h ↦ hs ?_
  exact Ioo_subset_Ioc_self h

omit hβ in
theorem bigBEps_one_eq (z : ℝ) : bigBEps β 1 z = ∫ s in (0 : ℝ)..z, β s := by
  simp [bigBEps, betaEps]

theorem hasDerivAt_bigB (z : ℝ) : HasDerivAt (bigBEps β 1) (β z) z := by
  simpa [betaEps] using hβ.hasDerivAt_bigBEps 1 z

theorem deriv_bigB : deriv (bigBEps β 1) = β := funext fun z ↦ (hβ.hasDerivAt_bigB z).deriv

theorem continuous_bigB : Continuous (bigBEps β 1) :=
  continuous_iff_continuousAt.2 fun z ↦ (hβ.hasDerivAt_bigB z).continuousAt

theorem contDiff_bigB : ContDiff ℝ ∞ (bigBEps β 1) :=
  contDiff_infty_iff_deriv.2 ⟨fun z ↦ (hβ.hasDerivAt_bigB z).differentiableAt,
    by rw [hβ.deriv_bigB]; exact hβ.contDiff⟩

theorem bigB_monotone : Monotone (bigBEps β 1) :=
  monotone_of_hasDerivAt_nonneg' hβ.hasDerivAt_bigB hβ.nonneg

theorem bigB_of_nonpos {z : ℝ} (hz : z ≤ 0) : bigBEps β 1 z = 0 := by
  rw [bigBEps_one_eq]
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_]
  · simp
  · rw [uIcc_of_ge hz] at hs
    exact hβ.eq_zero_of_nonpos hs.2

theorem bigB_one : bigBEps β 1 1 = 1 / 2 := by rw [bigBEps_one_eq, hβ.integral_eq_half]

theorem bigB_of_one_le {z : ℝ} (hz : 1 ≤ z) : bigBEps β 1 z = 1 / 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable β volume a b := fun a b ↦
    hβ.continuous.intervalIntegrable a b
  rw [bigBEps_one_eq, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 z),
    hβ.integral_eq_half, intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_]
  · simp
  · rw [uIcc_of_le hz] at hs
    exact hβ.eq_zero_of_one_le hs.1

theorem bigB_nonneg (z : ℝ) : 0 ≤ bigBEps β 1 z := by
  rcases le_total z 0 with hz | hz
  · rw [hβ.bigB_of_nonpos hz]
  · rw [← hβ.bigB_of_nonpos le_rfl]; exact hβ.bigB_monotone hz

theorem bigB_le_half (z : ℝ) : bigBEps β 1 z ≤ 1 / 2 := by
  rcases le_total z 1 with hz | hz
  · rw [← hβ.bigB_one]; exact hβ.bigB_monotone hz
  · rw [hβ.bigB_of_one_le hz]

theorem bigB_strictMonoOn : StrictMonoOn (bigBEps β 1) (Icc 0 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) hβ.continuous_bigB.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [hβ.deriv_bigB]
  exact hβ.pos hx.1 hx.2

theorem bigB_lt_half {z : ℝ} (hz : z < 1) : bigBEps β 1 z < 1 / 2 := by
  rcases le_total z 0 with h0 | h0
  · rw [hβ.bigB_of_nonpos h0]; norm_num
  · rw [← hβ.bigB_one]
    exact hβ.bigB_strictMonoOn ⟨h0, hz.le⟩ ⟨zero_le_one, le_rfl⟩ hz

theorem bigB_pos {z : ℝ} (hz : 0 < z) : 0 < bigBEps β 1 z := by
  rcases lt_or_ge z 1 with h1 | h1
  · rw [← hβ.bigB_of_nonpos le_rfl]
    exact hβ.bigB_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨hz.le, h1.le⟩ hz
  · rw [hβ.bigB_of_one_le h1]; norm_num

omit hβ in
/-- Rescaling: `𝓑_ε(z) = 𝓑(z/ε)`. -/
theorem bigBEps_eq {ε : ℝ} (hε : ε ≠ 0) (z : ℝ) : bigBEps β ε z = bigBEps β 1 (z / ε) := by
  rw [bigBEps_one_eq, bigBEps]
  simp only [betaEps]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_div (fun s ↦ β s) hε,
    zero_div, smul_eq_mul, mul_div_cancel_left₀ _ hε]

theorem bigBEps_nonneg {ε : ℝ} (hε : ε ≠ 0) (z : ℝ) : 0 ≤ bigBEps β ε z := by
  rw [bigBEps_eq hε]; exact hβ.bigB_nonneg _

theorem bigBEps_le_half {ε : ℝ} (hε : ε ≠ 0) (z : ℝ) : bigBEps β ε z ≤ 1 / 2 := by
  rw [bigBEps_eq hε]; exact hβ.bigB_le_half _

/-- `β(0) = 0`, hence `β_ε(0) = 0`. -/
theorem betaEps_zero (ε : ℝ) : betaEps β ε 0 = 0 := by
  simp [betaEps, hβ.eq_zero_of_nonpos le_rfl]

end IsReactionProfile

/-! ### Lemma A.2: the sub-profile `Φ_{1,θ}` -/

/-- The vector field `z ↦ √((1-θ) + 2θ𝓑(z))` of (A.2). -/
noncomputable def subField (β : ℝ → ℝ) (θ z : ℝ) : ℝ := √((1 - θ) + 2 * θ * bigBEps β 1 z)

/-- **Lemma A.2**: the sub-profile `Φ_{1,θ}(s) = G⁻¹(s - 1)`, where
`G(z) = ∫₁ᶻ dw / √((1-θ) + 2θ𝓑(w))` (proof of Lemma A.2). -/
noncomputable def profileSub (β : ℝ → ℝ) (θ : ℝ) (s : ℝ) : ℝ := odeSol (subField β θ) 1 (s - 1)

/-- The zero `s₀ = 1 + G(0)` of `Φ_{1,θ}` (Lemma A.2(iii)). -/
noncomputable def profileSubZero (β : ℝ → ℝ) (θ : ℝ) : ℝ := 1 + odeTimeMap (subField β θ) 1 0

/-- The constant `c_θ = (1 - √(1-θ)) / √(1-θ)` of Lemma A.2(iii). -/
noncomputable def subConst (θ : ℝ) : ℝ := (1 - √(1 - θ)) / √(1 - θ)

section ProfileSub

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
include hβ hθ hθ1

omit hθ1 in
theorem subField_arg_ge (z : ℝ) : 1 - θ ≤ (1 - θ) + 2 * θ * bigBEps β 1 z := by
  have := hβ.bigB_nonneg z; nlinarith

theorem subField_arg_pos (z : ℝ) : 0 < (1 - θ) + 2 * θ * bigBEps β 1 z :=
  (sub_pos.2 hθ1).trans_le (subField_arg_ge hβ hθ z)

omit hθ1 in
theorem subField_arg_le (z : ℝ) : (1 - θ) + 2 * θ * bigBEps β 1 z ≤ 1 := by
  have := hβ.bigB_le_half z; nlinarith

theorem subField_pos (z : ℝ) : 0 < subField β θ z := Real.sqrt_pos.2 (subField_arg_pos hβ hθ hθ1 z)

omit hθ1 in
theorem subField_le_one (z : ℝ) : subField β θ z ≤ 1 :=
  Real.sqrt_le_one.2 (subField_arg_le hβ hθ z)

omit hθ1 in
theorem sqrt_le_subField (z : ℝ) : √(1 - θ) ≤ subField β θ z :=
  Real.sqrt_le_sqrt (subField_arg_ge hβ hθ z)

omit hθ hθ1 in
theorem subField_of_one_le {z : ℝ} (hz : 1 ≤ z) : subField β θ z = 1 := by
  have : (1 - θ) + 2 * θ * (1 / 2 : ℝ) = 1 := by ring
  rw [subField, hβ.bigB_of_one_le hz, this, Real.sqrt_one]

omit hθ hθ1 in
theorem continuous_subField : Continuous (subField β θ) :=
  (continuous_const.add (continuous_const.mul hβ.continuous_bigB)).sqrt

theorem contDiff_subField : ContDiff ℝ ∞ (subField β θ) :=
  (contDiff_const.add (contDiff_const.mul hβ.contDiff_bigB)).sqrt fun z ↦
    (subField_arg_pos hβ hθ hθ1 z).ne'

theorem hasDerivAt_subField (z : ℝ) :
    HasDerivAt (subField β θ) (θ * β z / subField β θ z) z := by
  have h1 : HasDerivAt (fun z ↦ (1 - θ) + 2 * θ * bigBEps β 1 z) (2 * θ * β z) z :=
    ((hβ.hasDerivAt_bigB z).const_mul (2 * θ)).const_add (1 - θ)
  have h2 := h1.sqrt (subField_arg_pos hβ hθ hθ1 z).ne'
  convert h2 using 1
  simp only [subField]
  field_simp

theorem profileSub_hasDerivAt (s : ℝ) :
    HasDerivAt (profileSub β θ) (subField β θ (profileSub β θ s)) s := by
  have h := (odeSol_hasDerivAt (a := 1) (continuous_subField hβ) (subField_pos hβ hθ hθ1)
    (subField_le_one hβ hθ) (s - 1)).comp s ((hasDerivAt_id s).sub_const 1)
  simpa [profileSub] using h

theorem profileSub_deriv : deriv (profileSub β θ) = fun s ↦ subField β θ (profileSub β θ s) :=
  funext fun s ↦ (profileSub_hasDerivAt hβ hθ hθ1 s).deriv

theorem profileSub_one : profileSub β θ 1 = 1 := by
  simp [profileSub, odeSol_zero (continuous_subField hβ) (subField_pos hβ hθ hθ1)]

theorem profileSub_strictMono : StrictMono (profileSub β θ) := fun s t hst ↦
  odeSol_strictMono (continuous_subField hβ) (subField_pos hβ hθ hθ1) (subField_le_one hβ hθ)
    (by linarith)

theorem profileSub_continuous : Continuous (profileSub β θ) :=
  continuous_iff_continuousAt.2 fun s ↦ (profileSub_hasDerivAt hβ hθ hθ1 s).continuousAt

/-- `Φ_{1,θ} ∈ C^∞(ℝ)` (bootstrap, as in the proof of Lemma A.2). -/
theorem profileSub_contDiff : ContDiff ℝ ∞ (profileSub β θ) :=
  contDiff_infty_of_hasDerivAt_comp (profileSub_hasDerivAt hβ hθ hθ1) (contDiff_subField hβ hθ hθ1)

/-- The second derivative: `Φ'' = θ β(Φ)`, as a `HasDerivAt` statement for `Φ'`. -/
theorem profileSub_hasDerivAt_deriv (s : ℝ) :
    HasDerivAt (deriv (profileSub β θ)) (θ * β (profileSub β θ s)) s := by
  rw [profileSub_deriv hβ hθ hθ1]
  have h := (hasDerivAt_subField hβ hθ hθ1 (profileSub β θ s)).comp s
    (profileSub_hasDerivAt hβ hθ hθ1 s)
  convert h using 1
  field_simp [(subField_pos hβ hθ hθ1 (profileSub β θ s)).ne']

/-- **Lemma A.2(i)**: `Φ'' = θ β(Φ)` on `ℝ`. -/
theorem profileSub_deriv_deriv (s : ℝ) :
    deriv (deriv (profileSub β θ)) s = θ * β (profileSub β θ s) :=
  (profileSub_hasDerivAt_deriv hβ hθ hθ1 s).deriv

/-- **Lemma A.2(ii)**, derivative bounds: `√(1-θ) ≤ Φ' ≤ 1`. -/
theorem profileSub_deriv_mem (s : ℝ) :
    √(1 - θ) ≤ deriv (profileSub β θ) s ∧ deriv (profileSub β θ) s ≤ 1 := by
  rw [profileSub_deriv hβ hθ hθ1]
  exact ⟨sqrt_le_subField hβ hθ _, subField_le_one hβ hθ _⟩

theorem profileSub_deriv_pos (s : ℝ) : 0 < deriv (profileSub β θ) s := by
  rw [profileSub_deriv hβ hθ hθ1]; exact subField_pos hβ hθ hθ1 _

/-- **Lemma A.2(ii)**: `Φ(s) = s` for `s ≥ 1`. -/
theorem profileSub_of_one_le {s : ℝ} (hs : 1 ≤ s) : profileSub β θ s = s := by
  rcases hs.eq_or_lt with rfl | hs
  · exact profileSub_one hβ hθ hθ1
  have hd : ∀ t, HasDerivAt (fun t ↦ profileSub β θ t - t)
      (subField β θ (profileSub β θ t) - 1) t := fun t ↦
    (profileSub_hasDerivAt hβ hθ hθ1 t).sub (hasDerivAt_id t)
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun t ↦ profileSub β θ t - t)
    (fun t ↦ subField β θ (profileSub β θ t) - 1) hs
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) fun t _ ↦ hd t
  have hc1 : 1 ≤ profileSub β θ c := by
    rw [← profileSub_one hβ hθ hθ1]; exact (profileSub_strictMono hβ hθ hθ1).monotone hc.1.le
  rw [subField_of_one_le hβ hc1, sub_self, eq_comm, div_eq_zero_iff,
    profileSub_one hβ hθ hθ1] at hc'
  rcases hc' with h | h
  · linarith
  · linarith

/-- `s ↦ Φ(s) - s` is antitone (as `Φ' ≤ 1`). -/
theorem profileSub_sub_antitone : Antitone fun s ↦ profileSub β θ s - s := by
  have hd : ∀ t, HasDerivAt (fun t ↦ profileSub β θ t - t)
      (subField β θ (profileSub β θ t) - 1) t := fun t ↦
    (profileSub_hasDerivAt hβ hθ hθ1 t).sub (hasDerivAt_id t)
  refine antitone_of_deriv_nonpos (fun s ↦ (hd s).differentiableAt) fun s ↦ ?_
  rw [(hd s).deriv]
  linarith [subField_le_one hβ hθ (profileSub β θ s)]

/-- **Lemma A.2(iii)**: `s ≤ Φ(s)` for all `s` (`Φ(s) ≥ s` for `s ≤ 1`, equality for `s ≥ 1`). -/
theorem self_le_profileSub (s : ℝ) : s ≤ profileSub β θ s := by
  rcases le_total s 1 with hs | hs
  · have := profileSub_sub_antitone hβ hθ hθ1 hs
    simp only [profileSub_one hβ hθ hθ1, sub_self] at this
    linarith
  · rw [profileSub_of_one_le hβ hθ hθ1 hs]

/-- **Lemma A.2(iii)**: `Φ(s) ≤ 1` for `s ≤ 1`. -/
theorem profileSub_le_one {s : ℝ} (hs : s ≤ 1) : profileSub β θ s ≤ 1 := by
  rw [← profileSub_one hβ hθ hθ1]; exact (profileSub_strictMono hβ hθ hθ1).monotone hs

/-- `s ↦ Φ(s) - √(1-θ) s` is monotone (as `Φ' ≥ √(1-θ)`). -/
theorem profileSub_sub_monotone : Monotone fun s ↦ profileSub β θ s - √(1 - θ) * s :=
  monotone_of_hasDerivAt_nonneg' (fun s ↦ (profileSub_hasDerivAt hβ hθ hθ1 s).sub
    ((hasDerivAt_id s).const_mul _)) fun s ↦ by
      simp only [mul_one, sub_nonneg]; exact sqrt_le_subField hβ hθ _

theorem profileSub_profileSubZero : profileSub β θ (profileSubZero β θ) = 0 := by
  simp only [profileSub, profileSubZero, add_sub_cancel_left]
  exact odeSol_odeTimeMap (continuous_subField hβ) (subField_pos hβ hθ hθ1) 0

/-- **Lemma A.2(iii)**: `Φ > 0` exactly on `(s₀, ∞)`. -/
theorem profileSub_pos_iff (s : ℝ) : 0 < profileSub β θ s ↔ profileSubZero β θ < s := by
  rw [← profileSub_profileSubZero hβ hθ hθ1]; exact (profileSub_strictMono hβ hθ hθ1).lt_iff_lt

theorem profileSub_nonpos_iff (s : ℝ) : profileSub β θ s ≤ 0 ↔ s ≤ profileSubZero β θ := by
  rw [← not_lt, profileSub_pos_iff hβ hθ hθ1, not_lt]

theorem profileSubZero_nonpos : profileSubZero β θ ≤ 0 :=
  (profileSub_strictMono hβ hθ hθ1).le_iff_le.1 (by
    rw [profileSub_profileSubZero hβ hθ hθ1]; exact self_le_profileSub hβ hθ hθ1 0)

/-- **Lemma A.2(iii)**: `s₀ ∈ [-c_θ, 0]`. -/
theorem profileSubZero_mem : profileSubZero β θ ∈ Icc (-subConst θ) 0 := by
  refine ⟨?_, profileSubZero_nonpos hβ hθ hθ1⟩
  have hsq : 0 < √(1 - θ) := Real.sqrt_pos.2 (by linarith)
  have h1 := profileSub_sub_monotone hβ hθ hθ1 (profileSubZero_nonpos hβ hθ hθ1)
  have h2 := profileSub_sub_monotone hβ hθ hθ1 (zero_le_one' ℝ)
  simp only [profileSub_profileSubZero hβ hθ hθ1, profileSub_one hβ hθ hθ1] at h1 h2
  rw [subConst, neg_le, le_div_iff₀ hsq]
  linarith

omit hβ in
/-- `c_θ ≥ 0`. -/
theorem subConst_nonneg : 0 ≤ subConst θ := by
  have hsq : 0 < √(1 - θ) := Real.sqrt_pos.2 (by linarith)
  have : √(1 - θ) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  exact div_nonneg (by linarith) hsq.le

/-- **Lemma A.2(iii)**: `sup_ℝ |Φ₊ - s₊| ≤ 1`. -/
theorem abs_max_profileSub_sub_le (s : ℝ) :
    |max (profileSub β θ s) 0 - max s 0| ≤ 1 := by
  rcases le_total 1 s with hs | hs
  · rw [profileSub_of_one_le hβ hθ hθ1 hs, sub_self, abs_zero]; exact zero_le_one
  · have h1 := profileSub_le_one hβ hθ hθ1 hs
    rw [abs_le]
    constructor
    · have : max s 0 ≤ 1 := max_le hs zero_le_one
      have : 0 ≤ max (profileSub β θ s) 0 := le_max_right _ _
      linarith
    · have : max (profileSub β θ s) 0 ≤ 1 := max_le h1 zero_le_one
      have : 0 ≤ max s 0 := le_max_right _ _
      linarith

/-- `Φ` is `1`-Lipschitz: `|Φ(t) - Φ(s)| ≤ |t - s|`. -/
theorem abs_profileSub_sub_le (s t : ℝ) :
    |profileSub β θ t - profileSub β θ s| ≤ |t - s| := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm, abs_sub_comm t]; exact this t s (le_of_not_ge hst)
  have h1 := (profileSub_strictMono hβ hθ hθ1).monotone hst
  have h2 := profileSub_sub_antitone hβ hθ hθ1 hst
  simp only at h2
  rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 hst)]
  linarith

end ProfileSub

/-! ### (A.5): the rescaled sub-profile `Φ_{ε,θ}` -/

/-- (A.5): `Φ_{ε,θ}(s) = ε Φ_{1,θ}(s/ε)`. -/
noncomputable def profileSubEps (β : ℝ → ℝ) (θ ε : ℝ) (s : ℝ) : ℝ := ε * profileSub β θ (s / ε)

section ProfileSubEps

variable {β : ℝ → ℝ} (hβ : IsReactionProfile β) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
  {ε : ℝ} (hε : 0 < ε)
include hβ hθ hθ1 hε

theorem profileSubEps_hasDerivAt (s : ℝ) :
    HasDerivAt (profileSubEps β θ ε) (deriv (profileSub β θ) (s / ε)) s := by
  have h := ((profileSub_hasDerivAt hβ hθ hθ1 (s / ε)).comp s
    ((hasDerivAt_id s).div_const ε)).const_mul ε
  rw [profileSub_deriv hβ hθ hθ1]
  convert h using 1
  field_simp

theorem profileSubEps_deriv :
    deriv (profileSubEps β θ ε) = fun s ↦ deriv (profileSub β θ) (s / ε) :=
  funext fun s ↦ (profileSubEps_hasDerivAt hβ hθ hθ1 hε s).deriv

/-- Rescaled Lemma A.2(ii): `0 < Φ_ε' ≤ 1`. -/
theorem profileSubEps_deriv_mem (s : ℝ) :
    0 < deriv (profileSubEps β θ ε) s ∧ deriv (profileSubEps β θ ε) s ≤ 1 := by
  rw [profileSubEps_deriv hβ hθ hθ1 hε]
  exact ⟨profileSub_deriv_pos hβ hθ hθ1 _, (profileSub_deriv_mem hβ hθ hθ1 _).2⟩

omit hβ hθ hθ1 in
theorem profileSubEps_div (s : ℝ) : profileSubEps β θ ε s / ε = profileSub β θ (s / ε) := by
  rw [profileSubEps, mul_div_cancel_left₀ _ hε.ne']

theorem profileSubEps_hasDerivAt_deriv (s : ℝ) :
    HasDerivAt (deriv (profileSubEps β θ ε)) (θ * betaEps β ε (profileSubEps β θ ε s)) s := by
  rw [profileSubEps_deriv hβ hθ hθ1 hε]
  have h := (profileSub_hasDerivAt_deriv hβ hθ hθ1 (s / ε)).comp s
    ((hasDerivAt_id s).div_const ε)
  rw [betaEps, profileSubEps_div hε]
  convert h using 1
  simp only [one_div]
  ring

/-- Rescaled Lemma A.2(i): `Φ_ε'' = θ β_ε(Φ_ε)`. -/
theorem profileSubEps_deriv_deriv (s : ℝ) :
    deriv (deriv (profileSubEps β θ ε)) s = θ * betaEps β ε (profileSubEps β θ ε s) :=
  (profileSubEps_hasDerivAt_deriv hβ hθ hθ1 hε s).deriv

omit hε in
theorem profileSubEps_contDiff : ContDiff ℝ ∞ (profileSubEps β θ ε) :=
  contDiff_const.mul ((profileSub_contDiff hβ hθ hθ1).comp (contDiff_id.div_const ε))

omit hε in
theorem profileSubEps_continuous : Continuous (profileSubEps β θ ε) :=
  (profileSubEps_contDiff hβ hθ hθ1).continuous

theorem profileSubEps_strictMono : StrictMono (profileSubEps β θ ε) := fun _ _ hst ↦
  mul_lt_mul_of_pos_left ((profileSub_strictMono hβ hθ hθ1) (div_lt_div_of_pos_right hst hε)) hε

/-- Rescaled Lemma A.2(ii): `Φ_ε(s) = s` for `s ≥ ε`. -/
theorem profileSubEps_of_le {s : ℝ} (hs : ε ≤ s) : profileSubEps β θ ε s = s := by
  rw [profileSubEps, profileSub_of_one_le hβ hθ hθ1 ((one_le_div hε).2 hs),
    mul_div_cancel₀ _ hε.ne']

/-- Rescaled Lemma A.2(iii): `s ≤ Φ_ε(s)`. -/
theorem self_le_profileSubEps (s : ℝ) : s ≤ profileSubEps β θ ε s := by
  have := self_le_profileSub hβ hθ hθ1 (s / ε)
  rw [profileSubEps]
  calc s = ε * (s / ε) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left this hε.le

/-- Rescaled Lemma A.2(iii): `Φ_ε > 0` exactly on `(ε s₀, ∞)`. -/
theorem profileSubEps_pos_iff (s : ℝ) :
    0 < profileSubEps β θ ε s ↔ ε * profileSubZero β θ < s := by
  rw [profileSubEps, mul_pos_iff_of_pos_left hε, profileSub_pos_iff hβ hθ hθ1, lt_div_iff₀ hε,
    mul_comm]

/-- Rescaled Lemma A.2(iii): `sup_ℝ |(Φ_ε)₊ - s₊| ≤ ε`. -/
theorem abs_max_profileSubEps_sub_le (s : ℝ) :
    |max (profileSubEps β θ ε s) 0 - max s 0| ≤ ε := by
  have h := abs_max_profileSub_sub_le hβ hθ hθ1 (s / ε)
  have e1 : max (profileSubEps β θ ε s) 0 = ε * max (profileSub β θ (s / ε)) 0 := by
    rw [mul_max_of_nonneg _ _ hε.le, mul_zero, profileSubEps]
  have e2 : max s 0 = ε * max (s / ε) 0 := by
    rw [mul_max_of_nonneg _ _ hε.le, mul_zero, mul_div_cancel₀ _ hε.ne']
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos hε]
  exact mul_le_of_le_one_right hε.le h

/-- `Φ_ε` is `1`-Lipschitz. -/
theorem abs_profileSubEps_sub_le (s t : ℝ) :
    |profileSubEps β θ ε t - profileSubEps β θ ε s| ≤ |t - s| := by
  have h := abs_profileSub_sub_le hβ hθ hθ1 (s / ε) (t / ε)
  rw [profileSubEps, profileSubEps, ← mul_sub, abs_mul, abs_of_pos hε, ← sub_div, abs_div,
    abs_of_pos hε] at *
  rwa [le_div_iff₀ hε, mul_comm] at h

/-- Where the reaction term is active, `ε s₀ < s < ε` (used in the proof of Lemma A.4). -/
theorem mem_of_betaEps_profileSubEps_pos {s : ℝ}
    (hs : 0 < betaEps β ε (profileSubEps β θ ε s)) :
    ε * profileSubZero β θ < s ∧ s < ε := by
  rw [betaEps, profileSubEps_div hε] at hs
  have hb : 0 < β (profileSub β θ (s / ε)) := (div_pos_iff_of_pos_right hε).1 hs
  constructor
  · rw [← profileSubEps_pos_iff hβ hθ hθ1 hε, profileSubEps]
    exact mul_pos hε (lt_of_not_ge fun h ↦ hb.ne' (hβ.eq_zero_of_nonpos h))
  · by_contra h
    have h1 : 1 ≤ s / ε := (one_le_div hε).2 (le_of_not_gt h)
    rw [profileSub_of_one_le hβ hθ hθ1 h1] at hb
    exact hb.ne' (hβ.eq_zero_of_one_le h1)

end ProfileSubEps

end PerronVariational

end
