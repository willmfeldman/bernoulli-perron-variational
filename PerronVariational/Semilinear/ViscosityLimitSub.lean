/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Parabolic.StatToPara
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.ViscosityLimitCalculus
import PerronVariational.Semilinear.ViscosityLimitSuper
import PerronVariational.Topology.KLimit

/-!
# Proposition 5.3, Step 1: the relaxed subsolution property

Step 1 of the proof of Proposition 5.3 of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

## The paper's Proposition 5.3 is false for `E = limsup* {u_j > ε_j}`

Counterexample (any reaction profile `β`): `U = B₁ ⊆ ℝᵈ`, `Q ≡ 1`, `z = 2e₁`, `0 < t₀ < T`, `Γ` the
heat kernel, `h(x,t) = Γ(x - z, t - t₀)` for `t > t₀` and `0` for `t ≤ t₀` (smooth, bounded,
nonnegative heat solution on `U × ℝ`, positive exactly for `t > t₀`), `u_j = ε_j (1 + h)`. As
`u_j ≥ ε_j` and `β = 0` on `[1, ∞)`, `u_j` solves the semilinear equation; `u_j → u ≡ 0` uniformly
and `E = Ū × [t₀, T]`. For `V = B_{ρ₁}`, `a < t₀ < b`, `φ = A(|x|² - ρ²) + B(t - t₀)`
(`0 < ρ < ρ₁ < 1`, `2Aρ₁ < 1`, `B > 2dA`) is a strict supersolution with `u ≺_E φ` on `∂_P`
(`E ∩ ∂_P = ∂V × [t₀, b]`, where `φ > 0 = u`), but `p = (0, t₀) ∈ E` has `u(p) = 0 > φ(p)`.
The gap in the paper's proof is at the parabolic boundary in Step 1: off `E_j` one only has
`u_j ≤ ε_j`, not `u_j ≤ Ψ_{ε_j}(φ - δ)`. The authors' correction replaces `E` by
`E* = \overline{⋃_{0<κ≤1} limsup* {u_j > κ ε_j}}` (`ViscosityLimitStar`).

## What is proved here

* `relaxedSub_contra_of_nhds`: at a first crossing point `p` (maximal `u - φ` on `E` at the
  crossing time) where `E` contains a neighbourhood of `p`, a local stability argument (touching
  `u_j` from above by `φ` plus a strict quadratic penalty) gives a contradiction; hence
  `relaxedSub_case_pos` (case `u(p) > 0`, the paper's case (i)).
* `semilinear_limit_relaxedSolution` (**Proposition 5.3** in corrected form):
  `(u, \overline{U × (0,T]})` is a relaxed viscosity solution.
* `isParaRelaxedSub_semilinearLimitSet_of_case_zero`: the relaxed subsolution property for
  `E = limsup* {u_j > ε_j}`, conditional on excluding the case `u(p) = 0`.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### A quadratic penalty -/

section Penalty

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem hasFDerivAt_normSq_sub' (x₀ y : F) :
    HasFDerivAt (fun y ↦ ‖y - x₀‖ ^ 2) ((2 : ℝ) • innerSL ℝ (y - x₀)) y := by
  convert ((hasFDerivAt_id y).sub_const x₀).norm_sq using 1
  ext v
  simp [two_smul]

/-- `Δ ‖y - x₀‖² = 2 dim`. -/
theorem laplacian_normSq_sub' (x₀ x : F) :
    Δ (fun y ↦ ‖y - x₀‖ ^ 2) x = 2 * Module.finrank ℝ F := by
  have hf : fderiv ℝ (fun y ↦ ‖y - x₀‖ ^ 2) = fun y ↦ (2 : ℝ) • innerSL ℝ (y - x₀) :=
    funext fun y ↦ (hasFDerivAt_normSq_sub' x₀ y).fderiv
  rw [laplacian_eq_sum_fderiv_fderiv, hf]
  have hd : HasFDerivAt (fun y ↦ (2 : ℝ) • innerSL ℝ (y - x₀)) ((2 : ℝ) • innerSL ℝ) x := by
    have := ((innerSL ℝ (E := F)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀))
    exact this.const_smul (2 : ℝ)
  rw [hd.fderiv]
  have h1 : ∀ i, ((2 : ℝ) • innerSL ℝ (E := F)) (stdOrthonormalBasis ℝ F i)
      (stdOrthonormalBasis ℝ F i) = 2 := fun i ↦ by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, (stdOrthonormalBasis ℝ F).orthonormal.1 i]
    norm_num
  refine (Finset.sum_congr rfl fun i _ ↦ h1 i).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Penalty

/-- The heat operator of `φ + γ|x - x₀|² + γ(t₀ - t) + c` is that of `φ` minus `γ(1 + 2d)`. -/
theorem heat_quadPert {φ : E d × ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (γ c : ℝ) (x₀ : E d) (t₀ : ℝ)
    (p : E d × ℝ) :
    dₜ (fun q ↦ φ q + γ * ‖q.1 - x₀‖ ^ 2 + γ * (t₀ - q.2) + c) p -
        lapₓ (fun q ↦ φ q + γ * ‖q.1 - x₀‖ ^ 2 + γ * (t₀ - q.2) + c) p =
      dₜ φ p - lapₓ φ p - γ * (1 + 2 * d) := by
  have hdφ : DifferentiableAt ℝ φ p := hφ.differentiable (by norm_num) p
  have ht : HasDerivAt (fun s ↦ φ (p.1, s) + γ * ‖p.1 - x₀‖ ^ 2 + γ * (t₀ - s) + c)
      (fderiv ℝ φ p ((0 : E d), (1 : ℝ)) + γ * (0 - 1)) p.2 := by
    have h3 : HasDerivAt (fun s : ℝ ↦ γ * (t₀ - s)) (γ * (0 - 1)) p.2 :=
      ((hasDerivAt_const p.2 t₀).sub (hasDerivAt_id p.2)).const_mul γ
    exact (((hasDerivAt_timeSlice hdφ).add_const _).add h3).add_const c
  have hdt : dₜ (fun q ↦ φ q + γ * ‖q.1 - x₀‖ ^ 2 + γ * (t₀ - q.2) + c) p =
      dₜ φ p - γ := by
    rw [dₜ, ht.deriv, dₜ_eq_fderiv hdφ]; ring
  have hs1 : ContDiffAt ℝ 2 (fun y : E d ↦ φ (y, p.2)) p.1 :=
    (contDiff_spaceSlice hφ p.2).contDiffAt
  have hs2 : ContDiffAt ℝ 2 (γ • fun y : E d ↦ ‖y - x₀‖ ^ 2) p.1 :=
    (((contDiff_id.sub contDiff_const).norm_sq ℝ).const_smul γ).contDiffAt
  have hlap : lapₓ (fun q ↦ φ q + γ * ‖q.1 - x₀‖ ^ 2 + γ * (t₀ - q.2) + c) p =
      lapₓ φ p + γ * (2 * d) := by
    have e : (fun y : E d ↦ φ (y, p.2) + γ * ‖y - x₀‖ ^ 2 + γ * (t₀ - p.2) + c) =
        ((fun y : E d ↦ φ (y, p.2)) + γ • fun y : E d ↦ ‖y - x₀‖ ^ 2) +
          fun _ ↦ γ * (t₀ - p.2) + c := by
      funext y; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [lapₓ, e, ContDiffAt.laplacian_add
      (f₁ := (fun y : E d ↦ φ (y, p.2)) + γ • fun y : E d ↦ ‖y - x₀‖ ^ 2) (hs1.add hs2)
      contDiffAt_const, hs1.laplacian_add hs2,
      InnerProductSpace.laplacian_smul (f := fun y : E d ↦ ‖y - x₀‖ ^ 2) γ
        ((contDiff_id.sub contDiff_const).norm_sq ℝ).contDiffAt,
      laplacian_normSq_sub', finrank_euclideanSpace_fin, InnerProductSpace.laplacian_const]
    simp only [Pi.zero_apply, add_zero, smul_eq_mul, lapₓ]
  rw [hdt, hlap]; ring

/-! ### The limit set -/

section LimitSet

variable {S : Setting d} {β : ℝ → ℝ} {T : ℝ} {εs : ℕ → ℝ} {us : ℕ → E d × ℝ → ℝ}
  {u : E d × ℝ → ℝ}

/-- `{u > 0} ⊆ E = limsup* {u_j > ε_j}`. -/
theorem posSetP_subset_semilinearLimitSet (hεlim : Tendsto εs atTop (𝓝 0))
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    posSetP u (S.U ×ˢ Ioc 0 T) ⊆ semilinearLimitSet S.U (Ioc 0 T) εs us := by
  rintro p ⟨hpΩ, hup⟩
  have ht : Tendsto (fun j ↦ us j p - εs j) atTop (𝓝 (u p - 0)) :=
    (hconv.tendsto_at hpΩ).sub hεlim
  rw [sub_zero] at ht
  have hev : ∀ᶠ j in atTop, εs j < us j p := by
    filter_upwards [ht.eventually (lt_mem_nhds hup)] with j hj using sub_pos.1 hj
  intro N hN
  exact (hev.mono fun j hj ↦ ⟨p, ⟨hpΩ, hj⟩, mem_of_mem_nhds hN⟩).frequently

theorem semilinearLimitSet_subset :
    semilinearLimitSet S.U (Ioc 0 T) εs us ⊆ closure S.U ×ˢ closure (Ioc 0 T) := by
  rw [← closure_prod_eq]
  exact upperKLimit_subset_closure_of_eventually (Eventually.of_forall fun j ↦ sep_subset _ _)

theorem mem_cyl_of_not_mem_parBdry {V : Set (E d)} {a b : ℝ} (hV : IsOpen V) {q : E d × ℝ}
    (hq : q ∈ closure V ×ˢ Icc a b) (hn : q ∉ parBdry V a b) : q ∈ cyl V a b := by
  refine ⟨?_, ?_, hq.2.2⟩
  · by_contra hx
    refine hn (Or.inr ⟨⟨hq.1, ?_⟩, hq.2⟩)
    rw [hV.interior_eq]; exact hx
  · rcases hq.2.1.lt_or_eq with h | h
    · exact h
    · exact absurd (Or.inl ⟨hq.1, h.symm⟩) hn

end LimitSet

/-! ### Step 1 -/

section Step1

variable {S : Setting d} {β : ℝ → ℝ} {T : ℝ} {εs : ℕ → ℝ} {us : ℕ → E d × ℝ → ℝ}
  {u : E d × ℝ → ℝ}

/-- **Local contradiction at a first crossing point** (core of Step 1, case `u(p) > 0`). Let
`Eset` be any set containing a neighbourhood of `p` in `V × (a, b]`, `u ≥ 0`, and let `p` be a
first crossing point of the strict supersolution `φ` relative to `Eset` (`u < φ` on `Eset`
strictly before `p.2`, `u - φ` maximal at `p` on `Eset` up to time `p.2`) with `φ(p) ≤ u(p)`.
Then there is a contradiction: `p ∈ \overline{{φ > 0}}`, so `∂ₜφ - Δφ > 0` at `p`, and touching
`u_j` from above by `φ` plus a strict quadratic penalty contradicts the viscosity subsolution
property of `u_j`. -/
theorem relaxedSub_contra_of_nhds (hβ : IsReactionProfile β) (hεpos : ∀ j, 0 < εs j)
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T))
    (hunn : ∀ q ∈ S.U ×ˢ Ioc 0 T, 0 ≤ u q) {Eset : Set (E d × ℝ)}
    {V : Set (E d)} {a b : ℝ} {φ : E d × ℝ → ℝ} (hcyl : AdmissibleCyl S.U (Ioc 0 T) V a b)
    (hφ : IsClassicalStrictParaSuper S.Q φ V a b) {p : E d × ℝ} (hpcyl : p ∈ cyl V a b)
    (_hup : φ p ≤ u p) (hnE : ∃ ρ₀ > 0, ∀ q ∈ cyl V a b, dist q p < ρ₀ → q ∈ Eset)
    (hstrict : ∀ q ∈ Eset ∩ (closure V ×ˢ Icc a b), q.2 < p.2 → u q < φ q)
    (hmax : ∀ q ∈ Eset ∩ (closure V ×ˢ Icc a b), q.2 ≤ p.2 → u q - φ q ≤ u p - φ p) :
    False := by
  set Ω := S.U ×ˢ Ioc 0 T with hΩ_def
  obtain ⟨hVo, hVb, hab, hKΩ⟩ := hcyl
  have hucont := continuousOn_semilinearLimit hsol hconv
  have hpK : p ∈ closure V ×ˢ Icc a b := cyl_subset hpcyl
  have hpΩ : p ∈ Ω := hKΩ hpK
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (WithTop.coe_le_coe.2 le_top)
  -- (1) a neighbourhood of `p` in the cylinder lies in `Eset`
  obtain ⟨ρ₀, hρ₀, hρ₀E⟩ := hnE
  -- (2) `V` open
  obtain ⟨ρV, hρV, hballV⟩ := Metric.isOpen_iff.1 hVo p.1 hpcyl.1
  have hat : a < p.2 := hpcyl.2.1
  -- points of `cyl` near `p` belong to `E`
  have hinE : ∀ q ∈ cyl V a b, dist q p < ρ₀ → q ∈ Eset ∧ q ∈ closure V ×ˢ Icc a b :=
    fun q hq hd ↦ ⟨hρ₀E q hq hd, cyl_subset hq⟩
  -- (4) `p ∈ \overline{{φ > 0}}`
  have hclos : p ∈ closure {q | 0 < φ q} := by
    rcases lt_or_ge 0 (φ p) with hφp | hφp
    · exact subset_closure hφp
    have htend : Tendsto (fun s : ℝ ↦ (p.1, s)) (𝓝[<] p.2) (𝓝 p) :=
      ((continuous_const.prodMk continuous_id).tendsto p.2).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT (show max (p.2 - ρ₀) a < p.2 from max_lt (by linarith) hat)]
      with s hs
    have hq : (p.1, s) ∈ cyl V a b :=
      ⟨hpcyl.1, (le_max_right _ _).trans_lt hs.1, hs.2.le.trans hpcyl.2.2⟩
    have hd : dist (p.1, s) p < ρ₀ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_neg (by linarith [hs.2])]
      simp only [max_lt_iff]
      exact ⟨hρ₀, by linarith [(le_max_left (p.2 - ρ₀) a).trans_lt hs.1]⟩
    obtain ⟨hqE, hqK⟩ := hinE _ hq hd
    have h1 := hstrict _ ⟨hqE, hqK⟩ hs.2
    have h2 := hunn _ (hKΩ hqK)
    exact h2.trans_lt h1
  -- (5) the strict supersolution inequality at `p`
  set c₀ := dₜ φ p - lapₓ φ p with hc₀_def
  have hc₀ : 0 < c₀ := hφ.2.1 p ⟨hclos, hpK⟩
  have hheatc : Continuous (fun q ↦ dₜ φ q - lapₓ φ q) :=
    (continuous_dₜ (hφ.1.of_le (WithTop.coe_le_coe.2 le_top))).sub (continuous_lapₓ hφ2)
  obtain ⟨ρ₁, hρ₁, hρ₁h⟩ : ∃ ρ₁ > 0, ∀ q, dist q p < ρ₁ → c₀ / 2 < dₜ φ q - lapₓ φ q := by
    have h := hheatc.continuousAt.eventually (lt_mem_nhds (half_lt_self hc₀))
    exact Metric.eventually_nhds_iff.1 h
  set γ := c₀ / (4 * (1 + 2 * d)) with hγ_def
  have hγ : 0 < γ := by positivity
  have hγc : γ * (1 + 2 * d) = c₀ / 4 := by
    rw [hγ_def]; field_simp
  -- (8) the past cylinder `C`
  set ρ := min (min ρ₀ ρ₁) (min ρV (p.2 - a)) / 2 with hρ_def
  have hρ : 0 < ρ := by
    have : 0 < p.2 - a := by linarith
    positivity
  have hρ₀' : ρ < ρ₀ := by
    have := min_le_left (min ρ₀ ρ₁) (min ρV (p.2 - a)); have := min_le_left ρ₀ ρ₁; linarith
  have hρ₁' : ρ < ρ₁ := by
    have := min_le_left (min ρ₀ ρ₁) (min ρV (p.2 - a)); have := min_le_right ρ₀ ρ₁; linarith
  have hρV' : ρ < ρV := by
    have := min_le_right (min ρ₀ ρ₁) (min ρV (p.2 - a)); have := min_le_left ρV (p.2 - a)
    linarith
  have hρa : ρ < p.2 - a := by
    have := min_le_right (min ρ₀ ρ₁) (min ρV (p.2 - a)); have := min_le_right ρV (p.2 - a)
    linarith
  set C := closedBall p.1 ρ ×ˢ Icc (p.2 - ρ) p.2 with hC_def
  have hCc : IsCompact C := (isCompact_closedBall _ _).prod isCompact_Icc
  have hpC : p ∈ C := ⟨mem_closedBall_self hρ.le, by linarith, le_rfl⟩
  have hCcyl : ∀ q ∈ C, q ∈ cyl V a b := fun q hq ↦
    ⟨hballV (mem_ball.2 ((mem_closedBall.1 hq.1).trans_lt hρV')),
      by linarith [hq.2.1], hq.2.2.trans hpcyl.2.2⟩
  have hCdist : ∀ q ∈ C, dist q p ≤ ρ := fun q hq ↦ by
    rw [Prod.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [hq.2.2])]
    exact max_le (mem_closedBall.1 hq.1) (by linarith [hq.2.1])
  have hCΩ : C ⊆ Ω := fun q hq ↦ hKΩ (cyl_subset (hCcyl q hq))
  have hCmax : ∀ q ∈ C, u q - φ q ≤ u p - φ p := fun q hq ↦ by
    obtain ⟨hqE, hqK⟩ := hinE q (hCcyl q hq) ((hCdist q hq).trans_lt hρ₀')
    exact hmax q ⟨hqE, hqK⟩ hq.2.2
  -- (9) choose `j`
  set κ₀ := γ * min (ρ ^ 2) ρ with hκ₀_def
  have hκ₀ : 0 < κ₀ := by positivity
  obtain ⟨j, hj⟩ := (eventually_abs_sub_lt_of_isCompact hconv hCc hCΩ
    (show 0 < κ₀ / 3 by positivity)).exists
  -- (10) the maximum point of `u_j - ζ` on `C`
  set ζ : E d × ℝ → ℝ := fun q ↦ φ q + γ * ‖q.1 - p.1‖ ^ 2 + γ * (p.2 - q.2) with hζ_def
  have hζc : Continuous ζ := by
    rw [hζ_def]
    exact (hφ.1.continuous.add (continuous_const.mul
      ((continuous_fst.sub continuous_const).norm.pow 2))).add
      (continuous_const.mul (continuous_const.sub continuous_snd))
  obtain ⟨pj, hpjC, hpjmax⟩ := hCc.exists_isMaxOn ⟨p, hpC⟩
    (((hsol j).1.mono hCΩ).sub hζc.continuousOn)
  have hζp : ζ p = φ p := by simp [hζ_def]
  have hgp : us j p - ζ p ≤ us j pj - ζ pj := hpjmax hpC
  have hpen : ∀ q ∈ C, 0 ≤ γ * ‖q.1 - p.1‖ ^ 2 ∧ 0 ≤ γ * (p.2 - q.2) := fun q hq ↦
    ⟨by positivity, mul_nonneg hγ.le (by linarith [hq.2.2])⟩
  have hbound : ∀ q ∈ C, us j q - ζ q ≤
      u p - φ p - (γ * ‖q.1 - p.1‖ ^ 2 + γ * (p.2 - q.2)) + κ₀ / 3 := fun q hq ↦ by
    have h1 := hCmax q hq
    have h2 := (abs_lt.1 (hj q hq)).2
    simp only [hζ_def]
    linarith
  have hlow : u p - κ₀ / 3 - φ p < us j pj - ζ pj := by
    have := (abs_lt.1 (hj p hpC)).1
    rw [hζp] at hgp
    linarith
  have hκle : ∀ q ∈ C, (ρ ≤ ‖q.1 - p.1‖ ∨ q.2 ≤ p.2 - ρ) →
      κ₀ ≤ γ * ‖q.1 - p.1‖ ^ 2 + γ * (p.2 - q.2) := by
    intro q hq hor
    obtain ⟨h1, h2⟩ := hpen q hq
    rcases hor with h | h
    · have : ρ ^ 2 ≤ ‖q.1 - p.1‖ ^ 2 := pow_le_pow_left₀ hρ.le h 2
      have : κ₀ ≤ γ * ‖q.1 - p.1‖ ^ 2 := by
        rw [hκ₀_def]; exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans this) hγ.le
      linarith
    · have : κ₀ ≤ γ * (p.2 - q.2) := by
        rw [hκ₀_def]
        exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (by linarith)) hγ.le
      linarith
  have hpj_int : ‖pj.1 - p.1‖ < ρ ∧ p.2 - ρ < pj.2 := by
    by_contra hc
    rw [not_and_or, not_lt, not_lt] at hc
    have h1 := hκle pj hpjC hc
    have h2 := hbound pj hpjC
    linarith
  -- (11) the touching test function
  set cj := us j pj - ζ pj with hcj_def
  set ψ : E d × ℝ → ℝ := fun q ↦ φ q + γ * ‖q.1 - p.1‖ ^ 2 + γ * (p.2 - q.2) + cj with hψ_def
  have hψc : ContDiff ℝ 2 ψ := by
    rw [hψ_def]
    refine ((hφ2.add (contDiff_const.mul ((contDiff_fst.sub contDiff_const).norm_sq ℝ))).add
      (contDiff_const.mul (contDiff_const.sub contDiff_snd))).add contDiff_const
  have hpjΩ := hCΩ hpjC
  have htouch : TouchesAbove ψ (us j) (Ω ∩ {q | q.2 ≤ pj.2}) pj := by
    refine ⟨⟨hpjΩ, show pj.2 ≤ pj.2 from le_rfl⟩, by simp [hψ_def, hcj_def, hζ_def], ?_⟩
    have hopen : IsOpen (ball p.1 ρ ×ˢ Ioi (p.2 - ρ)) := isOpen_ball.prod isOpen_Ioi
    have hmem : pj ∈ ball p.1 ρ ×ˢ Ioi (p.2 - ρ) :=
      ⟨mem_ball_iff_norm.2 hpj_int.1, hpj_int.2⟩
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem), self_mem_nhdsWithin]
      with q hq hqS
    have hqC : q ∈ C := ⟨mem_closedBall.2 (mem_ball.1 hq.1).le, (mem_Ioi.1 hq.2).le,
      hqS.2.trans hpjC.2.2⟩
    have := hpjmax hqC
    simp only [mem_setOf_eq] at this
    simp only [hψ_def, hcj_def]
    simp only [hζ_def] at this ⊢
    linarith
  -- (12) the viscosity subsolution property of `u_j`
  have hvisc := (Registry.isSemilinearViscSubOn_of_solOn S.isOpen Ioc_leftNhds (hsol j)).2 ψ
    hψc pj hpjΩ htouch
  have hrhs : -(S.Q pj.1 ^ 2 * betaEps β (εs j) (us j pj)) ≤ 0 := by
    have := hβ.betaEps_nonneg (εs j) (us j pj) (hεpos j).le
    nlinarith [sq_nonneg (S.Q pj.1)]
  have hheat := heat_quadPert hφ2 γ cj p.1 p.2 pj
  have hpjd : dist pj p < ρ₁ := (hCdist pj hpjC).trans_lt hρ₁'
  have := hρ₁h pj hpjd
  simp only [hψ_def] at hvisc
  linarith

/-- **Step 1, case `u(p) > 0`.** At a first crossing point `p ∈ E ∩ (V × (a, b])` of a strict
supersolution `φ` with `u(p) > 0` there is a contradiction (local stability argument). -/
theorem relaxedSub_case_pos (hβ : IsReactionProfile β) (hεpos : ∀ j, 0 < εs j)
    (hεlim : Tendsto εs atTop (𝓝 0))
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hnn : ∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p)
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T))
    {V : Set (E d)} {a b : ℝ} {φ : E d × ℝ → ℝ} (hcyl : AdmissibleCyl S.U (Ioc 0 T) V a b)
    (hφ : IsClassicalStrictParaSuper S.Q φ V a b) {p : E d × ℝ} (hpcyl : p ∈ cyl V a b)
    (hup : φ p ≤ u p) (hu0 : 0 < u p)
    (hstrict : ∀ q ∈ semilinearLimitSet S.U (Ioc 0 T) εs us ∩ (closure V ×ˢ Icc a b),
      q.2 < p.2 → u q < φ q)
    (hmax : ∀ q ∈ semilinearLimitSet S.U (Ioc 0 T) εs us ∩ (closure V ×ˢ Icc a b),
      q.2 ≤ p.2 → u q - φ q ≤ u p - φ p) : False := by
  have hucont := continuousOn_semilinearLimit hsol hconv
  have hpΩ : p ∈ S.U ×ˢ Ioc 0 T := hcyl.2.2.2 (cyl_subset hpcyl)
  obtain ⟨ρ₀, hρ₀, hρ₀u⟩ : ∃ ρ₀ > 0, ∀ q ∈ S.U ×ˢ Ioc 0 T, dist q p < ρ₀ → 0 < u q := by
    have h := (hucont p hpΩ).eventually (lt_mem_nhds hu0)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ρ, hρ, hh⟩ := h
    exact ⟨ρ, hρ, fun q hq hd ↦ hh hd hq⟩
  exact relaxedSub_contra_of_nhds hβ hεpos hsol hconv (semilinearLimit_nonneg hnn hconv) hcyl hφ
    hpcyl hup ⟨ρ₀, hρ₀, fun q hq hd ↦ posSetP_subset_semilinearLimitSet hεlim hconv
      ⟨hcyl.2.2.2 (cyl_subset hq), hρ₀u q (hcyl.2.2.2 (cyl_subset hq)) hd⟩⟩ hstrict hmax

/-- **Reduction of the relaxed subsolution property with `E = limsup* {u_j > ε_j}` to the case
`u(p) = 0`.** Taking a first crossing time and then a maximum of `u - φ` on `E` at that time, the
case `u(p) > 0` is excluded by `relaxedSub_case_pos`; the remaining case is the hypothesis
`hzero`. (By the counterexample in the module docstring, `hzero` fails for general sequences
`u_j`; Corollary 5.4 uses the set `E*` instead.) -/
theorem isParaRelaxedSub_semilinearLimitSet_of_case_zero (hβ : IsReactionProfile β)
    (hεpos : ∀ j, 0 < εs j) (hεlim : Tendsto εs atTop (𝓝 0))
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hnn : ∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p)
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T))
    (hzero : ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ),
      AdmissibleCyl S.U (Ioc 0 T) V a b → IsClassicalStrictParaSuper S.Q φ V a b →
      PrecOn u φ (semilinearLimitSet S.U (Ioc 0 T) εs us) (parBdry V a b) →
      ∀ p ∈ semilinearLimitSet S.U (Ioc 0 T) εs us, p ∈ cyl V a b → φ p ≤ u p → u p = 0 →
      (∀ q ∈ semilinearLimitSet S.U (Ioc 0 T) εs us ∩ (closure V ×ˢ Icc a b),
        q.2 < p.2 → u q < φ q) →
      (∀ q ∈ semilinearLimitSet S.U (Ioc 0 T) εs us ∩ (closure V ×ˢ Icc a b),
        q.2 ≤ p.2 → u q - φ q ≤ u p - φ p) → False) :
    IsParaRelaxedSub S.U S.Q (Ioc 0 T) u (semilinearLimitSet S.U (Ioc 0 T) εs us) := by
  set Eset := semilinearLimitSet S.U (Ioc 0 T) εs us with hE_def
  have hucont := continuousOn_semilinearLimit hsol hconv
  have hunn := semilinearLimit_nonneg hnn hconv
  have hEc : IsClosed Eset := isClosed_upperKLimit
  refine ⟨hucont, hunn, hEc, semilinearLimitSet_subset,
    posSetP_subset_semilinearLimitSet hεlim hconv, ?_⟩
  intro V a b φ hcyl hφ hbd
  obtain ⟨hVo, hVb, hab, hKΩ⟩ := hcyl
  set K := closure V ×ˢ Icc a b with hK_def
  have hKc : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hKcont : ContinuousOn (fun q ↦ φ q - u q) K :=
    hφ.1.continuous.continuousOn.sub (hucont.mono hKΩ)
  intro p ⟨hpE, hpcyl⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨p₀, hp₀, hfp₀, hfirst⟩ := exists_first_crossing hVb hEc hKcont
    ⟨hpE, cyl_subset hpcyl⟩ (show φ p - u p ≤ 0 by linarith)
  -- maximize `u - φ` on `E ∩ K` at time `p₀.2`
  set C := Eset ∩ K ∩ {q | q.2 = p₀.2} with hC_def
  have hCc : IsCompact C := (hKc.inter_left hEc).inter_right
    (isClosed_eq continuous_snd continuous_const)
  obtain ⟨p₁, hp₁C, hp₁max⟩ := hCc.exists_isMaxOn ⟨p₀, hp₀, rfl⟩
    ((hucont.mono hKΩ).sub hφ.1.continuous.continuousOn |>.mono
      (inter_subset_left.trans inter_subset_right))
  have hp₁E : p₁ ∈ Eset ∩ K := hp₁C.1
  have hp₁t : p₁.2 = p₀.2 := hp₁C.2
  have hge : u p₀ - φ p₀ ≤ u p₁ - φ p₁ := hp₁max ⟨hp₀, rfl⟩
  have hup₁ : φ p₁ ≤ u p₁ := by linarith
  have hstrict : ∀ q ∈ Eset ∩ K, q.2 < p₁.2 → u q < φ q := fun q hq hqt ↦ by
    have := hfirst q hq (hp₁t ▸ hqt); linarith
  have hmax : ∀ q ∈ Eset ∩ K, q.2 ≤ p₁.2 → u q - φ q ≤ u p₁ - φ p₁ := by
    intro q hq hqt
    rcases hqt.lt_or_eq with h | h
    · have := hstrict q hq h; linarith
    · exact hp₁max ⟨hq, h.trans hp₁t⟩
  have hp₁cyl : p₁ ∈ cyl V a b := by
    refine mem_cyl_of_not_mem_parBdry hVo hp₁E.2 fun hbdy ↦ ?_
    have := hbd p₁ ⟨hp₁E.1, hbdy⟩
    linarith
  have hcyl : AdmissibleCyl S.U (Ioc 0 T) V a b := ⟨hVo, hVb, hab, hKΩ⟩
  rcases (hunn p₁ (hKΩ hp₁E.2)).lt_or_eq with hpos | hzero'
  · exact relaxedSub_case_pos hβ hεpos hεlim hsol hnn hconv hcyl hφ hp₁cyl hup₁ hpos hstrict
      hmax
  · exact hzero V a b φ hcyl hφ hbd p₁ hp₁E.1 hp₁cyl hup₁ hzero'.symm hstrict hmax

/-- **Proved replacement for Proposition 5.3's relaxed subsolution part.** With the trivial
set `E = \overline{U × (0, T]}`, `(u, E)` is a relaxed subsolution. (The relaxed ordering on all of
`∂_P` forces `φ > 0` on `∂_P`; the local contradiction `relaxedSub_contra_of_nhds` applies at every
first crossing point since `E` contains every neighbourhood.) This suffices for Theorem 3.9(iv)
in the decreasing case, which only asserts `∃ E`. -/
theorem semilinear_limit_isParaRelaxedSub_closure (hβ : IsReactionProfile β)
    (hεpos : ∀ j, 0 < εs j)
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hnn : ∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p)
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    IsParaRelaxedSub S.U S.Q (Ioc 0 T) u (closure (S.U ×ˢ Ioc 0 T)) := by
  set Eset := closure (S.U ×ˢ Ioc 0 T) with hE_def
  have hucont := continuousOn_semilinearLimit hsol hconv
  have hunn := semilinearLimit_nonneg hnn hconv
  have hEc : IsClosed Eset := isClosed_closure
  refine ⟨hucont, hunn, hEc, (closure_prod_eq).subset,
    fun q hq ↦ subset_closure hq.1, ?_⟩
  intro V a b φ hcyl hφ hbd
  obtain ⟨hVo, hVb, hab, hKΩ⟩ := hcyl
  set K := closure V ×ˢ Icc a b with hK_def
  have hKc : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hKcont : ContinuousOn (fun q ↦ φ q - u q) K :=
    hφ.1.continuous.continuousOn.sub (hucont.mono hKΩ)
  intro p ⟨hpE, hpcyl⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨p₀, hp₀, hfp₀, hfirst⟩ := exists_first_crossing hVb hEc hKcont
    ⟨hpE, cyl_subset hpcyl⟩ (show φ p - u p ≤ 0 by linarith)
  set C := Eset ∩ K ∩ {q | q.2 = p₀.2} with hC_def
  have hCc : IsCompact C := (hKc.inter_left hEc).inter_right
    (isClosed_eq continuous_snd continuous_const)
  obtain ⟨p₁, hp₁C, hp₁max⟩ := hCc.exists_isMaxOn ⟨p₀, hp₀, rfl⟩
    ((hucont.mono hKΩ).sub hφ.1.continuous.continuousOn |>.mono
      (inter_subset_left.trans inter_subset_right))
  have hp₁E : p₁ ∈ Eset ∩ K := hp₁C.1
  have hp₁t : p₁.2 = p₀.2 := hp₁C.2
  have hge : u p₀ - φ p₀ ≤ u p₁ - φ p₁ := hp₁max ⟨hp₀, rfl⟩
  have hup₁ : φ p₁ ≤ u p₁ := by linarith
  have hstrict : ∀ q ∈ Eset ∩ K, q.2 < p₁.2 → u q < φ q := fun q hq hqt ↦ by
    have := hfirst q hq (hp₁t ▸ hqt); linarith
  have hmax : ∀ q ∈ Eset ∩ K, q.2 ≤ p₁.2 → u q - φ q ≤ u p₁ - φ p₁ := by
    intro q hq hqt
    rcases hqt.lt_or_eq with h | h
    · have := hstrict q hq h; linarith
    · exact hp₁max ⟨hq, h.trans hp₁t⟩
  have hp₁cyl : p₁ ∈ cyl V a b := by
    refine mem_cyl_of_not_mem_parBdry hVo hp₁E.2 fun hbdy ↦ ?_
    have := hbd p₁ ⟨hp₁E.1, hbdy⟩
    linarith
  exact relaxedSub_contra_of_nhds hβ hεpos hsol hconv hunn ⟨hVo, hVb, hab, hKΩ⟩ hφ hp₁cyl hup₁
    ⟨1, one_pos, fun q hq _ ↦ subset_closure (hKΩ (cyl_subset hq))⟩ hstrict hmax

/-- Proposition 5.3 in corrected form: the limit is a relaxed viscosity solution for
`E = \overline{U × (0, T]}`. -/
theorem semilinear_limit_relaxedSolution_closure (hβ : IsReactionProfile β)
    (hεpos : ∀ j, 0 < εs j) (hεlim : Tendsto εs atTop (𝓝 0))
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hnn : ∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p)
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    IsParaRelaxedSolution S.U S.Q (Ioc 0 T) u (closure (S.U ×ˢ Ioc 0 T)) :=
  ⟨semilinear_limit_isParaSuper hβ hεpos hεlim hsol hnn hconv,
    semilinear_limit_isParaRelaxedSub_closure hβ hεpos hsol hnn hconv⟩

end Step1

/-- **Proposition 5.3**, in the corrected form of `SemilinearLimitRelaxedStatement`: the limit
is a relaxed viscosity solution with `E = \overline{U × (0, T]}`. The paper assumes
`E = limsup* {u_j > ε_j}`; here `E = \overline{U × (0, T]}`, because the statement with the
paper's set is false (see the module docstring). -/
theorem semilinear_limit_relaxedSolution : SemilinearLimitRelaxedStatement := by
  intro d S β hβ T εs us u _ hεpos hεlim hsol hnn hconv
  exact semilinear_limit_relaxedSolution_closure hβ hεpos hεlim hsol hnn hconv

end PerronVariational

end
