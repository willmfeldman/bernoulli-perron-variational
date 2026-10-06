/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Monotone relaxed subsolutions are subsolutions (Proposition 3.5)

The remark after Definition 3.4 and Proposition 3.5 of F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981.

## Main results

* `IsParaRelaxedSub.isParaSub_of_subset_closure` (remark after Definition 3.4): a relaxed
  subsolution `(u, E)` with `E ⊆ \overline{{u > 0}}` (inside `U × I`) is a subsolution, and `E`
  agrees with `\overline{{u > 0}}` on `U × I`.
* `nondegBarrier` and `nondegBarrier_isClassicalStrictParaSuper`: an explicit globally smooth,
  time-independent, strictly superharmonic radial barrier.
* `IsParaRelaxedSub.exists_sphere_le_of_mem` (Step 1, (3.2)):
  quantitative non-degeneracy `sup_{∂B_r(x₀)} u(·, t₀) ≥ κ_d q r`.
* `IsParaRelaxedSub.isParaSub_of_monotone` (**Proposition 3.5**, Step 2).

## Deviations from the paper's proof

* The paper's barrier is harmonic in `B₁ ∖ B_{1/2}`, so `∂ₜh - Δh = 0` there: it is *not* a
  classical *strict* supersolution, which the comparison with a relaxed subsolution
  (Definition 3.4) requires. We use instead
  `h(y) = A (1 - exp(K - λ |y - x₀|²))` with `K = d + 1`, `λ = 4K/r²`, `A = q r / (8K)`, which
  is globally smooth, vanishes exactly on `∂B_{r/2}(x₀)`, satisfies `Δh < 0` on `{h ≥ 0}` and
  `|∇h| = q/2 < Q` on `{h = 0}` provided `Q ≥ q > 0` there.
* No rescaling is used: the barrier is built directly at scale `r` around `x₀`, since the
  relaxed-subsolution property is not scale invariant with the same `Q`.
* Since test cylinders must satisfy `V̄ × [a, b] ⊆ U × I` (so `a > 0` when `I ⊆ (0, ∞)`), the
  bottom of the cylinder is placed at a small positive time `a`; closedness of `E` and
  `(B̄_r(x₀) × {0}) ∩ E = ∅` give `(B̄_r(x₀) × {a}) ∩ E = ∅`.
* The paper assumes "`E_t` nondecreasing"; here we do not, because the argument does not use it. The
  initial trace `u₀` is an arbitrary function with `u₀ ≤ u(·, t)` (the paper's `u(·, 0)`, combined
  with time monotonicity).
-/

open Set Filter Topology Metric InnerProductSpace
open scoped Gradient Laplacian RealInnerProductSpace ContDiff

@[expose] public section

namespace PerronVariational

/-! ### Laplacian calculus -/

section Calculus

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `Δf(x) = ∑ᵢ D²f(x)(eᵢ, eᵢ)` for the standard orthonormal basis. -/
private theorem laplacian_eq_sum_fderiv_fderiv' (f : F → ℝ) (x : F) :
    Δ f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ F i)
      (stdOrthonormalBasis ℝ F i) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply]
  rfl

/-- `∑ᵢ (Dg(x) eᵢ)² = |∇g(x)|²`. -/
private theorem sum_fderiv_basis_sq' (g : F → ℝ) (x : F) :
    ∑ i, (fderiv ℝ g x (stdOrthonormalBasis ℝ F i)) ^ 2 = ‖∇ g x‖ ^ 2 := by
  have h : ∀ v : F, fderiv ℝ g x v = ⟪∇ g x, v⟫ := fun v ↦ by
    simp [gradient, toDual_symm_apply]
  rw [← real_inner_self_eq_norm_sq, ← (stdOrthonormalBasis ℝ F).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h, sq, real_inner_comm (stdOrthonormalBasis ℝ F i)]

/-- Chain rule for the Laplacian: `Δ(f ∘ g)(x) = f''(g x) |∇g(x)|² + f'(g x) Δg(x)`
(same statement as `laplacian_comp` in `Semilinear/Calculus.lean`; duplicated here to avoid the
import). -/
private theorem laplacian_comp' {f : ℝ → ℝ} {g : F → ℝ} {x : F} (hf : ContDiffAt ℝ 2 f (g x))
    (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y ↦ f (g y)) x =
      deriv (deriv f) (g x) * ‖∇ g x‖ ^ 2 + deriv f (g x) * Δ g x := by
  have hgev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y := by
    filter_upwards [hg.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hfev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f (g y) := by
    have h1 : ∀ᶠ z in 𝓝 (g x), DifferentiableAt ℝ f z := by
      filter_upwards [hf.eventually (by simp)] with z hz
      exact hz.differentiableAt (by norm_num)
    exact hg.continuousAt.tendsto.eventually h1
  have hD1 : fderiv ℝ (fun y ↦ f (g y)) =ᶠ[𝓝 x] fun y ↦ deriv f (g y) • fderiv ℝ g y := by
    filter_upwards [hgev, hfev] with y hy1 hy2
    exact (hy2.hasDerivAt.comp_hasFDerivAt y hy1.hasFDerivAt).fderiv
  have hf1 : DifferentiableAt ℝ (deriv f) (g x) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) (g x) := hf.fderiv_right (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun z ↦ fderiv ℝ f z 1) (g x) := h1.clm_apply contDiffAt_const
    have h3 : (fun z ↦ fderiv ℝ f z 1) = deriv f := funext fun z ↦ fderiv_apply_one_eq_deriv
    rw [h3] at h2
    exact h2.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y ↦ deriv f (g y))
      (deriv (deriv f) (g x) • fderiv ℝ g x) x :=
    hf1.hasDerivAt.comp_hasFDerivAt x (hgev.self_of_nhds.hasFDerivAt)
  have hD2 := hc.smul hg1.hasFDerivAt
  have hfd : fderiv ℝ (fderiv ℝ fun y ↦ f (g y)) x =
      deriv f (g x) • fderiv ℝ (fderiv ℝ g) x +
        (deriv (deriv f) (g x) • fderiv ℝ g x).smulRight (fderiv ℝ g x) := by
    rw [hD1.fderiv_eq]; exact hD2.fderiv
  rw [laplacian_eq_sum_fderiv_fderiv', laplacian_eq_sum_fderiv_fderiv', hfd,
    ← sum_fderiv_basis_sq', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ F] in
private theorem hasFDerivAt_normSq_sub (x₀ y : F) :
    HasFDerivAt (fun y ↦ ‖y - x₀‖ ^ 2) ((2 : ℝ) • innerSL ℝ (y - x₀)) y := by
  convert ((hasFDerivAt_id y).sub_const x₀).norm_sq using 1 <;>
    first | rfl | (ext v; simp [two_smul])

omit [FiniteDimensional ℝ F] in
private theorem fderiv_normSq_sub (x₀ : F) :
    fderiv ℝ (fun y ↦ ‖y - x₀‖ ^ 2) = fun y ↦ (2 : ℝ) • innerSL ℝ (y - x₀) :=
  funext fun y ↦ (hasFDerivAt_normSq_sub x₀ y).fderiv

private theorem norm_gradient_normSq_sub (x₀ y : F) :
    ‖∇ (fun y ↦ ‖y - x₀‖ ^ 2) y‖ = 2 * ‖y - x₀‖ := by
  have : ‖∇ (fun y ↦ ‖y - x₀‖ ^ 2) y‖ = ‖fderiv ℝ (fun y ↦ ‖y - x₀‖ ^ 2) y‖ := by
    simp [gradient]
  rw [this, fderiv_normSq_sub, norm_smul, innerSL_apply_norm]
  norm_num

private theorem laplacian_normSq_sub (x₀ x : F) :
    Δ (fun y ↦ ‖y - x₀‖ ^ 2) x = 2 * Module.finrank ℝ F := by
  rw [laplacian_eq_sum_fderiv_fderiv', fderiv_normSq_sub]
  have hd : HasFDerivAt (fun y ↦ (2 : ℝ) • innerSL ℝ (y - x₀)) ((2 : ℝ) • innerSL ℝ) x := by
    have := ((innerSL ℝ (E := F)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀))
    exact this.const_smul (2 : ℝ)
  rw [hd.fderiv]
  have h1 : ∀ i, ((2 : ℝ) • innerSL ℝ (E := F)) (stdOrthonormalBasis ℝ F i)
      (stdOrthonormalBasis ℝ F i) = 2 := fun i ↦ by
    rw [smul_apply, smul_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, (stdOrthonormalBasis ℝ F).orthonormal.1 i]
    norm_num
  refine (Finset.sum_congr rfl fun i _ ↦ h1 i).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Calculus

/-! ### The barrier -/

section Barrier

variable {d : ℕ}

/-- The universal non-degeneracy constant `κ_d = (1 - e^{-3(d+1)}) / (8(d+1))` of (3.2). -/
noncomputable def nondegConst (d : ℕ) : ℝ :=
  (1 - Real.exp (-(3 * ((d : ℝ) + 1)))) / (8 * ((d : ℝ) + 1))

theorem nondegConst_pos (d : ℕ) : 0 < nondegConst d := by
  unfold nondegConst
  have : Real.exp (-(3 * ((d : ℝ) + 1))) < 1 :=
    Real.exp_lt_one_iff.2 (neg_neg_of_pos (by positivity))
  exact div_pos (by linarith) (by positivity)

/-- The radial profile `f(s) = A (1 - exp(K - λ s))` of the barrier, with `K = d + 1`,
`λ = 4K / r²`, `A = q r / (8K)`, as a function of `s = |y - x₀|²`. -/
noncomputable def nondegProfile (d : ℕ) (r q : ℝ) (s : ℝ) : ℝ :=
  q * r / (8 * ((d : ℝ) + 1)) * (1 - Real.exp (((d : ℝ) + 1) - 4 * ((d : ℝ) + 1) / r ^ 2 * s))

/-- **Barrier** (replacement for the harmonic barrier of the proof of Proposition 3.5, which is not
a strict supersolution; see the module docstring): the time-independent, globally smooth radial
function `h(y, t) = A (1 - exp(K - λ |y - x₀|²))`, `K = d + 1`, `λ = 4K / r²`, `A = q r / (8K)`. It
is negative at `x₀`, vanishes exactly on `∂B_{r/2}(x₀)`, equals `κ_d q r` on `∂B_r(x₀)`, and is a
classical strict supersolution whenever `Q ≥ q` on `∂B_{r/2}(x₀)`. -/
noncomputable def nondegBarrier (x₀ : E d) (r q : ℝ) : E d × ℝ → ℝ :=
  fun p ↦ nondegProfile d r q (‖p.1 - x₀‖ ^ 2)

private theorem hasDerivAt_nondegProfile (r q s : ℝ) :
    HasDerivAt (nondegProfile d r q)
      (q * r / (8 * ((d : ℝ) + 1)) * (4 * ((d : ℝ) + 1) / r ^ 2) *
        Real.exp (((d : ℝ) + 1) - 4 * ((d : ℝ) + 1) / r ^ 2 * s)) s := by
  have h := (((hasDerivAt_id s).const_mul (4 * ((d : ℝ) + 1) / r ^ 2)).const_sub
    ((d : ℝ) + 1)).exp
  have h2 := (h.const_sub 1).const_mul (q * r / (8 * ((d : ℝ) + 1)))
  convert h2 using 1
  · rfl
  · simp only [id]
    ring

private theorem deriv_nondegProfile (r q : ℝ) :
    deriv (nondegProfile d r q) = fun s ↦ q * r / (8 * ((d : ℝ) + 1)) *
      (4 * ((d : ℝ) + 1) / r ^ 2) *
        Real.exp (((d : ℝ) + 1) - 4 * ((d : ℝ) + 1) / r ^ 2 * s) :=
  funext fun s ↦ (hasDerivAt_nondegProfile r q s).deriv

private theorem deriv_deriv_nondegProfile (r q s : ℝ) :
    deriv (deriv (nondegProfile d r q)) s = -(q * r / (8 * ((d : ℝ) + 1)) *
      (4 * ((d : ℝ) + 1) / r ^ 2) ^ 2 *
        Real.exp (((d : ℝ) + 1) - 4 * ((d : ℝ) + 1) / r ^ 2 * s)) := by
  rw [deriv_nondegProfile]
  have h := (((hasDerivAt_id s).const_mul (4 * ((d : ℝ) + 1) / r ^ 2)).const_sub
    ((d : ℝ) + 1)).exp.const_mul (q * r / (8 * ((d : ℝ) + 1)) * (4 * ((d : ℝ) + 1) / r ^ 2))
  simp only [id] at h
  rw [h.deriv]
  ring

private theorem contDiff_nondegProfile (r q : ℝ) : ContDiff ℝ ∞ (nondegProfile d r q) := by
  unfold nondegProfile
  fun_prop

theorem contDiff_nondegBarrier (x₀ : E d) (r q : ℝ) : ContDiff ℝ ∞ (nondegBarrier x₀ r q) := by
  unfold nondegBarrier
  have h1 : ContDiff ℝ ∞ (fun p : E d × ℝ ↦ ‖p.1 - x₀‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const)
  exact (contDiff_nondegProfile r q).comp h1

theorem continuous_nondegBarrier (x₀ : E d) (r q : ℝ) : Continuous (nondegBarrier x₀ r q) :=
  (contDiff_nondegBarrier x₀ r q).continuous

/-- Sign of the profile: for `r ≠ 0`, `q r > 0`, `0 ≤ f(s) ↔ r²/4 ≤ s`. -/
private theorem nondegProfile_nonneg_iff {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (s : ℝ) :
    0 ≤ nondegProfile d r q s ↔ r ^ 2 / 4 ≤ s := by
  unfold nondegProfile
  have hA : 0 < q * r / (8 * ((d : ℝ) + 1)) := by positivity
  rw [mul_nonneg_iff_of_pos_left hA, sub_nonneg, Real.exp_le_one_iff, sub_nonpos,
    div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

private theorem nondegProfile_eq_zero_iff {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (s : ℝ) :
    nondegProfile d r q s = 0 ↔ s = r ^ 2 / 4 := by
  unfold nondegProfile
  have hA : q * r / (8 * ((d : ℝ) + 1)) ≠ 0 := by positivity
  rw [mul_eq_zero, or_iff_right hA, sub_eq_zero, eq_comm, Real.exp_eq_one_iff, sub_eq_zero,
    div_mul_eq_mul_div, eq_div_iff (by positivity)]
  constructor
  · intro h; nlinarith
  · intro h; subst h; ring

theorem nondegBarrier_center {x₀ : E d} {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (t : ℝ) :
    nondegBarrier x₀ r q (x₀, t) < 0 := by
  have h1 : ¬ 0 ≤ nondegBarrier x₀ r q (x₀, t) := by
    unfold nondegBarrier
    rw [nondegProfile_nonneg_iff hr hq]
    simp only [sub_self, norm_zero]
    intro h; nlinarith
  linarith [not_le.1 h1]

theorem nondegBarrier_of_mem_sphere {x₀ y : E d} {r q : ℝ} (hy : y ∈ sphere x₀ r) (hr : 0 < r)
    (t : ℝ) : nondegBarrier x₀ r q (y, t) = nondegConst d * q * r := by
  rw [mem_sphere, dist_eq_norm] at hy
  unfold nondegBarrier nondegProfile nondegConst
  simp only
  rw [hy]
  have : ((d : ℝ) + 1) - 4 * ((d : ℝ) + 1) / r ^ 2 * r ^ 2 = -(3 * ((d : ℝ) + 1)) := by
    field_simp; ring
  rw [this]
  field_simp

private theorem laplacian_nondegBarrier {x₀ : E d} {r q : ℝ} (y : E d) :
    Δ (fun y ↦ nondegProfile d r q (‖y - x₀‖ ^ 2)) y =
      q * r / (8 * ((d : ℝ) + 1)) * (4 * ((d : ℝ) + 1) / r ^ 2) *
        Real.exp (((d : ℝ) + 1) - 4 * ((d : ℝ) + 1) / r ^ 2 * ‖y - x₀‖ ^ 2) *
          (2 * d - 4 * (4 * ((d : ℝ) + 1) / r ^ 2 * ‖y - x₀‖ ^ 2)) := by
  have hg : ContDiff ℝ 2 (fun y : E d ↦ ‖y - x₀‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  rw [laplacian_comp' ((contDiff_nondegProfile r q).contDiffAt.of_le (by norm_cast))
    hg.contDiffAt, deriv_deriv_nondegProfile, deriv_nondegProfile, norm_gradient_normSq_sub,
    laplacian_normSq_sub, finrank_euclideanSpace_fin]
  ring

private theorem norm_gradient_nondegBarrier {x₀ : E d} {r q : ℝ} (y : E d) :
    ‖∇ (fun y ↦ nondegProfile d r q (‖y - x₀‖ ^ 2)) y‖ =
      |q * r / (8 * ((d : ℝ) + 1)) * (4 * ((d : ℝ) + 1) / r ^ 2) *
        Real.exp (((d : ℝ) + 1) - 4 * ((d : ℝ) + 1) / r ^ 2 * ‖y - x₀‖ ^ 2)| *
          (2 * ‖y - x₀‖) := by
  have hc := (hasDerivAt_nondegProfile (d := d) r q (‖y - x₀‖ ^ 2)).comp_hasFDerivAt y
    (hasFDerivAt_normSq_sub x₀ y)
  have : ‖∇ (fun y ↦ nondegProfile d r q (‖y - x₀‖ ^ 2)) y‖ =
      ‖fderiv ℝ (fun y ↦ nondegProfile d r q (‖y - x₀‖ ^ 2)) y‖ := by
    simp [gradient]
  rw [this, show (fun y ↦ nondegProfile d r q (‖y - x₀‖ ^ 2)) =
    nondegProfile d r q ∘ fun y ↦ ‖y - x₀‖ ^ 2 from rfl, hc.fderiv, norm_smul, norm_smul,
    innerSL_apply_norm, Real.norm_eq_abs]
  norm_num

/-- **The barrier is a classical strict supersolution** (in the sense of
`IsClassicalStrictParaSuper`, on every `V̄ × [a, b]`) provided `Q ≥ q > 0` on `∂B_{r/2}(x₀)`. -/
theorem nondegBarrier_isClassicalStrictParaSuper {Q : E d → ℝ} {x₀ : E d} {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hQ : ∀ y ∈ sphere x₀ (r / 2), q ≤ Q y) (V : Set (E d))
    (a b : ℝ) : IsClassicalStrictParaSuper Q (nondegBarrier x₀ r q) V a b := by
  have hcont := continuous_nondegBarrier x₀ r q
  have hK : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  refine ⟨contDiff_nondegBarrier x₀ r q, ?_, ?_⟩
  · rintro p ⟨hp, -⟩
    have hp' : 0 ≤ nondegBarrier x₀ r q p :=
      closure_lt_subset_le continuous_const hcont hp
    unfold nondegBarrier at hp'
    rw [nondegProfile_nonneg_iff hr hq] at hp'
    have hdt : dₜ (nondegBarrier x₀ r q) p = 0 := by
      unfold dₜ nondegBarrier; simp
    have hlap : lapₓ (nondegBarrier x₀ r q) p =
        Δ (fun y ↦ nondegProfile d r q (‖y - x₀‖ ^ 2)) p.1 := rfl
    rw [hdt, hlap, laplacian_nondegBarrier]
    have hL : (d : ℝ) + 1 ≤ 4 * ((d : ℝ) + 1) / r ^ 2 * ‖p.1 - x₀‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
    have hpos : 0 < q * r / (8 * ((d : ℝ) + 1)) * (4 * ((d : ℝ) + 1) / r ^ 2) *
        Real.exp (((d : ℝ) + 1) - 4 * ((d : ℝ) + 1) / r ^ 2 * ‖p.1 - x₀‖ ^ 2) := by
      positivity
    have hneg : 2 * (d : ℝ) - 4 * (4 * ((d : ℝ) + 1) / r ^ 2 * ‖p.1 - x₀‖ ^ 2) < 0 := by
      linarith
    nlinarith
  · rintro p ⟨hp, -⟩
    have hopen : IsOpen {q' | 0 < nondegBarrier x₀ r q q'} :=
      isOpen_lt continuous_const hcont
    rw [hopen.frontier_eq] at hp
    have h0 : nondegBarrier x₀ r q p = 0 :=
      le_antisymm (not_lt.1 hp.2) (closure_lt_subset_le continuous_const hcont hp.1)
    unfold nondegBarrier at h0
    rw [nondegProfile_eq_zero_iff hr hq] at h0
    have hn : ‖p.1 - x₀‖ = r / 2 := by
      have : ‖p.1 - x₀‖ ^ 2 = (r / 2) ^ 2 := by rw [h0]; ring
      exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
    have hgrad : gradₓ (nondegBarrier x₀ r q) p =
        ∇ (fun y ↦ nondegProfile d r q (‖y - x₀‖ ^ 2)) p.1 := rfl
    rw [hgrad, norm_gradient_nondegBarrier, h0, hn]
    have hsph : p.1 ∈ sphere x₀ (r / 2) := by rw [mem_sphere, dist_eq_norm, hn]
    have hQp := hQ _ hsph
    have : 4 * ((d : ℝ) + 1) / r ^ 2 * (r ^ 2 / 4) = (d : ℝ) + 1 := by field_simp
    rw [this, sub_self, Real.exp_zero, mul_one]
    rw [abs_of_pos (by positivity)]
    have : q * r / (8 * ((d : ℝ) + 1)) * (4 * ((d : ℝ) + 1) / r ^ 2) * (2 * (r / 2)) = q / 2 := by
      field_simp; ring
    rw [this]
    linarith

end Barrier

/-! ### Relaxed subsolutions contained in the closure of the positivity set -/

section Relaxed

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ}
  {Eset : Set (E d × ℝ)}

/-- For a relaxed subsolution, `\overline{{u > 0}} ⊆ E` (as `E` is closed and `{u > 0} ⊆ E`). -/
theorem IsParaRelaxedSub.closure_posSetP_subset (h : IsParaRelaxedSub U Q I u Eset) :
    closure (posSetP u (U ×ˢ I)) ⊆ Eset :=
  closure_minimal h.2.2.2.2.1 h.2.2.1

theorem AdmissibleCyl.parBdry_subset {V : Set (E d)} {a b : ℝ} (h : AdmissibleCyl U I V a b) :
    parBdry V a b ⊆ U ×ˢ I := by
  rintro ⟨x, t⟩ (⟨hx, ht⟩ | ⟨hx, ht⟩)
  · rw [mem_singleton_iff] at ht
    subst ht
    exact h.2.2.2 ⟨hx, le_rfl, h.2.2.1.le⟩
  · exact h.2.2.2 ⟨frontier_subset_closure hx, ht⟩

theorem AdmissibleCyl.cyl_subset {V : Set (E d)} {a b : ℝ} (h : AdmissibleCyl U I V a b) :
    cyl V a b ⊆ U ×ˢ I := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  exact h.2.2.2 ⟨subset_closure hx, Ioc_subset_Icc_self ht⟩

/-- **Remark after Definition 3.4**. If `(u, E)` is a relaxed subsolution and
`E ⊆ \overline{{u > 0}}` (inside the space-time domain `U × I`), then `E = \overline{{u > 0}}` on
`U × I` and `u` is a subsolution in the sense of Definition 3.2. -/
theorem IsParaRelaxedSub.isParaSub_of_subset_closure (h : IsParaRelaxedSub U Q I u Eset)
    (hE : Eset ∩ (U ×ˢ I) ⊆ closure (posSetP u (U ×ˢ I))) :
    Eset ∩ (U ×ˢ I) = closure (posSetP u (U ×ˢ I)) ∩ (U ×ˢ I) ∧ IsParaSub U Q I u := by
  refine ⟨subset_antisymm (fun p hp ↦ ⟨hE hp, hp.2⟩)
    (inter_subset_inter_left _ h.closure_posSetP_subset), h.1, h.2.1, ?_⟩
  intro V a b φ hV hφ hbd
  have hbd' : PrecOn u φ Eset (parBdry V a b) := fun p hp ↦
    hbd p ⟨hE ⟨hp.1, hV.parBdry_subset hp.2⟩, hp.2⟩
  have hin := h.2.2.2.2.2 V a b φ hV hφ hbd'
  exact fun p hp ↦ hin p ⟨h.closure_posSetP_subset hp.1, hp.2⟩

/-! ### Non-degeneracy (Step 1 of the proof of Proposition 3.5) -/

/-- **Non-degeneracy** (Step 1 of the proof of Proposition 3.5, (3.2)),
at scale `r` around `x₀` and without rescaling. Let `(u, E)` be a relaxed subsolution in `U × I`,
nondecreasing in time, let `B̄_r(x₀) ⊆ U`, `[a, t₀] ⊆ I` with `a < t₀`, suppose that the bottom
`B̄_r(x₀) × {a}` does not meet `E` and that `Q ≥ q > 0` on `∂B_{r/2}(x₀)`. If `(x₀, t₀) ∈ E` then
`sup_{∂B_r(x₀)} u(·, t₀) ≥ κ_d q r`. -/
theorem IsParaRelaxedSub.exists_sphere_le_of_mem (h : IsParaRelaxedSub U Q I u Eset)
    (hmono : MonotoneInTime u U I) {x₀ : E d} {r q a t₀ : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hball : closedBall x₀ r ⊆ U) (hat : a < t₀) (hI : Icc a t₀ ⊆ I)
    (hbot : ∀ y ∈ closedBall x₀ r, (y, a) ∉ Eset) (hQ : ∀ y ∈ sphere x₀ (r / 2), q ≤ Q y)
    (hmem : (x₀, t₀) ∈ Eset) :
    ∃ y ∈ sphere x₀ r, nondegConst d * q * r ≤ u (y, t₀) := by
  by_contra hcon
  push Not at hcon
  have hV : AdmissibleCyl U I (ball x₀ r) a t₀ := by
    refine ⟨isOpen_ball, isBounded_ball, hat, ?_⟩
    rw [closure_ball x₀ hr.ne']
    exact prod_mono hball hI
  have hbd : PrecOn u (nondegBarrier x₀ r q) Eset (parBdry (ball x₀ r) a t₀) := by
    rintro ⟨y, t⟩ ⟨hE, (⟨hy, ht⟩ | ⟨hy, ht⟩)⟩
    · rw [closure_ball x₀ hr.ne'] at hy
      rw [mem_singleton_iff] at ht
      subst ht
      exact absurd hE (hbot y hy)
    · rw [frontier_ball x₀ hr.ne'] at hy
      have hyU : y ∈ U := hball (sphere_subset_closedBall hy)
      calc u (y, t) ≤ u (y, t₀) := hmono y hyU (hI ht) (hI ⟨hat.le, le_rfl⟩) ht.2
        _ < nondegConst d * q * r := hcon y hy
        _ = nondegBarrier x₀ r q (y, t) := (nondegBarrier_of_mem_sphere hy hr t).symm
  have hin := h.2.2.2.2.2 _ _ _ _ hV
    (nondegBarrier_isClassicalStrictParaSuper hr hq hQ _ _ _) hbd
  have h1 := hin (x₀, t₀) ⟨hmem, mem_ball_self hr, hat, le_rfl⟩
  have h2 := h.2.1 (x₀, t₀) ⟨hball (mem_closedBall_self hr.le), hI ⟨hat.le, le_rfl⟩⟩
  have h3 := nondegBarrier_center (x₀ := x₀) (q := q) hr hq t₀
  linarith

/-- Qualitative non-degeneracy: under the hypotheses of `exists_sphere_le_of_mem` (with
`Q ≥ q > 0` on all of `B̄_r(x₀)`), `x₀ ∈ \overline{{u(·, t₀) > 0}}`. -/
theorem IsParaRelaxedSub.mem_closure_slice_of_mem (h : IsParaRelaxedSub U Q I u Eset)
    (hmono : MonotoneInTime u U I) {x₀ : E d} {r q a t₀ : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hball : closedBall x₀ r ⊆ U) (hat : a < t₀) (hI : Icc a t₀ ⊆ I)
    (hbot : ∀ y ∈ closedBall x₀ r, (y, a) ∉ Eset) (hQ : ∀ y ∈ closedBall x₀ r, q ≤ Q y)
    (hmem : (x₀, t₀) ∈ Eset) :
    x₀ ∈ closure {y ∈ U | 0 < u (y, t₀)} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hr' : 0 < min r (ε / 2) := lt_min hr (half_pos hε)
  have hr'r : min r (ε / 2) ≤ r := min_le_left _ _
  have hsub : closedBall x₀ (min r (ε / 2)) ⊆ closedBall x₀ r := closedBall_subset_closedBall hr'r
  obtain ⟨y, hy, hyu⟩ := h.exists_sphere_le_of_mem hmono hr' hq (hsub.trans hball) hat hI
    (fun y hy ↦ hbot y (hsub hy))
    (fun y hy ↦ hQ y (closedBall_subset_closedBall (by linarith) (sphere_subset_closedBall hy)))
    hmem
  have hκ := nondegConst_pos d
  refine ⟨y, ⟨hball (hsub (sphere_subset_closedBall hy)), lt_of_lt_of_le (by positivity) hyu⟩,
    ?_⟩
  rw [mem_sphere, dist_comm] at hy
  rw [hy]
  linarith [min_le_right r (ε / 2)]

/-! ### Proposition 3.5 -/

/-- **Proposition 3.5**, inclusion part. Let `(u, E)` be a relaxed
subsolution in `U × I`, where `U` is open and `I ⊆ (0, ∞)` is an initial segment
(`(0, t] ⊆ I` for `t ∈ I`; e.g. `I = (0, T]` or `(0, ∞)`), with `u` nondecreasing in time, and
`Q` locally bounded below by positive constants in `U`. Let `u₀` be an initial datum below `u`
(`u₀ ≤ u(·, t)` on `U` for `t ∈ I`; the paper's `u(·, 0)` with time monotonicity) with
`E₀ ∩ U ⊆ \overline{{u₀ > 0}}`. Then `E ⊆ \overline{{u > 0}}` in `U × I`.

The paper's hypothesis that the slices `E_t` are nondecreasing is not needed. -/
theorem IsParaRelaxedSub.subset_closure_posSetP_of_monotone (hU : IsOpen U)
    (hIpos : I ⊆ Ioi 0) (hIseg : ∀ t ∈ I, Ioc 0 t ⊆ I) (h : IsParaRelaxedSub U Q I u Eset)
    (hmono : MonotoneInTime u U I) (hQ : ∀ x ∈ U, ∃ q > 0, ∀ᶠ y in 𝓝 x, q ≤ Q y)
    (u₀ : E d → ℝ) (hu₀ : ∀ x ∈ U, ∀ t ∈ I, u₀ x ≤ u (x, t))
    (hE₀ : timeSlice Eset 0 ∩ U ⊆ closure {x ∈ U | 0 < u₀ x}) :
    Eset ∩ (U ×ˢ I) ⊆ closure (posSetP u (U ×ˢ I)) := by
  rintro ⟨x₀, t₀⟩ ⟨hmem, hx₀, ht₀⟩
  suffices hs : x₀ ∈ closure {y ∈ U | 0 < u (y, t₀)} by
    have hc : Continuous (fun y : E d ↦ (y, t₀)) := by fun_prop
    have hmaps : MapsTo (fun y : E d ↦ (y, t₀)) {y ∈ U | 0 < u (y, t₀)}
        (posSetP u (U ×ˢ I)) := fun y hy ↦ ⟨⟨hy.1, ht₀⟩, hy.2⟩
    exact hmaps.closure hc hs
  by_cases h0 : x₀ ∈ timeSlice Eset 0
  · refine closure_mono ?_ (hE₀ ⟨h0, hx₀⟩)
    rintro y ⟨hy, hpos⟩
    exact ⟨hy, hpos.trans_le (hu₀ y hy t₀ ht₀)⟩
  · -- a space-time ball around `(x₀, 0)` misses `E`
    obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.1 h.2.2.1.isOpen_compl (x₀, 0) h0
    obtain ⟨q, hq, hQev⟩ := hQ x₀ hx₀
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.eventually_nhds_iff_ball.1 (hQev.and (hU.mem_nhds hx₀))
    have ht₀pos : 0 < t₀ := hIpos ht₀
    set r := min (ρ / 2) (ε / 2) with hr_def
    have hr : 0 < r := lt_min (half_pos hρ) (half_pos hε)
    have hrρ : closedBall x₀ r ⊆ ball x₀ ρ :=
      closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ))
    set a := min (ε / 2) (t₀ / 2) with ha_def
    have ha : 0 < a := lt_min (half_pos hε) (half_pos ht₀pos)
    have hat : a < t₀ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self ht₀pos)
    refine h.mem_closure_slice_of_mem hmono hr hq (fun y hy ↦ (hρsub y (hrρ hy)).2) hat
      (fun t ht ↦ hIseg t₀ ht₀ ⟨ha.trans_le ht.1, ht.2⟩) ?_ (fun y hy ↦ (hρsub y (hrρ hy)).1) hmem
    intro y hy hyE
    refine hεE ?_ hyE
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · exact lt_of_le_of_lt (mem_closedBall.1 hy)
        (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε))
    · rw [Real.dist_eq, sub_zero, abs_of_pos ha]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)

/-- **Proposition 3.5**. Under the hypotheses of `subset_closure_posSetP_of_monotone`,
`E ⊆ \overline{{u > 0}}` in `U × I` and `u` is a standard subsolution (Definition 3.2). (See also
`isParaSub_of_subset_closure` for `E = \overline{{u > 0}}` on `U × I`.) -/
theorem IsParaRelaxedSub.isParaSub_of_monotone (hU : IsOpen U)
    (hIpos : I ⊆ Ioi 0) (hIseg : ∀ t ∈ I, Ioc 0 t ⊆ I) (h : IsParaRelaxedSub U Q I u Eset)
    (hmono : MonotoneInTime u U I) (hQ : ∀ x ∈ U, ∃ q > 0, ∀ᶠ y in 𝓝 x, q ≤ Q y)
    (u₀ : E d → ℝ) (hu₀ : ∀ x ∈ U, ∀ t ∈ I, u₀ x ≤ u (x, t))
    (hE₀ : timeSlice Eset 0 ∩ U ⊆ closure {x ∈ U | 0 < u₀ x}) :
    Eset ∩ (U ×ˢ I) ⊆ closure (posSetP u (U ×ˢ I)) ∧ IsParaSub U Q I u := by
  have hE := h.subset_closure_posSetP_of_monotone hU hIpos hIseg hmono hQ u₀ hu₀ hE₀
  exact ⟨hE, (h.isParaSub_of_subset_closure hE).2⟩

/-- Initial-time points: if `u₀ ≤ u(·, t)` and `E₀ ∩ U ⊆ \overline{{u₀ > 0}}`, and `I ⊆ (0, ∞)` is
a nonempty initial segment, then every `(x, 0) ∈ E` with `x ∈ U` lies in `\overline{{u > 0}}`. -/
theorem mem_closure_posSetP_of_mem_timeSlice_zero (hIne : I.Nonempty) (hIpos : I ⊆ Ioi 0)
    (hIseg : ∀ t ∈ I, Ioc 0 t ⊆ I) (u₀ : E d → ℝ) (hu₀ : ∀ x ∈ U, ∀ t ∈ I, u₀ x ≤ u (x, t))
    (hE₀ : timeSlice Eset 0 ∩ U ⊆ closure {x ∈ U | 0 < u₀ x}) {x : E d}
    (hx : x ∈ timeSlice Eset 0 ∩ U) : (x, (0 : ℝ)) ∈ closure (posSetP u (U ×ˢ I)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, ⟨hyU, hy0⟩, hxy⟩ := Metric.mem_closure_iff.1 (hE₀ hx) ε hε
  obtain ⟨t₁, ht₁⟩ := hIne
  have ht₁pos : 0 < t₁ := hIpos ht₁
  have htpos : 0 < min t₁ (ε / 2) := lt_min ht₁pos (half_pos hε)
  have htI : min t₁ (ε / 2) ∈ I := hIseg t₁ ht₁ ⟨htpos, min_le_left _ _⟩
  refine ⟨(y, min t₁ (ε / 2)), ⟨⟨hyU, htI⟩, hy0.trans_le (hu₀ y hyU _ htI)⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  refine ⟨hxy, ?_⟩
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos htpos]
  exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)

/-- **Proposition 3.5**, inclusion including the initial time: under the hypotheses of
`subset_closure_posSetP_of_monotone` and `I ≠ ∅`, `E ⊆ \overline{{u > 0}}` on `U × ({0} ∪ I)`.
(Only lateral-boundary points `x ∈ ∂U` of `E` are not covered.) -/
theorem IsParaRelaxedSub.subset_closure_posSetP_of_monotone' (hU : IsOpen U) (hIne : I.Nonempty)
    (hIpos : I ⊆ Ioi 0) (hIseg : ∀ t ∈ I, Ioc 0 t ⊆ I) (h : IsParaRelaxedSub U Q I u Eset)
    (hmono : MonotoneInTime u U I) (hQ : ∀ x ∈ U, ∃ q > 0, ∀ᶠ y in 𝓝 x, q ≤ Q y)
    (u₀ : E d → ℝ) (hu₀ : ∀ x ∈ U, ∀ t ∈ I, u₀ x ≤ u (x, t))
    (hE₀ : timeSlice Eset 0 ∩ U ⊆ closure {x ∈ U | 0 < u₀ x}) :
    Eset ∩ (U ×ˢ insert 0 I) ⊆ closure (posSetP u (U ×ˢ I)) := by
  rintro ⟨x, t⟩ ⟨hmem, hx, ht | ht⟩
  · subst ht
    exact mem_closure_posSetP_of_mem_timeSlice_zero hIne hIpos hIseg u₀ hu₀ hE₀ ⟨hmem, hx⟩
  · exact h.subset_closure_posSetP_of_monotone hU hIpos hIseg hmono hQ u₀ hu₀ hE₀ ⟨hmem, hx, ht⟩

/-- If moreover every point of `E` is a limit of points of `E ∩ (U × ({0} ∪ I))`, then
`E = \overline{{u > 0}}`. -/
theorem IsParaRelaxedSub.eq_closure_posSetP_of_monotone (hU : IsOpen U) (hIne : I.Nonempty)
    (hIpos : I ⊆ Ioi 0) (hIseg : ∀ t ∈ I, Ioc 0 t ⊆ I) (h : IsParaRelaxedSub U Q I u Eset)
    (hmono : MonotoneInTime u U I) (hQ : ∀ x ∈ U, ∃ q > 0, ∀ᶠ y in 𝓝 x, q ≤ Q y)
    (u₀ : E d → ℝ) (hu₀ : ∀ x ∈ U, ∀ t ∈ I, u₀ x ≤ u (x, t))
    (hE₀ : timeSlice Eset 0 ∩ U ⊆ closure {x ∈ U | 0 < u₀ x})
    (hcl : Eset ⊆ closure (Eset ∩ (U ×ˢ insert 0 I))) :
    Eset = closure (posSetP u (U ×ˢ I)) := by
  refine subset_antisymm (hcl.trans ?_) h.closure_posSetP_subset
  rw [← closure_closure (s := posSetP u (U ×ˢ I))]
  exact closure_mono
    (h.subset_closure_posSetP_of_monotone' hU hIne hIpos hIseg hmono hQ u₀ hu₀ hE₀)

/-- **Proposition 3.5** in the standing setting (`S : Setting d`) on `U × (0, T]`, the form used
by Corollary 5.4. -/
theorem IsParaRelaxedSub.isParaSub_of_monotone_Ioc (S : Setting d) {T : ℝ}
    (h : IsParaRelaxedSub S.U S.Q (Ioc 0 T) u Eset) (hmono : MonotoneInTime u S.U (Ioc 0 T))
    (u₀ : E d → ℝ) (hu₀ : ∀ x ∈ S.U, ∀ t ∈ Ioc 0 T, u₀ x ≤ u (x, t))
    (hE₀ : timeSlice Eset 0 ∩ S.U ⊆ closure {x ∈ S.U | 0 < u₀ x}) :
    Eset ∩ (S.U ×ˢ Ioc 0 T) ⊆ closure (posSetP u (S.U ×ˢ Ioc 0 T)) ∧
      IsParaSub S.U S.Q (Ioc 0 T) u := by
  refine h.isParaSub_of_monotone S.isOpen (fun t ht ↦ ht.1)
    (fun t ht s hs ↦ ⟨hs.1, hs.2.trans ht.2⟩) hmono ?_ u₀ hu₀ hE₀
  intro x hx
  refine ⟨S.Qmin, S.Qmin_pos, ?_⟩
  filter_upwards [S.isOpen.mem_nhds hx] with y hy
  exact (S.Q_mem y (subset_closure hy)).1

end Relaxed

end PerronVariational

end
