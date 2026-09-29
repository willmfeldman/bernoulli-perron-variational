/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Setting
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import PerronVariational.Semilinear.Calculus

/-!
# Directional derivatives of smooth functions (calculus for the Bernstein argument)

Steps 1 and 3 of the joint proof of Propositions A.5 and A.6 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.4):
the computation of the equation (A.8) for `w = |∇v|²` and the derivative tests at a maximum of
`z = η² w`.

We work with directional derivatives `D_a f(p) = Df(p) a` (`dd a f`) of functions `f : X → ℝ`
which are `C^∞` on an open set `O`, stating the calculus rules as equalities of functions on `O`
(`Set.EqOn`) so that they can be iterated. For space-time functions `f : ℝᵈ × ℝ → ℝ`, the
spatial directions are `(eᵢ, 0)` for the standard orthonormal basis `eᵢ` and the time direction
is `(0, 1)`; we relate them to `gradₓ`, `lapₓ`, `dₜ` and prove the derivative tests at a local
maximum relative to the parabolic past.
-/

open Set Filter Topology
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

section General

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The directional derivative `D_a f(p) = Df(p) a`. -/
noncomputable def dd (a : X) (f : X → ℝ) : X → ℝ := fun p ↦ fderiv ℝ f p a

variable {O : Set X} {f g : X → ℝ} {p : X}

theorem _root_.ContDiffOn.dd (hf : ContDiffOn ℝ ∞ f O) (hO : IsOpen O) (a : X) :
    ContDiffOn ℝ ∞ (dd a f) O :=
  (hf.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem _root_.ContDiffOn.differentiableAt' (hf : ContDiffOn ℝ ∞ f O) (hO : IsOpen O) (hp : p ∈ O) :
    DifferentiableAt ℝ f p :=
  (hf.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)

/-- `dd` only depends on the germ. -/
theorem dd_congr (h : EqOn f g O) (hO : IsOpen O) (hp : p ∈ O) (a : X) : dd a f p = dd a g p := by
  simp only [PerronVariational.dd]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hO.mem_nhds hp) h)]

theorem dd_add (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : X) :
    dd a (fun q ↦ f q + g q) p = dd a f p + dd a g p := by
  simp only [PerronVariational.dd, fderiv_fun_add hf hg, ContinuousLinearMap.add_apply]

theorem dd_sub (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : X) :
    dd a (fun q ↦ f q - g q) p = dd a f p - dd a g p := by
  simp only [PerronVariational.dd, fderiv_fun_sub hf hg, ContinuousLinearMap.sub_apply]

theorem dd_mul (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : X) :
    dd a (fun q ↦ f q * g q) p = f p * dd a g p + g p * dd a f p := by
  simp only [PerronVariational.dd, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem dd_const_mul (hf : DifferentiableAt ℝ f p) (c : ℝ) (a : X) :
    dd a (fun q ↦ c * f q) p = c * dd a f p := by
  simp only [PerronVariational.dd, fderiv_const_mul hf, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

theorem dd_const (c : ℝ) (a : X) : dd a (fun _ ↦ c) p = 0 := by
  simp [PerronVariational.dd]

theorem dd_sum {ι : Type*} (s : Finset ι) {F : ι → X → ℝ}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) p) (a : X) :
    dd a (fun q ↦ ∑ i ∈ s, F i q) p = ∑ i ∈ s, dd a (F i) p := by
  simp only [PerronVariational.dd]
  rw [fderiv_fun_sum hF, ContinuousLinearMap.sum_apply]

theorem dd_comp {Φ : ℝ → ℝ} (hΦ : DifferentiableAt ℝ Φ (f p)) (hf : DifferentiableAt ℝ f p)
    (a : X) : dd a (fun q ↦ Φ (f q)) p = deriv Φ (f p) * dd a f p := by
  change fderiv ℝ (Φ ∘ f) p a = _
  rw [(hΦ.hasDerivAt.comp_hasFDerivAt p hf.hasFDerivAt).fderiv]
  rfl

theorem dd_sq (hf : DifferentiableAt ℝ f p) (a : X) :
    dd a (fun q ↦ f q ^ 2) p = 2 * f p * dd a f p := by
  have : (fun q ↦ f q ^ 2) = fun q ↦ f q * f q := funext fun q ↦ sq (f q)
  rw [this, dd_mul hf hf]; ring

/-- `D_a D_b f = D²f(a, b)` (derivative in the direction `a` of `D_b f`). -/
theorem dd_dd_eq (hf : DifferentiableAt ℝ (fderiv ℝ f) p) (a b : X) :
    dd a (dd b f) p = fderiv ℝ (fderiv ℝ f) p a b := by
  change fderiv ℝ (fun q ↦ fderiv ℝ f q b) p a = _
  rw [fderiv_clm_apply hf (differentiableAt_const b)]
  simp

/-- **Symmetry of second derivatives**: `D_a D_b f = D_b D_a f` for `f` which is `C²` at `p`. -/
theorem dd_comm (hf : ContDiffAt ℝ 2 f p) (a b : X) : dd a (dd b f) p = dd b (dd a f) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [dd_dd_eq hd, dd_dd_eq hd]
  exact ContDiffAt.isSymmSndFDerivAt hf (by simp) a b

theorem _root_.ContDiffOn.contDiffAt_two (hf : ContDiffOn ℝ ∞ f O) (hO : IsOpen O) (hp : p ∈ O) :
    ContDiffAt ℝ 2 f p :=
  (hf.contDiffAt (hO.mem_nhds hp)).of_le (WithTop.coe_le_coe.2 le_top)

/-! #### Calculus rules as equalities on `O` -/

variable (hO : IsOpen O)
include hO

theorem dd_mul_eqOn (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O) (a : X) :
    EqOn (dd a (fun q ↦ f q * g q)) (fun q ↦ f q * dd a g q + g q * dd a f q) O :=
  fun _ hq ↦ dd_mul (hf.differentiableAt' hO hq) (hg.differentiableAt' hO hq) a

theorem dd_sq_eqOn (hf : ContDiffOn ℝ ∞ f O) (a : X) :
    EqOn (dd a (fun q ↦ f q ^ 2)) (fun q ↦ 2 * f q * dd a f q) O :=
  fun _ hq ↦ dd_sq (hf.differentiableAt' hO hq) a

theorem dd_comp_eqOn {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hf : ContDiffOn ℝ ∞ f O) (a : X) :
    EqOn (dd a (fun q ↦ Φ (f q))) (fun q ↦ deriv Φ (f q) * dd a f q) O :=
  fun _ hq ↦ dd_comp (hΦ.differentiable (by simp) _) (hf.differentiableAt' hO hq) a

theorem dd_sum_eqOn {ι : Type*} (s : Finset ι) {F : ι → X → ℝ}
    (hF : ∀ i ∈ s, ContDiffOn ℝ ∞ (F i) O) (a : X) :
    EqOn (dd a (fun q ↦ ∑ i ∈ s, F i q)) (fun q ↦ ∑ i ∈ s, dd a (F i) q) O :=
  fun _ hq ↦ dd_sum s (fun i hi ↦ (hF i hi).differentiableAt' hO hq) a

end General

/-! ### Space-time directions -/

section SpaceTime

variable {d : ℕ}

/-- The index type of the standard orthonormal basis of `ℝᵈ`. -/
abbrev Idx (d : ℕ) := Fin (Module.finrank ℝ (E d))

/-- The spatial direction `(eᵢ, 0)`. -/
noncomputable def spaceDir (i : Idx d) : E d × ℝ := ((stdOrthonormalBasis ℝ (E d) i : E d), 0)

/-- The time direction `(0, 1)`. -/
def timeDir : E d × ℝ := (0, 1)

variable {f z : E d × ℝ → ℝ} {p : E d × ℝ}

/-- The derivative of the time slice through `p` in the direction `v` is `Df(p)(v, 0)`. -/
theorem hasFDerivAt_slice (hf : DifferentiableAt ℝ f p) :
    HasFDerivAt (fun y ↦ f (y, p.2))
      ((fderiv ℝ f p).comp ((ContinuousLinearMap.id ℝ (E d)).prod 0)) p.1 := by
  have h : HasFDerivAt (fun y : E d ↦ (y, p.2)) ((ContinuousLinearMap.id ℝ (E d)).prod 0) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  exact hf.hasFDerivAt.comp p.1 h

theorem fderiv_slice_apply (hf : DifferentiableAt ℝ f p) (v : E d) :
    fderiv ℝ (fun y ↦ f (y, p.2)) p.1 v = fderiv ℝ f p (v, 0) := by
  rw [(hasFDerivAt_slice hf).fderiv]
  simp

theorem dd_spaceDir_eq (hf : DifferentiableAt ℝ f p) (i : Idx d) :
    dd (spaceDir i) f p = fderiv ℝ (fun y ↦ f (y, p.2)) p.1 (stdOrthonormalBasis ℝ (E d) i) :=
  (fderiv_slice_apply hf _).symm

/-- `∂ₜ f = D_{(0,1)} f`. -/
theorem dₜ_eq_dd (hf : DifferentiableAt ℝ f p) : dₜ f p = dd timeDir f p := by
  have h : HasDerivAt (fun s : ℝ ↦ ((p.1, s) : E d × ℝ)) ((0 : E d), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h2 := hf.hasFDerivAt.comp_hasDerivAt p.2 h
  simp only [dₜ, PerronVariational.dd, timeDir]
  exact h2.deriv

/-- `|∇ₓ f|² = ∑ᵢ (D_{(eᵢ,0)} f)²`. -/
theorem norm_gradₓ_sq (hf : DifferentiableAt ℝ f p) :
    ‖gradₓ f p‖ ^ 2 = ∑ i : Idx d, dd (spaceDir i) f p ^ 2 := by
  simp only [gradₓ]
  rw [← sum_fderiv_basis_sq]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [dd_spaceDir_eq hf]

/-- `Δₓ f = ∑ᵢ D_{(eᵢ,0)} D_{(eᵢ,0)} f` for `f` which is `C²` at `p`. -/
theorem lapₓ_eq_sum_dd (hf : ContDiffAt ℝ 2 f p) :
    lapₓ f p = ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) f) p := by
  have hsl : ContDiffAt ℝ 2 (fun y ↦ f (y, p.2)) p.1 :=
    hf.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
  have hsl1 : DifferentiableAt ℝ (fderiv ℝ fun y ↦ f (y, p.2)) p.1 :=
    (hsl.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q := by
    filter_upwards [hf.eventually (by simp)] with q hq using hq.differentiableAt (by norm_num)
  have hdd : ∀ i, DifferentiableAt ℝ (dd (spaceDir i) f) p := fun i ↦
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  simp only [lapₓ]
  rw [laplacian_eq_sum_fderiv_fderiv]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← dd_dd_eq hsl1]
  have hev' : (dd (stdOrthonormalBasis ℝ (E d) i) fun y ↦ f (y, p.2)) =ᶠ[𝓝 p.1]
      fun y ↦ dd (spaceDir i) f (y, p.2) := by
    have ht : Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝 p) := by
      have : Continuous (fun y : E d ↦ (y, p.2)) := continuous_id.prodMk continuous_const
      simpa using this.tendsto p.1
    filter_upwards [ht.eventually hev] with y hy
    exact (dd_spaceDir_eq (p := (y, p.2)) hy i).symm
  simp only [PerronVariational.dd] at hev' ⊢
  rw [hev'.fderiv_eq]
  exact fderiv_slice_apply (hdd i) _

/-! #### Derivative tests at a maximum relative to the parabolic past -/

variable (hz : ContDiffAt ℝ 2 z p) (hmax : ∀ᶠ q in 𝓝 p, q.2 ≤ p.2 → z q ≤ z p)
include hz hmax

omit hz in
theorem isLocalMax_slice : IsLocalMax (fun y ↦ z (y, p.2)) p.1 := by
  have ht : Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝 p) := by
    have : Continuous (fun y : E d ↦ (y, p.2)) := continuous_id.prodMk continuous_const
    simpa using this.tendsto p.1
  filter_upwards [ht.eventually hmax] with y hy using hy le_rfl

/-- First-order spatial test: `D_{(eᵢ,0)} z = 0`. -/
theorem dd_spaceDir_eq_zero_of_max (i : Idx d) : dd (spaceDir i) z p = 0 := by
  rw [dd_spaceDir_eq (hz.differentiableAt (by norm_num)), (isLocalMax_slice hmax).fderiv_eq_zero]
  rfl

/-- Second-order spatial test: `∑ᵢ D_{(eᵢ,0)}² z ≤ 0`. -/
theorem sum_dd_spaceDir_nonpos_of_max :
    ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) z) p ≤ 0 := by
  rw [← lapₓ_eq_sum_dd hz]
  have hsl : ContDiffAt ℝ 2 (fun y ↦ z (y, p.2)) p.1 :=
    hz.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
  have hmin : IsLocalMin (fun y ↦ -z (y, p.2)) p.1 := (isLocalMax_slice hmax).neg
  have h := laplacian_nonneg_of_isLocalMin hmin hsl.neg
  have hneg : Δ (fun y ↦ -z (y, p.2)) p.1 = -Δ (fun y ↦ z (y, p.2)) p.1 := by
    have := congrFun (InnerProductSpace.laplacian_neg (f := fun y ↦ z (y, p.2))) p.1
    exact this
  simp only [lapₓ]
  linarith

/-- First-order time test (one-sided): `D_{(0,1)} z ≥ 0`. -/
theorem dd_timeDir_nonneg_of_max : 0 ≤ dd timeDir z p := by
  have hd : DifferentiableAt ℝ z p := hz.differentiableAt (by norm_num)
  rw [← dₜ_eq_dd hd]
  have hts : DifferentiableAt ℝ (fun s ↦ z (p.1, s)) p.2 :=
    hd.comp p.2 ((differentiableAt_const p.1).prodMk differentiableAt_id)
  refine deriv_nonneg_of_eventually_le_left hts ?_
  have ht : Tendsto (fun s : ℝ ↦ (p.1, s)) (𝓝[≤] p.2) (𝓝 p) := by
    have : Continuous (fun s : ℝ ↦ (p.1, s)) := continuous_const.prodMk continuous_id
    exact (by simpa using this.tendsto p.2 : Tendsto _ (𝓝 p.2) (𝓝 p)).mono_left
      nhdsWithin_le_nhds
  filter_upwards [ht.eventually hmax, self_mem_nhdsWithin] with s hs hs' using hs hs'

end SpaceTime

end PerronVariational

end
