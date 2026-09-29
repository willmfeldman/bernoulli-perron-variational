/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Registry.Semilinear
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Registry.Comparison
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Profiles

/-!
# Monotonicity in time and `L^∞` bounds (Proposition 3.8(ii), Lemma A.1)

Lemma A.1 (Appendix A.1) and the bound (3.7) of Proposition 3.8(ii) of F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981.

## Main results

* `IsSemilinearSolOn.mono`, `IsSemilinearSolOn.comp_add_time`, `isSemilinearSolOn_const`:
  restriction, time translation and constant solutions (constants `c` with `β_ε(c) = 0`).
* `IsSemilinearViscSubStat.isSemilinearViscSubOn`,
  `IsSemilinearViscSuperStat.isSemilinearViscSuperOn`:
  a stationary viscosity sub/supersolution of `Δv = Q² β_ε(v)` is a time-independent parabolic
  viscosity sub/supersolution of `∂ₜu = Δu - Q² β_ε(u)`.
* `IsSemilinearSolution.le_of_viscSubStat`, `IsSemilinearSolution.le_of_viscSuperStat`:
  comparison of the solution with its (stationary sub/super) data (first step of Lemma A.1).
* `IsSemilinearSolution.monotoneInTime`, `IsSemilinearSolution.antitoneInTime`: **Lemma A.1**,
  by comparison with the time-shifted solution.
* `IsSemilinearSolution.mem_Icc`: the bound (3.7), by comparison with constant solutions.
* `isSemilinearViscSuperOn_of_classical`: classical parabolic supersolutions are viscosity
  supersolutions; `IsSemilinearSolOn.mono_left`: spatial restriction.
* `IsSemilinearSolution.le_add_of_lipschitzOnWith`: `u(y, t) ≤ g(y) + σ + 2d (L²/4σ) t`, by
  comparison with a caloric quadratic barrier (used for Lemma A.11).

All comparisons are the comparison principle for the semilinear equation
(`Registry.semilinear_comparison`, from parabolic-basic-theory v0.1.0) on the cylinders
`U × (0, b]`; classical solutions are viscosity solutions by the same dependency
(`Registry.isSemilinearViscSubOn_of_solOn`, `Registry.isSemilinearViscSuperOn_of_solOn`).
-/

open Set Filter Topology
open scoped Gradient Laplacian ContDiff NNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Left neighbourhoods (the one-sided derivative tests are in `Semilinear.Calculus`) -/

/-- Left neighbourhoods in `(a, b]`. -/
theorem exists_Ioc_subset_Ioc {a b : ℝ} :
    ∀ t ∈ Ioc a b, ∃ δ > 0, Ioc (t - δ) t ⊆ Ioc a b :=
  fun t ht ↦ ⟨t - a, sub_pos.2 ht.1, fun s hs ↦ ⟨by linarith [hs.1], hs.2.trans ht.2⟩⟩

/-! ### Classical solutions: restriction, translation, constants -/

section Classical

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {I J : Set ℝ}
  {u : E d × ℝ → ℝ}

/-- Restriction of a classical solution to a smaller time set. -/
theorem IsSemilinearSolOn.mono (hu : IsSemilinearSolOn U Q β ε I u) (hJ : J ⊆ I) :
    IsSemilinearSolOn U Q β ε J u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hu
  have hs : U ×ˢ J ⊆ U ×ˢ I := prod_mono subset_rfl hJ
  exact ⟨h1.mono hs, fun t ht ↦ h2 t (hJ ht), h3.mono hs, h4.mono hs, fun p hp ↦ h5 p (hs hp),
    h6.mono hs, fun p hp ↦ h7 p (hs hp)⟩

/-- Restriction of a classical solution to a smaller spatial set. -/
theorem IsSemilinearSolOn.mono_left {V : Set (E d)} (hu : IsSemilinearSolOn U Q β ε I u)
    (hV : V ⊆ U) : IsSemilinearSolOn V Q β ε I u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hu
  have hs : V ×ˢ I ⊆ U ×ˢ I := prod_mono hV subset_rfl
  exact ⟨h1.mono hs, fun t ht ↦ (h2 t ht).mono hV, h3.mono hs, h4.mono hs,
    fun p hp ↦ h5 p (hs hp), h6.mono hs, fun p hp ↦ h7 p (hs hp)⟩

/-- The time derivative commutes with time translation. -/
theorem dₜ_comp_add_time (u : E d × ℝ → ℝ) (h : ℝ) :
    dₜ (fun q : E d × ℝ ↦ u (q.1, q.2 + h)) = fun p ↦ dₜ u (p.1, p.2 + h) := by
  funext p
  exact deriv_comp_add_const (f := fun s ↦ u (p.1, s)) (a := h) (x := p.2)

/-- The time translate `(x, t) ↦ u(x, t + h)` of a classical solution in `U × I` is a classical
solution in `U × (I - h)`. -/
theorem IsSemilinearSolOn.comp_add_time (hu : IsSemilinearSolOn U Q β ε I u) (h : ℝ) :
    IsSemilinearSolOn U Q β ε ((· + h) ⁻¹' I) (fun q ↦ u (q.1, q.2 + h)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hu
  have hc : Continuous fun q : E d × ℝ ↦ (q.1, q.2 + h) := by fun_prop
  have hm : MapsTo (fun q : E d × ℝ ↦ (q.1, q.2 + h)) (U ×ˢ ((· + h) ⁻¹' I)) (U ×ˢ I) :=
    fun q hq ↦ ⟨hq.1, hq.2⟩
  refine ⟨h1.comp hc.continuousOn hm, fun t ht ↦ h2 (t + h) ht, ?_, ?_, fun p hp ↦ ?_, ?_,
    fun p hp ↦ ?_⟩
  · exact h3.comp (f := fun q : E d × ℝ ↦ (q.1, q.2 + h)) hc.continuousOn hm
  · exact h4.comp (f := fun q : E d × ℝ ↦ (q.1, q.2 + h)) hc.continuousOn hm
  · exact DifferentiableAt.comp (g := fun s ↦ u (p.1, s)) (f := fun s ↦ s + h) p.2 (h5 _ (hm hp))
      (differentiableAt_id.add_const h)
  · rw [dₜ_comp_add_time]
    exact h6.comp (f := fun q : E d × ℝ ↦ (q.1, q.2 + h)) hc.continuousOn hm
  · rw [dₜ_comp_add_time]
    exact h7 _ (hm hp)

/-- A constant `c` with `β_ε(c) = 0` is a classical solution. -/
theorem isSemilinearSolOn_const {c : ℝ} (hc : betaEps β ε c = 0) :
    IsSemilinearSolOn U Q β ε I (fun _ ↦ c) := by
  have hgrad : gradₓ (fun _ : E d × ℝ ↦ c) = fun _ ↦ 0 := by
    funext p; exact gradient_fun_const _ _
  have hdt : dₜ (fun _ : E d × ℝ ↦ c) = fun _ ↦ 0 := by
    funext p; exact deriv_const _ _
  have hlap : lapₓ (fun _ : E d × ℝ ↦ c) = fun _ ↦ 0 := by
    funext p; exact congrFun InnerProductSpace.laplacian_const p.1
  refine ⟨continuousOn_const, fun _ _ ↦ contDiffOn_const, by rw [hgrad]; exact continuousOn_const,
    ?_, fun _ _ ↦ differentiableAt_const _, by rw [hdt]; exact continuousOn_const, fun p _ ↦ ?_⟩
  · simp only [iteratedFDeriv_const_of_ne two_ne_zero]
    exact continuousOn_const
  · rw [hdt, hlap, hc]; ring

end Classical

/-! ### Stationary viscosity sub/supersolutions are parabolic ones -/

section Stationary

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {I : Set ℝ} {g : E d → ℝ}

/-- The time slice of a touching test function touches the stationary function. -/
theorem eventually_slice_of_parabolicPast {x : E d} {t : ℝ} (ht : t ∈ I)
    {P : E d × ℝ → Prop} (h : ∀ᶠ q in 𝓝[(U ×ˢ I) ∩ {q | q.2 ≤ t}] (x, t), P q) :
    ∀ᶠ y in 𝓝[U] x, P (y, t) := by
  have hT : Tendsto (fun y : E d ↦ (y, t)) (𝓝[U] x) (𝓝[(U ×ˢ I) ∩ {q | q.2 ≤ t}] (x, t)) :=
    (Continuous.prodMk_left t).continuousWithinAt.tendsto_nhdsWithin
      fun y hy ↦ ⟨⟨hy, ht⟩, show t ≤ t from le_rfl⟩
  exact hT.eventually h

/-- The time line through a touching point stays in the parabolic past. -/
theorem eventually_time_of_parabolicPast {x : E d} {t : ℝ} (hx : x ∈ U)
    (hI : ∃ δ > 0, Ioc (t - δ) t ⊆ I) {P : E d × ℝ → Prop}
    (h : ∀ᶠ q in 𝓝[(U ×ˢ I) ∩ {q | q.2 ≤ t}] (x, t), P q) :
    ∀ᶠ s in 𝓝[≤] t, P (x, s) := by
  obtain ⟨δ, hδ, hsub⟩ := hI
  have hT : Tendsto (fun s : ℝ ↦ (x, s)) (𝓝[≤] t) (𝓝[(U ×ˢ I) ∩ {q | q.2 ≤ t}] (x, t)) := by
    refine tendsto_nhdsWithin_iff.2
      ⟨((Continuous.prodMk_right x).tendsto t).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioc_mem_nhdsLE (show t - δ < t by linarith)] with s hs
    exact ⟨⟨hx, hsub hs⟩, hs.2⟩
  exact hT.eventually h

theorem contDiff_spaceSlice_two {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (t : ℝ) :
    ContDiff ℝ 2 (fun y : E d ↦ ψ (y, t)) :=
  hψ.comp (contDiff_id.prodMk contDiff_const)

theorem differentiableAt_timeLine {ψ : E d × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (x : E d)
    (t : ℝ) : DifferentiableAt ℝ (fun s : ℝ ↦ ψ (x, s)) t :=
  ((hψ.differentiable two_ne_zero).comp (differentiable_const x |>.prodMk differentiable_id)) t

/-- A stationary viscosity subsolution of `Δv = Q² β_ε(v)` in `U` is a (time-independent)
parabolic viscosity subsolution of `∂ₜu = Δu - Q² β_ε(u)` in `U × I`, provided every `t ∈ I` has
a left neighbourhood in `I`. -/
theorem IsSemilinearViscSubStat.isSemilinearViscSubOn (hg : IsSemilinearViscSubStat U Q β ε g)
    (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I) :
    IsSemilinearViscSubOn U Q β ε I (fun p ↦ g p.1) := by
  refine ⟨hg.1.comp continuousOn_fst fun p hp ↦ hp.1, fun ψ hψ p hp htouch ↦ ?_⟩
  obtain ⟨x, t⟩ := p
  obtain ⟨-, hpeq, hev⟩ := htouch
  have hlap : Q x ^ 2 * betaEps β ε (g x) ≤ lapₓ ψ (x, t) :=
    hg.2 _ (contDiff_spaceSlice_two hψ t) x hp.1
      ⟨hp.1, hpeq, eventually_slice_of_parabolicPast hp.2 hev⟩
  have hdt : dₜ ψ (x, t) ≤ 0 :=
    deriv_nonpos_of_eventually_le_left (differentiableAt_timeLine hψ x t)
      ((eventually_time_of_parabolicPast hp.1 (hI t hp.2) hev).mono fun s hs ↦ by
        simp only at hpeq hs ⊢; rw [hpeq]; exact hs)
  simp only
  linarith

/-- A stationary viscosity supersolution of `Δv = Q² β_ε(v)` in `U` is a (time-independent)
parabolic viscosity supersolution of `∂ₜu = Δu - Q² β_ε(u)` in `U × I`. -/
theorem IsSemilinearViscSuperStat.isSemilinearViscSuperOn
    (hg : IsSemilinearViscSuperStat U Q β ε g) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I) :
    IsSemilinearViscSuperOn U Q β ε I (fun p ↦ g p.1) := by
  refine ⟨hg.1.comp continuousOn_fst fun p hp ↦ hp.1, fun ψ hψ p hp htouch ↦ ?_⟩
  obtain ⟨x, t⟩ := p
  obtain ⟨-, hpeq, hev⟩ := htouch
  have hlap : lapₓ ψ (x, t) ≤ Q x ^ 2 * betaEps β ε (g x) :=
    hg.2 _ (contDiff_spaceSlice_two hψ t) x hp.1
      ⟨hp.1, hpeq, eventually_slice_of_parabolicPast hp.2 hev⟩
  have hdt : 0 ≤ dₜ ψ (x, t) :=
    deriv_nonneg_of_eventually_le_left (differentiableAt_timeLine hψ x t)
      ((eventually_time_of_parabolicPast hp.1 (hI t hp.2) hev).mono fun s hs ↦ by
        simp only at hpeq hs ⊢; rw [hpeq]; exact hs)
  simp only
  linarith

/-- A classical parabolic supersolution is a viscosity supersolution: if `U` is open, every
`t ∈ I` has a left neighbourhood in `I`, the time slices of `B` are `C²`, `B` is differentiable
in time, and `-Q² β_ε(B) ≤ ∂ₜB - ΔₓB` pointwise on `U × I`, then `B` is a parabolic viscosity
supersolution of `∂ₜu = Δu - Q² β_ε(u)` in `U × I`. -/
theorem isSemilinearViscSuperOn_of_classical {B : E d × ℝ → ℝ} (hU : IsOpen U)
    (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I) (hBc : ContinuousOn B (U ×ˢ I))
    (hBx : ∀ t, ContDiff ℝ 2 (fun y ↦ B (y, t)))
    (hBt : ∀ x t, DifferentiableAt ℝ (fun s ↦ B (x, s)) t)
    (hB : ∀ p ∈ U ×ˢ I, -(Q p.1 ^ 2 * betaEps β ε (B p)) ≤ dₜ B p - lapₓ B p) :
    IsSemilinearViscSuperOn U Q β ε I B := by
  refine ⟨hBc, fun ψ hψ p hp htouch ↦ ?_⟩
  obtain ⟨x, t⟩ := p
  obtain ⟨-, hpeq, hev⟩ := htouch
  have hlap : lapₓ ψ (x, t) ≤ lapₓ B (x, t) := by
    have hsl := eventually_slice_of_parabolicPast (U := U) hp.2 hev
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hp.1)] at hsl
    exact laplacian_le_of_eventually_le (contDiff_spaceSlice_two hψ t).contDiffAt (hBx t).contDiffAt
      hpeq hsl
  have hdt : dₜ B (x, t) ≤ dₜ ψ (x, t) := by
    have h := deriv_nonpos_of_eventually_le_left ((hBt x t).sub (differentiableAt_timeLine hψ x t))
      ((eventually_time_of_parabolicPast hp.1 (hI t hp.2) hev).mono fun s hs ↦ by
        simp only [Pi.sub_apply] at hpeq hs ⊢; rw [hpeq]; linarith)
    rw [deriv_sub (hBt x t) (differentiableAt_timeLine hψ x t)] at h
    simp only [dₜ]; linarith
  have := hB (x, t) hp
  linarith

/-- A classical parabolic subsolution is a viscosity subsolution (mirror of
`isSemilinearViscSuperOn_of_classical`). -/
theorem isSemilinearViscSubOn_of_classical {B : E d × ℝ → ℝ} (hU : IsOpen U)
    (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I) (hBc : ContinuousOn B (U ×ˢ I))
    (hBx : ∀ t, ContDiff ℝ 2 (fun y ↦ B (y, t)))
    (hBt : ∀ x t, DifferentiableAt ℝ (fun s ↦ B (x, s)) t)
    (hB : ∀ p ∈ U ×ˢ I, dₜ B p - lapₓ B p ≤ -(Q p.1 ^ 2 * betaEps β ε (B p))) :
    IsSemilinearViscSubOn U Q β ε I B := by
  refine ⟨hBc, fun ψ hψ p hp htouch ↦ ?_⟩
  obtain ⟨x, t⟩ := p
  obtain ⟨-, hpeq, hev⟩ := htouch
  have hlap : lapₓ B (x, t) ≤ lapₓ ψ (x, t) := by
    have hsl := eventually_slice_of_parabolicPast (U := U) hp.2 hev
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hp.1)] at hsl
    exact laplacian_le_of_eventually_le (hBx t).contDiffAt (contDiff_spaceSlice_two hψ t).contDiffAt
      hpeq.symm hsl
  have hdt : dₜ ψ (x, t) ≤ dₜ B (x, t) := by
    have h := deriv_nonpos_of_eventually_le_left
      ((differentiableAt_timeLine hψ x t).sub (hBt x t))
      ((eventually_time_of_parabolicPast hp.1 (hI t hp.2) hev).mono fun s hs ↦ by
        simp only [Pi.sub_apply] at hpeq hs ⊢; rw [hpeq]; linarith)
    rw [deriv_sub (differentiableAt_timeLine hψ x t) (hBt x t)] at h
    simp only [dₜ]; linarith
  have := hB (x, t) hp
  linarith

end Stationary

/-! ### Quadratic functions -/

section Quadratic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem hasFDerivAt_normSq_sub_const (x₀ y : F) :
    HasFDerivAt (fun y ↦ ‖y - x₀‖ ^ 2) ((2 : ℝ) • innerSL ℝ (y - x₀)) y := by
  convert ((hasFDerivAt_id y).sub_const x₀).norm_sq using 1
  ext v
  simp [two_smul]

/-- `Δ ‖y - x₀‖² = 2 dim F`. -/
theorem laplacian_normSq_sub_const (x₀ x : F) :
    Δ (fun y ↦ ‖y - x₀‖ ^ 2) x = 2 * Module.finrank ℝ F := by
  have hf : fderiv ℝ (fun y ↦ ‖y - x₀‖ ^ 2) = fun y ↦ (2 : ℝ) • innerSL ℝ (y - x₀) :=
    funext fun y ↦ (hasFDerivAt_normSq_sub_const x₀ y).fderiv
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

omit [FiniteDimensional ℝ F] in
theorem contDiff_normSq_sub_const (x₀ : F) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y ↦ ‖y - x₀‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)

/-- `Δ (a + b ‖y - x₀‖²) = 2 b dim F`. -/
theorem laplacian_const_add_mul_normSq (a b : ℝ) (x₀ x : F) :
    Δ (fun y ↦ a + b * ‖y - x₀‖ ^ 2) x = 2 * b * Module.finrank ℝ F := by
  have h := laplacian_comp (f := fun z ↦ a + b * z) (g := fun y ↦ ‖y - x₀‖ ^ 2) (x := x)
    (by fun_prop) (contDiff_normSq_sub_const x₀).contDiffAt
  have hd : deriv (fun z : ℝ ↦ a + b * z) = fun _ ↦ b := by
    funext z
    simp
  simp only [hd, deriv_const', zero_mul, zero_add, laplacian_normSq_sub_const] at h
  rw [h]; ring

end Quadratic

/-! ### Comparison consequences for solutions of (3.4) -/

/-- Points of the parabolic boundary lie over `V̄`. -/
theorem parBdry_fst_mem {V : Set (E d)} {a b : ℝ} {p : E d × ℝ} (hp : p ∈ parBdry V a b) :
    p.1 ∈ closure V := by
  rcases hp with ⟨hx, -⟩ | ⟨hx, -⟩
  exacts [hx, frontier_subset_closure hx]

namespace IsSemilinearSolution

variable {S : Setting d} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {u : E d × ℝ → ℝ}

/-- A solution of (3.4) is a viscosity subsolution in `U × (0, b]`. -/
theorem viscSubOn (hu : IsSemilinearSolution S.U S.Q β ε g u) (b : ℝ) :
    IsSemilinearViscSubOn S.U S.Q β ε (Ioc 0 b) u :=
  Registry.isSemilinearViscSubOn_of_solOn S.isOpen exists_Ioc_subset_Ioc
    (hu.2.1.mono Ioc_subset_Ioi_self)

/-- A solution of (3.4) is a viscosity supersolution in `U × (0, b]`. -/
theorem viscSuperOn (hu : IsSemilinearSolution S.U S.Q β ε g u) (b : ℝ) :
    IsSemilinearViscSuperOn S.U S.Q β ε (Ioc 0 b) u :=
  Registry.isSemilinearViscSuperOn_of_solOn S.isOpen exists_Ioc_subset_Ioc
    (hu.2.1.mono Ioc_subset_Ioi_self)

theorem continuousOn_Icc (hu : IsSemilinearSolution S.U S.Q β ε g u) (b : ℝ) :
    ContinuousOn u (closure S.U ×ˢ Icc 0 b) :=
  hu.1.mono (prod_mono subset_rfl Icc_subset_Ici_self)

/-- The parabolic boundary values of a solution are the data. -/
theorem eq_on_parBdry (hu : IsSemilinearSolution S.U S.Q β ε g u) {b : ℝ} {p : E d × ℝ}
    (hp : p ∈ parBdry S.U 0 b) : u p = g p.1 := by
  rcases hp with ⟨hx, ht⟩ | ⟨hx, ht⟩
  · rw [mem_singleton_iff] at ht
    obtain ⟨x, t⟩ := p
    simp only at ht hx ⊢
    rw [ht]; exact hu.2.2.1 x hx
  · exact hu.2.2.2 _ hx _ ht.1

/-- The time-independent extension of data continuous on `Ū`. -/
theorem continuousOn_const_time {g : E d → ℝ} (hg : ContinuousOn g (closure S.U)) (b : ℝ) :
    ContinuousOn (fun p : E d × ℝ ↦ g p.1) (closure S.U ×ˢ Icc 0 b) :=
  hg.comp continuousOn_fst fun _ hp ↦ hp.1

/-- First step of **Lemma A.1**: if the data `g` are a stationary viscosity
subsolution, then `g ≤ u` on `Ū × [0, ∞)`. -/
theorem le_of_viscSubStat (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) (hg : IsSemilinearViscSubStat S.U S.Q β ε g)
    (hgc : ContinuousOn g (closure S.U)) :
    ∀ p ∈ closure S.U ×ˢ Ici 0, g p.1 ≤ u p := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  have hb : (0 : ℝ) < t + 1 := by simp only [mem_Ici] at ht; linarith
  refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
    (continuousOn_const_time hgc _) (hu.continuousOn_Icc _)
    (hg.isSemilinearViscSubOn exists_Ioc_subset_Ioc) (hu.viscSuperOn _)
    (fun p hp ↦ (hu.eq_on_parBdry hp).ge) (x, t) ⟨hx, ht, by simp⟩

/-- Supersolution version of `le_of_viscSubStat`: `u ≤ g` on `Ū × [0, ∞)`. -/
theorem le_of_viscSuperStat (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) (hg : IsSemilinearViscSuperStat S.U S.Q β ε g)
    (hgc : ContinuousOn g (closure S.U)) :
    ∀ p ∈ closure S.U ×ˢ Ici 0, u p ≤ g p.1 := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  have hb : (0 : ℝ) < t + 1 := by simp only [mem_Ici] at ht; linarith
  refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
    (hu.continuousOn_Icc _) (continuousOn_const_time hgc _)
    (hu.viscSubOn _) (hg.isSemilinearViscSuperOn exists_Ioc_subset_Ioc)
    (fun p hp ↦ (hu.eq_on_parBdry hp).le) (x, t) ⟨hx, ht, by simp⟩

/-- The time translate by `h ≥ 0` of a solution, on `U × (0, b]`. -/
theorem shift_facts (hu : IsSemilinearSolution S.U S.Q β ε g u) {h : ℝ} (hh : 0 ≤ h)
    (b : ℝ) :
    ContinuousOn (fun q : E d × ℝ ↦ u (q.1, q.2 + h)) (closure S.U ×ˢ Icc 0 b) ∧
    IsSemilinearViscSubOn S.U S.Q β ε (Ioc 0 b) (fun q ↦ u (q.1, q.2 + h)) ∧
    IsSemilinearViscSuperOn S.U S.Q β ε (Ioc 0 b) (fun q ↦ u (q.1, q.2 + h)) := by
  have hsol : IsSemilinearSolOn S.U S.Q β ε (Ioc 0 b) (fun q ↦ u (q.1, q.2 + h)) :=
    (hu.2.1.comp_add_time h).mono fun t ht ↦ by
      simp only [mem_preimage, mem_Ioi]; linarith [ht.1]
  refine ⟨hu.1.comp (by fun_prop : Continuous fun q : E d × ℝ ↦ (q.1, q.2 + h)).continuousOn
    fun q hq ↦ ⟨hq.1, by simp only [mem_Ici]; linarith [hq.2.1]⟩, ?_, ?_⟩
  · exact Registry.isSemilinearViscSubOn_of_solOn S.isOpen exists_Ioc_subset_Ioc hsol
  · exact Registry.isSemilinearViscSuperOn_of_solOn S.isOpen exists_Ioc_subset_Ioc hsol

/-- **Lemma A.1**, increasing case: if `g ≤ u` on `Ū × [0, ∞)` (e.g.
by `le_of_viscSubStat`), then `t ↦ u(x, t)` is nondecreasing on `[0, ∞)` for every `x ∈ Ū`.
Comparison of `u` with the translate `u(·, · + h)`. -/
theorem monotoneInTime (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u)
    (hle : ∀ p ∈ closure S.U ×ˢ Ici 0, g p.1 ≤ u p) :
    MonotoneInTime u (closure S.U) (Ici 0) := by
  intro x hx s hs t ht hst
  simp only [mem_Ici] at hs ht
  have hh : 0 ≤ t - s := sub_nonneg.2 hst
  have hb : (0 : ℝ) < s + 1 := by linarith
  obtain ⟨hc, -, hsuper⟩ := shift_facts hu hh (s + 1)
  have key := Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
    (hu.continuousOn_Icc _) hc (hu.viscSubOn _) hsuper ?_ (x, s)
    ⟨hx, hs, by linarith⟩
  · simpa using key
  · intro p hp
    rw [hu.eq_on_parBdry hp]
    rcases hp with ⟨hx', ht'⟩ | ⟨hx', ht'⟩
    · rw [mem_singleton_iff] at ht'
      simp only [ht', zero_add]
      exact hle (p.1, t - s) ⟨hx', hh⟩
    · exact (hu.2.2.2 _ hx' _ (by linarith [ht'.1])).ge

/-- **Lemma A.1**, decreasing case: if `u ≤ g` on `Ū × [0, ∞)` (e.g. by `le_of_viscSuperStat`),
then `t ↦ u(x, t)` is nonincreasing on `[0, ∞)` for every `x ∈ Ū`. -/
theorem antitoneInTime (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u)
    (hle : ∀ p ∈ closure S.U ×ˢ Ici 0, u p ≤ g p.1) :
    AntitoneInTime u (closure S.U) (Ici 0) := by
  intro x hx s hs t ht hst
  simp only [mem_Ici] at hs ht
  have hh : 0 ≤ t - s := sub_nonneg.2 hst
  have hb : (0 : ℝ) < s + 1 := by linarith
  obtain ⟨hc, hsub, -⟩ := shift_facts hu hh (s + 1)
  have key := Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
    hc (hu.continuousOn_Icc _) hsub (hu.viscSuperOn _) ?_ (x, s)
    ⟨hx, hs, by linarith⟩
  · simpa using key
  · intro p hp
    rw [hu.eq_on_parBdry hp]
    rcases hp with ⟨hx', ht'⟩ | ⟨hx', ht'⟩
    · rw [mem_singleton_iff] at ht'
      simp only [ht', zero_add]
      exact hle (p.1, t - s) ⟨hx', hh⟩
    · exact (hu.2.2.2 _ hx' _ (by linarith [ht'.1])).le

/-- `L^∞` bounds by comparison with constant solutions: if `m ≤ g ≤ M` on `Ū` and
`β_ε(m) = β_ε(M) = 0`, then `m ≤ u ≤ M` on `Ū × [0, ∞)`. -/
theorem mem_Icc (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {m M : ℝ} (hm : betaEps β ε m = 0)
    (hM : betaEps β ε M = 0) (hg : ∀ x ∈ closure S.U, m ≤ g x ∧ g x ≤ M) :
    ∀ p ∈ closure S.U ×ˢ Ici 0, m ≤ u p ∧ u p ≤ M := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  have hb : (0 : ℝ) < t + 1 := by simp only [mem_Ici] at ht; linarith
  have hpt : (x, t) ∈ closure S.U ×ˢ Icc 0 (t + 1) := ⟨hx, ht, by simp⟩
  have hI := exists_Ioc_subset_Ioc (a := 0) (b := t + 1)
  constructor
  · refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
      continuousOn_const (hu.continuousOn_Icc _)
      (Registry.isSemilinearViscSubOn_of_solOn S.isOpen hI (isSemilinearSolOn_const hm))
      (hu.viscSuperOn _) (fun p hp ↦ ?_) _ hpt
    rw [hu.eq_on_parBdry hp]
    exact (hg p.1 (parBdry_fst_mem hp)).1
  · refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
      (hu.continuousOn_Icc _) continuousOn_const (hu.viscSubOn _)
      (Registry.isSemilinearViscSuperOn_of_solOn S.isOpen hI (isSemilinearSolOn_const hM))
      (fun p hp ↦ ?_) _ hpt
    rw [hu.eq_on_parBdry hp]
    exact (hg p.1 (parBdry_fst_mem hp)).2

/-- **Upper bound from the initial/boundary data** (heat barrier): if `g` is `L`-Lipschitz on `Ū`,
then for every `σ > 0`, `y ∈ Ū` and `t ≥ 0`,
`u(y, t) ≤ g(y) + σ + 2 d A t` with `A = L²/(4σ)`. Comparison with the caloric function
`g(y) + σ + A|x - y|² + 2 d A t`, which is a supersolution since `β_ε ≥ 0`. -/
theorem le_add_of_lipschitzOnWith (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {L : ℝ≥0}
    (hg : LipschitzOnWith L g (closure S.U)) {σ : ℝ} (hσ : 0 < σ) :
    ∀ y ∈ closure S.U, ∀ t, 0 ≤ t →
      u (y, t) ≤ g y + σ + 2 * d * ((L : ℝ) ^ 2 / (4 * σ)) * t := by
  intro y hy t ht
  set A := (L : ℝ) ^ 2 / (4 * σ) with hA
  have hA0 : 0 ≤ A := by positivity
  set B : E d × ℝ → ℝ := fun q ↦ (g y + σ + 2 * d * A * q.2) + A * ‖q.1 - y‖ ^ 2 with hB
  have hBc : Continuous B := by rw [hB]; fun_prop
  have hb : (0 : ℝ) < t + 1 := by linarith
  have hsuper : IsSemilinearViscSuperOn S.U S.Q β ε (Ioc 0 (t + 1)) B := by
    refine isSemilinearViscSuperOn_of_classical S.isOpen exists_Ioc_subset_Ioc hBc.continuousOn
      (fun s ↦ by
        simp only [hB]; exact contDiff_const.add (contDiff_const.mul (contDiff_normSq_sub_const y)))
      (fun x s ↦ by simp only [hB]; fun_prop) fun p _ ↦ ?_
    have hdt : dₜ B p = 2 * d * A := by
      simp only [dₜ, hB]
      simp
    have hlap : lapₓ B p = 2 * d * A := by
      simp only [lapₓ, hB]
      rw [laplacian_const_add_mul_normSq, finrank_euclideanSpace_fin]; ring
    have h1 := hβ.betaEps_nonneg ε (B p) hε.le
    rw [hdt, hlap, sub_self, neg_nonpos]
    positivity
  have key := Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
    (hu.continuousOn_Icc _) hBc.continuousOn (hu.viscSubOn _) hsuper ?_ (y, t)
    ⟨hy, ht, by linarith⟩
  · refine key.trans (le_of_eq ?_)
    simp only [hB, sub_self, norm_zero]; ring
  · intro p hp
    rw [hu.eq_on_parBdry hp]
    have hx := parBdry_fst_mem hp
    have ht0 : 0 ≤ p.2 := by
      rcases hp with ⟨-, h⟩ | ⟨-, h⟩
      · rw [mem_singleton_iff] at h; rw [h]
      · exact h.1
    have hlip : g p.1 ≤ g y + L * ‖p.1 - y‖ := by
      have := hg.dist_le_mul p.1 hx y hy
      rw [Real.dist_eq, dist_eq_norm] at this
      linarith [le_abs_self (g p.1 - g y)]
    have hamgm : (L : ℝ) * ‖p.1 - y‖ ≤ σ + A * ‖p.1 - y‖ ^ 2 := by
      have e : σ + A * ‖p.1 - y‖ ^ 2 - L * ‖p.1 - y‖ = (2 * σ - L * ‖p.1 - y‖) ^ 2 / (4 * σ) := by
        rw [hA]; field_simp; ring
      have : 0 ≤ (2 * σ - L * ‖p.1 - y‖) ^ 2 / (4 * σ) := by positivity
      linarith
    have h3 : 0 ≤ 2 * d * A * p.2 := by positivity
    simp only [hB]
    linarith

/-- Comparison with a (time-dependent) viscosity supersolution `B` of the equation in `U_∞`
lying above the data on the parabolic boundary: `u ≤ B` on `Ū × [0, ∞)`. -/
theorem le_of_super (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {B : E d × ℝ → ℝ}
    (hBc : ContinuousOn B (closure S.U ×ˢ Ici 0))
    (hB : ∀ T > 0, IsSemilinearViscSuperOn S.U S.Q β ε (Ioc 0 T) B)
    (hbd : ∀ x ∈ closure S.U, ∀ s, 0 ≤ s → (s = 0 ∨ x ∈ frontier S.U) → g x ≤ B (x, s)) :
    ∀ x ∈ closure S.U, ∀ t, 0 ≤ t → u (x, t) ≤ B (x, t) := by
  intro x hx t ht
  have hb : (0 : ℝ) < t + 1 := by linarith
  refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
    (hu.continuousOn_Icc _) (hBc.mono (prod_mono subset_rfl Icc_subset_Ici_self))
    (hu.viscSubOn _) (hB _ hb) (fun p hp ↦ ?_) (x, t) ⟨hx, ht, by simp⟩
  rw [hu.eq_on_parBdry hp]
  rcases hp with ⟨hx', hs⟩ | ⟨hx', hs⟩
  · rw [mem_singleton_iff] at hs
    exact hbd p.1 hx' p.2 hs.ge (Or.inl hs)
  · exact hbd p.1 (frontier_subset_closure hx') p.2 hs.1 (Or.inr hx')

/-- Comparison with a (time-dependent) viscosity subsolution `B` of the equation in `U_∞`
lying below the data on the parabolic boundary: `B ≤ u` on `Ū × [0, ∞)`. -/
theorem ge_of_sub (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {B : E d × ℝ → ℝ}
    (hBc : ContinuousOn B (closure S.U ×ˢ Ici 0))
    (hB : ∀ T > 0, IsSemilinearViscSubOn S.U S.Q β ε (Ioc 0 T) B)
    (hbd : ∀ x ∈ closure S.U, ∀ s, 0 ≤ s → (s = 0 ∨ x ∈ frontier S.U) → B (x, s) ≤ g x) :
    ∀ x ∈ closure S.U, ∀ t, 0 ≤ t → B (x, t) ≤ u (x, t) := by
  intro x hx t ht
  have hb : (0 : ℝ) < t + 1 := by linarith
  refine Registry.semilinear_comparison S.isOpen S.isBounded hb S.lip hβ hε
    (hBc.mono (prod_mono subset_rfl Icc_subset_Ici_self)) (hu.continuousOn_Icc _)
    (hB _ hb) (hu.viscSuperOn _) (fun p hp ↦ ?_) (x, t) ⟨hx, ht, by simp⟩
  rw [hu.eq_on_parBdry hp]
  rcases hp with ⟨hx', hs⟩ | ⟨hx', hs⟩
  · rw [mem_singleton_iff] at hs
    exact hbd p.1 hx' p.2 hs.ge (Or.inl hs)
  · exact hbd p.1 (frontier_subset_closure hx') p.2 hs.1 (Or.inr hx')

/-- `0 ≤ u ≤ max M 1` for data `0 ≤ g ≤ M` and `ε ≤ 1` (comparison with constants). -/
theorem nonneg_le_max (hβ : IsReactionProfile β) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : IsSemilinearSolution S.U S.Q β ε g u) {M : ℝ}
    (hg : ∀ x ∈ closure S.U, 0 ≤ g x ∧ g x ≤ M) :
    ∀ p ∈ closure S.U ×ˢ Ici 0, 0 ≤ u p ∧ u p ≤ max M 1 := by
  have hM : betaEps β ε (max M 1) = 0 := by
    rw [betaEps, hβ.eq_zero_of_one_le, zero_div]
    rw [le_div_iff₀ hε, one_mul]
    exact hε1.trans (le_max_right _ _)
  exact hu.mem_Icc hβ hε (hβ.betaEps_zero ε) hM fun x hx ↦
    ⟨(hg x hx).1, (hg x hx).2.trans (le_max_left _ _)⟩

end IsSemilinearSolution

end PerronVariational

end
