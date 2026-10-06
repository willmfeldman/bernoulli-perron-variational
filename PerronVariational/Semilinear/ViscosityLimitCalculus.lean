/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.ProfileSuper
public import PerronVariational.Registry.Semilinear
public import PerronVariational.Semilinear.Profiles
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Parabolic.StatToPara
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.WellPrepared

/-!
# Space-time calculus for the semilinear limit (Proposition 5.3)

Tools for the proof of Proposition 5.3 of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981:

* derivatives of time and space slices of a `C²` space-time function, and continuity of
  `∂ₜφ`, `∇ₓφ`, `Δₓφ` (`continuous_dₜ`, `continuous_gradₓ`, `continuous_lapₓ`);
* the parabolic chain rule for `f ∘ φ` (`dₜ_comp`, `lapₓ_comp`): `∂ₜ` picks up `f'(φ) ∂ₜφ`;
* touching comparison relative to the parabolic past (`touch_compare`), and the passage from
  local classical inequalities to the semilinear viscosity notions of `Registry/Semilinear`
  (`isSemilinearViscSubOn_of_local`, `isSemilinearViscSuperOn_of_local`);
* the pointwise profile inequalities behind the parabolic versions of Lemma A.4:
  `profileSuperEps_ineq` (for `Ψ_{ε,θ̂}`, including the exponential tail case) and
  `profileSubEps_ineq` (for `Φ_{ε,θ}`).
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Slices of space-time functions -/

section Slices

variable {φ : E d × ℝ → ℝ} {p : E d × ℝ}

theorem hasDerivAt_timeSlice (hφ : DifferentiableAt ℝ φ p) :
    HasDerivAt (fun s ↦ φ (p.1, s)) (fderiv ℝ φ p ((0 : E d), (1 : ℝ))) p.2 := by
  have h : HasDerivAt (fun s : ℝ ↦ (p.1, s)) ((0 : E d), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact hφ.hasFDerivAt.comp_hasDerivAt p.2 h

theorem dₜ_eq_fderiv (hφ : DifferentiableAt ℝ φ p) :
    dₜ φ p = fderiv ℝ φ p ((0 : E d), (1 : ℝ)) :=
  (hasDerivAt_timeSlice hφ).deriv

theorem hasFDerivAt_spaceSlice (hφ : DifferentiableAt ℝ φ p) :
    HasFDerivAt (fun y ↦ φ (y, p.2)) ((fderiv ℝ φ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ))
      p.1 := by
  have h : HasFDerivAt (fun y : E d ↦ (y, p.2)) (ContinuousLinearMap.inl ℝ (E d) ℝ) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  exact hφ.hasFDerivAt.comp p.1 h

theorem gradₓ_eq_fderiv (hφ : DifferentiableAt ℝ φ p) :
    gradₓ φ p = (InnerProductSpace.toDual ℝ (E d)).symm
      ((fderiv ℝ φ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) := by
  rw [gradₓ, gradient, (hasFDerivAt_spaceSlice hφ).fderiv]

theorem continuous_dₜ (hφ : ContDiff ℝ 1 φ) : Continuous (dₜ φ) := by
  have h : dₜ φ = fun p ↦ fderiv ℝ φ p ((0 : E d), (1 : ℝ)) :=
    funext fun p ↦ dₜ_eq_fderiv (hφ.differentiable one_ne_zero p)
  rw [h]
  exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_gradₓ (hφ : ContDiff ℝ 1 φ) : Continuous (gradₓ φ) := by
  have h : gradₓ φ = fun p ↦ (InnerProductSpace.toDual ℝ (E d)).symm
      ((fderiv ℝ φ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) :=
    funext fun p ↦ gradₓ_eq_fderiv (hφ.differentiable one_ne_zero p)
  rw [h]
  exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp
    ((hφ.continuous_fderiv one_ne_zero).clm_comp continuous_const)

theorem contDiff_spaceSlice {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) (t : ℝ) :
    ContDiff ℝ n (fun y : E d ↦ φ (y, t)) :=
  hφ.comp (contDiff_id.prodMk contDiff_const)

theorem contDiff_timeSlice {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) (x : E d) :
    ContDiff ℝ n (fun s : ℝ ↦ φ (x, s)) :=
  hφ.comp (contDiff_const.prodMk contDiff_id)

/-- The second derivative of a space slice, through the joint second derivative. -/
theorem iteratedFDeriv_two_spaceSlice (hφ : ContDiff ℝ 2 φ) (y v : E d) (t : ℝ) :
    iteratedFDeriv ℝ 2 (fun z : E d ↦ φ (z, t)) y ![v, v] =
      iteratedFDeriv ℝ 2 φ (y, t) ![(v, 0), (v, 0)] := by
  set f' : E d × ℝ → ℝ := fun z ↦ φ (z + ((0 : E d), t)) with hf'
  have hf'c : ContDiff ℝ 2 f' := hφ.comp (contDiff_id.add contDiff_const)
  have hcomp : (fun z : E d ↦ φ (z, t)) = f' ∘ (ContinuousLinearMap.inl ℝ (E d) ℝ) := by
    funext z; simp [hf']
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf'c _ le_rfl, hf',
    iteratedFDeriv_comp_add_right]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem lapₓ_eq_sum (hφ : ContDiff ℝ 2 φ) (p : E d × ℝ) :
    lapₓ φ p = ∑ i, iteratedFDeriv ℝ 2 φ p
      ![(stdOrthonormalBasis ℝ (E d) i, 0), (stdOrthonormalBasis ℝ (E d) i, 0)] := by
  rw [lapₓ, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact iteratedFDeriv_two_spaceSlice hφ p.1 _ p.2

theorem continuous_lapₓ (hφ : ContDiff ℝ 2 φ) : Continuous (lapₓ φ) := by
  have h : lapₓ φ = fun p ↦ ∑ i, iteratedFDeriv ℝ 2 φ p
      ![(stdOrthonormalBasis ℝ (E d) i, 0), (stdOrthonormalBasis ℝ (E d) i, 0)] :=
    funext (lapₓ_eq_sum hφ)
  rw [h]
  exact continuous_finsetSum _ fun i _ ↦ (hφ.continuous_iteratedFDeriv le_rfl).eval_const _

/-- **Parabolic chain rule, time part**: `∂ₜ(f ∘ φ) = f'(φ) ∂ₜφ`. -/
theorem dₜ_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hφ : DifferentiableAt ℝ φ p) :
    dₜ (fun q ↦ f (φ q)) p = deriv f (φ p) * dₜ φ p := by
  have h := (hf (φ p)).hasDerivAt.comp p.2 (hasDerivAt_timeSlice hφ)
  change deriv (f ∘ fun s ↦ φ (p.1, s)) p.2 = _
  rw [h.deriv, dₜ_eq_fderiv hφ]

/-- **Parabolic chain rule, space part** (from `laplacian_comp`):
`Δₓ(f ∘ φ) = f''(φ)|∇ₓφ|² + f'(φ) Δₓφ`. -/
theorem lapₓ_comp {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ) :
    lapₓ (fun q ↦ f (φ q)) p =
      deriv (deriv f) (φ p) * ‖gradₓ φ p‖ ^ 2 + deriv f (φ p) * lapₓ φ p :=
  laplacian_comp hf.contDiffAt (contDiff_spaceSlice hφ p.2).contDiffAt

/-- The heat operator of a composition: `(∂ₜ - Δₓ)(f ∘ φ) = -(f''(φ)|∇ₓφ|² + f'(φ)(Δₓφ - ∂ₜφ))`. -/
theorem heat_comp {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ) :
    dₜ (fun q ↦ f (φ q)) p - lapₓ (fun q ↦ f (φ q)) p =
      -(deriv (deriv f) (φ p) * ‖gradₓ φ p‖ ^ 2 + deriv f (φ p) * (lapₓ φ p - dₜ φ p)) := by
  rw [dₜ_comp (hf.differentiable (by norm_num)) (hφ.differentiable (by norm_num) p),
    lapₓ_comp hf hφ]
  ring

end Slices

/-! ### Touching relative to the parabolic past -/

section Touching

variable {F G : E d × ℝ → ℝ} {p : E d × ℝ} {S : Set (E d × ℝ)}

/-- **Touching comparison relative to the parabolic past.** Let `S` contain a spatial
neighbourhood of `p` at time `p.2` and a left time-neighbourhood of `p`. If `F ≤ G` near `p`
in `S` with `F p = G p` (both `C²`), then `Δₓ F(p) ≤ Δₓ G(p)` and `∂ₜ G(p) ≤ ∂ₜ F(p)`. -/
theorem touch_compare (hS : ∀ᶠ y in 𝓝 p.1, (y, p.2) ∈ S)
    (hSt : ∀ᶠ s in 𝓝[<] p.2, (p.1, s) ∈ S) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (heq : F p = G p) (hle : ∀ᶠ q in 𝓝[S] p, F q ≤ G q) :
    lapₓ F p ≤ lapₓ G p ∧ dₜ G p ≤ dₜ F p := by
  constructor
  · -- space
    have hy : Tendsto (fun y : E d ↦ (y, p.2)) (𝓝 p.1) (𝓝[S] p) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hS⟩
      have : Continuous (fun y : E d ↦ (y, p.2)) := continuous_id.prodMk continuous_const
      simpa using this.tendsto p.1
    exact laplacian_le_of_eventually_le (contDiff_spaceSlice hF p.2).contDiffAt
      (contDiff_spaceSlice hG p.2).contDiffAt heq (hy.eventually hle)
  · -- time
    have hs : Tendsto (fun s : ℝ ↦ (p.1, s)) (𝓝[<] p.2) (𝓝[S] p) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hSt⟩
      have : Continuous (fun s : ℝ ↦ (p.1, s)) := continuous_const.prodMk continuous_id
      exact (this.tendsto p.2).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ s in 𝓝[<] p.2, F (p.1, s) ≤ G (p.1, s) := hs.eventually hle
    obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hev
    have hGd := ((contDiff_timeSlice hG p.1).differentiable (by norm_num) p.2).hasDerivAt
    have hFd := ((contDiff_timeSlice hF p.1).differentiable (by norm_num) p.2).hasDerivAt
    have hdiff : DifferentiableAt ℝ (fun s ↦ G (p.1, s) - F (p.1, s)) p.2 :=
      (hGd.sub hFd).differentiableAt
    have h := deriv_nonpos_of_le_left hdiff ha fun t ht ↦ by
      have := hsub ht
      simp only [Set.mem_ofPred_eq] at this
      change G (p.1, p.2) - F (p.1, p.2) ≤ G (p.1, t) - F (p.1, t)
      have : G (p.1, p.2) = F (p.1, p.2) := heq.symm
      linarith [hsub ht]
    have h2 : deriv (fun s ↦ G (p.1, s) - F (p.1, s)) p.2 =
        deriv (fun s ↦ G (p.1, s)) p.2 - deriv (fun s ↦ F (p.1, s)) p.2 := (hGd.sub hFd).deriv
    rw [h2] at h
    rw [dₜ, dₜ]
    linarith

variable {V : Set (E d)} {I : Set ℝ} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {w : E d × ℝ → ℝ}

/-- The parabolic past `(V × I) ∩ {s ≤ t}` contains the spatial and left time neighbourhoods
required by `touch_compare`. -/
theorem past_nhds (hV : IsOpen V) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hp : p ∈ V ×ˢ I) :
    (∀ᶠ y in 𝓝 p.1, (y, p.2) ∈ (V ×ˢ I) ∩ {q | q.2 ≤ p.2}) ∧
      ∀ᶠ s in 𝓝[<] p.2, (p.1, s) ∈ (V ×ˢ I) ∩ {q | q.2 ≤ p.2} := by
  constructor
  · filter_upwards [hV.mem_nhds hp.1] with y hy using ⟨⟨hy, hp.2⟩, show p.2 ≤ p.2 from le_rfl⟩
  · obtain ⟨δ, hδ, hsub⟩ := hI p.2 hp.2
    filter_upwards [Ioo_mem_nhdsLT (show p.2 - δ < p.2 by linarith)] with s hs
    exact ⟨⟨hp.1, hsub ⟨hs.1, hs.2.le⟩⟩, hs.2.le⟩

/-- **Local classical subsolutions are viscosity subsolutions.** If at every `p ∈ V × I` there is
a `C²` function `F ≤ w` near `p`, `F p = w p`, with `∂ₜF - ΔₓF ≤ -Q² β_ε(w)` at `p`, then `w` is a
viscosity subsolution of the semilinear equation in `V × I`. (Covers both `w = F` near `p` and
the case `w(p) = 0 ≤ w`, with `F = 0`.) -/
theorem isSemilinearViscSubOn_of_local (hV : IsOpen V) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hw : ContinuousOn w (V ×ˢ I))
    (hloc : ∀ p ∈ V ×ˢ I, ∃ F : E d × ℝ → ℝ, ContDiff ℝ 2 F ∧ F p = w p ∧
      (∀ᶠ q in 𝓝 p, F q ≤ w q) ∧ dₜ F p - lapₓ F p ≤ -(Q p.1 ^ 2 * betaEps β ε (w p))) :
    IsSemilinearViscSubOn V Q β ε I w := by
  refine ⟨hw, fun ψ hψ p hp htouch ↦ ?_⟩
  obtain ⟨-, hψp, hle⟩ := htouch
  obtain ⟨F, hF, hFp, hFle, hFineq⟩ := hloc p hp
  obtain ⟨hS, hSt⟩ := past_nhds hV hI hp
  have hle' : ∀ᶠ q in 𝓝[(V ×ˢ I) ∩ {q | q.2 ≤ p.2}] p, F q ≤ ψ q := by
    filter_upwards [hle, nhdsWithin_le_nhds hFle] with q h1 h2 using h2.trans h1
  obtain ⟨h1, h2⟩ := touch_compare hS hSt hF hψ (hFp.trans hψp.symm) hle'
  linarith

/-- **Local classical supersolutions are viscosity supersolutions** (dual of
`isSemilinearViscSubOn_of_local`). -/
theorem isSemilinearViscSuperOn_of_local (hV : IsOpen V)
    (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I) (hw : ContinuousOn w (V ×ˢ I))
    (hloc : ∀ p ∈ V ×ˢ I, ∃ F : E d × ℝ → ℝ, ContDiff ℝ 2 F ∧ F p = w p ∧
      (∀ᶠ q in 𝓝 p, w q ≤ F q) ∧ -(Q p.1 ^ 2 * betaEps β ε (w p)) ≤ dₜ F p - lapₓ F p) :
    IsSemilinearViscSuperOn V Q β ε I w := by
  refine ⟨hw, fun ψ hψ p hp htouch ↦ ?_⟩
  obtain ⟨-, hψp, hle⟩ := htouch
  obtain ⟨F, hF, hFp, hFle, hFineq⟩ := hloc p hp
  obtain ⟨hS, hSt⟩ := past_nhds hV hI hp
  have hle' : ∀ᶠ q in 𝓝[(V ×ˢ I) ∩ {q | q.2 ≤ p.2}] p, ψ q ≤ F q := by
    filter_upwards [hle, nhdsWithin_le_nhds hFle] with q h1 h2 using h1.trans h2
  obtain ⟨h1, h2⟩ := touch_compare hS hSt hψ hF (hψp.trans hFp.symm) hle'
  linarith

/-- A classical `C^{2,1}` solution restricted to a smaller open cylinder is still a solution. -/
theorem IsSemilinearSolOn.mono_domain {U : Set (E d)} {J : Set ℝ} {u : E d × ℝ → ℝ}
    (h : IsSemilinearSolOn U Q β ε I u) (hVU : V ⊆ U) (hJI : J ⊆ I) :
    IsSemilinearSolOn V Q β ε J u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hsub : V ×ˢ J ⊆ U ×ˢ I := prod_mono hVU hJI
  exact ⟨h1.mono hsub, fun t ht ↦ (h2 t (hJI ht)).mono hVU, h3.mono hsub, h4.mono hsub,
    fun p hp ↦ h5 p (hsub hp), h6.mono hsub, fun p hp ↦ h7 p (hsub hp)⟩

end Touching

/-! ### Pointwise profile inequalities -/

section Profiles

variable {β : ℝ → ℝ}

/-- **Pointwise form of the supersolution computation of Lemma A.4** (its proof), with the
Laplacian term `Lap` a free parameter (in the parabolic application `Lap = Δₓψ - ∂ₜψ`).
Given `a₀ > 0`, `θ̂ > 1`, `Q_min > 0` and bounds `Gmax`, `D`, there is `ε₀ > 0` such that for
`ε ∈ (0, ε₀]`: if `Lap ≤ 0` where `s > -a₀`, `θ̂ G ≤ q²` where `|s| ≤ a₀`, `0 ≤ G ≤ Gmax`,
`|Lap| ≤ D` and `Q_min ≤ q`, then `Ψ_ε''(s) G + Ψ_ε'(s) Lap ≤ q² β_ε(Ψ_ε(s))`. -/
theorem profileSuperEps_ineq (hβ : IsReactionProfile β) {a₀ θh Qmin Gmax D : ℝ} (ha₀ : 0 < a₀)
    (hθh : 1 < θh) (hQmin : 0 < Qmin) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, ∀ s G Lap q : ℝ, (-a₀ < s → Lap ≤ 0) →
      (|s| ≤ a₀ → θh * G ≤ q ^ 2) → 0 ≤ G → G ≤ Gmax → |Lap| ≤ D → Qmin ≤ q →
      deriv (deriv (profileSuperEps β θh ε)) s * G + deriv (profileSuperEps β θh ε) s * Lap ≤
        q ^ 2 * betaEps β ε (profileSuperEps β θh ε s) := by
  set κ := superKappa β θh with hκ_def
  have hκ0 : 0 < κ := superKappa_pos hβ hθh
  have hκ1 : κ < 1 := superKappa_lt_one hβ hθh
  obtain ⟨C, c, hc0, -, hC1, htail⟩ := profileSuper_tail hβ hθh
  obtain ⟨b, hb0, hb⟩ := hβ.exists_pos_le hκ0 (show (1 + κ) / 2 < 1 by linarith)
  set A := |Gmax| + |D| with hA_def
  have hA : 0 ≤ A := by positivity
  have hC0 : 0 < C := by linarith
  set ε₀ := min (min a₀ 1) (min (c * a₀ * (1 - κ) / (2 * C))
    (c * a₀ * (Qmin ^ 2 * b) / (C * A + 1))) with hε₀_def
  have hε₀ : 0 < ε₀ := by
    refine lt_min (lt_min ha₀ one_pos) (lt_min ?_ ?_)
    · exact div_pos (mul_pos (mul_pos hc0 ha₀) (by linarith)) (by linarith)
    · exact div_pos (mul_pos (mul_pos hc0 ha₀) (by positivity)) (by positivity)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε s G Lap q hLap hGq hG0 hGmax hD hq
  obtain ⟨hε0, hεle⟩ := hε
  have hεa : ε ≤ a₀ := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε2 : ε ≤ c * a₀ * (1 - κ) / (2 * C) :=
    hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε ≤ c * a₀ * (Qmin ^ 2 * b) / (C * A + 1) :=
    hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
  set Ex := C * Real.exp (-(c * a₀ / ε)) with hEx_def
  have hE0 : 0 ≤ Ex := by positivity
  have hca : 0 < c * a₀ := mul_pos hc0 ha₀
  have hEle : Ex ≤ C * ε / (c * a₀) := by
    calc Ex ≤ C * (ε / (c * a₀)) :=
          mul_le_mul_of_nonneg_left (exp_neg_div_le hc0 ha₀ hε0) hC0.le
      _ = C * ε / (c * a₀) := by ring
  have hE1 : Ex ≤ (1 - κ) / 2 := by
    refine hEle.trans ?_
    rw [div_le_div_iff₀ hca two_pos]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)).1 hε2
    linarith
  have hE2 : Ex * A ≤ Qmin ^ 2 * b := by
    have h1 : Ex * A ≤ C * ε / (c * a₀) * A := mul_le_mul_of_nonneg_right hEle hA
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < C * A + 1)).1 hε3
    have h3 : C * ε / (c * a₀) * A ≤ Qmin ^ 2 * b := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hca]
      linarith
    linarith
  obtain ⟨hP2a, hP2b⟩ := profileSuperEps_deriv_deriv_mem hβ hθh hε0 s
  have hP1 := profileSuperEps_deriv_mem hβ hθh hε0 s
  have hq0 : 0 < q := hQmin.trans_le hq
  have hQ2 : 0 ≤ q ^ 2 := sq_nonneg _
  rcases lt_or_ge (-a₀) s with hsa | hsa
  · have hterm2 : deriv (profileSuperEps β θh ε) s * Lap ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hP1.1.le (hLap hsa)
    have hterm1 : deriv (deriv (profileSuperEps β θh ε)) s * G ≤
        q ^ 2 * betaEps β ε (profileSuperEps β θh ε s) := by
      rcases lt_or_ge s ε with hsε | hsε
      · have habs : |s| ≤ a₀ := abs_le.2 ⟨hsa.le, by linarith⟩
        have hG := hGq habs
        have hB := hβ.betaEps_nonneg ε (profileSuperEps β θh ε s) hε0.le
        calc _ ≤ θh * betaEps β ε (profileSuperEps β θh ε s) * G :=
              mul_le_mul_of_nonneg_right hP2b hG0
          _ = betaEps β ε (profileSuperEps β θh ε s) * (θh * G) := by ring
          _ ≤ betaEps β ε (profileSuperEps β θh ε s) * q ^ 2 := mul_le_mul_of_nonneg_left hG hB
          _ = _ := by ring
      · have hzero : betaEps β ε (profileSuperEps β θh ε s) = 0 := by
          rw [profileSuperEps_of_le hβ hθh hε0 hsε, betaEps,
            hβ.eq_zero_of_one_le ((one_le_div hε0).2 hsε), zero_div]
        rw [hzero, mul_zero] at hP2b ⊢
        have : deriv (deriv (profileSuperEps β θh ε)) s = 0 := le_antisymm hP2b hP2a
        rw [this, zero_mul]
    linarith
  · -- exponential tail
    set σ := s / ε with hσ_def
    have hs0 : σ ≤ -(a₀ / ε) := by
      rw [hσ_def, neg_div']; exact div_le_div_of_nonneg_right (by linarith) hε0.le
    have hsn : σ ≤ 0 := hs0.trans (neg_nonpos.2 (by positivity))
    obtain ⟨t1, t2, t3⟩ := htail σ hsn
    have hexp : C * Real.exp (c * σ) ≤ Ex := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0.le
      calc c * σ ≤ c * -(a₀ / ε) := mul_le_mul_of_nonneg_left hs0 hc0.le
        _ = -(c * a₀ / ε) := by ring
    have hΨ2 : deriv (deriv (profileSuperEps β θh ε)) s ≤ Ex / ε := by
      rw [profileSuperEps_deriv_deriv hβ hθh hε0]
      exact div_le_div_of_nonneg_right (t3.trans hexp) hε0.le
    have hΨ1 : deriv (profileSuperEps β θh ε) s ≤ Ex := by
      rw [profileSuperEps_deriv hβ hθh hε0]; exact t2.trans hexp
    have hGA : G ≤ |Gmax| := hGmax.trans (le_abs_self _)
    have hLD : Lap ≤ |D| := (le_abs_self _).trans (hD.trans (le_abs_self _))
    have hlhs : deriv (deriv (profileSuperEps β θh ε)) s * G +
        deriv (profileSuperEps β θh ε) s * Lap ≤ Ex * A / ε := by
      have h1 : deriv (deriv (profileSuperEps β θh ε)) s * G ≤ Ex / ε * |Gmax| :=
        mul_le_mul hΨ2 hGA hG0 (by positivity)
      have h2 : deriv (profileSuperEps β θh ε) s * Lap ≤ Ex * |D| := by
        rcases le_total Lap 0 with hn | hn
        · exact (mul_nonpos_of_nonneg_of_nonpos hP1.1.le hn).trans (by positivity)
        · exact mul_le_mul hΨ1 hLD hn hE0
      have h3 : Ex * |D| ≤ Ex / ε * |D| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [le_div_iff₀ hε0]; nlinarith
      have h4 : Ex / ε * |Gmax| + Ex / ε * |D| = Ex * A / ε := by rw [hA_def]; ring
      linarith
    have hΨs : profileSuper β θh σ ∈ Icc κ ((1 + κ) / 2) := by
      refine ⟨(kappa_lt_profileSuper hβ hθh σ).le, ?_⟩
      have := t1.trans hexp
      linarith
    have hrhs : Qmin ^ 2 * b / ε ≤ q ^ 2 * betaEps β ε (profileSuperEps β θh ε s) := by
      rw [betaEps, profileSuperEps_div hε0, ← hσ_def, mul_div_assoc']
      refine div_le_div_of_nonneg_right ?_ hε0.le
      have hQ2' : Qmin ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hQmin.le hq 2
      exact mul_le_mul hQ2' (hb _ hΨs) hb0.le hQ2
    have hmid : Ex * A / ε ≤ Qmin ^ 2 * b / ε := div_le_div_of_nonneg_right hE2 hε0.le
    linarith

/-- **Pointwise form of the subsolution computation of Lemma A.4** (its proof), with the
Laplacian term `Lap` a free parameter: if `Lap ≥ 0`, `G ≥ 0`, and `q² ≤ θ G` wherever the
reaction term `β_ε(Φ_ε(s))` is active, then `q² β_ε(Φ_ε(s)) ≤ Φ_ε''(s) G + Φ_ε'(s) Lap`. -/
theorem profileSubEps_ineq (hβ : IsReactionProfile β) {θ ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) (s G Lap q : ℝ) (hLap : 0 ≤ Lap)
    (hGq : 0 < betaEps β ε (profileSubEps β θ ε s) → q ^ 2 ≤ θ * G) :
    q ^ 2 * betaEps β ε (profileSubEps β θ ε s) ≤
      deriv (deriv (profileSubEps β θ ε)) s * G + deriv (profileSubEps β θ ε) s * Lap := by
  rw [profileSubEps_deriv_deriv hβ hθ hθ1 hε]
  have h1 : 0 ≤ deriv (profileSubEps β θ ε) s * Lap :=
    mul_nonneg (profileSubEps_deriv_mem hβ hθ hθ1 hε s).1.le hLap
  have hB := hβ.betaEps_nonneg ε (profileSubEps β θ ε s) hε.le
  rcases hB.eq_or_lt with h0 | hpos
  · rw [← h0]; simp only [mul_zero, zero_mul, zero_add]; exact h1
  · have := mul_le_mul_of_nonneg_left (hGq hpos) hpos.le
    linarith

end Profiles

end PerronVariational

end
