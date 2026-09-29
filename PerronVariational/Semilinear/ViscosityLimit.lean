/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import Mathlib.Algebra.Order.Ring.Star
import PerronVariational.Parabolic.Nondegen
import PerronVariational.Semilinear.ViscosityLimitCalculus
import PerronVariational.Semilinear.ViscosityLimitStar
import PerronVariational.Semilinear.ViscosityLimitSuper

/-!
# Proposition 5.3 and Corollary 5.4: semilinear limits in the viscosity sense

Proposition 5.3 and Corollary 5.4 of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

* `semilinear_limit_relaxedSolution : SemilinearLimitRelaxedStatement` (**Proposition 5.3**, in
  corrected form), proved in `ViscosityLimitSub` (supersolution part in `ViscosityLimitSuper`).
  The paper states it with `E = limsup* {u_j > ε_j}`, and with that set it is false: `u ≡ ε` is a
  stationary solution, and a vanishing perturbation lifts a whole `ε`-plateau over the threshold.
  The formal statement uses `E = \overline{U × (0, T]}`; the relaxed subsolution property for the
  authors' corrected set `E*` below is `semilinear_limit_isParaRelaxedSub_star`.
* `semilinear_limit_viscSolution_increasing : SemilinearLimitIncreasingStatement`
  (**Corollary 5.4**), with the authors' corrected set
  `E* = \overline{⋃_{0<κ≤1} limsup* {u_j > κ ε_j}}`: the supersolution part of
  Proposition 5.3, the relaxed subsolution property of `(u, E*)`
  (`semilinear_limit_isParaRelaxedSub_star`, `ViscosityLimitStar`), Proposition 3.5
  (`isParaSub_of_monotone_Ioc`) with the time-`0` hypothesis from Proposition 3.8(vi*), and
  monotonicity of the limit. The properties of the well-prepared family enter as hypotheses.

The paper states the identity `E* = \overline{{u > 0}}` of Corollary 5.4 without restriction, but
argues it only at `t = 0`, not at lateral boundary points over `∂U`; here it is stated inside
`U × [0, T]`, which is all that is used later.
-/

open Set Filter Topology Metric

@[expose] public section

namespace PerronVariational

variable {d : ℕ}


section Cor54

variable {S : Setting d} {g : E d → ℝ} {β : ℝ → ℝ} {ε₀ : ℝ} {gε : ℝ → E d → ℝ}
  {uε : ℝ → E d × ℝ → ℝ} {T : ℝ} {εs : ℕ → ℝ} {u : E d × ℝ → ℝ}

/-- **No points of `E*` at `t = 0` away from `\overline{{g > 0}}`** (from
Proposition 3.8(vi*)). Every point of `E*` near `(x, 0)` is a limit of points of some
`limsup* {u_j > κ ε_j}`, and (vi*) with that `κ` excludes these near `K × [0, τ]`. -/
theorem timeSlice_semilinearLimitSetStar_zero_subset
    (hvistar : ∀ K : Set (E d), IsCompact K → K ⊆ S.U \ closure (posSet g (closure S.U)) →
      ∃ τ > 0, ∀ κ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ → ∀ x ∈ K, ∀ t ∈ Icc 0 τ,
        uε ε (x, t) < κ * ε)
    (hεs : ∀ j, εs j ∈ Ioo 0 ε₀) (hεlim : Tendsto εs atTop (𝓝 0)) :
    timeSlice (semilinearLimitSetStar S.U (Ioc 0 T) εs (fun j ↦ uε (εs j))) 0 ∩ S.U ⊆
      closure {x ∈ S.U | 0 < max (g x) 0} := by
  rintro x ⟨hxE, hxU⟩
  by_contra hx
  have hxP : x ∉ closure (posSet g (closure S.U)) := by
    intro hxP
    refine hx (Metric.mem_closure_iff.2 fun ε hε ↦ ?_)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 S.isOpen x hxU
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hxP (min ε r) (lt_min hε hr)
    exact ⟨y, ⟨hball (mem_ball'.2 (hxy.trans_le (min_le_right _ _))),
      lt_max_of_lt_left hy.2⟩, hxy.trans_le (min_le_left _ _)⟩
  have hopen : IsOpen (S.U ∩ (closure (posSet g (closure S.U)))ᶜ) :=
    S.isOpen.inter isClosed_closure.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen x ⟨hxU, hxP⟩
  have hKsub : closedBall x (r / 2) ⊆ S.U \ closure (posSet g (closure S.U)) := fun y hy ↦ by
    have := hball (closedBall_subset_ball (by linarith) hy)
    exact ⟨this.1, this.2⟩
  obtain ⟨τ, hτ, hsmall⟩ := hvistar _ (isCompact_closedBall x (r / 2)) hKsub
  set N := ball x (r / 2) ×ˢ Iio τ with hN_def
  have hNo : IsOpen N := isOpen_ball.prod isOpen_Iio
  have hN : N ∈ 𝓝 (x, (0 : ℝ)) := hNo.mem_nhds ⟨mem_ball_self (by linarith), hτ⟩
  obtain ⟨q, hqN, hqU⟩ := mem_closure_iff_nhds.1 hxE N hN
  rw [mem_iUnion₂] at hqU
  obtain ⟨κ, hκ, hqL⟩ := hqU
  obtain ⟨ε₁, hε₁, hsmallκ⟩ := hsmall κ hκ.1
  have hev : ∀ᶠ j in atTop, εs j < ε₁ := hεlim.eventually (gt_mem_nhds hε₁)
  obtain ⟨j, ⟨q', ⟨hq'Ω, hq'κ⟩, hq'N⟩, hj⟩ :=
    ((hqL N (hNo.mem_nhds hqN)).and_eventually hev).exists
  have := hsmallκ (εs j) ⟨(hεs j).1, hj⟩ (hεs j).2 q'.1 (ball_subset_closedBall hq'N.1) q'.2
    ⟨hq'Ω.2.1.le, (mem_Iio.1 hq'N.2).le⟩
  exact absurd hq'κ (not_lt.2 this.le)

/-- **Corollary 5.4**, with the authors' corrected set `E*`. For the
well-prepared family of Proposition 3.8 with strict subsolution data `g` (increasing in time), and
`u_{ε_j} → u` locally uniformly in `U × (0, T]`: `u` is monotone increasing in time,
`E* = \overline{{u > 0}}` in `U × [0, T]`, and `u` is a viscosity solution of (3.1) in `U × (0, T]`.
Proof: Proposition 5.3 with `E*` (`semilinear_limit_isParaSuper`,
`semilinear_limit_isParaRelaxedSub_star`), then Proposition 3.5 with the time-`0` hypothesis from
Proposition 3.8(vi*) (`timeSlice_semilinearLimitSetStar_zero_subset`). -/
theorem semilinear_limit_viscSolution_increasing : SemilinearLimitIncreasingStatement := by
  intro d S g β ε₀ gε uε hβ hg hwp T εs u hT hεs hεlim hconv
  obtain ⟨hε₀, hfam, -, -, -, -, -, -, hvistar⟩ := hwp
  set us : ℕ → E d × ℝ → ℝ := fun j ↦ uε (εs j) with hus_def
  set Ω := S.U ×ˢ Ioc 0 T with hΩ_def
  set Eset := semilinearLimitSetStar S.U (Ioc 0 T) εs us with hE_def
  -- a bound for `g` on `Ū`
  obtain ⟨M, hM⟩ := S.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hg.1.continuous.continuousOn
  have hM' : ∀ x ∈ S.U, |g x| ≤ M := fun x hx ↦ by
    simpa [Real.norm_eq_abs] using hM x (subset_closure hx)
  have hfj : ∀ j, _ := fun j ↦ hfam (εs j) (hεs j)
  have hsolj : ∀ j, IsSemilinearSolution S.U S.Q β (εs j) (gε (εs j)) (us j) :=
    fun j ↦ (hfj j).1
  have hmonoj : ∀ j, MonotoneInTime (us j) (closure S.U) (Ici 0) := fun j ↦ by
    have := (hfj j).2.2.2.2.2.2.1
    simpa using this
  have hbdsj : ∀ j, ∀ x ∈ closure S.U, max (g x) 0 ≤ gε (εs j) x ∧
      gε (εs j) x ≤ max (g x) 0 + εs j := fun j ↦ (hfj j).2.2.1
  have hnnj : ∀ j, ∀ p ∈ closure S.U ×ˢ Ici 0, 0 ≤ us j p ∧ us j p ≤ M + εs j :=
    fun j ↦ (hfj j).2.2.2.2.2.2.2.1 M hM'
  have hεpos : ∀ j, 0 < εs j := fun j ↦ (hεs j).1
  have hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j) :=
    fun j ↦ (hsolj j).2.1.mono_domain subset_rfl Ioc_subset_Ioi_self
  have hnn : ∀ j, ∀ p ∈ Ω, 0 ≤ us j p := fun j p hp ↦
    (hnnj j p ⟨subset_closure hp.1, le_of_lt hp.2.1⟩).1
  -- Proposition 5.3 with `E*`
  have hsuper : IsParaSuper S.U S.Q (Ioc 0 T) u :=
    semilinear_limit_isParaSuper hβ hεpos hεlim hsol hnn hconv
  have hrelsub : IsParaRelaxedSub S.U S.Q (Ioc 0 T) u Eset :=
    semilinear_limit_isParaRelaxedSub_star hβ hεpos hεlim hsol hnn hconv
  -- monotonicity of the limit
  have hmono : MonotoneInTime u S.U (Ioc 0 T) := by
    intro x hx s hs t ht hst
    exact le_of_tendsto_of_tendsto' (hconv.tendsto_at ⟨hx, hs⟩) (hconv.tendsto_at ⟨hx, ht⟩)
      fun j ↦ hmonoj j x (subset_closure hx) (mem_Ici.2 hs.1.le) (mem_Ici.2 ht.1.le) hst
  -- `u ≥ g₊`
  have hu₀ : ∀ x ∈ S.U, ∀ t ∈ Ioc 0 T, max (g x) 0 ≤ u (x, t) := by
    intro x hx t ht
    refine ge_of_tendsto (hconv.tendsto_at ⟨hx, ht⟩) (Eventually.of_forall fun j ↦ ?_)
    have h0 : us j (x, 0) = gε (εs j) x := (hsolj j).2.2.1 x (subset_closure hx)
    have h1 := hmonoj j x (subset_closure hx) (mem_Ici.2 le_rfl) (mem_Ici.2 ht.1.le) ht.1.le
    simp only at h1
    linarith [(hbdsj j x (subset_closure hx)).1]
  -- no points of `E*` at `t = 0` outside `\overline{{g > 0}}` (Proposition 3.8(vi*))
  have hE₀ : timeSlice Eset 0 ∩ S.U ⊆ closure {x ∈ S.U | 0 < max (g x) 0} :=
    timeSlice_semilinearLimitSetStar_zero_subset (hvistar rfl) hεs hεlim
  -- Proposition 3.5
  obtain ⟨-, hsub⟩ := hrelsub.isParaSub_of_monotone_Ioc S hmono _ hu₀ hE₀
  have hEsub' := hrelsub.subset_closure_posSetP_of_monotone' S.isOpen
    (show (Ioc 0 T).Nonempty from ⟨T, hT, le_rfl⟩) (fun t ht ↦ ht.1)
    (fun t ht s hs ↦ (⟨hs.1, hs.2.trans ht.2⟩ : s ∈ Ioc 0 T)) hmono
    (fun x hx ↦ ⟨S.Qmin, S.Qmin_pos, by
      filter_upwards [S.isOpen.mem_nhds hx] with y hy
      exact (S.Q_mem y (subset_closure hy)).1⟩) _ hu₀ hE₀
  refine ⟨hmono, subset_antisymm ?_ ?_, hsuper, hsub⟩
  · -- `E* ⊆ \overline{{u > 0}}` inside `U × [0, T]`
    rintro p ⟨hpE, hpU, hpI⟩
    refine ⟨hEsub' ⟨hpE, hpU, ?_⟩, hpU, hpI⟩
    rcases hpI.1.lt_or_eq with h | h
    · exact Or.inr ⟨h, hpI.2⟩
    · exact Or.inl h.symm
  · rintro p ⟨hp, hpUI⟩
    exact ⟨closure_minimal hrelsub.2.2.2.2.1 hrelsub.2.2.1 hp, hpUI⟩

end Cor54

end PerronVariational

end
