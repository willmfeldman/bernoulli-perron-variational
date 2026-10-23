/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
import PerronVariational.Inner.Compactness
import PerronVariational.Inner.LongTimeTimeReg
import PerronVariational.Inner.LongTimeUniform

/-!
# Long-time limit, Step 1 along a sequence of times (no monotonicity)

Step 1 of the proof of **[Theorem 3.14](#AFS:t.longtime-inner)** of F. Abedin, W. M. Feldman, K.
Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981, as in the paper: "Consider any sequence `t → ∞`. [...] The
uniform boundedness, interior Lipschitz estimate [(3.13)](#AFS:eqn:LipEst), and the Arzelà–Ascoli
theorem show convergence of the sequence is locally uniform and that the limit inherits
[(3.13)](#AFS:eqn:LipEst)."

* `exists_subseq_tendstoLocallyUniformlyOn`: for any `tₙ → ∞`, a subsequence of `u(·, tₙ)`
  converges locally uniformly in `U` (Arzelà–Ascoli,
  `Inner.exists_tendstoLocallyUniformlyOn_subseq`, from the uniform bound and the equi-Lipschitz
  bounds given by [(3.13)](#AFS:eqn:LipEst) for `t > 4`). The paper also extracts a weak `H¹(U)`
  limit here; in the formalization no extraction is needed: the weak convergence of the gradients
  follows in Step 2 from the locally uniform convergence and the local gradient bounds
  (`StationaryLimit.tendstoLpLoc_gradient_of_energy`).
* `norm_gradient_le_of_tendsto_seq`: the limit satisfies [(3.15)](#AFS:eqn:inftyLip) with the
  constant of [(3.13)](#AFS:eqn:LipEst). Estimate [(3.13)](#AFS:eqn:LipEst) at time `tₙ` involves
  `sup |u|` on the backward cylinder `B_{2r}(x) × (tₙ - 4r², tₙ]`; the backward slices are uniformly
  close to `u(·, tₙ)` by `eventually_abs_sub_le_window` (time regularity from `∂ₜu ∈ L²(U_∞)`). The
  paper's "inherits" leaves this step implicit.
-/

open Set Filter Topology Metric MeasureTheory
open scoped Gradient NNReal

@[expose] public section

namespace PerronVariational

namespace LongTime

variable {d : ℕ} {U : Set (E d)} {Q : E d → ℝ} {u w χ : E d × ℝ → ℝ} {M C : ℝ}

/-- Uniform local Lipschitz bounds for the slices `u(·, τ)`, `τ > 4`, from
[(3.13)](#AFS:eqn:LipEst). -/
theorem exists_ball_lipschitzOnWith_slices (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hM : ∀ p ∈ UInf U, u p ≤ M) (hlip : InteriorLipEst U u C) {x : E d} (hx : x ∈ U) :
    ∃ r > 0, ball x r ⊆ U ∧ ∃ K : ℝ≥0,
      ∀ τ, 4 < τ → LipschitzOnWith K (fun y ↦ u (y, τ)) (ball x r) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  set r := min (ε / 2) 1 with hr_def
  have hr : 0 < r := lt_min (by linarith) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have h2r : 2 * r ≤ ε := by have := min_le_left (ε / 2) 1; linarith
  refine ⟨r, hr, (ball_subset_ball (by linarith)).trans hball, (C * (M / r + 1)).toNNReal,
    fun τ hτ ↦ ?_⟩
  have hcyl : parCyl x τ (2 * r) ⊆ UInf U := fun q hq ↦
    ⟨hball (ball_subset_ball h2r hq.1), show 0 < q.2 by have := hq.2.1; nlinarith⟩
  exact lipschitzOnWith_slice_of_interiorLipEst hlip h hr hr1 hcyl fun q hq ↦
    abs_le.2 ⟨by linarith [h.nonneg q (hcyl hq), hM q (hcyl hq)], hM q (hcyl hq)⟩

/-- **[Theorem 3.14](#AFS:t.longtime-inner), Step 1** (paper version, no monotonicity): for a
bounded parabolic inner variational solution satisfying [(3.13)](#AFS:eqn:LipEst) and any sequence
`tₙ → ∞`, a subsequence `u(·, t_{φ n})` converges locally uniformly in `U` to a nonnegative locally
Lipschitz function `u_∞`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn (hU : IsOpen U)
    (h : IsParaInnerVarSolution U Q u w χ) (hM : ∀ p ∈ UInf U, u p ≤ M)
    (hlip : InteriorLipEst U u C) {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ uInf : E d → ℝ,
      TendstoLocallyUniformlyOn (fun n x ↦ u (x, t (φ n))) uInf atTop U ∧
      (∀ x ∈ U, 0 ≤ uInf x) ∧ LocallyLipschitzOn U uInf := by
  obtain ⟨N, hN⟩ := (ht.eventually_gt_atTop 4).exists_forall_of_atTop
  set f : ℕ → E d → ℝ := fun n x ↦ u (x, t (n + N)) with hf
  have htN : ∀ n, 4 < t (n + N) := fun n ↦ hN _ (Nat.le_add_left N n)
  have hpos : ∀ n, 0 < t (n + N) := fun n ↦ by linarith [htN n]
  have hcont : ∀ n, ContinuousOn (f n) U := fun n ↦
    (locallyLipschitzOn_slice h (hpos n)).continuousOn
  have hbdd : ∀ x ∈ U, ∃ B : ℝ, ∀ n, |f n x| ≤ B := fun x hx ↦ ⟨M, fun n ↦ abs_le.2
    ⟨by linarith [h.nonneg _ (mk_mem_prod hx (hpos n)), hM _ (mk_mem_prod hx (hpos n))],
      hM _ (mk_mem_prod hx (hpos n))⟩⟩
  have heq : ∀ x ∈ U, ∀ η > 0, ∀ᶠ y in 𝓝 x, ∀ n, |f n y - f n x| < η := by
    intro x hx η hη
    obtain ⟨r, hr, -, K, hK⟩ := exists_ball_lipschitzOnWith_slices hU h hM hlip hx
    have hρ : 0 < min r (η / ((K : ℝ) + 1)) := lt_min hr (by positivity)
    filter_upwards [ball_mem_nhds x hρ] with y hy n
    have hyr : y ∈ ball x r := ball_subset_ball (min_le_left _ _) hy
    have h1 := (hK _ (htN n)).dist_le_mul y hyr x (mem_ball_self hr)
    rw [Real.dist_eq] at h1
    have hd : dist y x < η / ((K : ℝ) + 1) := lt_of_lt_of_le (mem_ball.1 hy) (min_le_right _ _)
    have hK0 : (0 : ℝ) ≤ K := K.2
    calc |f n y - f n x| ≤ K * dist y x := h1
      _ ≤ ((K : ℝ) + 1) * dist y x := by nlinarith [dist_nonneg (x := y) (y := x)]
      _ < ((K : ℝ) + 1) * (η / ((K : ℝ) + 1)) := by gcongr
      _ = η := by field_simp
  obtain ⟨φ, hφ, f₀, -, hconv⟩ :=
    Inner.exists_tendstoLocallyUniformlyOn_subseq hU f hcont hbdd heq
  refine ⟨fun n ↦ φ n + N, fun m n hmn ↦ by simpa using hφ hmn, f₀, hconv, fun x hx ↦ ?_,
    fun x hx ↦ ?_⟩
  · exact ge_of_tendsto (hconv.tendsto_at hx) (Eventually.of_forall fun n ↦
      h.nonneg _ (mk_mem_prod hx (hpos _)))
  · obtain ⟨r, hr, hsub, K, hK⟩ := exists_ball_lipschitzOnWith_slices hU h hM hlip hx
    exact ⟨K, ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),
      lipschitzOnWith_of_tendsto (Eventually.of_forall fun n ↦ hK _ (htN _))
        fun y hy ↦ hconv.tendsto_at (hsub hy)⟩

/-- **[(3.15)](#AFS:eqn:inftyLip)** for a limit along a sequence (no monotonicity): if
`u(·, tₙ) → u_∞` locally uniformly in `U` with `tₙ → ∞`, then for `B_{2r}(x) ⊆ U`, `r ≤ 1` and
`|u_∞| ≤ M'` on `B_{2r}(x)`, `‖∇u_∞‖ ≤ C (M'/r + 1)` on `B_r(x)`, with the constant `C` of
[(3.13)](#AFS:eqn:LipEst). -/
theorem norm_gradient_le_of_tendsto_seq (hU : IsOpen U) (h : IsParaInnerVarSolution U Q u w χ)
    (hM : ∀ p ∈ UInf U, u p ≤ M) (hlip : InteriorLipEst U u C) {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) {uInf : E d → ℝ}
    (hconv : TendstoLocallyUniformlyOn (fun n x ↦ u (x, t n)) uInf atTop U)
    (x : E d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hball : ball x (2 * r) ⊆ U) (M' : ℝ)
    (hM' : ∀ y ∈ ball x (2 * r), |uInf y| ≤ M') (y : E d) (hy : y ∈ ball x r) :
    ‖∇ uInf y‖ ≤ C * (M' / r + 1) := by
  have hpt : ∀ z ∈ U, Tendsto (fun n ↦ u (z, t n)) atTop (𝓝 (uInf z)) := fun z hz ↦
    hconv.tendsto_at hz
  -- the bound at every smaller radius `r' ∈ (dist y x, r)`, with slack `δ = r - r'`
  have key : ∀ r' ∈ Ioo (max (dist y x) (r / 2)) r,
      ‖∇ uInf y‖ ≤ C * ((M' + (r - r')) / r' + 1) := by
    intro r' hr'
    have hr'0 : 0 < r' := lt_of_lt_of_le (by linarith) (le_max_right _ _ |>.trans hr'.1.le)
    have hyr' : y ∈ ball x r' := lt_of_le_of_lt (le_max_left _ _) hr'.1
    have hr'1 : r' ≤ 1 := hr'.2.le.trans hr1
    set δ := r - r' with hδ
    have hδ0 : 0 < δ := by linarith [hr'.2]
    have hKsub : closedBall x (2 * r') ⊆ U :=
      (closedBall_subset_ball (by linarith [hr'.2])).trans hball
    have hunif : TendstoUniformlyOn (fun n x ↦ u (x, t n)) uInf atTop (closedBall x (2 * r')) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hKsub
        (isCompact_closedBall x (2 * r'))
    have hclose : ∀ᶠ n in atTop, ∀ z ∈ closedBall x (2 * r'), u (z, t n) < uInf z + δ / 2 := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif (δ / 2) (half_pos hδ0)] with n hn z hz
      have := hn z hz
      rw [Real.dist_eq] at this
      linarith [le_abs_self (uInf z - u (z, t n)), neg_abs_le (uInf z - u (z, t n))]
    -- backward slices are close to `u(·, tₙ)` (time regularity)
    have hwin := ht.eventually (eventually_abs_sub_le_window hU h hlip hM
      (isCompact_closedBall x (2 * r')) hKsub (sq_nonneg (2 * r')) (half_pos hδ0))
    -- eventually the sup bound `M' + δ` holds on the cylinder `Q_{2r'}(x, tₙ)`
    have hbound : ∀ᶠ n in atTop, parCyl x (t n) (2 * r') ⊆ UInf U ∧
        ∀ q ∈ parCyl x (t n) (2 * r'), |u q| ≤ M' + δ := by
      filter_upwards [ht.eventually (eventually_gt_atTop ((2 * r') ^ 2)), hclose, hwin] with n hn
        hcl hw
      have hcyl : parCyl x (t n) (2 * r') ⊆ UInf U := fun q hq ↦
        ⟨hKsub (ball_subset_closedBall hq.1), show 0 < q.2 by have := hq.2.1; linarith⟩
      refine ⟨hcyl, fun q hq ↦ abs_le.2 ⟨?_, ?_⟩⟩
      · linarith [h.nonneg q (hcyl hq), abs_nonneg (uInf q.1),
          hM' q.1 (ball_subset_ball (by linarith [hr'.2]) hq.1)]
      have hM'z : uInf q.1 ≤ M' :=
        (le_abs_self _).trans (hM' q.1 (ball_subset_ball (by linarith [hr'.2]) hq.1))
      have hqb : q.1 ∈ closedBall x (2 * r') := ball_subset_closedBall hq.1
      have h1 := hw q.1 hqb q.2 ⟨hq.2.1.le, hq.2.2⟩
      have h2 := hcl q.1 hqb
      rw [show ((q.1, q.2) : E d × ℝ) = q from rfl] at h1
      linarith [le_abs_self (u q - u (q.1, t n))]
    set g := C * ((M' + δ) / r' + 1) with hg
    have hlipt : ∀ᶠ n in atTop, LipschitzOnWith g.toNNReal (fun z ↦ u (z, t n)) (ball x r') :=
      hbound.mono fun n hn ↦ lipschitzOnWith_slice_of_interiorLipEst hlip h hr'0 hr'1 hn.1 hn.2
    have hlipInf : LipschitzOnWith g.toNNReal uInf (ball x r') :=
      lipschitzOnWith_of_tendsto hlipt fun z hz ↦
        hpt z (hKsub (ball_subset_closedBall.trans (closedBall_subset_closedBall
          (by linarith)) hz))
    -- `g ≥ 0`, since [(3.13)](#AFS:eqn:LipEst) bounds a norm by `g`
    obtain ⟨n, hn⟩ := hbound.exists
    have hg0 : 0 ≤ g := (norm_nonneg _).trans
      (hlip x (t n) r' hr'0 hr'1 hn.1 (M' + δ) hn.2 (x, t n)
        ⟨mem_ball_self hr'0, by simp only [mem_Ioc]; constructor <;> nlinarith⟩)
    have hfd : ‖fderiv ℝ uInf y‖ ≤ g.toNNReal :=
      norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hyr') hlipInf
    rw [Real.coe_toNNReal _ hg0] at hfd
    simpa [gradient] using hfd
  -- let `r' ↑ r`
  have hlim : Tendsto (fun r' ↦ C * ((M' + (r - r')) / r' + 1)) (𝓝[<] r)
      (𝓝 (C * (M' / r + 1))) := by
    have hc : ContinuousAt (fun r' ↦ C * ((M' + (r - r')) / r' + 1)) r :=
      ((continuousAt_const.add (continuousAt_const.sub continuousAt_id)).div continuousAt_id
        hr.ne').add continuousAt_const |>.const_mul C
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlt : max (dist y x) (r / 2) < r := max_lt hy (by linarith)
  exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsLT hlt) fun r' hr' ↦ key r' hr')

end LongTime

end PerronVariational

end
