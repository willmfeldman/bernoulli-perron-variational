/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Main
public import PerronVariational.Statements.Intermediate
import Mathlib.Analysis.InnerProductSpace.Calculus
import PerronVariational.Semilinear.Calculus
import PerronVariational.Stationary.ViscosityLocal

/-!
# Theorem 1.1 (conditional assembly)

Reference: F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

**Theorem 1.1** of the paper, assembled from
* Proposition 6.1 / Proposition 6.2 (`InnerSmallestStatement`, `InnerLargestStatement`): parts (i),
  (ii);
* Lemma 2.7 and its dual (`Setting.perronSmallest_isLocalSmallestSuper_near_fb`,
  `Setting.perronLargest_isLocalLargestSub_near_fb`): the Perron solution is a local extremal
  solution in a ball around each free boundary point;
* Lemma 6.3 (`DirectionalStatement`), applied in the standing setting restricted to that ball
  (`Setting.restrictBall`): part (iii).

Lemma 2.7 needs the Perron solution to be continuous on `Ū` (the glued competitor must lie in the
Perron class, whose members are in `C(Ū)`). The paper does not state this continuity; here it is a
conclusion of `InnerSmallestStatement` / `InnerLargestStatement`, a by-product of the proofs of
Propositions 6.1/6.2, so Lemma 2.7 applies with no extra hypothesis.

The unconditional theorems `main_smallest`, `main_largest` are in `PerronVariational.Main.Final`.
`main_smallest_of`, `main_largest_of` and `directional` are fully proved.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### The standing setting on a ball -/

/-- A ball has `C²` boundary, in the defining-function encoding of `HasC2Boundary`, with defining
function `ρ(y) = |y - x|² - r²`. -/
theorem hasC2Boundary_ball (x : E d) {r : ℝ} (hr : 0 < r) : HasC2Boundary (ball x r) := by
  refine ⟨fun y ↦ ‖y - x‖ ^ 2 - r ^ 2,
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const, ?_, ?_⟩
  · ext y
    simp only [mem_ball, dist_eq_norm, mem_setOf_eq, sub_neg]
    exact (sq_lt_sq₀ (norm_nonneg _) hr.le).symm
  · intro y hy h0
    rw [frontier_ball x hr.ne'] at hy
    have hyx : ‖y - x‖ = r := by simpa [dist_eq_norm] using hy
    have hd : HasFDerivAt (fun y ↦ ‖y - x‖ ^ 2 - r ^ 2)
        ((2 : ℕ) • (innerSL ℝ (y - x)).comp (ContinuousLinearMap.id ℝ (E d))) y :=
      ((hasFDerivAt_sub_const (𝕜 := ℝ) (x := y) x).norm_sq).sub_const _
    have hf0 : fderiv ℝ (fun y ↦ ‖y - x‖ ^ 2 - r ^ 2) y = 0 := by
      rw [← norm_eq_zero, ← norm_gradient_eq_norm_fderiv, h0, norm_zero]
    rw [hd.fderiv] at hf0
    have h2 := congrArg (fun L : E d →L[ℝ] ℝ ↦ L (y - x)) hf0
    simp only [two_nsmul, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at h2
    rw [real_inner_self_eq_norm_sq, hyx] at h2
    have : 0 < r ^ 2 := by positivity
    linarith

/-- The standing setting restricted to a ball `B_r(x)` with `B̄_r(x) ⊆ U` (same `Q`, bounds). -/
def Setting.restrictBall (S : Setting d) (x : E d) {r : ℝ} (hr : 0 < r)
    (hB : closedBall x r ⊆ S.U) : Setting d where
  U := ball x r
  Q := S.Q
  Qmin := S.Qmin
  Qmax := S.Qmax
  two_le := S.two_le
  isOpen := isOpen_ball
  isBounded := isBounded_ball
  isConnected := (convex_ball x r).isConnected (nonempty_ball.2 hr)
  c2 := hasC2Boundary_ball x hr
  lip := let ⟨K, hK⟩ := S.lip
    ⟨K, hK.mono (closure_ball_subset_closedBall.trans (hB.trans subset_closure))⟩
  Qmin_pos := S.Qmin_pos
  Qmin_le_Qmax := S.Qmin_le_Qmax
  Q_mem := fun y hy ↦ S.Q_mem y (subset_closure (hB (closure_ball_subset_closedBall hy)))

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1**, smallest supersolution case, conditional on Proposition 6.1 (including the
continuity of the Perron solution on `Ū`, input of Lemma 2.7) and Lemma 6.3. -/
theorem main_smallest_of (h61 : InnerSmallestStatement) (h63 : DirectionalStatement) :
    MainSmallestStatement := by
  intro d S g hg hbd
  obtain ⟨hvisc, ⟨χ, hinner⟩, hcont⟩ := h61 d S g hg hbd
  refine ⟨hvisc, ⟨χ, hinner⟩, fun x hx ↦ ?_⟩
  obtain ⟨r, hr, hB, hloc⟩ :=
    S.perronSmallest_isLocalSmallestSuper_near_fb hg hvisc.1 hcont hx
  refine ⟨r, hr, hB, ?_⟩
  have hbU : ball x r ⊆ S.U := ball_subset_closedBall.trans hB
  have hpos : posSet (perronSmallest S.U S.Q g) (ball x r) ⊆
      posSet (perronSmallest S.U S.Q g) S.U := fun y hy ↦ ⟨hbU hy.1, hy.2⟩
  exact (h63 d (S.restrictBall x hr hB) (perronSmallest S.U S.Q g) (hinner.locLip.mono hbU)
    (hinner.c2.mono hpos) fun y hy ↦ hinner.harmonic y (hpos hy)).1 hloc

/-- **Theorem 1.1**, largest subsolution case, conditional on Proposition 6.2 (including the
continuity of the Perron solution on `Ū`) and Lemma 6.3.

The paper proves "Perron extremal ⇒ local extremal" (Lemma 2.7) only for smallest
supersolutions, and Lemma 6.3 needs the dual statement for largest subsolutions. Here the dual is
proved (`Setting.perronLargest_isLocalLargestSub_near_fb`): the glued competitor stays below `g₊`
by comparison with the strict supersolutions `g + ε(r² - |y - x|²)`. -/
theorem main_largest_of (h62 : InnerLargestStatement) (h63 : DirectionalStatement) :
    MainLargestStatement := by
  intro d S g hg
  obtain ⟨hvisc, ⟨χ, hinner⟩, hcont⟩ := h62 d S g hg
  refine ⟨hvisc, ⟨χ, hinner⟩, fun x hx ↦ ?_⟩
  obtain ⟨r, hr, hB, hloc⟩ :=
    S.perronLargest_isLocalLargestSub_near_fb hg hvisc.2 hcont hx
  refine ⟨r, hr, hB, ?_⟩
  have hbU : ball x r ⊆ S.U := ball_subset_closedBall.trans hB
  have hpos : posSet (perronLargest S.U S.Q g) (ball x r) ⊆
      posSet (perronLargest S.U S.Q g) S.U := fun y hy ↦ ⟨hbU hy.1, hy.2⟩
  exact (h63 d (S.restrictBall x hr hB) (perronLargest S.U S.Q g) (hinner.locLip.mono hbU)
    (hinner.c2.mono hpos) fun y hy ↦ hinner.harmonic y (hpos hy)).2 hloc

end PerronVariational

end
