/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import ParabolicBasic.Defs.Classical
public import ParabolicBasic.Defs.Parabolic
public import ParabolicBasic.Defs.Semilinear
public import ParabolicBasic.MainTheorems
public import PerronVariational.Defs.Semilinear
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Semilinear.Profiles

/-!
# Bridge to parabolic-basic-theory

The classical well-posedness of the semilinear problem, its comparison principle, and the
regularity of the spatial gradient up to `t = 0` for smooth data (the results from the literature
used in Appendix A of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981) are proved in the
dependency parabolic-basic-theory v0.1.0 (`ParabolicBasic.MainTheorems`), which treats the
general semilinear equation `∂ₜu = Δₓu - f(x, u)`. The equation (3.4) of the paper is the case

  `f(x, z) = Q(x)² β_ε(z)` (`semilinearReaction Q β ε`).

* The definitions agree by `rfl`: `hasC2Boundary_iff_pb`, `parBdry_eq_pb`, `gradₓ_eq_pb`,
  `isSemilinearSolOn_iff_pb`, `isSemilinearSolution_iff_pb` (and, in `Registry.Semilinear`, the
  viscosity notions). They check that the definitions of the two libraries still match.
* `semilinearReactionHyp`: if `Q` is Lipschitz on a compact set `s`, then `f` is Hölder (with
  exponent `1`) in `x` on `s`, Lipschitz in `z`, and bounded, uniformly on `s`. These are the
  hypotheses `hfx`, `hfz`, `hfb` of the theorems of parabolic-basic-theory.
* `contDiff_semilinearReaction`, `continuous_semilinearReaction`: joint regularity of `f` for the
  smoothness statements.
-/

open Set Filter Topology
open scoped ContDiff

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- The reaction term `f(x, z) = Q(x)² β_ε(z)` of (3.4), in the form `f : E d → ℝ → ℝ` used by
parabolic-basic-theory. -/
noncomputable def semilinearReaction (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ) : E d → ℝ → ℝ :=
  fun x z ↦ Q x ^ 2 * betaEps β ε z

/-! ### Definitional agreement -/

theorem hasC2Boundary_iff_pb {U : Set (E d)} :
    HasC2Boundary U ↔ ParabolicBasic.HasC2Boundary U :=
  Iff.rfl

theorem parBdry_eq_pb (V : Set (E d)) (a b : ℝ) : parBdry V a b = ParabolicBasic.parBdry V a b :=
  rfl

theorem gradₓ_eq_pb (u : E d × ℝ → ℝ) : gradₓ u = ParabolicBasic.gradₓ u :=
  rfl

theorem isSemilinearSolOn_iff_pb {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {I : Set ℝ}
    {u : E d × ℝ → ℝ} :
    IsSemilinearSolOn U Q β ε I u ↔
      ParabolicBasic.IsSemilinearSolOn U (semilinearReaction Q β ε) I u :=
  Iff.rfl

theorem isSemilinearSolution_iff_pb {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ}
    {g : E d → ℝ} {u : E d × ℝ → ℝ} :
    IsSemilinearSolution U Q β ε g u ↔
      ParabolicBasic.IsSemilinearSolution U (semilinearReaction Q β ε) g u :=
  Iff.rfl

/-! ### Hypotheses on the reaction term -/

namespace IsReactionProfile

variable {β : ℝ → ℝ}

/-- `β` is Lipschitz, hence `|β_ε(s) - β_ε(s')| ≤ (Lβ/ε²) |s - s'|`. -/
theorem exists_abs_betaEps_sub_le (hβ : IsReactionProfile β) :
    ∃ Lβ : ℝ, 0 ≤ Lβ ∧ ∀ ε > 0, ∀ s s' : ℝ,
      |betaEps β ε s - betaEps β ε s'| ≤ Lβ / ε ^ 2 * |s - s'| := by
  have hcs : HasCompactSupport β := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun s hs ↦ ?_
    exact hβ.2.1 s fun h ↦ hs (Ioo_subset_Icc_self h)
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) (n := 1) hcs
    (hβ.contDiff.of_le (by simp)) one_ne_zero
  refine ⟨C, C.2, fun ε hε s s' ↦ ?_⟩
  have h := hC.dist_le_mul (s / ε) (s' / ε)
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hε] at h
  rw [betaEps, betaEps, ← sub_div, abs_div, abs_of_pos hε, div_le_iff₀ hε]
  calc |β (s / ε) - β (s' / ε)| ≤ C * (|s - s'| / ε) := h
    _ = C / ε ^ 2 * |s - s'| * ε := by field_simp

end IsReactionProfile

/-- If `Q` is Lipschitz on a compact set `s`, then `f(x, z) = Q(x)² β_ε(z)` satisfies the
hypotheses of the theorems of parabolic-basic-theory on `s`: Hölder (exponent `1`) in `x`
uniformly in `z`, Lipschitz in `z` uniformly in `x`, and bounded. -/
theorem semilinearReactionHyp {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ} (hε : 0 < ε)
    {Q : E d → ℝ} {s : Set (E d)} (hs : IsCompact s) (hQ : ∃ K, LipschitzOnWith K Q s) :
    ParabolicBasic.SemilinearHyp (semilinearReaction Q β ε) s := by
  obtain ⟨K, hK⟩ := hQ
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hK.continuousOn
  obtain ⟨B, -, hB⟩ := hβ.exists_le
  obtain ⟨Lβ, -, hLβ⟩ := hβ.exists_abs_betaEps_sub_le
  have hb0 : ∀ z, 0 ≤ betaEps β ε z := fun z ↦ hβ.betaEps_nonneg ε z hε.le
  have hb1 : ∀ z, betaEps β ε z ≤ B / ε := fun z ↦ div_le_div_of_nonneg_right (hB _) hε.le
  have hM' : ∀ x ∈ s, |Q x| ≤ M := fun x hx ↦ by simpa [Real.norm_eq_abs] using hM x hx
  have hsq : ∀ x ∈ s, Q x ^ 2 ≤ M ^ 2 := fun x hx ↦ sq_le_sq' (abs_le.1 (hM' x hx)).1
    (abs_le.1 (hM' x hx)).2
  refine ⟨⟨2 * M * K * (B / ε), 1, one_pos, le_rfl, fun x hx y hy z ↦ ?_⟩,
    ⟨M ^ 2 * (Lβ / ε ^ 2), fun x hx z w ↦ ?_⟩, ⟨M ^ 2 * (B / ε), fun x hx z ↦ ?_⟩⟩
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' x hx)
    have hxy : |Q x - Q y| ≤ K * dist x y := by
      simpa [Real.dist_eq] using hK.dist_le_mul x hx y hy
    have hsum : |Q x + Q y| ≤ 2 * M := (abs_add_le _ _).trans (by linarith [hM' x hx, hM' y hy])
    simp only [semilinearReaction, Real.rpow_one]
    rw [← sub_mul, sq_sub_sq, abs_mul, abs_mul, abs_of_nonneg (hb0 z)]
    calc |Q x + Q y| * |Q x - Q y| * betaEps β ε z ≤ 2 * M * (K * dist x y) * (B / ε) :=
          mul_le_mul (mul_le_mul hsum hxy (abs_nonneg _) (by positivity)) (hb1 z) (hb0 z)
            (by positivity)
      _ = 2 * M * K * (B / ε) * dist x y := by ring
  · simp only [semilinearReaction]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _), mul_assoc]
    exact mul_le_mul (hsq x hx) (hLβ ε hε z w) (abs_nonneg _) (sq_nonneg _)
  · simp only [semilinearReaction]
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hb0 z))]
    exact mul_le_mul (hsq x hx) (hb1 z) (hb0 z) (sq_nonneg _)

/-- For `C^∞` `Q` and a reaction profile `β`, `(x, z) ↦ Q(x)² β_ε(z)` is `C^∞`. -/
theorem contDiff_semilinearReaction {Q : E d → ℝ} {β : ℝ → ℝ} (hQ : ContDiff ℝ ∞ Q)
    (hβ : IsReactionProfile β) (ε : ℝ) :
    ContDiff ℝ ∞ (fun q : E d × ℝ ↦ semilinearReaction Q β ε q.1 q.2) :=
  ((hQ.comp contDiff_fst).pow 2).mul
    (((hβ.contDiff.comp (contDiff_id.div_const ε)).div_const ε).comp contDiff_snd)

/-- For continuous `Q` and a reaction profile `β`, `(x, z) ↦ Q(x)² β_ε(z)` is continuous. -/
theorem continuous_semilinearReaction {Q : E d → ℝ} {β : ℝ → ℝ} (hQ : Continuous Q)
    (hβ : IsReactionProfile β) (ε : ℝ) :
    Continuous (fun q : E d × ℝ ↦ semilinearReaction Q β ε q.1 q.2) :=
  ((hQ.comp continuous_fst).pow 2).mul ((hβ.continuous_betaEps ε).comp continuous_snd)

end PerronVariational

end
