/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Autonomous scalar ODEs by inversion of the time map

For a continuous vector field `F : ℝ → ℝ` with `0 < F ≤ K`, the autonomous ODE `T' = F(T)`,
`T(0) = a`, has the global solution `T = G⁻¹`, where `G(z) = ∫ₐᶻ dw / F(w)` is the *time map*.
This is the construction used in the proofs of Lemmas A.2 and A.3 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981.
It avoids ODE existence theory: `G` is a `C¹` strictly increasing bijection of `ℝ`
(since `G' = 1/F ≥ 1/K`), and the inverse function theorem in one variable gives `T' = F(T)`.

If moreover `F` is `C^n`, a bootstrap of `T' = F ∘ T` gives `T ∈ C^{n+1}`.
-/

open Set Filter Topology
open scoped ContDiff

@[expose] public section

namespace PerronVariational

/-- The time map `G(z) = ∫ₐᶻ dw / F(w)` of the autonomous ODE `T' = F(T)`. -/
noncomputable def odeTimeMap (F : ℝ → ℝ) (a z : ℝ) : ℝ := ∫ w in a..z, (F w)⁻¹

/-- The solution of the autonomous ODE `T' = F(T)`, `T(0) = a`, defined as the inverse of the
time map `odeTimeMap F a` (meaningful when `F` is continuous with `0 < F ≤ K`; see
`odeSol_hasDerivAt`). -/
noncomputable def odeSol (F : ℝ → ℝ) (a : ℝ) : ℝ → ℝ := Function.invFun (odeTimeMap F a)

section ODE

variable {F : ℝ → ℝ} {K a : ℝ}

theorem odeTimeMap_hasDerivAt (hF : Continuous F) (hpos : ∀ t, 0 < F t) (z : ℝ) :
    HasDerivAt (odeTimeMap F a) (F z)⁻¹ z :=
  ((hF.inv₀ fun t ↦ (hpos t).ne').integral_hasStrictDerivAt a z).hasDerivAt

theorem odeTimeMap_self : odeTimeMap F a a = 0 := by simp [odeTimeMap]

theorem odeTimeMap_strictMono (hF : Continuous F) (hpos : ∀ t, 0 < F t) :
    StrictMono (odeTimeMap F a) :=
  strictMono_of_deriv_pos fun z ↦ by
    rw [(odeTimeMap_hasDerivAt hF hpos z).deriv]; exact inv_pos.2 (hpos z)

/-- `z ↦ G(z) - z / K` is monotone: the time map grows at least at rate `1/K`. -/
theorem odeTimeMap_sub_monotone (hF : Continuous F) (hpos : ∀ t, 0 < F t)
    (hK : ∀ t, F t ≤ K) : Monotone fun z ↦ odeTimeMap F a z - z / K := by
  have hK0 : 0 < K := (hpos 0).trans_le (hK 0)
  have hd : ∀ z, HasDerivAt (fun z ↦ odeTimeMap F a z - z / K) ((F z)⁻¹ - 1 / K) z := fun z ↦
    (odeTimeMap_hasDerivAt hF hpos z).sub ((hasDerivAt_id z).div_const K)
  refine monotone_of_deriv_nonneg (fun z ↦ (hd z).differentiableAt) fun z ↦ ?_
  rw [(hd z).deriv, sub_nonneg, one_div]
  exact inv_anti₀ (hpos z) (hK z)

theorem odeTimeMap_surjective (hF : Continuous F) (hpos : ∀ t, 0 < F t)
    (hK : ∀ t, F t ≤ K) : Function.Surjective (odeTimeMap F a) := by
  have hK0 : 0 < K := (hpos 0).trans_le (hK 0)
  have hmono := odeTimeMap_sub_monotone (a := a) hF hpos hK
  have hcont : Continuous (odeTimeMap F a) :=
    continuous_iff_continuousAt.2 fun z ↦ (odeTimeMap_hasDerivAt hF hpos z).continuousAt
  refine hcont.surjective ?_ ?_
  · -- `G z ≥ G a + (z - a)/K` for `z ≥ a`
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-(a / K))
      (Tendsto.atTop_div_const hK0 tendsto_id))
    filter_upwards [eventually_ge_atTop a] with z hz
    have := hmono hz
    simp only [odeTimeMap_self, zero_sub] at this
    simp only [id]
    linarith
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_atBot_add_const_right _ (-(a / K))
      (Tendsto.atBot_div_const hK0 tendsto_id))
    filter_upwards [eventually_le_atBot a] with z hz
    have := hmono hz
    simp only [odeTimeMap_self, zero_sub] at this
    simp only [id]
    linarith

theorem odeTimeMap_odeSol (hF : Continuous F) (hpos : ∀ t, 0 < F t) (hK : ∀ t, F t ≤ K)
    (s : ℝ) : odeTimeMap F a (odeSol F a s) = s :=
  Function.rightInverse_invFun (odeTimeMap_surjective hF hpos hK) s

theorem odeSol_odeTimeMap (hF : Continuous F) (hpos : ∀ t, 0 < F t) (z : ℝ) :
    odeSol F a (odeTimeMap F a z) = z :=
  Function.leftInverse_invFun (odeTimeMap_strictMono hF hpos).injective z

theorem odeSol_zero (hF : Continuous F) (hpos : ∀ t, 0 < F t) : odeSol F a 0 = a := by
  simpa [odeTimeMap_self] using odeSol_odeTimeMap (a := a) hF hpos a

theorem odeSol_strictMono (hF : Continuous F) (hpos : ∀ t, 0 < F t) (hK : ∀ t, F t ≤ K) :
    StrictMono (odeSol F a) := by
  intro s t hst
  have hG := odeTimeMap_strictMono (a := a) hF hpos
  rw [← hG.lt_iff_lt, odeTimeMap_odeSol hF hpos hK, odeTimeMap_odeSol hF hpos hK]
  exact hst

theorem odeSol_continuous (hF : Continuous F) (hpos : ∀ t, 0 < F t) (hK : ∀ t, F t ≤ K) :
    Continuous (odeSol F a) :=
  (odeSol_strictMono hF hpos hK).monotone.continuous_of_surjective fun z ↦
    ⟨_, odeSol_odeTimeMap hF hpos z⟩

/-- The inverse of the time map solves the autonomous ODE `T' = F(T)`. -/
theorem odeSol_hasDerivAt (hF : Continuous F) (hpos : ∀ t, 0 < F t) (hK : ∀ t, F t ≤ K)
    (s : ℝ) : HasDerivAt (odeSol F a) (F (odeSol F a s)) s := by
  have h := HasDerivAt.of_local_left_inverse (odeSol_continuous (a := a) hF hpos hK).continuousAt
    (odeTimeMap_hasDerivAt hF hpos (odeSol F a s)) (inv_ne_zero (hpos _).ne')
    (Eventually.of_forall fun y ↦ odeTimeMap_odeSol hF hpos hK y)
  rwa [inv_inv] at h

theorem odeSol_deriv (hF : Continuous F) (hpos : ∀ t, 0 < F t) (hK : ∀ t, F t ≤ K) :
    deriv (odeSol F a) = F ∘ odeSol F a :=
  funext fun s ↦ (odeSol_hasDerivAt hF hpos hK s).deriv

end ODE

/-! ### Bootstrap regularity -/

/-- Bootstrap: if `T' = F ∘ T` everywhere and `F ∈ C^n`, then `T ∈ C^{n+1}`. -/
theorem contDiff_succ_of_hasDerivAt_comp {F T : ℝ → ℝ} (hT : ∀ s, HasDerivAt T (F (T s)) s) :
    ∀ n : ℕ, ContDiff ℝ n F → ContDiff ℝ (n + 1) T := by
  have hdT : deriv T = F ∘ T := funext fun s ↦ (hT s).deriv
  have hTd : Differentiable ℝ T := fun s ↦ (hT s).differentiableAt
  intro n
  induction n with
  | zero =>
    intro hF
    rw [Nat.cast_zero, zero_add, contDiff_one_iff_deriv, hdT]
    exact ⟨hTd, hF.continuous.comp hTd.continuous⟩
  | succ n ih =>
    intro hF
    have hTn : ContDiff ℝ (n + 1) T := ih (hF.of_le (by exact_mod_cast Nat.le_succ n))
    rw [contDiff_succ_iff_deriv, hdT]
    refine ⟨hTd, by simp, ?_⟩
    exact_mod_cast hF.comp (by exact_mod_cast hTn)

/-- Bootstrap to `C^∞`: if `T' = F ∘ T` everywhere and `F ∈ C^∞`, then `T ∈ C^∞`. -/
theorem contDiff_infty_of_hasDerivAt_comp {F T : ℝ → ℝ} (hT : ∀ s, HasDerivAt T (F (T s)) s)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ T :=
  contDiff_infty.2 fun n ↦ (contDiff_succ_of_hasDerivAt_comp hT n
    (hF.of_le (by exact_mod_cast le_top))).of_le (by exact_mod_cast Nat.le_succ n)

end PerronVariational

end
