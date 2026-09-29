/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Semilinear
import PerronVariational.Semilinear.Profiles

/-!
# Small helpers shared by the Section 4 files

Helpers for Section 4 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, kept in one small early
module so that the files that need only them do not wait for the semilinear estimates:

* `LocLipₓ`: local spatial Lipschitz continuity on a space-time set (the form of
  `∇u ∈ L^∞_loc` used in Definition 3.7(i)); re-exported by `Inner.SemilinearEstimates`;
* `continuousOn_slice_of_prod`, `IsSemilinearSolOn.continuousOn_lapₓ`: continuity of time slices
  and of the spatial Laplacian of a classical solution;
* `setLIntegral_comp_add_le`: translating the domain of a set lintegral (with the instance
  that `volume` on `E d × ℝ` is an additive Haar measure).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-- Local spatial Lipschitz continuity on a space-time set `Ω`, uniform in time near each point
(the form of `∇u ∈ L^∞_loc` used in Definition 3.7(i)). The paper assumes `∇u ∈ L^∞_loc`; here we
assume local spatial Lipschitz bounds, uniform in time near each point, which is equivalent for
continuous `u`. -/
def LocLipₓ (Ω : Set (E d × ℝ)) (u : E d × ℝ → ℝ) : Prop :=
  ∀ p ∈ Ω, ∃ K : ℝ, ∃ N ∈ 𝓝 p, ∀ q ∈ N, ∀ q' ∈ N, q.2 = q'.2 → |u q - u q'| ≤ K * ‖q.1 - q'.1‖

/-! ### Slices and translations -/

instance : (volume : Measure (E d × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

theorem continuousOn_slice_of_prod {X : Type*} [TopologicalSpace X] {U : Set (E d)} {I : Set ℝ}
    {F : E d × ℝ → X} (hF : ContinuousOn F (U ×ˢ I)) {t : ℝ} (ht : t ∈ I) :
    ContinuousOn (fun x ↦ F (x, t)) U :=
  hF.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hx ↦ ⟨hx, ht⟩

/-- The spatial Laplacian of a classical solution is continuous (from the equation). -/
theorem IsSemilinearSolOn.continuousOn_lapₓ {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {ε : ℝ} {I : Set ℝ} {v : E d × ℝ → ℝ}
    (hv : IsSemilinearSolOn U Q β ε I v) (hQ : ContinuousOn Q U) :
    ContinuousOn (lapₓ v) (U ×ˢ I) := by
  refine (hv.2.2.2.2.2.1.add (((hQ.comp continuousOn_fst fun p hp ↦ hp.1).pow 2).mul
    ((hβ.continuous_betaEps ε).comp_continuousOn hv.1))).congr fun p hp ↦ ?_
  simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  rw [hv.2.2.2.2.2.2 p hp]
  ring

/-- Translating the domain of a set integral: if `A + v ⊆ A'` then
`∫_A F(p + v) ≤ ∫_{A'} F`. -/
theorem setLIntegral_comp_add_le {A A' : Set (E d × ℝ)} (hAm : MeasurableSet A)
    (hA'm : MeasurableSet A') (F : E d × ℝ → ℝ≥0∞) (v : E d × ℝ) (hAA' : ∀ p ∈ A, p + v ∈ A') :
    ∫⁻ p in A, F (p + v) ≤ ∫⁻ q in A', F q := by
  rw [← lintegral_indicator hAm, ← lintegral_indicator hA'm,
    ← lintegral_add_right_eq_self (μ := volume) (A'.indicator F) v]
  refine lintegral_mono fun p ↦ ?_
  by_cases hp : p ∈ A
  · rw [indicator_of_mem hp, indicator_of_mem (hAA' p hp)]
  · rw [indicator_of_notMem hp]
    exact zero_le

end Inner

end PerronVariational

end
