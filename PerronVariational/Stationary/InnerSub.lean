/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Registry.KriventsovWeiss
import PerronVariational.Main.Directional
import PerronVariational.Stationary.ConeDensity

/-!
# Inner variational solutions are viscosity subsolutions (Lemma 2.9)

**Lemma 2.9** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: if `(u, χ)` is an inner
variational solution of (1.1) in `U` then `u` is a viscosity subsolution of (1.1) in `U`.

The proof follows the paper, using two results of
D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), 545–591,
arXiv:2306.10131 (proved in bernoulli-rectifiability v0.2.0, stated in
`Registry/KriventsovWeiss.lean`):
* the dichotomy [Kriventsov–Weiss, Theorem 1.2(i)] (`Registry.innerVar_dichotomy`): `u ≡ 0` or
  `χ = 1_{u > 0}` a.e.;
* [Kriventsov–Weiss, Lemma 8.3] (`Registry.isViscSolution_diff_highDensitySet`): `u` is a
  viscosity solution in `U \ Σ^H`.

A touching point `x₀ ∉ Σ^H` is a touching point for `U \ Σ^H` (the positivity set is unchanged,
since `Σ^H ⊆ ∂{u > 0}` and `{u > 0}` is open), so the second result applies; the relative
closedness of `Σ^H` ([Kriventsov–Weiss, Proposition 3.5]) is not needed for this. At
`x₀ ∈ Σ^H`, if `Δφ(x₀) < 0` then `{φ < 0}` contains a rescaled
copy `x₀ + r • K` of a fixed open set for all small `r` (`Stationary/ConeDensity.lean`), while
`{φ < 0} ⊆ {u = 0}` near `x₀` and `χ = 1_{u > 0}` a.e.; this contradicts the density `1` of
`{χ = 1}` at `x₀`.

The hypotheses on `U` and `Q` (`U` open and connected, `Q` Lipschitz on `U` with positive lower
and finite upper bounds) are those of the two results of Kriventsov–Weiss.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- Removing a subset of the free boundary from `U` does not change the positivity set. -/
theorem posSet_diff_of_subset_frontier {U T : Set (E d)} {u : E d → ℝ}
    (hP : IsOpen (posSet u U)) (hT : T ⊆ frontier (posSet u U)) :
    posSet u (U \ T) = posSet u U := by
  ext y
  refine ⟨fun hy ↦ ⟨hy.1.1, hy.2⟩, fun hy ↦ ⟨⟨hy.1, fun hyT ↦ ?_⟩, hy.2⟩⟩
  have := hT hyT
  rw [frontier, hP.interior_eq] at this
  exact this.2 hy

/-- **Lemma 2.9**, at a point of `Σ^H`: if `φ₊`
touches `u` from above in `\overline{{u > 0}} ∩ U` at `x₀ ∈ Σ^H` and `χ = 1_{u > 0}` a.e. in
`U`, then `Δφ(x₀) ≥ 0` (proof of Lemma 2.9). -/
theorem laplacian_nonneg_of_touchesAbove_highDensitySet {U : Set (E d)} {u χ φ : E d → ℝ}
    {x : E d} (hU : IsOpen U) (hu : ContinuousOn u U) (hnn : ∀ y ∈ U, 0 ≤ u y)
    (hχ : ∀ᵐ y ∂(volume.restrict U), χ y = (posSet u U).indicator 1 y)
    (hφ : ContDiff ℝ ∞ φ) (hxH : x ∈ highDensitySet u χ U)
    (hx : TouchesAbove (fun y ↦ max (φ y) 0) u (closure (posSet u U) ∩ U) x) :
    0 ≤ Δ φ x := by
  set P := posSet u U
  have hP : IsOpen P := isOpen_posSet hU hu
  -- `u(x₀) = 0`, hence `φ(x₀) ≤ 0`
  have hxP : x ∉ P := by
    have := hxH.1.1
    rw [frontier, hP.interior_eq] at this
    exact this.2
  have hux : u x = 0 :=
    le_antisymm (not_lt.1 fun h ↦ hxP ⟨hxH.1.2, h⟩) (hnn x hxH.1.2)
  have hφx : φ x ≤ 0 := by
    have := hx.2.1
    rw [hux] at this
    exact this ▸ le_max_left _ _
  -- near `x₀`, `{φ < 0}` misses `{u > 0}`
  obtain ⟨ε₁, hε₁, hε₁c⟩ := Metric.eventually_nhds_iff_ball.1
    (eventually_nhdsWithin_iff.1 hx.2.2)
  obtain ⟨ε₂, hε₂, hε₂U⟩ := Metric.isOpen_iff.1 hU x hxH.1.2
  set ρ := min ε₁ ε₂
  have hρ : 0 < ρ := lt_min hε₁ hε₂
  have hneg : ∀ y ∈ ball x ρ, φ y < 0 → y ∉ P := by
    intro y hy hφy hyP
    have h1 : u y ≤ max (φ y) 0 :=
      hε₁c y (ball_subset_ball (min_le_left _ _) hy) ⟨subset_closure hyP, hyP.1⟩
    rw [max_eq_right hφy.le] at h1
    exact hyP.2.not_ge h1
  set A := {y | φ y < 0}
  have hA : NullMeasurableSet A :=
    (isOpen_lt hφ.continuous continuous_const).measurableSet.nullMeasurableSet
  -- `{χ = 1} ∩ {φ < 0}` is null near `x₀`
  have hdisj : ∀ r ≤ ρ, volume ({y | χ y = 1} ∩ A ∩ ball x r) = 0 := by
    intro r hr
    have hae := (ae_restrict_iff' hU.measurableSet).1 hχ
    refine measure_mono_null ?_ (ae_iff.1 hae)
    rintro y ⟨⟨hy1, hyA⟩, hyr⟩ hy
    have hyρ : y ∈ ball x ρ := ball_subset_ball hr hyr
    have hyU : y ∈ U := hε₂U (ball_subset_ball (min_le_right _ _) hyρ)
    have := hy hyU
    rw [indicator_of_notMem (hneg y hyρ hyA), show χ y = 1 from hy1] at this
    exact one_ne_zero this
  by_contra! hΔ
  obtain ⟨K, hK, hKne, hK1, r₀, hr₀, hKneg⟩ : ∃ K : Set (E d), IsOpen K ∧ K.Nonempty ∧
      K ⊆ ball 0 1 ∧ ∃ r₀ > (0 : ℝ), ∀ r ∈ Ioo 0 r₀, ∀ v ∈ K, φ (x + r • v) < 0 := by
    by_cases h0 : fderiv ℝ φ x = 0
    · exact exists_scaled_neg_of_laplacian_neg (hφ.of_le (by norm_cast)) hφx h0 hΔ
    · exact exists_scaled_neg_of_fderiv_ne_zero (hφ.of_le (by norm_cast)) hφx h0
  exact not_tendsto_density_one hA hK hKne hK1 (lt_min hr₀ hρ)
    (fun r hr v hv ↦ hKneg r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩ v hv)
    (hdisj _ (min_le_right _ _)) hxH.2

/-- **Lemma 2.9**. Let `U` be open and
connected, `Q` Lipschitz on `U` with `0 < c ≤ Q ≤ C` on `U`. If `(u, χ)` is an inner variational
solution of (1.1) in `U` (Definition 2.8), then `u` is a viscosity subsolution of (1.1) in `U`
(Definition 2.1(ii)).

Uses the results of Kriventsov–Weiss `Registry.innerVar_dichotomy` and
`Registry.isViscSolution_diff_highDensitySet`. -/
theorem IsInnerVarSolution.isViscSub {U : Set (E d)} {Q u χ : E d → ℝ} (hd : 2 ≤ d)
    (hU : IsOpen U)
    (hUc : IsConnected U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (h : IsInnerVarSolution U Q u χ) : IsViscSub U Q u := by
  have hcont : ContinuousOn u U := h.locLip.continuousOn
  have hP : IsOpen (posSet u U) := isOpen_posSet hU hcont
  refine ⟨hcont, h.nonneg, fun φ hφ x hx ↦ ?_⟩
  by_cases hxH : x ∈ highDensitySet u χ U
  · -- touching in `Σ^H`: the density argument, after the dichotomy of Kriventsov–Weiss
    left
    rcases Registry.innerVar_dichotomy hd hU hUc hQ hQpos hQb h with ⟨hzero, -⟩ | hχ
    · have hempty : posSet u U = ∅ :=
        eq_empty_of_forall_notMem fun y hy ↦ (hzero y hy.1 ▸ hy.2).false
      have := hxH.1.1
      rw [hempty, frontier_empty] at this
      exact this.elim
    · exact laplacian_nonneg_of_touchesAbove_highDensitySet hU hcont h.nonneg hχ hφ hxH hx
  · -- touching off `Σ^H`: [Kriventsov–Weiss, Lemma 8.3]
    have hsub := (Registry.isViscSolution_diff_highDensitySet hd hU hQ hQpos hQb h).2
    have hpos := posSet_diff_of_subset_frontier hP
      (T := highDensitySet u χ U) fun y hy ↦ hy.1.1
    refine hsub.2.2 φ hφ x ⟨?_, hx.2.1, hx.2.2.filter_mono (nhdsWithin_mono _ ?_)⟩
    · rw [hpos]; exact ⟨hx.1.1, hx.1.2, hxH⟩
    · rw [hpos]; exact inter_subset_inter_right _ Set.sdiff_subset

end PerronVariational

end
