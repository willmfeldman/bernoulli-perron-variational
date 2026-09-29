/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolutionQ
public import PerronVariational.Defs.Stationary
import InnerVariational.Statements.LipschitzQ
import PerronVariational.Foundations.IVSolution
import PerronVariational.Foundations.IVViscosity
import PerronVariational.Stationary.ViscosityLocal

/-!
# The dichotomy and the high-density set, from bernoulli-rectifiability

Part of the Lean formalization of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper"). The
paper cites D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness
for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591,
doi:10.1002/cpa.22226 for two facts about inner variational solutions: the dichotomy
(Kriventsov–Weiss, Thm 1.2(i)) and the closedness of the high-density part `Σ^H` of the free
boundary together with the viscosity property off `Σ^H` (Kriventsov–Weiss, Prop 3.5 and Lemma 8.3).
Here they are proved from the dependency bernoulli-rectifiability v0.2.0 (Lake package
`inner_variational`), the Lean formalization of Kriventsov–Weiss with a Lipschitz coefficient `Q`.

* `sep_freeBoundary_inter_eq_sigmaHQ`: on an open `B ⊆ U` on which `(u, χ)` is a
  `Q`-variational solution in the sense of bernoulli-rectifiability, the high-density set of the
  paper (from the proof of Lemma 2.9; `highDensitySet u χ U`, written out here because it is
  defined in `Registry/`) meets `B` in `sigmaHQ B Q u χ`. This is the density characterization
  `IsVariationalSolutionQ.mem_sigmaHQ_iff_frontier_inter` together with the locality of the
  frontier (`frontier_posSet_inter_iff`).
* `innerVar_dichotomy_of_iv`: `Singular.chi_eq_indicator_of_localQ`, with the local solutions of
  `exists_ball_isVariationalSolutionQ`.
* `highDensitySet_relClosed_of_iv`: `closure_sigmaHQ_inter_subset` on a ball around each point of
  `U`, through `sep_freeBoundary_inter_eq_sigmaHQ`.
* `isViscSolution_diff_highDensitySet_of_iv`: `isViscositySolutionQ_diff_sigmaHQ` on balls,
  `sep_freeBoundary_inter_eq_sigmaHQ` and `isViscSolution_of_isViscositySolutionQ`, glued by the
  locality of Def 2.1 (`isViscSuper_of_locally`, `isViscSub_of_locally`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped NNReal

@[expose] public section

namespace PerronVariational

namespace Foundations

variable {d : ℕ}

/-- Coefficient bounds on `U` restrict to the `QBounds` of bernoulli-rectifiability on any `B ⊆ U`.
-/
theorem qBounds_of_subset {U B : Set (E d)} {Q : E d → ℝ} (hBU : B ⊆ U) {K : ℝ≥0}
    (hK : LipschitzOnWith K Q U) {c C : ℝ} (hc : 0 < c) (hcQ : ∀ x ∈ U, c ≤ Q x)
    (hQC : ∀ x ∈ U, Q x ≤ C) : InnerVariational.QBounds B Q K c C :=
  ⟨hK.mono hBU, hc, fun x hx ↦ hcQ x (hBU hx), fun x hx ↦ hQC x (hBU hx)⟩

/-- **Locality of the free boundary.** For an open `B ⊆ U` and `x ∈ B`, `x` lies on the frontier of
`{u > 0} ∩ U` if and only if it lies on the frontier of `{u > 0} ∩ B`. -/
theorem frontier_posSet_inter_iff {U B : Set (E d)} {u : E d → ℝ} (hB : IsOpen B)
    (hBU : B ⊆ U) {x : E d} (hx : x ∈ B) :
    x ∈ frontier (posSet u U) ↔ x ∈ frontier {y | y ∈ B ∧ 0 < u y} := by
  have hs : {y | y ∈ B ∧ 0 < u y} = posSet u U ∩ B := by
    ext y
    simp only [posSet, mem_setOf_eq, mem_inter_iff]
    exact ⟨fun h ↦ ⟨⟨hBU h.1, h.2⟩, h.1⟩, fun h ↦ ⟨h.2, h.1.2⟩⟩
  have h' := Set.ext_iff.1 (frontier_inter_open_inter (s := posSet u U) hB) x
  simp only [mem_inter_iff, hx, and_true] at h'
  rw [hs, h']

/-- **The high-density set.** On an open `B ⊆ U` on which `(u, χ)` is a `Q`-variational solution
in the sense of bernoulli-rectifiability, the high-density set (paper, proof of Lemma 2.9) meets
`B` in `sigmaHQ B Q u χ`. -/
theorem sep_freeBoundary_inter_eq_sigmaHQ [NeZero d] {U B : Set (E d)} {Q u χ : E d → ℝ}
    {C L : ℝ≥0} {c C' : ℝ} (hB : IsOpen B) (hBU : B ⊆ U)
    (hQ : InnerVariational.QBounds B Q L c C')
    (h : InnerVariational.IsVariationalSolutionQ B C Q u χ) :
    {x ∈ freeBoundary u U | Tendsto (fun r ↦ volume ({y | χ y = 1} ∩ ball x r) /
      volume (ball x r)) (𝓝[>] 0) (𝓝 1)} ∩ B = InnerVariational.sigmaHQ B Q u χ := by
  ext x
  rw [h.mem_sigmaHQ_iff_frontier_inter hQ]
  simp only [mem_inter_iff, mem_setOf_eq, freeBoundary]
  constructor
  · rintro ⟨⟨⟨hfr, -⟩, hT⟩, hxB⟩
    exact ⟨hxB, (frontier_posSet_inter_iff hB hBU hxB).1 hfr, hT⟩
  · rintro ⟨hxB, hfr, hT⟩
    exact ⟨⟨⟨(frontier_posSet_inter_iff hB hBU hxB).2 hfr, hBU hxB⟩, hT⟩, hxB⟩

/-- **The Kriventsov–Weiss dichotomy**, from bernoulli-rectifiability. See
`Registry.innerVar_dichotomy`. -/
theorem innerVar_dichotomy_of_iv {U : Set (E d)} {Q u χ : E d → ℝ} (hd : 2 ≤ d)
    (hU : IsOpen U) (hUc : IsConnected U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (h : IsInnerVarSolution U Q u χ) :
    ((∀ x ∈ U, u x = 0) ∧ ∀ᵐ x ∂(volume.restrict U), χ x = 1) ∨
      ∀ᵐ x ∂(volume.restrict U), χ x = (posSet u U).indicator 1 x := by
  obtain ⟨K, hK⟩ := hQ
  obtain ⟨c, hc, hcQ⟩ := hQpos
  obtain ⟨C', hC'⟩ := hQb
  have hloc : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ (C L : ℝ≥0) (c C' : ℝ),
      InnerVariational.QBounds V Q L c C' ∧ InnerVariational.IsVariationalSolutionQ V C Q u χ := by
    intro x hx
    obtain ⟨δ, hδ, hδU, C, hsol⟩ := exists_ball_isVariationalSolutionQ h hU hx
    exact ⟨ball x δ, isOpen_ball, mem_ball_self hδ, hδU, C, K, c, C',
      qBounds_of_subset hδU hK hc hcQ hC', hsol⟩
  rcases InnerVariational.Singular.chi_eq_indicator_of_localQ hd hUc hloc with h1 | h2
  · exact Or.inl h1
  · right
    filter_upwards [h2, ae_restrict_mem hU.measurableSet] with x hx hxU
    rw [hx]
    by_cases hux : 0 < u x
    · rw [InnerVariational.posIndicator_of_pos hux, indicator_of_mem (show x ∈ posSet u U from
        ⟨hxU, hux⟩)]
      rfl
    · rw [InnerVariational.posIndicator_of_nonpos (not_lt.1 hux),
        indicator_of_notMem (show x ∉ posSet u U from fun h ↦ hux h.2)]

/-- **`Σ^H` is relatively closed**, from bernoulli-rectifiability. See
`Registry.highDensitySet_relClosed`. -/
theorem highDensitySet_relClosed_of_iv {U : Set (E d)} {Q u χ : E d → ℝ} (hd : 2 ≤ d)
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (h : IsInnerVarSolution U Q u χ) :
    closure {x ∈ freeBoundary u U | Tendsto (fun r ↦ volume ({y | χ y = 1} ∩ ball x r) /
        volume (ball x r)) (𝓝[>] 0) (𝓝 1)} ∩ U ⊆
      {x ∈ freeBoundary u U | Tendsto (fun r ↦ volume ({y | χ y = 1} ∩ ball x r) /
        volume (ball x r)) (𝓝[>] 0) (𝓝 1)} := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨K, hK⟩ := hQ
  obtain ⟨c, hc, hcQ⟩ := hQpos
  obtain ⟨C', hC'⟩ := hQb
  rintro x ⟨hxcl, hxU⟩
  obtain ⟨δ, hδ, hδU, C, hsol⟩ := exists_ball_isVariationalSolutionQ h hU hxU
  have hQB := qBounds_of_subset hδU hK hc hcQ hC'
  have heq := sep_freeBoundary_inter_eq_sigmaHQ isOpen_ball hδU hQB hsol
  have hx' : x ∈ closure (InnerVariational.sigmaHQ (ball x δ) Q u χ) := by
    rw [← heq, inter_comm]
    exact isOpen_ball.inter_closure ⟨mem_ball_self hδ, hxcl⟩
  have := hsol.closure_sigmaHQ_inter_subset hQB ⟨hx', mem_ball_self hδ⟩
  rw [← heq] at this
  exact this.1

/-- **Viscosity solution off `Σ^H`**, from bernoulli-rectifiability. See
`Registry.isViscSolution_diff_highDensitySet`. -/
theorem isViscSolution_diff_highDensitySet_of_iv {U : Set (E d)} {Q u χ : E d → ℝ}
    (hd : 2 ≤ d) (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (h : IsInnerVarSolution U Q u χ) :
    IsViscSolution (U \ {x ∈ freeBoundary u U | Tendsto (fun r ↦
      volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0) (𝓝 1)}) Q u := by
  haveI : NeZero d := ⟨by omega⟩
  set H := {x ∈ freeBoundary u U | Tendsto (fun r ↦
      volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0) (𝓝 1)} with hH
  have hclosed := highDensitySet_relClosed_of_iv hd hU hQ hQpos hQb h
  obtain ⟨K, hK⟩ := hQ
  obtain ⟨c, hc, hcQ⟩ := hQpos
  obtain ⟨C', hC'⟩ := hQb
  have hWo : IsOpen (U \ H) := by
    have : U \ H = U ∩ (closure H)ᶜ := by
      ext x
      simp only [mem_diff, mem_inter_iff, mem_compl_iff]
      exact ⟨fun hx ↦ ⟨hx.1, fun hcl ↦ hx.2 (hclosed ⟨hcl, hx.1⟩)⟩,
        fun hx ↦ ⟨hx.1, fun hxH ↦ hx.2 (subset_closure hxH)⟩⟩
    rw [this]
    exact hU.inter isClosed_closure.isOpen_compl
  have hloc : ∀ x ∈ U \ H, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U \ H ∧ IsViscSolution W Q u := by
    rintro x ⟨hxU, hxH⟩
    obtain ⟨δ, hδ, hδU, C, hsol⟩ := exists_ball_isVariationalSolutionQ h hU hxU
    have hQB := qBounds_of_subset hδU hK hc hcQ hC'
    have heq := sep_freeBoundary_inter_eq_sigmaHQ isOpen_ball hδU hQB hsol
    have hW : ball x δ \ InnerVariational.sigmaHQ (ball x δ) Q u χ = ball x δ ∩ (U \ H) := by
      rw [← heq]
      ext y
      simp only [mem_diff, mem_inter_iff]
      exact ⟨fun hy ↦ ⟨hy.1, hδU hy.1, fun hyH ↦ hy.2 ⟨hyH, hy.1⟩⟩,
        fun hy ↦ ⟨hy.1, fun hyH ↦ hy.2.2 hyH.1⟩⟩
    have hvisc := hsol.isViscositySolutionQ_diff_sigmaHQ hd hQB
    rw [hW] at hvisc
    exact ⟨ball x δ ∩ (U \ H), isOpen_ball.inter hWo, ⟨mem_ball_self hδ, hxU, hxH⟩,
      inter_subset_right, isViscSolution_of_isViscositySolutionQ (isOpen_ball.inter hWo) hvisc⟩
  refine ⟨isViscSuper_of_locally hWo fun x hx ↦ ?_, isViscSub_of_locally fun x hx ↦ ?_⟩
  · obtain ⟨W, hW, hxW, hWU, hsol⟩ := hloc x hx
    exact ⟨W, hW, hxW, hWU, u, hsol.1, fun _ _ ↦ rfl⟩
  · obtain ⟨W, hW, hxW, hWU, hsol⟩ := hloc x hx
    exact ⟨W, hW, hxW, hWU, u, hsol.2, fun _ _ ↦ rfl⟩

end Foundations

end PerronVariational

end
