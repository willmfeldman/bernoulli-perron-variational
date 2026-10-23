/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
public import PerronVariational.Basic.BV
public import PerronVariational.Inner.InnerVarCompactness
public import PerronVariational.Foundations.IVSigmaH

/-!
# Registry: results of Kriventsov–Weiss on inner variational solutions

This file collects the results from the literature on inner variational solutions that are used in
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper").

Reference: D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, 545–591, doi:10.1002/cpa.22226. Its results are stated for `Q ≡ 1`; the paper asserts
that they carry over to Lipschitz `Q` with positive bounds, which is how they are stated here.
All items assume `2 ≤ d`, as Kriventsov–Weiss and its Lean formalization do. The paper works in
`d ≥ 2` throughout (`Setting.two_le`); for `d = 1` the problem is trivial.

* `Registry.innerVar_dichotomy` (Kriventsov–Weiss, Thm 1.2(i)).
* `highDensitySet`, `Registry.highDensitySet_relClosed` (Kriventsov–Weiss, Prop 3.5) and
  `Registry.isViscSolution_diff_highDensitySet` (Kriventsov–Weiss, Lemma 8.3).
* These three are proved in bernoulli-rectifiability v0.2.0 (Lake package `inner_variational`,
  the Lean formalization of Kriventsov–Weiss, for Lipschitz coefficients). The bridges are in
  `Foundations/IVSolution.lean`, `Foundations/IVViscosity.lean` and `Foundations/IVSigmaH.lean`.
* `Registry.innerVar_compactness_of_gradient_bound` (the paper's
  [Lemma 2.14](#AFS:l.inner-compactness-stability), `l.inner-compactness-stability`;
  Kriventsov–Weiss, proof of Thm 9.3; D. Jerison and N. Kamburov, *Structure of one-phase free
  boundaries in the plane*, Int. Math. Res. Not. IMRN 2016, no. 19, 5922–5987,
  doi:10.1093/imrn/rnv339, Prop 4.2), as in the paper. It is proved here, as
  `InnerVarCompactness.innerVar_compactness_of_gradient_bound` (`Inner/InnerVarCompactness.lean`);
  the perimeter bound it needs (the paper's [Lemma 2.13](#AFS:l.perimeter-bound)) is
  `PerimeterBound.exists_totalVariationOn_le` (`Stationary/PerimeterBound.lean`), from
  Kriventsov–Weiss, Lemma 3.3 in bernoulli-rectifiability v0.4.2. Weyl's lemma enters through
  `Analysis/WeylWeakGradient.lean`, which applies Weyl's lemma from viscosity-solution-theory
  v0.2.0. `Registry.innerVar_compactness` is the earlier form with an extra perimeter hypothesis,
  kept as a corollary for existing call sites.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal Gradient

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- The set of free boundary points of highest density (paper, proof of
[Lemma 2.12](#AFS:l.inner-variational-implies-subsoln)):
`Σ^H = {x ∈ ∂{u > 0} ∩ U : |{χ = 1} ∩ B_r(x)| / |B_r| → 1 as r → 0⁺}`. -/
def highDensitySet (u χ : E d → ℝ) (U : Set (E d)) : Set (E d) :=
  {x ∈ freeBoundary u U |
    Tendsto (fun r ↦ volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0) (𝓝 1)}

namespace Registry

/-- **Kriventsov–Weiss dichotomy.** Let `U` be open and connected, `Q` Lipschitz on
`U` with `0 < c ≤ Q ≤ C` on `U`, and `(u, χ)` an inner variational solution of
[(1.1)](#AFS:e.bernoulli-basic) in `U` ([Def 2.11](#AFS:d.stationary-inner)). Then either `u ≡ 0`
in `U` and `χ = 1` a.e. in `U`, or `χ = 1_{u > 0}` a.e. in `U`.

A result from the literature: Kriventsov–Weiss, Theorem 1.2(i) (for `Q ≡ 1`; the paper asserts
the extension to Lipschitz `Q`). The paper uses it in the proofs of
[Lemma 2.12](#AFS:l.inner-variational-implies-subsoln) and of
[Lemma 2.16](#AFS:l.directionalStable), Step 2.

Proved in bernoulli-rectifiability v0.2.0 (`Singular.chi_eq_indicator_of_localQ`), through the
bridge `Foundations.innerVar_dichotomy_of_iv` (`Foundations/IVSigmaH.lean`). -/
theorem innerVar_dichotomy {U : Set (E d)} {Q u χ : E d → ℝ} (hd : 2 ≤ d) (hU : IsOpen U)
    (hUc : IsConnected U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (h : IsInnerVarSolution U Q u χ) :
    ((∀ x ∈ U, u x = 0) ∧ ∀ᵐ x ∂(volume.restrict U), χ x = 1) ∨
      ∀ᵐ x ∂(volume.restrict U), χ x = (posSet u U).indicator 1 x :=
  Foundations.innerVar_dichotomy_of_iv hd hU hUc hQ hQpos hQb h

/-- **`Σ^H` is relatively closed in `U`.** Let `U` be open, `Q` Lipschitz on `U`
with `0 < c ≤ Q ≤ C` on `U`, and `(u, χ)` an inner variational solution of
[(1.1)](#AFS:e.bernoulli-basic) in `U`. Then the high-density set `Σ^H` is closed in `U`.

A result from the literature: Kriventsov–Weiss, Proposition 3.5 (for `Q ≡ 1`). The paper uses it
in the proof of [Lemma 2.12](#AFS:l.inner-variational-implies-subsoln).

Proved in bernoulli-rectifiability v0.2.0
(`IsVariationalSolutionQ.closure_sigmaHQ_inter_subset` and `mem_sigmaHQ_iff_frontier_inter`),
through the bridge `Foundations.highDensitySet_relClosed_of_iv`. -/
theorem highDensitySet_relClosed {U : Set (E d)} {Q u χ : E d → ℝ} (hd : 2 ≤ d) (hU : IsOpen U)
    (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (h : IsInnerVarSolution U Q u χ) :
    closure (highDensitySet u χ U) ∩ U ⊆ highDensitySet u χ U :=
  Foundations.highDensitySet_relClosed_of_iv hd hU hQ hQpos hQb h

/-- **Viscosity property off `Σ^H`.** Under the hypotheses of
`highDensitySet_relClosed`, `u` is a viscosity solution ([Def 2.1](#AFS:d.stationary-viscosity)) of
[(1.1)](#AFS:e.bernoulli-basic) in the open set `U \ Σ^H`.

A result from the literature: Kriventsov–Weiss, Lemma 8.3 (for `Q ≡ 1`). The paper uses it in
the proof of [Lemma 2.12](#AFS:l.inner-variational-implies-subsoln).

Proved in bernoulli-rectifiability v0.2.0
(`IsVariationalSolutionQ.isViscositySolutionQ_diff_sigmaHQ`), through the bridge
`Foundations.isViscSolution_diff_highDensitySet_of_iv`. -/
theorem isViscSolution_diff_highDensitySet {U : Set (E d)} {Q u χ : E d → ℝ} (hd : 2 ≤ d)
    (hU : IsOpen U)
    (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (h : IsInnerVarSolution U Q u χ) :
    IsViscSolution (U \ highDensitySet u χ U) Q u :=
  Foundations.isViscSolution_diff_highDensitySet_of_iv hd hU hQ hQpos hQb h

/-- **Compactness of inner variational solutions (paper,
[Lemma 2.14](#AFS:l.inner-compactness-stability), `l.inner-compactness-stability`).** Let
`U` be open, `Q` Lipschitz on `U` with `0 < c ≤ Q ≤ C` on `U`, and `(u_k, χ_k)` inner variational
solutions of [(1.1)](#AFS:e.bernoulli-basic) in `U` such that for every `V ⊂⊂ U`:
`sup_k ‖u_k‖_{L^∞(V)} < ∞` and `sup_k ‖∇u_k‖_{L^∞(V)} < ∞`. Then along a subsequence `k_j`,
`u_{k_j} → u` locally uniformly in `U`, `∇u_{k_j} → ∇u` in `L²_loc(U)`, `χ_{k_j} → χ` in
`L¹_loc(U)`, and `(u, χ)` is an inner variational solution of [(1.1)](#AFS:e.bernoulli-basic) in
`U`.

The gradient bound is stated pointwise at every point of `V` (`∇` is `0` at points of
non-differentiability); for locally Lipschitz `u_k` this is equivalent to the `L^∞(V)` bound.
The perimeter control on `χ_k` comes from the paper's [Lemma 2.13](#AFS:l.perimeter-bound)
(`PerimeterBound.exists_totalVariationOn_le`).

A result from the literature: Kriventsov–Weiss, first paragraph of the proof of Theorem 9.3;
Jerison–Kamburov, Proposition 4.2. Proved here:
`InnerVarCompactness.innerVar_compactness_of_gradient_bound` (`Inner/InnerVarCompactness.lean`). -/
theorem innerVar_compactness_of_gradient_bound {U : Set (E d)} {Q : E d → ℝ} (hd : 2 ≤ d)
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (u χ : ℕ → E d → ℝ)
    (h : ∀ k, IsInnerVarSolution U Q (u k) (χ k))
    (hbdd : ∀ V, CompactlyContained V U → ∃ M : ℝ, ∀ k, ∀ x ∈ V, |u k x| ≤ M)
    (hLip : ∀ V, CompactlyContained V U → ∃ L : ℝ, ∀ k, ∀ x ∈ V, ‖∇ (u k) x‖ ≤ L) :
    ∃ (φ : ℕ → ℕ) (u₀ χ₀ : E d → ℝ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun j ↦ u (φ j)) u₀ atTop U ∧
      TendstoLpLoc 2 volume U (fun j ↦ ∇ (u (φ j))) (∇ u₀) atTop ∧
      TendstoLpLoc 1 volume U (fun j ↦ χ (φ j)) χ₀ atTop ∧
      IsInnerVarSolution U Q u₀ χ₀ :=
  InnerVarCompactness.innerVar_compactness_of_gradient_bound hd hU hQ hQpos hQb u χ h hbdd hLip

/-- [Lemma 2.14](#AFS:l.inner-compactness-stability) with an additional local perimeter bound
`sup_k ∫_V |∇χ_k| < ∞` (the earlier form of the registry statement; the hypothesis `hPer` is not
needed, see `innerVar_compactness_of_gradient_bound`). Kept for existing call sites. -/
theorem innerVar_compactness {U : Set (E d)} {Q : E d → ℝ} (hd : 2 ≤ d) (hU : IsOpen U)
    (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (u χ : ℕ → E d → ℝ)
    (h : ∀ k, IsInnerVarSolution U Q (u k) (χ k))
    (hbdd : ∀ V, CompactlyContained V U → ∃ M : ℝ, ∀ k, ∀ x ∈ V, |u k x| ≤ M)
    (hLip : ∀ V, CompactlyContained V U → ∃ L : ℝ, ∀ k, ∀ x ∈ V, ‖∇ (u k) x‖ ≤ L)
    (hPer : ∀ V, CompactlyContained V U → ∃ P : ℝ, ∀ k,
      totalVariationOn V (χ k) ≤ ENNReal.ofReal P) :
    ∃ (φ : ℕ → ℕ) (u₀ χ₀ : E d → ℝ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun j ↦ u (φ j)) u₀ atTop U ∧
      TendstoLpLoc 2 volume U (fun j ↦ ∇ (u (φ j))) (∇ u₀) atTop ∧
      TendstoLpLoc 1 volume U (fun j ↦ χ (φ j)) χ₀ atTop ∧
      IsInnerVarSolution U Q u₀ χ₀ :=
  InnerVarCompactness.innerVar_compactness hd hU hQ hQpos hQb u χ h hbdd hLip hPer

end Registry

end PerronVariational

end
