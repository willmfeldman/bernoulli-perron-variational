/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
public import PerronVariational.Foundations.Glue
public import PerronVariational.Foundations.IVBlowup

/-!
# Registry: blow-up analysis for Cor 1.2

Results from the literature used only in the proof sketch of Cor 1.2 of F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the
Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper").

* `Registry.locallyLipschitzOn_of_isViscSolution` (interior Lipschitz estimate,
  Caffarelli–Salsa, Lemma 11.19). Proved in elliptic-bernoulli-foundations v0.1.0.
* `Registry.blowup_homogeneous` (Weiss monotonicity ⇒ blow-up limits of inner variational
  solutions are 1-homogeneous global inner variational solutions), and its sequence form
  `Registry.blowup_homogeneous_seq`. Proved in bernoulli-rectifiability v0.2.0.
* `Registry.classification_homogeneous_planar` (1-homogeneous global inner variational solutions
  in the plane, Jerison–Kamburov, §5). Proved in elliptic-bernoulli-foundations v0.1.0.
* `Registry.isClassicalNear_of_flat` (ε-regularity: flatness ⇒ `C^{1,γ}` free boundary,
  Caffarelli; De Silva). Proved in elliptic-bernoulli-foundations v0.1.0.

References.
* L. A. Caffarelli and S. Salsa, *A geometric approach to free boundary problems*, Graduate
  Studies in Mathematics 68, AMS, 2005, doi:10.1090/gsm/068.
* G. S. Weiss, *Partial regularity for weak solutions of an elliptic free boundary problem*,
  Comm. Partial Differential Equations 23 (1998), no. 3–4, 439–455,
  doi:10.1080/03605309808821352.
* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591,
  doi:10.1002/cpa.22226.
* D. Jerison and N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math.
  Res. Not. IMRN 2016, no. 19, 5922–5987, doi:10.1093/imrn/rnv339.
* L. A. Caffarelli, *A Harnack inequality approach to the regularity of free boundaries. I.
  Lipschitz free boundaries are `C^{1,α}`*, Rev. Mat. Iberoamericana 3 (1987), no. 2, 139–162,
  doi:10.4171/RMI/47; *II. Flat free boundaries are Lipschitz*, Comm. Pure Appl. Math. 42
  (1989), no. 1, 55–78, doi:10.1002/cpa.3160420105.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free
  Bound. 13 (2011), no. 2, 223–238, doi:10.4171/IFB/255.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

namespace Registry

variable {d : ℕ}

/-- **Interior Lipschitz estimate for viscosity solutions.** Under the standing
assumptions (`S : Setting d`), a viscosity solution (Def 2.1) `u` of (1.1) in `U` is locally
Lipschitz in `U` (qualitative form of the interior estimate).

A result from the literature: Caffarelli–Salsa, Lemma 11.19. Paper: proof sketch of Cor 1.2.

Proved in elliptic-bernoulli-foundations v0.1.0 (`locallyLipschitzOn_of_isViscSolution`), through
the bridge `Foundations.locallyLipschitzOn_of_isViscSolution`. -/
theorem locallyLipschitzOn_of_isViscSolution (S : Setting d) {u : E d → ℝ}
    (hu : IsViscSolution S.U S.Q u) : LocallyLipschitzOn S.U u :=
  Foundations.locallyLipschitzOn_of_isViscSolution S hu

/-- **Homogeneity of blow-ups (Weiss).** Under the standing assumptions, let
`(u, χ)` be an inner variational solution of (1.1) in `U` and `x₀ ∈ ∂{u > 0} ∩ U`. Every blow-up
limit `v` of `u` at `x₀` (`u_{x₀, r_n} → v` locally uniformly for some `r_n → 0⁺`) is homogeneous
of degree one, and `(v, χ₀)` is a global inner variational solution with constant coefficient
`Q(x₀)` for some `χ₀`.

A result from the literature: Weiss (1998), the monotonicity formula and its consequence that
blow-up limits are homogeneous of degree one, for the variable coefficient `Q ∈ C^{0,1}` as in the
paper ("with coefficient `Q ∈ C^{0,1} ⊂ C^γ`"); the existence of `χ₀` and the passage to the limit
use the compactness of inner variational solutions (`Registry.innerVar_compactness`, with the
perimeter bounds of Kriventsov–Weiss). Paper: proof sketch of Cor 1.2.

Proved in bernoulli-rectifiability v0.2.0, through the bridge
`Foundations.blowup_homogeneous_of_iv` (`Foundations/IVBlowup.lean`), from the sequence form
below. -/
theorem blowup_homogeneous (S : Setting d) {u χ : E d → ℝ} (h : IsInnerVarSolution S.U S.Q u χ)
    {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u S.U) {v : E d → ℝ} (hv : IsBlowupLimit u x₀ v) :
    (∀ t : ℝ, 0 < t → ∀ y : E d, v (t • y) = t * v y) ∧
      ∃ χ₀ : E d → ℝ, IsInnerVarSolution univ (fun _ ↦ S.Q x₀) v χ₀ :=
  Foundations.blowup_homogeneous_of_iv S h hx₀ hv

/-- **Homogeneity of blow-ups, sequence form with convergence of `χ`.** Under the hypotheses of
`blowup_homogeneous`, let `u_{x₀, r_n} → v` locally uniformly along an explicit sequence
`r_n → 0⁺`. Then `v` is homogeneous of degree one, and along a subsequence `r_{φ(n)}` the rescaled
phases `χ(x₀ + r_{φ(n)} y)` converge in `L¹_loc(ℝᵈ)` to some `χ₀` such that `(v, χ₀)` is a global
inner variational solution with constant coefficient `Q(x₀)`.

This is how the cited theory produces `χ₀`: the perimeter bound of Kriventsov–Weiss, Lemma 3.3,
is scale-invariant, so the rescaled `χ` are precompact in `L¹_loc` (BV compactness). The inner
variation identity passes to the limit by the compactness of inner variational solutions
(Kriventsov–Weiss, proof of Thm 9.3; Jerison–Kamburov, Prop 4.2; `Registry.innerVar_compactness`),
and homogeneity follows from Weiss's monotonicity formula. It is used for the flatness step of
Cor 1.2(ii) in the largest-subsolution case, which the paper's sketch leaves incomplete:
non-degeneracy at free boundary points (Thm B.1) does not exclude a far side on which `u` is small
and positive, and this form of the blow-up rules that out.

A result from the literature: as for `blowup_homogeneous`, together with Kriventsov–Weiss,
Lemma 3.3 and the proof of Thm 9.3, and Jerison–Kamburov, Proposition 4.2.

Proved in bernoulli-rectifiability v0.2.0 (`IsVariationalSolutionQ.exists_blowup_limit` and
`IsVariationalSolutionQ.blowup_homogeneous`), through the bridge
`Foundations.blowup_homogeneous_seq_of_iv` (`Foundations/IVBlowup.lean`). -/
theorem blowup_homogeneous_seq (S : Setting d) {u χ : E d → ℝ}
    (h : IsInnerVarSolution S.U S.Q u χ) {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u S.U)
    {v : E d → ℝ} {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hv : TendstoLocallyUniformly (fun n ↦ blowup u x₀ (r n)) v atTop) :
    (∀ t : ℝ, 0 < t → ∀ y : E d, v (t • y) = t * v y) ∧
      ∃ (φ : ℕ → ℕ) (χ₀ : E d → ℝ), StrictMono φ ∧
        TendstoLpLoc 1 volume univ (fun n y ↦ χ (x₀ + r (φ n) • y)) χ₀ atTop ∧
        IsInnerVarSolution univ (fun _ ↦ S.Q x₀) v χ₀ :=
  Foundations.blowup_homogeneous_seq_of_iv S h hx₀ hr hr0 hv

/-- **Classification of 1-homogeneous global inner variational solutions in the plane.** Let `q > 0`
and `(v, χ)` a global inner variational solution in `ℝ²` with constant coefficient `q`, with `v`
homogeneous of degree one. Then for some unit vector `e`, either
* `v(y) = q (y · e)₊` and `χ = 1_{y · e > 0}` a.e. (half-plane solution), or
* `v(y) = α |y · e|` for some `α ≥ 0` and `χ = 1` a.e. (two-plane solutions, including `v ≡ 0`
  with `χ ≡ 1`), or
* `v ≡ 0` and `χ = 0` a.e.

The paper's list omits the last alternative (`v ≡ 0`, `χ ≡ 0`, which is an inner variational
solution); here it is included, because it occurs. In the smallest-supersolution case of Cor 1.2
it is excluded by non-degeneracy of the smallest supersolution.

A result from the literature: Jerison–Kamburov, Section 5. Paper: proof sketch of Cor 1.2.

Proved in elliptic-bernoulli-foundations v0.1.0 (`classification_homogeneous_planar`), through
the bridge `Foundations.classification_homogeneous_planar`. -/
theorem classification_homogeneous_planar {q : ℝ} (hq : 0 < q) {v χ : E 2 → ℝ}
    (h : IsInnerVarSolution univ (fun _ ↦ q) v χ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ y : E 2, v (t • y) = t * v y) :
    ∃ e : E 2, ‖e‖ = 1 ∧
      (((∀ y, v y = q * max (inner ℝ y e) 0) ∧
          ∀ᵐ y, χ y = {z : E 2 | 0 < inner ℝ z e}.indicator 1 y) ∨
        (∃ α : ℝ, 0 ≤ α ∧ (∀ y, v y = α * |inner ℝ y e|) ∧ ∀ᵐ y, χ y = 1) ∨
        ((∀ y, v y = 0) ∧ ∀ᵐ y, χ y = 0)) :=
  Foundations.classification_homogeneous_planar hq h hhom

/-- **ε-regularity (flat free boundaries are `C^{1,γ}`).** Under the standing
assumptions, there is `ε̄ > 0` (depending on the setting) such that: if `u` is a viscosity
solution of (1.1) in `U`, `x₀ ∈ ∂{u > 0} ∩ U`, `0 < r ≤ ε̄` with `B_r(x₀) ⊆ U`, and `u` is
`ε̄`-flat in `B_r(x₀)` in direction `e`:
`Q(x₀) ((y - x₀) · e - ε̄ r)₊ ≤ u(y) ≤ Q(x₀) ((y - x₀) · e + ε̄ r)₊` for `y ∈ B_r(x₀)`,
then `u` is a classical solution near `x₀` (`IsClassicalNear`: `C^{1,γ}` free boundary, `u`
harmonic in `{u > 0}` with `|∇u| = Q` classically on the free boundary).

This is the *flatness* form of the ε-regularity theorem. The paper applies ε-regularity at
points where *some blow-up is a half-plane solution*; here we assume two-sided flatness, because
locally uniform convergence to a half-plane only gives the lower half of the flatness condition.
The upper half (`u = 0` on `{(y - x₀) · e < -ε̄ r}`) additionally requires Hausdorff convergence of
the free boundaries, which the proof of Cor 1.2 obtains from non-degeneracy (smallest case) and
from `blowup_homogeneous_seq` (largest case).

A result from the literature: Caffarelli (1987, 1989); De Silva (2011), Theorem 1.1 (flatness ⇒
`C^{1,α}` for Hölder `Q`), plus regularity of `u` up to the `C^{1,α}` free boundary. Paper: proof
sketch of Cor 1.2.

Proved in elliptic-bernoulli-foundations v0.1.0 (`isClassicalNear_of_flat`, following De Silva),
through the bridge `Foundations.isClassicalNear_of_flat`. That proof needs only `Q` Lipschitz on
`U` and `0 < Qmin ≤ Q` on `U`, and does not use boundary Schauder regularity: it gets the gradient
up to the free boundary from interior estimates plus pointwise `C^{1,α}` flatness. -/
theorem isClassicalNear_of_flat (S : Setting d) :
    ∃ εbar > 0, ∀ (u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsViscSolution S.U S.Q u →
      x₀ ∈ freeBoundary u S.U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ S.U →
      (∀ y ∈ ball x₀ r, S.Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ S.Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsClassicalNear S.U S.Q u x₀ :=
  Foundations.isClassicalNear_of_flat S

end Registry

end PerronVariational

end
