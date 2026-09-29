/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Sobolev
public import PerronVariational.Basic.Touching
public import ViscositySolns.Applications.Laplace.Dirichlet
public import ViscositySolns.Applications.Laplace.ExteriorSphere
public import PerronVariational.Analysis.WeylWeakGradient

/-!
# Registry: linear elliptic facts

Results from the literature on the Laplace equation used in F. Abedin, W. M. Feldman,
K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase
problem*, arXiv:2609.14981 ("the paper"). References: D. Gilbarg and N. S. Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics in Mathematics, Springer, 2001,
doi:10.1007/978-3-642-61798-0; L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate
Studies in Mathematics 19, AMS, 2010, doi:10.1090/gsm/019; M. G. Crandall, H. Ishii and
P.-L. Lions, *User's guide to viscosity solutions of second order partial differential
equations*, Bull. Amer. Math. Soc. (N.S.) 27 (1992), 1–67, doi:10.1090/S0273-0979-1992-00266-5.

* `Registry.dirichlet_harmonic_modulus`: the Dirichlet problem for the Laplacian in a bounded
  `C²` domain with Lipschitz data, with a boundary modulus depending only on the Lipschitz
  constant and sup bound of the data (paper, proof of Lemma A.9). Proved in
  viscosity-solution-theory v0.2.0.
* `Registry.harmonic_of_weakly_harmonic` (Weyl's lemma). Proved here as
  `Analysis.harmonic_of_hasWeakGradient` (`Analysis/WeylWeakGradient.lean`), which applies
  Weyl's lemma from viscosity-solution-theory v0.2.0.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff Gradient Laplacian NNReal

@[expose] public section

namespace PerronVariational

namespace Registry

variable {d : ℕ}

/-- **Dirichlet problem with a uniform boundary modulus.** Let `U` be open, bounded, with `C²`
boundary (encoded by a defining function, see `HasC2Boundary`), and let `L ≥ 0`, `M`. There is a
modulus `ϖ` (`ϖ(r) → 0` as `r → 0⁺`) such that for every `g` which is `L`-Lipschitz on `Ū` with
`|g| ≤ M` on `Ū`, there is `h ∈ C(Ū) ∩ C²(U)` harmonic in `U` with `h = g` on `∂U` and
`|h(x) - g(x₀)| ≤ ϖ(|x - x₀|)` for all `x₀ ∈ ∂U`, `x ∈ Ū`.

A result from the literature: Gilbarg–Trudinger, Theorem 2.14 (Perron solvability of the Dirichlet
problem when every boundary point has a barrier, e.g. under the exterior sphere condition, §2.8),
together with the explicit exterior-sphere barrier of §2.8, which gives a modulus depending only on
the uniform exterior-sphere radius of `∂U` and on `L`, `M` (cf. the paper's own barrier `η` in the
proof of Lemma A.9). Proved in viscosity-solution-theory v0.2.0: Perron's method
(Crandall–Ishii–Lions) for the Laplacian with exterior-sphere barriers,
`ViscositySolns.dirichlet_harmonic_modulus_of_uniformExteriorSphere`, and
`ViscositySolns.uniformExteriorSphere_of_contDiff_levelSet` (C² ⇒ uniform exterior sphere); the
modulus is `ϖ t = K √t`. Paper: proof of Lemma A.9 ("Since `U` is a `C²` regular domain there is a
modulus of continuity `ϖ₀` depending only on `L` and `M`"). -/
theorem dirichlet_harmonic_modulus {U : Set (E d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hC2 : HasC2Boundary U) (L : ℝ≥0) (M : ℝ) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ g : E d → ℝ, LipschitzOnWith L g (closure U) → (∀ x ∈ closure U, |g x| ≤ M) →
        ∃ h : E d → ℝ, ContinuousOn h (closure U) ∧ ContDiffOn ℝ 2 h U ∧
          (∀ x ∈ U, Δ h x = 0) ∧ (∀ x ∈ frontier U, h x = g x) ∧
          ∀ x₀ ∈ frontier U, ∀ x ∈ closure U, |h x - g x₀| ≤ ϖ ‖x - x₀‖ :=
  ViscositySolns.dirichlet_harmonic_modulus_of_uniformExteriorSphere hU hUb
    (ViscositySolns.uniformExteriorSphere_of_contDiff_levelSet hUb hC2) L M

/-- **Weyl's lemma.** Let `U` be open and `u` continuous on `U` with a weak gradient `G` in `U`
(carried as explicit data) such that `∫_U G · ∇φ = 0` for every `φ ∈ C_c^∞(U)`. Then `u` is `C^∞`
and harmonic in `U`.

A result from the literature: Weyl's lemma; e.g. Gilbarg–Trudinger, Theorem 8.8 and Corollary 8.11
(interior regularity of weak solutions), or Evans, §6.3.1, Theorem 3 (infinite differentiability in
the interior). Paper: proof of Thm 3.10, Step 2 ("`u_∞` is harmonic in its positivity set", obtained
in weak form), where `Δu_∞ = 0` classically is needed for Def 2.8(i).

Proved here: `Analysis.harmonic_of_hasWeakGradient` (`Analysis/WeylWeakGradient.lean`), which
reduces to distributional harmonicity and applies Weyl's lemma for continuous weakly harmonic
functions from viscosity-solution-theory v0.2.0
(`ViscositySolns.Analysis.weyl_of_weaklyHarmonicOn`). -/
theorem harmonic_of_weakly_harmonic {U : Set (E d)} {u : E d → ℝ} {G : E d → E d}
    (hU : IsOpen U) (hu : ContinuousOn u U) (hG : HasWeakGradient U u G)
    (hweak : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, inner ℝ (G x) (∇ φ x) = 0) :
    ContDiffOn ℝ ∞ u U ∧ ∀ x ∈ U, Δ u x = 0 :=
  Analysis.harmonic_of_hasWeakGradient hU hu hG hweak

end Registry

end PerronVariational

end
