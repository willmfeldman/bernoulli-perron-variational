/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Semilinear
public import PerronVariational.Basic.Touching
public import PerronVariational.Semilinear.ParabolicBasicBridge

/-!
# Registry: the semilinear equation

Viscosity notions for the semilinear equation `∂ₜu = Δu - Q(x)² β_ε(u)` (first line of (3.4) in
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
the Bernoulli one-phase problem*, arXiv:2609.14981, "the paper") and its stationary version
`Δv = Q(x)² β_ε(v)`, and the well-posedness facts from the literature cited at the beginning of
the paper's Appendix A.

References: O. A. Ladyženskaja, V. A. Solonnikov and N. N. Ural'ceva, *Linear and quasilinear
equations of parabolic type*, Translations of Mathematical Monographs 23, AMS, 1968 ("LSU");
G. M. Lieberman, *Second order parabolic differential equations*, World Scientific, 1996,
doi:10.1142/3302; L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in
Mathematics 19, AMS, 2010, doi:10.1090/gsm/019; M. G. Crandall, H. Ishii and P.-L. Lions,
*User's guide to viscosity solutions of second order partial differential equations*, Bull. Amer.
Math. Soc. (N.S.) 27 (1992), 1–67, doi:10.1090/S0273-0979-1992-00266-5.

* `IsSemilinearViscSubStat`, `IsSemilinearViscSuperStat`: stationary continuous viscosity
  sub/supersolutions (used in Lemma A.4 and in the attainment argument of Lemma A.9).
* `IsSemilinearViscSubOn`, `IsSemilinearViscSuperOn`: parabolic continuous viscosity
  sub/supersolutions in `U × I`, touching relative to the parabolic past `{s ≤ t}`.
* `Registry.semilinear_exists`, `Registry.semilinear_unique`,
  `Registry.semilinear_contDiffOn_of_contDiff`: classical well-posedness (LSU Ch. V,
  Lieberman Ch. IX). Proved in parabolic-basic-theory v0.1.0.
* `Registry.semilinear_continuousOn_gradₓ_of_contDiff`: `∇ₓu` continuous up to `t = 0` for
  smooth `Q`, `g` (LSU Ch. IV §10). Proved in parabolic-basic-theory v0.1.0.
* `Registry.isSemilinearViscSubOn_of_solOn`, `Registry.isSemilinearViscSuperOn_of_solOn`:
  classical `C^{2,1}` solutions are viscosity solutions. Proved in parabolic-basic-theory v0.1.0.
  The comparison principle itself is in `PerronVariational.Registry.Comparison`.
  The energy dissipation inequality `Registry.semilinear_energy_dissipation` is in
  `PerronVariational.Registry.SemilinearDissipation`.

The results from parabolic-basic-theory v0.1.0 are those of `ParabolicBasic.MainTheorems`, with
`f(x, z) = Q(x)² β_ε(z)`; see `PerronVariational.Semilinear.ParabolicBasicBridge`. The viscosity
notions below agree with those of parabolic-basic-theory by `rfl`
(`isSemilinearViscSubOn_iff_pb`, `isSemilinearViscSuperOn_iff_pb`).

Test functions are globally `C²` functions (of `x`, resp. of `(x, t)`); this is equivalent to
local test functions by a cutoff, since all conditions are local. For the
parabolic notions, globally `C²` test functions give the same class of viscosity sub- and
supersolutions as `C^{2,1}` test functions (every element of the parabolic semijet is realized
by a `C²` function touching relative to the parabolic past).
-/

open Set Filter Topology
open scoped ContDiff Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Stationary semilinear viscosity notions -/

/-- Stationary continuous viscosity subsolution of `Δv = Q(x)² β_ε(v)` in `U` (globally `C²` test
functions): `v` is continuous on `U`, and whenever a `C²` function `ψ` touches `v` from above in `U`
at `x ∈ U`, `Q(x)² β_ε(v(x)) ≤ Δψ(x)`.

Used in Lemma A.4, where `(Φ_{ε,θ}(g))₊` is shown to be a stationary subsolution of (3.4), and in
the proof of Lemma A.9. A stationary subsolution is a
time-independent parabolic subsolution of `∂ₜu = Δu - Q² β_ε(u)`. -/
def IsSemilinearViscSubStat (U : Set (E d)) (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ)
    (v : E d → ℝ) : Prop :=
  ContinuousOn v U ∧ ∀ ψ : E d → ℝ, ContDiff ℝ 2 ψ → ∀ x ∈ U, TouchesAbove ψ v U x →
    Q x ^ 2 * betaEps β ε (v x) ≤ Δ ψ x

/-- Stationary continuous viscosity supersolution of `Δv = Q(x)² β_ε(v)` in `U` (globally `C²` test
functions): `v` is continuous on `U`, and whenever a `C²` function `ψ` touches `v` from below in `U`
at `x ∈ U`, `Δψ(x) ≤ Q(x)² β_ε(v(x))`.

Used in Lemma A.4 (supersolution case with `Ψ_{ε,θ̂}`) and in the proof of Lemma A.9 (the
harmonic function `h_ε` is a stationary supersolution). -/
def IsSemilinearViscSuperStat (U : Set (E d)) (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ)
    (v : E d → ℝ) : Prop :=
  ContinuousOn v U ∧ ∀ ψ : E d → ℝ, ContDiff ℝ 2 ψ → ∀ x ∈ U, TouchesBelow ψ v U x →
    Δ ψ x ≤ Q x ^ 2 * betaEps β ε (v x)

/-! ### Parabolic semilinear viscosity notions -/

/-- Parabolic continuous viscosity subsolution of `∂ₜu = Δu - Q(x)² β_ε(u)` in `U × I`
(test functions are globally `C²` in `(x, t)`): `u` is continuous on `U × I`, and whenever
a `C²` function `ψ` touches `u` from above at `p = (x, t) ∈ U × I`, relative to the parabolic past
`(U × I) ∩ {s ≤ t}`, then `∂ₜψ(p) - Δₓψ(p) ≤ -Q(x)² β_ε(u(p))`.

Touching relative to the parabolic past (rather than a full space-time neighbourhood) makes this
notion *stronger* than the standard one, so comparison (`Registry.semilinear_comparison`) for it
follows from the standard theory. Used in Prop 5.3 and Appendix A (Lemma A.1, Lemma A.9,
Cor A.12). -/
def IsSemilinearViscSubOn (U : Set (E d)) (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ) (I : Set ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ U ×ˢ I,
    TouchesAbove ψ u ((U ×ˢ I) ∩ {q | q.2 ≤ p.2}) p →
      dₜ ψ p - lapₓ ψ p ≤ -(Q p.1 ^ 2 * betaEps β ε (u p))

/-- Parabolic continuous viscosity supersolution of `∂ₜu = Δu - Q(x)² β_ε(u)` in `U × I` (globally
`C²` test functions): `u` is continuous on `U × I`, and whenever a `C²` function `ψ` touches `u`
from below at `p = (x, t) ∈ U × I`, relative to the parabolic past `(U × I) ∩ {s ≤ t}`, then
`-Q(x)² β_ε(u(p)) ≤ ∂ₜψ(p) - Δₓψ(p)`. -/
def IsSemilinearViscSuperOn (U : Set (E d)) (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ) (I : Set ℝ)
    (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ 2 ψ → ∀ p ∈ U ×ˢ I,
    TouchesBelow ψ u ((U ×ˢ I) ∩ {q | q.2 ≤ p.2}) p →
      -(Q p.1 ^ 2 * betaEps β ε (u p)) ≤ dₜ ψ p - lapₓ ψ p

/-- The parabolic viscosity subsolutions here are those of parabolic-basic-theory, with
`f(x, z) = Q(x)² β_ε(z)` (`rfl`). -/
theorem isSemilinearViscSubOn_iff_pb {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ}
    {I : Set ℝ} {u : E d × ℝ → ℝ} :
    IsSemilinearViscSubOn U Q β ε I u ↔
      ParabolicBasic.IsSemilinearViscSubOn U (semilinearReaction Q β ε) I u :=
  Iff.rfl

/-- The parabolic viscosity supersolutions here are those of parabolic-basic-theory, with
`f(x, z) = Q(x)² β_ε(z)` (`rfl`). -/
theorem isSemilinearViscSuperOn_iff_pb {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ}
    {I : Set ℝ} {u : E d × ℝ → ℝ} :
    IsSemilinearViscSuperOn U Q β ε I u ↔
      ParabolicBasic.IsSemilinearViscSuperOn U (semilinearReaction Q β ε) I u :=
  Iff.rfl

namespace Registry

/-! ### Classical well-posedness -/

/-- **Semilinear well-posedness: existence.** Let `U` satisfy the standing assumptions (bounded,
connected, `C²` boundary; `Q` Lipschitz on `Ū` with `0 < Q_min ≤ Q ≤ Q_max`), `β` a reaction profile
(3.5) and `ε > 0`. For time-independent parabolic data `g` that is Lipschitz on `Ū`, the problem
(3.4) has a solution `u ∈ C(Ū × [0, ∞)) ∩ C^{2,1}(U_∞)` in the sense of `IsSemilinearSolution`
(classical in `U_∞`, `u = g` on `∂_P U_∞`). The paper's Prop 3.8 asserts `u_ε ∈ C^∞(U_∞)`; here
solutions are classical `C^{2,1}`, because `Q` is only Lipschitz, and the appendix itself gets `C^∞`
only for smooth `Q`.

A result from the literature: LSU, Chapter V (§6, Theorem 6.1, together with approximation of
the Lipschitz data); Lieberman, Chapter IX (the Cauchy–Dirichlet problem for semilinear
equations with Lipschitz nonlinearity). The nonlinearity `f(x, z) = -Q(x)² β_ε(z)` is bounded
and Lipschitz in `z` uniformly in `x`; the data are compatible because they are time-independent.

Paper: beginning of Appendix A ("standard existence and uniqueness theory ... yields a solution
`u_ε ∈ C(Ū × [0, ∞)) ∩ C^{2,1}(U_∞)`"); used for Prop 3.8.
Proved in parabolic-basic-theory v0.1.0: `ParabolicBasic.semilinear_exists` with
`f(x, z) = Q(x)² β_ε(z)`, with `hfx`, `hfz`, `hfb` from `semilinearReactionHyp` on `Ū`. -/
theorem semilinear_exists (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ}
    (hε : 0 < ε) {g : E d → ℝ} (hg : ∃ L, LipschitzOnWith L g (closure S.U)) :
    ∃ u : E d × ℝ → ℝ, IsSemilinearSolution S.U S.Q β ε g u :=
  have hf := semilinearReactionHyp hβ hε S.isBounded.isCompact_closure S.lip
  ParabolicBasic.semilinear_exists S.isOpen S.isBounded S.c2 hf.holder_x hf.lip_z hf.bounded hg

/-- **Semilinear well-posedness: uniqueness.** Under the hypotheses of `semilinear_exists`, two
solutions of (3.4) with the same Lipschitz data `g` agree on `Ū × [0, ∞)`.

A result from the literature: LSU Chapter V (uniqueness via the maximum principle for the
linearized equation); Lieberman, Chapter IX; equivalently a consequence of the comparison
principle `Registry.semilinear_comparison`. Paper: beginning of Appendix A ("existence and
uniqueness"), used in Lemma A.1 ("the unique classical solution").
Proved in parabolic-basic-theory v0.1.0: `ParabolicBasic.semilinear_unique` with
`f(x, z) = Q(x)² β_ε(z)`, with `hfx`, `hfz` from `semilinearReactionHyp` on `Ū` (the Lipschitz
hypothesis on `g` is not needed). -/
theorem semilinear_unique (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ}
    (hε : 0 < ε) {g : E d → ℝ} (_hg : ∃ L, LipschitzOnWith L g (closure S.U))
    {u v : E d × ℝ → ℝ} (hu : IsSemilinearSolution S.U S.Q β ε g u)
    (hv : IsSemilinearSolution S.U S.Q β ε g v) :
    ∀ p ∈ closure S.U ×ˢ Ici (0 : ℝ), u p = v p :=
  have hf := semilinearReactionHyp hβ hε S.isBounded.isCompact_closure S.lip
  ParabolicBasic.semilinear_unique S.isOpen S.isBounded hf.holder_x hf.lip_z
    (isSemilinearSolution_iff_pb.1 hu) (isSemilinearSolution_iff_pb.1 hv)

/-- **Semilinear well-posedness: interior smoothness.** If `Q` is `C^∞`, `β` is a reaction profile,
`ε > 0`, `U ⊆ ℝᵈ` and `I ⊆ ℝ` are open, and `u` is a classical `C^{2,1}` solution of
`∂ₜu = Δu - Q² β_ε(u)` in `U × I`, then `u` is `C^∞` in `U × I`.

A result from the literature: interior parabolic Schauder estimates and bootstrap; LSU
Chapter IV §10 and Chapter V §6; Lieberman Chapter IV (Theorem 4.9) and Chapter IX. Paper:
beginning of Appendix A ("If `Q` is smooth then the interior regularity can be upgraded to
`u_ε ∈ C^∞(U_∞)`"), used for the Bernstein argument (Props A.5–A.6), which approximates `Q` by
smooth coefficients.
Proved in parabolic-basic-theory v0.1.0: `ParabolicBasic.semilinear_contDiffOn_of_contDiff` with
`f(x, z) = Q(x)² β_ε(z)`, using `contDiff_semilinearReaction`. -/
theorem semilinear_contDiffOn_of_contDiff {U : Set (E d)} {I : Set ℝ} {Q : E d → ℝ}
    {β : ℝ → ℝ} {ε : ℝ} {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : IsOpen I)
    (hQ : ContDiff ℝ ∞ Q) (hβ : IsReactionProfile β) (_hε : 0 < ε)
    (hu : IsSemilinearSolOn U Q β ε I u) :
    ContDiffOn ℝ ∞ u (U ×ˢ I) :=
  ParabolicBasic.semilinear_contDiffOn_of_contDiff hU hI (contDiff_semilinearReaction hQ hβ ε)
    (isSemilinearSolOn_iff_pb.1 hu)

/-! ### Gradient regularity up to the initial time -/

/-- **Regularity of the gradient up to `t = 0` for smooth data.** If `Q` and the data `g` are
`C^∞`, the spatial gradient of the solution of (3.4) is continuous on `U × [0, ∞)`.

This is interior (in space) parabolic Schauder regularity up to the initial time, an extension of
`semilinear_contDiffOn_of_contDiff`, which gives regularity only in `U_∞`. The paper uses it
silently in the proof of Lemma A.7 ("mollification argument": "∇u_ε is continuous at t = 0 on
V" for smooth data).

A result from the literature: LSU, Chapter IV §10 (local estimates near the lower base of the
cylinder); Lieberman, Chapter IV.
Proved in parabolic-basic-theory v0.1.0: `ParabolicBasic.semilinear_continuousOn_gradₓ_of_contDiff`
with `f(x, z) = Q(x)² β_ε(z)`, which needs only continuous `f` and `C²` data. -/
theorem semilinear_continuousOn_gradₓ_of_contDiff (S : Setting d) {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {ε : ℝ} (_hε : 0 < ε) (hQ : ContDiff ℝ ∞ S.Q) {g : E d → ℝ}
    (hg : ContDiff ℝ ∞ g) {u : E d × ℝ → ℝ} (hu : IsSemilinearSolution S.U S.Q β ε g u) :
    ContinuousOn (gradₓ u) (S.U ×ˢ Ici 0) :=
  ParabolicBasic.semilinear_continuousOn_gradₓ_of_contDiff S.isOpen
    (continuous_semilinearReaction hQ.continuous hβ ε) (hg.of_le (WithTop.coe_le_coe.2 le_top))
    (isSemilinearSolution_iff_pb.1 hu)

/-! ### Classical solutions are viscosity solutions -/

/-- **Classical ⇒ viscosity subsolution.** If `U` is open, every `t ∈ I` has a
left neighbourhood `(t - δ, t] ⊆ I`, and `u` is a classical `C^{2,1}` solution of
`∂ₜu = Δu - Q² β_ε(u)` in `U × I` (`IsSemilinearSolOn`), then `u` is a viscosity subsolution in
`U × I`.

A standard result (first- and second-order conditions at a one-sided local maximum of `u - ψ`);
see Crandall–Ishii–Lions, §8. Paper: implicit throughout Appendix A (e.g. Lemma A.1 and the proof
of Lemma A.9, where the classical solution `u_ε` is compared with viscosity barriers).
Proved in parabolic-basic-theory v0.1.0: `ParabolicBasic.isSemilinearViscSubOn_of_solOn` with
`f(x, z) = Q(x)² β_ε(z)`. -/
theorem isSemilinearViscSubOn_of_solOn {U : Set (E d)} {I : Set ℝ} {Q : E d → ℝ} {β : ℝ → ℝ}
    {ε : ℝ} {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U Q β ε I u) : IsSemilinearViscSubOn U Q β ε I u :=
  ParabolicBasic.isSemilinearViscSubOn_of_solOn hU hI (isSemilinearSolOn_iff_pb.1 hu)

/-- **Classical ⇒ viscosity supersolution.** Same hypotheses as
`isSemilinearViscSubOn_of_solOn`; then `u` is a viscosity supersolution in `U × I`.

A standard result; Crandall–Ishii–Lions, §8. Paper: as for `isSemilinearViscSubOn_of_solOn`.
Proved in parabolic-basic-theory v0.1.0: `ParabolicBasic.isSemilinearViscSuperOn_of_solOn` with
`f(x, z) = Q(x)² β_ε(z)`. -/
theorem isSemilinearViscSuperOn_of_solOn {U : Set (E d)} {I : Set ℝ} {Q : E d → ℝ} {β : ℝ → ℝ}
    {ε : ℝ} {u : E d × ℝ → ℝ} (hU : IsOpen U) (hI : ∀ t ∈ I, ∃ δ > 0, Ioc (t - δ) t ⊆ I)
    (hu : IsSemilinearSolOn U Q β ε I u) : IsSemilinearViscSuperOn U Q β ε I u :=
  ParabolicBasic.isSemilinearViscSuperOn_of_solOn hU hI (isSemilinearSolOn_iff_pb.1 hu)

end Registry

end PerronVariational

end
