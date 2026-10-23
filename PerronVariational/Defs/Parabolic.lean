/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.KLimit
public import PerronVariational.Basic.BV
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Parabolic solution notions

The parabolic solution notions of [§3](#AFS:s.parabolic_bernoulli) of F. Abedin, W. M. Feldman, K.
Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 ("the paper").

Space-time points are `p : E d × ℝ`. A general time set `I : Set ℝ` is used (the paper uses
`(0, T]` and `(0, ∞)`); `U ×ˢ I` is the space-time domain.

* Parabolic cylinders, parabolic boundaries, admissible cylinders `V × (a, b] ⊂⊂ U × I`.
* The ordering `≺` ([Definition 3.1](#AFS:d.prec-ordering)) and classical strict sub/supersolutions
  (before [Definition 3.3](#AFS:d.parabolic-supersolution)).
* Parabolic viscosity super/sub/solutions ([Definition 3.3](#AFS:d.parabolic-supersolution)).
* Parabolic relaxed subsolutions/solutions ([Definition 3.5](#AFS:d.parabolic-relaxed-subsolution)).
* Time monotonicity (after [Definition 3.5](#AFS:d.parabolic-relaxed-subsolution)).
* Parabolic inner variational solutions ([Definition 3.8](#AFS:d.parabolic-inner)).
* The estimates [(3.12)](#AFS:eqn:diss2)–[(3.14)](#AFS:eqn:chiEst2) of
  [Theorem 3.13](#AFS:t.parabolic-existence) as named predicates.

Test functions are globally smooth on space-time; the paper uses `φ ∈ C^∞(V̄ × [a, b])`. The two
are equivalent by a cutoff argument, since all conditions are local. The classical strict
sub/supersolutions are the paper's, with uniform constants `a₀, δ₀`
(`IsClassicalStrictParaSubWith`). The dependency bernoulli-parabolic-comparison uses a pointwise
form; the resulting parabolic notions agree when `Q` is continuous and positive
(`Parabolic/BernoulliComparisonBridge.lean`).

Note: `E d × ℝ` carries the product (sup) metric; this only enters through the distance
`d_η` in `WeightedPerimeterEst` (a parameter of an arbitrary constant function).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Cylinders and parabolic boundaries -/

/-- The cylinder `V × (a, b]`. -/
def cyl (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) := V ×ˢ Ioc a b

/-- The parabolic boundary `∂_P(V × (a, b]) = (V̄ × {a}) ∪ (∂V × [a, b])`. -/
def parBdry (V : Set (E d)) (a b : ℝ) : Set (E d × ℝ) :=
  (closure V ×ˢ {a}) ∪ (frontier V ×ˢ Icc a b)

/-- `U_∞ = U × (0, ∞)` (paper, [§1.2](#AFS:ss.notation)). -/
def UInf (U : Set (E d)) : Set (E d × ℝ) := U ×ˢ Ioi 0

/-- The parabolic boundary `∂_P U_∞ = (Ū × {0}) ∪ (∂U × [0, ∞))`. -/
def parBdryInf (U : Set (E d)) : Set (E d × ℝ) :=
  (closure U ×ˢ {0}) ∪ (frontier U ×ˢ Ici 0)

/-- The parabolic cylinder `Q_r(x, t) = B_r(x) × (t - r², t]` (paper, [§1.2](#AFS:ss.notation)). -/
def parCyl (x : E d) (t r : ℝ) : Set (E d × ℝ) := ball x r ×ˢ Ioc (t - r ^ 2) t

/-- `V × (a, b] ⊂⊂ U × I` is an admissible test cylinder
([Definition 3.3](#AFS:d.parabolic-supersolution)): `V` is open and bounded, `a < b`, and
`closure (V × (a, b]) = V̄ × [a, b] ⊆ U × I`. -/
def AdmissibleCyl (U : Set (E d)) (I : Set ℝ) (V : Set (E d)) (a b : ℝ) : Prop :=
  IsOpen V ∧ Bornology.IsBounded V ∧ a < b ∧ closure V ×ˢ Icc a b ⊆ U ×ˢ I

/-! ### Positivity sets and the ordering `≺` -/

/-- The space-time positivity set `{u > 0}` inside the domain `Ω`. -/
def posSetP (u : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) : Set (E d × ℝ) := {p ∈ Ω | 0 < u p}

/-- The paper's `u ≺ v on F` ([Definition 3.1](#AFS:d.prec-ordering)): `u ≺_E v on F` with
`E = \overline{{u > 0}}`, where `{u > 0}` is taken inside the domain `Ω` of `u`. -/
def Prec (u v : E d × ℝ → ℝ) (Ω F : Set (E d × ℝ)) : Prop :=
  PrecOn u v (closure (posSetP u Ω)) F

/-! ### Classical strict sub/supersolutions -/

/-- Classical strict subsolution of [(3.1)](#AFS:e.bernoulli-parabolic) on `V̄ × [a, b]` with
constants `a₀, δ₀` (paper, before [Definition 3.3](#AFS:d.parabolic-supersolution)):
`1/2 ≥ a₀, δ₀ > 0`, `φ` is (globally) smooth, and (i) `∂ₜφ - Δφ ≤ -δ₀` in
`{φ > -a₀} ∩ (V̄ × [a, b])`, (ii) `|∇φ|² ≥ (1 + δ₀) Q²` in `{|φ| ≤ a₀} ∩ (V̄ × [a, b])`.
The sets `{φ > -a₀}` and `{|φ| ≤ a₀}` are taken in all of space-time (`φ` is globally defined);
the paper takes `φ` and these sets in an open neighbourhood of `V̄ × [a, b]`, which is
equivalent by a cutoff. -/
structure IsClassicalStrictParaSubWith (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d))
    (a b a₀ δ₀ : ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ φ
  a₀_pos : 0 < a₀
  a₀_le : a₀ ≤ 1 / 2
  δ₀_pos : 0 < δ₀
  δ₀_le : δ₀ ≤ 1 / 2
  heat : ∀ p ∈ {q | -a₀ < φ q} ∩ (closure V ×ˢ Icc a b), dₜ φ p - lapₓ φ p ≤ -δ₀
  grad : ∀ p ∈ {q | |φ q| ≤ a₀} ∩ (closure V ×ˢ Icc a b),
    (1 + δ₀) * Q p.1 ^ 2 ≤ ‖gradₓ φ p‖ ^ 2

/-- Classical strict supersolution of [(3.1)](#AFS:e.bernoulli-parabolic) on `V̄ × [a, b]` with
constants `a₀, δ₀` (paper, before [Definition 3.3](#AFS:d.parabolic-supersolution)):
`1/2 ≥ a₀, δ₀ > 0`, `φ` is (globally) smooth, and (i) `∂ₜφ - Δφ ≥ δ₀` in
`{φ > -a₀} ∩ (V̄ × [a, b])`, (ii) `|∇φ|² ≤ (1 - δ₀) Q²` in `{|φ| ≤ a₀} ∩ (V̄ × [a, b])`.
As for `IsClassicalStrictParaSubWith`, the sets are taken in all of space-time. -/
structure IsClassicalStrictParaSuperWith (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d))
    (a b a₀ δ₀ : ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ φ
  a₀_pos : 0 < a₀
  a₀_le : a₀ ≤ 1 / 2
  δ₀_pos : 0 < δ₀
  δ₀_le : δ₀ ≤ 1 / 2
  heat : ∀ p ∈ {q | -a₀ < φ q} ∩ (closure V ×ˢ Icc a b), δ₀ ≤ dₜ φ p - lapₓ φ p
  grad : ∀ p ∈ {q | |φ q| ≤ a₀} ∩ (closure V ×ˢ Icc a b),
    ‖gradₓ φ p‖ ^ 2 ≤ (1 - δ₀) * Q p.1 ^ 2

/-- Classical strict subsolution of [(3.1)](#AFS:e.bernoulli-parabolic) on `V̄ × [a, b]` (paper,
before [Definition 3.3](#AFS:d.parabolic-supersolution)): a globally smooth `φ` with
`IsClassicalStrictParaSubWith Q φ V a b a₀ δ₀` for some constants `1/2 ≥ a₀, δ₀ > 0`. -/
def IsClassicalStrictParaSub (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ∃ a₀ δ₀ : ℝ, IsClassicalStrictParaSubWith Q φ V a b a₀ δ₀

/-- Classical strict supersolution of [(3.1)](#AFS:e.bernoulli-parabolic) on `V̄ × [a, b]` (paper,
before [Definition 3.3](#AFS:d.parabolic-supersolution)): a globally smooth `φ` with
`IsClassicalStrictParaSuperWith Q φ V a b a₀ δ₀` for some constants `1/2 ≥ a₀, δ₀ > 0`. -/
def IsClassicalStrictParaSuper (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ∃ a₀ δ₀ : ℝ, IsClassicalStrictParaSuperWith Q φ V a b a₀ δ₀

/-! ### Parabolic viscosity solutions ([Definition 3.3](#AFS:d.parabolic-supersolution)) -/

/-- **[Definition 3.3](#AFS:d.parabolic-supersolution)**, supersolution case, with globally smooth
test functions. `u ∈ C(U × I; [0, ∞))` is a supersolution of [(3.1)](#AFS:e.bernoulli-parabolic):
for every admissible cylinder `V × (a, b] ⊂⊂ U × I` and every classical strict subsolution `φ` on
`V̄ × [a, b]` with `φ ≺ u` on `∂_P(V × (a, b])`, also `φ ≺ u` in `V × (a, b]`.
(`φ ≺ u` uses `\overline{{φ > 0}}`, computed in all of space-time.) -/
def IsParaSuper (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSub Q φ V a b → Prec φ u univ (parBdry V a b) →
        Prec φ u univ (cyl V a b)

/-- **[Definition 3.3](#AFS:d.parabolic-supersolution)**, subsolution case, with globally smooth
test functions. `u ∈ C(U × I; [0, ∞))` is a subsolution of [(3.1)](#AFS:e.bernoulli-parabolic): for
every admissible cylinder `V × (a, b] ⊂⊂ U × I` and every classical strict supersolution `φ` on
`V̄ × [a, b]` with `u ≺ φ` on `∂_P(V × (a, b])`, also `u ≺ φ` in `V × (a, b]`.
(`u ≺ φ` uses `\overline{{u > 0}}`, `{u > 0} ⊆ U × I`.) -/
def IsParaSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSuper Q φ V a b → Prec u φ (U ×ˢ I) (parBdry V a b) →
        Prec u φ (U ×ˢ I) (cyl V a b)

/-- **[Definition 3.3](#AFS:d.parabolic-supersolution)**. Parabolic viscosity solution: both a
super- and a subsolution. -/
def IsParaSolution (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  IsParaSuper U Q I u ∧ IsParaSub U Q I u

/-! ### Parabolic relaxed subsolutions ([Definition 3.5](#AFS:d.parabolic-relaxed-subsolution)) -/

/-- **[Definition 3.5](#AFS:d.parabolic-relaxed-subsolution)**, with globally smooth test functions.
For `u ∈ C(U × I; [0, ∞))` and `E` closed in `Ū × Ī` with `{u > 0} ⊆ E`, `(u, E)` is a relaxed
subsolution: for every admissible cylinder `V × (a, b] ⊂⊂ U × I` and classical strict supersolution
`φ` on `V̄ × [a, b]` with `u ≺_E φ` on `∂_P(V × (a, b])`, also `u ≺_E φ` in `V × (a, b]`. -/
def IsParaRelaxedSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧ IsClosed Eset ∧
    Eset ⊆ closure U ×ˢ closure I ∧ posSetP u (U ×ˢ I) ⊆ Eset ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSuper Q φ V a b → PrecOn u φ Eset (parBdry V a b) →
        PrecOn u φ Eset (cyl V a b)

/-- **[Definition 3.5](#AFS:d.parabolic-relaxed-subsolution)**. `(u, E)` is a relaxed viscosity
solution: `u` is a (standard) supersolution and `(u, E)` is a relaxed subsolution. -/
def IsParaRelaxedSolution (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) : Prop :=
  IsParaSuper U Q I u ∧ IsParaRelaxedSub U Q I u Eset

/-! ### Time monotonicity -/

/-- The time slice `E_t = {x : (x, t) ∈ E}` (paper, after
[Definition 3.5](#AFS:d.parabolic-relaxed-subsolution)). -/
def timeSlice (Eset : Set (E d × ℝ)) (t : ℝ) : Set (E d) := {x | (x, t) ∈ Eset}

/-- `t ↦ u(x, t)` is nondecreasing on `I` for every `x ∈ A`. -/
def MonotoneInTime (u : E d × ℝ → ℝ) (A : Set (E d)) (I : Set ℝ) : Prop :=
  ∀ x ∈ A, MonotoneOn (fun t ↦ u (x, t)) I

/-- `t ↦ u(x, t)` is nonincreasing on `I` for every `x ∈ A`. -/
def AntitoneInTime (u : E d × ℝ → ℝ) (A : Set (E d)) (I : Set ℝ) : Prop :=
  ∀ x ∈ A, AntitoneOn (fun t ↦ u (x, t)) I

/-- The time slices `E_t` are nondecreasing in `t ∈ I` (paper, after
[Definition 3.5](#AFS:d.parabolic-relaxed-subsolution)). -/
def SlicesMonotone (Eset : Set (E d × ℝ)) (I : Set ℝ) : Prop :=
  ∀ s ∈ I, ∀ t ∈ I, s ≤ t → timeSlice Eset s ⊆ timeSlice Eset t

/-! ### Parabolic inner variational solutions ([Definition 3.8](#AFS:d.parabolic-inner)) -/

/-- `w` is the weak time derivative of `u` in the open set `Ω`: `u, w` are locally
integrable on `Ω` and `∫_Ω u ∂ₜψ = -∫_Ω w ψ` for every `ψ ∈ C_c^∞(Ω)`.
[Definition 3.8](#AFS:d.parabolic-inner) asks `∂ₜu ∈ L²`; here the time derivative is carried as
explicit data `w` together with this weak-derivative predicate. -/
def HasWeakTimeDeriv (Ω : Set (E d × ℝ)) (u w : E d × ℝ → ℝ) : Prop :=
  LocallyIntegrableOn u Ω ∧ LocallyIntegrableOn w Ω ∧
    ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∫ p in Ω, u p * dₜ ψ p = -∫ p in Ω, w p * ψ p

/-- The integrand of the parabolic inner variation identity [(3.3)](#AFS:e.parabolic-inner-var):
`(|∇u|² + Q²χ) div ξ - 2 ∇u · Dξ ∇u + ∇(Q²) · ξ χ - 2 (ξ · ∇u) ∂ₜu`, with spatial
derivatives, pointwise spatial gradient of `u`, and `∂ₜu` supplied as data `w`. -/
noncomputable def paraInnerVarIntegrand (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ)
    (ξ : E d × ℝ → E d) (p : E d × ℝ) : ℝ :=
  (‖gradₓ u p‖ ^ 2 + Q p.1 ^ 2 * χ p) * divₓ ξ p
    - 2 * inner ℝ (gradₓ u p) (fderivₓ ξ p (gradₓ u p))
    + fderiv ℝ (fun y ↦ Q y ^ 2) p.1 (ξ p) * χ p
    - 2 * inner ℝ (ξ p) (gradₓ u p) * w p

/-- **[Definition 3.8](#AFS:d.parabolic-inner)**. `(u, χ)` (with `∂ₜu = w`) is an inner
variational solution of [(3.1)](#AFS:e.bernoulli-parabolic) in `U_∞ = U × (0, ∞)`:
(i) `u ∈ C(U_∞)`, `u ≥ 0`, `∇u ∈ L^∞_loc(U_∞)`, `∂ₜu = w ∈ L²(U_∞)`;
(ii) `χ` Borel measurable with values in `{0, 1}` on `U_∞`;
(iii) `1_{u > 0} ≤ χ` a.e. in `U_∞`;
(iv) [(3.3)](#AFS:e.parabolic-inner-var) holds for every `ξ ∈ C¹_c(U_∞; ℝᵈ)`.

The paper's [Definition 3.8](#AFS:d.parabolic-inner) also requires the heat equation `∂ₜu = Δu` in
`{u > 0}`; here it is not part of the structure, and its weak form is the separate predicate
`WeakHeatInPos`. The paper assumes `∇u ∈ L^∞_loc(U_∞)`; here we assume local spatial Lipschitz
bounds, uniform in time on a neighbourhood of each point, because this is the pointwise form of the
same condition for continuous `u`. The time derivative is explicit data `w` with a weak-derivative
predicate. In (iv) we additionally record integrability of the pointwise integrand, which holds for
the paper's (a.e.-defined) integrand under (i)–(iii); this rules out junk values of the Bochner
integral. -/
structure IsParaInnerVarSolution (U : Set (E d)) (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) :
    Prop where
  continuousOn : ContinuousOn u (UInf U)
  nonneg : ∀ p ∈ UInf U, 0 ≤ u p
  locLipₓ : ∀ p ∈ UInf U, ∃ K : ℝ, ∃ N ∈ 𝓝 p, ∀ q ∈ N, ∀ q' ∈ N, q.2 = q'.2 →
    |u q - u q'| ≤ K * ‖q.1 - q'.1‖
  timeDeriv : HasWeakTimeDeriv (UInf U) u w
  timeDeriv_memL2 : MemLp w 2 (volume.restrict (UInf U))
  meas : Measurable χ
  zero_one : ∀ p ∈ UInf U, χ p = 0 ∨ χ p = 1
  pos_le : ∀ᵐ p ∂(volume.restrict (UInf U)), 0 < u p → χ p = 1
  integrable : ∀ ξ : E d × ℝ → E d, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
    tsupport ξ ⊆ UInf U → Integrable (paraInnerVarIntegrand Q u w χ ξ) (volume.restrict (UInf U))
  stationary : ∀ ξ : E d × ℝ → E d, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
    tsupport ξ ⊆ UInf U → ∫ p in UInf U, paraInnerVarIntegrand Q u w χ ξ p = 0

/-- The weak heat equation in the positivity set, [(4.6)](#AFS:eqn:weakHeat): for every Lipschitz
`φ` with compact support in `{u > 0} ∩ U_∞`, `∫_{U_∞} ∂ₜu φ = -∫_{U_∞} ∇u · ∇φ` (with `∂ₜu = w`).

The paper includes the heat equation in `{u > 0}` (in the strong sense) in
[Definition 3.8](#AFS:d.parabolic-inner); here `IsParaInnerVarSolution` does not contain it, and its
weak form is this separate predicate: a hypothesis of [Theorem 3.14](#AFS:t.longtime-inner) and
[Lemma 5.8](#AFS:l.subsolution-inner-limit) and a conclusion of
[Proposition 4.1](#AFS:p.eps-inner-limit) and [Theorem 3.13](#AFS:t.parabolic-existence). It cannot
be dropped: in the unit ball of `ℝ²`, `u = 1 + |x₁|`, `w = 0`, `χ ≡ 1` is a bounded,
time-independent pair satisfying `IsParaInnerVarSolution` and
[(3.12)](#AFS:eqn:diss2)–[(3.14)](#AFS:eqn:chiEst2), but its limit is not harmonic in `{u > 0}`. -/
def WeakHeatInPos (U : Set (E d)) (u w : E d × ℝ → ℝ) : Prop :=
  ∀ φ : E d × ℝ → ℝ, (∃ K, LipschitzWith K φ) → HasCompactSupport φ →
    tsupport φ ⊆ posSetP u (UInf U) →
    ∫ p in UInf U, w p * φ p = -∫ p in UInf U, inner ℝ (gradₓ u p) (gradₓ φ p)

/-! ### The estimates [(3.12)](#AFS:eqn:diss2)–[(3.14)](#AFS:eqn:chiEst2)

These are the estimates of [Theorem 3.13](#AFS:t.parabolic-existence). -/

/-- The dissipation inequality [(3.12)](#AFS:eqn:diss2): for a.e. `T > 0`,
`½ J(u(T), χ(T); U) + ∫₀ᵀ ∫_U (∂ₜu)² ≤ ½ E0`.

The right-hand side is an explicit energy bound `E0`; the statements take
`E0 = ∫_U |∇g|² + Q_max² |U|`. -/
def DissipationIneq (U : Set (E d)) (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (E0 : ℝ≥0∞) : Prop :=
  ∀ᵐ T ∂(volume.restrict (Ioi (0 : ℝ))),
    energyJχ U Q (fun x ↦ gradₓ u (x, T)) (fun x ↦ χ (x, T)) / 2 +
        ∫⁻ p in U ×ˢ Ioc 0 T, ENNReal.ofReal (w p ^ 2) ≤ E0 / 2

/-- The interior Lipschitz bound [(3.13)](#AFS:eqn:LipEst) with constant `C`: for every
`Q_{2r}(x, t) ⊆ U_∞` with `0 < r ≤ 1`,
`‖∇u‖_{L^∞(Q_r(x,t))} ≤ C (r⁻¹ ‖u‖_{L^∞(Q_{2r}(x,t))} + 1)`, stated pointwise for the spatial
gradient with `‖u‖_{L^∞(Q_{2r})}` replaced by any bound `M` (equivalent for continuous `u`). -/
def InteriorLipEst (U : Set (E d)) (u : E d × ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ (x : E d) (t r : ℝ), 0 < r → r ≤ 1 → parCyl x t (2 * r) ⊆ UInf U →
    ∀ M : ℝ, (∀ q ∈ parCyl x t (2 * r), |u q| ≤ M) →
      ∀ p ∈ parCyl x t r, ‖gradₓ u p‖ ≤ C * (M / r + 1)

/-- Admissible weights for [(3.14)](#AFS:eqn:chiEst2): `η ∈ C¹_c(U_∞; [0, ∞))`. -/
def IsPerimeterWeight (U : Set (E d)) (η : E d × ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 η ∧ HasCompactSupport η ∧ tsupport η ⊆ UInf U ∧ ∀ p, 0 ≤ η p

/-- The norm `‖η‖_{L²((0,∞); H¹(U))} = (∫_{U_∞} η² + |∇ₓη|²)^{1/2}`. -/
noncomputable def l2H1Norm (U : Set (E d)) (η : E d × ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ p in UInf U, η p ^ 2 + ‖gradₓ η p‖ ^ 2)

/-- `d_η = dist(spt η, ∂_P U_∞)` (paper, after [(3.14)](#AFS:eqn:chiEst2)). -/
noncomputable def weightDist (U : Set (E d)) (η : E d × ℝ → ℝ) : ℝ :=
  sInf ((fun p ↦ infDist p (parBdryInf U)) '' tsupport η)

/-- The final time `sup {t : (x, t) ∈ spt η}` of the support of `η`. -/
noncomputable def weightTime (η : E d × ℝ → ℝ) : ℝ :=
  sSup (Prod.snd '' tsupport η)

/-- The time-length `ℓ_η = sup {t : (x, t) ∈ spt η} - inf {t : (x, t) ∈ spt η}` of the support
of `η` (the paper's `T_η`, after [(3.14)](#AFS:eqn:chiEst2)). -/
noncomputable def weightTimeLength (η : E d × ℝ → ℝ) : ℝ :=
  sSup (Prod.snd '' tsupport η) - sInf (Prod.snd '' tsupport η)

/-- The weighted perimeter bound [(3.14)](#AFS:eqn:chiEst2): for every
`η ∈ C¹_c(U_∞; [0, ∞))`, `∫_{U_∞} η |∇χ| ≤ C_η ‖η‖_{L²((0,∞); H¹(U))}`, where
`C_η = C d_η ℓ_η` depends on `η` only through `d_η = dist(spt η, ∂_P U_∞)` and the time-length
`ℓ_η` of `spt η`. -/
def WeightedPerimeterEst (U : Set (E d)) (χ : E d × ℝ → ℝ) (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ η : E d × ℝ → ℝ, IsPerimeterWeight U η →
    weightedTVₓ (UInf U) η χ ≤
      ENNReal.ofReal (C (weightDist U η) (weightTimeLength η) * l2H1Norm U η)

end PerronVariational

end
