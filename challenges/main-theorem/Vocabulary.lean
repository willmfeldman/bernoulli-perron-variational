module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Trusted statements: Perron's extremal solutions of the Bernoulli problem

This file imports Mathlib only. It is the complete trusted surface of the `main-theorem`
challenge: `Challenge.lean` and `Solution.lean` both state the three claims below.

## Source

F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
the Bernoulli one-phase problem*, arXiv:2609.14981 (`[AFS]` below).

* `MainSmallestClaim`, `MainLargestClaim`: [AFS, Theorem 1.1], the smallest supersolution and the
  largest subsolution cases.
* `ModelExampleClaim`: a non-vacuity check (a model example), not a result of the paper. In `ℝ²`
  with `Q ≡ 1`, one domain and one boundary condition give distinct smallest and largest solutions,
  and the smallest one has a two-plane point.

## The problem

The Bernoulli one-phase problem [AFS, (1.1)] in a domain `U ⊆ ℝᵈ`, with coefficient `Q > 0`:
`Δu = 0` in `{u > 0}` and `|∇u| = Q` on `∂{u > 0} ∩ U`, for `u ≥ 0`. Its Alt–Caffarelli energy is
`J_Q(u; V) = ∫_V |∇u|² + Q² 1_{u>0}` [AFS, (1.2)].

## Standing assumptions

[AFS, §1] assumes throughout: `U ⊆ ℝᵈ`, `d ≥ 2`, is open, bounded and connected with `C²`
boundary, and `Q` is Lipschitz on `Ū` with `0 < Q_min ≤ Q ≤ Q_max` on `Ū`. The claims below state
these as separate hypotheses. The `C²` boundary is encoded by a global defining function
(`HasC2Boundary`), a standard equivalent form.

## Vocabulary

The ambient space is `ℝᵈ = EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. All functions
are total functions on `ℝᵈ`; each definition restricts to its domain explicitly, and values outside
the domain are never used. Gradients `∇`, Laplacians `Δ` and derivatives are Mathlib's pointwise
ones (`0` at points of non-differentiability, by Mathlib's convention).

* `posSet`, `freeBoundary`: `{u > 0}` and `∂{u > 0} ∩ U`, taken inside `U`.
* `TouchesBelow`, `TouchesAbove`: local, non-strict touching in a set.
* `IsViscSuper`, `IsViscSub`, `IsViscSolution`: viscosity solutions [AFS, Definition 2.1].
* `IsStrictSub`, `IsStrictSuper`: smooth strict sub- and supersolutions [AFS, Definition 2.2].
* `perronSuperClass`, `perronSmallest`, `perronSubClass`, `perronLargest`: Perron's classes and
  extremal solutions [AFS, (2.1)–(2.4)].
* `divergence`, `innerVarIntegrand`, `IsInnerVarSolution`: inner variational solutions
  [AFS, Definition 2.8, (2.5)].
* `HasWeakGradient`, `MemH1Loc`, `energyJ`, `IsDownwardMinimizer`, `IsUpwardMinimizer`: one-sided
  minimizers of `J_Q` [AFS, Definition 2.11].
* `blowup`, `IsBlowupLimit`: blow-ups at a free boundary point, used by the model example.

## Differences from the printed paper

Each is stated in the docstring of the definition concerned.

* Test functions in the viscosity definitions are smooth on all of `ℝᵈ` rather than on `U`. This is
  equivalent, since the conditions are local: multiply by a cutoff.
* The data `g` of Definition 2.2 are `C²` on `ℝᵈ` rather than on `Ū`. A `C²(Ū)` function on a
  `C²` domain extends to a `C²(ℝᵈ)` function.
* Sobolev functions carry their weak gradient as explicit data `G`, and the energy `J_Q` is an
  `ℝ≥0∞`-valued lower Lebesgue integral, so that no integrability side conditions are needed.
* In Definition 2.11 the paper takes `u, v ∈ H¹(U)` and compares `J_Q(·; U)`. Here `u, v` are in
  `H¹_loc(U)` and the energies are compared on the ball `B`, where `u` and `v` differ. The two
  forms agree when `J_Q(u; U) < ∞`. The condition `u − v ∈ H¹₀(B)` is written `v = u` a.e. on
  `U \ B`, which is equivalent for balls.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian NNReal ENNReal

namespace PerronVariationalChallenge

/-- The Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-! ### The domain -/

/-- The positivity set `{u > 0}` of `u` inside the domain `U`. -/
def posSet (u : E d → ℝ) (U : Set (E d)) : Set (E d) := {x ∈ U | 0 < u x}

/-- The free boundary `∂{u > 0} ∩ U`. -/
def freeBoundary (u : E d → ℝ) (U : Set (E d)) : Set (E d) := frontier (posSet u U) ∩ U

/-- `U` has `C²` boundary, encoded by a global `C²` defining function: `U = {ρ < 0}` with
`∇ρ ≠ 0` on `∂U`. -/
def HasC2Boundary (U : Set (E d)) : Prop :=
  ∃ ρ : E d → ℝ, ContDiff ℝ 2 ρ ∧ U = {x | ρ x < 0} ∧ ∀ x ∈ frontier U, ∇ ρ x ≠ 0

/-- The divergence `∇ · ξ = tr Dξ` of a vector field `ξ : ℝᵈ → ℝᵈ` (pointwise, from Mathlib's
`fderiv`; `0` where `ξ` is not differentiable). -/
def divergence (ξ : E d → E d) (x : E d) : ℝ :=
  LinearMap.trace ℝ (E d) (fderiv ℝ ξ x).toLinearMap

/-! ### Viscosity solutions ([AFS, Definition 2.1]) -/

/-- `φ` touches `u` from below in `S` at `x`: `x ∈ S`, `φ x = u x`, and `φ ≤ u` on a
neighbourhood of `x` relative to `S` (local, non-strict touching). -/
def TouchesBelow (φ u : E d → ℝ) (S : Set (E d)) (x : E d) : Prop :=
  x ∈ S ∧ φ x = u x ∧ ∀ᶠ y in 𝓝[S] x, φ y ≤ u y

/-- `φ` touches `u` from above in `S` at `x`: `x ∈ S`, `φ x = u x`, and `u ≤ φ` on a
neighbourhood of `x` relative to `S`. -/
def TouchesAbove (φ u : E d → ℝ) (S : Set (E d)) (x : E d) : Prop :=
  x ∈ S ∧ φ x = u x ∧ ∀ᶠ y in 𝓝[S] x, u y ≤ φ y

/-- [AFS, Definition 2.1(i)]. `u ∈ C(U)`, `u ≥ 0`, is a viscosity supersolution in `U`: whenever
a smooth `φ` touches `u` from below at `x ∈ U`, either `Δφ(x) ≤ 0`, or `φ(x) = 0` and
`|∇φ(x)| ≤ Q(x)`. The test functions `φ` are smooth on `ℝᵈ` (the paper: on `U`). -/
def IsViscSuper (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  ContinuousOn u U ∧ (∀ x ∈ U, 0 ≤ u x) ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x ∈ U, TouchesBelow φ u U x →
      Δ φ x ≤ 0 ∨ (φ x = 0 ∧ ‖∇ φ x‖ ≤ Q x)

/-- [AFS, Definition 2.1(ii)]. `u ∈ C(U)`, `u ≥ 0`, is a viscosity subsolution in `U`: whenever
`φ` is smooth and `φ₊ = max φ 0` touches `u` from above in `\overline{{u > 0}} ∩ U` at `x`, either
`Δφ(x) ≥ 0`, or `φ(x) = 0` and `|∇φ(x)| ≥ Q(x)`. The test functions `φ` are smooth on `ℝᵈ`. -/
def IsViscSub (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  ContinuousOn u U ∧ (∀ x ∈ U, 0 ≤ u x) ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x,
      TouchesAbove (fun y ↦ max (φ y) 0) u (closure (posSet u U) ∩ U) x →
        0 ≤ Δ φ x ∨ (φ x = 0 ∧ Q x ≤ ‖∇ φ x‖)

/-- [AFS, Definition 2.1(iii)]. A viscosity solution is both a viscosity super- and
subsolution. -/
def IsViscSolution (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  IsViscSuper U Q u ∧ IsViscSub U Q u

/-! ### Smooth strict sub- and supersolutions ([AFS, Definition 2.2]) -/

/-- [AFS, Definition 2.2]. `g` is a smooth strict subsolution: `g` is `C²` (on `ℝᵈ`; the paper:
on `Ū`) and there are `a₀, δ₀ > 0` with (i) `Δg ≥ 0` on `{g > -a₀}` and
(ii) `|∇g|² ≥ (1 + δ₀) Q²` on `{|g| ≤ a₀}`, both sets taken inside `Ū`. -/
def IsStrictSub (U : Set (E d)) (Q g : E d → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ ∃ a₀ > 0, ∃ δ₀ > 0,
    (∀ x ∈ closure U, -a₀ < g x → 0 ≤ Δ g x) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → (1 + δ₀) * Q x ^ 2 ≤ ‖∇ g x‖ ^ 2

/-- [AFS, Definition 2.2]. `g` is a smooth strict supersolution: `g` is `C²` and there are
`a₀, δ₀ > 0` with (i) `Δg ≤ 0` on `{g > -a₀}` and (ii) `|∇g|² ≤ (1 - δ₀) Q²` on `{|g| ≤ a₀}`,
both sets taken inside `Ū`. -/
def IsStrictSuper (U : Set (E d)) (Q g : E d → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ ∃ a₀ > 0, ∃ δ₀ > 0,
    (∀ x ∈ closure U, -a₀ < g x → Δ g x ≤ 0) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → ‖∇ g x‖ ^ 2 ≤ (1 - δ₀) * Q x ^ 2

/-! ### Perron's method ([AFS, (2.1)–(2.4)]) -/

/-- The class `𝒮_g` of [AFS, (2.3)]: the functions `v ∈ C(Ū)` that are viscosity supersolutions
in `U` with `v ≥ g₊` on `Ū`. -/
def perronSuperClass (U : Set (E d)) (Q g : E d → ℝ) : Set (E d → ℝ) :=
  {v | ContinuousOn v (closure U) ∧ IsViscSuper U Q v ∧ ∀ x ∈ closure U, max (g x) 0 ≤ v x}

/-- The smallest supersolution above `g` [AFS, (2.4)]: `u(x) = inf_{v ∈ 𝒮_g} v(x)`, as a real
infimum (`sInf`). Only its values on `Ū` enter the claims. -/
def perronSmallest (U : Set (E d)) (Q g : E d → ℝ) (x : E d) : ℝ :=
  sInf ((fun v ↦ v x) '' perronSuperClass U Q g)

/-- The class `𝒮^g` of [AFS, (2.1)]: the functions `v ∈ C(Ū)` that are viscosity subsolutions in
`U` with `v ≤ g₊` on `Ū`. -/
def perronSubClass (U : Set (E d)) (Q g : E d → ℝ) : Set (E d → ℝ) :=
  {v | ContinuousOn v (closure U) ∧ IsViscSub U Q v ∧ ∀ x ∈ closure U, v x ≤ max (g x) 0}

/-- The largest subsolution below `g` [AFS, (2.2)]: `u(x) = sup_{v ∈ 𝒮^g} v(x)`, as a real
supremum (`sSup`). Only its values on `Ū` enter the claims. -/
def perronLargest (U : Set (E d)) (Q g : E d → ℝ) (x : E d) : ℝ :=
  sSup ((fun v ↦ v x) '' perronSubClass U Q g)

/-! ### Inner variational solutions ([AFS, Definition 2.8]) -/

/-- The integrand of the inner variation identity [AFS, (2.5)]:
`(|∇u|² + Q²χ) div ξ - 2 ∇u · Dξ ∇u + ∇(Q²) · ξ χ`.
The derivatives are Mathlib's pointwise ones. For `u` locally Lipschitz and `Q`, `ξ` Lipschitz they
agree almost everywhere with the weak derivatives (Rademacher's theorem). -/
def innerVarIntegrand (Q u χ : E d → ℝ) (ξ : E d → E d) (x : E d) : ℝ :=
  (‖∇ u x‖ ^ 2 + Q x ^ 2 * χ x) * divergence ξ x
    - 2 * inner ℝ (∇ u x) (fderiv ℝ ξ x (∇ u x))
    + fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x) * χ x

/-- [AFS, Definition 2.8]. `(u, χ)` is an inner variational solution in the open set `U`:
(i) `u ≥ 0`, `u` is locally Lipschitz in `U`, `C²` in `{u > 0}`, and `Δu = 0` in `{u > 0}`;
(ii) `χ` is Borel measurable with values in `{0, 1}` on `U`;
(iii) `1_{u > 0} ≤ χ` a.e. on `U`;
(iv) the inner variation identity [AFS, (2.5)] holds for every Lipschitz vector field `ξ` with
compact support in `U`.

In (iv) the integrand is bounded, measurable and compactly supported in `U`, so the Bochner
integral is a genuine Lebesgue integral. -/
structure IsInnerVarSolution (U : Set (E d)) (Q u χ : E d → ℝ) : Prop where
  /-- `u ≥ 0` on `U`. -/
  nonneg : ∀ x ∈ U, 0 ≤ u x
  /-- `u` is locally Lipschitz in `U`. -/
  locLip : LocallyLipschitzOn U u
  /-- `u` is `C²` in `{u > 0}`. -/
  c2 : ContDiffOn ℝ 2 u (posSet u U)
  /-- `u` is harmonic in `{u > 0}`. -/
  harmonic : ∀ x ∈ posSet u U, Δ u x = 0
  /-- `χ` is Borel measurable. -/
  meas : Measurable χ
  /-- `χ` takes the values `0` and `1` on `U`. -/
  zero_one : ∀ x ∈ U, χ x = 0 ∨ χ x = 1
  /-- `1_{u > 0} ≤ χ` a.e. on `U`. -/
  pos_le : ∀ᵐ x ∂(volume.restrict U), 0 < u x → χ x = 1
  /-- The inner variation identity [AFS, (2.5)]. -/
  stationary : ∀ ξ : E d → E d, (∃ K, LipschitzWith K ξ) → HasCompactSupport ξ →
    tsupport ξ ⊆ U → ∫ x in U, innerVarIntegrand Q u χ ξ x = 0

/-! ### One-sided minimizers ([AFS, Definition 2.11]) -/

/-- `G` is a weak gradient of `u` in the open set `U`: `u` and `G` are locally integrable on `U`,
and `∫_U u ∂_v φ = - ∫_U (G · v) φ` for every `φ ∈ C_c^∞(U)` and every direction `v`. -/
def HasWeakGradient (U : Set (E d)) (u : E d → ℝ) (G : E d → E d) : Prop :=
  LocallyIntegrableOn u U ∧ LocallyIntegrableOn G U ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : E d,
      ∫ x in U, u x * fderiv ℝ φ x v = -∫ x in U, inner ℝ (G x) v * φ x

/-- `u ∈ H¹_loc(U)` with weak gradient `G`: `G` is a weak gradient of `u` in `U`, and `u` and `G`
are in `L²(K)` for every compact `K ⊆ U`. -/
def MemH1Loc (U : Set (E d)) (u : E d → ℝ) (G : E d → E d) : Prop :=
  HasWeakGradient U u G ∧ ∀ K ⊆ U, IsCompact K →
    MemLp u 2 (volume.restrict K) ∧ MemLp G 2 (volume.restrict K)

/-- The Alt–Caffarelli energy `J_Q(u; V) = ∫_V |∇u|² + Q² 1_{u>0}` [AFS, (1.2)], with the gradient
supplied as data `G`. It is an `ℝ≥0∞`-valued lower Lebesgue integral: it is defined, possibly
`∞`, for every `u`, and it needs no integrability hypothesis. -/
def energyJ (V : Set (E d)) (Q u : E d → ℝ) (G : E d → E d) : ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal (‖G x‖ ^ 2 + Q x ^ 2 * (posSet u V).indicator 1 x)

/-- [AFS, Definition 2.11], downward case. `u` is a downward minimizer of `J_Q` in `U`:
(i) `u ∈ H¹_loc(U)`, `{u > 0}` is open, and `u` is harmonic (`C²` with `Δu = 0`) in `{u > 0}`;
(ii) for every ball `B = B_r(x)` with `\overline{B} ⊆ U`, and every `v ∈ H¹_loc(U)` with `v ≤ u`
a.e. in `U` and `v = u` a.e. in `U \ B`, `J_Q(u; B) ≤ J_Q(v; B)` (for all weak gradients `Gu`,
`Gv` of `u`, `v`).

Differences from the paper: the paper takes `u, v ∈ H¹(U)` and compares `J_Q(u; U) ≤ J_Q(v; U)`;
here `u, v ∈ H¹_loc(U)` and the energies are compared on `B`. Since `v = u` outside `B`, the two
forms agree when `J_Q(u; U) < ∞`. The paper's condition `u − v ∈ H¹₀(B)` is written `v = u` a.e.
in `U \ B`, which is equivalent for a ball `B`. -/
def IsDownwardMinimizer (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  (∃ G, MemH1Loc U u G) ∧ IsOpen (posSet u U) ∧ ContDiffOn ℝ 2 u (posSet u U) ∧
    (∀ x ∈ posSet u U, Δ u x = 0) ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U →
      ∀ (Gu : E d → E d) (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U u Gu → MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict U), v y ≤ u y) →
        (∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) →
        energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv

/-- [AFS, Definition 2.11], upward case: as `IsDownwardMinimizer`, with competitors `v ≥ u`
a.e. in `U`. -/
def IsUpwardMinimizer (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  (∃ G, MemH1Loc U u G) ∧ IsOpen (posSet u U) ∧ ContDiffOn ℝ 2 u (posSet u U) ∧
    (∀ x ∈ posSet u U, Δ u x = 0) ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U →
      ∀ (Gu : E d → E d) (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U u Gu → MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
        (∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) →
        energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv

/-! ### Blow-ups -/

/-- The blow-up `u_{x₀,r}(y) = r⁻¹ u(x₀ + r y)`. -/
def blowup (u : E d → ℝ) (x₀ : E d) (r : ℝ) (y : E d) : ℝ :=
  u (x₀ + r • y) / r

/-- `v` is a (subsequential) blow-up limit of `u` at `x₀`: `u_{x₀,r_n} → v` locally uniformly on
`ℝᵈ` along some sequence `r_n → 0⁺`. -/
def IsBlowupLimit (u : E d → ℝ) (x₀ : E d) (v : E d → ℝ) : Prop :=
  ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
    TendstoLocallyUniformly (fun n ↦ blowup u x₀ (r n)) v atTop

/-! ### The claims -/

/-- **[AFS, Theorem 1.1]**, smallest supersolution case. Let `d ≥ 2`, let `U ⊆ ℝᵈ` be open,
bounded and connected with `C²` boundary, and let `Q` be Lipschitz on `Ū` with
`0 < Q_min ≤ Q ≤ Q_max` on `Ū`. Let `g` be a smooth strict subsolution with `g > 0` on `∂U`, and
let `u` be the smallest supersolution above `g`. Then
(i) `u` is a viscosity solution in `U`;
(ii) `u` is an inner variational solution in `U`, for some `χ`;
(iii) `u` is a downward minimizer of `J_Q` locally around each free boundary point: every
`x ∈ ∂{u > 0} ∩ U` has a ball `B_r(x)` with `\overline{B_r(x)} ⊆ U` in which `u` is a downward
minimizer. -/
def MainSmallestClaim (d : ℕ) : Prop :=
  2 ≤ d → ∀ (U : Set (E d)) (Q : E d → ℝ) (Qmin Qmax : ℝ),
    IsOpen U → Bornology.IsBounded U → IsConnected U → HasC2Boundary U →
    (∃ K, LipschitzOnWith K Q (closure U)) → 0 < Qmin → Qmin ≤ Qmax →
    (∀ x ∈ closure U, Qmin ≤ Q x ∧ Q x ≤ Qmax) →
    ∀ g : E d → ℝ, IsStrictSub U Q g → (∀ x ∈ frontier U, 0 < g x) →
      IsViscSolution U Q (perronSmallest U Q g) ∧
      (∃ χ : E d → ℝ, IsInnerVarSolution U Q (perronSmallest U Q g) χ) ∧
      ∀ x ∈ freeBoundary (perronSmallest U Q g) U, ∃ r > 0, closedBall x r ⊆ U ∧
        IsDownwardMinimizer (ball x r) Q (perronSmallest U Q g)

/-- **[AFS, Theorem 1.1]**, largest subsolution case. Under the standing assumptions on `U` and
`Q` (as in `MainSmallestClaim`), let `g` be a smooth strict supersolution (no boundary positivity is
needed) and `u` the largest subsolution below `g`. Then (i) `u` is a viscosity solution in `U`,
(ii) an inner variational solution in `U`, for some `χ`, and (iii) an upward minimizer of `J_Q`
locally around each free boundary point. -/
def MainLargestClaim (d : ℕ) : Prop :=
  2 ≤ d → ∀ (U : Set (E d)) (Q : E d → ℝ) (Qmin Qmax : ℝ),
    IsOpen U → Bornology.IsBounded U → IsConnected U → HasC2Boundary U →
    (∃ K, LipschitzOnWith K Q (closure U)) → 0 < Qmin → Qmin ≤ Qmax →
    (∀ x ∈ closure U, Qmin ≤ Q x ∧ Q x ≤ Qmax) →
    ∀ g : E d → ℝ, IsStrictSuper U Q g →
      IsViscSolution U Q (perronLargest U Q g) ∧
      (∃ χ : E d → ℝ, IsInnerVarSolution U Q (perronLargest U Q g) χ) ∧
      ∀ x ∈ freeBoundary (perronLargest U Q g) U, ∃ r > 0, closedBall x r ⊆ U ∧
        IsUpwardMinimizer (ball x r) Q (perronLargest U Q g)

/-- **Model example: a two-plane point, and distinct extremal solutions.** Not a result of
[AFS]; it shows that the two cases of [AFS, Theorem 1.1] can produce different solutions from the
same boundary data, and that the second alternative of [AFS, Corollary 1.2(i)] (a point where every
blow-up is a two-plane solution) occurs.

In `ℝ²` with `Q ≡ 1` there are a domain `U` and data `g_sub`, `g_super` such that
* `U`, `Q`, `g_sub` satisfy the hypotheses of `MainSmallestClaim`, and `U`, `Q`, `g_super` those
  of `MainLargestClaim` (except the trivial ones: `2 ≤ 2`, and, for `Q ≡ 1` with
  `Q_min = Q_max = 1`, the bounds `0 < Q_min ≤ Q ≤ Q_max`);
* `g_sub = g_super` on `∂U`: the two problems have the same boundary data;

and, writing `u_min = perronSmallest U 1 g_sub` and `u_max = perronLargest U 1 g_super`:
1. `u_min` and `u_max` are nontrivial: each is positive at some point of `U`, vanishes at some
   point of `U`, and has a nonempty free boundary;
2. `0` is a two-plane point of `u_min`: `0 ∈ ∂{u_min > 0} ∩ U`, the blow-ups `(u_min)_{0,t}`
   converge to `y ↦ |y₁|` locally uniformly on `ℝ²` as `t → 0⁺`, and every blow-up limit of
   `u_min` at `0` is `y ↦ |y₁|`, where `y₁ = ⟪y, e₁⟫`;
3. `u_min ≠ u_max`: they differ at some point of `U` (values outside `U` are irrelevant).

The construction behind the solution: `U = B₁(0) \ (B̄_{a/2}(a e₁) ∪ B̄_{a/2}(-a e₁))` for a small
`a > 0`, with data equal to `a log 2` on both inner circles, so that the radial solutions
`(a log (a / |x ∓ a e₁|))₊` from the two holes have free boundaries `∂B_a(± a e₁)`, which touch at
`0`. The claim itself is existential and does not fix the construction. -/
def ModelExampleClaim : Prop :=
  ∃ (U : Set (E 2)) (gsub gsuper : E 2 → ℝ),
    IsOpen U ∧ Bornology.IsBounded U ∧ IsConnected U ∧ HasC2Boundary U ∧
    (∃ K, LipschitzOnWith K (fun _ : E 2 ↦ (1 : ℝ)) (closure U)) ∧
    IsStrictSub U (fun _ ↦ 1) gsub ∧ (∀ x ∈ frontier U, 0 < gsub x) ∧
    IsStrictSuper U (fun _ ↦ 1) gsuper ∧
    (∀ x ∈ frontier U, gsub x = gsuper x) ∧
    (∃ x ∈ U, 0 < perronSmallest U (fun _ ↦ 1) gsub x) ∧
    (∃ x ∈ U, perronSmallest U (fun _ ↦ 1) gsub x = 0) ∧
    (freeBoundary (perronSmallest U (fun _ ↦ 1) gsub) U).Nonempty ∧
    (∃ x ∈ U, 0 < perronLargest U (fun _ ↦ 1) gsuper x) ∧
    (∃ x ∈ U, perronLargest U (fun _ ↦ 1) gsuper x = 0) ∧
    (freeBoundary (perronLargest U (fun _ ↦ 1) gsuper) U).Nonempty ∧
    (0 : E 2) ∈ freeBoundary (perronSmallest U (fun _ ↦ 1) gsub) U ∧
    TendstoLocallyUniformly (fun t ↦ blowup (perronSmallest U (fun _ ↦ 1) gsub) 0 t)
      (fun y ↦ |inner ℝ y (EuclideanSpace.single 0 1)|) (𝓝[>] 0) ∧
    (∀ v, IsBlowupLimit (perronSmallest U (fun _ ↦ 1) gsub) 0 v →
      ∀ y, v y = |inner ℝ y (EuclideanSpace.single 0 1)|) ∧
    ∃ x ∈ U, perronSmallest U (fun _ ↦ 1) gsub x ≠ perronLargest U (fun _ ↦ 1) gsuper x

end PerronVariationalChallenge

end
