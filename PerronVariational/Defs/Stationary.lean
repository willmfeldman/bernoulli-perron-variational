/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Touching
public import PerronVariational.Basic.Sobolev
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Stationary solution notions

The solution notions of §2 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper"):

* Viscosity super/sub/solutions (Definition 2.1).
* Smooth strict sub/supersolutions (Definition 2.2).
* Relaxed subsolutions/solutions (Definition 2.3).
* Perron classes and extremal solutions ((2.1)–(2.4)).
* Local smallest supersolutions / largest subsolutions (Definition 2.6).
* Inner variational solutions (Definition 2.8).
* Upward/downward minimizers (Definition 2.11).
* Blow-ups and classical regularity near a free boundary point (Theorem 1.1, Corollary 1.2).

Test functions. The paper tests with `φ ∈ C^∞(U)`; here test functions are globally smooth
`E d → ℝ`. The two versions are equivalent by a cutoff argument, since every condition is local
at the touching point.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian NNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Viscosity solutions (Definition 2.1) -/

/-- **Definition 2.1(i)**, with globally smooth test functions. `u ∈ C(U)`, `u ≥ 0`, is a viscosity
supersolution of (1.1) in `U`: whenever a smooth `φ` touches `u` from below at `x ∈ U`, either
`Δφ(x) ≤ 0`, or `φ(x) = 0` and `|∇φ(x)| ≤ Q(x)`. -/
def IsViscSuper (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  ContinuousOn u U ∧ (∀ x ∈ U, 0 ≤ u x) ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x ∈ U, TouchesBelow φ u U x →
      Δ φ x ≤ 0 ∨ (φ x = 0 ∧ ‖∇ φ x‖ ≤ Q x)

/-- **Definition 2.1(ii)**, with globally smooth test functions. `u ∈ C(U)`, `u ≥ 0`, is a viscosity
subsolution of (1.1) in `U`: whenever `φ` is smooth and `φ₊` touches `u` from above in
`\overline{{u > 0}} ∩ U` at `x`, either `Δφ(x) ≥ 0`, or `φ(x) = 0` and `|∇φ(x)| ≥ Q(x)`. -/
def IsViscSub (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  ContinuousOn u U ∧ (∀ x ∈ U, 0 ≤ u x) ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x,
      TouchesAbove (fun y ↦ max (φ y) 0) u (closure (posSet u U) ∩ U) x →
        0 ≤ Δ φ x ∨ (φ x = 0 ∧ Q x ≤ ‖∇ φ x‖)

/-- **Definition 2.1(iii)**. Viscosity solution: both a viscosity super- and subsolution. -/
def IsViscSolution (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  IsViscSuper U Q u ∧ IsViscSub U Q u

/-! ### Smooth strict sub/supersolutions (Definition 2.2) -/

/-- **Definition 2.2**, subsolution case. `g` is a smooth strict subsolution: there are
`a₀, δ₀ > 0` with (i) `Δg ≥ 0` in `{g > -a₀}` and (ii) `|∇g|² ≥ (1 + δ₀) Q²` on `{|g| ≤ a₀}`
(both sets taken inside `Ū`, the domain of `g`).

The paper assumes `g ∈ C²(Ū)`; here we assume `g ∈ C²(ℝᵈ)`, because a `C²(Ū)` function on a
domain with `C²` boundary extends to a `C²` function on `ℝᵈ`, and only values on `Ū` enter. -/
def IsStrictSub (U : Set (E d)) (Q g : E d → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ ∃ a₀ > 0, ∃ δ₀ > 0,
    (∀ x ∈ closure U, -a₀ < g x → 0 ≤ Δ g x) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → (1 + δ₀) * Q x ^ 2 ≤ ‖∇ g x‖ ^ 2

/-- **Definition 2.2**, supersolution case. `g` is a smooth strict supersolution: there are
`a₀, δ₀ > 0` with (i) `Δg ≤ 0` in `{g > -a₀}` and (ii) `|∇g|² ≤ (1 - δ₀) Q²` on `{|g| ≤ a₀}`
(both sets taken inside `Ū`). As for `IsStrictSub`, the paper assumes `g ∈ C²(Ū)` and here
`g ∈ C²(ℝᵈ)`. -/
def IsStrictSuper (U : Set (E d)) (Q g : E d → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ ∃ a₀ > 0, ∃ δ₀ > 0,
    (∀ x ∈ closure U, -a₀ < g x → Δ g x ≤ 0) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → ‖∇ g x‖ ^ 2 ≤ (1 - δ₀) * Q x ^ 2

/-! ### Relaxed subsolutions (Definition 2.3) -/

/-- **Definition 2.3**, with globally smooth test functions. For `u ∈ C(U)`, `u ≥ 0`, and `E`
closed (in `Ū`, i.e. closed and `⊆ Ū`) containing `{u > 0}`, the pair `(u, E)` is a relaxed
subsolution: whenever a smooth `φ` touches `u` from above in `E ∩ U` at `x`, either
`Δφ(x) ≥ 0`, or `φ(x) = 0` and `|∇φ(x)| ≥ Q(x)`. (Literal: `φ`, not `φ₊`, touches.) -/
def IsRelaxedSub (U : Set (E d)) (Q u : E d → ℝ) (Eset : Set (E d)) : Prop :=
  ContinuousOn u U ∧ (∀ x ∈ U, 0 ≤ u x) ∧ IsClosed Eset ∧ Eset ⊆ closure U ∧
    posSet u U ⊆ Eset ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x, TouchesAbove φ u (Eset ∩ U) x →
      0 ≤ Δ φ x ∨ (φ x = 0 ∧ Q x ≤ ‖∇ φ x‖)

/-- **Definition 2.3**. `(u, E)` is a relaxed solution: `u` is a viscosity supersolution and
`(u, E)` is a relaxed subsolution. -/
def IsRelaxedSolution (U : Set (E d)) (Q u : E d → ℝ) (Eset : Set (E d)) : Prop :=
  IsViscSuper U Q u ∧ IsRelaxedSub U Q u Eset

/-! ### Perron's method ((2.1)–(2.4)) -/

/-- The class `𝒮_g` of (2.3): `v ∈ C(Ū)` viscosity supersolutions in `U` with
`v ≥ g₊` on `Ū`. -/
def perronSuperClass (U : Set (E d)) (Q g : E d → ℝ) : Set (E d → ℝ) :=
  {v | ContinuousOn v (closure U) ∧ IsViscSuper U Q v ∧ ∀ x ∈ closure U, max (g x) 0 ≤ v x}

/-- The smallest supersolution above `g`, (2.4):
`u(x) = inf_{v ∈ 𝒮_g} v(x)`. Meaningful for `x ∈ Ū` (where the set is bounded below by `g₊`
and nonempty); the value outside `Ū` is irrelevant. -/
noncomputable def perronSmallest (U : Set (E d)) (Q g : E d → ℝ) (x : E d) : ℝ :=
  sInf ((fun v ↦ v x) '' perronSuperClass U Q g)

/-- The class `𝒮^g` of (2.1): `v ∈ C(Ū)` viscosity subsolutions in `U` with
`v ≤ g₊` on `Ū`. -/
def perronSubClass (U : Set (E d)) (Q g : E d → ℝ) : Set (E d → ℝ) :=
  {v | ContinuousOn v (closure U) ∧ IsViscSub U Q v ∧ ∀ x ∈ closure U, v x ≤ max (g x) 0}

/-- The largest subsolution below `g`, (2.2):
`u(x) = sup_{v ∈ 𝒮^g} v(x)`. Meaningful for `x ∈ Ū`. -/
noncomputable def perronLargest (U : Set (E d)) (Q g : E d → ℝ) (x : E d) : ℝ :=
  sSup ((fun v ↦ v x) '' perronSubClass U Q g)

/-- Sanity check (paper, after (2.4)): `0 ∈ 𝒮^g`. -/
theorem zero_mem_perronSubClass (U : Set (E d)) (Q g : E d → ℝ) :
    (0 : E d → ℝ) ∈ perronSubClass U Q g := by
  refine ⟨continuousOn_const, ⟨continuousOn_const, fun _ _ ↦ le_rfl, ?_⟩,
    fun _ _ ↦ le_max_right _ _⟩
  intro φ _ x hx
  have hpos : posSet (0 : E d → ℝ) U = ∅ := by
    ext y; simp [posSet]
  have := hx.1
  simp [hpos] at this

/-! ### Local extremal solutions (Definition 2.6) -/

/-- **Definition 2.6(i)**. `u` is a (local) smallest supersolution in `U`:
a viscosity supersolution such that for every ball `B ⊂⊂ U` (here `B = ball x r`,
`closedBall x r ⊆ U`) and every viscosity supersolution `v ∈ C(U)` with `v = u` on `U \ B`,
`v ≥ u` in `U`. -/
def IsLocalSmallestSuper (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  IsViscSuper U Q u ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U → ∀ v : E d → ℝ, IsViscSuper U Q v →
      (∀ y ∈ U \ ball x r, v y = u y) → ∀ y ∈ U, u y ≤ v y

/-- **Definition 2.6(ii)**. `u` is a (local) largest subsolution in `U`:
a viscosity subsolution such that for every ball `B ⊂⊂ U` and every viscosity subsolution
`v ∈ C(U)` with `v = u` on `U \ B`, `v ≤ u` in `U`. -/
def IsLocalLargestSub (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  IsViscSub U Q u ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U → ∀ v : E d → ℝ, IsViscSub U Q v →
      (∀ y ∈ U \ ball x r, v y = u y) → ∀ y ∈ U, v y ≤ u y

/-! ### Inner variational solutions (Definition 2.8) -/

/-- The integrand of the inner variation identity (2.5):
`(|∇u|² + Q²χ) div ξ - 2 ∇u · Dξ ∇u + ∇(Q²) · ξ χ`.
Gradients are pointwise (`0` where not differentiable); for locally Lipschitz `u`, Lipschitz
`Q` and `ξ` they agree a.e. with the weak ones (Rademacher). -/
noncomputable def innerVarIntegrand (Q u χ : E d → ℝ) (ξ : E d → E d) (x : E d) : ℝ :=
  (‖∇ u x‖ ^ 2 + Q x ^ 2 * χ x) * divergence ξ x
    - 2 * inner ℝ (∇ u x) (fderiv ℝ ξ x (∇ u x))
    + fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x) * χ x

/-- **Definition 2.8**. `(u, χ)` is an inner variational solution of (1.1)
in the open set `U`:
(i) `u ≥ 0`, `u ∈ C^{0,1}_loc(U) ∩ C²({u > 0})` and `Δu = 0` in `{u > 0}`;
(ii) `χ` is Borel measurable with values in `{0, 1}` on `U`;
(iii) `1_{u > 0} ≤ χ` a.e. on `U`;
(iv) the inner variation identity (2.5) holds for every `ξ ∈ C^{0,1}_c(U; ℝᵈ)`.

Since `u` is locally Lipschitz, `ξ` Lipschitz with compact support, `χ` bounded measurable and
`Q` Lipschitz, the integrand of (iv) is bounded, measurable and compactly supported in `U`, so the
Bochner integral in (iv) is a genuine Lebesgue integral. -/
structure IsInnerVarSolution (U : Set (E d)) (Q u χ : E d → ℝ) : Prop where
  nonneg : ∀ x ∈ U, 0 ≤ u x
  locLip : LocallyLipschitzOn U u
  c2 : ContDiffOn ℝ 2 u (posSet u U)
  harmonic : ∀ x ∈ posSet u U, Δ u x = 0
  meas : Measurable χ
  zero_one : ∀ x ∈ U, χ x = 0 ∨ χ x = 1
  pos_le : ∀ᵐ x ∂(volume.restrict U), 0 < u x → χ x = 1
  stationary : ∀ ξ : E d → E d, (∃ K, LipschitzWith K ξ) → HasCompactSupport ξ →
    tsupport ξ ⊆ U → ∫ x in U, innerVarIntegrand Q u χ ξ x = 0

/-! ### Directional minimizers (Definition 2.11) -/

/-- **Definition 2.11**, downward case.
(i) `{u > 0}` is open and `u` is harmonic (classically: `C²` with `Δu = 0`) in `{u > 0}`;
(ii) for every ball `B = ball x r ⊂⊂ U` and every `v ∈ H¹_loc(U)` with `v ≤ u` a.e. and `v = u`
a.e. on `U \ B`, `J_Q(u; B) ≤ J_Q(v; B)`.

Differences from the paper:
* The paper takes `u, v ∈ H¹(U)` and compares `J_Q(·; U)`; here `u, v ∈ H¹_loc(U)` and the
  energies are compared on the ball `B`. The two agree when `J_Q(u; U) < ∞`. We change it because
  the paper applies the definition on `U = ℝᵈ` (Corollary 2.13, Proposition 2.14), where the
  two-plane functions are not in `H¹(ℝᵈ)` and every energy is infinite, so the literal
  definition would be vacuous there.
* The paper's condition `u - v ∈ H¹₀(B)` is encoded as `v = u` a.e. on `U \ B`; for balls the two
  are equivalent.
* Sobolev functions carry their weak gradients as explicit data (see `MemH1Loc`). -/
def IsDownwardMinimizer (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  (∃ G, MemH1Loc U u G) ∧ IsOpen (posSet u U) ∧ ContDiffOn ℝ 2 u (posSet u U) ∧
    (∀ x ∈ posSet u U, Δ u x = 0) ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U →
      ∀ (Gu : E d → E d) (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U u Gu → MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict U), v y ≤ u y) →
        (∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) →
        energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv

/-- **Definition 2.11**, upward case; same encoding (and the same differences from the paper)
as `IsDownwardMinimizer`, with competitors `v ≥ u` a.e. -/
def IsUpwardMinimizer (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  (∃ G, MemH1Loc U u G) ∧ IsOpen (posSet u U) ∧ ContDiffOn ℝ 2 u (posSet u U) ∧
    (∀ x ∈ posSet u U, Δ u x = 0) ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U →
      ∀ (Gu : E d → E d) (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U u Gu → MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
        (∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) →
        energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv

/-! ### Blow-ups and classical regularity (Corollary 1.2) -/

/-- The blow-up `u_{x₀,r}(y) = r⁻¹ u(x₀ + r y)` (paper, proof sketch of Corollary 1.2, and
Corollary 2.13). -/
noncomputable def blowup (u : E d → ℝ) (x₀ : E d) (r : ℝ) (y : E d) : ℝ :=
  u (x₀ + r • y) / r

/-- `v` is a (subsequential) blow-up limit of `u` at `x₀`: `u_{x₀,r_n} → v` locally uniformly on
`ℝᵈ` along some sequence `r_n → 0⁺` (Corollary 1.2(i)). -/
def IsBlowupLimit (u : E d → ℝ) (x₀ : E d) (v : E d → ℝ) : Prop :=
  ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
    TendstoLocallyUniformly (fun n ↦ blowup u x₀ (r n)) v atTop

/-- `S` is a `C^{1,γ}` hypersurface in `ball x₀ r` (Corollary 1.2, footnote): for some
`γ ∈ (0, 1]`, unit vector `e` and `f ∈ C¹` with `γ`-Hölder derivative, `S ∩ ball x₀ r` is the
graph `{y : (y - x₀) · e = f(P(y - x₀))}` over the hyperplane `e^⊥`, where
`P z = z - (z · e) e` is the orthogonal projection onto `e^⊥`. -/
def IsC1GammaHypersurfaceNear (S : Set (E d)) (x₀ : E d) (r : ℝ) : Prop :=
  ∃ γ : ℝ≥0, 0 < γ ∧ γ ≤ 1 ∧ ∃ e : E d, ‖e‖ = 1 ∧ ∃ (f : E d → ℝ) (C : ℝ≥0),
    ContDiff ℝ 1 f ∧ HolderWith C γ (fderiv ℝ f) ∧
    S ∩ ball x₀ r =
      {y ∈ ball x₀ r | inner ℝ (y - x₀) e = f (y - x₀ - inner ℝ (y - x₀) e • e)}

/-- `u` is a classical solution of (1.1) near the free boundary point `x₀` (Corollary 1.2 and its
footnote): for some `r > 0` with `ball x₀ r ⊆ U`,
* the free boundary `∂{u > 0} ∩ U` is a `C^{1,γ}` hypersurface in `ball x₀ r`;
* `u` is `C²` and harmonic in `{u > 0} ∩ ball x₀ r`;
* `∇u` extends continuously (as `G`) to `\overline{{u > 0}} ∩ ball x₀ r` and the free boundary
  condition `|∇u| = Q` holds classically on `∂{u > 0} ∩ ball x₀ r`. -/
def IsClassicalNear (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) : Prop :=
  ∃ r > 0, ball x₀ r ⊆ U ∧ IsC1GammaHypersurfaceNear (freeBoundary u U) x₀ r ∧
    ContDiffOn ℝ 2 u (posSet u U ∩ ball x₀ r) ∧ (∀ y ∈ posSet u U ∩ ball x₀ r, Δ u y = 0) ∧
    ∃ G : E d → E d, ContinuousOn G (closure (posSet u U) ∩ ball x₀ r) ∧
      (∀ y ∈ posSet u U ∩ ball x₀ r, G y = ∇ u y) ∧
      ∀ y ∈ freeBoundary u U ∩ ball x₀ r, ‖G y‖ = Q y

end PerronVariational

end
