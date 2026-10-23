/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
public import PerronVariational.Defs.Semilinear

/-!
# Statements of the intermediate results

One `def …Statement : Prop` per intermediate result of F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 ("the paper"). This file contains the statements only; each is proved in the
module that carries the corresponding result.

Where a statement differs from the paper, its docstring says how and why.

Uniformity of constants. Where the paper calls a constant "universal" and later uses it
uniformly over a family of data (the shifts `g + a` in Propositions [6.1](#AFS:p.inner-smallest) and
[6.2](#AFS:p.inner-largest)), the constant is quantified *before* the data: the interior Lipschitz
constant `C` of [(3.13)](#AFS:eqn:LipEst) depends only on the setting (and on `β`), the perimeter
constant of [(3.14)](#AFS:eqn:chiEst2) only on the setting and bounds `M` (sup-norm) and `E0`
(energy) of the data, and the constants of [(3.15)](#AFS:eqn:inftyLip)–[(3.16)](#AFS:eqn:inftyPerim)
only on the constants of the hypotheses.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- The energy bound `∫_U |G|² + Q_max² |U|` for data with (weak) gradient `G`; for `G = ∇g` this
is `E₀` of [Lemma 3.11(iv)](#AFS:part.gep-4). -/
noncomputable def energyBound (S : Setting d) (G : E d → E d) : ℝ≥0∞ :=
  ∫⁻ x in S.U, ENNReal.ofReal (‖G x‖ ^ 2 + S.Qmax ^ 2)

/-! ### [Proposition 3.12](#AFS:p.semilinear-wellposed) (semilinear well-posedness) -/

/-- The conclusions (data, (i)–(v)) of **[Proposition 3.12](#AFS:p.semilinear-wellposed)** for a
family `(gε ε, uε ε)`, `0 < ε < ε₀`, with `increasing = true` for strict subsolution data (resp.
`false` for strict supersolution data).
* (solution) `uε ε` solves [(3.4)](#AFS:e.bernoulli-parabolic-semilinear) with data
  `gε ε ∈ C^{0,1}(Ū)`;
* (data, [Lemma 3.11](#AFS:l.well-prepared)) `g₊ ≤ gε ≤ g₊ + ε` on `Ū`,
  `‖∇gε‖_{L^∞(U)} ≤ ‖∇g‖_{L^∞(U)}`, `J(gε, χ⁰_ε; U) ≤ E₀`, and (Lipschitz form) every Lipschitz
  constant of `g` on `Ū` is one of `gε`, which makes the modulus of
  [Proposition B.5](#AFS:p.attainment) depend on `g` only through `(Lip g, sup |g|)`;
  `gε ∈ H¹(U)` with weak gradient its pointwise gradient;
* (i) `t ↦ uε(x, t)` monotone for `x ∈ Ū`, and [(3.8)](#AFS:e.Linfty): `0 ≤ uε ≤ ‖g‖_{L^∞(U)} + ε`
  on `Ū × [0, ∞)`;
* (ii) the energy dissipation inequality [(3.9)](#AFS:e.dissipation-eps), with `≤`, for every
  `T > 0`;
* (iii) the interior Lipschitz bound [(3.10)](#AFS:e.localEst) with a constant `C` independent of
  `ε`, and `sup_{t > 0} ‖∇uε(·, t)‖_{L^∞(V)} ≤ C_V` for `V ⊂⊂ U`, `C_V` independent of `ε`;
* (iv) a modulus of continuity `ϖ` on `Ū × [0, ∞)` independent of `ε` (`uε = gε` on `∂_P U_∞` is
  part of the solution property);
* (v) for `K ⊂⊂ Ū \ \overline{{g > 0}}` there is `τ > 0` with `K ⊆ {uε(·, t) < ε}` for
  `0 ≤ t ≤ τ` and all sufficiently small `ε`;
* (v*) (increasing case only) for compact `K ⊆ U \ \overline{{g > 0}}` there is `τ > 0` such
  that for **every** `κ > 0`, `K ⊆ {uε(·, t) < κ ε}` for `0 ≤ t ≤ τ` and all sufficiently small
  `ε` (depending on `κ`). Same barrier as [Lemma B.8](#AFS:l.positivity-trace), with the
  super-profile parameter `θ̂ ↓ 1` so that its floor `κ_θ̂ ↓ 0`; it uses `gε = 0` near `K`.

Differences from the paper:
* The paper states [(3.9)](#AFS:e.dissipation-eps) as an equality; here it is the inequality `≤`,
  because only `≤` is used later, and the inequality is what the truncation argument for classical
  solutions with `H¹` data proves.
* The Lipschitz form of the data clause is added: the paper states in (iv) that the modulus
  depends on `g` only through `‖g‖_{L^∞}` and `‖∇g‖_{L^∞}`; here (iv) only asserts a modulus for
  the family, and the dependence on `g` only through `(Lip g, sup |g|)`, which makes the modulus
  uniform over the shifts `g + a` in Propositions [6.1](#AFS:p.inner-smallest) and
  [6.2](#AFS:p.inner-largest), is carried by the Lipschitz form of the data clause. -/
def IsWellPreparedFamily (S : Setting d) (g : E d → ℝ) (β : ℝ → ℝ) (increasing : Bool)
    (ε₀ : ℝ) (gε : ℝ → E d → ℝ) (uε : ℝ → E d × ℝ → ℝ) : Prop :=
  0 < ε₀ ∧
  (∀ ε ∈ Ioo 0 ε₀,
    IsSemilinearSolution S.U S.Q β ε (gε ε) (uε ε) ∧
    (∃ K, LipschitzOnWith K (gε ε) (closure S.U)) ∧
    (∀ x ∈ closure S.U, max (g x) 0 ≤ gε ε x ∧ gε ε x ≤ max (g x) 0 + ε) ∧
    (∀ M : ℝ, (∀ x ∈ S.U, ‖∇ g x‖ ≤ M) → ∀ x ∈ S.U, ‖∇ (gε ε) x‖ ≤ M) ∧
    MemH1 S.U (gε ε) (∇ (gε ε)) ∧
    energyJχ S.U S.Q (∇ (gε ε)) (fun x ↦ chiEps β ε (uε ε) (x, 0)) ≤ energyBound S (∇ g) ∧
    (if increasing then MonotoneInTime (uε ε) (closure S.U) (Ici 0)
      else AntitoneInTime (uε ε) (closure S.U) (Ici 0)) ∧
    (∀ M : ℝ, (∀ x ∈ S.U, |g x| ≤ M) →
      ∀ p ∈ closure S.U ×ˢ Ici 0, 0 ≤ uε ε p ∧ uε ε p ≤ M + ε) ∧
    (∀ T : ℝ, 0 < T →
      energyJχ S.U S.Q (fun x ↦ gradₓ (uε ε) (x, T)) (fun x ↦ chiEps β ε (uε ε) (x, T)) / 2 +
          ∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ (uε ε) p ^ 2) ≤
        energyJχ S.U S.Q (∇ (gε ε)) (fun x ↦ chiEps β ε (uε ε) (x, 0)) / 2) ∧
    -- data, Lipschitz form: Lipschitz constants of `g` on `Ū` are ones of `gε`
    ∀ K : NNReal, LipschitzOnWith K g (closure S.U) → LipschitzOnWith K (gε ε) (closure S.U)) ∧
  (∃ C : ℝ, ∀ ε ∈ Ioo 0 ε₀, InteriorLipEst S.U (uε ε) C) ∧
  (∀ V : Set (E d), CompactlyContained V S.U → ∃ CV : ℝ, ∀ ε ∈ Ioo 0 ε₀, ∀ x ∈ V, ∀ t : ℝ,
    0 < t → ‖gradₓ (uε ε) (x, t)‖ ≤ CV) ∧
  (∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧ ∀ ε ∈ Ioo 0 ε₀,
    ∀ p ∈ closure S.U ×ˢ Ici 0, ∀ q ∈ closure S.U ×ˢ Ici 0,
      |uε ε p - uε ε q| ≤ ϖ (‖p.1 - q.1‖ + |p.2 - q.2|)) ∧
  (∀ K : Set (E d), IsCompact K → K ⊆ closure S.U \ closure (posSet g (closure S.U)) →
    ∃ τ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ → ∀ x ∈ K, ∀ t ∈ Icc 0 τ, uε ε (x, t) < ε) ∧
  -- (v*) (increasing case): below every level `κ ε` near `{g < 0}` for short times
  (increasing = true → ∀ K : Set (E d), IsCompact K → K ⊆ S.U \ closure (posSet g (closure S.U)) →
    ∃ τ > 0, ∀ κ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ → ∀ x ∈ K, ∀ t ∈ Icc 0 τ,
      uε ε (x, t) < κ * ε)

/-- **[Proposition 3.12](#AFS:p.semilinear-wellposed)**. For a reaction profile `β` and a smooth
strict subsolution (resp. supersolution) `g`, for all sufficiently small `ε > 0` there are data `gε`
and solutions `uε` of [(3.4)](#AFS:e.bernoulli-parabolic-semilinear) with the data properties and
(i)–(v) (monotone increasing, resp. decreasing, in time). For the differences from the paper
([(3.9)](#AFS:e.dissipation-eps) as an inequality, the added items) see `IsWellPreparedFamily`. -/
def SemilinearWellposedStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (g : E d → ℝ) (β : ℝ → ℝ), IsReactionProfile β →
    (IsStrictSub S.U S.Q g →
      ∃ (ε₀ : ℝ) (gε : ℝ → E d → ℝ) (uε : ℝ → E d × ℝ → ℝ),
        IsWellPreparedFamily S g β true ε₀ gε uε) ∧
    (IsStrictSuper S.U S.Q g →
      ∃ (ε₀ : ℝ) (gε : ℝ → E d → ℝ) (uε : ℝ → E d × ℝ → ℝ),
        IsWellPreparedFamily S g β false ε₀ gε uε)

/-! ### [Theorem 3.13](#AFS:t.parabolic-existence) (parabolic existence) -/

/-- The common conclusions (i), (iii), (v) of **[Theorem 3.13](#AFS:t.parabolic-existence)** for
`(u, χ)` with `∂ₜu = w`: `u ∈ C(Ū × [0, ∞))` with `u = g₊` on `∂_P U_∞`; `(u, χ)` is a parabolic
inner variational solution; the weak heat [equation (4.6)](#AFS:eqn:weakHeat) in `{u > 0}`; the
estimates [(3.12)](#AFS:eqn:diss2) (with right-hand side `E₀ = energyBound S (∇g)`),
[(3.13)](#AFS:eqn:LipEst) (constant `C`) and [(3.14)](#AFS:eqn:chiEst2) (constant function
`Cper`). -/
def ParabolicExistenceCommon (S : Setting d) (g : E d → ℝ) (C : ℝ) (Cper : ℝ → ℝ → ℝ)
    (u w χ : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (closure S.U ×ˢ Ici 0) ∧ (∀ p ∈ parBdryInf S.U, u p = max (g p.1) 0) ∧
    IsParaInnerVarSolution S.U S.Q u w χ ∧ WeakHeatInPos S.U u w ∧
    DissipationIneq S.U S.Q u w χ (energyBound S (∇ g)) ∧
    InteriorLipEst S.U u C ∧ WeightedPerimeterEst S.U χ Cper

/-- **[Theorem 3.13](#AFS:t.parabolic-existence)**. For a smooth strict subsolution (resp.
supersolution) `g` there is `(u, χ)` with (i) `u ∈ C(Ū × [0, ∞))`, `u = g₊` on `∂_P U_∞`; (ii) `u`
monotone increasing (resp. decreasing) in time; (iii) `(u, χ)` a parabolic inner variational
solution; (iv) `u` a viscosity solution (resp. `(u, E)` a relaxed viscosity solution for some `E`)
in `U_∞`; (v) the estimates [(3.12)](#AFS:eqn:diss2)–[(3.14)](#AFS:eqn:chiEst2).

Differences from the paper:
* The heat equation in `{u > 0}`, which the paper includes in
  [Definition 3.8](#AFS:d.parabolic-inner), is exported separately in its weak form
  [(4.6)](#AFS:eqn:weakHeat) (see `WeakHeatInPos`).
* In the increasing case we also export that `u` vanishes near `t = 0` on compact sets away from
  `\overline{{g > 0}}`. This follows from [Proposition 3.12(v)](#AFS:part.trace); the proof of
  [Proposition 6.1](#AFS:p.inner-smallest) uses it (citing [Proposition 3.12(v)](#AFS:part.trace)
  directly) to get the strict ordering of [Theorem 3.7](#AFS:t.comparison) on a neighbourhood of the
  parabolic boundary.
* The constant `C` of [(3.13)](#AFS:eqn:LipEst) is universal (depends only on the setting), and the
  function `Cper` of [(3.14)](#AFS:eqn:chiEst2) depends only on the setting and on bounds
  `M ≥ sup_U |g|`, `E0 ≥ E₀` (`E0 < ∞`); see the module docstring. -/
def ParabolicExistenceStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d), ∃ C : ℝ, ∀ (M : ℝ) (E0 : ℝ≥0∞), E0 ≠ ⊤ → ∃ Cper : ℝ → ℝ → ℝ,
    ∀ g : E d → ℝ, (∀ x ∈ S.U, |g x| ≤ M) → energyBound S (∇ g) ≤ E0 →
      (IsStrictSub S.U S.Q g → ∃ u w χ : E d × ℝ → ℝ,
        ParabolicExistenceCommon S g C Cper u w χ ∧ MonotoneInTime u (closure S.U) (Ici 0) ∧
          IsParaSolution S.U S.Q (Ioi 0) u ∧
          -- no outward jump of `{u > 0}` at `t = 0` (from [Prop 3.12(v)](#AFS:part.trace); used in
          -- [Prop 6.1](#AFS:p.inner-smallest))
          ∀ K : Set (E d), IsCompact K → K ⊆ closure S.U \ closure (posSet g (closure S.U)) →
            ∃ τ > 0, ∀ x ∈ K, ∀ t ∈ Icc 0 τ, u (x, t) = 0) ∧
      (IsStrictSuper S.U S.Q g → ∃ u w χ : E d × ℝ → ℝ,
        ParabolicExistenceCommon S g C Cper u w χ ∧ AntitoneInTime u (closure S.U) (Ici 0) ∧
          ∃ Eset : Set (E d × ℝ), IsParaRelaxedSolution S.U S.Q (Ioi 0) u Eset)

/-! ### [Theorem 3.14](#AFS:t.longtime-inner) (long-time limit, variational form) -/

/-- **[Theorem 3.14](#AFS:t.longtime-inner)**. Let `(u, χ)` (with `∂ₜu = w`) be a parabolic inner
variational solution in `U_∞`, bounded by `M`, satisfying the weak heat
[equation (4.6)](#AFS:eqn:weakHeat) in `{u > 0}`, [(3.12)](#AFS:eqn:diss2) with a finite energy
bound `E0`, [(3.13)](#AFS:eqn:LipEst) with constant `C` and [(3.14)](#AFS:eqn:chiEst2) with constant
function `Cper`. Then there are a sequence `tᵢ → ∞` and functions `u_∞`, `χ_∞` such that
`u(·, tᵢ) → u_∞` locally uniformly in `U`, `∇u(·, tᵢ) → ∇u_∞` in `L²_loc(U)` (with the uniform
convergence, `u(·, tᵢ) → u_∞` in `H¹_loc(U)`), `χ(·, tᵢ) → χ_∞` in `L¹_loc(U)`, and `(u_∞, χ_∞)` is
an inner variational solution in `U`; [(3.15)](#AFS:eqn:inftyLip) and [(3.16)](#AFS:eqn:inftyPerim)
hold, with the constant `C` of [(3.13)](#AFS:eqn:LipEst) in [(3.15)](#AFS:eqn:inftyLip) and `C_V`
depending only on `V` and `M, E0, C, Cper`.

As in the paper, no time monotonicity is assumed. For flows monotone in time the limit holds as
`t → ∞` along all times: `LongtimeInnerMonotoneStatement`.

Differences from the paper:
* The heat equation in `{u > 0}`, which the paper includes in
  [Definition 3.8](#AFS:d.parabolic-inner), is a separate hypothesis here, in its weak form
  [(4.6)](#AFS:eqn:weakHeat) (see `WeakHeatInPos`).
* In [(3.15)](#AFS:eqn:inftyLip), `‖u_∞‖_{L^∞(B_{2r}(x))}` is replaced by any bound `M'` of `|u_∞|`
  on `B_{2r}(x)` (equivalent). -/
def LongtimeInnerStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (M : ℝ) (E0 : ℝ≥0∞) (C : ℝ) (Cper : ℝ → ℝ → ℝ), E0 ≠ ⊤ →
    ∃ CV : Set (E d) → ℝ, ∀ u w χ : E d × ℝ → ℝ,
      IsParaInnerVarSolution S.U S.Q u w χ → WeakHeatInPos S.U u w → (∀ p ∈ UInf S.U, u p ≤ M) →
      DissipationIneq S.U S.Q u w χ E0 → InteriorLipEst S.U u C →
      WeightedPerimeterEst S.U χ Cper →
      ∃ (t : ℕ → ℝ) (uInf χInf : E d → ℝ), Tendsto t atTop atTop ∧
        TendstoLocallyUniformlyOn (fun i x ↦ u (x, t i)) uInf atTop S.U ∧
        TendstoLpLoc 2 volume S.U (fun i x ↦ gradₓ u (x, t i)) (∇ uInf) atTop ∧
        TendstoLpLoc 1 volume S.U (fun i x ↦ χ (x, t i)) χInf atTop ∧
        IsInnerVarSolution S.U S.Q uInf χInf ∧
        (∀ (x : E d) (r : ℝ), 0 < r → r ≤ 1 → ball x (2 * r) ⊆ S.U →
          ∀ M' : ℝ, (∀ y ∈ ball x (2 * r), |uInf y| ≤ M') →
            ∀ y ∈ ball x r, ‖∇ uInf y‖ ≤ C * (M' / r + 1)) ∧
        ∀ V : Set (E d), CompactlyContained V S.U →
          totalVariationOn V χInf ≤ ENNReal.ofReal (CV V)

/-- **[Theorem 3.14](#AFS:t.longtime-inner) for flows monotone in time**: under the hypotheses of
`LongtimeInnerStatement` and time monotonicity (increasing or decreasing), `u(·, t) → u_∞` locally
uniformly in `U` as `t → ∞` along all times, and the other conclusions of
[Theorem 3.14](#AFS:t.longtime-inner) hold along some `tᵢ → ∞`.

This is the form used in Propositions [6.1](#AFS:p.inner-smallest) and [6.2](#AFS:p.inner-largest)
(which set `u_{a,∞} := lim_{t→∞} 𝔲_a(·, t)`) and in [Lemma 5.8](#AFS:l.subsolution-inner-limit) /
[Theorem 3.16(ii)](#AFS:part.longtime-viscosity-2). The paper justifies the full limit in the remark
after [Lemma 5.8](#AFS:l.subsolution-inner-limit) (label `l.subsolution-inner-limit`; for monotone
flows the limit as `t → ∞` exists, and it is locally uniform by Arzelà–Ascoli and
[(3.13)](#AFS:eqn:LipEst)). It follows from `LongtimeInnerStatement`
(`LongtimeInnerStatement.monotone`, `Inner/LongTimeMonotone.lean`). -/
def LongtimeInnerMonotoneStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (M : ℝ) (E0 : ℝ≥0∞) (C : ℝ) (Cper : ℝ → ℝ → ℝ), E0 ≠ ⊤ →
    ∃ CV : Set (E d) → ℝ, ∀ u w χ : E d × ℝ → ℝ,
      IsParaInnerVarSolution S.U S.Q u w χ → WeakHeatInPos S.U u w → (∀ p ∈ UInf S.U, u p ≤ M) →
      (MonotoneInTime u S.U (Ioi 0) ∨ AntitoneInTime u S.U (Ioi 0)) →
      DissipationIneq S.U S.Q u w χ E0 → InteriorLipEst S.U u C →
      WeightedPerimeterEst S.U χ Cper →
      ∃ uInf : E d → ℝ, TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop S.U ∧
        ∃ (t : ℕ → ℝ) (χInf : E d → ℝ), Tendsto t atTop atTop ∧
          TendstoLpLoc 2 volume S.U (fun i x ↦ gradₓ u (x, t i)) (∇ uInf) atTop ∧
          TendstoLpLoc 1 volume S.U (fun i x ↦ χ (x, t i)) χInf atTop ∧
          IsInnerVarSolution S.U S.Q uInf χInf ∧
          (∀ (x : E d) (r : ℝ), 0 < r → r ≤ 1 → ball x (2 * r) ⊆ S.U →
            ∀ M' : ℝ, (∀ y ∈ ball x (2 * r), |uInf y| ≤ M') →
              ∀ y ∈ ball x r, ‖∇ uInf y‖ ≤ C * (M' / r + 1)) ∧
          ∀ V : Set (E d), CompactlyContained V S.U →
            totalVariationOn V χInf ≤ ENNReal.ofReal (CV V)

/-! ### [Theorem 3.16](#AFS:t.longtime-viscosity) (long-time limit, viscosity form) -/

/-- **[Theorem 3.16(i)](#AFS:part.longtime-viscosity-1)** (proved via
[Proposition 5.6](#AFS:p.supersolution-limit) and [Corollary 5.7](#AFS:c.monotone-long-time)). A
bounded viscosity solution of [(3.1)](#AFS:e.bernoulli-parabolic) in `U × (0, ∞)`, monotonically
increasing in time, with `u(·, t) ↗ u_∞` locally uniformly in `U`: then `u_∞` is a viscosity
solution of [(1.1)](#AFS:e.bernoulli-basic) in `U`. -/
def LongtimeViscIncreasingStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (u : E d × ℝ → ℝ) (uInf : E d → ℝ),
    IsParaSolution S.U S.Q (Ioi 0) u → (∃ M : ℝ, ∀ p ∈ UInf S.U, u p ≤ M) →
    MonotoneInTime u S.U (Ioi 0) →
    TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop S.U →
    IsViscSolution S.U S.Q uInf

/-- **[Theorem 3.16(ii)](#AFS:part.longtime-viscosity-2)**
([Lemma 5.8](#AFS:l.subsolution-inner-limit)). A bounded parabolic inner variational solution
`(u, χ)`, monotone in time, which is a viscosity supersolution and satisfies
[(4.6)](#AFS:eqn:weakHeat) and [(3.12)](#AFS:eqn:diss2)–[(3.14)](#AFS:eqn:chiEst2): along some
`tᵢ → ∞`, `u(·, tᵢ) → u_∞` locally uniformly, `χ(·, tᵢ) → χ_∞` in `L¹_loc`, and `u_∞` is a viscosity
solution of [(1.1)](#AFS:e.bernoulli-basic). Time monotonicity is a hypothesis, as in the paper; the
weak heat [equation (4.6)](#AFS:eqn:weakHeat) is a separate hypothesis, as in
`LongtimeInnerStatement` ([Theorem 3.14](#AFS:t.longtime-inner)). -/
def LongtimeViscInnerStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (u w χ : E d × ℝ → ℝ) (M : ℝ) (E0 : ℝ≥0∞) (C : ℝ)
    (Cper : ℝ → ℝ → ℝ),
    IsParaInnerVarSolution S.U S.Q u w χ → WeakHeatInPos S.U u w → IsParaSuper S.U S.Q (Ioi 0) u →
    (∀ p ∈ UInf S.U, u p ≤ M) → (MonotoneInTime u S.U (Ioi 0) ∨ AntitoneInTime u S.U (Ioi 0)) →
    E0 ≠ ⊤ → DissipationIneq S.U S.Q u w χ E0 →
    InteriorLipEst S.U u C → WeightedPerimeterEst S.U χ Cper →
    ∃ (t : ℕ → ℝ) (uInf χInf : E d → ℝ), Tendsto t atTop atTop ∧
      TendstoLocallyUniformlyOn (fun i x ↦ u (x, t i)) uInf atTop S.U ∧
      TendstoLpLoc 1 volume S.U (fun i x ↦ χ (x, t i)) χInf atTop ∧
      IsViscSolution S.U S.Q uInf

/-! ### [Proposition 4.1](#AFS:p.eps-inner-limit) (ε → 0 limit, variational form) -/

/-- **[Proposition 4.1](#AFS:p.eps-inner-limit)**. Assume [(3.5)](#AFS:e.beta-conditions), `gε → g`
weakly in `H¹(U; [0, ∞))` as `ε → 0⁺` (weak gradients `Gε ε`, `Gg` as data) with
`sup_ε ‖gε‖_{L^∞(U)} ≤ M`, and let `uε ε` solve [(3.4)](#AFS:e.bernoulli-parabolic-semilinear) with
data `gε ε` for `0 < ε < ε₀`. Let `E0` bound the initial energies, `J(gε, χ⁰_ε; U) ≤ E0`
([Lemma 3.11(iv)](#AFS:part.gep-4)). Then along some `ε_j ↓ 0` there is `(u, χ)` (with
`∂ₜu = w`) such that
(i) `uε ε_j → u` locally uniformly in `U_∞`, `∇uε ε_j ⇀ ∇u` weakly in `L²(U × (0, T))` for every
    `T > 0`, `χ_{ε_j} → χ` in `L¹_loc(U_∞)` and a.e., `χ ∈ {0, 1}` a.e.;
(ii) `(u, χ)` is a parabolic inner variational solution in `U_∞`, and it satisfies the weak heat
[equation (4.6)](#AFS:eqn:weakHeat) in `{u > 0}` (proved in [§4.2](#AFS:subsec:strongGrad) of the
paper; recorded here because [Theorem 3.14](#AFS:t.longtime-inner) needs it, see `WeakHeatInPos`);
(iii) [(3.12)](#AFS:eqn:diss2) with right-hand side `E0`, [(3.13)](#AFS:eqn:LipEst) and
[(3.14)](#AFS:eqn:chiEst2) hold. The constant `C` of [(3.13)](#AFS:eqn:LipEst) depends only on the
setting and `β`; `Cper` only on these and the bounds `M`, `Ebd ≥ E0`, `Ebd < ∞`.

Weak `H¹(U)` convergence is written out: `∫_U gε φ → ∫_U g φ` and `∫_U Gε · Φ → ∫_U Gg · Φ` for
all `φ, Φ ∈ L²(U)`. (`TendstoWeakL2` asks for `L²` membership at every index, and `gε ε` is only
given for `0 < ε < ε₀`.)

Differences from the paper:
* The limit `g` and the weak convergence `gε ⇀ g` are extra hypotheses. The paper's statement
  does not have them, and the proof does not use them.
* The paper's (i) also states strong convergence of `∇uε_j` in `L²_loc(U_∞)`
  ([Lemma 4.2](#AFS:lem:strongGrad), proved in `Inner/StrongConv.lean`); here (i) records only the
  weak convergence in `L²(U × (0, T))` for every `T`. -/
def EpsInnerLimitStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (β : ℝ → ℝ), IsReactionProfile β →
    ∃ C : ℝ, ∀ (M : ℝ) (Ebd : ℝ≥0∞), Ebd ≠ ⊤ → ∃ Cper : ℝ → ℝ → ℝ,
    ∀ (ε₀ : ℝ) (g : E d → ℝ) (Gg : E d → E d) (gε : ℝ → E d → ℝ) (Gε : ℝ → E d → E d)
      (uε : ℝ → E d × ℝ → ℝ) (E0 : ℝ≥0∞), 0 < ε₀ →
      MemH1 S.U g Gg → (∀ ε ∈ Ioo 0 ε₀, MemH1 S.U (gε ε) (Gε ε)) →
      (∀ φ : E d → ℝ, MemLp φ 2 (volume.restrict S.U) →
        Tendsto (fun ε ↦ ∫ x in S.U, gε ε x * φ x) (𝓝[>] 0) (𝓝 (∫ x in S.U, g x * φ x))) →
      (∀ Φ : E d → E d, MemLp Φ 2 (volume.restrict S.U) →
        Tendsto (fun ε ↦ ∫ x in S.U, inner ℝ (Gε ε x) (Φ x)) (𝓝[>] 0)
          (𝓝 (∫ x in S.U, inner ℝ (Gg x) (Φ x)))) →
      (∀ ε ∈ Ioo 0 ε₀, ∀ x ∈ S.U, 0 ≤ gε ε x ∧ gε ε x ≤ M) →
      E0 ≤ Ebd →
      (∀ ε ∈ Ioo 0 ε₀, energyJχ S.U S.Q (Gε ε) (fun x ↦ chiEps β ε (uε ε) (x, 0)) ≤ E0) →
      (∀ ε ∈ Ioo 0 ε₀, IsSemilinearSolution S.U S.Q β ε (gε ε) (uε ε)) →
      ∃ (εs : ℕ → ℝ) (u w χ : E d × ℝ → ℝ),
        (∀ j, εs j ∈ Ioo 0 ε₀) ∧ StrictAnti εs ∧ Tendsto εs atTop (𝓝 0) ∧
        -- (i) compactness
        TendstoLocallyUniformlyOn (fun j ↦ uε (εs j)) u atTop (UInf S.U) ∧
        (∀ T : ℝ, 0 < T → TendstoWeakL2 volume (S.U ×ˢ Ioo 0 T)
          (fun j ↦ gradₓ (uε (εs j))) (gradₓ u) atTop) ∧
        TendstoLpLoc 1 volume (UInf S.U) (fun j ↦ chiEps β (εs j) (uε (εs j))) χ atTop ∧
        (∀ᵐ p ∂(volume.restrict (UInf S.U)),
          Tendsto (fun j ↦ chiEps β (εs j) (uε (εs j)) p) atTop (𝓝 (χ p))) ∧
        (∀ᵐ p ∂(volume.restrict (UInf S.U)), χ p = 0 ∨ χ p = 1) ∧
        -- (ii) existence
        IsParaInnerVarSolution S.U S.Q u w χ ∧
        -- [(4.6)](#AFS:eqn:weakHeat) weak heat equation in the positivity set (needed by
        -- [Theorem 3.14](#AFS:t.longtime-inner))
        WeakHeatInPos S.U u w ∧
        -- (iii) estimates
        DissipationIneq S.U S.Q u w χ E0 ∧ InteriorLipEst S.U u C ∧
        WeightedPerimeterEst S.U χ Cper

/-! ### The ε → 0 limit, viscosity form

[Proposition 5.3](#AFS:p.semilinear-limit-viscosity) and [Corollary 5.4](#AFS:cor:increasing). -/

/-- The set `E = limsup* {uε_j > ε_j}`, the sets taken in `U × I` (the term `κ = 1` of
`semilinearLimitSetStar`). -/
def semilinearLimitSet (U : Set (E d)) (I : Set ℝ) (εs : ℕ → ℝ) (us : ℕ → E d × ℝ → ℝ) :
    Set (E d × ℝ) :=
  upperKLimit (fun j ↦ {p ∈ U ×ˢ I | εs j < us j p}) atTop

/-- The set `E* = \overline{⋃_{0 < κ ≤ 1} limsup* {uε_j > κ ε_j}}` of
[Proposition 5.3](#AFS:p.semilinear-limit-viscosity). It contains `semilinearLimitSet` (`κ = 1`)
and, unlike it, every point where the `uε_j` are not `o(ε_j)`. -/
def semilinearLimitSetStar (U : Set (E d)) (I : Set ℝ) (εs : ℕ → ℝ) (us : ℕ → E d × ℝ → ℝ) :
    Set (E d × ℝ) :=
  closure (⋃ κ ∈ Ioc (0 : ℝ) 1, upperKLimit (fun j ↦ {p ∈ U ×ˢ I | κ * εs j < us j p}) atTop)

/-- **[Proposition 5.3](#AFS:p.semilinear-limit-viscosity)**. If `u_j` (nonnegative) solve the
semilinear equation with `ε_j → 0` in `U × (0, T]` and `u_j → u` locally uniformly in `U × (0, T]`,
then `(u, E*)` is a relaxed viscosity solution of [(3.1)](#AFS:e.bernoulli-parabolic) in
`U × (0, T]`, where `E* = \overline{⋃_{0<κ≤1} limsup* {u_j > κ ε_j}}` (`semilinearLimitSetStar`).

With the smaller set `E = limsup* {u_j > ε_j}` (`semilinearLimitSet`) the statement fails: for
`U = B₁`, `Q ≡ 1`, `u_j = ε_j (1 + h)` with `h ≥ 0` the heat kernel from a point outside `Ū`
switched on at time `t₀` (a solution since `β = 0` on `[1, ∞)`), one gets `u ≡ 0` and
`E = Ū × [t₀, T]`, and the strict supersolution `φ = A(|x|² - ρ²) + B(t - t₀)` violates the
relaxed subsolution property at `(0, t₀)`. -/
def SemilinearLimitRelaxedStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (β : ℝ → ℝ), IsReactionProfile β →
    ∀ (T : ℝ) (εs : ℕ → ℝ) (us : ℕ → E d × ℝ → ℝ) (u : E d × ℝ → ℝ), 0 < T →
      (∀ j, 0 < εs j) → Tendsto εs atTop (𝓝 0) →
      (∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j)) →
      (∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p) →
      TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T) →
      IsParaRelaxedSolution S.U S.Q (Ioc 0 T) u (semilinearLimitSetStar S.U (Ioc 0 T) εs us)

/-- **[Corollary 5.4](#AFS:cor:increasing)**. If the `uε` are as in
[Proposition 3.12](#AFS:p.semilinear-wellposed) with `g` a strict subsolution, `uε ε_j → u` with
`ε_j → 0`, and `E = E* = \overline{⋃_{0<κ≤1} limsup* {uε ε_j > κ ε_j}}` (`semilinearLimitSetStar`),
then `u` is monotone increasing in `t`, `E = \overline{{u > 0}}` inside `U × [0, T]`, and `u` is a
viscosity solution of [(3.1)](#AFS:e.bernoulli-parabolic) in `U × (0, T]`. -/
def SemilinearLimitIncreasingStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (g : E d → ℝ) (β : ℝ → ℝ) (ε₀ : ℝ) (gε : ℝ → E d → ℝ)
    (uε : ℝ → E d × ℝ → ℝ), IsReactionProfile β → IsStrictSub S.U S.Q g →
    IsWellPreparedFamily S g β true ε₀ gε uε →
    ∀ (T : ℝ) (εs : ℕ → ℝ) (u : E d × ℝ → ℝ), 0 < T → (∀ j, εs j ∈ Ioo 0 ε₀) →
      Tendsto εs atTop (𝓝 0) →
      TendstoLocallyUniformlyOn (fun j ↦ uε (εs j)) u atTop (S.U ×ˢ Ioc 0 T) →
      MonotoneInTime u S.U (Ioc 0 T) ∧
        semilinearLimitSetStar S.U (Ioc 0 T) εs (fun j ↦ uε (εs j)) ∩ (S.U ×ˢ Icc 0 T) =
          closure (posSetP u (S.U ×ˢ Ioc 0 T)) ∩ (S.U ×ˢ Icc 0 T) ∧
        IsParaSolution S.U S.Q (Ioc 0 T) u

/-! ### Extremal solutions

Propositions [6.1](#AFS:p.inner-smallest), [6.2](#AFS:p.inner-largest) and
[Proposition 6.3](#AFS:p.downward). -/

/-- **[Proposition 6.1](#AFS:p.inner-smallest)**. If `g` is a smooth strict subsolution with
`g > 0` on `∂U`, the smallest supersolution above `g` is both an inner variational and a
viscosity solution of [(1.1)](#AFS:e.bernoulli-basic) in `U`. We also export that it is continuous
on `Ū`: the "sandwich" argument uses that the limit `û`, extended by `g₊`, lies in `𝒮_g`, which
needs continuity up to `∂U`, and [Lemma 2.8](#AFS:l.local-minimality) needs `u ∈ C(Ū)`. The proof
gets it from the modulus of [Proposition 3.12(iv)](#AFS:part.attainment), which is uniform in `ε`,
`t` and the shifts `g + a`. -/
def InnerSmallestStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (g : E d → ℝ), IsStrictSub S.U S.Q g →
    (∀ x ∈ frontier S.U, 0 < g x) →
    IsViscSolution S.U S.Q (perronSmallest S.U S.Q g) ∧
      (∃ χ : E d → ℝ, IsInnerVarSolution S.U S.Q (perronSmallest S.U S.Q g) χ) ∧
      ContinuousOn (perronSmallest S.U S.Q g) (closure S.U)

/-- **[Proposition 6.2](#AFS:p.inner-largest)**. If `g` is a smooth strict supersolution, the
largest subsolution below `g` is both an inner variational and a viscosity solution of
[(1.1)](#AFS:e.bernoulli-basic) in `U`. As in [Proposition 6.1](#AFS:p.inner-smallest), we also
export that it is continuous on `Ū`. -/
def InnerLargestStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (g : E d → ℝ), IsStrictSuper S.U S.Q g →
    IsViscSolution S.U S.Q (perronLargest S.U S.Q g) ∧
      (∃ χ : E d → ℝ, IsInnerVarSolution S.U S.Q (perronLargest S.U S.Q g) χ) ∧
      ContinuousOn (perronLargest S.U S.Q g) (closure S.U)

/-- **[Proposition 6.3](#AFS:p.downward)**, with extra hypotheses: a local smallest supersolution
(resp. largest subsolution) `u` in the sense of [Definition 2.7](#AFS:d.largest-smallest) which is
moreover locally Lipschitz in `U` and `C²` and harmonic in `{u > 0}` is a downward (resp. upward)
minimizer of `J_Q(·; U)` ([Definition 2.15](#AFS:d.directional), in the form of
`IsDownwardMinimizer`).

The paper states the lemma for local extremal solutions only, and its proof obtains these
properties by citation (local extremal solutions are locally Lipschitz viscosity solutions, after
Feldman–Kim). Here they are hypotheses; [Theorem 1.1(iii)](#AFS:part.downward) supplies them from
[Theorem 1.1(ii)](#AFS:part.inner). -/
def DirectionalStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (u : E d → ℝ),
    LocallyLipschitzOn S.U u → ContDiffOn ℝ 2 u (posSet u S.U) →
    (∀ x ∈ posSet u S.U, Δ u x = 0) →
    (IsLocalSmallestSuper S.U S.Q u → IsDownwardMinimizer S.U S.Q u) ∧
    (IsLocalLargestSub S.U S.Q u → IsUpwardMinimizer S.U S.Q u)

end PerronVariational

end
