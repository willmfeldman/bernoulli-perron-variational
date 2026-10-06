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
uniformly over a family of data (the shifts `g + a` in Propositions 6.1 and 6.2), the constant
is quantified *before* the data: the interior Lipschitz constant `C` of (3.12) depends only on
the setting (and on `β`), the perimeter constant of (3.13) only on the setting and bounds `M`
(sup-norm) and `E0` (energy) of the data, and the constants of (3.14)–(3.15) only on the
constants of the hypotheses. The paper's statements do not say this explicitly, but its proofs
of Propositions 6.1 and 6.2 need it.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- The energy bound `∫_U |G|² + Q_max² |U|` for data with (weak) gradient `G`; for `G = ∇g` this
is `E₀` of Proposition 3.8(i). -/
noncomputable def energyBound (S : Setting d) (G : E d → E d) : ℝ≥0∞ :=
  ∫⁻ x in S.U, ENNReal.ofReal (‖G x‖ ^ 2 + S.Qmax ^ 2)

/-! ### Proposition 3.8 (semilinear well-posedness) -/

/-- The conclusions (i)–(vi) of **Proposition 3.8** for a family `(gε ε, uε ε)`, `0 < ε < ε₀`,
with `increasing = true` for strict subsolution data (resp. `false` for strict supersolution
data).
* (solution) `uε ε` solves (3.4) with data `gε ε ∈ C^{0,1}(Ū)`;
* (i) `g₊ ≤ gε ≤ g₊ + ε` on `Ū`, `‖∇gε‖_{L^∞(U)} ≤ ‖∇g‖_{L^∞(U)}`, `J(gε, χ⁰_ε; U) ≤ E₀`, and
  (Lipschitz form) every Lipschitz constant of `g` on `Ū` is one of `gε`, which makes the
  modulus of Proposition A.8 depend on `g` only through `(Lip g, sup |g|)`;
* (i') `gε ∈ H¹(U)` and `gε → g₊` in `H¹(U)` as `ε → 0⁺`;
* (ii) `t ↦ uε(x, t)` monotone for `x ∈ Ū`, and (3.7): `0 ≤ uε ≤ ‖g‖_{L^∞(U)} + ε` on
  `Ū × [0, ∞)`;
* (iii) the energy dissipation inequality (3.8), with `≤`, for every `T > 0`;
* (iv) the interior Lipschitz bound (3.9) with a constant `C` independent of `ε`, and
  `sup_{t > 0} ‖∇uε(·, t)‖_{L^∞(V)} ≤ C_V` for `V ⊂⊂ U`, `C_V` independent of `ε`;
* (v) a modulus of continuity `ϖ` on `Ū × [0, ∞)` independent of `ε` (`uε = gε` on `∂_P U_∞` is
  part of the solution property);
* (vi) for `K ⊂⊂ Ū \ \overline{{g > 0}}` there is `τ > 0` with `K ⊆ {uε(·, t) < ε}` for
  `0 ≤ t ≤ τ` and all sufficiently small `ε`;
* (vi*) (increasing case only) for compact `K ⊆ U \ \overline{{g > 0}}` there is `τ > 0` such
  that for **every** `κ > 0`, `K ⊆ {uε(·, t) < κ ε}` for `0 ≤ t ≤ τ` and all sufficiently small
  `ε` (depending on `κ`). Same barrier as Lemma A.11, with the super-profile parameter `θ̂ ↓ 1`
  so that its floor `κ_θ̂ ↓ 0`; it uses `gε = 0` near `K`.

Differences from the paper:
* The paper asserts `uε ∈ C^∞(U_∞)`; here solutions are classical `C^{2,1}`, because `Q` is only
  Lipschitz, which gives `C^{2,1}` and not `C^∞` regularity.
* The paper states (3.8) as an equality; here it is the inequality `≤`, because only `≤` is used
  later, and the inequality is what the truncation argument for classical solutions with `H¹`
  data proves.
* Item (i') is added: the proof of Theorem 3.9 applies Proposition 4.1, which needs `gε → g₊`
  in `H¹`, but the paper does not check this (it holds for the explicit data of Lemma A.4).
* The Lipschitz form of (i) is added: the modulus in (v) must be uniform over the shifts `g + a`
  in Propositions 6.1 and 6.2, and it depends on `g` only through `(Lip g, sup |g|)`.
* Item (vi*) is added, for the corrected set `E*` of Proposition 5.3 and Corollary 5.4 (see
  `semilinearLimitSetStar`): Corollary 5.4 then needs the positivity set to stay below every
  level `κ ε`, not just below `ε`, near `{g < 0}` for short times. -/
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
    -- (i), Lipschitz form: Lipschitz constants of `g` on `Ū` are ones of `gε`
    ∀ K : NNReal, LipschitzOnWith K g (closure S.U) → LipschitzOnWith K (gε ε) (closure S.U)) ∧
  -- (i') `gε → g₊` in `H¹(U)` (needed to apply Prop 4.1 in the proof of Thm 3.9)
  MemH1 S.U (fun x ↦ max (g x) 0) ({x | 0 < g x}.indicator (∇ g)) ∧
  Tendsto (fun ε ↦ eLpNorm (fun x ↦ gε ε x - max (g x) 0) 2 (volume.restrict S.U) +
      eLpNorm (fun x ↦ ∇ (gε ε) x - {x | 0 < g x}.indicator (∇ g) x) 2 (volume.restrict S.U))
    (𝓝[>] 0) (𝓝 0) ∧
  (∃ C : ℝ, ∀ ε ∈ Ioo 0 ε₀, InteriorLipEst S.U (uε ε) C) ∧
  (∀ V : Set (E d), CompactlyContained V S.U → ∃ CV : ℝ, ∀ ε ∈ Ioo 0 ε₀, ∀ x ∈ V, ∀ t : ℝ,
    0 < t → ‖gradₓ (uε ε) (x, t)‖ ≤ CV) ∧
  (∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧ ∀ ε ∈ Ioo 0 ε₀,
    ∀ p ∈ closure S.U ×ˢ Ici 0, ∀ q ∈ closure S.U ×ˢ Ici 0,
      |uε ε p - uε ε q| ≤ ϖ (‖p.1 - q.1‖ + |p.2 - q.2|)) ∧
  (∀ K : Set (E d), IsCompact K → K ⊆ closure S.U \ closure (posSet g (closure S.U)) →
    ∃ τ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ → ∀ x ∈ K, ∀ t ∈ Icc 0 τ, uε ε (x, t) < ε) ∧
  -- (vi*) (increasing case): below every level `κ ε` near `{g < 0}` for short times
  (increasing = true → ∀ K : Set (E d), IsCompact K → K ⊆ S.U \ closure (posSet g (closure S.U)) →
    ∃ τ > 0, ∀ κ > 0, ∃ ε₁ > 0, ∀ ε ∈ Ioo 0 ε₁, ε < ε₀ → ∀ x ∈ K, ∀ t ∈ Icc 0 τ,
      uε ε (x, t) < κ * ε)

/-- **Proposition 3.8**. For a reaction profile `β` and a smooth strict subsolution (resp.
supersolution) `g`, for all sufficiently small `ε > 0` there are data `gε` and solutions `uε` of
(3.4) with properties (i)–(vi) (monotone increasing, resp. decreasing, in time). For the
differences from the paper (`C^{2,1}` regularity, (3.8) as an inequality, the added items) see
`IsWellPreparedFamily`. -/
def SemilinearWellposedStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (g : E d → ℝ) (β : ℝ → ℝ), IsReactionProfile β →
    (IsStrictSub S.U S.Q g →
      ∃ (ε₀ : ℝ) (gε : ℝ → E d → ℝ) (uε : ℝ → E d × ℝ → ℝ),
        IsWellPreparedFamily S g β true ε₀ gε uε) ∧
    (IsStrictSuper S.U S.Q g →
      ∃ (ε₀ : ℝ) (gε : ℝ → E d → ℝ) (uε : ℝ → E d × ℝ → ℝ),
        IsWellPreparedFamily S g β false ε₀ gε uε)

/-! ### Theorem 3.9 (parabolic existence) -/

/-- The common conclusions (i), (iii), (v) of **Theorem 3.9** for `(u, χ)` with `∂ₜu = w`:
`u ∈ C(Ū × [0, ∞))` with `u = g₊` on `∂_P U_∞`; `(u, χ)` is a parabolic inner variational
solution; the weak heat equation (4.5) in `{u > 0}`; the estimates (3.11) (with right-hand side
`E₀ = energyBound S (∇g)`), (3.12) (constant `C`) and (3.13) (constant function `Cper`). -/
def ParabolicExistenceCommon (S : Setting d) (g : E d → ℝ) (C : ℝ) (Cper : ℝ → ℝ → ℝ)
    (u w χ : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (closure S.U ×ˢ Ici 0) ∧ (∀ p ∈ parBdryInf S.U, u p = max (g p.1) 0) ∧
    IsParaInnerVarSolution S.U S.Q u w χ ∧ WeakHeatInPos S.U u w ∧
    DissipationIneq S.U S.Q u w χ (energyBound S (∇ g)) ∧
    InteriorLipEst S.U u C ∧ WeightedPerimeterEst S.U χ Cper

/-- **Theorem 3.9**. For a smooth strict subsolution (resp. supersolution) `g` there is `(u, χ)`
with (i) `u ∈ C(Ū × [0, ∞))`, `u = g₊` on `∂_P U_∞`; (ii) `u` monotone increasing (resp.
decreasing) in time; (iii) `(u, χ)` a parabolic inner variational solution; (iv) `u` a viscosity
solution (resp. `(u, E)` a relaxed viscosity solution for some `E`) in `U_∞`; (v) the estimates
(3.11)–(3.13).

Differences from the paper:
* In (3.11) the paper's right-hand side `½ J(u(0), χ(0); U)` is replaced by the larger `½ E₀`,
  `E₀ = ∫_U |∇g|² + Q_max² |U|` (the bound of Proposition 3.8(i)), because Definition 3.7
  defines `χ` only on `U_∞`, so `χ(0)` has no meaning.
* (3.13) is in the form the paper's proof gives (see `WeightedPerimeterEst`).
* The weak heat equation (4.5) in `{u > 0}` is an extra conclusion, because Theorem 3.10 needs it
  as a hypothesis (see `WeakHeatInPos`).
* In the increasing case we also export that `u` vanishes near `t = 0` on compact sets away from
  `\overline{{g > 0}}`. This follows from Proposition 3.8(vi), and the proof of Proposition 6.1
  needs it (without saying so) to get the strict ordering of Theorem 3.6 on a neighbourhood of
  the parabolic boundary.
* The constant `C` of (3.12) is universal (depends only on the setting), and the function `Cper`
  of (3.13) depends only on the setting and on bounds `M ≥ sup_U |g|`, `E0 ≥ E₀` (`E0 < ∞`); see
  the module docstring. -/
def ParabolicExistenceStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d), ∃ C : ℝ, ∀ (M : ℝ) (E0 : ℝ≥0∞), E0 ≠ ⊤ → ∃ Cper : ℝ → ℝ → ℝ,
    ∀ g : E d → ℝ, (∀ x ∈ S.U, |g x| ≤ M) → energyBound S (∇ g) ≤ E0 →
      (IsStrictSub S.U S.Q g → ∃ u w χ : E d × ℝ → ℝ,
        ParabolicExistenceCommon S g C Cper u w χ ∧ MonotoneInTime u (closure S.U) (Ici 0) ∧
          IsParaSolution S.U S.Q (Ioi 0) u ∧
          -- no outward jump of `{u > 0}` at `t = 0` (from Prop 3.8(vi); used in Prop 6.1)
          ∀ K : Set (E d), IsCompact K → K ⊆ closure S.U \ closure (posSet g (closure S.U)) →
            ∃ τ > 0, ∀ x ∈ K, ∀ t ∈ Icc 0 τ, u (x, t) = 0) ∧
      (IsStrictSuper S.U S.Q g → ∃ u w χ : E d × ℝ → ℝ,
        ParabolicExistenceCommon S g C Cper u w χ ∧ AntitoneInTime u (closure S.U) (Ici 0) ∧
          ∃ Eset : Set (E d × ℝ), IsParaRelaxedSolution S.U S.Q (Ioi 0) u Eset)

/-! ### Theorem 3.10 (long-time limit, variational form) -/

/-- **Theorem 3.10**. Let `(u, χ)` (with `∂ₜu = w`) be a parabolic inner variational solution in
`U_∞`, bounded by `M`, satisfying the weak heat equation (4.5) in `{u > 0}`, (3.11) with a finite
energy bound `E0`, (3.12) with constant `C` and (3.13) with constant function `Cper`, and
**monotone in time** (increasing or decreasing). Then `u(·, t) → u_∞` locally uniformly in `U` as
`t → ∞`; along some `tᵢ → ∞`, `∇u(·, tᵢ) → ∇u_∞` in `L²_loc(U)` and `χ(·, tᵢ) → χ_∞` in
`L¹_loc(U)`, and `(u_∞, χ_∞)` is an inner variational solution in `U`; (3.14) and (3.15) hold.

Differences from the paper:
* The paper's hypotheses mention data `g_ε → g` in `H¹`, although the flow `(u, χ)` does not
  depend on `ε`; here the hypotheses are stated directly for the flow (bounded, finite initial
  energy, (3.11)–(3.13)).
* The paper assumes no time monotonicity; here we assume it, because Step 1 of the paper's proof
  ("by (3.11), `u(·, t)` is Cauchy in `L²`") does not follow: `∂ₜu ∈ L²(U_∞)` only gives
  `‖u(t) - u(s)‖_{L²} ≤ |t - s|^{1/2} ‖∂ₜu‖_{L²}`. Both applications (Propositions 6.1 and 6.2)
  have monotone flows, for which the limit exists by monotonicity.
* The weak heat equation (4.5) is an extra hypothesis, because the theorem is false without it
  (see `WeakHeatInPos`).
* The paper claims `H¹_loc` convergence along all `t → ∞`; its proof (Step 2) gives strong
  gradient convergence only along the good times `tᵢ`, and that is what we state.
* (3.14) is stated as in its proof and use: the same constant `C` as in (3.12) and the ball
  `B_{2r}` on the right-hand side, for `B_{2r}(x) ⊆ U`, `r ≤ 1`. The literal (3.14) has `B_r` on
  both sides and a constant depending on `V`, which is nearly vacuous and not what
  Propositions 6.1 and 6.2 use.
* (3.15): `C_V` depends only on `V` and the constants `M, E0, C, Cper` (the paper:
  `C_V = C_V(‖g‖_{H¹})`). -/
def LongtimeInnerStatement : Prop :=
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

/-! ### Theorem 3.12 (long-time limit, viscosity form) -/

/-- **Theorem 3.12(i)** (proved via Lemma 5.6 and Corollary 5.7). A bounded viscosity solution
of (3.1) in `U × (0, ∞)`, monotonically increasing in time, with `u(·, t) ↗ u_∞` locally
uniformly in `U`: then `u_∞` is a viscosity solution of (1.1) in `U`. -/
def LongtimeViscIncreasingStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (u : E d × ℝ → ℝ) (uInf : E d → ℝ),
    IsParaSolution S.U S.Q (Ioi 0) u → (∃ M : ℝ, ∀ p ∈ UInf S.U, u p ≤ M) →
    MonotoneInTime u S.U (Ioi 0) →
    TendstoLocallyUniformlyOn (fun t x ↦ u (x, t)) uInf atTop S.U →
    IsViscSolution S.U S.Q uInf

/-- **Theorem 3.12(ii)** (Lemma 5.8). A bounded parabolic inner variational solution `(u, χ)`,
monotone in time, which is a viscosity supersolution and satisfies (4.5) and (3.11)–(3.13): along
some `tᵢ → ∞`, `u(·, tᵢ) → u_∞` locally uniformly, `χ(·, tᵢ) → χ_∞` in `L¹_loc`, and `u_∞`
is a viscosity solution of (1.1). Time monotonicity and the weak heat equation (4.5) are
hypotheses here for the same reasons as in `LongtimeInnerStatement` (Theorem 3.10). -/
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

/-! ### Proposition 4.1 (ε → 0 limit, variational form) -/

/-- **Proposition 4.1**. Assume (3.5), `gε → g` in `H¹(U; [0, ∞))` as `ε → 0⁺` (weak gradients
`Gε ε`, `Gg` as data) with `sup_ε ‖gε‖_{L^∞(U)} ≤ M`, and let `uε ε` solve (3.4) with data
`gε ε` for `0 < ε < ε₀`. Then along some `ε_j ↓ 0` there is `(u, χ)` (with `∂ₜu = w`) such
that
(i) `uε ε_j → u` locally uniformly in `U_∞`, `∇uε ε_j ⇀ ∇u` weakly in `L²(U × (0, T))` for every
    `T > 0`, `χ_{ε_j} → χ` in `L¹_loc(U_∞)` and a.e., `χ ∈ {0, 1}` a.e.;
(ii) `(u, χ)` is a parabolic inner variational solution in `U_∞`, and it satisfies the weak heat
equation (4.5) in `{u > 0}` (proved in §4.2 of the paper; recorded here because Theorem 3.10
needs it, see `WeakHeatInPos`);
(iii) (3.11) (with right-hand side `E0 = ∫_U |∇g|² + Q_max² |U|`, cf. Proposition 3.8(i)),
(3.12) and (3.13) hold. The constant `C` of (3.12) depends only on the setting and `β`; `Cper`
only on these and the bounds `M`, `Ebd < ∞`.

The paper states weak convergence in `L²(U_∞)` (and has the typo `→ u` for `→ ∇u`); here it is
stated on `U × (0, T)` for every `T`, because `∇u` is in general only in `L^∞_t L²_x`, not in
`L²(U × (0, ∞))`, and this is what the proof, via (3.8), gives. -/
def EpsInnerLimitStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (β : ℝ → ℝ), IsReactionProfile β →
    ∃ C : ℝ, ∀ (M : ℝ) (Ebd : ℝ≥0∞), Ebd ≠ ⊤ → ∃ Cper : ℝ → ℝ → ℝ,
    ∀ (ε₀ : ℝ) (g : E d → ℝ) (Gg : E d → E d) (gε : ℝ → E d → ℝ) (Gε : ℝ → E d → E d)
      (uε : ℝ → E d × ℝ → ℝ), 0 < ε₀ →
      MemH1 S.U g Gg → (∀ ε ∈ Ioo 0 ε₀, MemH1 S.U (gε ε) (Gε ε)) →
      Tendsto (fun ε ↦ eLpNorm (gε ε - g) 2 (volume.restrict S.U) +
        eLpNorm (Gε ε - Gg) 2 (volume.restrict S.U)) (𝓝[>] 0) (𝓝 0) →
      (∀ ε ∈ Ioo 0 ε₀, ∀ x ∈ S.U, 0 ≤ gε ε x ∧ gε ε x ≤ M) →
      energyBound S Gg ≤ Ebd →
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
        -- (4.5) weak heat equation in the positivity set (needed by Theorem 3.10)
        WeakHeatInPos S.U u w ∧
        -- (iii) estimates
        DissipationIneq S.U S.Q u w χ (energyBound S Gg) ∧ InteriorLipEst S.U u C ∧
        WeightedPerimeterEst S.U χ Cper

/-! ### Proposition 5.3 and Corollary 5.4 (ε → 0 limit, viscosity form) -/

/-- The set `E = limsup* {uε_j > ε_j}` of Proposition 5.3 in arXiv v1, the sets taken in
`U × I`. -/
def semilinearLimitSet (U : Set (E d)) (I : Set ℝ) (εs : ℕ → ℝ) (us : ℕ → E d × ℝ → ℝ) :
    Set (E d × ℝ) :=
  upperKLimit (fun j ↦ {p ∈ U ×ˢ I | εs j < us j p}) atTop

/-- The set `E* = \overline{⋃_{0 < κ ≤ 1} limsup* {uε_j > κ ε_j}}`, which replaces the set `E` of
Proposition 5.3 in arXiv v1 (that `E` does not make the limit a relaxed subsolution; see
`SemilinearLimitRelaxedStatement`). This replacement is the authors' correction. It contains
`semilinearLimitSet` (`κ = 1`) and, unlike it, every point where the `uε_j` are not `o(ε_j)`. -/
def semilinearLimitSetStar (U : Set (E d)) (I : Set ℝ) (εs : ℕ → ℝ) (us : ℕ → E d × ℝ → ℝ) :
    Set (E d × ℝ) :=
  closure (⋃ κ ∈ Ioc (0 : ℝ) 1, upperKLimit (fun j ↦ {p ∈ U ×ˢ I | κ * εs j < us j p}) atTop)

/-- **Proposition 5.3**, **corrected**. If `u_j` (nonnegative) solve the semilinear equation
with `ε_j → 0` in `U × (0, T]` and `u_j → u` locally uniformly in `U × (0, T]`, then `(u, E*)` is
a relaxed viscosity solution of (3.1) in `U × (0, T]`, where
`E* = \overline{⋃_{0<κ≤1} limsup* {u_j > κ ε_j}}` (`semilinearLimitSetStar`).

Difference from arXiv v1: there the set is `E = limsup* {u_j > ε_j}` (`semilinearLimitSet`), and
with that set the statement is **false**: for `U = B₁`, `Q ≡ 1`, `u_j = ε_j (1 + h)` with `h ≥ 0`
the heat kernel from a point outside `Ū` switched on at time `t₀` (a solution since `β = 0` on
`[1, ∞)`), one gets `u ≡ 0` and `E = Ū × [t₀, T]`, and the strict supersolution
`φ = A(|x|² - ρ²) + B(t - t₀)` violates the relaxed subsolution property at `(0, t₀)`. The
authors' corrected set `E*` also contains the points where the `u_j` are not `o(ε_j)`. -/
def SemilinearLimitRelaxedStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (β : ℝ → ℝ), IsReactionProfile β →
    ∀ (T : ℝ) (εs : ℕ → ℝ) (us : ℕ → E d × ℝ → ℝ) (u : E d × ℝ → ℝ), 0 < T →
      (∀ j, 0 < εs j) → Tendsto εs atTop (𝓝 0) →
      (∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j)) →
      (∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p) →
      TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T) →
      IsParaRelaxedSolution S.U S.Q (Ioc 0 T) u (semilinearLimitSetStar S.U (Ioc 0 T) εs us)

/-- **Corollary 5.4**. If the `uε` are as in Proposition 3.8 with `g` a strict subsolution,
`uε ε_j → u` with `ε_j → 0`, and `E = E* = \overline{⋃_{0<κ≤1} limsup* {uε ε_j > κ ε_j}}`
(`semilinearLimitSetStar`), then `u` is monotone increasing in `t`, `E = \overline{{u > 0}}`
inside `U × [0, T]`, and `u` is a viscosity solution of (3.1) in `U × (0, T]`.

Differences from arXiv v1:
* arXiv v1 uses `E = limsup* {uε ε_j > ε_j}`; here we use the authors' corrected set `E*`,
  because with the set of arXiv v1 the relaxed subsolution property of Proposition 5.3 fails (see
  `SemilinearLimitRelaxedStatement`).
* arXiv v1 claims `E = \overline{{u > 0}}` everywhere, but never treats the points of `E` over
  `∂U`; we state the equality inside `U × [0, T]`, which is all that is used. -/
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

/-! ### Propositions 6.1, 6.2 and Lemma 6.3 -/

/-- **Proposition 6.1**. If `g` is a smooth strict subsolution with
`g > 0` on `∂U`, the smallest supersolution above `g` is both an inner variational and a
viscosity solution of (1.1) in `U`. We also export that it is continuous on `Ū`: the paper's
"sandwich" argument uses that the limit `û`, extended by `g₊`, lies in `𝒮_g`, which needs
continuity up to `∂U`, and Lemma 2.7 needs `u ∈ C(Ū)`; neither is stated in the paper. The proof
gets it from the modulus of Proposition 3.8(v), which is uniform in `ε`, `t` and the shifts
`g + a`. -/
def InnerSmallestStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (g : E d → ℝ), IsStrictSub S.U S.Q g →
    (∀ x ∈ frontier S.U, 0 < g x) →
    IsViscSolution S.U S.Q (perronSmallest S.U S.Q g) ∧
      (∃ χ : E d → ℝ, IsInnerVarSolution S.U S.Q (perronSmallest S.U S.Q g) χ) ∧
      ContinuousOn (perronSmallest S.U S.Q g) (closure S.U)

/-- **Proposition 6.2**. If `g` is a smooth strict supersolution, the largest subsolution below
`g` is both an inner variational and a viscosity solution of (1.1) in `U`. As in
Proposition 6.1, we also export that it is continuous on `Ū`. -/
def InnerLargestStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (g : E d → ℝ), IsStrictSuper S.U S.Q g →
    IsViscSolution S.U S.Q (perronLargest S.U S.Q g) ∧
      (∃ χ : E d → ℝ, IsInnerVarSolution S.U S.Q (perronLargest S.U S.Q g) χ) ∧
      ContinuousOn (perronLargest S.U S.Q g) (closure S.U)

/-- **Lemma 6.3**, with extra hypotheses: a local smallest supersolution (resp. largest
subsolution) `u` in the sense of Definition 2.6 which is moreover locally Lipschitz in `U` and
`C²` and harmonic in `{u > 0}` is a downward (resp. upward) minimizer of `J_Q(·; U)`
(Definition 2.11, in the form of `IsDownwardMinimizer`).

The paper states the lemma for local extremal solutions only, but its proof takes harmonicity in
`{u > 0}` from Propositions 6.1 and 6.2, which apply to Perron solutions, and it also needs
`u ∈ H¹_loc`. We therefore add these properties as hypotheses; Theorem 1.1(iii) supplies them
from Theorem 1.1(ii). -/
def DirectionalStatement : Prop :=
  ∀ (d : ℕ) (S : Setting d) (u : E d → ℝ),
    LocallyLipschitzOn S.U u → ContDiffOn ℝ 2 u (posSet u S.U) →
    (∀ x ∈ posSet u S.U, Δ u x = 0) →
    (IsLocalSmallestSuper S.U S.Q u → IsDownwardMinimizer S.U S.Q u) ∧
    (IsLocalLargestSub S.U S.Q u → IsUpwardMinimizer S.U S.Q u)

end PerronVariational

end
