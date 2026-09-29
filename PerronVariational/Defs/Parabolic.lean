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

The parabolic solution notions of §3 of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981
("the paper").

Space-time points are `p : E d × ℝ`. A general time set `I : Set ℝ` is used (the paper uses
`(0, T]` and `(0, ∞)`); `U ×ˢ I` is the space-time domain.

* Parabolic cylinders, parabolic boundaries, admissible cylinders `V × (a, b] ⊂⊂ U × I`.
* The ordering `≺` (Definition 3.1) and classical strict sub/supersolutions (before
  Definition 3.2).
* Parabolic viscosity super/sub/solutions (Definition 3.2).
* Parabolic relaxed subsolutions/solutions (Definition 3.4).
* Time monotonicity (after Definition 3.4).
* Parabolic inner variational solutions (Definition 3.7).
* The estimates (3.11)–(3.13) of Theorem 3.9 as named predicates.

Test functions are globally smooth on space-time; the paper uses `φ ∈ C^∞(V̄ × [a, b])`. The two
are equivalent by a cutoff argument, since all conditions are local.

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

/-- `U_∞ = U × (0, ∞)` (paper, §1.2). -/
def UInf (U : Set (E d)) : Set (E d × ℝ) := U ×ˢ Ioi 0

/-- The parabolic boundary `∂_P U_∞ = (Ū × {0}) ∪ (∂U × [0, ∞))`. -/
def parBdryInf (U : Set (E d)) : Set (E d × ℝ) :=
  (closure U ×ˢ {0}) ∪ (frontier U ×ˢ Ici 0)

/-- The parabolic cylinder `Q_r(x, t) = B_r(x) × (t - r², t]` (paper, §1.2). -/
def parCyl (x : E d) (t r : ℝ) : Set (E d × ℝ) := ball x r ×ˢ Ioc (t - r ^ 2) t

/-- `V × (a, b] ⊂⊂ U × I` is an admissible test cylinder (Definition 3.2): `V` is open and
bounded, `a < b`, and `closure (V × (a, b]) = V̄ × [a, b] ⊆ U × I`. -/
def AdmissibleCyl (U : Set (E d)) (I : Set ℝ) (V : Set (E d)) (a b : ℝ) : Prop :=
  IsOpen V ∧ Bornology.IsBounded V ∧ a < b ∧ closure V ×ˢ Icc a b ⊆ U ×ˢ I

/-! ### Positivity sets and the ordering `≺` -/

/-- The space-time positivity set `{u > 0}` inside the domain `Ω`. -/
def posSetP (u : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) : Set (E d × ℝ) := {p ∈ Ω | 0 < u p}

/-- The paper's `u ≺ v on F` (Definition 3.1): `u ≺_E v on F` with `E = \overline{{u > 0}}`, where
`{u > 0}` is taken inside the domain `Ω` of `u`. -/
def Prec (u v : E d × ℝ → ℝ) (Ω F : Set (E d × ℝ)) : Prop :=
  PrecOn u v (closure (posSetP u Ω)) F

/-! ### Classical strict sub/supersolutions -/

/-- Classical strict subsolution of (3.1) on `V̄ × [a, b]` (paper, before Definition 3.2), with
`φ` globally smooth (the paper: `φ ∈ C^∞(V̄ × [a, b])`, equivalent by cutoff); `{φ > 0}`, its
closure and boundary are taken in all of space-time, which realizes the paper's convention of an
open neighbourhood of `V̄ × [a, b]`:
`∂ₜφ - Δφ < 0` on `\overline{{φ > 0}} ∩ (V̄ × [a, b])` and `|∇φ| > Q` on
`∂{φ > 0} ∩ (V̄ × [a, b])`. -/
def IsClassicalStrictParaSub (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ContDiff ℝ ∞ φ ∧
    (∀ p ∈ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), dₜ φ p - lapₓ φ p < 0) ∧
    ∀ p ∈ frontier {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), Q p.1 < ‖gradₓ φ p‖

/-- Classical strict supersolution of (3.1) on `V̄ × [a, b]` (paper, before Definition 3.2), with
`φ` globally smooth: `∂ₜφ - Δφ > 0` on `\overline{{φ > 0}} ∩ (V̄ × [a, b])` and `|∇φ| < Q` on
`∂{φ > 0} ∩ (V̄ × [a, b])`. The paper says "with the analogous relations for a classical strict
subsolution"; the second "subsolution" should read "supersolution", and these are the analogous
relations. -/
def IsClassicalStrictParaSuper (Q : E d → ℝ) (φ : E d × ℝ → ℝ) (V : Set (E d)) (a b : ℝ) :
    Prop :=
  ContDiff ℝ ∞ φ ∧
    (∀ p ∈ closure {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), 0 < dₜ φ p - lapₓ φ p) ∧
    ∀ p ∈ frontier {q | 0 < φ q} ∩ (closure V ×ˢ Icc a b), ‖gradₓ φ p‖ < Q p.1

/-! ### Parabolic viscosity solutions (Definition 3.2) -/

/-- **Definition 3.2**, supersolution case, with globally smooth test functions.
`u ∈ C(U × I; [0, ∞))` is a supersolution of (3.1): for every admissible cylinder
`V × (a, b] ⊂⊂ U × I` and every classical strict subsolution `φ` on `V̄ × [a, b]` with `φ ≺ u` on
`∂_P(V × (a, b])`, also `φ ≺ u` in `V × (a, b]`.
(`φ ≺ u` uses `\overline{{φ > 0}}`, computed in all of space-time.) -/
def IsParaSuper (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSub Q φ V a b → Prec φ u univ (parBdry V a b) →
        Prec φ u univ (cyl V a b)

/-- **Definition 3.2**, subsolution case, with globally smooth test functions.
`u ∈ C(U × I; [0, ∞))` is a subsolution of (3.1): for every admissible cylinder
`V × (a, b] ⊂⊂ U × I` and every classical strict supersolution `φ` on `V̄ × [a, b]` with `u ≺ φ` on
`∂_P(V × (a, b])`, also `u ≺ φ` in `V × (a, b]`.
(`u ≺ φ` uses `\overline{{u > 0}}`, `{u > 0} ⊆ U × I`.) -/
def IsParaSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSuper Q φ V a b → Prec u φ (U ×ˢ I) (parBdry V a b) →
        Prec u φ (U ×ˢ I) (cyl V a b)

/-- **Definition 3.2**. Parabolic viscosity solution: both a super- and a subsolution. -/
def IsParaSolution (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ) : Prop :=
  IsParaSuper U Q I u ∧ IsParaSub U Q I u

/-! ### Parabolic relaxed subsolutions (Definition 3.4) -/

/-- **Definition 3.4**, with globally smooth test functions. For `u ∈ C(U × I; [0, ∞))` and
`E` closed in `Ū × Ī` with `{u > 0} ⊆ E`, `(u, E)` is a relaxed subsolution: for every admissible
cylinder `V × (a, b] ⊂⊂ U × I` and classical strict supersolution `φ` on `V̄ × [a, b]` with
`u ≺_E φ` on `∂_P(V × (a, b])`, also `u ≺_E φ` in `V × (a, b]`. -/
def IsParaRelaxedSub (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) : Prop :=
  ContinuousOn u (U ×ˢ I) ∧ (∀ p ∈ U ×ˢ I, 0 ≤ u p) ∧ IsClosed Eset ∧
    Eset ⊆ closure U ×ˢ closure I ∧ posSetP u (U ×ˢ I) ⊆ Eset ∧
    ∀ (V : Set (E d)) (a b : ℝ) (φ : E d × ℝ → ℝ), AdmissibleCyl U I V a b →
      IsClassicalStrictParaSuper Q φ V a b → PrecOn u φ Eset (parBdry V a b) →
        PrecOn u φ Eset (cyl V a b)

/-- **Definition 3.4**. `(u, E)` is a relaxed viscosity solution: `u` is a (standard)
supersolution and `(u, E)` is a relaxed subsolution. -/
def IsParaRelaxedSolution (U : Set (E d)) (Q : E d → ℝ) (I : Set ℝ) (u : E d × ℝ → ℝ)
    (Eset : Set (E d × ℝ)) : Prop :=
  IsParaSuper U Q I u ∧ IsParaRelaxedSub U Q I u Eset

/-! ### Time monotonicity -/

/-- The time slice `E_t = {x : (x, t) ∈ E}` (paper, after Definition 3.4). -/
def timeSlice (Eset : Set (E d × ℝ)) (t : ℝ) : Set (E d) := {x | (x, t) ∈ Eset}

/-- `t ↦ u(x, t)` is nondecreasing on `I` for every `x ∈ A`. -/
def MonotoneInTime (u : E d × ℝ → ℝ) (A : Set (E d)) (I : Set ℝ) : Prop :=
  ∀ x ∈ A, MonotoneOn (fun t ↦ u (x, t)) I

/-- `t ↦ u(x, t)` is nonincreasing on `I` for every `x ∈ A`. -/
def AntitoneInTime (u : E d × ℝ → ℝ) (A : Set (E d)) (I : Set ℝ) : Prop :=
  ∀ x ∈ A, AntitoneOn (fun t ↦ u (x, t)) I

/-- The time slices `E_t` are nondecreasing in `t ∈ I` (paper, after Definition 3.4). -/
def SlicesMonotone (Eset : Set (E d × ℝ)) (I : Set ℝ) : Prop :=
  ∀ s ∈ I, ∀ t ∈ I, s ≤ t → timeSlice Eset s ⊆ timeSlice Eset t

/-! ### Parabolic inner variational solutions (Definition 3.7) -/

/-- `w` is the weak time derivative of `u` in the open set `Ω`: `u, w` are locally
integrable on `Ω` and `∫_Ω u ∂ₜψ = -∫_Ω w ψ` for every `ψ ∈ C_c^∞(Ω)`.
Definition 3.7 asks `∂ₜu ∈ L²`; here the time derivative is carried as explicit data `w`
together with this weak-derivative predicate. -/
def HasWeakTimeDeriv (Ω : Set (E d × ℝ)) (u w : E d × ℝ → ℝ) : Prop :=
  LocallyIntegrableOn u Ω ∧ LocallyIntegrableOn w Ω ∧
    ∀ ψ : E d × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∫ p in Ω, u p * dₜ ψ p = -∫ p in Ω, w p * ψ p

/-- The integrand of the parabolic inner variation identity (3.3):
`(|∇u|² + Q²χ) div ξ - 2 ∇u · Dξ ∇u + ∇(Q²) · ξ χ - 2 (ξ · ∇u) ∂ₜu`, with spatial
derivatives, pointwise spatial gradient of `u`, and `∂ₜu` supplied as data `w`. -/
noncomputable def paraInnerVarIntegrand (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ)
    (ξ : E d × ℝ → E d) (p : E d × ℝ) : ℝ :=
  (‖gradₓ u p‖ ^ 2 + Q p.1 ^ 2 * χ p) * divₓ ξ p
    - 2 * inner ℝ (gradₓ u p) (fderivₓ ξ p (gradₓ u p))
    + fderiv ℝ (fun y ↦ Q y ^ 2) p.1 (ξ p) * χ p
    - 2 * inner ℝ (ξ p) (gradₓ u p) * w p

/-- **Definition 3.7**. `(u, χ)` (with `∂ₜu = w`) is an inner
variational solution of (3.1) in `U_∞ = U × (0, ∞)`:
(i) `u ∈ C(U_∞)`, `u ≥ 0`, `∇u ∈ L^∞_loc(U_∞)`, `∂ₜu = w ∈ L²(U_∞)`;
(ii) `χ` Borel measurable with values in `{0, 1}` on `U_∞`;
(iii) `1_{u > 0} ≤ χ` a.e. in `U_∞`;
(iv) (3.3) holds for every `ξ ∈ C¹_c(U_∞; ℝᵈ)`.

The paper assumes `∇u ∈ L^∞_loc(U_∞)`; here we assume local spatial Lipschitz bounds, uniform in
time on a neighbourhood of each point, because this is the pointwise form of the same condition
for continuous `u`. The time derivative is explicit data `w` with a weak-derivative predicate.
In (iv) we additionally record integrability of the pointwise integrand, which holds for the
paper's (a.e.-defined) integrand under (i)–(iii); this rules out junk values of the Bochner
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

/-- The weak heat equation in the positivity set, (4.5): for every Lipschitz `φ` with compact
support in `{u > 0} ∩ U_∞`, `∫_{U_∞} ∂ₜu φ = -∫_{U_∞} ∇u · ∇φ` (with `∂ₜu = w`).

This is **not part of Definition 3.7** in the paper. The proof of Theorem 3.10 (Step 2) uses it,
and the paper proves it only for the `ε → 0` limit (§4.2). Here it is a hypothesis of
Theorem 3.10 and Lemma 5.8 and a conclusion of Proposition 4.1 and Theorem 3.9, because without it
Theorem 3.10 is false: in the unit ball of `ℝ²`, `u = 1 + |x₁|`, `w = 0`, `χ ≡ 1` is a bounded,
time-independent parabolic inner variational solution satisfying (3.11)–(3.13), but its limit is
not harmonic in `{u > 0}`. -/
def WeakHeatInPos (U : Set (E d)) (u w : E d × ℝ → ℝ) : Prop :=
  ∀ φ : E d × ℝ → ℝ, (∃ K, LipschitzWith K φ) → HasCompactSupport φ →
    tsupport φ ⊆ posSetP u (UInf U) →
    ∫ p in UInf U, w p * φ p = -∫ p in UInf U, inner ℝ (gradₓ u p) (gradₓ φ p)

/-! ### The estimates (3.11)–(3.13) of Theorem 3.9 -/

/-- The dissipation inequality (3.11): for a.e. `T > 0`,
`½ J(u(T), χ(T); U) + ∫₀ᵀ ∫_U (∂ₜu)² ≤ ½ E0`.

The paper's right-hand side is `½ J(u(0), χ(0); U)`; here it is an explicit energy bound `E0`,
because Definition 3.7 defines `χ` only on `U_∞`, so `χ(0)` has no meaning. The statements take
`E0 = ∫_U |∇g|² + Q_max² |U|`; the paper's inequality implies this bound for any `χ(0) ≤ 1`, and it
suffices for Theorem 3.10. -/
def DissipationIneq (U : Set (E d)) (Q : E d → ℝ) (u w χ : E d × ℝ → ℝ) (E0 : ℝ≥0∞) : Prop :=
  ∀ᵐ T ∂(volume.restrict (Ioi (0 : ℝ))),
    energyJχ U Q (fun x ↦ gradₓ u (x, T)) (fun x ↦ χ (x, T)) / 2 +
        ∫⁻ p in U ×ˢ Ioc 0 T, ENNReal.ofReal (w p ^ 2) ≤ E0 / 2

/-- The interior Lipschitz bound (3.12) with constant `C`: for every
`Q_{2r}(x, t) ⊆ U_∞` with `0 < r ≤ 1`,
`‖∇u‖_{L^∞(Q_r(x,t))} ≤ C (r⁻¹ ‖u‖_{L^∞(Q_{2r}(x,t))} + 1)`, stated pointwise for the spatial
gradient with `‖u‖_{L^∞(Q_{2r})}` replaced by any bound `M` (equivalent for continuous `u`). -/
def InteriorLipEst (U : Set (E d)) (u : E d × ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ (x : E d) (t r : ℝ), 0 < r → r ≤ 1 → parCyl x t (2 * r) ⊆ UInf U →
    ∀ M : ℝ, (∀ q ∈ parCyl x t (2 * r), |u q| ≤ M) →
      ∀ p ∈ parCyl x t r, ‖gradₓ u p‖ ≤ C * (M / r + 1)

/-- Admissible weights for (3.13): `η ∈ C¹_c(U_∞; [0, ∞))`. -/
def IsPerimeterWeight (U : Set (E d)) (η : E d × ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 η ∧ HasCompactSupport η ∧ tsupport η ⊆ UInf U ∧ ∀ p, 0 ≤ η p

/-- The norm `‖η‖_{L²((0,∞); H¹(U))} = (∫_{U_∞} η² + |∇ₓη|²)^{1/2}`. -/
noncomputable def l2H1Norm (U : Set (E d)) (η : E d × ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ p in UInf U, η p ^ 2 + ‖gradₓ η p‖ ^ 2)

/-- `d_η = dist(spt η, ∂_P U_∞)` (paper, after (3.13)). -/
noncomputable def weightDist (U : Set (E d)) (η : E d × ℝ → ℝ) : ℝ :=
  sInf ((fun p ↦ infDist p (parBdryInf U)) '' tsupport η)

/-- `T_η = sup {t : (x, t) ∈ spt η}` (paper, after (3.13)). -/
noncomputable def weightTime (η : E d × ℝ → ℝ) : ℝ :=
  sSup (Prod.snd '' tsupport η)

/-- The time-length `ℓ_η = T_η - inf {t : (x, t) ∈ spt η}` of the support of `η`. -/
noncomputable def weightTimeLength (η : E d × ℝ → ℝ) : ℝ :=
  sSup (Prod.snd '' tsupport η) - sInf (Prod.snd '' tsupport η)

/-- The weighted perimeter bound (3.13), in the form **proved** by the paper: for every
`η ∈ C¹_c(U_∞; [0, ∞))`, `∫_{U_∞} η |∇χ| ≤ C_η ‖η‖_{L²((0,∞); H¹(U))}`, where
`C_η = C d_η ℓ_η` depends on `η` only through `d_η = dist(spt η, ∂_P U_∞)` and the time-length
`ℓ_η` of `spt η`.

The paper's statement lets `C_η` depend on `T_η = sup {t : (x,t) ∈ spt η}`; here it depends on
`ℓ_η` instead, because the literal form does not support Step 3 of the proof of Theorem 3.10
(which needs a constant independent of `t` for weights supported in `U_k × (i, i + 1)`), while the
proof of (3.13) (via (4.7)) gives the `ℓ_η` form. -/
def WeightedPerimeterEst (U : Set (E d)) (χ : E d × ℝ → ℝ) (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ η : E d × ℝ → ℝ, IsPerimeterWeight U η →
    weightedTVₓ (UInf U) η χ ≤
      ENNReal.ofReal (C (weightDist U η) (weightTimeLength η) * l2H1Norm U η)

end PerronVariational

end
