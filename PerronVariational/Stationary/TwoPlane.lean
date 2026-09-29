/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.TwoPlane.Basic
public import PerronVariational.Stationary.TwoPlane.Step2
public import PerronVariational.Stationary.TwoPlane.OneDim
public import PerronVariational.Stationary.TwoPlane.Step3

/-!
# Proposition 2.14: one-sided minimality of two-plane solutions

**Proposition 2.14** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. Let `φ_α(x) = α |x · e|`
(`twoPlane α e`, `e` a unit vector) and `Q ≡ q > 0`. Then
1. `φ_α` is not an upward minimizer of `J_q` in `ℝᵈ` for any `α > 0`
   (`twoPlane_not_upwardMinimizer`);
2. `φ_α` is a downward minimizer of `J_q` in `ℝᵈ` iff `α ≥ q`
   (`twoPlane_downwardMinimizer_of_le`, `twoPlane_not_downwardMinimizer_of_lt`).

Minimality is in the sense of Definition 2.11 (`IsUpwardMinimizer`, `IsDownwardMinimizer`). The
paper's definition assumes `u ∈ H¹(U)` and compares `J_Q(·; U)`; here we assume `u ∈ H¹_loc(U)`
and compare the energies on the ball where the competitor differs, because on `U = ℝᵈ` the
two-plane functions are not in `H¹(ℝᵈ)` and every energy is infinite, so the literal definition
is vacuous there. The two versions agree when `J_Q(u; U) < ∞`.

## Proof notes

* (1) *Deviation of proof.* The paper uses harmonic replacement in `B₁`. We use instead the
  explicit first-variation competitor `v = φ_α + t η`, `η(x) = ((1 - |x|²)₊)²` (a `C¹` bump), on
  the ball `B₂(0)`. Since `∇φ_α = α sgn(x · e) e` and `∇η(x) = -4 (1 - |x|²)₊ x`, the cross term
  is the pointwise identity `⟨∇φ_α, ∇η⟩ = -4 α |x · e| (1 - |x|²)₊ ≤ 0` (no hyperplane integrals
  are needed), so `J(v) - J(φ_α) = 2t ∫⟨∇φ_α, ∇η⟩ + t² ∫|∇η|² < 0` for small `t > 0`. The
  positivity term is unchanged because `{φ_α > 0}` has full measure.
* (2), `α < q` (Step 2): the competitor `ψ = min(φ_α, A(|x·e| - εη)₊)`,
  `A = α/(1-ε)`, where `η` is a fixed smooth cut-off depending only on the variables orthogonal
  to `e` (`cylBump`). We take `L = 1` and `ε` small instead of `ε` fixed and `L` large; the
  `min` with `φ_α` makes `ψ = φ_α` outside `{|x·e| < η}` automatically, so no cylinder has to be
  cut out. The energy is compared column by column in coordinates adapted to `e`
  (`coordEquiv`, `lintegral_eq_lintegral_coord`): each column gains
  `2εη [α²/(1-ε) - q² + εα²|∇η|²/(1-ε)] < 0`.
* (2), `α ≥ q` (Step 3): the one-dimensional statement `oneDim_downward` (for
  absolutely continuous competitors, via `oneDim_core` and `ratio_ineq`) is integrated over the
  slices of the ball (`energyJ_ge_of_downward`). The reduction to slices uses the ACL property of
  Sobolev functions along `e` (`ae_slice_hasPrimitive`), which the paper uses implicitly;
  it is proved here from the weak-gradient identity tested against
  `χ(x · e) θ(x')`, Fubini, and a one-dimensional lemma (`exists_primitive_of_weakDeriv`:
  mollify, compare derivatives on a dense set, pass to the limit a.e.).

## File layout

* `PerronVariational.Stationary.TwoPlane.Basic`: one-dimensional calculus (Steps 1 and 3), the
  two-plane function `twoPlane` and its regularity.
* `PerronVariational.Stationary.TwoPlane.Step2`: the first-variation competitor for
  Proposition 2.14 (1), coordinates adapted to `e`, the cut-off `cylBump` and Step 2.
* `PerronVariational.Stationary.TwoPlane.OneDim`: the one-dimensional downward minimality
  (`oneDim_core`, `oneDim_downward`) and weak derivatives on the line
  (`exists_primitive_of_weakDeriv`).
* `PerronVariational.Stationary.TwoPlane.Step3`: slices and marginals, the ACL property along `e`,
  Step 3 and Proposition 2.14.
-/

@[expose] public section

end
