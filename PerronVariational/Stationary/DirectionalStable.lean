/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Stationary.DirectionalStable.Basic
public import PerronVariational.Stationary.DirectionalStable.DownStep
public import PerronVariational.Stationary.DirectionalStable.Lemma211
public import PerronVariational.Stationary.DirectionalStable.Blowup

/-!
# Stability of directional minimality (Lemma 2.12, Corollary 2.13)

**Lemma 2.12** and **Corollary 2.13** of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

## Proof route

We use the paper's competitor `v_n = φ min{v, u_n} + (1 - φ) u_n` (downward case, resp.
`φ max{v, u_n} + (1 - φ) u_n` upward), written as `v_n = u_n - φ (u_n - v)₊`
(resp. `u_n + φ (v - u_n)₊`), the cutoff energy estimate on the annulus `B_R \ B_s` and the
Poincaré inequality with zero outer trace on annuli (from gmt-foundations v0.1.0). The only
change is the accounting in the ball `B_s`: the paper asserts `min{v, u_n} → v` in `H¹(B)` (proof
of Lemma 2.12, Step 1), which needs *strong* `H¹` convergence of `u_n`. Instead we use the lattice
identity
`J(min{v, u_n}; B_s) + J(max{v, u_n}; B_s) = J(v; B_s) + J(u_n; B_s)`
and the lower semicontinuity of `J` along `max{v, u_n} → max{v, u} = u` (downward case), resp.
`min{v, u_n} → u` (upward case). This only needs *weak* convergence of the gradients (weak `L²`
compactness and lower semicontinuity of the norm, from gmt-foundations v0.1.0) and Fatou's lemma
for the indicator term. In particular the upward case does not need the input from
D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), 545–591,
arXiv:2306.10131 (the dichotomy of their Theorem 1.2(i) and the compactness Lemma 2.10) used in
the paper's Step 2. The paper's proof treats only `Q_n = Q` ("the generalization to a uniformly
convergent sequence of `Q_n` is not difficult"), while Corollary 2.13 needs
`Q_n = Q(x₀ + r_n ·)`; here varying `Q_n` are handled directly.

## Main results

* `DirectionalStable.isDownwardMinimizer_of_tendsto`,
  `DirectionalStable.isUpwardMinimizer_of_tendsto` (Lemma 2.12(i), (ii); the upward case
  also without the inner-variational hypothesis, `isUpwardMinimizer_of_tendsto'`).
* `DirectionalStable.blowup_isDownwardMinimizer`, `DirectionalStable.blowup_isUpwardMinimizer`
  (Corollary 2.13(i), (ii); again `blowup_isUpwardMinimizer'` without the inner-variational
  hypothesis).
* Intermediate: `energyJ_le_of_down`, `energyJ_le_of_up` (the estimate on one ball, for functions
  `uₙ` on varying domains `Uₙ`), `energyJ_le_liminf` (lower semicontinuity of `J`, weak
  compactness and Fatou), `energyJ_add_le_of_swap` (lattice identity), `harmonic_of_tendsto`
  (harmonicity of the limit, Weyl's lemma), `isDownwardMinimizer_of_exhaust` (Lemma 2.12 on
  domains exhausting `ℝᵈ`), `blowup_isDownwardMinimizer_scaled` (scaling invariance of
  Definition 2.11).

Results from the literature used here: weak `L²` compactness and lower semicontinuity, locally
Lipschitz functions are `H¹_loc`, and the Poincaré inequality on annuli (all from gmt-foundations
v0.1.0); Weyl's lemma (from viscosity-solution-theory v0.2.0, see
`Analysis/WeylWeakGradient.lean`). The precompactness claim of Corollary 2.13 (Arzelà–Ascoli)
is not formalized here; `IsBlowupLimit` assumes the convergence.

## File layout

* `PerronVariational.Stationary.DirectionalStable.Basic`: Sobolev helpers, lower semicontinuity of
  `J`, the lattice identity, annuli, the approximating data and the competitors.
* `PerronVariational.Stationary.DirectionalStable.DownStep`: the estimate on one ball for a fixed
  inner radius `s` (`down_step`, `up_step`).
* `PerronVariational.Stationary.DirectionalStable.Lemma211`: the limit `s → R`, Lemma 2.12 and its
  version on exhausting domains.
* `PerronVariational.Stationary.DirectionalStable.Blowup`: scaling invariance of Definition 2.11
  and Corollary 2.13 (blow-ups).
-/

@[expose] public section

end
