/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Parabolic.Existence
public import PerronVariational.Statements.Main
import PerronVariational.Inner.EpsLimit
import PerronVariational.Inner.LongTime
import PerronVariational.Main.Directional
import PerronVariational.Main.InnerLargest
import PerronVariational.Main.InnerSmallest
import PerronVariational.Main.Theorem
import PerronVariational.Semilinear.ViscosityLimit
import PerronVariational.Semilinear.ViscosityLimitSub
import PerronVariational.Semilinear.WellPosed

/-!
# Main theorem: unconditional assembly

Reference: F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

`main_smallest : MainSmallestStatement` and `main_largest : MainLargestStatement` (**Theorem 1.1**
of the paper), obtained by plugging every intermediate theorem into the conditional assemblies
`main_smallest_of`, `main_largest_of`, `inner_smallest_of`, `inner_largest_of` and
`parabolic_existence_bdd_of`. Along the way, `inner_smallest : InnerSmallestStatement` and
`inner_largest : InnerLargestStatement` (**Propositions 6.1, 6.2**) are stated on their own, since
they also give continuity on `Ū`, which Theorem 1.1 does not state.

Both theorems are fully proved. The results the paper cites from the literature enter through the
`Registry` modules, where each one is proved, either in this library or in one of its
dependencies. The continuity of the Perron solutions on `Ū`, needed by Lemma 2.7 and its dual, is
a conclusion of Propositions 6.1/6.2 (the paper uses it without stating it).
-/

@[expose] public section

namespace PerronVariational

/-- **Parabolic existence (Theorem 3.9)** with the `L^∞` bound, unconditional. -/
theorem parabolic_existence_bdd : ParabolicExistenceBddStatement :=
  parabolic_existence_bdd_of semilinear_wellposed Inner.eps_inner_limit
    semilinear_limit_relaxedSolution semilinear_limit_viscSolution_increasing

/-- **Proposition 6.1**, unconditional: Perron's smallest supersolution above a smooth strict
subsolution `g` with `g > 0` on `∂U` is a viscosity and an inner variational solution of (1.1) in
`U`, and it is continuous on `Ū`. -/
theorem inner_smallest : InnerSmallestStatement :=
  inner_smallest_of parabolic_existence_bdd longtime_innerVar

/-- **Proposition 6.2**, unconditional: Perron's largest subsolution below a smooth strict
supersolution `g` is a viscosity and an inner variational solution of (1.1) in `U`, and it is
continuous on `Ū`. -/
theorem inner_largest : InnerLargestStatement :=
  inner_largest_of parabolic_existence_bdd longtime_innerVar

/-- **Theorem 1.1**, smallest supersolution case. -/
theorem main_smallest : MainSmallestStatement :=
  main_smallest_of inner_smallest directional

/-- **Theorem 1.1**, largest subsolution case. -/
theorem main_largest : MainLargestStatement :=
  main_largest_of inner_largest directional

end PerronVariational

end
