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

`main_smallest : MainSmallestStatement` and `main_largest : MainLargestStatement`
(**[Theorem 1.1](#AFS:t.main)** of the paper), obtained by plugging every intermediate theorem into
the conditional assemblies `main_smallest_of`, `main_largest_of`, `inner_smallest_of`,
`inner_largest_of` and `parabolic_existence_bdd_of`. Along the way,
`inner_smallest : InnerSmallestStatement` and `inner_largest : InnerLargestStatement`
(**Propositions [6.1](#AFS:p.inner-smallest), [6.2](#AFS:p.inner-largest)**) are stated on their
own, since they also give continuity on `Ū`, which [Theorem 1.1](#AFS:t.main) does not state.

Data classes. `main_smallest` and `main_largest` take `g` in the general classes `IsStrictSub` /
`IsStrictSuper` (`Δg ≥ 0`, resp. `Δg ≤ 0`), which contain the paper's class of
[Definition 2.3](#AFS:d.strict-sub) (`Δg ≥ δ₀`, resp. `Δg ≤ -δ₀`, with `a₀, δ₀ ≤ 1/2`); they are a
documented strengthening of the paper's [Theorem 1.1](#AFS:t.main), and the general class is kept on
purpose. `main_smallest_unif : MainSmallestUnifStatement`,
`main_largest_unif : MainLargestUnifStatement` are the paper-literal versions (data as in
[Definition 2.3](#AFS:d.strict-sub), `IsUnifStrictSub` / `IsUnifStrictSuper`), assembled the same
way but with the paper's proof of [Lemma 2.8](#AFS:l.local-minimality).

All of these theorems are fully proved. The results the paper cites from the literature enter
through the `Registry` modules, where each one is proved, either in this library or in one of its
dependencies. The continuity of the Perron solutions on `Ū`, needed by
[Lemma 2.8](#AFS:l.local-minimality) and its dual, is a conclusion of
[Propositions 6.1](#AFS:p.inner-smallest)/6.2.
-/

@[expose] public section

namespace PerronVariational

/-- **Parabolic existence ([Theorem 3.13](#AFS:t.parabolic-existence))** with the `L^∞` bound,
unconditional. -/
theorem parabolic_existence_bdd : ParabolicExistenceBddStatement :=
  parabolic_existence_bdd_of semilinear_wellposed Inner.eps_inner_limit
    semilinear_limit_relaxedSolution semilinear_limit_viscSolution_increasing

/-- **[Proposition 6.1](#AFS:p.inner-smallest)**, unconditional: Perron's smallest supersolution
above a smooth strict subsolution `g` with `g > 0` on `∂U` is a viscosity and an inner variational
solution of [(1.1)](#AFS:e.bernoulli-basic) in `U`, and it is continuous on `Ū`. -/
theorem inner_smallest : InnerSmallestStatement :=
  inner_smallest_of parabolic_existence_bdd longtime_innerVar

/-- **[Proposition 6.2](#AFS:p.inner-largest)**, unconditional: Perron's largest subsolution below a
smooth strict supersolution `g` is a viscosity and an inner variational solution of
[(1.1)](#AFS:e.bernoulli-basic) in `U`, and it is continuous on `Ū`. -/
theorem inner_largest : InnerLargestStatement :=
  inner_largest_of parabolic_existence_bdd longtime_innerVar

/-- **[Theorem 1.1](#AFS:t.main)**, smallest supersolution case, for the general data class
`IsStrictSub` (a strengthening of the paper's statement; see the module docstring). -/
theorem main_smallest : MainSmallestStatement :=
  main_smallest_of inner_smallest directional

/-- **[Theorem 1.1](#AFS:t.main)**, largest subsolution case, for the general data class
`IsStrictSuper` (a strengthening of the paper's statement; see the module docstring). -/
theorem main_largest : MainLargestStatement :=
  main_largest_of inner_largest directional

/-- **[Theorem 1.1](#AFS:t.main)**, smallest supersolution case, paper-literal: `g` a smooth strict
subsolution as in [Definition 2.3](#AFS:d.strict-sub); part (iii) through the paper's proof
of [Lemma 2.8](#AFS:l.local-minimality). -/
theorem main_smallest_unif : MainSmallestUnifStatement :=
  main_smallest_unif_of inner_smallest directional

/-- **[Theorem 1.1](#AFS:t.main)**, largest subsolution case, paper-literal: `g` a smooth strict
supersolution as in [Definition 2.3](#AFS:d.strict-sub); part (iii) through the paper's proof
of [Lemma 2.8](#AFS:l.local-minimality). -/
theorem main_largest_unif : MainLargestUnifStatement :=
  main_largest_unif_of inner_largest directional

end PerronVariational

end
