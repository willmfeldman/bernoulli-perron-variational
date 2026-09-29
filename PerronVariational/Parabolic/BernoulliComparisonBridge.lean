/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Parabolic
public import BernoulliComparison.Interface.Parabolic
public import BernoulliComparison.Corollary.StrictComparison

/-!
# Bridge to bernoulli-parabolic-comparison

The strict comparison principle for the parabolic Bernoulli problem, Theorem 3.6 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
the Bernoulli one-phase problem*, arXiv:2609.14981, is a result from the literature (I. C. Kim,
*A free boundary problem arising in flame propagation*, J. Differential Equations 191 (2003),
470–489, doi:10.1016/S0022-0396(02)00195-X, Theorem 2.2). It is proved in the dependency
bernoulli-parabolic-comparison v0.1.0 (`BernoulliComparison.para_strict_comparison`). That
library's parabolic solution notions were adapted verbatim from Definitions 3.1, 3.2 and 3.4 of
the paper as encoded here, and they agree with ours by `rfl`. The lemmas below check that the two
libraries' definitions still match.
-/
open Set

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Definitional agreement -/

theorem parBdry_eq_bpc (V : Set (E d)) (a b : ℝ) :
    parBdry V a b = BernoulliComparison.parBdry V a b :=
  rfl

theorem posSetP_eq_bpc (u : E d × ℝ → ℝ) (Ω : Set (E d × ℝ)) :
    posSetP u Ω = BernoulliComparison.posSetP u Ω :=
  rfl

theorem prec_iff_bpc {u v : E d × ℝ → ℝ} {Ω F : Set (E d × ℝ)} :
    Prec u v Ω F ↔ BernoulliComparison.Prec u v Ω F :=
  Iff.rfl

theorem isClassicalStrictParaSub_iff_bpc {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} :
    IsClassicalStrictParaSub Q φ V a b ↔ BernoulliComparison.IsClassicalStrictParaSub Q φ V a b :=
  Iff.rfl

theorem isClassicalStrictParaSuper_iff_bpc {Q : E d → ℝ} {φ : E d × ℝ → ℝ} {V : Set (E d)}
    {a b : ℝ} :
    IsClassicalStrictParaSuper Q φ V a b ↔
      BernoulliComparison.IsClassicalStrictParaSuper Q φ V a b :=
  Iff.rfl

theorem isParaSuper_iff_bpc {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ} :
    IsParaSuper U Q I u ↔ BernoulliComparison.IsParaSuper U Q I u :=
  Iff.rfl

theorem isParaSub_iff_bpc {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ} {u : E d × ℝ → ℝ} :
    IsParaSub U Q I u ↔ BernoulliComparison.IsParaSub U Q I u :=
  Iff.rfl

theorem isParaRelaxedSub_iff_bpc {U : Set (E d)} {Q : E d → ℝ} {I : Set ℝ}
    {u : E d × ℝ → ℝ} {Eset : Set (E d × ℝ)} :
    IsParaRelaxedSub U Q I u Eset ↔ BernoulliComparison.IsParaRelaxedSub U Q I u Eset :=
  Iff.rfl

end PerronVariational

end
