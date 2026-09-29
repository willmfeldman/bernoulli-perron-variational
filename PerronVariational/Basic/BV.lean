/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Sobolev
public import GMTFoundations.Defs.BV

/-!
# Weighted total variation

The (weighted) perimeter `∫_Ω η |∇χ|` of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, is
defined here by duality: `sup {∫_Ω χ div ψ : ψ ∈ C¹_c(Ω; ℝᵈ), |ψ| ≤ η}`. The paper writes
`∫ η |∇χ|` for the total variation measure of `χ ∈ BV`; the duality formula is the standard
equivalent definition and needs no measure-valued gradient.

* `weightedTV Ω η χ` on `ℝᵈ` (used for (3.15) and, with `η = 1`, the hypotheses of Lemma 2.10).
* `weightedTVₓ Ω η χ` on space-time `ℝᵈ × ℝ` with the *spatial* divergence (used for (3.13); the
  gradient `∇χ` there is spatial, cf. (4.7)).
* `totalVariationOn V χ = weightedTV V 1 χ`.

Since `ψ ↦ -ψ` preserves the class of test fields, the supremum of `∫ χ div ψ` equals the
supremum of `|∫ χ div ψ|`. For bounded measurable `χ` (the only case used) the integrals are
genuine Lebesgue integrals.

The definitions are in gmt-foundations v0.1.0 (`GMTFoundations.Defs.BV`) and are re-exported
here.
-/
open Set Filter Topology MeasureTheory
open scoped ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

export GMTFoundations (IsTVTestField weightedTV totalVariationOn IsTVTestFieldₓ weightedTVₓ)

end PerronVariational

end
