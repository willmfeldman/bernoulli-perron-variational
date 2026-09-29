/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.WeissTime.EnergyMoment
public import PerronVariational.Inner.WeissTime.Translation
public import PerronVariational.Inner.WeissTime.ChiEps

/-!
# Time regularity of the energy density (proof of Lemma 4.3)

From the proof of Lemma 4.3 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981. For a classical
solution `v` of (3.4) and `ψ ∈ C¹_c(U)`, the spatial moment
`a(t) = ∫ (|∇v|² + Q² χ_ε(v))(x, t) ψ(x) dx` of the energy density satisfies
`a'(t) = -2 ∫ ψ (∂ₜv)² - 2 ∫ ∂ₜv ∇v · ∇ψ` (the computation leading to (4.8), which the paper
localizes from Weiss's argument in G. S. Weiss, *A singular limit arising in combustion theory: fine
properties of the free boundary*, Calc. Var. Partial Differential Equations 17 (2003), 311–340,
doi:10.1007/s00526-002-0171-z, Proposition 4.1). The paper's computation differentiates `|∇v|²` in
time, which needs the mixed derivative `∂ₜ∇v`. The paper assumes the semilinear solutions are `C^∞`;
here they are only `C^{2,1}` (`C¹` jointly, `C²` in `x`), because `Q` is only Lipschitz. So we
integrate by parts first (`integral_norm_grad_sq_sub_mul`) and pass to the limit in difference
quotients.

## File layout

* `PerronVariational.Inner.WeissTime.EnergyMoment`: the energy moment `energyMoment`, its time
  derivative and increment bound.
* `PerronVariational.Inner.WeissTime.Translation`: translation continuity, time translations of the
  mollified energy density, the spatial mollification error and auxiliary lemmas for the assembly.
* `PerronVariational.Inner.WeissTime.ChiEps`: Lemma 4.3: temporal translations of `χ_ε` and the
  compactness statement.
-/

@[expose] public section

end
