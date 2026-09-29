/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Main.Corollary2D.Supersolution
public import PerronVariational.Main.Corollary2D.Flat
public import PerronVariational.Main.Corollary2D.Structure

/-!
# Corollary 1.2: structure of the free boundary of extremal solutions in the plane

**Corollary 1.2** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

## Part 1: classical points form a relatively open set

`IsClassicalNear U Q u x₀` propagates to all points of the ball in which it holds
(`IsClassicalNear.eventually`), so the set of classical points is open. We take
`FB_reg := {x ∈ ∂{u > 0} ∩ U : u is classical near x}` and `FB_TP := ∂{u > 0} ∩ U \ FB_reg`.

## File layout

* `PerronVariational.Main.Corollary2D.Supersolution`: openness of the set of classical points,
  blow-ups of supersolutions and the supersolution test for two-plane functions.
* `PerronVariational.Main.Corollary2D.Flat`: flatness from half-plane blow-ups.
* `PerronVariational.Main.Corollary2D.Structure`: classification of blow-ups in the plane and
  Corollary 1.2 (i), (ii).
-/

@[expose] public section

end
