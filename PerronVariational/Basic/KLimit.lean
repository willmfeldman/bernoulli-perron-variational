/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Upper Kuratowski limits and strict ordering on a set

Notation from F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

* `upperKLimit A l`: the paper's `limsup*` of sets (used in Lemma 2.4, Prop 5.3 and Lemma 5.5).
* `PrecOn u v E F`: the paper's `u ≺_E v on F` (Definition 3.1).
-/

open Set Filter Topology

@[expose] public section

namespace PerronVariational

variable {X ι : Type*}

/-- Upper Kuratowski limit of a family of sets along a filter (paper's `limsup*`):
`x` belongs to it iff every neighbourhood of `x` meets `A i` for frequently many `i` along `l`.
For `l = atTop` on `ℕ` in a metric space this is the set of limits `x = lim x_{j_k}` of
subsequences with `x_{j_k} ∈ A_{j_k}`, which is the paper's usage (e.g. the proof of
Lemma 5.1). -/
def upperKLimit [TopologicalSpace X] (A : ι → Set X) (l : Filter ι) : Set X :=
  {x | ∀ N ∈ 𝓝 x, ∃ᶠ i in l, (A i ∩ N).Nonempty}

/-- `u ≺_E v on F` (paper, Definition 3.1): `u < v` on `E ∩ F`. -/
def PrecOn (u v : X → ℝ) (Eset F : Set X) : Prop := ∀ p ∈ Eset ∩ F, u p < v p

end PerronVariational

end
