/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import PerronVariational.Inner.LongTimeUniform

/-!
# [Theorem 3.14](#AFS:t.longtime-inner) for flows monotone in time

For a flow monotone in time, the conclusion of **[Theorem 3.14](#AFS:t.longtime-inner)** of F.
Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the
Bernoulli one-phase problem*, arXiv:2609.14981, holds with `u(·, t) → u_∞` locally uniformly as
`t → ∞` along all times. This is the form used in Propositions [6.1](#AFS:p.inner-smallest) and
[6.2](#AFS:p.inner-largest) (`u_{a,∞} := lim_{t→∞} 𝔲_a(·, t)`) and in
[Lemma 5.8](#AFS:l.subsolution-inner-limit) / [Theorem 3.16(ii)](#AFS:part.longtime-viscosity-2).
The paper justifies it in the remark after [Lemma 5.8](#AFS:l.subsolution-inner-limit): for a
monotone flow the limit as `t → ∞` exists, and it is locally uniform by Arzelà–Ascoli and
[(3.13)](#AFS:eqn:LipEst); it agrees with the limit along the sequence `tᵢ` of
[Theorem 3.14](#AFS:t.longtime-inner).

## Main results

* `PerronVariational.LongtimeInnerStatement.monotone`: `LongtimeInnerStatement` implies
  `LongtimeInnerMonotoneStatement`.
-/

open Set Filter Topology

@[expose] public section

namespace PerronVariational

/-- **[Theorem 3.14](#AFS:t.longtime-inner) for monotone flows**, from
[Theorem 3.14](#AFS:t.longtime-inner): the full limit `u(·, t) → v` exists locally uniformly
(`LongTime.exists_tendstoLocallyUniformlyOn`), and `v = u_∞` on `U` by uniqueness of limits along
`tᵢ`. -/
theorem LongtimeInnerStatement.monotone (h : LongtimeInnerStatement) :
    LongtimeInnerMonotoneStatement := by
  intro d S M E0 C Cper hE0
  obtain ⟨CV, hCV⟩ := h d S M E0 C Cper hE0
  refine ⟨CV, fun u w χ hsol hheat hM hmono hdiss hlip hper ↦ ?_⟩
  obtain ⟨t, uInf, χInf, ht, hconvt, hgrad, hχ, hinner, h314, h315⟩ :=
    hCV u w χ hsol hheat hM hdiss hlip hper
  obtain ⟨v, hv, -, -⟩ := LongTime.exists_tendstoLocallyUniformlyOn S.isOpen hsol hM hmono hlip
  have heq : EqOn v uInf S.U := fun x hx ↦
    tendsto_nhds_unique ((hv.tendsto_at hx).comp ht) (hconvt.tendsto_at hx)
  exact ⟨uInf, hv.congr_right heq, t, χInf, ht, hgrad, hχ, hinner, h314, h315⟩

end PerronVariational

end
