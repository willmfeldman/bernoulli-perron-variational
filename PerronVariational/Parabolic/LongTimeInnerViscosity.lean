/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import PerronVariational.Inner.LongTimeMonotone
import PerronVariational.Parabolic.LongTimeViscosity
import PerronVariational.Stationary.InnerSub

/-!
# Long-time limits of inner variational supersolutions

**[Lemma 5.8](#AFS:l.subsolution-inner-limit)** of F. Abedin, W. M. Feldman, K.
Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981: a bounded, time-monotone parabolic inner variational solution `(u, χ)` which is a
parabolic viscosity supersolution and satisfies [(3.12)](#AFS:eqn:diss2)–[(3.14)](#AFS:eqn:chiEst2)
has, along some `tᵢ → ∞`, a locally uniform limit `u_∞` with `χ(·, tᵢ) → χ_∞` in `L¹_loc`, and `u_∞`
is a viscosity solution of [(1.1)](#AFS:e.bernoulli-basic).

This is the form of [Theorem 3.16(ii)](#AFS:part.longtime-viscosity-2) (bounded, time-monotone
flows). [Lemma 5.8](#AFS:l.subsolution-inner-limit) of the paper assumes, instead of time
monotonicity, that `u(·, t)` converges locally uniformly as `t → ∞`; for monotone flows this
convergence holds (the remark after [Lemma 5.8](#AFS:l.subsolution-inner-limit)), and time
monotonicity holds in every application (Propositions [6.1](#AFS:p.inner-smallest) and
[6.2](#AFS:p.inner-largest)).

The result is proved from the statement of **[Theorem 3.14](#AFS:t.longtime-inner)**
(`LongtimeInnerStatement`), taken as a hypothesis, through its monotone form
(`LongtimeInnerStatement.monotone`), together with
* [Lemma 2.12](#AFS:l.inner-variational-implies-subsoln) (`IsInnerVarSolution.isViscSub`): the inner
  variational limit `(u_∞, χ_∞)` gives the viscosity subsolution property;
* [Proposition 5.6](#AFS:p.supersolution-limit) (`longtime_super`): the locally uniform limit of a
  parabolic supersolution is a stationary supersolution.
-/

open Set Filter Topology MeasureTheory Metric

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- Locally uniform convergence along a filter `l` passes to `F ∘ φ` along any `q` with
`φ → l`. -/
theorem TendstoLocallyUniformlyOn.comp_tendsto {α β ι κ : Type*} [TopologicalSpace α]
    [UniformSpace β] {F : ι → α → β} {f : α → β} {l : Filter ι} {s : Set α}
    (h : TendstoLocallyUniformlyOn F f l s) {q : Filter κ} {φ : κ → ι} (hφ : Tendsto φ q l) :
    TendstoLocallyUniformlyOn (fun k ↦ F (φ k)) f q s := by
  intro V hV x hx
  obtain ⟨t, ht, H⟩ := h V hV x hx
  exact ⟨t, ht, hφ.eventually H⟩

/-- The standing assumptions give the hypotheses on `Q` used by
[Lemma 2.12](#AFS:l.inner-variational-implies-subsoln) on `U`. -/
theorem Setting.lipschitzOn_U (S : Setting d) : ∃ K, LipschitzOnWith K S.Q S.U := by
  obtain ⟨K, hK⟩ := S.lip
  exact ⟨K, hK.mono subset_closure⟩

theorem Setting.continuousOn_Q (S : Setting d) : ContinuousOn S.Q S.U := by
  obtain ⟨K, hK⟩ := S.lipschitzOn_U
  exact hK.continuousOn

theorem Setting.exists_pos_le_Q (S : Setting d) : ∃ c > 0, ∀ x ∈ S.U, c ≤ S.Q x :=
  ⟨S.Qmin, S.Qmin_pos, fun x hx ↦ (S.Q_mem x (subset_closure hx)).1⟩

theorem Setting.exists_Q_le (S : Setting d) : ∃ C, ∀ x ∈ S.U, S.Q x ≤ C :=
  ⟨S.Qmax, fun x hx ↦ (S.Q_mem x (subset_closure hx)).2⟩

/-- **[Lemma 5.8](#AFS:l.subsolution-inner-limit)**, which is
[Theorem 3.16(ii)](#AFS:part.longtime-viscosity-2), from [Theorem 3.14](#AFS:t.longtime-inner)
(`LongtimeInnerStatement`), [Lemma 2.12](#AFS:l.inner-variational-implies-subsoln) and
[Proposition 5.6](#AFS:p.supersolution-limit). -/
theorem longtime_viscosity_inner_of (h310 : LongtimeInnerStatement) :
    LongtimeViscInnerStatement := by
  intro d S u w χ M E0 C Cper hinner hheat hsuper hbdd hmono hE0 hdiss hLip hPer
  obtain ⟨CV, hCV⟩ := LongtimeInnerStatement.monotone h310 d S M E0 C Cper hE0
  obtain ⟨uInf, hconv, t, χInf, ht, -, hχ, hInfInner, -, -⟩ :=
    hCV u w χ hinner hheat hbdd hmono hdiss hLip hPer
  refine ⟨t, uInf, χInf, ht, TendstoLocallyUniformlyOn.comp_tendsto hconv ht, hχ, ?_, ?_⟩
  · -- [Proposition 5.6](#AFS:p.supersolution-limit)
    exact longtime_super S.isOpen S.continuousOn_Q
      (fun x hx ↦ S.Qmin_pos.le.trans (S.Q_mem x (subset_closure hx)).1) hsuper hconv
  · -- [Lemma 2.12](#AFS:l.inner-variational-implies-subsoln)
    exact hInfInner.isViscSub S.two_le S.isOpen S.isConnected S.lipschitzOn_U S.exists_pos_le_Q
      S.exists_Q_le

end PerronVariational

end
