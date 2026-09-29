/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import PerronVariational.Parabolic.LongTimeViscosity
import PerronVariational.Stationary.InnerSub

/-!
# Lemma 5.8 / Theorem 3.12(ii): long-time limits of inner variational supersolutions

**Lemma 5.8** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: a bounded, time-monotone
parabolic inner variational solution `(u, χ)` which is a parabolic viscosity supersolution and
satisfies (3.11)–(3.13) has, along some `tᵢ → ∞`, a locally uniform limit `u_∞` with
`χ(·, tᵢ) → χ_∞` in `L¹_loc`, and `u_∞` is a viscosity solution of (1.1).

The paper assumes neither boundedness nor time monotonicity in Lemma 5.8 (Theorem 3.12(ii)
assumes boundedness); here we assume both, because the lemma is proved from Theorem 3.10, which
is formalized for bounded, time-monotone flows. Step 1 of the paper's proof of Theorem 3.10
deduces that `u(·, t)` is Cauchy in `L²` from `∂ₜu ∈ L²(U_∞)`, which does not follow; monotonicity
in time gives the limit, and it holds in every application (Propositions 6.1 and 6.2).

The result is proved from the statement of **Theorem 3.10** (`LongtimeInnerStatement`), taken as
a hypothesis, together with
* Lemma 2.9 (`IsInnerVarSolution.isViscSub`): the inner variational limit `(u_∞, χ_∞)` gives
  the viscosity subsolution property;
* Lemma 5.6 (`longtime_super`): the locally uniform limit of a parabolic supersolution is a
  stationary supersolution.

Compared with the paper's proof, Lemma 2.10 (compactness of inner variational solutions) is not
needed: `LongtimeInnerStatement` already states that `(u_∞, χ_∞)` is an inner variational
solution.
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

/-- The standing assumptions give the hypotheses on `Q` used by Lemma 2.9 on `U`. -/
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

/-- **Lemma 5.8** = **Theorem 3.12(ii)**, from **Theorem 3.10** (`LongtimeInnerStatement`),
Lemma 2.9 and Lemma 5.6. -/
theorem longtime_viscosity_inner_of (h310 : LongtimeInnerStatement) :
    LongtimeViscInnerStatement := by
  intro d S u w χ M E0 C Cper hinner hheat hsuper hbdd hmono hE0 hdiss hLip hPer
  obtain ⟨CV, hCV⟩ := h310 d S M E0 C Cper hE0
  obtain ⟨uInf, hconv, t, χInf, ht, -, hχ, hInfInner, -, -⟩ :=
    hCV u w χ hinner hheat hbdd hmono hdiss hLip hPer
  refine ⟨t, uInf, χInf, ht, TendstoLocallyUniformlyOn.comp_tendsto hconv ht, hχ, ?_, ?_⟩
  · -- Lemma 5.6
    exact longtime_super S.isOpen S.continuousOn_Q hsuper hconv
  · -- Lemma 2.9
    exact hInfInner.isViscSub S.two_le S.isOpen S.isConnected S.lipschitzOn_U S.exists_pos_le_Q
      S.exists_Q_le

end PerronVariational

end
