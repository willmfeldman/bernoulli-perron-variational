/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Registry.Semilinear
public import PerronVariational.Parabolic.BernoulliComparisonBridge

/-!
# Registry: comparison principles

Comparison principles from the literature used in F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 ("the paper"). References: I. C. Kim, *A free boundary problem arising in flame
propagation*, J. Differential Equations 191 (2003), no. 2, 470–489,
doi:10.1016/S0022-0396(02)00195-X; M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to
viscosity solutions of second order partial differential equations*, Bull. Amer. Math. Soc.
(N.S.) 27 (1992), 1–67, doi:10.1090/S0273-0979-1992-00266-5.

* `Registry.para_strict_comparison`: strict comparison for the parabolic Bernoulli problem
  [(3.1)](#AFS:e.bernoulli-parabolic), the paper's [Thm 3.7](#AFS:t.comparison), from Kim (2003),
  Thm 2.2. Proved in bernoulli-parabolic-comparison (`BernoulliComparison.para_strict_comparison`)
  for its pointwise classical strict barriers; the parabolic notions agree with the paper's
  (uniform barriers) when `Q` is continuous and positive, see
  `Parabolic/BernoulliComparisonBridge.lean`.
* `Registry.semilinear_comparison`: comparison between continuous viscosity sub- and
  supersolutions of the semilinear equation `∂ₜu = Δu - Q² β_ε(u)` on a cylinder `V × (a, b]`
  (paper, start of [Appendix B](#AFS:s.semilinear)). Proved in parabolic-basic-theory v0.1.0
  (`ParabolicBasic.semilinear_comparison` with `f(x, z) = Q(x)² β_ε(z)`).
-/

open Set Filter Topology

@[expose] public section

namespace PerronVariational

namespace Registry

variable {d : ℕ}

/-- **Strict comparison (paper, [Thm 3.7](#AFS:t.comparison)).**
Let `U` be a bounded domain (open, bounded, connected), `Q` Lipschitz on `Ū` with a positive lower
bound, `T > 0`, and `u, v ∈ C(Ū × [0, T])` respectively a viscosity subsolution and a viscosity
supersolution ([Def 3.3](#AFS:d.parabolic-supersolution)) of [(3.1)](#AFS:e.bernoulli-parabolic) in
`U × (0, T]`. If `u ≺ v` on a neighbourhood `N` of the parabolic boundary
`∂_P(U × (0, T]) = (Ū × {0}) ∪ (∂U × [0, T])`, then `u ≺ v` on `Ū × [0, T]`.

Here `≺` is taken with `E = \overline{{u > 0}}`, `{u > 0}` computed in the domain
`Ū × [0, T]` of `u` (paper, [Def 3.1](#AFS:d.prec-ordering): `E` closed in `Ū × [0, T]`); since `u`
is continuous on `Ū × [0, T] = \overline{U × (0, T]}`, this closure is the same as the closure of
`{u > 0}` computed in `U × (0, T]`.

A result from the literature: Kim (2003), Theorem 2.2 (on the whole space; the paper, after
[Thm 3.7](#AFS:t.comparison), explains the adaptation to a bounded domain via sup/inf-convolutions
on a slightly smaller domain using the strict ordering near `∂_P`). Used in Props
[6.1](#AFS:p.inner-smallest) and [6.2](#AFS:p.inner-largest). Proved in
bernoulli-parabolic-comparison: `BernoulliComparison.para_strict_comparison` (which does not need
connectedness of `U`), for its pointwise classical strict barriers; transported through
`isParaSub_iff_bpc` and `isParaSuper_iff_bpc`. -/
theorem para_strict_comparison {U : Set (E d)} {Q : E d → ℝ} {T : ℝ} {u v : E d × ℝ → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (_hUc : IsConnected U)
    (hQ : ∃ K, LipschitzOnWith K Q (closure U)) (hQpos : ∃ c > 0, ∀ x ∈ closure U, c ≤ Q x)
    (hT : 0 < T) (hu : ContinuousOn u (closure U ×ˢ Icc 0 T))
    (hv : ContinuousOn v (closure U ×ˢ Icc 0 T))
    (hsub : IsParaSub U Q (Ioc 0 T) u) (hsuper : IsParaSuper U Q (Ioc 0 T) v)
    {N : Set (E d × ℝ)} (hN : N ∈ 𝓝ˢ (parBdry U 0 T))
    (hprec : Prec u v (closure U ×ˢ Icc 0 T) N) :
    Prec u v (closure U ×ˢ Icc 0 T) (closure U ×ˢ Icc 0 T) :=
  have hQc : ContinuousOn Q U := let ⟨_, hK⟩ := hQ; hK.continuousOn.mono subset_closure
  have hQU : ∀ x ∈ U, 0 < Q x := fun x hx ↦
    let ⟨_, hc, hcle⟩ := hQpos; hc.trans_le (hcle x (subset_closure hx))
  BernoulliComparison.para_strict_comparison hU hUb hQ hQpos hT hu hv
    ((isParaSub_iff_bpc hU hQc hQU).1 hsub) ((isParaSuper_iff_bpc hU hQc hQU).1 hsuper) hN hprec

/-- **Comparison for the semilinear equation.**
Let `V ⊆ ℝᵈ` be bounded and open, `a < b`, `Q` Lipschitz on `V̄`, `β` a reaction profile
[(3.5)](#AFS:e.beta-conditions) and `ε > 0` (so `z ↦ Q(x)² β_ε(z)` is bounded and Lipschitz in `z`,
uniformly in `x`). If `u` is a continuous viscosity subsolution and `v` a continuous viscosity
supersolution of `∂ₜu = Δu - Q² β_ε(u)` in `V × (a, b]` (`IsSemilinearViscSubOn`,
`IsSemilinearViscSuperOn`), both continuous on `V̄ × [a, b]`, and `u ≤ v` on the parabolic boundary
`∂_P(V × (a, b]) = (V̄ × {a}) ∪ (∂V × [a, b])`, then `u ≤ v` on `V̄ × [a, b]`.

A result from the literature: Crandall–Ishii–Lions, Theorem 8.2 (parabolic comparison on bounded
cylinders), applied after the change of unknown `e^{-λt} u` which makes the zero-order term monotone
(the nonlinearity is Lipschitz in `u`). Our subsolution notion (touching relative to the parabolic
past, `C²` test functions) is at least as strong as the one in Crandall–Ishii–Lions, §8, so the
cited theorem applies. Paper, start of [Appendix B](#AFS:s.semilinear) ("the parabolic comparison
principle holds between continuous viscosity sub and supersolutions"), which cites the same Theorem
8.2 and makes the equation proper by proving comparison for `e^{-λt} u` with `λ > Lip(β_ε)`; used in
[Lemma B.1](#AFS:l.monotone), [Prop 5.3](#AFS:p.semilinear-limit-viscosity),
[Lemma B.6](#AFS:l.attainment-lateral) and [Cor B.9](#AFS:c.positivity-no-jump), and throughout the
semilinear approximation. Proved in parabolic-basic-theory v0.1.0:
`ParabolicBasic.semilinear_comparison` with `f(x, z) = Q(x)² β_ε(z)`, with `hfx`, `hfz` from
`semilinearReactionHyp` on `V̄`. -/
theorem semilinear_comparison {V : Set (E d)} {a b : ℝ} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ}
    {u v : E d × ℝ → ℝ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hab : a < b)
    (hQ : ∃ K, LipschitzOnWith K Q (closure V)) (hβ : IsReactionProfile β) (hε : 0 < ε)
    (hu : ContinuousOn u (closure V ×ˢ Icc a b)) (hv : ContinuousOn v (closure V ×ˢ Icc a b))
    (hsub : IsSemilinearViscSubOn V Q β ε (Ioc a b) u)
    (hsuper : IsSemilinearViscSuperOn V Q β ε (Ioc a b) v)
    (hbdry : ∀ p ∈ parBdry V a b, u p ≤ v p) :
    ∀ p ∈ closure V ×ˢ Icc a b, u p ≤ v p :=
  have hf := semilinearReactionHyp hβ hε hVb.isCompact_closure hQ
  ParabolicBasic.semilinear_comparison hV hVb hab hf.holder_x hf.lip_z hu hv hsub hsuper hbdry

end Registry

end PerronVariational

end
