/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary

/-!
# A two-disc model example: statement

A model example for F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 (`[AFS]`). It is not a
result of the paper; it shows that the two cases of [AFS, Theorem 1.1] can produce different
solutions from the same boundary data, and that the smallest supersolution can have a two-plane
point, the second alternative of [AFS, Corollary 1.2(i)].

The construction: in `ℝ²` with `Q ≡ 1`, `U = B₁(0) \ (B̄_{a/2}(a e₁) ∪ B̄_{a/2}(-a e₁))` for a small
`a > 0`. The data equal `a log 2` on both inner circles, so that the radial solutions
`(a log (a / |x ∓ a e₁|))₊` issuing from the two holes have free boundaries `∂B_a(± a e₁)`, which
touch at `0`.
-/

open Set Filter Topology Metric

@[expose] public section

namespace PerronVariational

/-- **The two-disc model example.** In `ℝ²` with `Q ≡ 1` there are a setting `S` and data
`g_sub`, `g_super` such that `g_sub` is a smooth strict subsolution with `g_sub > 0` on `∂U`,
`g_super` is a smooth strict supersolution, `g_sub = g_super` on `∂U`, and, writing
`u_min = perronSmallest U 1 g_sub` and `u_max = perronLargest U 1 g_super`:
1. `u_min` and `u_max` are nontrivial: each is positive somewhere in `U`, vanishes somewhere in
   `U`, and has a nonempty free boundary;
2. `0` is a two-plane point of `u_min`: `0 ∈ ∂{u_min > 0} ∩ U`, the blow-ups `(u_min)_{0,t}`
   converge to `y ↦ |y₁|` locally uniformly as `t → 0⁺`, and hence every blow-up limit of
   `u_min` at `0` is `y ↦ |y₁|` (here `y₁ = ⟪y, e₁⟫`);
3. `u_min ≠ u_max` in `U`. -/
def ModelExampleStatement : Prop :=
  ∃ (S : Setting 2) (gsub gsuper : E 2 → ℝ), S.Q = (fun _ ↦ 1) ∧
    IsStrictSub S.U S.Q gsub ∧ (∀ x ∈ frontier S.U, 0 < gsub x) ∧
    IsStrictSuper S.U S.Q gsuper ∧ (∀ x ∈ frontier S.U, gsub x = gsuper x) ∧
    (∃ x ∈ S.U, 0 < perronSmallest S.U S.Q gsub x) ∧
    (∃ x ∈ S.U, perronSmallest S.U S.Q gsub x = 0) ∧
    (freeBoundary (perronSmallest S.U S.Q gsub) S.U).Nonempty ∧
    (∃ x ∈ S.U, 0 < perronLargest S.U S.Q gsuper x) ∧
    (∃ x ∈ S.U, perronLargest S.U S.Q gsuper x = 0) ∧
    (freeBoundary (perronLargest S.U S.Q gsuper) S.U).Nonempty ∧
    (0 : E 2) ∈ freeBoundary (perronSmallest S.U S.Q gsub) S.U ∧
    TendstoLocallyUniformly (fun t ↦ blowup (perronSmallest S.U S.Q gsub) 0 t)
      (fun y ↦ |inner ℝ y (EuclideanSpace.single 0 1)|) (𝓝[>] 0) ∧
    (∀ v, IsBlowupLimit (perronSmallest S.U S.Q gsub) 0 v →
      ∀ y, v y = |inner ℝ y (EuclideanSpace.single 0 1)|) ∧
    ∃ x ∈ S.U, perronSmallest S.U S.Q gsub x ≠ perronLargest S.U S.Q gsuper x

end PerronVariational

end
