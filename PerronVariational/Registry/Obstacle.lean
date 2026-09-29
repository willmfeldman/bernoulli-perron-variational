/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
public import PerronVariational.Foundations.Glue

/-!
# Registry: one-sided obstacle problems for `J_Q`

Results from the literature used in the proof of Lemma 6.3 of F. Abedin, W. M. Feldman,
K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli one-phase
problem*, arXiv:2609.14981 ("the paper").

* `Registry.obstacle_below_exists`, `Registry.obstacle_above_exists`: minimizers of `J_Q(·; B)`
  with `u` as an upper (resp. lower) obstacle exist and are continuous in `B`. The paper cites
  [FKP2, §3], which does not cover this problem (see the docstrings). Proved in
  elliptic-bernoulli-foundations v0.1.0.
* `Registry.energy_decrease_of_not_super`, `Registry.energy_decrease_of_not_sub`: if a smooth
  function touching `w` strictly from below (resp. above) violates the supersolution (resp.
  subsolution) condition of Def 2.1, the local upward (resp. downward) perturbation
  `w ∨ (φ + δ)₊` (resp. `w ∧ (φ - δ)₊`) strictly decreases `J_Q` ([FKP, proof of Lemma 3.3 and
  Lemma A.1]). Proved in elliptic-bernoulli-foundations v0.1.0.

Competitors encode `u - v ∈ H¹₀(B)` as `v = u` a.e. outside `B` (equivalent for balls, which
have Lipschitz boundary), and carry weak gradients as explicit data; `B` is a ball `B_r(x₀)` with
`B̄ ⊆ U`.

References. [FKP] W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate independent
droplet evolution*, arXiv:2310.03656. [FKP2] W. M. Feldman, I. C. Kim, N. Požár, *An obstacle
approach to rate-independent droplet evolution*, Forum Math. Sigma 14 (2026), Paper No. e38,
doi:10.1017/fms.2026.10189. M. Giaquinta and E. Giusti, *Quasi-minima*, Ann. Inst. H. Poincaré
Anal. Non Linéaire 1 (1984), 79–107. E. Giusti, *Direct Methods in the Calculus of Variations*,
World Scientific, 2003.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

namespace Registry

variable {d : ℕ}

/-- **Obstacle problem, obstacle from above.** Let `U` be open, `Q` Lipschitz on `U` with
`0 < c ≤ Q ≤ C` on `U`, `u ≥ 0` locally Lipschitz on `U` with `u ∈ H¹_loc(U)` (weak gradient
`Gu`), and `B = B_r(x₀)` with `B̄ ⊆ U`. Then the problem
`min {J_Q(w; B) : w ∈ u + H¹₀(B), 0 ≤ w ≤ u}` (paper (6.1)) has a
minimizer `w` which is continuous in `B`; we take the representative with `w = u` on `U \ B`
(so `0 ≤ w ≤ u` holds everywhere on `U`).

Only continuity *in* `B` is asserted, as in the paper's claim. The paper also needs continuity
of `w` across `∂B` (to call `w` a supersolution in `U`) but does not argue it; here it is proved
separately in `Regularity/ObstacleBoundary.lean`.

A result from the literature: existence by the direct method; interior continuity by De Giorgi /
quasi-minimizer regularity (Giaquinta–Giusti; Giusti, Ch. 7). The paper cites [FKP2, Section 3]
here, but that section treats domain obstacles (the constraint `u > 0` in a set, or `u = 0` off
it), not function obstacles, so we rely on the quasi-minimizer route instead. Paper: Lemma 6.3,
Step 1.

Proved in elliptic-bernoulli-foundations v0.1.0 (`exists_obstacle_below`,
`IsObstacleMinimizer.exists_continuousOn`), through the bridge `Foundations.obstacle_below_exists`.
-/
theorem obstacle_below_exists {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d} (hU : IsOpen U)
    (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    (hGu : MemH1Loc U u Gu) {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc U w Gw ∧ ContinuousOn w (ball x₀ r) ∧
      (∀ y ∈ U \ ball x₀ r, w y = u y) ∧ (∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y) ∧
      ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
        (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
        energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv :=
  Foundations.obstacle_below_exists hU hQ hQpos hQb hu hu0 hGu hr hB

/-- **Obstacle problem, obstacle from below.** Same hypotheses as `obstacle_below_exists`. The
problem `min {J_Q(w; B) : w ∈ u + H¹₀(B), w ≥ u}` (paper (6.3)) has a
minimizer `w` which is continuous in `B`; we take the representative with `w = u` on `U \ B`
(so `w ≥ u` everywhere on `U`).

A result from the literature: as for `obstacle_below_exists` (the paper's citation of
[FKP2, Section 3] does not fit here either). Paper: Lemma 6.3, Step 2 ("which exists and is
continuous as before").

Proved in elliptic-bernoulli-foundations v0.1.0 (`exists_obstacle_above`,
`IsObstacleMinimizer.exists_continuousOn`), through the bridge `Foundations.obstacle_above_exists`.
-/
theorem obstacle_above_exists {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d} (hU : IsOpen U)
    (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu : LocallyLipschitzOn U u) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    (hGu : MemH1Loc U u Gu) {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), MemH1Loc U w Gw ∧ ContinuousOn w (ball x₀ r) ∧
      (∀ y ∈ U \ ball x₀ r, w y = u y) ∧ (∀ y ∈ U, u y ≤ w y) ∧
      ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
        (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
        energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv :=
  Foundations.obstacle_above_exists hU hQ hQpos hQb hu hu0 hGu hr hB

/-- **Energy decrease when the supersolution condition fails.** Let `U` be open, `Q` Lipschitz on
`U` with `0 < c ≤ Q ≤ C` on `U`, `w ≥ 0` continuous on `U` with `w ∈ H¹_loc(U)` (weak gradient
`Gw`), `B` open with `B ⊂⊂ U`, and `φ` smooth touching `w` *strictly* from below at `x₀ ∈ B`
(`φ(x₀) = w(x₀)`, `φ < w` in a punctured neighbourhood of `x₀`) such that the supersolution
condition of Def 2.1(i) fails at `x₀`: `Δφ(x₀) > 0` and (`φ(x₀) = 0 → |∇φ(x₀)| > Q(x₀)`).
Then for every `ρ > 0` with `B_ρ(x₀) ⊆ B` and every `η > 0` there is a competitor `w'` with
`w ≤ w' ≤ max(w, φ + η)` on `U`, `w' = w` on `U \ B_ρ(x₀)`, `w' ∈ H¹_loc(U)`, and
`J_Q(w'; B) < J_Q(w; B)`. (In the paper `w' = w ∨ (φ + δ)₊` near `x₀` for small `δ > 0`.)

A result from the literature: [FKP, proof of Lemma 3.3] and the energy difference formula
[FKP, Lemma A.1]. Paper: proof of Lemma 6.3, Step 1. The paper applies it to a test function that
touches `w`, but the perturbation argument needs *strict* touching, which is what is assumed here
(the proof of Lemma 6.3 in `Main/Directional.lean` reduces to it by a small quartic perturbation
of the test function).

Proved in elliptic-bernoulli-foundations v0.1.0 (`energy_decrease_of_not_super`), through the
bridge `Foundations.energy_decrease_of_not_super`. -/
theorem energy_decrease_of_not_super {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (htouch : φ x₀ = w x₀ ∧ ∀ᶠ y in 𝓝[≠] x₀, φ y < w y)
    (hfail : 0 < Δ φ x₀ ∧ (φ x₀ = 0 → Q x₀ < ‖∇ φ x₀‖)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, w y ≤ w' y ∧ w' y ≤ max (w y) (φ y + η)) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw :=
  Foundations.energy_decrease_of_not_super hU hQ hQpos hQb hw hw0 hGw hB hBU hφ hx₀ htouch hfail

/-- **Energy decrease when the subsolution condition fails.** Let `U` be open, `Q` Lipschitz on
`U` with `0 < c ≤ Q ≤ C` on `U`, `w ≥ 0` continuous on `U` with `w ∈ H¹_loc(U)`, `B` open with
`B ⊂⊂ U`, and `φ` smooth such that `φ₊` touches `w` *strictly* from above in
`\overline{{w > 0}} ∩ U` at `x₀ ∈ B` (`x₀ ∈ \overline{{w > 0}}`, `φ₊(x₀) = w(x₀)`, `w < φ₊` at
the other points of `\overline{{w > 0}} ∩ U` near `x₀`), and the subsolution condition of
Def 2.1(ii) fails at `x₀`: `Δφ(x₀) < 0` and (`φ(x₀) = 0 → |∇φ(x₀)| < Q(x₀)`). Then for every
`ρ > 0` with `B_ρ(x₀) ⊆ B` and every `η > 0` there is a competitor `w'` with
`min(w, (φ - η)₊) ≤ w' ≤ w` on `U`, `w' = w` on `U \ B_ρ(x₀)`, `w' ∈ H¹_loc(U)`, and
`J_Q(w'; B) < J_Q(w; B)`. (In the paper `w' = w ∧ (φ - δ)₊` near `x₀` for small `δ > 0`.)

A result from the literature: [FKP, proof of Lemma 3.3] and [FKP, Lemma A.1]. Paper: proof of
Lemma 6.3, Step 2. As in the supersolution case, strict touching is assumed.

Proved in elliptic-bernoulli-foundations v0.1.0 (`energy_decrease_of_not_sub`), through the
bridge `Foundations.energy_decrease_of_not_sub`. -/
theorem energy_decrease_of_not_sub {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (hx₀pos : x₀ ∈ closure (posSet w U))
    (htouch : max (φ x₀) 0 = w x₀ ∧
      ∀ᶠ y in 𝓝[(closure (posSet w U) ∩ U) \ {x₀}] x₀, w y < max (φ y) 0)
    (hfail : Δ φ x₀ < 0 ∧ (φ x₀ = 0 → ‖∇ φ x₀‖ < Q x₀)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, min (w y) (max (φ y - η) 0) ≤ w' y ∧ w' y ≤ w y) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw :=
  Foundations.energy_decrease_of_not_sub hU hQ hQpos hQb hw hw0 hGw hB hBU hφ hx₀ hx₀pos htouch
    hfail

end Registry

end PerronVariational

end
