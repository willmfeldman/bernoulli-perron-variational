import Statement
import PerronVariational

/-!
# Solution: the two-disc model example

The trusted vocabulary of `Statement.lean` is definitionally the library's (see the bridge in
`challenges/main-theorem/Solution.lean`), so the library theorem
`PerronVariational.TwoDisc.model_example` applies after unpacking its `Setting`: the domain is
`U = B₁(0) \ (B̄_{1/20}(p) ∪ B̄_{1/20}(-p))`, `p = (1/10, 0)`, with `Q ≡ 1`.
-/

open Set Metric

namespace PerronVariationalChallenge.Bridge

theorem hasC2Boundary_iff (U : Set (E 2)) :
    HasC2Boundary U ↔ PerronVariational.HasC2Boundary U := Iff.rfl

theorem isStrictSub_iff (U : Set (E 2)) (Q g : E 2 → ℝ) :
    IsStrictSub U Q g ↔ PerronVariational.IsStrictSub U Q g := Iff.rfl

theorem isStrictSuper_iff (U : Set (E 2)) (Q g : E 2 → ℝ) :
    IsStrictSuper U Q g ↔ PerronVariational.IsStrictSuper U Q g := Iff.rfl

theorem perronSmallest_eq (U : Set (E 2)) (Q g : E 2 → ℝ) :
    perronSmallest U Q g = PerronVariational.perronSmallest U Q g := rfl

theorem perronLargest_eq (U : Set (E 2)) (Q g : E 2 → ℝ) :
    perronLargest U Q g = PerronVariational.perronLargest U Q g := rfl

theorem freeBoundary_eq (u : E 2 → ℝ) (U : Set (E 2)) :
    freeBoundary u U = PerronVariational.freeBoundary u U := rfl

theorem blowup_eq (u : E 2 → ℝ) (x₀ : E 2) (r : ℝ) :
    blowup u x₀ r = PerronVariational.blowup u x₀ r := rfl

theorem isBlowupLimit_iff (u : E 2 → ℝ) (x₀ : E 2) (v : E 2 → ℝ) :
    IsBlowupLimit u x₀ v ↔ PerronVariational.IsBlowupLimit u x₀ v := Iff.rfl

end PerronVariationalChallenge.Bridge

open PerronVariationalChallenge PerronVariationalChallenge.Bridge

theorem challenge_model_example : ModelExampleClaim := by
  obtain ⟨S, gsub, gsuper, hQ, hsub, hpos, hsup, hbd, h1, h2, h3, h4, h5, h6, h0, hlim, hbl, hne⟩ :=
    PerronVariational.TwoDisc.model_example
  rw [hQ] at hsub hsup h1 h2 h3 h4 h5 h6 h0 hlim hbl hne
  exact ⟨S.U, gsub, gsuper, S.isOpen, S.isBounded, S.isConnected, (hasC2Boundary_iff _).2 S.c2,
    ⟨0, (LipschitzWith.const (1 : ℝ)).lipschitzOnWith⟩, (isStrictSub_iff ..).2 hsub, hpos,
    (isStrictSuper_iff ..).2 hsup, hbd, h1, h2, h3, h4, h5, h6, h0, hlim,
    fun v hv ↦ hbl v ((isBlowupLimit_iff ..).1 hv), hne⟩
