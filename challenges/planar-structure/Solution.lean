module

public import Vocabulary
public import PerronVariational

/-!
# Solution: Corollary 1.2, and the two-disc model example

The trusted vocabulary of `Vocabulary.lean` is reconciled with the library's, then the library
theorems `PerronVariational.corollary_2d_smallest` and `PerronVariational.corollary_2d_largest`
are applied.

* `HasC2Boundary`, `IsStrictSub`, `IsStrictSuper`, `perronSmallest`, `perronLargest`,
  `freeBoundary`, `IsClassicalNear` and `IsBlowupLimit` are definitionally the library's.
* The unbundled hypotheses on `U` and `Q` are packed into the library's `Setting 2`, whose field
  `2 ≤ 2` is discharged by `le_rfl`.
* The model example: the library theorem `PerronVariational.TwoDisc.model_example` applies after
  unpacking its `Setting`: the domain is `U = B₁(0) \ (B̄_{1/20}(p) ∪ B̄_{1/20}(-p))`,
  `p = (1/10, 0)`, with `Q ≡ 1`.
-/

open Set Metric

@[expose] public section

namespace PerronVariationalChallenge.Bridge

variable {d : ℕ}

theorem hasC2Boundary_iff (U : Set (E d)) :
    HasC2Boundary U ↔ PerronVariational.HasC2Boundary U := Iff.rfl

theorem isStrictSub_iff (U : Set (E d)) (Q g : E d → ℝ) :
    IsStrictSub U Q g ↔ PerronVariational.IsStrictSub U Q g := Iff.rfl

theorem isStrictSuper_iff (U : Set (E d)) (Q g : E d → ℝ) :
    IsStrictSuper U Q g ↔ PerronVariational.IsStrictSuper U Q g := Iff.rfl

theorem perronSmallest_eq (U : Set (E d)) (Q g : E d → ℝ) :
    perronSmallest U Q g = PerronVariational.perronSmallest U Q g := rfl

theorem perronLargest_eq (U : Set (E d)) (Q g : E d → ℝ) :
    perronLargest U Q g = PerronVariational.perronLargest U Q g := rfl

theorem freeBoundary_eq (u : E d → ℝ) (U : Set (E d)) :
    freeBoundary u U = PerronVariational.freeBoundary u U := rfl

theorem isClassicalNear_iff (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) :
    IsClassicalNear U Q u x₀ ↔ PerronVariational.IsClassicalNear U Q u x₀ := Iff.rfl

theorem isBlowupLimit_iff (u : E d → ℝ) (x₀ : E d) (v : E d → ℝ) :
    IsBlowupLimit u x₀ v ↔ PerronVariational.IsBlowupLimit u x₀ v := Iff.rfl

end PerronVariationalChallenge.Bridge

open PerronVariationalChallenge PerronVariationalChallenge.Bridge

theorem challenge_corollary_2d_smallest : Corollary2DSmallestClaim := by
  intro U Q Qmin Qmax hU hb hc hC2 hlip hQmin hQle hQ g hg hgpos
  let S : PerronVariational.Setting 2 :=
    ⟨U, Q, Qmin, Qmax, le_rfl, hU, hb, hc, (hasC2Boundary_iff U).1 hC2, hlip, hQmin, hQle, hQ⟩
  obtain ⟨FBreg, FBtp, hdisj, hunion, hopen, hreg, htp⟩ :=
    PerronVariational.corollary_2d_smallest S g ((isStrictSub_iff U Q g).1 hg) hgpos
  rw [perronSmallest_eq, freeBoundary_eq]
  exact ⟨FBreg, FBtp, hdisj, hunion, hopen,
    fun x₀ hx₀ ↦ (isClassicalNear_iff ..).2 (hreg x₀ hx₀),
    fun x₀ hx₀ v hv ↦ htp x₀ hx₀ v ((isBlowupLimit_iff ..).1 hv)⟩

theorem challenge_corollary_2d_largest : Corollary2DLargestClaim := by
  intro U Q Qmin Qmax hU hb hc hC2 hlip hQmin hQle hQ g hg x₀ hx₀
  let S : PerronVariational.Setting 2 :=
    ⟨U, Q, Qmin, Qmax, le_rfl, hU, hb, hc, (hasC2Boundary_iff U).1 hC2, hlip, hQmin, hQle, hQ⟩
  rw [perronLargest_eq] at hx₀ ⊢
  exact (isClassicalNear_iff ..).2
    (PerronVariational.corollary_2d_largest S g ((isStrictSuper_iff U Q g).1 hg) x₀ hx₀)

theorem challenge_model_example : ModelExampleClaim := by
  obtain ⟨S, gsub, gsuper, hQ, hsub, hpos, hsup, hbd, h1, h2, h3, h4, h5, h6, h0, hlim, hbl, hne⟩ :=
    PerronVariational.TwoDisc.model_example
  rw [hQ] at hsub hsup h1 h2 h3 h4 h5 h6 h0 hlim hbl hne
  exact ⟨S.U, gsub, gsuper, S.isOpen, S.isBounded, S.isConnected, (hasC2Boundary_iff _).2 S.c2,
    ⟨0, (LipschitzWith.const (1 : ℝ)).lipschitzOnWith⟩, (isStrictSub_iff ..).2 hsub, hpos,
    (isStrictSuper_iff ..).2 hsup, hbd, h1, h2, h3, h4, h5, h6, h0, hlim,
    fun v hv ↦ hbl v ((isBlowupLimit_iff ..).1 hv), hne⟩
