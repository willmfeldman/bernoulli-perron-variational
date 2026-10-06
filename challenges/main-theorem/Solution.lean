module

public import Vocabulary
public import PerronVariational

/-!
# Solution: Theorem 1.1, and the two-disc model example

The trusted vocabulary of `Vocabulary.lean` is reconciled with the library's, then the library
theorems `PerronVariational.main_smallest` and `PerronVariational.main_largest` are applied.

* `HasC2Boundary`, `IsStrictSub`, `IsStrictSuper`, `perronSmallest`, `perronLargest`,
  `freeBoundary`, `IsViscSolution`, `IsDownwardMinimizer` and `IsUpwardMinimizer` are
  definitionally the library's.
* `IsInnerVarSolution` has the same fields as the library's structure (`isInnerVarSolution_iff`);
  its integrand `innerVarIntegrand` is definitionally the library's.
* `blowup` and `IsBlowupLimit` are definitionally the library's.
* The unbundled hypotheses on `U` and `Q` are packed into the library's `Setting d`.
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

theorem isViscSolution_iff (U : Set (E d)) (Q u : E d → ℝ) :
    IsViscSolution U Q u ↔ PerronVariational.IsViscSolution U Q u := Iff.rfl

theorem innerVarIntegrand_eq (Q u χ : E d → ℝ) (ξ : E d → E d) :
    innerVarIntegrand Q u χ ξ = PerronVariational.innerVarIntegrand Q u χ ξ := rfl

theorem isInnerVarSolution_iff (U : Set (E d)) (Q u χ : E d → ℝ) :
    IsInnerVarSolution U Q u χ ↔ PerronVariational.IsInnerVarSolution U Q u χ :=
  ⟨fun h ↦ ⟨h.nonneg, h.locLip, h.c2, h.harmonic, h.meas, h.zero_one, h.pos_le, h.stationary⟩,
    fun h ↦ ⟨h.nonneg, h.locLip, h.c2, h.harmonic, h.meas, h.zero_one, h.pos_le, h.stationary⟩⟩

theorem isDownwardMinimizer_iff (U : Set (E d)) (Q u : E d → ℝ) :
    IsDownwardMinimizer U Q u ↔ PerronVariational.IsDownwardMinimizer U Q u := Iff.rfl

theorem isUpwardMinimizer_iff (U : Set (E d)) (Q u : E d → ℝ) :
    IsUpwardMinimizer U Q u ↔ PerronVariational.IsUpwardMinimizer U Q u := Iff.rfl

theorem isBlowupLimit_iff (u : E d → ℝ) (x₀ : E d) (v : E d → ℝ) :
    IsBlowupLimit u x₀ v ↔ PerronVariational.IsBlowupLimit u x₀ v := Iff.rfl

end PerronVariationalChallenge.Bridge

open PerronVariationalChallenge PerronVariationalChallenge.Bridge

theorem challenge_main_smallest (d : ℕ) : MainSmallestClaim d := by
  intro hd U Q Qmin Qmax hU hb hc hC2 hlip hQmin hQle hQ g hg hgpos
  let S : PerronVariational.Setting d :=
    ⟨U, Q, Qmin, Qmax, hd, hU, hb, hc, (hasC2Boundary_iff U).1 hC2, hlip, hQmin, hQle, hQ⟩
  obtain ⟨h1, ⟨χ, h2⟩, h3⟩ :=
    PerronVariational.main_smallest d S g ((isStrictSub_iff U Q g).1 hg) hgpos
  rw [perronSmallest_eq]
  exact ⟨(isViscSolution_iff ..).2 h1, ⟨χ, (isInnerVarSolution_iff ..).2 h2⟩,
    fun x hx ↦ by
      obtain ⟨r, hr, hsub, hmin⟩ := h3 x hx
      exact ⟨r, hr, hsub, (isDownwardMinimizer_iff ..).2 hmin⟩⟩

theorem challenge_main_largest (d : ℕ) : MainLargestClaim d := by
  intro hd U Q Qmin Qmax hU hb hc hC2 hlip hQmin hQle hQ g hg
  let S : PerronVariational.Setting d :=
    ⟨U, Q, Qmin, Qmax, hd, hU, hb, hc, (hasC2Boundary_iff U).1 hC2, hlip, hQmin, hQle, hQ⟩
  obtain ⟨h1, ⟨χ, h2⟩, h3⟩ :=
    PerronVariational.main_largest d S g ((isStrictSuper_iff U Q g).1 hg)
  rw [perronLargest_eq]
  exact ⟨(isViscSolution_iff ..).2 h1, ⟨χ, (isInnerVarSolution_iff ..).2 h2⟩,
    fun x hx ↦ by
      obtain ⟨r, hr, hsub, hmin⟩ := h3 x hx
      exact ⟨r, hr, hsub, (isUpwardMinimizer_iff ..).2 hmin⟩⟩

theorem challenge_model_example : ModelExampleClaim := by
  obtain ⟨S, gsub, gsuper, hQ, hsub, hpos, hsup, hbd, h1, h2, h3, h4, h5, h6, h0, hlim, hbl, hne⟩ :=
    PerronVariational.TwoDisc.model_example
  rw [hQ] at hsub hsup h1 h2 h3 h4 h5 h6 h0 hlim hbl hne
  exact ⟨S.U, gsub, gsuper, S.isOpen, S.isBounded, S.isConnected, (hasC2Boundary_iff _).2 S.c2,
    ⟨0, (LipschitzWith.const (1 : ℝ)).lipschitzOnWith⟩, (isStrictSub_iff ..).2 hsub, hpos,
    (isStrictSuper_iff ..).2 hsup, hbd, h1, h2, h3, h4, h5, h6, h0, hlim,
    fun v hv ↦ hbl v ((isBlowupLimit_iff ..).1 hv), hne⟩
