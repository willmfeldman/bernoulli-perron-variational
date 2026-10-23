module

public import Vocabulary
public import PerronVariational

/-!
# Solution: [Theorem 1.1](#AFS:t.main), [Corollary 1.2](#AFS:c.2d-structure), necklace example

The trusted vocabulary of `Vocabulary.lean` is reconciled with the library's, then the library
theorems `PerronVariational.main_smallest`, `PerronVariational.main_largest`,
`PerronVariational.corollary_2d_smallest`, `PerronVariational.corollary_2d_largest` and
`PerronVariational.Necklace.necklace_example` are applied.

* `HasC2Boundary`, `IsStrictSub`, `IsStrictSuper`, `perronSmallest`, `perronLargest`,
  `freeBoundary`, `IsViscSolution`, `IsDownwardMinimizer` and `IsUpwardMinimizer` are
  definitionally the library's.
* `IsInnerVarSolution` has the same fields as the library's structure (`isInnerVarSolution_iff`);
  its integrand `innerVarIntegrand` is definitionally the library's.
* `blowup`, `IsBlowupLimit` and `IsClassicalNear` are definitionally the library's.
* The unbundled hypotheses on `U` and `Q` are packed into the library's `Setting d` (for
  [Corollary 1.2](#AFS:c.2d-structure), `Setting 2`, whose field `2 ≤ 2` is discharged by `le_rfl`).
* `MemH1`, `MemH10` and `IsDirichletEnergyMinimizer` are definitionally the library's (`MemH1` is
  gmt-foundations' `GMTFoundations.MemH1`, re-exported by the library), and so is `energyJ`.
* The necklace example: the library theorem `PerronVariational.Necklace.necklace_example` applies
  after unpacking its `Setting`: the domain is `B₄(0)` minus `100` closed discs of radius `1/20`
  centred on the circle of radius `(1/10) / sin (π / 100)`, with `Q ≡ 1`.
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

theorem isClassicalNear_iff (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) :
    IsClassicalNear U Q u x₀ ↔ PerronVariational.IsClassicalNear U Q u x₀ := Iff.rfl

theorem isBlowupLimit_iff (u : E d → ℝ) (x₀ : E d) (v : E d → ℝ) :
    IsBlowupLimit u x₀ v ↔ PerronVariational.IsBlowupLimit u x₀ v := Iff.rfl

theorem memH1_iff (U : Set (E d)) (u : E d → ℝ) (G : E d → E d) :
    MemH1 U u G ↔ PerronVariational.MemH1 U u G := Iff.rfl

theorem memH10_iff (U : Set (E d)) (w : E d → ℝ) :
    MemH10 U w ↔ PerronVariational.MemH10 U w := Iff.rfl

theorem energyJ_eq (V : Set (E d)) (Q u : E d → ℝ) (G : E d → E d) :
    energyJ V Q u G = PerronVariational.energyJ V Q u G := rfl

theorem isDirichletEnergyMinimizer_iff (U : Set (E d)) (Q g u : E d → ℝ) :
    IsDirichletEnergyMinimizer U Q g u ↔ PerronVariational.IsDirichletEnergyMinimizer U Q g u :=
  Iff.rfl

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

theorem challenge_necklace_example : NecklaceExampleClaim := by
  obtain ⟨S, gsub, gsuper, hQ, hsub, hpos, hsup, hbd, h1, h2, h3, h4, h5, h6, ⟨x₀, hx₀, e, he, hlim,
    hbl⟩, hne, hex, hmin⟩ := PerronVariational.Necklace.necklace_example
  rw [hQ] at hsub hsup h1 h2 h3 h4 h5 h6 hx₀ hlim hbl hne hex hmin
  exact ⟨S.U, gsub, gsuper, S.isOpen, S.isBounded, S.isConnected, (hasC2Boundary_iff _).2 S.c2,
    ⟨0, (LipschitzWith.const (1 : ℝ)).lipschitzOnWith⟩, (isStrictSub_iff ..).2 hsub, hpos,
    (isStrictSuper_iff ..).2 hsup, hbd, h1, h2, h3, h4, h5, h6,
    ⟨x₀, hx₀, e, he, hlim, fun v hv ↦ hbl v ((isBlowupLimit_iff ..).1 hv)⟩, hne,
    hex.imp fun u hu ↦ (isDirichletEnergyMinimizer_iff ..).2 hu,
    fun u hu ↦ hmin u ((isDirichletEnergyMinimizer_iff ..).1 hu)⟩
