/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
import PerronVariational.Stationary.ViscosityJet

/-!
# Basic facts about Perron's method

Elementary facts behind Definition 2.2 and the Perron classes (2.1)–(2.4) of F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981.

* Constants `c ≥ 0` are viscosity supersolutions; hence `max g ∈ 𝒮_g` (the remark after (2.4)).
* The bounds `g₊ ≤ u ≤ max g` for the smallest supersolution and `0 ≤ u ≤ g₊` for the largest
  subsolution (the paper, after (2.4): "`0 ≤ u ≤ max g` in both cases").
* Shifts `g + a`, `|a| ≤ a₀/2`, of smooth strict sub/supersolutions (the remark after
  Definition 2.2).
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Touching in open sets -/

/-- A smooth (`C^∞`) test function is `C²`. -/
theorem contDiff_two_of_smooth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : F → ℝ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ 2 φ :=
  h.of_le (by norm_cast)

/-- In an open set, touching from below is touching on a full neighbourhood. -/
theorem TouchesBelow.eventually_le_of_isOpen {U : Set (E d)} {φ u : E d → ℝ} {x : E d}
    (hU : IsOpen U) (h : TouchesBelow φ u U x) : ∀ᶠ y in 𝓝 x, φ y ≤ u y := by
  have := h.2.2
  rwa [hU.nhdsWithin_eq h.1] at this

/-- In an open set, touching from above is touching on a full neighbourhood. -/
theorem TouchesAbove.eventually_le_of_isOpen {U : Set (E d)} {φ u : E d → ℝ} {x : E d}
    (hU : IsOpen U) (h : TouchesAbove φ u U x) : ∀ᶠ y in 𝓝 x, u y ≤ φ y := by
  have := h.2.2
  rwa [hU.nhdsWithin_eq h.1] at this

/-! ### Constants and nonemptiness of the Perron classes -/

/-- A nonnegative constant is a viscosity supersolution in an open set (the remark after (2.4)). -/
theorem isViscSuper_const {U : Set (E d)} {Q : E d → ℝ} (hU : IsOpen U) {c : ℝ} (hc : 0 ≤ c) :
    IsViscSuper U Q (fun _ ↦ c) := by
  refine ⟨continuousOn_const, fun _ _ ↦ hc, ?_⟩
  intro φ hφ x _ h
  left
  have hmax : IsLocalMax φ x := by
    filter_upwards [h.eventually_le_of_isOpen hU] with y hy
    rw [h.2.1]; exact hy
  exact IsLocalMax.laplacian_nonpos (contDiff_two_of_smooth hφ) hmax

/-- A constant `c ≥ max(g, 0)` on `Ū` belongs to `𝒮_g` (the remark after (2.4): `max g ∈ 𝒮_g`). -/
theorem const_mem_perronSuperClass {U : Set (E d)} {Q g : E d → ℝ} (hU : IsOpen U) {c : ℝ}
    (hc : 0 ≤ c) (hg : ∀ x ∈ closure U, g x ≤ c) :
    (fun _ ↦ c) ∈ perronSuperClass U Q g :=
  ⟨continuousOn_const, isViscSuper_const hU hc, fun x hx ↦ max_le (hg x hx) hc⟩

/-- `𝒮_g` is nonempty as soon as `g` is bounded above on `Ū` (the remark after (2.4)). -/
theorem perronSuperClass_nonempty {U : Set (E d)} {Q g : E d → ℝ} (hU : IsOpen U)
    (hg : BddAbove (g '' closure U)) : (perronSuperClass U Q g).Nonempty := by
  obtain ⟨c, hc⟩ := hg
  exact ⟨_, const_mem_perronSuperClass (c := max c 0) hU (le_max_right _ _)
    fun x hx ↦ (hc ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩

/-- In the standing setting, `𝒮_g` is nonempty for every `g` continuous on `Ū`. -/
theorem Setting.perronSuperClass_nonempty (S : Setting d) {g : E d → ℝ}
    (hg : ContinuousOn g (closure S.U)) : (perronSuperClass S.U S.Q g).Nonempty :=
  PerronVariational.perronSuperClass_nonempty S.isOpen
    (S.isBounded.isCompact_closure.bddAbove_image hg)

/-- `𝒮^g` is nonempty: it contains `0` (the remark after (2.4)). -/
theorem perronSubClass_nonempty (U : Set (E d)) (Q g : E d → ℝ) :
    (perronSubClass U Q g).Nonempty :=
  ⟨0, zero_mem_perronSubClass U Q g⟩

/-! ### Bounds for the smallest supersolution -/

section Smallest

variable {U : Set (E d)} {Q g : E d → ℝ} {x : E d}

theorem bddBelow_perronSuperClass_image (hx : x ∈ closure U) :
    BddBelow ((fun v ↦ v x) '' perronSuperClass U Q g) :=
  ⟨max (g x) 0, by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 x hx⟩

/-- `u ≤ v` on `Ū` for every `v ∈ 𝒮_g`. -/
theorem perronSmallest_le {v : E d → ℝ} (hv : v ∈ perronSuperClass U Q g)
    (hx : x ∈ closure U) : perronSmallest U Q g x ≤ v x :=
  csInf_le (bddBelow_perronSuperClass_image hx) ⟨v, hv, rfl⟩

/-- `g₊ ≤ u` on `Ū` (when `𝒮_g ≠ ∅`). -/
theorem le_perronSmallest (hne : (perronSuperClass U Q g).Nonempty) (hx : x ∈ closure U) :
    max (g x) 0 ≤ perronSmallest U Q g x :=
  le_csInf (hne.image _) (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 x hx)

/-- `g ≤ u` on `Ū` (when `𝒮_g ≠ ∅`). -/
theorem le_perronSmallest' (hne : (perronSuperClass U Q g).Nonempty) (hx : x ∈ closure U) :
    g x ≤ perronSmallest U Q g x :=
  (le_max_left _ _).trans (le_perronSmallest hne hx)

/-- `0 ≤ u` on `Ū` (when `𝒮_g ≠ ∅`) (the remark after (2.4)). -/
theorem perronSmallest_nonneg (hne : (perronSuperClass U Q g).Nonempty) (hx : x ∈ closure U) :
    0 ≤ perronSmallest U Q g x :=
  (le_max_right _ _).trans (le_perronSmallest hne hx)

/-- `u ≤ c` whenever `0 ≤ c` and `g ≤ c` on `Ū`; in particular `u ≤ max g`
(the remark after (2.4)). -/
theorem perronSmallest_le_const (hU : IsOpen U) {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ y ∈ closure U, g y ≤ c) (hx : x ∈ closure U) : perronSmallest U Q g x ≤ c :=
  perronSmallest_le (const_mem_perronSuperClass hU hc hg) hx

end Smallest

/-! ### Bounds for the largest subsolution -/

section Largest

variable {U : Set (E d)} {Q g : E d → ℝ} {x : E d}

theorem bddAbove_perronSubClass_image (hx : x ∈ closure U) :
    BddAbove ((fun v ↦ v x) '' perronSubClass U Q g) :=
  ⟨max (g x) 0, by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 x hx⟩

/-- `v ≤ u` on `Ū` for every `v ∈ 𝒮^g`. -/
theorem le_perronLargest {v : E d → ℝ} (hv : v ∈ perronSubClass U Q g) (hx : x ∈ closure U) :
    v x ≤ perronLargest U Q g x :=
  le_csSup (bddAbove_perronSubClass_image hx) ⟨v, hv, rfl⟩

/-- `u ≤ g₊` on `Ū`. -/
theorem perronLargest_le (hx : x ∈ closure U) : perronLargest U Q g x ≤ max (g x) 0 :=
  csSup_le ((perronSubClass_nonempty U Q g).image _)
    (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 x hx)

/-- `0 ≤ u` on `Ū` (the remark after (2.4)). -/
theorem perronLargest_nonneg (hx : x ∈ closure U) : 0 ≤ perronLargest U Q g x :=
  le_perronLargest (zero_mem_perronSubClass U Q g) hx

/-- `u ≤ c` whenever `0 ≤ c` and `g ≤ c` on `Ū`; in particular `u ≤ max g`
(the remark after (2.4)). -/
theorem perronLargest_le_const {c : ℝ} (hc : 0 ≤ c) (hg : ∀ y ∈ closure U, g y ≤ c)
    (hx : x ∈ closure U) : perronLargest U Q g x ≤ c :=
  (perronLargest_le hx).trans (max_le (hg x hx) hc)

end Largest

/-! ### Shifts of strict sub/supersolutions (the remark after Definition 2.2) -/

/-- `g` is a smooth strict subsolution (Definition 2.2) with the explicit constants `a₀, δ₀`. -/
def IsStrictSubWith (U : Set (E d)) (Q g : E d → ℝ) (a₀ δ₀ : ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ 0 < a₀ ∧ 0 < δ₀ ∧
    (∀ x ∈ closure U, -a₀ < g x → 0 ≤ Δ g x) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → (1 + δ₀) * Q x ^ 2 ≤ ‖∇ g x‖ ^ 2

/-- `g` is a smooth strict supersolution (Definition 2.2) with the explicit constants `a₀, δ₀`. -/
def IsStrictSuperWith (U : Set (E d)) (Q g : E d → ℝ) (a₀ δ₀ : ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ 0 < a₀ ∧ 0 < δ₀ ∧
    (∀ x ∈ closure U, -a₀ < g x → Δ g x ≤ 0) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → ‖∇ g x‖ ^ 2 ≤ (1 - δ₀) * Q x ^ 2

theorem isStrictSub_iff {U : Set (E d)} {Q g : E d → ℝ} :
    IsStrictSub U Q g ↔ ∃ a₀ δ₀, IsStrictSubWith U Q g a₀ δ₀ := by
  constructor
  · rintro ⟨hg, a₀, ha₀, δ₀, hδ₀, h1, h2⟩; exact ⟨a₀, δ₀, hg, ha₀, hδ₀, h1, h2⟩
  · rintro ⟨a₀, δ₀, hg, ha₀, hδ₀, h1, h2⟩; exact ⟨hg, a₀, ha₀, δ₀, hδ₀, h1, h2⟩

theorem isStrictSuper_iff {U : Set (E d)} {Q g : E d → ℝ} :
    IsStrictSuper U Q g ↔ ∃ a₀ δ₀, IsStrictSuperWith U Q g a₀ δ₀ := by
  constructor
  · rintro ⟨hg, a₀, ha₀, δ₀, hδ₀, h1, h2⟩; exact ⟨a₀, δ₀, hg, ha₀, hδ₀, h1, h2⟩
  · rintro ⟨a₀, δ₀, hg, ha₀, hδ₀, h1, h2⟩; exact ⟨hg, a₀, ha₀, δ₀, hδ₀, h1, h2⟩

/-- The remark after Definition 2.2: for `|a| ≤ a₀/2`, the shift `g + a` of a strict
subsolution is a strict subsolution with `a₀` replaced by `a₀/2` and the same `δ₀`. -/
theorem IsStrictSubWith.add_const {U : Set (E d)} {Q g : E d → ℝ} {a₀ δ₀ : ℝ}
    (h : IsStrictSubWith U Q g a₀ δ₀) {a : ℝ} (ha : |a| ≤ a₀ / 2) :
    IsStrictSubWith U Q (fun x ↦ g x + a) (a₀ / 2) δ₀ := by
  obtain ⟨hg, ha₀, hδ₀, h1, h2⟩ := h
  have hab := abs_le.1 ha
  refine ⟨hg.add contDiff_const, half_pos ha₀, hδ₀, fun x hx hgx ↦ ?_, fun x hx hgx ↦ ?_⟩
  · rw [laplacian_add_const hg.contDiffAt]
    exact h1 x hx (by linarith)
  · rw [gradient_add_const]
    refine h2 x hx ?_
    have := abs_le.1 hgx
    rw [abs_le]; constructor <;> linarith

/-- The remark after Definition 2.2: for `|a| ≤ a₀/2`, the shift `g + a` of a strict
supersolution is a strict supersolution with `a₀` replaced by `a₀/2` and the same `δ₀`. -/
theorem IsStrictSuperWith.add_const {U : Set (E d)} {Q g : E d → ℝ} {a₀ δ₀ : ℝ}
    (h : IsStrictSuperWith U Q g a₀ δ₀) {a : ℝ} (ha : |a| ≤ a₀ / 2) :
    IsStrictSuperWith U Q (fun x ↦ g x + a) (a₀ / 2) δ₀ := by
  obtain ⟨hg, ha₀, hδ₀, h1, h2⟩ := h
  have hab := abs_le.1 ha
  refine ⟨hg.add contDiff_const, half_pos ha₀, hδ₀, fun x hx hgx ↦ ?_, fun x hx hgx ↦ ?_⟩
  · rw [laplacian_add_const hg.contDiffAt]
    exact h1 x hx (by linarith)
  · rw [gradient_add_const]
    refine h2 x hx ?_
    have := abs_le.1 hgx
    rw [abs_le]; constructor <;> linarith

/-- Shifts of a strict subsolution by small constants are strict subsolutions (the remark
after Definition 2.2). -/
theorem IsStrictSub.exists_add_const {U : Set (E d)} {Q g : E d → ℝ} (h : IsStrictSub U Q g) :
    ∃ a₀ > 0, ∀ a : ℝ, |a| ≤ a₀ / 2 → IsStrictSub U Q (fun x ↦ g x + a) := by
  obtain ⟨a₀, δ₀, hw⟩ := isStrictSub_iff.1 h
  exact ⟨a₀, hw.2.1, fun a ha ↦ isStrictSub_iff.2 ⟨_, _, hw.add_const ha⟩⟩

/-- Shifts of a strict supersolution by small constants are strict supersolutions
(the remark after Definition 2.2). -/
theorem IsStrictSuper.exists_add_const {U : Set (E d)} {Q g : E d → ℝ}
    (h : IsStrictSuper U Q g) :
    ∃ a₀ > 0, ∀ a : ℝ, |a| ≤ a₀ / 2 → IsStrictSuper U Q (fun x ↦ g x + a) := by
  obtain ⟨a₀, δ₀, hw⟩ := isStrictSuper_iff.1 h
  exact ⟨a₀, hw.2.1, fun a ha ↦ isStrictSuper_iff.2 ⟨_, _, hw.add_const ha⟩⟩

end PerronVariational

end
