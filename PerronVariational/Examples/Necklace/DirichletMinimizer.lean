/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.Statement
public import PerronVariational.Foundations.Bridge
import EllipticBernoulli.Sobolev.ZeroExtension
import EllipticBernoulli.Sobolev.Energy
import EllipticBernoulli.Variational.Existence
import GMTFoundations.Sobolev.Lipschitz
import GMTFoundations.Sobolev.Lattice

/-!
# Minimizers of the Alt–Caffarelli energy with Dirichlet data

General facts about `IsDirichletEnergyMinimizer U Q g u` (minimize `J_Q(·; U)` among
`v ∈ H¹(U)` with `v - g ∈ H¹₀(U)`), used for the necklace example (`[AFS]`,
[Figure 1](#AFS:f.necklace)) of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of
Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 (`[AFS]`). Nothing
here depends on the example.

* `IsDirichletEnergyMinimizer.congr_ae`: the property only depends on `u` a.e. in `U`.
* `IsDirichletEnergyMinimizer.energyJ_le`: the minimality, for any weak gradient of `u`.
* `IsDirichletEnergyMinimizer.energyJ_ball_le`: a minimizer minimizes `J_Q(·; B)` on every ball
  `B ⊂⊂ U` among `v ∈ H¹_loc(U)` with `v = u` a.e. on `U \ B`. The competitor `v` is admissible
  for the global problem: `v - u` vanishes a.e. off the compact set `B̄ ⊆ U`, so its zero extension
  is in `H¹(ℝᵈ)`; and the energies on `U \ B` agree (Stampacchia's lemma), and are finite when
  `|U| < ∞` and `Q` is bounded.
* `IsDirichletEnergyMinimizer.isUpwardMinimizer`, `.isDownwardMinimizer`: hence, if `{u > 0}` is
  open and `u` is harmonic there, `u` is an upward and a downward minimizer in `U`
  ([AFS, [Definition 2.15](#AFS:d.directional)]).
* `exists_isDirichletEnergyMinimizer`: existence on bounded open sets for `C¹` data `g` and bounded
  measurable `Q`, from the existence theorem for the obstacle problem of
  elliptic-bernoulli-foundations (`EllipticBernoulli.exists_isObstacleMinimizer`), applied in
  `ℝᵈ` on a ball containing `U`, with the constraint `w = g` off `U`.
* `IsDirichletEnergyMinimizer.not_ae_eq_of_energyJ_lt`: for `Q ≡ 1`, a minimizer is not a.e. equal
  to a function `w` whose positivity set has measure larger than the energy of some admissible
  competitor.
-/

open Set Filter Topology Metric MeasureTheory
open scoped ENNReal Gradient Laplacian

@[expose] public noncomputable section

namespace PerronVariational

open Foundations

variable {d : ℕ}

/-! ### Energy lemmas of elliptic-bernoulli-foundations, in this library's vocabulary -/

theorem energyJ_congr' {V : Set (E d)} {Q f₁ f₂ : E d → ℝ} {G₁ G₂ : E d → E d}
    (hf : EqOn f₁ f₂ V) (hG : ∀ᵐ x ∂(volume.restrict V), G₁ x = G₂ x) :
    energyJ V Q f₁ G₁ = energyJ V Q f₂ G₂ :=
  EllipticBernoulli.energyJ_congr hf hG

theorem energyJ_congr_ae' {V : Set (E d)} (hV : MeasurableSet V) {Q f₁ f₂ : E d → ℝ}
    {G₁ G₂ : E d → E d} (hf : ∀ᵐ x ∂(volume.restrict V), f₁ x = f₂ x)
    (hG : ∀ᵐ x ∂(volume.restrict V), G₁ x = G₂ x) :
    energyJ V Q f₁ G₁ = energyJ V Q f₂ G₂ :=
  EllipticBernoulli.energyJ_congr_ae hV hf hG

theorem energyJ_split' {B B' : Set (E d)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hBB' : B ⊆ B') (Q f : E d → ℝ) (G : E d → E d) :
    energyJ B' Q f G = energyJ B Q f G + energyJ (B' \ B) Q f G :=
  EllipticBernoulli.energyJ_split hB hB' hBB' Q f G

theorem energyJ_eq_add' {V : Set (E d)} (Q v : E d → ℝ) {G : E d → E d}
    (hG : AEStronglyMeasurable G (volume.restrict V)) :
    energyJ V Q v G = (∫⁻ x in V, ENNReal.ofReal (‖G x‖ ^ 2)) +
      ∫⁻ x in V, ENNReal.ofReal (Q x ^ 2 * (posSet v V).indicator 1 x) :=
  EllipticBernoulli.energyJ_eq_add Q v hG

theorem energyJ_lt_top' {U B : Set (E d)} {Q v : E d → ℝ} {G : E d → E d} (hv : MemH1Loc U v G)
    (hBc : IsCompact (closure B)) (hBU : closure B ⊆ U) {CQ : ℝ} (hQ : ∀ x ∈ B, |Q x| ≤ CQ) :
    energyJ B Q v G < ⊤ :=
  EllipticBernoulli.energyJ_lt_top hv hBc hBU hQ

/-! ### Sobolev helpers -/

/-- A weak gradient restricts to subsets. -/
theorem hasWeakGradient_mono_set {U W : Set (E d)} {f : E d → ℝ} {G : E d → E d}
    (hf : HasWeakGradient U f G) (hWU : W ⊆ U) : HasWeakGradient W f G :=
  GMTFoundations.HasWeakGradient.of_integral_eq (hf.1.mono_set hWU) (hf.2.1.mono_set hWU)
    fun _ hφ hφc hφW v ↦ hf.integral_eq hφ hφc (hφW.trans hWU) v

theorem memH1Loc_of_memH1 {U : Set (E d)} {f : E d → ℝ} {G : E d → E d} (hf : MemH1 U f G) :
    MemH1Loc U f G :=
  ⟨hf.2.2, fun _ hK _ ↦ ⟨hf.1.mono_measure (Measure.restrict_mono hK le_rfl),
    hf.2.1.mono_measure (Measure.restrict_mono hK le_rfl)⟩⟩

/-- A function in `L²(S)` vanishing a.e. off `S` is in `L²(ℝᵈ)`. -/
theorem memLp_two_of_ae_eq_zero_off {F : Type*} [NormedAddCommGroup F] {S : Set (E d)}
    (hS : MeasurableSet S) {f : E d → F} (hf : MemLp f 2 (volume.restrict S))
    (h0 : ∀ᵐ x, x ∉ S → f x = 0) : MemLp f 2 volume := by
  refine ((memLp_indicator_iff_restrict hS).2 hf).ae_eq ?_
  filter_upwards [h0] with x hx
  by_cases hxS : x ∈ S
  · rw [indicator_of_mem hxS]
  · rw [indicator_of_notMem hxS, hx hxS]

theorem memH1_univ_iff {f : E d → ℝ} {G : E d → E d} :
    MemH1 univ f G ↔ MemLp f 2 volume ∧ MemLp G 2 volume ∧ HasWeakGradient univ f G := by
  unfold MemH1; rw [Measure.restrict_univ]

/-- `MemH1 univ` is invariant under a.e. changes of the function. -/
theorem memH1_univ_congr_ae {f f' : E d → ℝ} {G : E d → E d} (hf : MemH1 univ f G)
    (hff' : f =ᵐ[volume] f') : MemH1 univ f' G := by
  have h' : f =ᵐ[volume.restrict univ] f' := by rwa [Measure.restrict_univ]
  rw [memH1_univ_iff] at hf ⊢
  exact ⟨hf.1.ae_eq hff', hf.2.1, GMTFoundations.HasWeakGradient.congr_fun_ae hf.2.2 h'⟩

/-- `H¹₀(U)` is closed under addition. -/
theorem MemH10.add {U : Set (E d)} {a b : E d → ℝ} (ha : MemH10 U a) (hb : MemH10 U b) :
    MemH10 U (fun x ↦ a x + b x) := by
  obtain ⟨Ha, hHa⟩ := ha
  obtain ⟨Hb, hHb⟩ := hb
  refine ⟨fun x ↦ Ha x + Hb x, ?_⟩
  have hind : U.indicator (fun x ↦ a x + b x) = fun x ↦ U.indicator a x + U.indicator b x := by
    funext x; by_cases hx : x ∈ U <;> simp [hx]
  rw [hind]
  exact ⟨hHa.1.add hHb.1, hHa.2.1.add hHb.2.1,
    GMTFoundations.HasWeakGradient.add hHa.2.2 hHb.2.2⟩

/-- `H¹₀(U)` only sees functions a.e. in `U`. -/
theorem MemH10.congr_ae {U : Set (E d)} (hU : MeasurableSet U) {a b : E d → ℝ}
    (ha : MemH10 U a) (hab : a =ᵐ[volume.restrict U] b) : MemH10 U b := by
  obtain ⟨H, hH⟩ := ha
  refine ⟨H, memH1_univ_congr_ae hH ?_⟩
  filter_upwards [(ae_restrict_iff' hU).1 hab] with x hx
  by_cases hxU : x ∈ U
  · rw [indicator_of_mem hxU, indicator_of_mem hxU, hx hxU]
  · rw [indicator_of_notMem hxU, indicator_of_notMem hxU]

/-- **Zero extension.** A function `w ∈ H¹_loc(U)` vanishing a.e. off a compact `K ⊆ U` is in
`H¹₀(U)`, with whole-space weak gradient the zero extension of its gradient. -/
theorem memH1_univ_indicator_of_ae_eq_zero {U K : Set (E d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {w : E d → ℝ} {G : E d → E d} (hw : MemH1Loc U w G)
    (h0 : ∀ᵐ x ∂(volume.restrict (U \ K)), w x = 0) :
    MemH1 univ (U.indicator w) (U.indicator G) := by
  have hG0 : ∀ᵐ x ∂(volume.restrict (U \ K)), G x = 0 :=
    EllipticBernoulli.HasWeakGradient.ae_eq_zero_of_ae_eq_zero_on (memH1Loc_iff_eb.1 hw).1
      (hU.sdiff hK.isClosed) sdiff_subset h0
  have hUK : MeasurableSet (U \ K) := hU.measurableSet.diff hK.measurableSet
  rw [ae_restrict_iff' hUK] at h0 hG0
  obtain ⟨hwK, hGK⟩ := hw.2 K hKU hK
  refine memH1_univ_iff.2 ⟨memLp_two_of_ae_eq_zero_off hK.measurableSet ?_ ?_,
    memLp_two_of_ae_eq_zero_off hK.measurableSet ?_ ?_,
    hasWeakGradient_iff_eb.2 (EllipticBernoulli.HasWeakGradient.univ_of_ae_eq_zero hU
      (memH1Loc_iff_eb.1 hw).1 hK hKU (by rw [ae_restrict_iff' hUK]; exact h0))⟩
  · exact hwK.ae_eq ((ae_restrict_iff' hK.measurableSet).2
      (Eventually.of_forall fun x hx ↦ (indicator_of_mem (hKU hx) _).symm))
  · filter_upwards [h0] with x hx hxK
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU, hx ⟨hxU, hxK⟩]
    · rw [indicator_of_notMem hxU]
  · exact hGK.ae_eq ((ae_restrict_iff' hK.measurableSet).2
      (Eventually.of_forall fun x hx ↦ (indicator_of_mem (hKU hx) _).symm))
  · filter_upwards [hG0] with x hx hxK
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU, hx ⟨hxU, hxK⟩]
    · rw [indicator_of_notMem hxU]

/-- The positivity set of a function continuous on an open set is open. -/
theorem isOpen_posSet_of_continuousOn {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hu : ContinuousOn u U) : IsOpen (posSet u U) :=
  hu.isOpen_inter_preimage hU isOpen_Ioi

/-! ### Energy helpers -/

/-- `J_Q(u; V) < ∞` if `∇u ∈ L²(V)`, `|V| < ∞` and `Q` is bounded on `V`. -/
theorem energyJ_lt_top_of_memLp {V : Set (E d)} (hV : MeasurableSet V) (hVfin : volume V ≠ ∞)
    {Q u : E d → ℝ} {G : E d → E d} (hG : MemLp G 2 (volume.restrict V)) {C : ℝ}
    (hQ : ∀ x ∈ V, |Q x| ≤ C) : energyJ V Q u G < ∞ := by
  rw [energyJ_eq_add' Q u hG.aestronglyMeasurable]
  refine ENNReal.add_lt_top.2 ⟨hG.norm.integrable_sq.lintegral_lt_top, ?_⟩
  calc ∫⁻ x in V, ENNReal.ofReal (Q x ^ 2 * (posSet u V).indicator 1 x)
      ≤ ∫⁻ _ in V, ENNReal.ofReal (C ^ 2) := by
        refine setLIntegral_mono' hV fun x hx ↦ ENNReal.ofReal_le_ofReal ?_
        have hQ2 : Q x ^ 2 ≤ C ^ 2 := sq_le_sq' (abs_le.1 (hQ x hx)).1 (abs_le.1 (hQ x hx)).2
        by_cases hp : x ∈ posSet u V
        · rw [indicator_of_mem hp]; simpa using hQ2
        · rw [indicator_of_notMem hp]; simp [sq_nonneg]
    _ = ENNReal.ofReal (C ^ 2) * volume V := by rw [setLIntegral_const]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVfin.lt_top

/-- For `Q ≡ 1`, `|{u > 0} ∩ V| ≤ J_1(u; V)` when the positivity set is measurable. -/
theorem volume_posSet_le_energyJ {V : Set (E d)} {u : E d → ℝ} (hP : MeasurableSet (posSet u V))
    (G : E d → E d) : volume (posSet u V) ≤ energyJ V (fun _ ↦ 1) u G := by
  have hPV : posSet u V ⊆ V := fun x hx ↦ hx.1
  calc volume (posSet u V) = ∫⁻ x in V, (posSet u V).indicator 1 x := by
        rw [lintegral_indicator_one hP, Measure.restrict_apply hP, inter_eq_left.2 hPV]
    _ ≤ energyJ V (fun _ ↦ 1) u G := by
        refine lintegral_mono fun x ↦ ?_
        by_cases hp : x ∈ posSet u V
        · simp only [indicator_of_mem hp, Pi.one_apply, one_pow, one_mul]
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg ‖G x‖])
        · simp [indicator_of_notMem hp]

/-! ### Basic properties of Dirichlet minimizers -/

/-- The minimality, with an arbitrary weak gradient of `u`. -/
theorem IsDirichletEnergyMinimizer.energyJ_le {U : Set (E d)} (hU : IsOpen U) {Q g u : E d → ℝ}
    (hmin : IsDirichletEnergyMinimizer U Q g u) {Gu : E d → E d} (hu : MemH1 U u Gu)
    {v : E d → ℝ} {Gv : E d → E d} (hv : MemH1 U v Gv) (hvg : MemH10 U (v - g)) :
    energyJ U Q u Gu ≤ energyJ U Q v Gv := by
  obtain ⟨G₀, hu₀, -, hle⟩ := hmin
  have hG : ∀ᵐ x ∂(volume.restrict U), Gu x = G₀ x :=
    EllipticBernoulli.HasWeakGradient.ae_eq_of_eqOn hU hU subset_rfl hu.2.2 hu₀.2.2
      fun _ _ ↦ rfl
  rw [energyJ_congr' (fun _ _ ↦ rfl) hG]
  exact hle v Gv hv hvg

/-- **a.e. invariance.** Being a Dirichlet minimizer only depends on `u` a.e. in `U`. -/
theorem IsDirichletEnergyMinimizer.congr_ae {U : Set (E d)} (hU : MeasurableSet U)
    {Q g u u' : E d → ℝ} (hmin : IsDirichletEnergyMinimizer U Q g u)
    (huu' : u =ᵐ[volume.restrict U] u') : IsDirichletEnergyMinimizer U Q g u' := by
  obtain ⟨Gu, hu, hug, hle⟩ := hmin
  refine ⟨Gu, ⟨hu.1.ae_eq huu', hu.2.1, GMTFoundations.HasWeakGradient.congr_fun_ae hu.2.2 huu'⟩,
    hug.congr_ae hU ?_, fun v Gv hv hvg ↦ ?_⟩
  · filter_upwards [huu'] with x hx
    simp [hx]
  · rw [← energyJ_congr_ae' hU huu' (ae_of_all _ fun _ ↦ rfl)]
    exact hle v Gv hv hvg

/-! ### Local minimality on balls -/

/-- **A Dirichlet minimizer minimizes on balls.** Let `U` be open with `|U| < ∞` and `Q` bounded
on `U`. If `u` is a Dirichlet minimizer of `J_Q(·; U)`, then for every ball `B = ball x r` with
`B̄ ⊆ U` and every `v ∈ H¹_loc(U)` with `v = u` a.e. on `U \ B`, `J_Q(u; B) ≤ J_Q(v; B)`. -/
theorem IsDirichletEnergyMinimizer.energyJ_ball_le {U : Set (E d)} (hU : IsOpen U)
    (hUfin : volume U ≠ ∞) {Q g u : E d → ℝ} {C : ℝ} (hQ : ∀ x ∈ U, |Q x| ≤ C)
    (hmin : IsDirichletEnergyMinimizer U Q g u) {x : E d} {r : ℝ} (hB : closedBall x r ⊆ U)
    {v : E d → ℝ} {Gu Gv : E d → E d} (hu : MemH1Loc U u Gu)
    (hv : MemH1Loc U v Gv) (hvu : ∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) :
    energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv := by
  obtain ⟨G₀, hu₀, hug, hle⟩ := hmin
  have hBU : ball x r ⊆ U := ball_subset_closedBall.trans hB
  have hUm : MeasurableSet U := hU.measurableSet
  have hDm : MeasurableSet (U \ ball x r) := hUm.diff measurableSet_ball
  -- the difference `w = v - u` and its zero extension
  set w : E d → ℝ := fun y ↦ v y - u y with hw
  set Gw : E d → E d := fun y ↦ Gv y - G₀ y with hGw
  have hwL : MemH1Loc U w Gw := hv.sub (memH1Loc_of_memH1 hu₀)
  have hw0 : ∀ᵐ y ∂(volume.restrict (U \ ball x r)), w y = 0 := by
    filter_upwards [hvu] with y hy
    simp [hw, hy]
  have hext : MemH1 univ (U.indicator w) (U.indicator Gw) :=
    memH1_univ_indicator_of_ae_eq_zero hU (isCompact_closedBall x r) hB hwL
      (ae_restrict_of_ae_restrict_of_subset (sdiff_subset_sdiff_right ball_subset_closedBall) hw0)
  have hextU : MemH1 U (U.indicator w) (U.indicator Gw) := by
    rw [memH1_univ_iff] at hext
    exact ⟨hext.1.restrict U, hext.2.1.restrict U,
      hasWeakGradient_mono_set hext.2.2 (subset_univ U)⟩
  -- `v` is an admissible competitor
  have hvU : ∀ y ∈ U, v y = u y + U.indicator w y := fun y hy ↦ by
    rw [indicator_of_mem hy]; ring
  have hGvU : ∀ y ∈ U, Gv y = G₀ y + U.indicator Gw y := fun y hy ↦ by
    rw [indicator_of_mem hy]; simp [hGw]
  have hv1 : MemH1 U v Gv := by
    refine ⟨(hu₀.1.add hextU.1).ae_eq ?_, (hu₀.2.1.add hextU.2.1).ae_eq ?_, hv.1⟩
    · exact (ae_restrict_iff' hUm).2 (Eventually.of_forall fun y hy ↦ (hvU y hy).symm)
    · exact (ae_restrict_iff' hUm).2 (Eventually.of_forall fun y hy ↦ (hGvU y hy).symm)
  have hvg : MemH10 U (v - g) := by
    have h := hug.add ⟨_, hext⟩
    refine h.congr_ae hUm ((ae_restrict_iff' hUm).2 (Eventually.of_forall fun y hy ↦ ?_))
    simp only [Pi.sub_apply, hw]
    ring
  have hJ := hle v Gv hv1 hvg
  -- split off `U \ B`, where the two energies agree and are finite
  rw [energyJ_split' measurableSet_ball hUm hBU,
    energyJ_split' measurableSet_ball hUm hBU] at hJ
  have hGeq : ∀ᵐ y ∂(volume.restrict (U \ ball x r)), Gv y = G₀ y := by
    have hst := EllipticBernoulli.HasWeakGradient.ae_eq_zero_of_eq_zero hU
      (memH1Loc_iff_eb.1 hwL).1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset hst, hw0] with y h1 h2
    exact sub_eq_zero.1 (h1 h2)
  have hout : energyJ (U \ ball x r) Q v Gv = energyJ (U \ ball x r) Q u G₀ :=
    energyJ_congr_ae' hDm hvu hGeq
  have hfin : energyJ (U \ ball x r) Q u G₀ ≠ ∞ :=
    (energyJ_lt_top_of_memLp hDm (measure_ne_top_of_subset sdiff_subset hUfin)
      (hu₀.2.1.mono_measure (Measure.restrict_mono sdiff_subset le_rfl))
      fun y hy ↦ hQ y hy.1).ne
  rw [hout, ENNReal.add_le_add_iff_right hfin] at hJ
  have hG : ∀ᵐ y ∂(volume.restrict (ball x r)), Gu y = G₀ y :=
    ae_restrict_of_ae_restrict_of_subset hBU
      (EllipticBernoulli.HasWeakGradient.ae_eq_of_eqOn hU hU subset_rfl hu.1 hu₀.2.2
        fun _ _ ↦ rfl)
  rwa [energyJ_congr' (fun _ _ ↦ rfl) hG]

/-- A Dirichlet minimizer whose positivity set is open and on which it is harmonic is an upward
minimizer ([AFS, [Definition 2.15](#AFS:d.directional)]) in `U`. -/
theorem IsDirichletEnergyMinimizer.isUpwardMinimizer {U : Set (E d)} (hU : IsOpen U)
    (hUfin : volume U ≠ ∞) {Q g u : E d → ℝ} {C : ℝ} (hQ : ∀ x ∈ U, |Q x| ≤ C)
    (hmin : IsDirichletEnergyMinimizer U Q g u) (hpos : IsOpen (posSet u U))
    (hc2 : ContDiffOn ℝ 2 u (posSet u U)) (hharm : ∀ x ∈ posSet u U, Δ u x = 0) :
    IsUpwardMinimizer U Q u := by
  obtain ⟨G₀, hu₀, -⟩ := id hmin
  exact ⟨⟨G₀, memH1Loc_of_memH1 hu₀⟩, hpos, hc2, hharm, fun _ _ _ hB _ _ _ hu hv _ hvu ↦
    hmin.energyJ_ball_le hU hUfin hQ hB hu hv hvu⟩

/-- A Dirichlet minimizer whose positivity set is open and on which it is harmonic is a downward
minimizer ([AFS, [Definition 2.15](#AFS:d.directional)]) in `U`. -/
theorem IsDirichletEnergyMinimizer.isDownwardMinimizer {U : Set (E d)} (hU : IsOpen U)
    (hUfin : volume U ≠ ∞) {Q g u : E d → ℝ} {C : ℝ} (hQ : ∀ x ∈ U, |Q x| ≤ C)
    (hmin : IsDirichletEnergyMinimizer U Q g u) (hpos : IsOpen (posSet u U))
    (hc2 : ContDiffOn ℝ 2 u (posSet u U)) (hharm : ∀ x ∈ posSet u U, Δ u x = 0) :
    IsDownwardMinimizer U Q u := by
  obtain ⟨G₀, hu₀, -⟩ := id hmin
  exact ⟨⟨G₀, memH1Loc_of_memH1 hu₀⟩, hpos, hc2, hharm, fun _ _ _ hB _ _ _ hu hv _ hvu ↦
    hmin.energyJ_ball_le hU hUfin hQ hB hu hv hvu⟩

/-- For `Q ≡ 1`: a Dirichlet minimizer is not a.e. equal to a function `w` with measurable
positivity set whose measure exceeds the energy of some admissible competitor `v`. -/
theorem IsDirichletEnergyMinimizer.not_ae_eq_of_energyJ_lt {U : Set (E d)} (hU : IsOpen U)
    {g u w v : E d → ℝ} {Gv : E d → E d}
    (hmin : IsDirichletEnergyMinimizer U (fun _ ↦ 1) g u) (hP : MeasurableSet (posSet w U))
    (hv : MemH1 U v Gv) (hvg : MemH10 U (v - g))
    (hlt : energyJ U (fun _ ↦ 1) v Gv < volume (posSet w U)) :
    ¬ (u =ᵐ[volume.restrict U] w) := by
  intro huw
  obtain ⟨Gu, hu, -, -⟩ := id hmin
  have h1 := hmin.energyJ_le hU hu hv hvg
  rw [energyJ_congr_ae' hU.measurableSet huw (ae_of_all _ fun _ ↦ rfl)] at h1
  exact absurd (lt_of_lt_of_le hlt ((volume_posSet_le_energyJ hP Gu).trans h1)) (lt_irrefl _)

/-! ### Existence -/

/-- **Existence of a Dirichlet minimizer.** For a bounded open `U`, a bounded measurable `Q` and
`C¹` boundary data `g`, a minimizer of `J_Q(·; U)` among `v ∈ H¹(U)` with `v - g ∈ H¹₀(U)` exists.
Proof: the obstacle problem of elliptic-bernoulli-foundations in `ℝᵈ`, on a ball `B ⊇ U`, with
reference function `g` and constraint `w ∈ ℝ` in `U`, `w = g` off `U`. Its minimizer `w` is a
Dirichlet minimizer: every admissible `v` gives the obstacle competitor `g + 1_U (v - g)`, and on
`B \ U` both functions equal `g` with gradient `∇g` a.e. (Stampacchia's lemma). -/
theorem exists_isDirichletEnergyMinimizer {U : Set (E d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q g : E d → ℝ} (hQm : Measurable Q) {C : ℝ}
    (hQ : ∀ x, |Q x| ≤ C) (hg : ContDiff ℝ 1 g) :
    ∃ u, IsDirichletEnergyMinimizer U Q g u := by
  have hgL : MemH1Loc univ g (∇ g) :=
    GMTFoundations.memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hg.locallyLipschitz.locallyLipschitzOn
  obtain ⟨R₀, hR₀⟩ := hUb.subset_ball (0 : E d)
  set R : ℝ := |R₀| + 1 with hRdef
  have hR : 0 < R := by positivity
  have hUB : U ⊆ ball 0 R :=
    hR₀.trans (ball_subset_ball (by rw [hRdef]; linarith [le_abs_self R₀]))
  have hUcB : U ⊆ closedBall 0 R := hUB.trans ball_subset_closedBall
  have hBc : IsCompact (closedBall (0 : E d) R) := isCompact_closedBall 0 R
  have hBm : MeasurableSet (ball (0 : E d) R) := measurableSet_ball
  classical
  -- the obstacle problem: free in `U`, `w = g` off `U`
  set K : E d → Set ℝ := fun y ↦ if y ∈ U then univ else {g y} with hKdef
  have hKc : ∀ y, IsClosed (K y) := fun y ↦ by
    by_cases hy : y ∈ U <;> simp [hKdef, hy]
  have hgK : ∀ y ∈ (univ : Set (E d)), g y ∈ K y := fun y _ ↦ by
    by_cases hy : y ∈ U <;> simp [hKdef, hy]
  obtain ⟨w, Gw, hwL, -, hwK, hwmin⟩ := EllipticBernoulli.exists_isObstacleMinimizer
    (U := univ) (Q := Q) (u := g) (K := K) (x₀ := 0) (r := R) isOpen_univ ⟨C, fun x _ ↦ hQ x⟩
    hQm (memH1Loc_iff_eb.1 hgL) hR (subset_univ _) hKc hgK
  have hwL' : MemH1Loc univ w Gw := memH1Loc_iff_eb.2 hwL
  have hwg : ∀ y ∉ U, w y = g y := fun y hy ↦ by
    have := hwK y (mem_univ y)
    simpa [hKdef, hy] using this
  -- `w - g ∈ H¹(ℝᵈ)`, with gradient vanishing a.e. off `U` (Stampacchia)
  set Gf : E d → E d := fun y ↦ Gw y - ∇ g y with hGf
  have hfW : HasWeakGradient univ (fun y ↦ w y - g y) Gf :=
    GMTFoundations.HasWeakGradient.sub hwL'.1 hgL.1
  have hGf0 : ∀ᵐ y, y ∉ U → Gf y = 0 := by
    have h := EllipticBernoulli.HasWeakGradient.ae_eq_zero_of_eq_zero isOpen_univ
      (hasWeakGradient_iff_eb.1 hfW)
    rw [Measure.restrict_univ] at h
    filter_upwards [h] with y hy hyU using hy (by simp [hwg y hyU])
  obtain ⟨hwB, hGwB⟩ := hwL'.2 _ (subset_univ _) hBc
  obtain ⟨hgB, hGgB⟩ := hgL.2 _ (subset_univ _) hBc
  have hf1 : MemH1 univ (fun y ↦ w y - g y) Gf := memH1_univ_iff.2
    ⟨memLp_two_of_ae_eq_zero_off measurableSet_closedBall (hwB.sub hgB)
      (ae_of_all _ fun y hy ↦ by simp [hwg y (fun h ↦ hy (hUcB h))]),
     memLp_two_of_ae_eq_zero_off measurableSet_closedBall (hGwB.sub hGgB)
      (by filter_upwards [hGf0] with y hy hyB using hy (fun h ↦ hyB (hUcB h))),
     hfW⟩
  refine ⟨w, Gw, ⟨hwB.mono_measure (Measure.restrict_mono hUcB le_rfl),
    hGwB.mono_measure (Measure.restrict_mono hUcB le_rfl),
    hasWeakGradient_mono_set hwL'.1 (subset_univ U)⟩, ⟨Gf, ?_⟩, ?_⟩
  · have : U.indicator (w - g) = fun y ↦ w y - g y := by
      funext y
      by_cases hy : y ∈ U
      · simp [hy]
      · simp [hy, hwg y hy]
    rw [this]
    exact hf1
  -- minimality: `g + 1_U (v - g)` is an obstacle competitor
  rintro v Gv hv ⟨H, hH⟩
  set φ := U.indicator (v - g) with hφ
  have hH' := memH1_univ_iff.1 hH
  set vt : E d → ℝ := fun y ↦ g y + φ y with hvt
  set Gvt : E d → E d := fun y ↦ ∇ g y + H y with hGvt
  have hvtL : MemH1Loc univ vt Gvt := hgL.add (memH1Loc_of_memH1 hH)
  have hφ0 : ∀ y ∉ U, φ y = 0 := fun y hy ↦ indicator_of_notMem hy _
  have hvtg : ∀ y ∉ U, vt y = g y := fun y hy ↦ by simp [hvt, hφ0 y hy]
  have hJ := hwmin vt Gvt (memH1Loc_iff_eb.1 hvtL)
    ((ae_restrict_iff' (MeasurableSet.univ.diff hBm)).2
      (ae_of_all _ fun y hy ↦ hvtg y (fun h ↦ hy.2 (hUB h))))
    (ae_of_all _ fun y ↦ by by_cases hy : y ∈ U <;> simp [hKdef, hy, hvtg])
  change energyJ (ball 0 R) Q w Gw ≤ energyJ (ball 0 R) Q vt Gvt at hJ
  rw [energyJ_split' hU.measurableSet hBm hUB, energyJ_split' hU.measurableSet hBm hUB] at hJ
  -- on `B \ U` both are `g`, with gradient `∇g` a.e.
  have hH0 : ∀ᵐ y, y ∉ U → H y = 0 := by
    have h := EllipticBernoulli.HasWeakGradient.ae_eq_zero_of_eq_zero isOpen_univ
      (hasWeakGradient_iff_eb.1 hH'.2.2)
    rw [Measure.restrict_univ] at h
    filter_upwards [h] with y hy hyU using hy (hφ0 y hyU)
  have hout : energyJ (ball 0 R \ U) Q vt Gvt = energyJ (ball 0 R \ U) Q w Gw := by
    refine energyJ_congr' (fun y hy ↦ by rw [hvtg y hy.2, hwg y hy.2]) ?_
    filter_upwards [ae_restrict_of_ae hGf0, ae_restrict_of_ae hH0,
      ae_restrict_mem (hBm.diff hU.measurableSet)] with y h1 h2 hy
    have h3 := h1 hy.2
    simp only [hGf, sub_eq_zero] at h3
    simp [hGvt, h2 hy.2, h3]
  have hfin : energyJ (ball 0 R \ U) Q w Gw ≠ ∞ :=
    (energyJ_lt_top' hwL' (hBc.of_isClosed_subset isClosed_closure
      (closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall))
      (subset_univ _) (fun y _ ↦ hQ y)).ne
  rw [hout, ENNReal.add_le_add_iff_right hfin] at hJ
  -- on `U`, the competitor is `v`, with gradient `Gv` a.e.
  refine hJ.trans_eq (energyJ_congr' (fun y hy ↦ ?_) ?_)
  · simp [hvt, hφ, indicator_of_mem hy]
  · have hφU : HasWeakGradient U φ H := hasWeakGradient_mono_set hH'.2.2 (subset_univ U)
    have hvg' : HasWeakGradient U (fun y ↦ v y - g y) (fun y ↦ Gv y - ∇ g y) :=
      GMTFoundations.HasWeakGradient.sub hv.2.2 (hasWeakGradient_mono_set hgL.1 (subset_univ U))
    have h := EllipticBernoulli.HasWeakGradient.ae_eq_of_eqOn hU hU subset_rfl
      (hasWeakGradient_iff_eb.1 hφU) (hasWeakGradient_iff_eb.1 hvg')
      (fun y hy ↦ by simp [hφ, indicator_of_mem hy])
    filter_upwards [h] with y hy
    simp [hGvt, hy]

end PerronVariational

end
