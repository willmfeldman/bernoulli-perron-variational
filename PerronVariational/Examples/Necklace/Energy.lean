/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.Largest
public import PerronVariational.Examples.Necklace.Statement
public import GMTFoundations.Sobolev.Lipschitz
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The necklace example: the competitor and the energy bounds

For the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M. Feldman, K.
Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`), the explicit supersolution
`v = Σ_k (a log (a/|x - z_k|))₊ + (ρ_o log (|x|/ρ_o))₊` is an admissible competitor for the
Dirichlet problem with boundary values `gSub`, with small energy, while the largest subsolution
`u_max` is positive on a large set:

* `vSup_admissible`: `v ∈ H¹(U)` with weak gradient `∇v`, and `v - gSub ∈ H¹₀(U)`;
* `energyJ_vSup_le`: `J_1(v; U) ≤ (107/20) π`;
* `energyJ_ge_volume_posSet`: `J_1(w; U) ≥ |{w > 0} ∩ U|` for every measurable `w`;
* `volume_posSet_uMax_ge`: `|{u_max > 0} ∩ U| ≥ (97/10) π`, and the same for every `w = u_max`
  a.e. in `U` (`volume_posSet_ge_of_ae_eq`);
* `energyJ_vSup_lt_volume_posSet`: the strict comparison `J_1(v; U) < |{w > 0} ∩ U|` for every
  `w = u_max` a.e. in `U`.

So a Dirichlet minimizer `w` would satisfy `|{w > 0} ∩ U| ≤ J_1(w; U) ≤ J_1(v; U)`, which rules out
`w = u_max` a.e.

The energy bound: off the closed discs `B̄_a(z_k)` and the layer `{|x| ≥ ρ_o}`, `v` vanishes on an
open set; on `B_a(z_k) ∩ U` we have `|∇v| = a/|x - z_k| ≤ a/r = 2`, on the layer `|∇v| ≤ 1`; the
circles are null sets. Hence `J_1(v; U) ≤ 5 (N π (a² - r²) + π (16 - ρ_o²)) ≤ (107/20) π`.
The area bound: `U ∩ B_{ρ_in}` is `B_{ρ_in}` minus the holes, of area `≥ π (ρ_in² - N r²)`.
-/

open Set Filter Topology Metric MeasureTheory Real
open scoped Gradient ENNReal ContDiff

@[expose] public noncomputable section

namespace PerronVariational

/-! ### Indicators of functions vanishing on the boundary -/

section Indicator

variable {d : ℕ}

/-- A segment from a point of an open set `U` to a point outside `U` meets `∂U`. -/
theorem exists_mem_segment_frontier {U : Set (E d)} (hU : IsOpen U) {x y : E d} (hx : x ∈ U)
    (hy : y ∉ U) : ∃ p ∈ segment ℝ x y, p ∈ frontier U := by
  by_contra h
  push Not at h
  have hsub : segment ℝ x y ⊆ U ∪ (closure U)ᶜ := by
    intro p hp
    by_cases hpU : p ∈ U
    · exact Or.inl hpU
    · refine Or.inr fun hpc ↦ h p hp ⟨hpc, ?_⟩
      rwa [hU.interior_eq]
  rcases (convex_segment x y).isPreconnected.subset_or_subset hU isClosed_closure.isOpen_compl
    (Set.disjoint_compl_right_iff_subset.2 subset_closure) hsub with h1 | h1
  · exact hy (h1 (right_mem_segment ℝ x y))
  · exact h1 (left_mem_segment ℝ x y) (subset_closure hx)

/-- If `f` is `K`-Lipschitz on a convex set `s` and vanishes on `∂U ∩ s`, then so is the
extension of `f|_U` by zero. -/
theorem lipschitzOnWith_indicator {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {s : Set (E d)}
    (hs : Convex ℝ s) {K : NNReal} (hf : LipschitzOnWith K f s)
    (h0 : ∀ p ∈ s, p ∈ frontier U → f p = 0) : LipschitzOnWith K (U.indicator f) s := by
  have key : ∀ x ∈ s, ∀ y ∈ s, x ∈ U → y ∉ U → dist (f x) 0 ≤ K * dist x y := by
    intro x hx y hy hxU hyU
    obtain ⟨p, hp, hpf⟩ := exists_mem_segment_frontier hU hxU hyU
    have hps : p ∈ s := hs.segment_subset hx hy hp
    have h1 := hf.dist_le_mul x hx p hps
    rw [h0 p hps hpf] at h1
    have h2 : dist x p ≤ dist x y := by
      rw [dist_comm x p, dist_comm x y, dist_eq_norm, dist_eq_norm]
      exact norm_sub_le_of_mem_segment hp
    exact h1.trans (mul_le_mul_of_nonneg_left h2 K.coe_nonneg)
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U
  · rw [indicator_of_mem hxU, indicator_of_mem hyU]; exact hf.dist_le_mul x hx y hy
  · rw [indicator_of_mem hxU, indicator_of_notMem hyU]; exact key x hx y hy hxU hyU
  · rw [indicator_of_notMem hxU, indicator_of_mem hyU, dist_comm, dist_comm x]
    exact key y hy x hx hyU hxU
  · rw [indicator_of_notMem hxU, indicator_of_notMem hyU, dist_self]
    exact mul_nonneg K.coe_nonneg dist_nonneg

/-- If `f` is locally Lipschitz and vanishes on `∂U`, then the extension of `f|_U` by zero is
locally Lipschitz. -/
theorem locallyLipschitz_indicator_of_frontier {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : LocallyLipschitz f) (h0 : ∀ p ∈ frontier U, f p = 0) :
    LocallyLipschitz (U.indicator f) := by
  intro x
  obtain ⟨K, t, ht, hK⟩ := hf x
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
  exact ⟨K, ball x ε, ball_mem_nhds x hε,
    lipschitzOnWith_indicator hU (convex_ball x ε) (hK.mono hball) fun p _ hp ↦ h0 p hp⟩

/-- A locally Lipschitz function vanishing outside a closed ball lies in `H¹(ℝᵈ)`, with weak
gradient its pointwise gradient. -/
theorem memH1_univ_of_locallyLipschitz {w : E d → ℝ} (hw : LocallyLipschitz w) {c : E d}
    {R : ℝ} (hR : ∀ x ∉ closedBall c R, w x = 0) : MemH1 univ w (∇ w) := by
  obtain ⟨hwg, hL2⟩ := GMTFoundations.memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
    (hw.locallyLipschitzOn (s := univ))
  obtain ⟨h1, h2⟩ := hL2 (closedBall c R) (subset_univ _) (isCompact_closedBall c R)
  have hm : MeasurableSet (closedBall c R) := measurableSet_closedBall
  have ew : w = (closedBall c R).indicator w := by
    funext x
    by_cases hx : x ∈ closedBall c R
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hR x hx]
  have eg : ∇ w = (closedBall c R).indicator (∇ w) := by
    funext x
    by_cases hx : x ∈ closedBall c R
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      have hev : w =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
        exact hR y hy
      rw [hev.gradient_eq]
      exact gradient_fun_const x 0
  refine ⟨?_, ?_, hwg⟩
  · rw [Measure.restrict_univ, ew, memLp_indicator_iff_restrict hm]; exact h1
  · rw [Measure.restrict_univ, eg, memLp_indicator_iff_restrict hm]; exact h2

end Indicator

namespace Necklace

open TwoDisc (wIn contDiff_wIn wIn_eq wIn_pos max_wIn_eq_zero log_hundredth_sub cst cst_pos)

/-! ### `v` is locally Lipschitz -/

theorem locallyLipschitz_finset_sum {ι : Type*} (s : Finset ι) {f : ι → E 2 → ℝ}
    (h : ∀ i ∈ s, LocallyLipschitz (f i)) : LocallyLipschitz fun x ↦ ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocallyLipschitz.const (α := E 2) (0 : ℝ)
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

theorem locallyLipschitz_vSup : LocallyLipschitz vSup := by
  have h1 : LocallyLipschitz wSum := locallyLipschitz_finset_sum Finset.univ fun k _ ↦
    ((contDiff_wIn _).of_le one_le_two).locallyLipschitz.max_const 0
  exact h1.add ((contDiff_hLayer.of_le one_le_two).locallyLipschitz.max_const 0)

theorem domain_subset_closedBall : domain ⊆ closedBall (0 : E 2) 4 := fun x hx ↦
  ball_subset_closedBall (mem_domain_iff.1 hx |>.1 |> fun h ↦ by
    rw [mem_ball, dist_zero_right]; exact h)

/-- `v ∈ H¹(U)` with weak gradient `∇v`. -/
theorem memH1_vSup : MemH1 domain vSup (∇ vSup) := by
  obtain ⟨-, hL2⟩ := GMTFoundations.memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
    (locallyLipschitz_vSup.locallyLipschitzOn (s := univ))
  obtain ⟨hwg, -⟩ := GMTFoundations.memH1Loc_gradient_of_locallyLipschitzOn isOpen_domain
    (locallyLipschitz_vSup.locallyLipschitzOn (s := domain))
  obtain ⟨h1, h2⟩ := hL2 (closedBall 0 4) (subset_univ _) (isCompact_closedBall 0 4)
  exact ⟨h1.mono_measure (Measure.restrict_mono domain_subset_closedBall le_rfl),
    h2.mono_measure (Measure.restrict_mono domain_subset_closedBall le_rfl), hwg⟩

/-- `v = gSub` on `∂U`. -/
theorem vSup_eq_gSub_of_mem_frontier {x : E 2} (hx : x ∈ frontier domain) : vSup x = gSub x := by
  rcases mem_frontier_cases hx with h | ⟨k, hk⟩
  · have hfar : ∀ j : Fin numHoles, 1 / 100 ≤ ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2 :=
      fun j ↦ (geom_far (by rw [h]; norm_num) _).le
    have hL := layerRad_sq_bounds
    have hh : hLayer x = epsOut := by
      rw [hLayer_eq (by rw [h]; linarith) h.le, h, log_layerRad_sq]; unfold epsOut; ring
    rw [gSub_eq, (qSum_of_far hfar).1, qLayer_of_outer h, vSup_eq, wSum_eq_zero hfar, hh,
      max_eq_left epsOut_pos.le]
    ring
  · obtain ⟨hothers, h0⟩ := geom_disc (x := x) (k := k) (by rw [hk]; norm_num)
    rw [gSub_on_circle hk, vSup_eq, wSum_eq_single k hothers,
      max_hLayer_eq_zero (by linarith [ten_lt_layerRad_sq]), add_zero,
      wIn_eq (by rw [hk]) (by rw [hk]; norm_num), hk, log_hundredth_sub]
    have : (2 * Real.log 2) / 20 = cst := by unfold cst; ring
    rw [this, max_eq_left cst_pos.le]

/-- `v - gSub ∈ H¹₀(U)`: its extension by zero is locally Lipschitz (it vanishes on `∂U`) and
supported in `B̄₄`. -/
theorem memH10_vSup_sub_gSub : MemH10 domain (vSup - gSub) := by
  have hf : LocallyLipschitz (vSup - gSub) :=
    locallyLipschitz_vSup.sub ((contDiff_gSub.of_le one_le_two).locallyLipschitz)
  have hi := locallyLipschitz_indicator_of_frontier isOpen_domain hf fun p hp ↦ by
    simp [vSup_eq_gSub_of_mem_frontier hp]
  refine ⟨_, memH1_univ_of_locallyLipschitz hi (c := 0) (R := 4) fun x hx ↦ ?_⟩
  exact indicator_of_notMem (fun hxU ↦ hx (domain_subset_closedBall hxU)) _

/-- **The competitor is admissible**: `v ∈ H¹(U)` with weak gradient `∇v`, and
`v - gSub ∈ H¹₀(U)`. -/
theorem vSup_admissible : MemH1 domain vSup (∇ vSup) ∧ MemH10 domain (vSup - gSub) :=
  ⟨memH1_vSup, memH10_vSup_sub_gSub⟩

/-! ### The gradient of `v` -/

/-- On `B_a(z_k) ∩ U`, `v = W_k` near `x` and `|∇v(x)| = a/|x - z_k| ≤ 2`. -/
theorem norm_gradient_vSup_of_disc {x : E 2} {k : Fin numHoles}
    (h1 : 1 / 400 < ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2) (h2 : ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 < 1 / 100) :
    ‖∇ vSup x‖ ≤ 2 := by
  have hc : Continuous fun y : E 2 ↦ ‖y - cen ((k : ℕ) : ℤ)‖ ^ 2 := by fun_prop
  have hev : vSup =ᶠ[𝓝 x] wIn (cen ((k : ℕ) : ℤ)) := by
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h2,
      continuousAt_const.eventually_lt hc.continuousAt h1] with y hy2 hy1
    obtain ⟨hothers, h0⟩ := geom_disc hy2.le
    rw [vSup_eq, wSum_eq_single k hothers, max_hLayer_eq_zero (by linarith [ten_lt_layerRad_sq]),
      add_zero, max_eq_left (wIn_pos hy1.le hy2).le]
  rw [hev.gradient_eq, wIn, TwoDisc.pV, TwoDisc.norm_gradient_logRad_mid (by norm_num) cst_pos
    (by norm_num) (by norm_num) TwoDisc.clamp_wIn (by linarith) (TwoDisc.wIn_mid h1.le h2.le)]
  have hn : 1 / 20 < ‖x - cen ((k : ℕ) : ℤ)‖ :=
    (pow_lt_pow_iff_left₀ (by norm_num) (norm_nonneg _) two_ne_zero).1 (by linarith)
  rw [div_le_iff₀ (by linarith)]
  norm_num
  linarith

/-- On the layer `{ρ_o < |x| < 4}`, `v = h` near `x` and `|∇v(x)| = ρ_o/|x| ≤ 1`. -/
theorem norm_gradient_vSup_of_layer {x : E 2} (h1 : layerRad ^ 2 < ‖x - 0‖ ^ 2)
    (h2 : ‖x - 0‖ ^ 2 < 16) : ‖∇ vSup x‖ ≤ 1 := by
  have hc : Continuous fun y : E 2 ↦ ‖y - 0‖ ^ 2 := by fun_prop
  have hev : vSup =ᶠ[𝓝 x] hLayer := by
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h2,
      continuousAt_const.eventually_lt hc.continuousAt h1] with y hy2 hy1
    rw [vSup_eq, wSum_eq_zero fun j ↦ (geom_far (by linarith [ten_lt_layerRad_sq]) _).le,
      zero_add, max_eq_left (hLayer_pos hy1 hy2.le).le]
  have hr := layerRad_bounds
  rw [hev.gradient_eq, hLayer, TwoDisc.pH, TwoDisc.norm_gradient_logRad_mid (by norm_num) one_pos
    one_pos (by norm_num) clamp_hLayer (by linarith [layerRad_sq_bounds.1]) (ah_mid h1.le h2.le)]
  have hn : layerRad < ‖x - 0‖ :=
    (pow_lt_pow_iff_left₀ (by linarith) (norm_nonneg _) two_ne_zero).1 h1
  rw [div_le_iff₀ (by linarith), abs_of_pos (by linarith)]
  linarith

/-- Off the closed discs and the layer, `v` vanishes near `x`. -/
theorem vSup_eventually_zero {x : E 2}
    (h1 : ∀ j : Fin numHoles, 1 / 100 < ‖x - cen ((j : ℕ) : ℤ)‖ ^ 2)
    (h2 : ‖x - 0‖ ^ 2 < layerRad ^ 2) : vSup =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
  have hc : ∀ c : E 2, Continuous fun y : E 2 ↦ ‖y - c‖ ^ 2 := fun c ↦ by fun_prop
  filter_upwards [eventually_all.2 fun j : Fin numHoles ↦
      continuousAt_const.eventually_lt (hc (cen ((j : ℕ) : ℤ))).continuousAt (h1 j),
    (hc 0).continuousAt.eventually_lt continuousAt_const h2] with y hy hy0
  rw [vSup_eq, wSum_eq_zero fun j ↦ (hy j).le, max_hLayer_eq_zero hy0.le, add_zero]

/-! ### The energy of `v` -/

/-- The set carrying the energy of `v` in `U`: the annuli `B_a(z_k) \ B̄_r(z_k)` and the layer
`B₄ \ B̄_{ρ_o}`. -/
def energySet : Set (E 2) :=
  (⋃ k : Fin numHoles, ball (cen ((k : ℕ) : ℤ)) kissRad \ closedBall (cen ((k : ℕ) : ℤ)) holeRad) ∪
    (ball 0 4 \ closedBall 0 layerRad)

/-- The circles `∂B_a(z_k)` and `∂B_{ρ_o}`, a null set. -/
def nullCircles : Set (E 2) :=
  (⋃ k : Fin numHoles, sphere (cen ((k : ℕ) : ℤ)) kissRad) ∪ sphere 0 layerRad

theorem measurableSet_energySet : MeasurableSet energySet :=
  (MeasurableSet.iUnion fun _ ↦ measurableSet_ball.diff measurableSet_closedBall).union
    (measurableSet_ball.diff measurableSet_closedBall)

theorem volume_nullCircles : volume nullCircles = 0 :=
  measure_union_null (measure_iUnion_null fun _ ↦ Measure.addHaar_sphere _ _ _)
    (Measure.addHaar_sphere _ _ _)

theorem norm_eq_of_normSq_eq {v : E 2} {s : ℝ} (hs : 0 ≤ s) (h : ‖v‖ ^ 2 = s ^ 2) : ‖v‖ = s :=
  (pow_left_inj₀ (norm_nonneg _) hs two_ne_zero).1 h

/-- Pointwise bound of the energy density of `v`: off the null set `nullCircles`, it is at most
`5` on `energySet` and `0` elsewhere in `U`. -/
theorem energy_density_le {x : E 2} (hx : x ∈ domain) (hxZ : x ∉ nullCircles) :
    ENNReal.ofReal (‖∇ vSup x‖ ^ 2 + (fun _ : E 2 ↦ (1 : ℝ)) x ^ 2 *
      (posSet vSup domain).indicator 1 x) ≤ energySet.indicator (fun _ ↦ (5 : ℝ≥0∞)) x := by
  obtain ⟨h0, hk⟩ := normSq_of_mem_domain hx
  have hind : (posSet vSup domain).indicator (1 : E 2 → ℝ) x ≤ 1 := by
    unfold indicator; split_ifs <;> norm_num
  have hZk : ∀ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ≠ kissRad := fun k h ↦
    hxZ (Or.inl (mem_iUnion.2 ⟨k, by rw [mem_sphere_iff_norm]; exact h⟩))
  have hZ0 : ‖x - 0‖ ≠ layerRad := fun h ↦ hxZ (Or.inr (by rw [mem_sphere_iff_norm]; exact h))
  have hkr : kissRad ^ 2 = 1 / 100 := by norm_num [kissRad]
  have hhr : holeRad ^ 2 = 1 / 400 := by norm_num [holeRad]
  have hr := layerRad_bounds
  by_cases A : ∃ k : Fin numHoles, ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 < 1 / 100
  · obtain ⟨k, hkA⟩ := A
    have hmem : x ∈ energySet := by
      refine Or.inl (mem_iUnion.2 ⟨k, ?_, ?_⟩)
      · rw [mem_ball, dist_eq_norm, ← normSq_lt_iff (by norm_num [kissRad]), hkr]; exact hkA
      · rw [mem_closedBall, dist_eq_norm, ← normSq_le_iff (by norm_num [holeRad]), hhr, not_le]
        exact hk k
    rw [indicator_of_mem hmem]
    have hg := norm_gradient_vSup_of_disc (hk k) hkA
    have : ‖∇ vSup x‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (∇ vSup x)]
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal 5 := ENNReal.ofReal_le_ofReal (by simp only; linarith)
      _ = 5 := ENNReal.ofReal_ofNat 5
  push Not at A
  have A' : ∀ k : Fin numHoles, 1 / 100 < ‖x - cen ((k : ℕ) : ℤ)‖ ^ 2 := fun k ↦
    lt_of_le_of_ne (A k) fun h ↦ hZk k (norm_eq_of_normSq_eq (by norm_num [kissRad])
      (by rw [hkr]; exact h.symm))
  rcases lt_trichotomy (‖x - 0‖ ^ 2) (layerRad ^ 2) with B | B | B
  · have hev := vSup_eventually_zero A' B
    have hv0 : vSup x = 0 := hev.self_of_nhds
    have hi : (posSet vSup domain).indicator (1 : E 2 → ℝ) x = 0 :=
      indicator_of_notMem (fun h ↦ by have := h.2; rw [hv0] at this; exact lt_irrefl _ this) _
    rw [hev.gradient_eq, gradient_fun_const, hi]
    simp
  · exact absurd (norm_eq_of_normSq_eq (by linarith) B) hZ0
  · have hmem : x ∈ energySet := by
      refine Or.inr ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, ← normSq_lt_iff (by norm_num)]; norm_num; simpa using h0
      · rw [mem_closedBall, dist_eq_norm, ← normSq_le_iff (by linarith), not_le]; exact B
    rw [indicator_of_mem hmem]
    have hg := norm_gradient_vSup_of_layer B h0
    have : ‖∇ vSup x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (∇ vSup x)]
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal 5 := ENNReal.ofReal_le_ofReal (by simp only; linarith)
      _ = 5 := ENNReal.ofReal_ofNat 5

/-- The area of an annulus. -/
theorem volume_ball_sdiff_closedBall (c : E 2) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) :
    volume (ball c s \ closedBall c r) = ENNReal.ofReal (π * (s ^ 2 - r ^ 2)) := by
  rw [measure_sdiff (closedBall_subset_ball hrs) measurableSet_closedBall.nullMeasurableSet
    measure_closedBall_lt_top.ne, EuclideanSpace.volume_ball_fin_two,
    EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow (hr.trans hrs.le),
    ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_sub _ (by positivity)]
  congr 1; ring

theorem sum_ofReal_const (X : ℝ) :
    ∑ _k : Fin numHoles, ENNReal.ofReal X = ENNReal.ofReal (100 * X) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.ofReal_mul (by norm_num)]
  norm_num [numHoles]

theorem volume_energySet_le :
    volume energySet ≤
      ENNReal.ofReal (π * (100 * (kissRad ^ 2 - holeRad ^ 2) + (4 ^ 2 - layerRad ^ 2))) := by
  have hr := layerRad_bounds
  have hka : (0 : ℝ) ≤ π * (kissRad ^ 2 - holeRad ^ 2) := by
    have := pi_pos; norm_num [kissRad, holeRad]; positivity
  have hla : (0 : ℝ) ≤ π * (4 ^ 2 - layerRad ^ 2) := by
    have := pi_pos; have := layerRad_sq_bounds.2; nlinarith
  calc volume energySet
      ≤ volume (⋃ k : Fin numHoles,
            ball (cen ((k : ℕ) : ℤ)) kissRad \ closedBall (cen ((k : ℕ) : ℤ)) holeRad) +
          volume (ball (0 : E 2) 4 \ closedBall 0 layerRad) := measure_union_le _ _
    _ ≤ ∑ k : Fin numHoles,
            volume (ball (cen ((k : ℕ) : ℤ)) kissRad \ closedBall (cen ((k : ℕ) : ℤ)) holeRad) +
          volume (ball (0 : E 2) 4 \ closedBall 0 layerRad) := by
        gcongr; exact measure_iUnion_fintype_le _ _
    _ = ENNReal.ofReal (100 * (π * (kissRad ^ 2 - holeRad ^ 2))) +
          ENNReal.ofReal (π * (4 ^ 2 - layerRad ^ 2)) := by
        rw [volume_ball_sdiff_closedBall _ (by linarith) hr.2]
        simp_rw [volume_ball_sdiff_closedBall _ (by norm_num [holeRad] : (0 : ℝ) ≤ holeRad)
          (by norm_num [holeRad, kissRad] : holeRad < kissRad)]
        rw [sum_ofReal_const]
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) hla]; congr 1; ring

/-- **The energy of the competitor**: `J_1(v; U) ≤ 5 (N π (a² - r²) + π (16 - ρ_o²)) ≤ (107/20) π`
(numerically `5.35 π`; the exact energy is about `2.77 π`). -/
theorem energyJ_vSup_le :
    energyJ domain (fun _ ↦ 1) vSup (∇ vSup) ≤ ENNReal.ofReal (107 / 20 * π) := by
  have hae : ∀ᵐ x ∂(volume.restrict domain),
      ENNReal.ofReal (‖∇ vSup x‖ ^ 2 + (fun _ : E 2 ↦ (1 : ℝ)) x ^ 2 *
        (posSet vSup domain).indicator 1 x) ≤ energySet.indicator (fun _ ↦ (5 : ℝ≥0∞)) x := by
    refine (ae_restrict_iff' isOpen_domain.measurableSet).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 volume_nullCircles] with x hxZ hx
    exact energy_density_le hx hxZ
  have hr := layerRad_sq_bounds
  calc energyJ domain (fun _ ↦ 1) vSup (∇ vSup)
      ≤ ∫⁻ x in domain, energySet.indicator (fun _ ↦ (5 : ℝ≥0∞)) x := lintegral_mono_ae hae
    _ ≤ ∫⁻ x, energySet.indicator (fun _ ↦ (5 : ℝ≥0∞)) x := setLIntegral_le_lintegral _ _
    _ = 5 * volume energySet := lintegral_indicator_const measurableSet_energySet 5
    _ ≤ 5 * ENNReal.ofReal
          (π * (100 * (kissRad ^ 2 - holeRad ^ 2) + (4 ^ 2 - layerRad ^ 2))) := by
        gcongr; exact volume_energySet_le
    _ ≤ ENNReal.ofReal (107 / 20 * π) := by
        rw [← ENNReal.ofReal_ofNat 5, ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := pi_pos
        norm_num [kissRad, holeRad]
        nlinarith

/-! ### The positivity set of `u_max` -/

/-- `|U ∩ B_{ρ_in}| ≥ π (ρ_in² - N r²) ≥ (97/10) π`. -/
theorem volume_inner_ge :
    ENNReal.ofReal (97 / 10 * π) ≤ volume (domain ∩ ball (0 : E 2) innerRad) := by
  have hρ := innerRad_bounds
  have hsub : ball (0 : E 2) innerRad ⊆ (domain ∩ ball 0 innerRad) ∪ holes := by
    intro x hx
    by_cases hh : x ∈ holes
    · exact Or.inr hh
    · refine Or.inl ⟨⟨ball_subset_ball (by unfold outerRad; linarith) hx, hh⟩, hx⟩
  have hh0 : (0 : ℝ) ≤ π * holeRad ^ 2 := by positivity
  have hholes : volume holes ≤ ENNReal.ofReal (100 * (π * holeRad ^ 2)) := by
    calc volume holes ≤ ∑ k : Fin numHoles, volume (closedBall (cen ((k : ℕ) : ℤ)) holeRad) :=
          measure_iUnion_fintype_le _ _
      _ = ∑ _k : Fin numHoles, ENNReal.ofReal (π * holeRad ^ 2) := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow
            (by norm_num [holeRad] : (0 : ℝ) ≤ holeRad), ← ENNReal.ofReal_mul (by positivity),
            mul_comm]
      _ = _ := sum_ofReal_const _
  have hball : volume (ball (0 : E 2) innerRad) = ENNReal.ofReal (π * innerRad ^ 2) := by
    rw [EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow innerRad_pos.le,
      ← ENNReal.ofReal_mul (by positivity), mul_comm]
  have h1 : ENNReal.ofReal (π * innerRad ^ 2) ≤
      volume (domain ∩ ball (0 : E 2) innerRad) + ENNReal.ofReal (100 * (π * holeRad ^ 2)) := by
    rw [← hball]
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans (by gcongr))
  have h2 := tsub_le_iff_right.2 h1
  rw [← ENNReal.ofReal_sub _ (by positivity)] at h2
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h2
  have hρ2 : 9.98 < innerRad ^ 2 := by nlinarith
  have := mul_pos pi_pos (sub_pos.2 hρ2)
  norm_num [holeRad]
  nlinarith

/-- **`u_max` is positive on a large set**: `|{u_max > 0} ∩ U| ≥ (97/10) π`. -/
theorem volume_posSet_uMax_ge : ENNReal.ofReal (97 / 10 * π) ≤ volume (posSet uMax domain) := by
  obtain ⟨κ, hκ, h⟩ := uMax_pos_of_mem_inner
  exact volume_inner_ge.trans (measure_mono fun x hx ↦ ⟨hx.1, lt_of_lt_of_le hκ (h x hx)⟩)

/-- The same lower bound for every function equal to `u_max` a.e. in `U`. -/
theorem volume_posSet_ge_of_ae_eq {u : E 2 → ℝ} (hu : u =ᵐ[volume.restrict domain] uMax) :
    ENNReal.ofReal (97 / 10 * π) ≤ volume (posSet u domain) := by
  have hN : volume {x | x ∈ domain ∧ u x ≠ uMax x} = 0 := by
    have := (ae_restrict_iff' isOpen_domain.measurableSet).1 hu
    exact measure_mono_null (fun x hx ↦ by simp only [mem_ofPred_eq, not_imp]; exact hx)
      (ae_iff.1 this)
  calc ENNReal.ofReal (97 / 10 * π) ≤ volume (posSet uMax domain) := volume_posSet_uMax_ge
    _ ≤ volume (posSet u domain ∪ {x | x ∈ domain ∧ u x ≠ uMax x}) := by
        refine measure_mono fun x hx ↦ ?_
        by_cases h : u x = uMax x
        · exact Or.inl ⟨hx.1, h ▸ hx.2⟩
        · exact Or.inr ⟨hx.1, h⟩
    _ ≤ volume (posSet u domain) + 0 := (measure_union_le _ _).trans (by rw [hN])
    _ = _ := add_zero _

/-- The numerical gap between the two constants: `(107/20) π < (97/10) π`. -/
theorem energy_bound_lt_area_bound : ENNReal.ofReal (107 / 20 * π) < ENNReal.ofReal (97 / 10 * π) :=
  (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith [pi_pos])

/-- **The comparison**: `J_1(v; U) < |{u > 0} ∩ U|` for every `u = u_max` a.e. in `U`. -/
theorem energyJ_vSup_lt_volume_posSet {u : E 2 → ℝ} (hu : u =ᵐ[volume.restrict domain] uMax) :
    energyJ domain (fun _ ↦ 1) vSup (∇ vSup) < volume (posSet u domain) :=
  (energyJ_vSup_le.trans_lt energy_bound_lt_area_bound).trans_le (volume_posSet_ge_of_ae_eq hu)

end Necklace

/-! ### The energy controls the area of the positivity set -/

/-- `J_1(v; U) ≥ |{v > 0} ∩ U|` (the Dirichlet term is nonnegative and `Q ≡ 1`). -/
theorem energyJ_ge_volume_posSet {d : ℕ} {U : Set (E d)} (hU : MeasurableSet U) {v : E d → ℝ}
    (hv : AEStronglyMeasurable v (volume.restrict U)) (G : E d → E d) :
    volume (posSet v U) ≤ energyJ U (fun _ ↦ 1) v G := by
  have hns : NullMeasurableSet {x | (0 : ℝ) < v x} (volume.restrict U) :=
    nullMeasurableSet_lt aemeasurable_const hv.aemeasurable
  have hpos : posSet v U = U ∩ {x | 0 < v x} := rfl
  calc volume (posSet v U) = volume.restrict U {x | 0 < v x} := by
        rw [Measure.restrict_apply₀ hns, hpos, inter_comm]
    _ = ∫⁻ x in U, {x | 0 < v x}.indicator 1 x := (lintegral_indicator_one₀ hns).symm
    _ ≤ energyJ U (fun _ ↦ 1) v G := by
        refine lintegral_mono_ae ((ae_restrict_iff' hU).2 (Eventually.of_forall fun x hx ↦ ?_))
        by_cases h : 0 < v x
        · rw [indicator_of_mem (show x ∈ {x | 0 < v x} from h),
            indicator_of_mem (show x ∈ posSet v U from ⟨hx, h⟩)]
          simp only [Pi.one_apply, one_pow, mul_one]
          exact ENNReal.one_le_ofReal.2 (by nlinarith [sq_nonneg ‖G x‖])
        · rw [indicator_of_notMem (show x ∉ {x | 0 < v x} from h)]
          exact bot_le


end PerronVariational

end
