/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Examples.Necklace.Upper
public import PerronVariational.Examples.TwoDisc.Lower

/-!
# The lower bound in the necklace example

For the necklace example (`[AFS]`, [Figure 1](#AFS:f.necklace)) of F. Abedin, W. M. Feldman, K.
Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981 (`[AFS]`): every `V ∈ 𝒮_{gSub}` lies above each radial solution
`w_k = a log (a/|x - z_k|)` on `{r ≤ |x - z_k| < a}` (`wIn_le_of_mem_perronSuperClass`), hence so
does `u_min` (`wIn_le_perronSmallest`). With the upper bound `u_min ≤ v` this gives
`u_min = v` on `U ∩ B̄_{ρ_o}(0)` (`perronSmallest_eq_vSup_near`).

The barriers are those of the two-disc example (`TwoDisc.barrier`, centre-generic); only the
comparison argument depends on the domain: the closed annulus `{r ≤ |x - z_k| ≤ a}` lies in `Ū`,
its interior in `U`, and `gSub = c` on the hole circle `|x - z_k| = r`.
-/

open Set Filter Topology Metric InnerProductSpace Real
open scoped Gradient Laplacian ContDiff

@[expose] public noncomputable section

namespace PerronVariational.Necklace

open TwoDisc (cst cst_pos qIn qIn_of_circle wIn wIn_eq wIn_pos max_wIn_eq_zero isOpen_lt_normsq
  isOpen_gt_normsq barR barB barrier barrier_eq barrier_le_cst barrier_outer laplacian_barrier
  norm_gradient_barrier contDiff_barrier barR_bounds IsViscSuper.false_of_touch_contDiff_two)

/-- The smallest supersolution of the example. -/
abbrev uMin : E 2 → ℝ := perronSmallest domain (fun _ ↦ 1) gSub

theorem perronSuperClass_nonempty : (perronSuperClass domain (fun _ ↦ (1 : ℝ)) gSub).Nonempty :=
  ⟨vSup, vSup_mem_perronSuperClass⟩

/-! ### Geometry of the annuli around the holes -/

/-- The annulus `{r < |x - z_k| ≤ a}` lies in `U`. -/
theorem mem_domain_of_near {k : ℤ} {x : E 2} (h1 : 1 / 400 < ‖x - cen k‖ ^ 2)
    (h2 : ‖x - cen k‖ ^ 2 ≤ 1 / 100) : x ∈ domain := by
  obtain ⟨j, hj⟩ := exists_fin_cen_eq k
  rw [← hj] at h1 h2
  obtain ⟨hothers, h0⟩ := geom_disc h2
  rw [mem_domain_iff]
  refine ⟨?_, fun i ↦ ?_⟩
  · rw [sub_zero] at h0
    refine (normSq_lt_iff (by norm_num [outerRad])).1 ?_
    unfold outerRad; linarith
  · refine (pow_lt_pow_iff_left₀ (by norm_num [holeRad]) (norm_nonneg _) two_ne_zero).1 ?_
    unfold holeRad
    by_cases hij : i = j
    · subst hij; linarith
    · linarith [hothers i hij]

theorem mem_closure_of_near {k : ℤ} {x : E 2} (h1 : 1 / 400 ≤ ‖x - cen k‖ ^ 2)
    (h2 : ‖x - cen k‖ ^ 2 ≤ 1 / 100) : x ∈ closure domain := by
  rcases lt_or_eq_of_le h1 with h1 | h1
  · exact subset_closure (mem_domain_of_near h1 h2)
  -- on the hole circle, approach radially from outside
  set z := cen k
  have ht : Tendsto (fun t : ℝ ↦ z + (1 + t) • (x - z)) (𝓝[>] 0) (𝓝 x) := by
    have : Continuous fun t : ℝ ↦ z + (1 + t) • (x - z) := by fun_prop
    have h := this.tendsto 0
    simp only [add_zero, one_smul, add_sub_cancel] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hn : ‖z + (1 + t) • (x - z) - z‖ ^ 2 = (1 + t) ^ 2 * (1 / 400) := by
    rw [add_sub_cancel_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← h1]
  refine mem_domain_of_near (k := k) ?_ ?_ <;> rw [hn] <;> nlinarith [ht.1, ht.2]

/-- `gSub = c` on each hole circle. -/
theorem gSub_on_circle {k : ℤ} {x : E 2} (h : ‖x - cen k‖ ^ 2 = 1 / 400) : gSub x = cst := by
  obtain ⟨j, hj⟩ := exists_fin_cen_eq k
  rw [← hj] at h
  obtain ⟨-, h0⟩ := geom_disc (x := x) (k := j) (by rw [h]; norm_num)
  rw [gSub_eq, (qSum_of_disc (x := x) (k := j) (by rw [h]; norm_num)).1, qIn_of_circle h,
    (qLayer_floor (x := x) (by linarith)).1]
  ring

/-! ### Comparison -/

/-- **Barrier comparison.** Every `V ∈ 𝒮_{gSub}` lies above the barrier `Φ_θ` around `z_k` on
the annulus `{r ≤ |x - z_k| ≤ a - θ}`. -/
theorem barrier_le_of_mem {V : E 2 → ℝ} (hV : V ∈ perronSuperClass domain (fun _ ↦ 1) gSub)
    (k : ℤ) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1 / 20) {y : E 2}
    (hy1 : 1 / 400 ≤ ‖y - cen k‖ ^ 2) (hy2 : ‖y - cen k‖ ^ 2 ≤ barR θ ^ 2) :
    barrier (cen k) θ y ≤ V y := by
  set z := cen k with hz
  obtain ⟨hR1, hR2⟩ := barR_bounds hθ hθ'
  have hR2' : barR θ ^ 2 ≤ 1 / 100 := by nlinarith
  set K := {y : E 2 | 1 / 400 ≤ ‖y - z‖ ^ 2 ∧ ‖y - z‖ ^ 2 ≤ barR θ ^ 2} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · simp only [hK, Set.ofPred_and]
      exact (isClosed_le continuous_const (by fun_prop)).inter
        (isClosed_le (by fun_prop) continuous_const)
    · refine (Metric.isBounded_closedBall (x := z) (r := 1)).subset fun w hw ↦ ?_
      rw [mem_closedBall, dist_eq_norm]
      nlinarith [hw.2, norm_nonneg (w - z)]
  have hKcl : K ⊆ closure domain := fun w hw ↦ mem_closure_of_near hw.1 (hw.2.trans hR2')
  have hF : ContinuousOn (fun w ↦ barrier z θ w - V w) K :=
    ((contDiff_barrier z θ).continuous.continuousOn).sub (hV.1.mono hKcl)
  obtain ⟨m, hmK, hmax⟩ := hKc.exists_isMaxOn ⟨y, hy1, hy2⟩ hF
  by_contra hcon
  push Not at hcon
  have hpos : 0 < barrier z θ m - V m :=
    lt_of_lt_of_le (sub_pos.2 hcon) (hmax ⟨hy1, hy2⟩)
  have hVg : ∀ w ∈ closure domain, max (gSub w) 0 ≤ V w := hV.2.2
  rcases eq_or_lt_of_le hmK.1 with hin | hin
  · -- the inner circle
    have h1 := hVg m (hKcl hmK)
    rw [gSub_on_circle hin.symm] at h1
    have h2 := barrier_le_cst hθ hθ' hin.symm
    linarith [le_max_left cst 0]
  rcases eq_or_lt_of_le hmK.2 with hout | hout
  · -- the outer circle
    have := hVg m (hKcl hmK)
    rw [barrier_outer hθ hθ' hout] at hpos
    linarith [le_max_right (gSub m) 0]
  -- an interior maximum: `Φ_θ - max` touches `V` from below
  set M := barrier z θ m - V m with hM
  have hmU : m ∈ domain := mem_domain_of_near hin (hmK.2.trans hR2')
  have hnhds : K ∈ 𝓝 m := by
    refine Filter.mem_of_superset ((isOpen_gt_normsq z (1 / 400)).inter
      (isOpen_lt_normsq z (barR θ ^ 2)) |>.mem_nhds ⟨hin, hout⟩) ?_
    rintro w ⟨h1, h2⟩
    exact ⟨le_of_lt h1, le_of_lt h2⟩
  refine IsViscSuper.false_of_touch_contDiff_two (Φ := fun w ↦ barrier z θ w - M) two_pos
    isOpen_domain hV.2.1 hmU ((contDiff_barrier z θ).sub contDiff_const) ?_ (by rw [hM]; ring) ?_ ?_
  · filter_upwards [hnhds] with w hw
    have := hmax hw
    simp only [Set.mem_ofPred_eq] at this
    linarith
  · rw [show (fun w ↦ barrier z θ w - M) = fun w ↦ barrier z θ w + (-M) by funext w; ring,
      laplacian_add_const (contDiff_barrier z θ).contDiffAt,
      laplacian_barrier hmK.1 (hmK.2.trans hR2')]
    linarith
  · show (1 : ℝ) < _
    have : ∇ (fun w ↦ barrier z θ w - M) m = ∇ (barrier z θ) m := by
      rw [show (fun w ↦ barrier z θ w - M) = fun w ↦ barrier z θ w + (-M) by
        funext w; ring, gradient_add_const]
    rw [this]
    exact norm_gradient_barrier hθ hθ' hmK.1 hmK.2

/-- **The lower bound.** Every `V ∈ 𝒮_{gSub}` lies above the disc piece `w_k` on
`{r ≤ |x - z_k| < a}`. -/
theorem wIn_le_of_mem_perronSuperClass {V : E 2 → ℝ}
    (hV : V ∈ perronSuperClass domain (fun _ ↦ 1) gSub) (k : ℤ) {y : E 2}
    (hy1 : 1 / 400 ≤ ‖y - cen k‖ ^ 2) (hy2 : ‖y - cen k‖ ^ 2 < 1 / 100) : wIn (cen k) y ≤ V y := by
  set z := cen k with hz
  set τ := ‖y - z‖ ^ 2 with hτ
  have hs : ‖y - z‖ < 1 / 10 := by nlinarith [norm_nonneg (y - z)]
  -- the barriers at `y` converge to `w(y)` as `θ → 0⁺`
  set f : ℝ → ℝ := fun θ ↦ barB θ * ((Real.log (1 / 100) - Real.log τ) / 2 +
      Real.log (10 * barR θ)) + θ * (τ - barR θ ^ 2) with hf
  have hcont : ContinuousAt f 0 := by
    have hl : ContinuousAt (fun θ : ℝ ↦ Real.log (10 * barR θ)) 0 := by
      refine ContinuousAt.log (by unfold barR; fun_prop) ?_
      unfold barR; norm_num
    unfold barB barR at *
    exact ((continuousAt_id.const_sub _).add ((continuousAt_const.mul continuousAt_id).mul
      ((continuousAt_id.const_sub _).pow 2))).mul (continuousAt_const.add hl) |>.add
      (continuousAt_id.mul (continuousAt_const.sub ((continuousAt_id.const_sub _).pow 2)))
  have hf0 : f 0 = wIn z y := by
    have h1 : barB 0 = 1 / 10 := by norm_num [barB, barR]
    have h2 : barR 0 = 1 / 10 := by norm_num [barR]
    rw [hf]; dsimp only
    rw [h1, h2, show (10 : ℝ) * (1 / 10) = 1 by norm_num, Real.log_one, wIn_eq hy1 hy2.le]
    ring
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 (wIn z y)) := by
    rw [← hf0]; exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  have hgap : 0 < 1 / 10 - ‖y - z‖ := by linarith
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (1 / 20) (1 / 10 - ‖y - z‖) by positivity)]
    with θ hθ
  have hθ' : θ < 1 / 20 := lt_of_lt_of_le hθ.2 (min_le_left _ _)
  have hθ'' : θ < 1 / 10 - ‖y - z‖ := lt_of_lt_of_le hθ.2 (min_le_right _ _)
  have hyR : τ ≤ barR θ ^ 2 := by
    rw [hτ]; unfold barR
    have : ‖y - z‖ ≤ 1 / 10 - θ := by linarith
    nlinarith [norm_nonneg (y - z)]
  have := barrier_le_of_mem hV k hθ.1 hθ' hy1 hyR
  rwa [barrier_eq hy1 hy2.le] at this

/-- `u_min ≥ w_k` on `{r ≤ |x - z_k| < a}`. -/
theorem wIn_le_perronSmallest (k : ℤ) {y : E 2}
    (hy1 : 1 / 400 ≤ ‖y - cen k‖ ^ 2) (hy2 : ‖y - cen k‖ ^ 2 < 1 / 100) :
    wIn (cen k) y ≤ uMin y := by
  unfold uMin perronSmallest
  exact le_csInf (perronSuperClass_nonempty.image _)
    (by rintro _ ⟨V, hV, rfl⟩; exact wIn_le_of_mem_perronSuperClass hV k hy1 hy2)

/-- `u_min > 0` on `{r ≤ |x - z_k| < a}`. -/
theorem perronSmallest_pos (k : ℤ) {y : E 2}
    (hy1 : 1 / 400 ≤ ‖y - cen k‖ ^ 2) (hy2 : ‖y - cen k‖ ^ 2 < 1 / 100) : 0 < uMin y :=
  lt_of_lt_of_le (wIn_pos hy1 hy2) (wIn_le_perronSmallest k hy1 hy2)

/-! ### `u_min = v` inside the outer layer -/

/-- **`u_min = v` on `U ∩ B̄_{ρ_o}(0)`.** In particular `u_min = (w_k)₊` on `B̄_a(z_k) ∩ U` and
`u_min = 0` off the discs. -/
theorem perronSmallest_eq_vSup_near {y : E 2} (hy : y ∈ domain)
    (h0 : ‖y - 0‖ ^ 2 ≤ layerRad ^ 2) : uMin y = vSup y := by
  refine le_antisymm (perronSmallest_le_vSup (subset_closure hy)) ?_
  obtain ⟨-, hk⟩ := normSq_of_mem_domain hy
  have hnn := perronSmallest_nonneg perronSuperClass_nonempty (subset_closure hy)
  rw [vSup_eq, max_hLayer_eq_zero h0, add_zero]
  by_cases A : ∃ k : Fin numHoles, ‖y - cen ((k : ℕ) : ℤ)‖ ^ 2 < 1 / 100
  · obtain ⟨k, hkA⟩ := A
    rw [wSum_eq_single k (geom_disc hkA.le).1, max_eq_left (wIn_pos (hk k).le hkA).le]
    exact wIn_le_perronSmallest _ (hk k).le hkA
  · push Not at A
    rw [wSum_eq_zero A]
    exact hnn

end PerronVariational.Necklace

end
