/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Appendix.Nondegeneracy
public import PerronVariational.Statements.Intermediate
public import PerronVariational.Statements.Main
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import PerronVariational.Appendix.NondegeneracyLargest
import PerronVariational.Inner.LongTime
import PerronVariational.Main.Corollary2D.Flat
import PerronVariational.Main.Corollary2D.Supersolution
import PerronVariational.Main.Final
import PerronVariational.Main.InnerLargest
import PerronVariational.Main.InnerSmallest
import PerronVariational.Registry.BlowUp
import PerronVariational.Stationary.TwoPlane.Step3
import PerronVariational.Stationary.ViscosityLocal

/-!
# Corollary 1.2: classification of planar blow-ups and the structure theorem

**Corollary 1.2** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's
extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: classification of
blow-ups in the plane
(`blowup_classification`), the structure of the free boundary for downward resp. upward
minimizers (`fb_structure_of_downward`, `classical_of_upward`), existence of blow-ups
(`exists_isBlowupLimit`), and `corollary_2d_smallest`, `corollary_2d_largest`.

The cited blow-up results enter through the `Registry` modules: the Weiss monotonicity formula
(G. S. Weiss, *Partial regularity for weak solutions of an elliptic free boundary problem*, Comm.
Partial Differential Equations 23 (1998), 439–455, doi:10.1080/03605309808821352), the
classification of planar homogeneous solutions (D. Jerison, N. Kamburov, *Structure of one-phase
free boundaries in the plane*, Int. Math. Res. Not. IMRN 2016, no. 19, 5922–5987,
doi:10.1093/imrn/rnv339), and ε-regularity (L. A. Caffarelli, *A Harnack inequality approach to
the regularity of free boundaries. I, II*, Rev. Mat. Iberoamericana 3 (1987), 139–162,
doi:10.4171/RMI/47, and Comm. Pure Appl. Math. 42 (1989), 55–78, doi:10.1002/cpa.3160420105;
D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
13 (2011), 223–238, doi:10.4171/IFB/255). The flatness step for largest subsolutions also uses
the inner variational structure, following D. Kriventsov, G. S. Weiss, *Rectifiability, finite
Hausdorff measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl.
Math. 78 (2025), 545–591, doi:10.1002/cpa.22226.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian NNReal RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Corollary2D

variable {d : ℕ}

/-! ### Part 3: classification of blow-ups in the plane -/

section Classification

theorem _root_.PerronVariational.Setting.continuousAt_Q (S : Setting d) {x : E d} (hx : x ∈ S.U) :
    ContinuousAt S.Q x := by
  obtain ⟨K, hK⟩ := S.lip
  exact hK.continuousOn.continuousAt
    (Filter.mem_of_superset (S.isOpen.mem_nhds hx) subset_closure)

theorem _root_.PerronVariational.Setting.Q_pos (S : Setting d) {x : E d} (hx : x ∈ S.U) :
    0 < S.Q x :=
  S.Qmin_pos.trans_le (S.Q_mem x (subset_closure hx)).1

/-- **Blow-up classification at a free boundary point in the plane** (proof sketch of
Corollary 1.2). Let `u` be a viscosity and inner variational solution in `U ⊆ ℝ²`, `x₀` a free
boundary point and `v` a blow-up limit of `u` at `x₀`. Assume that half-plane blow-ups at `x₀`
force `u` to be classical near `x₀` (`hreg`: flatness + ε-regularity) and that `v ≢ 0`
(`hnz`: non-degeneracy). Then either `u` is classical near `x₀`, or `v = α |y · e|` with
`0 < α ≤ Q(x₀)`.

Inputs: the Weiss monotonicity formula (`Registry.blowup_homogeneous`: `v` is `1`-homogeneous and
inner variational with coefficient `Q(x₀)`), the planar classification of Jerison–Kamburov
(`Registry.classification_homogeneous_planar`), and the supersolution test
(`le_of_isBlowupLimit_twoPlane`, via Lemma 2.4). -/
theorem blowup_classification (S : Setting 2) {u χ : E 2 → ℝ} (hvisc : IsViscSolution S.U S.Q u)
    (hinner : IsInnerVarSolution S.U S.Q u χ) {x₀ : E 2} (hx₀ : x₀ ∈ freeBoundary u S.U)
    {v : E 2 → ℝ} (hv : IsBlowupLimit u x₀ v)
    (hreg : ∀ e : E 2, ‖e‖ = 1 → IsBlowupLimit u x₀ (fun y ↦ S.Q x₀ * max ⟪y, e⟫ 0) →
      IsClassicalNear S.U S.Q u x₀)
    (hnz : ∃ y, v y ≠ 0) :
    IsClassicalNear S.U S.Q u x₀ ∨
      ∃ e : E 2, ‖e‖ = 1 ∧ ∃ α : ℝ, 0 < α ∧ α ≤ S.Q x₀ ∧ ∀ y, v y = α * |⟪y, e⟫| := by
  have hxU : x₀ ∈ S.U := hx₀.2
  have hq : 0 < S.Q x₀ := S.Q_pos hxU
  obtain ⟨hhom, χ₀, hinner₀⟩ := Registry.blowup_homogeneous S hinner hx₀ hv
  obtain ⟨e, he, hcases⟩ := Registry.classification_homogeneous_planar hq hinner₀ hhom
  obtain ⟨y₀, hy₀⟩ := hnz
  rcases hcases with ⟨hhalf, -⟩ | ⟨α, hα, htwo, -⟩ | ⟨hzero, -⟩
  · left
    have : v = fun y ↦ S.Q x₀ * max ⟪y, e⟫ 0 := funext hhalf
    exact hreg e he (this ▸ hv)
  · right
    have hαpos : 0 < α := lt_of_le_of_ne hα fun h ↦ hy₀ (by rw [htwo, ← h, zero_mul])
    exact ⟨e, he, α, hαpos, le_of_isBlowupLimit_twoPlane S.isOpen hvisc.1 hxU
      (S.continuousAt_Q hxU) hq.le hv he htwo, htwo⟩
  · exact absurd (hzero y₀) hy₀

/-- **Two-plane blow-ups of local downward minimizers have slope `≥ Q(x₀)`** (Corollary 2.13 and
Proposition 2.14). -/
theorem le_of_downwardMinimizer (S : Setting d) {u : E d → ℝ} (hL : LocallyLipschitzOn S.U u)
    {x₀ : E d} (hxU : x₀ ∈ S.U) {r : ℝ} (hr : 0 < r) (hrU : closedBall x₀ r ⊆ S.U)
    (hmin : IsDownwardMinimizer (ball x₀ r) S.Q u) {v : E d → ℝ} (hv : IsBlowupLimit u x₀ v)
    {e : E d} (he : ‖e‖ = 1) {α : ℝ} (hα : 0 < α) (hvα : ∀ y, v y = α * |⟪y, e⟫|) :
    S.Q x₀ ≤ α := by
  have hbU : ball x₀ r ⊆ S.U := ball_subset_closedBall.trans hrU
  obtain ⟨K, hK⟩ := S.lip
  have hQc : ContinuousOn S.Q (ball x₀ r) :=
    hK.continuousOn.mono (hbU.trans subset_closure)
  have hQb : ∀ y ∈ ball x₀ r, |S.Q y| ≤ S.Qmax := fun y hy ↦ by
    have := S.Q_mem y (subset_closure (hbU hy))
    rw [abs_le]; constructor <;> linarith [S.Qmin_pos]
  have hmin' := DirectionalStable.blowup_isDownwardMinimizer isOpen_ball hQc hQb
    (hL.mono hbU) (mem_ball_self hr) hmin hv
  have : v = twoPlane α e := funext fun y ↦ by rw [hvα y, twoPlane]
  rw [this] at hmin'
  exact (twoPlane_downwardMinimizer_iff hα (S.Q_pos hxU) he).1 hmin'

/-- **Two-plane blow-ups are excluded for local upward minimizers** (Corollary 2.13 and
Proposition 2.14). -/
theorem false_of_upwardMinimizer (S : Setting d) {u : E d → ℝ} (hL : LocallyLipschitzOn S.U u)
    {x₀ : E d} {r : ℝ} (hr : 0 < r) (hrU : closedBall x₀ r ⊆ S.U)
    (hmin : IsUpwardMinimizer (ball x₀ r) S.Q u) {v : E d → ℝ} (hv : IsBlowupLimit u x₀ v)
    {e : E d} (he : ‖e‖ = 1) {α : ℝ} (hα : 0 < α) (hvα : ∀ y, v y = α * |⟪y, e⟫|) : False := by
  have hbU : ball x₀ r ⊆ S.U := ball_subset_closedBall.trans hrU
  obtain ⟨K, hK⟩ := S.lip
  have hQc : ContinuousOn S.Q (ball x₀ r) :=
    hK.continuousOn.mono (hbU.trans subset_closure)
  have hQb : ∀ y ∈ ball x₀ r, |S.Q y| ≤ S.Qmax := fun y hy ↦ by
    have := S.Q_mem y (subset_closure (hbU hy))
    rw [abs_le]; constructor <;> linarith [S.Qmin_pos]
  have hmin' := DirectionalStable.blowup_isUpwardMinimizer' isOpen_ball hQc hQb
    (hL.mono hbU) (mem_ball_self hr) hmin hv
  have : v = twoPlane α e := funext fun y ↦ by rw [hvα y, twoPlane]
  rw [this] at hmin'
  exact twoPlane_not_upwardMinimizer hα he _ hmin'

/-- **Half-plane blow-ups give classical points** under uniform non-degeneracy: flatness
(`flat_of_halfPlane_blowup`) and ε-regularity (`Registry.isClassicalNear_of_flat`). -/
theorem isClassicalNear_of_halfPlane (S : Setting d) {u : E d → ℝ}
    (hvisc : IsViscSolution S.U S.Q u) {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u S.U) {e : E d}
    (hflat : ∀ ε > 0, ∃ s, 0 < s ∧ s ≤ ε ∧ ball x₀ s ⊆ S.U ∧ ∀ y ∈ ball x₀ s,
      S.Q x₀ * max (⟪y - x₀, e⟫ - ε * s) 0 ≤ u y ∧ u y ≤ S.Q x₀ * max (⟪y - x₀, e⟫ + ε * s) 0)
    (he : ‖e‖ = 1) : IsClassicalNear S.U S.Q u x₀ := by
  obtain ⟨εbar, hεbar, hR15⟩ := Registry.isClassicalNear_of_flat S
  obtain ⟨s, hs, hsε, hsU, hfl⟩ := hflat εbar hεbar
  exact hR15 u x₀ e s hvisc hx₀ he hs hsε hsU hfl

end Classification

/-! ### Part 4: Corollary 1.2 -/

section Corollary

/-- **Corollary 1.2(i), abstract form.** Let `u` in `U ⊆ ℝ²` be a viscosity and inner variational
solution which is a downward minimizer of `J_Q` near each free boundary point and uniformly
non-degenerate near each free boundary point. Then the free boundary splits into the relatively
open set `FB_reg` of classical points and the set `FB_TP` at which every blow-up is
`Q(x₀) |y · e|`. -/
theorem fb_structure_of_downward (S : Setting 2) {u χ : E 2 → ℝ}
    (hvisc : IsViscSolution S.U S.Q u) (hinner : IsInnerVarSolution S.U S.Q u χ)
    (hdown : ∀ x ∈ freeBoundary u S.U, ∃ r > 0, closedBall x r ⊆ S.U ∧
      IsDownwardMinimizer (ball x r) S.Q u)
    (hnd : ∀ x ∈ freeBoundary u S.U, IsUniformlyNondegenerateNear S.U u x) :
    ∃ FBreg FBtp : Set (E 2),
      Disjoint FBreg FBtp ∧
      FBreg ∪ FBtp = freeBoundary u S.U ∧
      (∃ O : Set (E 2), IsOpen O ∧ FBreg = O ∩ freeBoundary u S.U) ∧
      (∀ x₀ ∈ FBreg, IsClassicalNear S.U S.Q u x₀) ∧
      ∀ x₀ ∈ FBtp, ∀ v : E 2 → ℝ, IsBlowupLimit u x₀ v →
        ∃ e : E 2, ‖e‖ = 1 ∧ ∀ y, v y = S.Q x₀ * |⟪y, e⟫| := by
  set FB := freeBoundary u S.U
  set FBreg := {x ∈ FB | IsClassicalNear S.U S.Q u x}
  refine ⟨FBreg, FB \ FBreg, disjoint_sdiff_right, union_diff_cancel (sep_subset _ _),
    ⟨{x | IsClassicalNear S.U S.Q u x}, isOpen_setOf_isClassicalNear _ _ _, ?_⟩,
    fun x hx ↦ hx.2, ?_⟩
  · ext x; simp [FBreg, and_comm]
  rintro x₀ ⟨hx₀, hreg⟩ v hv
  have hxU : x₀ ∈ S.U := hx₀.2
  have hxcl : x₀ ∈ closure (posSet u S.U) := frontier_subset_closure hx₀.1
  rcases blowup_classification S hvisc hinner hx₀ hv
      (fun e he hhalf ↦ isClassicalNear_of_halfPlane S hvisc hx₀
        (fun ε hε ↦ flat_of_halfPlane_blowup S.isOpen hvisc.1.2.1 hxU (hnd x₀ hx₀)
          (S.Q_pos hxU) he hhalf hε) he)
      (exists_ne_zero_of_isBlowupLimit ((hnd x₀ hx₀).isNondegenerateAt hxcl) hv) with
    hcl | ⟨e, he, α, hα, hαQ, hvα⟩
  · exact absurd ⟨hx₀, hcl⟩ hreg
  · obtain ⟨r, hr, hrU, hmin⟩ := hdown x₀ hx₀
    have hQα := le_of_downwardMinimizer S hinner.locLip hxU hr hrU hmin hv he hα hvα
    exact ⟨e, he, fun y ↦ by rw [hvα y, le_antisymm hαQ hQα]⟩

/-- **Corollary 1.2(ii), abstract form.** Let `u` in `U ⊆ ℝ²` be a viscosity and inner variational
solution which is an upward minimizer of `J_Q` near each free boundary point, whose blow-ups at
free boundary points do not vanish identically, and at whose free boundary points half-plane
blow-ups give classical points. Then `u` is classical near every free boundary point. -/
theorem classical_of_upward (S : Setting 2) {u χ : E 2 → ℝ}
    (hvisc : IsViscSolution S.U S.Q u) (hinner : IsInnerVarSolution S.U S.Q u χ)
    (hup : ∀ x ∈ freeBoundary u S.U, ∃ r > 0, closedBall x r ⊆ S.U ∧
      IsUpwardMinimizer (ball x r) S.Q u)
    (hnd : ∀ x ∈ freeBoundary u S.U, IsNondegenerateAt u x)
    (hreg : ∀ x₀ ∈ freeBoundary u S.U, ∀ e : E 2, ‖e‖ = 1 →
      IsBlowupLimit u x₀ (fun y ↦ S.Q x₀ * max ⟪y, e⟫ 0) → IsClassicalNear S.U S.Q u x₀)
    (hex : ∀ x₀ ∈ freeBoundary u S.U, ∃ v, IsBlowupLimit u x₀ v) :
    ∀ x₀ ∈ freeBoundary u S.U, IsClassicalNear S.U S.Q u x₀ := by
  intro x₀ hx₀
  obtain ⟨v, hv⟩ := hex x₀ hx₀
  rcases blowup_classification S hvisc hinner hx₀ hv (hreg x₀ hx₀)
      (exists_ne_zero_of_isBlowupLimit (hnd x₀ hx₀) hv) with hcl | ⟨e, he, α, hα, -, hvα⟩
  · exact hcl
  · obtain ⟨r, hr, hrU, hmin⟩ := hup x₀ hx₀
    exact (false_of_upwardMinimizer S hinner.locLip hr hrU hmin hv he hα hvα).elim


/-- **Existence of blow-up limits** (Arzelà–Ascoli; proof sketch of Corollary 1.2). If `u` is
locally Lipschitz in `U` and vanishes at `x₀ ∈ U`, then `u` has a blow-up limit at `x₀`. -/
theorem exists_isBlowupLimit {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hL : LocallyLipschitzOn U u) {x₀ : E d} (hx₀ : x₀ ∈ U) (hu0 : u x₀ = 0) :
    ∃ v, IsBlowupLimit u x₀ v := by
  obtain ⟨L, t, ht, hLt⟩ := hL hx₀
  obtain ⟨ρ, hρ, hρt⟩ := Metric.mem_nhdsWithin_iff.1 ht
  obtain ⟨ρ', hρ', hρU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set δ := min ρ ρ' / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδS : closedBall x₀ δ ⊆ t := fun y hy ↦ by
    have hm : 0 < min ρ ρ' := lt_min hρ hρ'
    have h1 : dist y x₀ < min ρ ρ' := (mem_closedBall.1 hy).trans_lt (by rw [hδ]; linarith)
    exact hρt ⟨mem_ball.2 (h1.trans_le (min_le_left _ _)),
      hρU (mem_ball.2 (h1.trans_le (min_le_right _ _)))⟩
  set r : ℕ → ℝ := fun n ↦ δ / ((n : ℝ) + 1) with hr_def
  have hr : ∀ n, 0 < r n := fun n ↦ by positivity
  have hr0 : Tendsto r atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hmem : ∀ n : ℕ, ∀ a ∈ closedBall (0 : E d) ((n : ℝ) + 1),
      x₀ + r n • a ∈ closedBall x₀ δ := by
    intro n a ha
    rw [mem_closedBall, dist_zero_right] at ha
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hr n), hr_def]
    calc δ / ((n : ℝ) + 1) * ‖a‖ ≤ δ / ((n : ℝ) + 1) * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left ha (hr n).le
      _ = δ := by field_simp
  have hLn : ∀ n : ℕ, LipschitzOnWith L (blowup u x₀ (r n)) (closedBall 0 ((n : ℝ) + 1)) :=
    fun n ↦ LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦
      DirectionalStable.dist_blowup_le (hr n) (hLt.mono hδS) (hmem n a ha) (hmem n b hb)
  choose w hwL hwEq using fun n ↦ (hLn n).extend_real
  have h0mem : ∀ n : ℕ, (0 : E d) ∈ closedBall (0 : E d) ((n : ℝ) + 1) := fun n ↦
    mem_closedBall_self (by positivity)
  have hw0 : ∀ n, w n 0 = 0 := fun n ↦ by
    rw [← hwEq n (h0mem n)]
    simp [blowup, hu0]
  -- the compact set of `L`-Lipschitz functions vanishing at `0`
  set K : Set C(E d, ℝ) := {f | LipschitzWith L f ∧ f 0 = 0} with hK
  have himg : ContinuousMap.toFun '' K = {f : E d → ℝ | LipschitzWith L f ∧ f 0 = 0} := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩; exact hg
    · intro hf; exact ⟨⟨f, hf.1.continuous⟩, hf, rfl⟩
  have hS1 : IsCompact (ContinuousMap.toFun '' K) := by
    rw [himg]
    have hbox : IsCompact (Set.pi univ fun y : E d ↦ Icc (-(L * ‖y‖)) (L * ‖y‖)) :=
      isCompact_univ_pi fun _ ↦ isCompact_Icc
    refine hbox.of_isClosed_subset ?_ ?_
    · have h1 : {f : E d → ℝ | LipschitzWith L f} =
          ⋂ x : E d, ⋂ y : E d, {f : E d → ℝ | dist (f x) (f y) ≤ L * dist x y} := by
        ext f; simp [lipschitzWith_iff_dist_le_mul]
      have h2 : {f : E d → ℝ | LipschitzWith L f ∧ f 0 = 0} =
          {f : E d → ℝ | LipschitzWith L f} ∩ {f | f 0 = 0} := rfl
      rw [h2, h1]
      refine (isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_).inter
        (isClosed_eq (continuous_apply 0) continuous_const)
      exact isClosed_le ((continuous_apply x).dist (continuous_apply y)) continuous_const
    · rintro f ⟨hfL, hf0⟩ y -
      have := hfL.dist_le_mul y 0
      rw [hf0, dist_zero_right, dist_zero_right, Real.norm_eq_abs] at this
      exact abs_le.1 this
  have hS2 : Equicontinuous ((↑) : K → E d → ℝ) :=
    (LipschitzWith.uniformEquicontinuous (fun f : K ↦ (f : E d → ℝ)) L fun f ↦ f.2.1).equicontinuous
  have hKc : IsCompact K := ArzelaAscoli.isCompact_of_equicontinuous K hS1 hS2
  set W : ℕ → C(E d, ℝ) := fun n ↦ ⟨w n, (hwL n).continuous⟩ with hW
  obtain ⟨v, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq (x := W) fun n ↦ ⟨hwL n, hw0 n⟩
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly] at hlim
  refine ⟨v, fun n ↦ r (φ n), fun n ↦ hr _, hr0.comp hφ.tendsto_atTop, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hlim ⊢
  intro C hC
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  refine (hlim C hC).congr ?_
  filter_upwards [hφ.tendsto_atTop.eventually (tendsto_natCast_atTop_atTop.eventually_ge_atTop R)]
    with n hn y hy
  have hy' : y ∈ closedBall (0 : E d) ((φ n : ℕ) + 1) :=
    closedBall_subset_closedBall (by linarith) (hR hy)
  exact (hwEq (φ n) hy').symm

/-- A property holding a.e. on `U` holds a.e. along the homothety `y ↦ x₀ + r y`. -/
theorem ae_homothety {U : Set (E d)} (hU : MeasurableSet U) {P : E d → Prop}
    (h : ∀ᵐ x ∂(volume.restrict U), P x) (x₀ : E d) {r : ℝ} (hr : r ≠ 0) :
    ∀ᵐ y : E d, x₀ + r • y ∈ U → P (x₀ + r • y) := by
  rw [ae_restrict_iff' hU, ae_iff] at h
  rw [ae_iff]
  have : {y : E d | ¬(x₀ + r • y ∈ U → P (x₀ + r • y))} =
      (fun y ↦ r • y) ⁻¹' ((fun x ↦ x₀ + x) ⁻¹' {x | ¬(x ∈ U → P x)}) := rfl
  rw [this, Measure.addHaar_preimage_smul _ hr, measure_preimage_add, h, mul_zero]

/-- Precomposition of a locally uniformly convergent sequence with a subsequence. -/
theorem tendstoLocallyUniformly_comp_strictMono {F : ℕ → E d → ℝ} {f : E d → ℝ}
    (h : TendstoLocallyUniformly F f atTop) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoLocallyUniformly (fun n ↦ F (φ n)) f atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at h ⊢
  intro K hK
  have hK' := h K hK
  rw [Metric.tendstoUniformlyOn_iff] at hK' ⊢
  intro δ hδ
  exact hφ.tendsto_atTop.eventually (hK' δ hδ)

/-- **Excluding a positive far side** (largest case, third step of the flatness argument). Let
`(u, χ)` be an inner variational solution in `U ⊆ ℝ²` and `x₀` a free boundary point where the
blow-ups along `r_n` converge to the half-plane solution `Q(x₀) (y · e)₊`. Then `u` cannot be
positive on the far regions `{(y - x₀) · e < -ε r_n / 4} ∩ B_{r_n/2}(x₀)` for infinitely many `n`:
otherwise `χ = 1` there, and the `L¹_loc` limit `χ₀` of the rescaled `χ`
(`Registry.blowup_homogeneous_seq`) would be `1` on `{y · e < -ε/4} ∩ B_{1/2}`, while the planar
classification forces `χ₀ = 1_{y · e > 0}`. -/
theorem not_frequently_pos_far (S : Setting 2) {u χ : E 2 → ℝ}
    (hinner : IsInnerVarSolution S.U S.Q u χ) {x₀ : E 2} (hx₀ : x₀ ∈ freeBoundary u S.U)
    {e : E 2} (he : ‖e‖ = 1) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hconv : TendstoLocallyUniformly (fun n ↦ blowup u x₀ (r n))
      (fun y ↦ S.Q x₀ * max ⟪y, e⟫ 0) atTop) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ¬ ∃ᶠ n in atTop, ball x₀ (r n / 2) ⊆ S.U ∧
      ∀ y ∈ ball x₀ (r n / 2), ⟪y - x₀, e⟫ < -(ε / 4) * r n → 0 < u y := by
  intro hfreq
  obtain ⟨ψ, hψ, hψP⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hq : 0 < S.Q x₀ := S.Qmin_pos.trans_le (S.Q_mem x₀ (subset_closure hx₀.2)).1
  obtain ⟨hhom, φ, χ₀, hφ, hLp, hsol⟩ := Registry.blowup_homogeneous_seq S hinner hx₀
    (r := fun n ↦ r (ψ n)) (fun n ↦ hr _) (hr0.comp hψ.tendsto_atTop)
    (tendstoLocallyUniformly_comp_strictMono hconv hψ)
  set h : E 2 → ℝ := fun y ↦ S.Q x₀ * max ⟪y, e⟫ 0 with hh
  set R : Set (E 2) := {y | ⟪y, e⟫ < -(ε / 4)} ∩ ball 0 (1 / 2) with hR
  have hRmeas : MeasurableSet R :=
    (measurableSet_lt (measurable_id.inner measurable_const) measurable_const).inter
      measurableSet_ball
  -- `χ₀ = 0` a.e. on `R`
  have hχ₀ : ∀ᵐ y ∂(volume.restrict R), χ₀ y = 0 := by
    have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    obtain ⟨e', -, halt⟩ := Registry.classification_homogeneous_planar hq hsol hhom
    rcases halt with ⟨hv, hχ⟩ | ⟨α, -, hv, -⟩ | ⟨hv, -⟩
    · refine (ae_restrict_iff' hRmeas).2 (hχ.mono fun y hy hyR ↦ ?_)
      rw [hy, indicator_of_notMem]
      have h1 := hv y
      have hye : ⟪y, e⟫ ≤ 0 := by
        have := hyR.1; simp only [mem_setOf_eq] at this; linarith
      simp only [hh, max_eq_right hye] at h1
      have : max ⟪y, e'⟫ 0 = 0 := (mul_left_cancel₀ hq.ne' h1).symm
      simp only [mem_setOf_eq, not_lt]
      exact (le_max_left _ _).trans this.le
    · exfalso
      have h1 := hv e
      have h2 := hv (-e)
      simp only [hh, hee, inner_neg_left, abs_neg] at h1 h2
      rw [max_eq_left zero_le_one, mul_one] at h1
      rw [max_eq_right (by norm_num), mul_zero] at h2
      linarith
    · exfalso
      have h1 := hv e
      simp only [hh, hee, max_eq_left zero_le_one, mul_one] at h1
      linarith
  -- `χ(x₀ + r_k y) = 1` a.e. on `R`
  have hf : ∀ k, ∀ᵐ y ∂(volume.restrict R), χ (x₀ + r (ψ (φ k)) • y) = 1 := by
    intro k
    set ρ := r (ψ (φ k))
    have hρ : 0 < ρ := hr _
    obtain ⟨hballU, hpos⟩ := hψP (φ k)
    have hae := ae_homothety S.isOpen.measurableSet hinner.pos_le x₀ hρ.ne'
    refine (ae_restrict_iff' hRmeas).2 (hae.mono fun y hy hyR ↦ ?_)
    have hyb : x₀ + ρ • y ∈ ball x₀ (ρ / 2) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hρ]
      have := mem_ball_zero_iff.1 hyR.2
      nlinarith
    refine hy (hballU hyb) (hpos _ hyb ?_)
    rw [add_sub_cancel_left, inner_smul_left]
    simp only [conj_trivial]
    have := hyR.1
    simp only [mem_setOf_eq] at this
    nlinarith
  -- the `L¹` distance on `R` is constant, equal to `|R| > 0`, and tends to `0`
  have hLpK := hLp (closedBall 0 1) (subset_univ _) (isCompact_closedBall _ _)
  have hconst : ∀ k, eLpNorm ((fun y ↦ χ (x₀ + r (ψ (φ k)) • y)) - χ₀) 1
      (volume.restrict R) = volume R := by
    intro k
    rw [eLpNorm_congr_ae (g := fun _ ↦ (1 : ℝ)) (by
      filter_upwards [hf k, hχ₀] with y h1 h2
      simp [h1, h2]), eLpNorm_one_eq_lintegral_enorm]
    simp
  have hRsub : R ⊆ closedBall 0 1 := fun y hy ↦
    ball_subset_closedBall (ball_subset_ball (by norm_num) hy.2)
  have hle : ∀ k, volume R ≤ eLpNorm ((fun y ↦ χ (x₀ + r (ψ (φ k)) • y)) - χ₀) 1
      (volume.restrict (closedBall 0 1)) := fun k ↦ by
    rw [← hconst k]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hRsub le_rfl)
  have h0 : volume R ≤ 0 := ge_of_tendsto' hLpK hle
  have hRpos : 0 < volume R := by
    refine ((isOpen_lt (continuous_id.inner continuous_const) continuous_const).inter
      isOpen_ball).measure_pos _ ⟨-(3 / 8 : ℝ) • e, ?_, ?_⟩
    · have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
      change ⟪-(3 / 8 : ℝ) • e, e⟫ < -(ε / 4)
      rw [real_inner_smul_left, hee]
      linarith
    · rw [mem_ball_zero_iff, norm_smul, he]; norm_num
  exact absurd h0 (not_le.2 hRpos)

/-- **The flatness step for largest subsolutions** (proof sketch of Corollary 1.2(ii)). If some
blow-up of the largest subsolution at a free boundary point `x₀` is the half-plane solution
`Q(x₀) (y · e)₊`, then `u` is `ε`-flat in arbitrarily small balls around `x₀`. The paper applies
ε-regularity directly after the blow-up; but locally uniform convergence gives only the lower half
of the flatness condition, and Theorem B.1 (non-degeneracy at free boundary points only) does not by
itself give `u = 0` on `{(y - x₀) · e < -ε s}`. Here we add the missing step: by Theorem B.1 there
are no free boundary points on the far side, so `u` vanishes identically or nowhere there
(`flat_or_pos_of_halfPlane_blowup`); the second alternative is excluded by the inner variational
structure, the sequence form of the Weiss blow-up result and the planar classification
(`not_frequently_pos_far`). -/
theorem perronLargest_flat_of_halfPlane (S : Setting 2) {g : E 2 → ℝ}
    (hg : IsStrictSuper S.U S.Q g) {x₀ : E 2}
    (hx₀ : x₀ ∈ freeBoundary (perronLargest S.U S.Q g) S.U) {e : E 2} (he : ‖e‖ = 1)
    (hv : IsBlowupLimit (perronLargest S.U S.Q g) x₀ fun y ↦ S.Q x₀ * max ⟪y, e⟫ 0) :
    ∀ ε > 0, ∃ s, 0 < s ∧ s ≤ ε ∧ ball x₀ s ⊆ S.U ∧ ∀ y ∈ ball x₀ s,
      S.Q x₀ * max (⟪y - x₀, e⟫ - ε * s) 0 ≤ perronLargest S.U S.Q g y ∧
        perronLargest S.U S.Q g y ≤ S.Q x₀ * max (⟪y - x₀, e⟫ + ε * s) 0 := by
  intro ε hε
  have h62 := inner_largest_of parabolic_existence_bdd longtime_innerVar
  obtain ⟨-, ⟨χ, hinner⟩, -⟩ := h62 2 S g hg
  have hnd := S.perronLargest_nondegenerate_near_fb h62 hg hx₀
  obtain ⟨r, hr, hr0, hconv⟩ := hv
  have hq : 0 < S.Q x₀ := S.Qmin_pos.trans_le (S.Q_mem x₀ (subset_closure hx₀.2)).1
  have hε' : 0 < min ε 1 := lt_min hε one_pos
  have hev := flat_or_pos_of_halfPlane_blowup S.isOpen hinner.nonneg hx₀.2 hnd hq he hr hr0
    hconv hε' (min_le_right _ _)
  have hnot := not_frequently_pos_far S hinner hx₀ he hr hr0 hconv hε' (min_le_right _ _)
  rw [Filter.not_frequently] at hnot
  obtain ⟨n, ⟨hsε, hU, hflat | hpos⟩, hnp⟩ := (hev.and hnot).exists
  · refine ⟨r n / 2, by linarith [hr n], hsε.trans (min_le_left _ _), hU,
      fun y hy ↦ ⟨?_, ?_⟩⟩
    · have hm : min ε 1 * (r n / 2) ≤ ε * (r n / 2) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith [hr n])
      refine le_trans ?_ (hflat y hy).1
      exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hq.le
    · have hm : min ε 1 * (r n / 2) ≤ ε * (r n / 2) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith [hr n])
      refine (hflat y hy).2.trans ?_
      exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hq.le
  · exact absurd ⟨hU, hpos⟩ hnp

end Corollary

end Corollary2D

open Corollary2D

/-- **Corollary 1.2(i)**, from Theorem 1.1 (smallest case), Proposition 6.1 (continuity on `Ū`)
and the non-degeneracy of smallest supersolutions.

The paper's proof sketch excludes two-plane blow-ups `α |y · e|` with `α > Q(x₀)` (supersolution
test) and with `0 < α < Q(x₀)` (Proposition 2.14), but not the degenerate blow-up `0`. Here `0` is
excluded by the uniform non-degeneracy of Perron's smallest supersolution
(`Setting.perronSmallest_uniformlyNondegenerate`, a radial barrier together with Lemma 2.7). -/
theorem corollary_2d_smallest_of (hmain : MainSmallestStatement) (h61 : InnerSmallestStatement) :
    Corollary2DSmallestStatement := by
  intro S g hg hbdry
  obtain ⟨hvisc, ⟨χ, hinner⟩, hdown⟩ := hmain 2 S g hg hbdry
  obtain ⟨-, -, hcont⟩ := h61 2 S g hg hbdry
  exact fb_structure_of_downward S hvisc hinner hdown fun x hx ↦
    S.perronSmallest_uniformlyNondegenerate hg hvisc.1 hcont hx

/-- **Corollary 1.2(i)**. -/
theorem corollary_2d_smallest : Corollary2DSmallestStatement :=
  corollary_2d_smallest_of main_smallest
    (inner_smallest_of parabolic_existence_bdd longtime_innerVar)


/-- **Theorem B.1** for Perron's largest subsolution. -/
theorem largestSub_nondegenerate : LargestSubNondegenerateStatement :=
  largestSub_nondegenerate_of (inner_largest_of parabolic_existence_bdd longtime_innerVar)

/-- **Corollary 1.2(ii)**, from Theorem 1.1 (largest case) and Theorem B.1. -/
theorem corollary_2d_largest_of (hmain : MainLargestStatement)
    (hB1 : LargestSubNondegenerateStatement) : Corollary2DLargestStatement := by
  intro S g hg
  obtain ⟨hvisc, ⟨χ, hinner⟩, hup⟩ := hmain 2 S g hg
  refine classical_of_upward S hvisc hinner hup (hB1 S g hg) (fun x₀ hx₀ e he hhalf ↦
    isClassicalNear_of_halfPlane S hvisc hx₀ (perronLargest_flat_of_halfPlane S hg hx₀ he hhalf)
      he) fun x₀ hx₀ ↦ exists_isBlowupLimit S.isOpen hinner.locLip hx₀.2
      (eq_zero_of_mem_freeBoundary S.isOpen hvisc.1.1 hvisc.1.2.1 hx₀)

/-- **Corollary 1.2(ii)**. -/
theorem corollary_2d_largest : Corollary2DLargestStatement :=
  corollary_2d_largest_of main_largest largestSub_nondegenerate

end PerronVariational

end
