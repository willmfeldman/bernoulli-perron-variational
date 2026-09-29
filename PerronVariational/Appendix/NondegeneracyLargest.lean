/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Appendix.Nondegeneracy
public import PerronVariational.Appendix.CircleMean
public import PerronVariational.Statements.Intermediate
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Covering.Vitali
import PerronVariational.Appendix.RieszMeasure
import PerronVariational.Main.Theorem
import PerronVariational.Registry.Elliptic
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.Monotone
import PerronVariational.Stationary.ViscosityLocal

/-!
# Theorem B.1: non-degeneracy of largest subsolutions in the plane

**Thm B.1** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper"), due to B.
Orcan-Ekmekci, *On the geometry and regularity of largest subsolutions for a free boundary problem
in ℝ²: elliptic case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3-4, 937–962,
doi:10.1007/s00526-013-0606-8. We follow the sketch of proof given in Appendix B of the paper.

* `le_zero_of_subharmonic_ball`: a weak maximum principle on balls, for functions that are `C²`
  and subharmonic where positive.
* **Lemma B.4** (`exists_notMem_closure_posSet_sphere`): for a local largest subsolution
  `u` with `x₀ ∈ ∂{u > 0}`, every sphere `∂B_t(x₀)` meets the complement of `\overline{{u > 0}}`.
  Proof as in the sketch, via the harmonic lift (solvability of the Dirichlet problem, from the
  dependency viscosity-solution-theory v0.2.0).
* `mass_lower_bound_of_exteriorBall`: Lemma B.2 plus Lemma B.3 at an outer-regular free boundary
  point `y` with exterior ball of radius `s`: `μ(B_{4s}(y)) ≥ c s`.
* `mass_lower_bound_of_covering`: the Vitali covering step. The paper's sketch takes
  `ρ_r = d(x, E)` where `d(x_r, E)` is meant; its Vitali subfamily of intervals
  `(r_j - ρ_j, r_j + ρ_j)` does not give disjoint balls `B_{2ρ_j}(x_{r_j})`; and for `r` near `1`
  these balls leave `B_1`. Here we use the distance from `x_r`, the enlarged intervals
  `(r - 5ρ_r, r + 5ρ_r)`, and radii `r ∈ [T/2, T]` so that all balls stay in `B_{6T}(x₀)`.
* `isNondegenerateAt_of_isLocalLargestSub`: Thm B.1 for local largest subsolutions.
* `largestSub_nondegenerate_of`: Thm B.1 for Perron's largest subsolution, given Prop 6.2.

The Riesz measure `μ = Δu`, which the paper uses without proof, is constructed in
`Appendix/RieszMeasure.lean`.
-/

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Laplacian Real ENNReal NNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### A weak maximum principle -/

/-- **Weak maximum principle on a ball.** Let `w` be continuous on `B̄_t(x₀)`, `w ≤ 0` on
`∂B_t(x₀)`, and `C²` with `Δw ≥ 0` near every point of `B_t(x₀)` where `w > 0`. Then `w ≤ 0`
on `B̄_t(x₀)`. Proof: `w + ε|y - x₀|²` cannot have an interior maximum where `w > 0`. -/
theorem le_zero_of_subharmonic_ball {w : E d → ℝ} {x₀ : E d} {t : ℝ} (hd : 1 ≤ d) (ht : 0 < t)
    (hw : ContinuousOn w (closedBall x₀ t)) (hbd : ∀ y ∈ sphere x₀ t, w y ≤ 0)
    (hsub : ∀ y ∈ ball x₀ t, 0 < w y → ContDiffAt ℝ 2 w y ∧ 0 ≤ Δ w y) :
    ∀ y ∈ closedBall x₀ t, w y ≤ 0 := by
  intro y₁ hy₁
  by_contra hpos
  push Not at hpos
  set ε := w y₁ / (2 * t ^ 2) with hε
  have hεpos : 0 < ε := by positivity
  set q : E d → ℝ := ε • fun y ↦ ‖y - x₀‖ ^ 2 with hq
  have hqy : ∀ y, q y = ε * ‖y - x₀‖ ^ 2 := fun y ↦ rfl
  have hqc : ContDiff ℝ 2 q := contDiff_const.smul (contDiff_normSq_sub_const x₀)
  set wε := w + q with hwε_def
  have hwε : ContinuousOn wε (closedBall x₀ t) := hw.add hqc.continuous.continuousOn
  obtain ⟨ŷ, hŷ, hmax⟩ := (isCompact_closedBall x₀ t).exists_isMaxOn ⟨y₁, hy₁⟩ hwε
  have hqnn : ∀ y, 0 ≤ q y := fun y ↦ by rw [hqy]; positivity
  have hqle : ∀ y ∈ closedBall x₀ t, q y ≤ w y₁ / 2 := fun y hy ↦ by
    rw [hqy]
    have h1 : ‖y - x₀‖ ^ 2 ≤ t ^ 2 := by
      rw [mem_closedBall, dist_eq_norm] at hy
      exact pow_le_pow_left₀ (norm_nonneg _) hy 2
    calc ε * ‖y - x₀‖ ^ 2 ≤ ε * t ^ 2 := by gcongr
      _ = w y₁ / 2 := by rw [hε]; field_simp
  have hŷ1 : w y₁ ≤ wε ŷ := by
    have := hmax hy₁
    simp only [mem_setOf_eq, hwε_def, Pi.add_apply] at this ⊢
    linarith [hqnn y₁]
  have hŷball : ŷ ∈ ball x₀ t := by
    rcases (mem_closedBall.1 hŷ).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hbd ŷ h
      have h2 := hqle ŷ hŷ
      simp only [hwε_def, Pi.add_apply] at hŷ1
      linarith
  have hwŷ : 0 < w ŷ := by
    have h2 := hqle ŷ hŷ
    simp only [hwε_def, Pi.add_apply] at hŷ1
    linarith
  obtain ⟨hC, hΔ⟩ := hsub ŷ hŷball hwŷ
  have hlap : Δ wε ŷ ≤ 0 := by
    have := laplacian_le_of_eventually_le (u := wε) (φ := fun _ ↦ wε ŷ) (hC.add hqc.contDiffAt)
      contDiffAt_const rfl (by
        filter_upwards [isOpen_ball.mem_nhds hŷball] with y hy
        exact hmax (ball_subset_closedBall hy))
    simpa using this
  have hlap2 : Δ wε ŷ = Δ w ŷ + ε * (2 * d) := by
    rw [hwε_def, hC.laplacian_add hqc.contDiffAt, hq,
      InnerProductSpace.laplacian_smul _ (contDiff_normSq_sub_const x₀).contDiffAt,
      laplacian_normSq_sub_const, finrank_euclideanSpace_fin, smul_eq_mul]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

/-! ### Lemma B.4 -/

section LemmaB4

variable {Q u : E 2 → ℝ} {x₀ : E 2} {R : ℝ} {K : ℝ≥0}

/-- **Lemma B.4.** Let `u` be a local largest subsolution in `B_R(x₀)`, Lipschitz, `C²`
and harmonic in `{u > 0}`, with `x₀ ∈ ∂{u > 0}`. Then for `0 < t < R`, the sphere `∂B_t(x₀)`
is not contained in `\overline{{u > 0}}`.

Proof (the paper's sketch, with two details made explicit: `v(x₀) > 0 = u(x₀)` suffices, rather than
`v > u` in the ball, and the subsolution property of the glued function on `∂B_t(x₀)` uses `∂B_t(x₀)
⊆ \overline{{u > 0}}`): otherwise let `h` be the harmonic lift of `u` in `B_t(x₀)` (solvability of
the Dirichlet problem, `Registry.dirichlet_harmonic_modulus`). By the maximum principle `0 ≤ h` and
`u ≤ h` in `B_t(x₀)`. The glued function `v = h` in `B_t(x₀)`, `v = u` outside, is a subsolution:
inside `B_t(x₀)` it is harmonic where positive (and `x ∉ \overline{{v > 0}}` where `h = 0`, by the
strong minimum principle); at the remaining points, `v ≥ u`, `v(x) = u(x)` and `x ∈ \overline{{u >
0}}` (on `∂B_t(x₀)` by the contradiction hypothesis), so touching `v` from above is touching `u`
from above. The largest subsolution property gives `v ≤ u`, so `u = h` in `B_t(x₀)`; then `h(x₀) =
0` and the strong minimum principle give `u ≡ 0` in `B_t(x₀)`, contradicting `x₀ ∈ \overline{{u >
0}}`. -/
theorem exists_notMem_closure_posSet_sphere (hll : IsLocalLargestSub (ball x₀ R) Q u)
    (hLip : LipschitzOnWith K u (ball x₀ R)) (hC2 : ContDiffOn ℝ 2 u (posSet u (ball x₀ R)))
    (hΔ : ∀ y ∈ posSet u (ball x₀ R), Δ u y = 0) (hx₀ : x₀ ∈ freeBoundary u (ball x₀ R))
    {t : ℝ} (ht : 0 < t) (htR : t < R) :
    ∃ y ∈ sphere x₀ t, y ∉ closure (posSet u (ball x₀ R)) := by
  classical
  set Ω := ball x₀ R with hΩ
  set P := posSet u Ω with hP
  by_contra hcon
  push Not at hcon
  have hsub := hll.1
  have hucont : ContinuousOn u Ω := hsub.1
  have hunn : ∀ y ∈ Ω, 0 ≤ u y := hsub.2.1
  have hux₀ : u x₀ = 0 := eq_zero_of_mem_freeBoundary isOpen_ball hucont hunn hx₀
  have hBΩ : closedBall x₀ t ⊆ Ω := closedBall_subset_ball htR
  have hPopen : IsOpen P := hucont.isOpen_inter_preimage isOpen_ball isOpen_Ioi
  -- the harmonic lift (solvability of the Dirichlet problem)
  obtain ⟨ϖ, -, hϖ⟩ := Registry.dirichlet_harmonic_modulus (isOpen_ball (x := x₀) (ε := t))
    isBounded_ball (hasC2Boundary_ball x₀ ht) K (K * t)
  have hcl : closure (ball x₀ t) = closedBall x₀ t := closure_ball x₀ ht.ne'
  have hfr : frontier (ball x₀ t) = sphere x₀ t := frontier_ball x₀ ht.ne'
  obtain ⟨h, hhc, hhC2, hhΔ, hhbd, -⟩ := hϖ u (by rw [hcl]; exact hLip.mono hBΩ) (by
    rw [hcl]
    intro y hy
    have := hLip.dist_le_mul y (hBΩ hy) x₀ (mem_ball_self (ht.trans htR))
    rw [Real.dist_eq, hux₀, sub_zero] at this
    refine this.trans ?_
    gcongr
    exact mem_closedBall.1 hy)
  rw [hcl] at hhc
  rw [hfr] at hhbd
  -- `h ≥ 0`
  have hh0 : ∀ y ∈ closedBall x₀ t, 0 ≤ h y := by
    have := le_zero_of_subharmonic_ball (w := -h) (by norm_num) ht hhc.neg
      (fun y hy ↦ by
        simp only [Pi.neg_apply, neg_nonpos, hhbd y hy]
        exact hunn y (hBΩ (sphere_subset_closedBall hy)))
      (fun y hy _ ↦ ⟨(hhC2.contDiffAt (isOpen_ball.mem_nhds hy)).neg, by
        rw [InnerProductSpace.laplacian_neg, Pi.neg_apply, hhΔ y hy, neg_zero]⟩)
    intro y hy
    have := this y hy
    simp only [Pi.neg_apply, neg_nonpos] at this
    exact this
  -- `u ≤ h`
  have huh : ∀ y ∈ closedBall x₀ t, u y ≤ h y := by
    have := le_zero_of_subharmonic_ball (w := u - h) (by norm_num) ht
      ((hucont.mono hBΩ).sub hhc) (fun y hy ↦ by simp [hhbd y hy]) (fun y hy hpos ↦ by
        have hyP : y ∈ P := ⟨hBΩ (ball_subset_closedBall hy), by
          simp only [Pi.sub_apply, sub_pos] at hpos
          linarith [hh0 y (ball_subset_closedBall hy)]⟩
        have hCu := hC2.contDiffAt (hPopen.mem_nhds hyP)
        have hCh := hhC2.contDiffAt (isOpen_ball.mem_nhds hy)
        refine ⟨hCu.sub hCh, ?_⟩
        rw [hCu.laplacian_sub hCh, hΔ y hyP, hhΔ y hy, sub_self])
    intro y hy
    have := this y hy
    simp only [Pi.sub_apply, sub_nonpos] at this
    exact this
  -- the competitor
  set v := (ball x₀ t).piecewise h u with hv
  have hvu_ge : ∀ y ∈ Ω, u y ≤ v y := fun y _ ↦ by
    by_cases hyB : y ∈ ball x₀ t
    · rw [hv, piecewise_eq_of_mem _ _ _ hyB]; exact huh y (ball_subset_closedBall hyB)
    · rw [hv, piecewise_eq_of_notMem _ _ _ hyB]
  have hvsub : IsViscSub Ω Q v := by
    refine ⟨?_, ?_, ?_⟩
    · refine ContinuousOn.piecewise (fun y hy ↦ ?_) ?_ ?_
      · exact hhbd y (hfr ▸ hy.2)
      · rw [hcl]; exact hhc.mono inter_subset_right
      · exact hucont.mono inter_subset_left
    · intro y hy
      by_cases hyB : y ∈ ball x₀ t
      · rw [hv, piecewise_eq_of_mem _ _ _ hyB]; exact hh0 y (ball_subset_closedBall hyB)
      · rw [hv, piecewise_eq_of_notMem _ _ _ hyB]; exact hunn y hy
    · intro φ hφ x htouch
      obtain ⟨⟨hxcl, hxΩ⟩, hφx, hev⟩ := htouch
      by_cases hxB : x ∈ ball x₀ t
      · have hvx : v x = h x := piecewise_eq_of_mem _ _ _ hxB
        have hδ : 0 < t - dist x x₀ := by linarith [mem_ball.1 hxB]
        have hballsub : ball x (t - dist x x₀) ⊆ ball x₀ t := fun y hy ↦ by
          rw [mem_ball] at hy ⊢; linarith [dist_triangle y x x₀]
        rcases (hh0 x (ball_subset_closedBall hxB)).lt_or_eq with hpos | hzero
        · left
          have hnear : ∀ᶠ y in 𝓝 x, y ∈ ball x₀ t ∧ 0 < h y :=
            (show ∀ᶠ y in 𝓝 x, y ∈ ball x₀ t from isOpen_ball.mem_nhds hxB).and
              ((hhC2.continuousOn.continuousAt
              (isOpen_ball.mem_nhds hxB)).eventually (lt_mem_nhds hpos))
          have hS : ∀ᶠ y in 𝓝 x, y ∈ closure (posSet v Ω) ∩ Ω := by
            filter_upwards [hnear, isOpen_ball.mem_nhds hxΩ] with y hy hyΩ
            refine ⟨subset_closure ⟨hyΩ, ?_⟩, hyΩ⟩
            rw [hv, piecewise_eq_of_mem _ _ _ hy.1]; exact hy.2
          have hev' : ∀ᶠ y in 𝓝 x, v y ≤ max (φ y) 0 := by
            rw [eventually_nhdsWithin_iff] at hev
            filter_upwards [hev, hS] with y hy hyS using hy hyS
          have hφh : h x = φ x := by
            have h1 : max (φ x) 0 = h x := by rw [← hvx]; exact hφx
            rcases le_total (φ x) 0 with h2 | h2
            · rw [max_eq_right h2] at h1; linarith
            · rw [max_eq_left h2] at h1; exact h1.symm
          have hle : ∀ᶠ y in 𝓝 x, h y ≤ φ y := by
            filter_upwards [hev', hnear] with y hy hy'
            rw [hv, piecewise_eq_of_mem _ _ _ hy'.1] at hy
            rcases le_total (φ y) 0 with h1 | h1
            · rw [max_eq_right h1] at hy; linarith [hy'.2]
            · rwa [max_eq_left h1] at hy
          have := laplacian_le_of_eventually_le (hhC2.contDiffAt (isOpen_ball.mem_nhds hxB))
            (contDiff_two_of_smooth hφ).contDiffAt hφh hle
          rwa [hhΔ x hxB] at this
        · exfalso
          have hz := eqOn_zero_of_harmonic_of_eq_zero (hhC2.mono hballsub)
            (fun y hy ↦ hhΔ y (hballsub hy))
            (fun y hy ↦ hh0 y (ball_subset_closedBall (hballsub hy))) hzero.symm
          obtain ⟨y, hyN, hyP⟩ := mem_closure_iff_nhds.1 hxcl _ (ball_mem_nhds x hδ)
          have : v y = 0 := by
            rw [hv, piecewise_eq_of_mem _ _ _ (hballsub hyN)]; exact hz y hyN
          linarith [hyP.2]
      · have hvx : v x = u x := piecewise_eq_of_notMem _ _ _ hxB
        have hxu : x ∈ closure P := by
          by_cases hxs : x ∈ sphere x₀ t
          · exact hcon x hxs
          · have hxO : x ∈ (closedBall x₀ t)ᶜ := fun h' ↦ by
              rcases (mem_closedBall.1 h').lt_or_eq with h'' | h''
              · exact hxB h''
              · exact hxs h''
            rw [mem_closure_iff_nhds] at hxcl ⊢
            intro N hN
            obtain ⟨y, hyN, hyP⟩ := hxcl (N ∩ (closedBall x₀ t)ᶜ)
              (inter_mem hN (isClosed_closedBall.isOpen_compl.mem_nhds hxO))
            refine ⟨y, hyN.1, hyP.1, ?_⟩
            have : v y = u y :=
              piecewise_eq_of_notMem _ _ _ fun h' ↦ hyN.2 (ball_subset_closedBall h')
            rw [← this]; exact hyP.2
        have hPv : closure P ∩ Ω ⊆ closure (posSet v Ω) ∩ Ω := fun y hy ↦
          ⟨closure_mono (show P ⊆ posSet v Ω from
            fun z hz ↦ ⟨hz.1, hz.2.trans_le (hvu_ge z hz.1)⟩) hy.1, hy.2⟩
        refine hsub.2.2 φ hφ x ⟨⟨hxu, hxΩ⟩, by rw [← hvx]; exact hφx, ?_⟩
        have := hev.filter_mono (nhdsWithin_mono x hPv)
        filter_upwards [this, self_mem_nhdsWithin] with y hy hyS
        exact (hvu_ge y hyS.2).trans hy
  have hcomp := hll.2 x₀ t ht hBΩ v hvsub fun y hy ↦ piecewise_eq_of_notMem _ _ _ hy.2
  have hhx₀ : h x₀ = 0 := by
    refine le_antisymm ?_ (hh0 x₀ (mem_closedBall_self ht.le))
    have := hcomp x₀ (mem_ball_self (ht.trans htR))
    rwa [hv, piecewise_eq_of_mem _ _ _ (mem_ball_self ht), hux₀] at this
  have hz := eqOn_zero_of_harmonic_of_eq_zero hhC2 hhΔ
    (fun y hy ↦ hh0 y (ball_subset_closedBall hy)) hhx₀
  obtain ⟨y, hyB, hyP⟩ :=
    mem_closure_iff_nhds.1 (frontier_subset_closure hx₀.1) (ball x₀ t) (ball_mem_nhds x₀ ht)
  have := huh y (ball_subset_closedBall hyB)
  rw [hz y hyB] at this
  linarith [hyP.2]

end LemmaB4

/-! ### Mass at outer-regular points (Lemmas B.2 and B.3) -/

/-- The non-degeneracy constant of Lemma B.2 in `d = 2`. -/
noncomputable def outerRegConst (q₀ : ℝ) : ℝ := q₀ / (32 * ((2 : ℕ) : ℝ) * Real.exp (3 * (2 : ℕ)))

/-- The circle-mean constant `A` of Lemma B.3 ((ii) ⇒ (i)). -/
noncomputable def meanConst (q₀ L : ℝ) : ℝ :=
  min (outerRegConst q₀ / (8 * L)) π * (outerRegConst q₀ / 4) / (2 * π)

/-- The mass constant at outer-regular points. -/
noncomputable def massConst (q₀ L : ℝ) : ℝ :=
  min (meanConst q₀ L / (2 * L)) (1 / 2) * π * meanConst q₀ L * outerRegConst q₀ / L

theorem outerRegConst_pos {q₀ : ℝ} (hq₀ : 0 < q₀) : 0 < outerRegConst q₀ := by
  unfold outerRegConst; positivity

theorem meanConst_pos {q₀ L : ℝ} (hq₀ : 0 < q₀) (hL : 0 < L) : 0 < meanConst q₀ L := by
  have := outerRegConst_pos hq₀
  unfold meanConst
  have : 0 < min (outerRegConst q₀ / (8 * L)) π := lt_min (by positivity) Real.pi_pos
  positivity

theorem massConst_pos {q₀ L : ℝ} (hq₀ : 0 < q₀) (hL : 0 < L) : 0 < massConst q₀ L := by
  have h1 := outerRegConst_pos hq₀
  have h2 := meanConst_pos hq₀ hL
  unfold massConst
  have : 0 < min (meanConst q₀ L / (2 * L)) (1 / 2) := lt_min (by positivity) (by norm_num)
  positivity

/-- **Mass at an outer-regular free boundary point.** Let `μ` be the Riesz measure of `u` in `Ω`,
`y ∈ ∂{u > 0}` with an exterior ball `B_s(p)` touching at `y` (`|y - p| = s`, `u = 0` in
`B_s(p)`), `u` an `L`-Lipschitz subsolution in `B_{4s}(y) ⊆ Ω` with `Q ≥ q₀`. Then
`μ(B_{4s}(y)) ≥ c s` (paper, proof of Thm B.1: Lemma B.2 and Lemma B.3).

Proof: Lemma B.2 gives `z ∈ B_{4s}(y)` with `u(z) ≥ c₂ s`; with `r' = |z - y| ≥ c₂ s / L`,
`u(z) ≥ c₂ r'/4`, so `⨍_{∂B_{r'}(y)} u ≥ A r'` (`le_circleMean_of_lipschitz`) and
`μ(B_{r'}(y)) ≥ κ π A r'` (`IsRieszMeasure.mass_lower_bound`). -/
theorem mass_lower_bound_of_exteriorBall {Ω : Set (E 2)} {Q u : E 2 → ℝ} {μ : Measure (E 2)}
    (hμ : IsRieszMeasure Ω u μ) {q₀ L s : ℝ} (hq₀ : 0 < q₀) (hL : 0 < L) (hs : 0 < s)
    {y p : E 2} (hΩ : ball y (4 * s) ⊆ Ω) (hsub : IsViscSub (ball y (4 * s)) Q u)
    (hQ : ∀ z ∈ ball y (4 * s), q₀ ≤ Q z)
    (hLip : LipschitzOnWith (Real.toNNReal L) u (ball y (4 * s)))
    (hy : y ∈ freeBoundary u (ball y (4 * s))) (hp : ‖y - p‖ = s)
    (hext : ∀ z ∈ ball p s ∩ ball y (4 * s), u z = 0) :
    ENNReal.ofReal (massConst q₀ L * s) ≤ μ (ball y (4 * s)) := by
  obtain ⟨z, hz, hzle⟩ := exists_le_of_exteriorBall (d := 2) (by norm_num) hs hq₀ hsub hQ hy hp
    hext
  set c₂ := outerRegConst q₀ with hc₂
  have hc₂pos : 0 < c₂ := outerRegConst_pos hq₀
  have hzle' : c₂ * s ≤ u z := hzle
  have huy : u y = 0 := eq_zero_of_mem_freeBoundary isOpen_ball hsub.1 hsub.2.1 hy
  set r' := dist z y with hr'
  have hLz := hLip.dist_le_mul z hz y (mem_ball_self (by positivity))
  rw [Real.coe_toNNReal _ hL.le, Real.dist_eq, huy, sub_zero] at hLz
  have hr'low : c₂ * s ≤ L * r' := hzle'.trans ((le_abs_self _).trans hLz)
  have hr'pos : 0 < r' := by
    by_contra h
    push Not at h
    nlinarith
  have hr'4 : r' < 4 * s := hz
  have hcb : closedBall y r' ⊆ ball y (4 * s) := closedBall_subset_ball hr'4
  set A := meanConst q₀ L with hA
  have hApos : 0 < A := meanConst_pos hq₀ hL
  have hmean : A * r' ≤ circleMean u y r' := by
    have h := le_circleMean_of_lipschitz (M := c₂ * r' / 4) hr'pos hL (by positivity)
      (hLip.mono hcb) (fun w hw ↦ hsub.2.1 w (hcb (sphere_subset_closedBall hw)))
      (show z ∈ sphere y r' from rfl) (by nlinarith)
    have e : c₂ * r' / 4 / (2 * L * r') = c₂ / (8 * L) := by field_simp; ring
    rw [e] at h
    refine le_of_eq_of_le ?_ h
    rw [hA, meanConst]
    ring
  have hmass := hμ.mass_lower_bound hr'pos hApos hL (hcb.trans hΩ) huy (hLip.mono hcb) hmean
  refine le_trans ?_ (hmass.trans (measure_mono (ball_subset_ball hr'4.le)))
  refine ENNReal.ofReal_le_ofReal ?_
  have hκ : 0 < min (A / (2 * L)) (1 / 2) := lt_min (by positivity) (by norm_num)
  have hsr : c₂ * s / L ≤ r' := by rw [div_le_iff₀ hL]; linarith
  calc massConst q₀ L * s = min (A / (2 * L)) (1 / 2) * π * A * (c₂ * s / L) := by
        rw [massConst, ← hA, ← hc₂]; ring
    _ ≤ min (A / (2 * L)) (1 / 2) * π * A * r' := by gcongr

/-! ### The covering step -/

/-- **The Vitali covering step** (proof of Thm B.1, with the corrections listed in the module
docstring). For
`t ∈ [T/2, T]` let `X t ∈ ∂B_t(x₀)` and `0 < ρ t ≤ t` with `μ(B_{5ρ(t)}(X t)) ≥ c ρ(t)`. Then
`μ(B_{6T}(x₀)) ≥ c T / 80`.

Proof: finitely many intervals `(t - 5ρ(t), t + 5ρ(t))` cover `[T/2, T]`; Vitali gives a
disjoint subfamily whose 4-fold enlargements cover, so `T/2 ≤ Σ 40 ρ(t_j)`; disjointness of the
intervals gives disjointness of the balls `B_{5ρ(t_j)}(X t_j)` since `|X t - X t'| ≥ |t - t'|`,
and all these balls lie in `B_{6T}(x₀)`. -/
theorem mass_lower_bound_of_covering {μ : Measure (E 2)} {x₀ : E 2} {T c : ℝ} (hc : 0 ≤ c)
    (X : ℝ → E 2) (ρ : ℝ → ℝ) (hX : ∀ t ∈ Icc (T / 2) T, dist (X t) x₀ = t)
    (hρ : ∀ t ∈ Icc (T / 2) T, 0 < ρ t ∧ ρ t ≤ t)
    (hmass : ∀ t ∈ Icc (T / 2) T, ENNReal.ofReal (c * ρ t) ≤ μ (ball (X t) (5 * ρ t))) :
    ENNReal.ofReal (c * T / 80) ≤ μ (ball x₀ (6 * T)) := by
  classical
  obtain ⟨F, hFsub, hFcov⟩ := (isCompact_Icc (a := T / 2) (b := T)).elim_nhds_subcover
    (fun t ↦ ball t (5 * ρ t)) fun t ht ↦ ball_mem_nhds t (by linarith [(hρ t ht).1])
  obtain ⟨u, huF, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (↑F : Set ℝ) id (fun t ↦ 5 * ρ t) (5 * T)
    (fun a ha ↦ show 5 * ρ a ≤ 5 * T by linarith [(hρ a (hFsub a ha)).2, (hFsub a ha).2]) 4
    (by norm_num)
  set G := F.filter (· ∈ u) with hG
  have hGu : ∀ b, b ∈ G ↔ b ∈ u := fun b ↦ by
    rw [hG, Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨huF h, h⟩⟩
  have hGI : ∀ b ∈ G, b ∈ Icc (T / 2) T := fun b hb ↦ hFsub b (Finset.mem_filter.1 hb).1
  -- (1) `T/2 ≤ 40 Σ ρ`
  have hsum : T / 2 ≤ 40 * ∑ b ∈ G, ρ b := by
    have hcover : Icc (T / 2) T ⊆ ⋃ b ∈ G, ball b (4 * (5 * ρ b)) := by
      intro t ht
      obtain ⟨a, haF, hta⟩ := mem_iUnion₂.1 (hFcov ht)
      obtain ⟨b, hbu, hab⟩ := hcov a haF
      exact mem_iUnion₂.2 ⟨b, (hGu b).2 hbu, hab hta⟩
    have h1 := (measure_mono (μ := volume) hcover).trans (measure_biUnion_finset_le G _)
    rw [Real.volume_Icc] at h1
    simp only [Real.volume_ball] at h1
    rw [← ENNReal.ofReal_sum_of_nonneg fun b hb ↦ by linarith [(hρ b (hGI b hb)).1],
      ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun b hb ↦ by
        linarith [(hρ b (hGI b hb)).1])] at h1
    have e : ∑ b ∈ G, 2 * (4 * (5 * ρ b)) = 40 * ∑ b ∈ G, ρ b := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ ↦ by ring
    linarith
  -- (2) disjoint balls inside `B_{6T}(x₀)`
  have hpd : (↑G : Set ℝ).PairwiseDisjoint fun b ↦ ball (X b) (5 * ρ b) := by
    intro b hb b' hb' hne
    have hbI := hGI b hb
    have hbI' := hGI b' hb'
    have hd := hdisj ((hGu b).1 hb) ((hGu b').1 hb') hne
    simp only [Function.onFun, id] at hd
    rw [disjoint_ball_ball_iff (by linarith [(hρ b hbI).1]) (by linarith [(hρ b' hbI').1])] at hd
    refine ball_disjoint_ball (hd.trans ?_)
    have := abs_dist_sub_le (X b) (X b') x₀
    rw [hX b hbI, hX b' hbI', ← Real.dist_eq] at this
    exact this
  have hunion : ⋃ b ∈ G, ball (X b) (5 * ρ b) ⊆ ball x₀ (6 * T) := by
    refine iUnion₂_subset fun b hb ↦ fun y hy ↦ ?_
    have hbI := hGI b hb
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y (X b) x₀, hX b hbI, (hρ b hbI).2, hbI.2]
  have h2 := (measure_mono (μ := μ) hunion)
  rw [measure_biUnion_finset hpd fun b _ ↦ measurableSet_ball] at h2
  calc ENNReal.ofReal (c * T / 80) ≤ ENNReal.ofReal (c * ∑ b ∈ G, ρ b) :=
        ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = ∑ b ∈ G, ENNReal.ofReal (c * ρ b) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun b hb ↦
          mul_nonneg hc (hρ b (hGI b hb)).1.le]
    _ ≤ ∑ b ∈ G, μ (ball (X b) (5 * ρ b)) := Finset.sum_le_sum fun b hb ↦ hmass b (hGI b hb)
    _ ≤ μ (ball x₀ (6 * T)) := h2

/-! ### Theorem B.1 -/

/-- **Thm B.1** for local largest subsolutions. Let `u` be a
local largest subsolution in `B_R(x₀) ⊆ ℝ²` with `Q ≥ q₀ > 0`, Lipschitz, `C²` and harmonic in
`{u > 0}`, and `x₀ ∈ ∂{u > 0}`. Then `u` is non-degenerate at `x₀`.

Quantitative form: `sup_{B̄_r(x₀)} u ≥ c r` for `r ≤ R/2`, with `c` depending only on `q₀` and
the Lipschitz constant `K`.

Proof (the paper's sketch): with `μ = Δu` (`exists_isRieszMeasure`), for `T ≤ R/7` and each
`t ∈ [T/2, T]`, Lemma B.4 gives `x_t ∈ ∂B_t(x₀) \ \overline{{u > 0}}`; with
`ρ_t = d(x_t, \overline{{u > 0}}) ∈ (0, t]` and a nearest point `y_t`, the exterior ball
`B_{ρ_t}(x_t)` touches at `y_t ∈ ∂{u > 0}`, so `μ(B_{5ρ_t}(x_t)) ≥ μ(B_{4ρ_t}(y_t)) ≥ c ρ_t`.
The covering step gives `μ(B_{6T}(x₀)) ≥ c T / 80`, i.e. condition (iii) of Lemma B.3 at `x₀`;
then (iii) ⇒ (i) ⇒ (ii). -/
theorem exists_le_of_isLocalLargestSub {Q u : E 2 → ℝ} {x₀ : E 2} {R q₀ : ℝ}
    {K : ℝ≥0} (_hR : 0 < R) (hq₀ : 0 < q₀) (hQ : ∀ y ∈ ball x₀ R, q₀ ≤ Q y)
    (hll : IsLocalLargestSub (ball x₀ R) Q u) (hLip : LipschitzOnWith K u (ball x₀ R))
    (hC2 : ContDiffOn ℝ 2 u (posSet u (ball x₀ R))) (hΔ : ∀ y ∈ posSet u (ball x₀ R), Δ u y = 0)
    (hx₀ : x₀ ∈ freeBoundary u (ball x₀ R)) :
    ∀ r, 0 < r → r ≤ R / 2 →
      ∃ y ∈ closedBall x₀ r, massConst q₀ (K + 1) / 480 / (4 * π) * r ≤ u y := by
  classical
  set Ω := ball x₀ R with hΩ
  set P := posSet u Ω with hP
  have hsub := hll.1
  have hucont : ContinuousOn u Ω := hsub.1
  have hunn : ∀ y ∈ Ω, 0 ≤ u y := hsub.2.1
  have hux₀ : u x₀ = 0 := eq_zero_of_mem_freeBoundary isOpen_ball hucont hunn hx₀
  have hPopen : IsOpen P := hucont.isOpen_inter_preimage isOpen_ball isOpen_Ioi
  obtain ⟨μ, hμ⟩ := exists_isRieszMeasure isOpen_ball hucont hunn hC2 hΔ
  set L : ℝ := K + 1 with hLdef
  have hL : 0 < L := by positivity
  have hLipL : LipschitzOnWith (Real.toNNReal L) u Ω := hLip.weaken (by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hL.le]; linarith)
  set c₄ := massConst q₀ L with hc₄
  have hc₄pos : 0 < c₄ := massConst_pos hq₀ hL
  have hne : (closure P).Nonempty := ⟨x₀, frontier_subset_closure hx₀.1⟩
  -- the mass bound at `x₀`
  have hstep : ∀ T, 0 < T → 7 * T ≤ R →
      ENNReal.ofReal (c₄ * T / 80) ≤ μ (ball x₀ (6 * T)) := by
    intro T hT hTR
    have hpt : ∀ t, ∃ X : E 2, ∃ ρ : ℝ, t ∈ Icc (T / 2) T →
        dist X x₀ = t ∧ (0 < ρ ∧ ρ ≤ t) ∧ ENNReal.ofReal (c₄ * ρ) ≤ μ (ball X (5 * ρ)) := by
      intro t
      by_cases ht : t ∈ Icc (T / 2) T
      swap
      · exact ⟨x₀, 0, fun h ↦ absurd h ht⟩
      have ht0 : 0 < t := by linarith [ht.1]
      have htR : t < R := by linarith [ht.2]
      obtain ⟨X, hXs, hXP⟩ := exists_notMem_closure_posSet_sphere hll hLip hC2 hΔ hx₀ ht0 htR
      set ρ := infDist X (closure P) with hρ
      have hρpos : 0 < ρ := (isClosed_closure.notMem_iff_infDist_pos hne).1 hXP
      have hρt : ρ ≤ t :=
        (infDist_le_dist_of_mem (frontier_subset_closure hx₀.1)).trans_eq hXs
      obtain ⟨Y, hYP, hYd⟩ := isClosed_closure.exists_infDist_eq_dist hne X
      rw [← hρ] at hYd
      have hYx₀ : dist Y x₀ ≤ 2 * t := by
        linarith [dist_triangle Y X x₀, dist_comm X Y, mem_sphere.1 hXs, hYd, hρt]
      have hball : ball Y (4 * ρ) ⊆ Ω := fun z hz ↦ by
        rw [mem_ball] at hz ⊢
        linarith [dist_triangle z Y x₀, ht.2]
      have hYΩ : Y ∈ Ω := hball (mem_ball_self (by positivity))
      have hzero : ∀ z ∈ ball X ρ, z ∈ Ω → u z = 0 := by
        intro z hz hzΩ
        refine le_antisymm (not_lt.1 fun hpos ↦ ?_) (hunn z hzΩ)
        have := infDist_le_dist_of_mem (x := X) (subset_closure (show z ∈ P from ⟨hzΩ, hpos⟩))
        rw [mem_ball, dist_comm] at hz
        linarith
      have huY : u Y = 0 := by
        refine le_antisymm (not_lt.1 fun hpos ↦ ?_) (hunn Y hYΩ)
        have hYcl : Y ∈ closure (ball X ρ) := by
          rw [closure_ball X hρpos.ne', mem_closedBall, dist_comm, ← hYd]
        obtain ⟨z, hzN, hzB⟩ :=
          mem_closure_iff_nhds.1 hYcl _ (hPopen.mem_nhds (show Y ∈ P from ⟨hYΩ, hpos⟩))
        linarith [hzero z hzB hzN.1, hzN.2]
      have hYfb : Y ∈ freeBoundary u (ball Y (4 * ρ)) := by
        refine ⟨⟨?_, fun hint ↦ ?_⟩, mem_ball_self (by positivity)⟩
        · rw [mem_closure_iff_nhds] at hYP ⊢
          intro N hN
          obtain ⟨z, hzN, hzP⟩ :=
            hYP (N ∩ ball Y (4 * ρ)) (inter_mem hN (ball_mem_nhds Y (by positivity)))
          exact ⟨z, hzN.1, hzN.2, hzP.2⟩
        · have := (interior_subset hint).2
          linarith
      have hmass := mass_lower_bound_of_exteriorBall hμ hq₀ hL hρpos hball
        (hsub.mono isOpen_ball hball) (fun z hz ↦ hQ z (hball hz)) (hLipL.mono hball) hYfb
        (p := X) (by rw [← dist_eq_norm, dist_comm, hYd])
        (fun z hz ↦ hzero z hz.1 (hball hz.2))
      refine ⟨X, ρ, fun _ ↦ ⟨hXs, ⟨hρpos, hρt⟩, hmass.trans (measure_mono fun z hz ↦ ?_)⟩⟩
      rw [mem_ball] at hz ⊢
      linarith [dist_triangle z Y X, dist_comm X Y]
    choose X ρ hXρ using hpt
    exact mass_lower_bound_of_covering hc₄pos.le X ρ (fun t ht ↦ (hXρ t ht).1)
      (fun t ht ↦ (hXρ t ht).2.1) fun t ht ↦ (hXρ t ht).2.2
  -- conclusion: (iii) ⇒ (i) ⇒ (ii)
  set c₅ := c₄ / 480 with hc₅
  have hc₅pos : 0 < c₅ := by positivity
  intro r hr hrR
  have hrΩ : closedBall x₀ r ⊆ Ω := closedBall_subset_ball (by linarith)
  have hmassr : ∀ s ∈ Ioo 0 r, ENNReal.ofReal (c₅ * s) ≤ μ (ball x₀ s) := by
    intro s hs
    have := hstep (s / 6) (by linarith [hs.1]) (by linarith [hs.2])
    rwa [show 6 * (s / 6) = s by ring, show c₄ * (s / 6) / 80 = c₅ * s by rw [hc₅]; ring]
      at this
  have hmean := hμ.circleMean_lower_bound hr hc₅pos.le hrΩ hmassr
  rw [hux₀, sub_zero] at hmean
  by_contra hcon
  push Not at hcon
  have hle := circleMean_le hr.le (hucont.mono (sphere_subset_closedBall.trans hrΩ))
    fun y hy ↦ (hcon y (sphere_subset_closedBall hy)).le
  have hπ := Real.pi_pos
  have : c₅ / (4 * π) * r < c₅ * r / (2 * π) := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hc₅pos hr]
  linarith

/-- **Thm B.1**, local form. -/
theorem isNondegenerateAt_of_isLocalLargestSub {Q u : E 2 → ℝ} {x₀ : E 2} {R q₀ : ℝ}
    {K : ℝ≥0} (hR : 0 < R) (hq₀ : 0 < q₀) (hQ : ∀ y ∈ ball x₀ R, q₀ ≤ Q y)
    (hll : IsLocalLargestSub (ball x₀ R) Q u) (hLip : LipschitzOnWith K u (ball x₀ R))
    (hC2 : ContDiffOn ℝ 2 u (posSet u (ball x₀ R))) (hΔ : ∀ y ∈ posSet u (ball x₀ R), Δ u y = 0)
    (hx₀ : x₀ ∈ freeBoundary u (ball x₀ R)) : IsNondegenerateAt u x₀ :=
  ⟨_, div_pos (div_pos (massConst_pos hq₀ (by positivity)) (by norm_num)) (by positivity),
    R / 2, by positivity, exists_le_of_isLocalLargestSub hR hq₀ hQ hll hLip hC2 hΔ hx₀⟩

/-- **Thm B.1** for Perron's largest subsolution, from Prop 6.2 (viscosity solution, inner
variational solution, continuous on `Ū`) and the dual of Lemma 2.7
(`Setting.perronLargest_isLocalLargestSub_near_fb`). -/
theorem largestSub_nondegenerate_of (h62 : InnerLargestStatement) :
    LargestSubNondegenerateStatement := by
  intro S g hg x₀ hx₀
  set u := perronLargest S.U S.Q g with hu
  obtain ⟨hvisc, ⟨χ, hinner⟩, hcont⟩ := h62 2 S g hg
  obtain ⟨r, hr, hrU, hll⟩ := S.perronLargest_isLocalLargestSub_near_fb hg hvisc.2 hcont hx₀
  have hbU : ball x₀ r ⊆ S.U := ball_subset_closedBall.trans hrU
  obtain ⟨K, hK⟩ := (hinner.locLip.mono hrU).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall x₀ r)
  have hPsub : posSet u (ball x₀ r) ⊆ posSet u S.U := fun y hy ↦ ⟨hbU hy.1, hy.2⟩
  refine isNondegenerateAt_of_isLocalLargestSub hr S.Qmin_pos
    (fun y hy ↦ (S.Q_mem y (subset_closure (hbU hy))).1) hll (hK.mono ball_subset_closedBall)
    (hinner.c2.mono hPsub) (fun y hy ↦ hinner.harmonic y (hPsub hy)) ⟨?_, mem_ball_self hr⟩
  have hloc : ∀ N ∈ 𝓝 x₀, N ∩ ball x₀ r ∈ 𝓝 x₀ := fun N hN ↦ inter_mem hN (ball_mem_nhds x₀ hr)
  refine ⟨?_, fun hint ↦ ?_⟩
  · rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨z, hzN, hzP⟩ := mem_closure_iff_nhds.1 (frontier_subset_closure hx₀.1) _ (hloc N hN)
    exact ⟨z, hzN.1, hzN.2, hzP.2⟩
  · have := (interior_subset hint).2
    have h0 := eq_zero_of_mem_freeBoundary S.isOpen hvisc.2.1 hvisc.2.2.1 hx₀
    linarith

/-! ### Uniform non-degeneracy at free boundary points near `x₀` -/

/-- The local largest subsolution property passes to open subsets. -/
theorem IsLocalLargestSub.mono {U W : Set (E d)} {Q u : E d → ℝ} (hU : IsOpen U)
    (hW : IsOpen W) (hWU : W ⊆ U) (hll : IsLocalLargestSub U Q u) : IsLocalLargestSub W Q u := by
  classical
  refine ⟨hll.1.mono hW hWU, fun x r hr hxr v hv heq y hy ↦ ?_⟩
  have hglue := isViscSub_piecewise hU hW hWU isClosed_closedBall hxr hll.1 hv
    fun z hz ↦ heq z ⟨hz.1, fun h ↦ hz.2 (ball_subset_closedBall h)⟩
  have h := hll.2 x r hr (hxr.trans hWU) _ hglue (fun z hz ↦ by
    by_cases hzW : z ∈ W
    · rw [piecewise_eq_of_mem _ _ _ hzW]; exact heq z ⟨hzW, hz.2⟩
    · rw [piecewise_eq_of_notMem _ _ _ hzW]) y (hWU hy)
  rwa [piecewise_eq_of_mem _ _ _ hy] at h

/-- A free boundary point of `u` in `U` is a free boundary point in every ball around it
contained in `U`. -/
theorem mem_freeBoundary_ball {U : Set (E d)} {u : E d → ℝ} {z : E d}
    (hz : z ∈ freeBoundary u U) {ρ : ℝ} (hρ : 0 < ρ) (hρU : ball z ρ ⊆ U) :
    z ∈ freeBoundary u (ball z ρ) := by
  refine ⟨⟨?_, fun hint ↦ ?_⟩, mem_ball_self hρ⟩
  · rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨y, hyN, hyP⟩ := mem_closure_iff_nhds.1 (frontier_subset_closure hz.1) _
      (inter_mem hN (ball_mem_nhds z hρ))
    exact ⟨y, hyN.1, hyN.2, hyP.2⟩
  · refine hz.1.2 ?_
    exact interior_mono (fun y (hy : y ∈ posSet u (ball z ρ)) ↦
      (⟨hρU hy.1, hy.2⟩ : y ∈ posSet u U)) hint

/-- **Uniform non-degeneracy of Perron's largest subsolution at free boundary points** near a free
boundary point `x₀` (Thm B.1 with constants depending only on `q₀`, the Lipschitz constant and the
radius of the local largest subsolution property). -/
theorem Setting.perronLargest_nondegenerate_near_fb (h62 : InnerLargestStatement)
    (S : Setting 2) {g : E 2 → ℝ} (hg : IsStrictSuper S.U S.Q g) {x₀ : E 2}
    (hx₀ : x₀ ∈ freeBoundary (perronLargest S.U S.Q g) S.U) :
    ∃ c > 0, ∃ ρ > 0, ∀ z ∈ freeBoundary (perronLargest S.U S.Q g) S.U ∩ ball x₀ ρ,
      ∀ r, 0 < r → r ≤ ρ → ∃ y ∈ closedBall z r, c * r ≤ perronLargest S.U S.Q g y := by
  set u := perronLargest S.U S.Q g with hu
  obtain ⟨hvisc, ⟨χ, hinner⟩, hcont⟩ := h62 2 S g hg
  obtain ⟨R, hR, hRU, hll⟩ := S.perronLargest_isLocalLargestSub_near_fb hg hvisc.2 hcont hx₀
  have hbU : ball x₀ R ⊆ S.U := ball_subset_closedBall.trans hRU
  obtain ⟨K, hK⟩ := (hinner.locLip.mono hRU).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall x₀ R)
  have hq₀ := S.Qmin_pos
  refine ⟨massConst S.Qmin (K + 1) / 480 / (4 * π),
    div_pos (div_pos (massConst_pos hq₀ (by positivity)) (by norm_num)) (by positivity),
    R / 4, by positivity, fun z hz r hr hrR ↦ ?_⟩
  have hzR : ball z (R / 2) ⊆ ball x₀ R := fun y hy ↦ by
    rw [mem_ball] at hy ⊢; linarith [dist_triangle y z x₀, mem_ball.1 hz.2]
  have hzU : ball z (R / 2) ⊆ S.U := hzR.trans hbU
  have hPsub : posSet u (ball z (R / 2)) ⊆ posSet u S.U := fun y hy ↦ ⟨hzU hy.1, hy.2⟩
  exact exists_le_of_isLocalLargestSub (by positivity) hq₀
    (fun y hy ↦ (S.Q_mem y (subset_closure (hzU hy))).1)
    (hll.mono isOpen_ball isOpen_ball hzR) ((hK.mono ball_subset_closedBall).mono hzR)
    (hinner.c2.mono hPsub) (fun y hy ↦ hinner.harmonic y (hPsub hy))
    (mem_freeBoundary_ball hz.1 (by positivity) hzU) r hr (by linarith)

end PerronVariational

end
