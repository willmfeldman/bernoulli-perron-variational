/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Registry.Semilinear
public import PerronVariational.Semilinear.Profiles
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Registry.Comparison
import PerronVariational.Semilinear.ViscosityLimitCalculus

/-!
# Proposition 5.3, Step 2: the semilinear limit is a supersolution

Step 2 of the proof of Proposition 5.3 of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

Let `u_j` solve `∂ₜu = Δu - Q² β_{ε_j}(u)` in `U × (0, T]` with `ε_j → 0` and `u_j → u` locally
uniformly. Then `u` is a parabolic viscosity supersolution of (3.1) (Definition 3.2):
`semilinear_limit_isParaSuper`.

## Deviation from the paper's proof (Step 2)

The paper perturbs a strict subsolution `φ` to `φ + δ` and compares `u_j` with `(Φ_{ε,θ}(φ + δ))₊`
on the whole cylinder. But `φ + δ` need **not** be a strict subsolution: the Definition 3.2
conditions constrain `φ` only on `\overline{{φ > 0}}`, and where `-δ < φ ≤ 0` away from
`\overline{{φ > 0}}` (e.g. a plateau `φ ≡ 0` at positive distance from `{φ > 0}`), `∂ₜφ - Δφ` has no
sign, so `(Φ_ε(φ + δ))₊` is not a subsolution there. (The same issue affects the use of Lemma A.4,
which needs the sub/supersolution inequalities on `{|g| ≤ a₀}`.)

We localize instead: with `A = \overline{{φ > 0}} ∩ (V̄ × [a, b])` and `D = dist(·, A)`, we use
the glued function `w = (Φ_{ε,θ}(φ + δ))₊` on `{D < 3r/2}`, `w = 0` elsewhere (`gluedSub`). For
`r` small: near `A` the strict subsolution inequalities hold with margins (compactness), and on the
annulus `{r ≤ D ≤ 2r}` one has `φ ≤ -η < 0` (a zero of `φ` near `A` has `∇ₓφ ≠ 0`, hence lies in
`\overline{{φ > 0}}`); so `w` is continuous and a viscosity subsolution for `δ, ε` small. The
boundary ordering is obtained by compactness (`exists_bdry_margin`), which replaces the paper's
identity (5.4).
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### Helpers -/

section Helpers

/-- A continuous positive function on a compact set has a positive lower bound. -/
theorem exists_pos_le_of_isCompact {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsCompact s) {f : X → ℝ} (hf : ContinuousOn f s) (hpos : ∀ x ∈ s, 0 < f x) :
    ∃ m > 0, ∀ x ∈ s, m ≤ f x := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hne hf
    exact ⟨f x, hpos x hx, fun y hy ↦ hmin hy⟩

/-- A zero of a differentiable space-time function with nonzero spatial gradient lies in the
closure of its positivity set. -/
theorem mem_closure_pos_of_gradₓ_ne_zero {φ : E d × ℝ → ℝ} {p : E d × ℝ}
    (hφ : DifferentiableAt ℝ φ p) (hp0 : φ p = 0) (hg : gradₓ φ p ≠ 0) :
    p ∈ closure {q | 0 < φ q} := by
  set v := gradₓ φ p with hv
  set L : ℝ → E d × ℝ := fun s ↦ (p.1 + s • v, p.2) with hL_def
  have hL : HasDerivAt L (v, (0 : ℝ)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ ↦ p.1 + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p.1
    exact h1.prodMk (hasDerivAt_const 0 p.2)
  have hL0 : L 0 = p := by simp [hL_def]
  have hφ' : HasFDerivAt φ (fderiv ℝ φ p) (L 0) := by rw [hL0]; exact hφ.hasFDerivAt
  have hd : HasDerivAt (φ ∘ L) (fderiv ℝ φ p (v, 0)) 0 := hφ'.comp_hasDerivAt 0 hL
  have hval : fderiv ℝ φ p (v, 0) = ‖v‖ ^ 2 := by
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E d) (x := v)
      (y := (fderiv ℝ φ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ))
    rw [← gradₓ_eq_fderiv hφ, ← hv, real_inner_self_eq_norm_sq] at h
    rw [h]; rfl
  have hpos : 0 < ‖v‖ ^ 2 := by positivity
  rw [hval] at hd
  have hslope := hasDerivAt_iff_tendsto_slope.1 hd
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < slope (φ ∘ L) 0 s :=
    (hslope.mono_left (nhdsWithin_mono _ fun s (hs : 0 < s) ↦ ne_of_gt hs)).eventually
      (lt_mem_nhds hpos)
  have hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), L s ∈ {q | 0 < φ q} := by
    filter_upwards [hev, self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
    rw [slope_def_field, sub_zero] at hs
    have h2 : 0 < (φ ∘ L) s - (φ ∘ L) 0 := (div_pos_iff_of_pos_right hs0).1 hs
    simp only [Function.comp, hL0, hp0, sub_zero] at h2
    exact h2
  have htend : Tendsto L (𝓝[>] 0) (𝓝 p) := by
    rw [← hL0]; exact hL.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto htend hmem

theorem isClosed_parBdry (V : Set (E d)) (a b : ℝ) : IsClosed (parBdry V a b) :=
  (isClosed_closure.prod isClosed_singleton).union (isClosed_frontier.prod isClosed_Icc)

theorem parBdry_subset {V : Set (E d)} {a b : ℝ} (hab : a ≤ b) :
    parBdry V a b ⊆ closure V ×ˢ Icc a b := by
  rintro ⟨x, t⟩ (⟨hx, ht⟩ | ⟨hx, ht⟩)
  · rw [mem_singleton_iff] at ht; subst ht; exact ⟨hx, le_rfl, hab⟩
  · exact ⟨frontier_subset_closure hx, ht⟩

theorem cyl_subset {V : Set (E d)} {a b : ℝ} : cyl V a b ⊆ closure V ×ˢ Icc a b :=
  fun _ hp ↦ ⟨subset_closure hp.1, Ioc_subset_Icc_self hp.2⟩

theorem Ioc_leftNhds {a b : ℝ} : ∀ t ∈ Ioc a b, ∃ δ > 0, Ioc (t - δ) t ⊆ Ioc a b :=
  fun t ht ↦ ⟨t - a, by linarith [ht.1], fun s hs ↦ ⟨by linarith [hs.1], hs.2.trans ht.2⟩⟩

end Helpers

/-! ### Geometry of a strict subsolution near its positivity set -/

section Geometry

variable {φ : E d × ℝ → ℝ} {K : Set (E d × ℝ)} {Q : E d → ℝ}

/-- **Margins for a strict subsolution near `A = \overline{{φ > 0}} ∩ K`.** There are
`θ ∈ (0, 1)`, `r ∈ (0, R]` and `η > 0` such that, with `D = dist(·, A)`:
(1) `∂ₜφ - Δₓφ < 0` on `K ∩ {D < r, φ > -r}`;
(2) `Q² ≤ θ |∇ₓφ|²` on `K ∩ {D < r, -r < φ ≤ 0}`;
(3) `φ ≤ -η` on `K ∩ {r ≤ D ≤ 2r}`. -/
theorem exists_sub_geometry (hφ : ContDiff ℝ ∞ φ) (hK : IsCompact K)
    (hA : (closure {q | 0 < φ q} ∩ K).Nonempty) {Qmin Qmax : ℝ} (hQmin : 0 < Qmin)
    (hQc : ContinuousOn (fun p : E d × ℝ ↦ Q p.1) K)
    (hQ : ∀ p ∈ K, Qmin ≤ Q p.1 ∧ Q p.1 ≤ Qmax)
    (h1 : ∀ p ∈ closure {q | 0 < φ q} ∩ K, dₜ φ p - lapₓ φ p < 0)
    (h2 : ∀ p ∈ frontier {q | 0 < φ q} ∩ K, Q p.1 < ‖gradₓ φ p‖) {R : ℝ} (hR : 0 < R) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ r > 0, r ≤ R ∧ ∃ η > 0,
      (∀ p ∈ K, infDist p (closure {q | 0 < φ q} ∩ K) < r → -r < φ p →
        dₜ φ p - lapₓ φ p < 0) ∧
      (∀ p ∈ K, infDist p (closure {q | 0 < φ q} ∩ K) < r → -r < φ p → φ p ≤ 0 →
        Q p.1 ^ 2 ≤ θ * ‖gradₓ φ p‖ ^ 2) ∧
      (∀ p ∈ K, r ≤ infDist p (closure {q | 0 < φ q} ∩ K) →
        infDist p (closure {q | 0 < φ q} ∩ K) ≤ 2 * r → φ p ≤ -η) := by
  set P := {q | 0 < φ q} with hP
  set A := closure P ∩ K with hA_def
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hPo : IsOpen P := isOpen_lt continuous_const hφ.continuous
  have hAc : IsClosed A := isClosed_closure.inter hK.isClosed
  have hmemA : ∀ p, infDist p A = 0 → p ∈ A := fun p hp ↦ by
    have := (mem_closure_iff_infDist_zero hA).2 hp
    rwa [hAc.closure_eq] at this
  have hcont1 : Continuous (fun p ↦ dₜ φ p - lapₓ φ p) :=
    (continuous_dₜ (hφ.of_le (WithTop.coe_le_coe.2 le_top))).sub (continuous_lapₓ hφ2)
  have hcontG : Continuous (fun p ↦ ‖gradₓ φ p‖ ^ 2) :=
    ((continuous_gradₓ (hφ.of_le (WithTop.coe_le_coe.2 le_top))).norm).pow 2
  set h : E d × ℝ → ℝ := fun p ↦ max (infDist p A) (-φ p) with hh_def
  have hhc : Continuous h := (continuous_infDist_pt A).max hφ.continuous.neg
  have hfr : ∀ p ∈ A, φ p ≤ 0 → p ∈ frontier P ∩ K := by
    intro p hp hφp
    refine ⟨?_, hp.2⟩
    rw [frontier, hPo.interior_eq]
    exact ⟨hp.1, fun h' ↦ (not_lt.2 hφp) h'⟩
  have hQ0 : ∀ p ∈ K, 0 ≤ Q p.1 := fun p hp ↦ hQmin.le.trans (hQ p hp).1
  -- gradient margin on the free boundary
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_isCompact (s := frontier P ∩ K)
    (hK.of_isClosed_subset (isClosed_frontier.inter hK.isClosed) inter_subset_right)
    (f := fun p ↦ ‖gradₓ φ p‖ ^ 2 - Q p.1 ^ 2)
    (hcontG.continuousOn.sub ((hQc.mono inter_subset_right).pow 2))
    (fun p hp ↦ sub_pos.2 (pow_lt_pow_left₀ (h2 p hp) (hQ0 p hp.2) two_ne_zero))
  have hQmax : 0 < Qmax := by
    obtain ⟨p, hp⟩ := hA
    linarith [(hQ p hp.2).1, (hQ p hp.2).2]
  set θ := Qmax ^ 2 / (Qmax ^ 2 + m / 2) with hθ_def
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ_def, div_lt_one (by positivity)]; linarith
  -- bad set 1: where the heat inequality fails
  have hB1 : IsCompact (K ∩ (fun p ↦ dₜ φ p - lapₓ φ p) ⁻¹' Ici 0) :=
    hK.of_isClosed_subset (hK.isClosed.inter (isClosed_Ici.preimage hcont1)) inter_subset_left
  obtain ⟨r₁, hr₁, hr₁le⟩ := exists_pos_le_of_isCompact hB1 hhc.continuousOn (fun p hp ↦ by
    by_contra hle
    push Not at hle
    have hd : infDist p A = 0 := le_antisymm ((le_max_left _ _).trans hle) infDist_nonneg
    have h' := h1 p (hmemA p hd)
    have h'' : (0 : ℝ) ≤ dₜ φ p - lapₓ φ p := hp.2
    linarith)
  -- bad set 2: where the gradient margin fails on `{φ ≤ 0}`
  have hB2 : IsCompact (K ∩ φ ⁻¹' Iic 0 ∩
      (fun p ↦ ‖gradₓ φ p‖ ^ 2 - Q p.1 ^ 2) ⁻¹' Iic (m / 2)) := by
    have hc : IsClosed (K ∩ φ ⁻¹' Iic 0) :=
      hK.isClosed.inter (isClosed_Iic.preimage hφ.continuous)
    refine hK.of_isClosed_subset ?_ (inter_subset_left.trans inter_subset_left)
    exact (hcontG.continuousOn.sub ((hQc.mono inter_subset_left).pow 2)
      ).preimage_isClosed_of_isClosed hc isClosed_Iic
  obtain ⟨r₂, hr₂, hr₂le⟩ := exists_pos_le_of_isCompact hB2 hhc.continuousOn (fun p hp ↦ by
    by_contra hle
    push Not at hle
    have hd : infDist p A = 0 := le_antisymm ((le_max_left _ _).trans hle) infDist_nonneg
    have hpA := hmemA p hd
    have hφ0 : φ p ≤ 0 := hp.1.2
    have h' := hmle p (hfr p hpA hφ0)
    have h'' : ‖gradₓ φ p‖ ^ 2 - Q p.1 ^ 2 ≤ m / 2 := hp.2
    simp only at h'
    linarith)
  set r := min (min r₁ r₂ / 3) R with hr_def
  have hr : 0 < r := lt_min (by positivity) hR
  have hrr₁ : 3 * r ≤ r₁ := by
    have := min_le_left (min r₁ r₂ / 3) R
    have := min_le_left r₁ r₂
    linarith
  have hrr₂ : 3 * r ≤ r₂ := by
    have := min_le_left (min r₁ r₂ / 3) R
    have := min_le_right r₁ r₂
    linarith
  -- outside the bad set 2, the gradient is large
  have hgradbig : ∀ p ∈ K, φ p ≤ 0 → h p < r₂ → m / 2 < ‖gradₓ φ p‖ ^ 2 - Q p.1 ^ 2 := by
    intro p hpK hφp hhp
    by_contra hc
    push Not at hc
    exact (hr₂le p ⟨⟨hpK, hφp⟩, hc⟩).not_gt hhp
  -- the annulus
  have hAnn : IsCompact (K ∩ (fun p ↦ infDist p A) ⁻¹' Icc r (2 * r)) :=
    hK.of_isClosed_subset (hK.isClosed.inter (isClosed_Icc.preimage (continuous_infDist_pt A)))
      inter_subset_left
  obtain ⟨η, hη, hηle⟩ := exists_pos_le_of_isCompact hAnn hφ.continuous.neg.continuousOn
    (fun p ⟨hpK, hr1, hr2⟩ ↦ by
      simp only at hr1 hr2
      have hpA : p ∉ A := fun hpA ↦ by rw [infDist_zero_of_mem hpA] at hr1; linarith
      have hφle : φ p ≤ 0 := by
        by_contra hpos
        push Not at hpos
        exact hpA ⟨subset_closure hpos, hpK⟩
      rcases hφle.lt_or_eq with hlt | heq
      · linarith
      · exfalso
        have hhp : h p < r₂ := by
          simp only [hh_def, heq, neg_zero]
          rw [max_eq_left infDist_nonneg]
          linarith
        have hgrad := hgradbig p hpK heq.le hhp
        have hg0 : gradₓ φ p ≠ 0 := fun h0 ↦ by
          rw [h0, norm_zero] at hgrad
          nlinarith [sq_nonneg (Q p.1)]
        exact hpA ⟨mem_closure_pos_of_gradₓ_ne_zero (hφ.differentiable (by simp) p) heq hg0,
          hpK⟩)
  refine ⟨θ, hθ0, hθ1, r, hr, min_le_right _ _, η, hη, ?_, ?_, ?_⟩
  · intro p hpK hd hφr
    have hhp : h p < r₁ := max_lt (by linarith) (by linarith)
    by_contra hc
    push Not at hc
    exact (hr₁le p ⟨hpK, hc⟩).not_gt hhp
  · intro p hpK hd hφr hφ0
    have hhp : h p < r₂ := max_lt (by linarith) (by linarith)
    have hgrad := hgradbig p hpK hφ0 hhp
    have hQx := hQ p hpK
    have hQ2 : Q p.1 ^ 2 ≤ Qmax ^ 2 := pow_le_pow_left₀ (hQ0 p hpK) hQx.2 2
    rw [hθ_def, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hQ2 (by positivity : (0 : ℝ) ≤ m / 2),
      sq_nonneg Qmax]
  · intro p hpK h1' h2'
    have := hηle p ⟨hpK, h1', h2'⟩
    simp only at this
    linarith

/-- **Boundary margin.** If `φ < u` on `A ∩ P_b` (`P_b` closed, inside the compact `K`), then for
some `μ, r₃ > 0`, `φ + μ < u` on `P_b ∩ {dist(·, A) < r₃}`. -/
theorem exists_bdry_margin {Pb A : Set (E d × ℝ)} (hK : IsCompact K) (hPb : IsClosed Pb)
    (hPbK : Pb ⊆ K) (hAne : A.Nonempty) (hAc : IsClosed A) {u : E d × ℝ → ℝ}
    (hu : ContinuousOn u K) (hφ : Continuous φ) (hbd : ∀ p ∈ A ∩ Pb, φ p < u p) :
    ∃ μ > 0, ∃ r₃ > 0, ∀ p ∈ Pb, infDist p A < r₃ → φ p + μ < u p := by
  have hPbc : IsCompact Pb := hK.of_isClosed_subset hPb hPbK
  obtain ⟨m', hm', hm'le⟩ := exists_pos_le_of_isCompact (hPbc.inter_left hAc)
    ((hu.mono (inter_subset_right.trans hPbK)).sub hφ.continuousOn)
    (fun p hp ↦ sub_pos.2 (hbd p hp))
  have hB4 : IsCompact (Pb ∩ (fun p ↦ u p - φ p) ⁻¹' Iic (m' / 2)) :=
    hPbc.of_isClosed_subset (((hu.mono hPbK).sub hφ.continuousOn).preimage_isClosed_of_isClosed
      hPb isClosed_Iic) inter_subset_left
  obtain ⟨r₃, hr₃, hr₃le⟩ := exists_pos_le_of_isCompact hB4
    (continuous_infDist_pt A).continuousOn (fun p hp ↦ by
      rcases (infDist_nonneg (x := p) (s := A)).lt_or_eq with h | h
      · exact h
      · exfalso
        have hpA : p ∈ A := by
          have := (mem_closure_iff_infDist_zero hAne).2 h.symm
          rwa [hAc.closure_eq] at this
        have h1 := hm'le p ⟨hpA, hp.1⟩
        have h2 : u p - φ p ≤ m' / 2 := hp.2
        simp only at h1
        linarith)
  refine ⟨m' / 2, by positivity, r₃, hr₃, fun p hp hd ↦ ?_⟩
  by_contra hc
  push Not at hc
  exact (hr₃le p ⟨hp, show u p - φ p ≤ m' / 2 by linarith⟩).not_gt hd

end Geometry

/-! ### The glued subsolution -/

/-- The glued function `w = (Φ_{ε,θ}(φ + δ))₊` on `{D < 3r/2}`, `w = 0` elsewhere. -/
noncomputable def gluedSub (β : ℝ → ℝ) (θ ε δ r : ℝ) (φ D : E d × ℝ → ℝ) (p : E d × ℝ) : ℝ :=
  if D p < 3 * r / 2 then max (profileSubEps β θ ε (φ p + δ)) 0 else 0

section Glue

variable {β : ℝ → ℝ} {φ D : E d × ℝ → ℝ} {K : Set (E d × ℝ)} {Q : E d → ℝ}
  {θ r η δ ε : ℝ}

theorem gluedSub_nonneg (p : E d × ℝ) : 0 ≤ gluedSub β θ ε δ r φ D p := by
  unfold gluedSub; split_ifs <;> simp

theorem gluedSub_le (hβ : IsReactionProfile β) (hθ : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (p : E d × ℝ) : gluedSub β θ ε δ r φ D p ≤ max (φ p + δ) 0 + ε := by
  unfold gluedSub
  split_ifs
  · have := (abs_le.1 (abs_max_profileSubEps_sub_le hβ hθ hθ1 hε (φ p + δ))).2
    linarith
  · have := le_max_right (φ p + δ) 0
    linarith

theorem le_gluedSub (hβ : IsReactionProfile β) (hθ : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    {p : E d × ℝ} (hp : D p < 3 * r / 2) : φ p + δ ≤ gluedSub β θ ε δ r φ D p := by
  unfold gluedSub
  rw [if_pos hp]
  exact (self_le_profileSubEps hβ hθ hθ1 hε _).trans (le_max_left _ _)

/-- Where `Φ_ε(φ + δ) > 0` we have `φ > -2δ` (using `ε s₀ ≥ -c_θ ε ≥ -δ`). -/
theorem neg_two_mul_lt_of_profileSubEps_pos (hβ : IsReactionProfile β) (hθ : 0 < θ)
    (hθ1 : θ < 1) (hε : 0 < ε) (hcε : subConst θ * ε ≤ δ) {p : E d × ℝ}
    (hpos : 0 < profileSubEps β θ ε (φ p + δ)) : -(2 * δ) < φ p := by
  rw [profileSubEps_pos_iff hβ hθ hθ1 hε] at hpos
  have h0 := (profileSubZero_mem hβ hθ hθ1).1
  have : -(subConst θ) * ε ≤ profileSubZero β θ * ε := mul_le_mul_of_nonneg_right h0 hε.le
  nlinarith

variable (hβ : IsReactionProfile β) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hA3 : ∀ p ∈ K, r ≤ D p → D p ≤ 2 * r → φ p ≤ -η)
  (hδ : 0 < δ) (hδη : 4 * δ ≤ η) (hε : 0 < ε) (hcε : subConst θ * ε ≤ δ)
include hβ hθ hθ1 hA3 hδ hδη hε hcε

/-- Where the glued function is positive: `D < r`, `φ > -2δ`, and `w = Φ_ε(φ + δ) > 0`. -/
theorem gluedSub_pos_imp {p : E d × ℝ} (hp : p ∈ K) (hw : 0 < gluedSub β θ ε δ r φ D p) :
    D p < r ∧ -(2 * δ) < φ p ∧ D p < 3 * r / 2 ∧ 0 < profileSubEps β θ ε (φ p + δ) := by
  unfold gluedSub at hw
  split_ifs at hw with hD
  · have hΦ : 0 < profileSubEps β θ ε (φ p + δ) := by
      by_contra hc
      push Not at hc
      rw [max_eq_right hc] at hw
      exact lt_irrefl _ hw
    have hφp := neg_two_mul_lt_of_profileSubEps_pos hβ hθ hθ1 hε hcε hΦ
    refine ⟨?_, hφp, hD, hΦ⟩
    by_contra hc
    push Not at hc
    have hr : 0 ≤ r := by
      by_contra hr; push Not at hr
      have : 3 * r / 2 < r := by linarith
      exact absurd (hD.trans this) (not_lt.2 hc)
    have := hA3 p hp hc (by linarith)
    linarith
  · exact absurd hw (lt_irrefl _)

theorem gluedSub_eq_zero {p : E d × ℝ} (hp : p ∈ K) (hr : r < D p) :
    gluedSub β θ ε δ r φ D p = 0 := by
  rcases (gluedSub_nonneg (β := β) (θ := θ) (ε := ε) (δ := δ) (r := r) (φ := φ) (D := D)
    p).eq_or_lt with h | h
  · exact h.symm
  · exact absurd (gluedSub_pos_imp hβ hθ hθ1 hA3 hδ hδη hε hcε hp h).1 (not_lt.2 hr.le)

omit hA3 hδ hδη hcε hε in
theorem gluedSub_eventuallyEq (_hε : 0 < ε) {p : E d × ℝ} (hφ : Continuous φ) (hD : Continuous D)
    (hDp : D p < 3 * r / 2) (hΦ : 0 < profileSubEps β θ ε (φ p + δ)) :
    (fun q ↦ profileSubEps β θ ε (φ q + δ)) =ᶠ[𝓝 p] gluedSub β θ ε δ r φ D := by
  have hc : Continuous (fun q ↦ profileSubEps β θ ε (φ q + δ)) :=
    (profileSubEps_continuous hβ hθ hθ1).comp (hφ.add continuous_const)
  filter_upwards [hD.continuousAt.eventually (gt_mem_nhds hDp),
    hc.continuousAt.eventually (lt_mem_nhds hΦ)] with q h1 h2
  simp only [gluedSub, if_pos h1, max_eq_left h2.le]

theorem continuousOn_gluedSub (hφ : Continuous φ) (hD : Continuous D) (hr0 : 0 < r) :
    ContinuousOn (gluedSub β θ ε δ r φ D) K := by
  intro p hp
  rcases lt_or_ge r (D p) with hr | hr
  · -- `w = 0` near `p` in `K`
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_
      (gluedSub_eq_zero hβ hθ hθ1 hA3 hδ hδη hε hcε hp hr)
    filter_upwards [nhdsWithin_le_nhds (hD.continuousAt.eventually (lt_mem_nhds hr)),
      self_mem_nhdsWithin] with q hq hqK
    exact gluedSub_eq_zero hβ hθ hθ1 hA3 hδ hδη hε hcε hqK hq
  · have hDp : D p < 3 * r / 2 := by linarith
    have hc : Continuous (fun q ↦ max (profileSubEps β θ ε (φ q + δ)) 0) :=
      ((profileSubEps_continuous hβ hθ hθ1).comp (hφ.add continuous_const)).max
        continuous_const
    refine (hc.continuousAt.congr ?_).continuousWithinAt
    filter_upwards [hD.continuousAt.eventually (gt_mem_nhds hDp)] with q hq
    simp only [gluedSub, if_pos hq]

/-- **The glued function is a viscosity subsolution** of the semilinear equation in `V × (a, b]`,
given the margins (1)–(2) of `exists_sub_geometry` (with `2δ ≤ r`, `ε ≤ δ`). -/
theorem gluedSub_isSemilinearViscSubOn {V : Set (E d)} {a b : ℝ} (hV : IsOpen V)
    (hVK : V ×ˢ Ioc a b ⊆ K) (hφ : ContDiff ℝ ∞ φ) (hD : Continuous D)
    (hA1 : ∀ p ∈ K, D p < r → -r < φ p → dₜ φ p - lapₓ φ p < 0)
    (hA2 : ∀ p ∈ K, D p < r → -r < φ p → φ p ≤ 0 → Q p.1 ^ 2 ≤ θ * ‖gradₓ φ p‖ ^ 2)
    (hδr : 2 * δ ≤ r) (hεδ : ε ≤ δ) :
    IsSemilinearViscSubOn V Q β ε (Ioc a b) (gluedSub β θ ε δ r φ D) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  refine isSemilinearViscSubOn_of_local hV Ioc_leftNhds
    ((continuousOn_gluedSub hβ hθ hθ1 hA3 hδ hδη hε hcε hφ.continuous hD
      (by linarith)).mono hVK)
    fun p hp ↦ ?_
  have hpK := hVK hp
  rcases (gluedSub_nonneg (β := β) (θ := θ) (ε := ε) (δ := δ) (r := r) (φ := φ) (D := D)
    p).eq_or_lt with h0 | hpos
  · -- `w(p) = 0`: compare with `F = 0`
    refine ⟨fun _ ↦ 0, contDiff_const, h0, Eventually.of_forall fun q ↦ gluedSub_nonneg q, ?_⟩
    rw [← h0, hβ.betaEps_zero]
    simp [dₜ, lapₓ]
  · obtain ⟨hDr, hφδ, hD3, hΦ⟩ := gluedSub_pos_imp hβ hθ hθ1 hA3 hδ hδη hε hcε hpK hpos
    set f : ℝ → ℝ := fun s ↦ profileSubEps β θ ε (s + δ) with hf_def
    have hΦc : ContDiff ℝ 2 (profileSubEps β θ ε) :=
      (profileSubEps_contDiff hβ hθ hθ1).of_le (WithTop.coe_le_coe.2 le_top)
    have hfc : ContDiff ℝ 2 f := hΦc.comp (contDiff_id.add contDiff_const)
    have hdf : deriv f = fun s ↦ deriv (profileSubEps β θ ε) (s + δ) :=
      funext fun s ↦ deriv_comp_add_const _ _ _
    have hddf : ∀ s, deriv (deriv f) s = deriv (deriv (profileSubEps β θ ε)) (s + δ) :=
      fun s ↦ by rw [hdf]; exact deriv_comp_add_const _ _ _
    have heq := gluedSub_eventuallyEq hβ hθ hθ1 hε hφ.continuous hD hD3 hΦ
    refine ⟨fun q ↦ f (φ q), hfc.comp hφ2, heq.eq_of_nhds, heq.le, ?_⟩
    rw [heat_comp hfc hφ2, hddf, hdf, ← heq.eq_of_nhds]
    simp only
    have hLap : 0 ≤ lapₓ φ p - dₜ φ p := by
      have := hA1 p hpK hDr (by linarith)
      linarith
    have hineq := profileSubEps_ineq hβ hθ hθ1 hε (φ p + δ) (‖gradₓ φ p‖ ^ 2)
      (lapₓ φ p - dₜ φ p) (Q p.1) hLap (fun hb ↦ by
        have hlt := (mem_of_betaEps_profileSubEps_pos hβ hθ hθ1 hε hb).2
        exact hA2 p hpK hDr (by linarith) (by linarith))
    linarith

end Glue

/-! ### Step 2 of Proposition 5.3 -/

section Step2

variable {S : Setting d} {β : ℝ → ℝ} {T : ℝ} {εs : ℕ → ℝ} {us : ℕ → E d × ℝ → ℝ}
  {u : E d × ℝ → ℝ}

/-- The locally uniform limit is continuous on `U × (0, T]`. -/
theorem continuousOn_semilinearLimit
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    ContinuousOn u (S.U ×ˢ Ioc 0 T) :=
  hconv.continuousOn (Frequently.of_forall fun j ↦ (hsol j).1)

/-- The locally uniform limit is nonnegative. -/
theorem semilinearLimit_nonneg (hnn : ∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p)
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ u p := fun p hp ↦
  ge_of_tendsto (hconv.tendsto_at hp) (Eventually.of_forall fun j ↦ hnn j p hp)

/-- Uniform convergence on a compact subset of `U × (0, T]`. -/
theorem eventually_abs_sub_lt_of_isCompact
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) {K : Set (E d × ℝ)}
    (hK : IsCompact K) (hKΩ : K ⊆ S.U ×ˢ Ioc 0 T) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ j in atTop, ∀ q ∈ K, |us j q - u q| < c := by
  have h := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 (hconv.mono hKΩ)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h c hc] with j hj q hq
  rw [← Real.dist_eq, dist_comm]
  exact hj q hq

/-- **Proposition 5.3, Step 2**: the locally uniform
limit `u` of solutions `u_j` of the semilinear equation with `ε_j → 0` is a viscosity
supersolution of (3.1) in `U × (0, T]` (Definition 3.2). See the module docstring for the
localization replacing the paper's `φ + δ`. -/
theorem semilinear_limit_isParaSuper (hβ : IsReactionProfile β) (hεpos : ∀ j, 0 < εs j)
    (hεlim : Tendsto εs atTop (𝓝 0))
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hnn : ∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p)
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    IsParaSuper S.U S.Q (Ioc 0 T) u := by
  have hucont := continuousOn_semilinearLimit hsol hconv
  refine ⟨hucont, semilinearLimit_nonneg hnn hconv, ?_⟩
  intro V a b φ hcyl hφ hbd
  obtain ⟨hVo, hVb, hab, hKΩ⟩ := hcyl
  set K := closure V ×ˢ Icc a b with hK_def
  have hKc : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hposeq : posSetP φ univ = {q | 0 < φ q} := by ext; simp [posSetP]
  simp only [Prec, PrecOn, hposeq] at hbd ⊢
  intro p₀ ⟨hp₀P, hp₀cyl⟩
  by_contra hlt
  push Not at hlt
  have hp₀K : p₀ ∈ K := cyl_subset hp₀cyl
  set A := closure {q | 0 < φ q} ∩ K with hA_def
  have hAne : A.Nonempty := ⟨p₀, hp₀P, hp₀K⟩
  have hAc : IsClosed A := isClosed_closure.inter hKc.isClosed
  -- the coefficient `Q`
  obtain ⟨L, hL⟩ := S.lip
  have hVU : closure V ⊆ S.U := fun x hx ↦
    (hKΩ (show (x, a) ∈ K from ⟨hx, left_mem_Icc.2 hab.le⟩)).1
  have hQc : ContinuousOn (fun p : E d × ℝ ↦ S.Q p.1) K :=
    (hL.continuousOn.mono (hVU.trans subset_closure)).comp continuous_fst.continuousOn
      fun p hp ↦ hp.1
  have hQK : ∀ p ∈ K, S.Qmin ≤ S.Q p.1 ∧ S.Q p.1 ≤ S.Qmax := fun p hp ↦
    S.Q_mem _ (subset_closure (hVU hp.1))
  -- boundary margin
  have hPbK : parBdry V a b ⊆ K := parBdry_subset hab.le
  obtain ⟨μ, hμ, r₃, hr₃, hmargin⟩ := exists_bdry_margin hKc (isClosed_parBdry V a b) hPbK hAne
    hAc (hucont.mono hKΩ) hφ.1.continuous (fun p hp ↦ hbd p ⟨hp.1.1, hp.2⟩)
  -- geometry of `φ`
  obtain ⟨θ, hθ0, hθ1, r, hr, hrr₃, η, hη, hA1, hA2, hA3⟩ := exists_sub_geometry hφ.1 hKc hAne
    S.Qmin_pos hQc hQK hφ.2.1 hφ.2.2 hr₃
  set δ := min (min (η / 4) (μ / 4)) (r / 2) with hδ_def
  have hδ : 0 < δ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hδη : 4 * δ ≤ η := by have := min_le_left (min (η / 4) (μ / 4)) (r / 2);
                             have := min_le_left (η / 4) (μ / 4); linarith
  have hδμ : 4 * δ ≤ μ := by have := min_le_left (min (η / 4) (μ / 4)) (r / 2);
                             have := min_le_right (η / 4) (μ / 4); linarith
  have hδr : 2 * δ ≤ r := by have := min_le_right (min (η / 4) (μ / 4)) (r / 2); linarith
  -- choose `j`
  have hc0 : 0 ≤ subConst θ := subConst_nonneg hθ0 hθ1
  have hev1 : ∀ᶠ j in atTop, εs j ≤ δ := hεlim.eventually (ge_mem_nhds hδ)
  have hev2 : ∀ᶠ j in atTop, subConst θ * εs j ≤ δ := by
    have : Tendsto (fun j ↦ subConst θ * εs j) atTop (𝓝 0) := by
      simpa using hεlim.const_mul (subConst θ)
    exact this.eventually (ge_mem_nhds hδ)
  obtain ⟨j, hj1, hj2, hj3⟩ := (hev1.and (hev2.and
    (eventually_abs_sub_lt_of_isCompact hconv hKc hKΩ hδ))).exists
  have hε := hεpos j
  set D : E d × ℝ → ℝ := fun p ↦ infDist p A with hD_def
  have hDc : Continuous D := continuous_infDist_pt A
  set w := gluedSub β θ (εs j) δ r φ D with hw_def
  -- the solution `u_j` is a viscosity supersolution in `V × (a, b]`
  have hVU' : V ⊆ S.U := subset_closure.trans hVU
  have hIoc : Ioc a b ⊆ Ioc 0 T := fun t ht ↦
    (hKΩ (show (p₀.1, t) ∈ K from ⟨subset_closure hp₀cyl.1, Ioc_subset_Icc_self ht⟩)).2
  have hsuper := Registry.isSemilinearViscSuperOn_of_solOn hVo Ioc_leftNhds
    ((hsol j).mono_domain hVU' hIoc)
  have hsub := gluedSub_isSemilinearViscSubOn hβ hθ0 hθ1 hA3 hδ hδη hε hj2 hVo
    (prod_mono subset_closure Ioc_subset_Icc_self) hφ.1 hDc hA1 hA2 hδr hj1
  have hbdry : ∀ p ∈ parBdry V a b, w p ≤ us j p := by
    intro p hp
    have hpK := hPbK hp
    have hpΩ := hKΩ hpK
    rcases (gluedSub_nonneg (β := β) (θ := θ) (ε := εs j) (δ := δ) (r := r) (φ := φ) (D := D)
      p).eq_or_lt with h0 | hpos
    · rw [hw_def, ← h0]; exact hnn j p hpΩ
    · obtain ⟨hDr, hφδ, -, -⟩ := gluedSub_pos_imp hβ hθ0 hθ1 hA3 hδ hδη hε hj2 hpK hpos
      have hm := hmargin p hp (hDr.trans_le hrr₃)
      have hup := gluedSub_le (δ := δ) (r := r) (φ := φ) (D := D) hβ hθ0 hθ1 hε p
      have hj := abs_lt.1 (hj3 p hpK)
      rcases le_total 0 (φ p + δ) with hφ0 | hφ0
      · rw [max_eq_left hφ0] at hup; linarith
      · rw [max_eq_right hφ0] at hup; linarith
  have hcomp := Registry.semilinear_comparison hVo hVb hab
    ⟨L, hL.mono (closure_mono hVU')⟩ hβ hε
    (continuousOn_gluedSub hβ hθ0 hθ1 hA3 hδ hδη hε hj2 hφ.1.continuous hDc hr)
    ((hsol j).1.mono hKΩ) hsub hsuper hbdry
  have h1 := hcomp p₀ hp₀K
  have h2 := le_gluedSub (δ := δ) (r := r) (φ := φ) (D := D) hβ hθ0 hθ1 hε
    (show D p₀ < 3 * r / 2 by
      rw [hD_def]; simp only; rw [infDist_zero_of_mem (show p₀ ∈ A from ⟨hp₀P, hp₀K⟩)]
      positivity)
  have h3 := abs_lt.1 (hj3 p₀ hp₀K)
  linarith

end Step2

end PerronVariational

end
