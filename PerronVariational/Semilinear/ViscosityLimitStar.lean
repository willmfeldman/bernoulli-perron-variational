/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.ProfileSuper
public import PerronVariational.Statements.Intermediate
import Mathlib.Algebra.Order.Ring.Star
import PerronVariational.Registry.Comparison
import PerronVariational.Semilinear.ViscosityLimitCalculus
import PerronVariational.Semilinear.ViscosityLimitSub
import PerronVariational.Semilinear.ViscosityLimitSuper
import PerronVariational.Topology.KLimit

/-!
# Proposition 5.3, Step 1, with the authors' corrected set `E*`

Step 1 of the proof of Proposition 5.3 of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

For solutions `u_j ≥ 0` of `∂ₜu = Δu - Q² β_{ε_j}(u)` in `U × (0, T]` with `ε_j → 0` and
`u_j → u` locally uniformly, let
`E* = \overline{⋃_{0 < κ ≤ 1} limsup* {u_j > κ ε_j}}` (`semilinearLimitSetStar`). Then `(u, E*)`
is a relaxed viscosity subsolution of (3.1) in `U × (0, T]`
(`semilinear_limit_isParaRelaxedSub_star`). The paper states Proposition 5.3 with
`E = limsup* {u_j > ε_j}`, for which it is false (see `ViscosityLimitSub`); `E*` is the authors'
correction.

## Proof (the paper's Step 1, repaired)

Let `φ` be a classical strict supersolution on `V̄ × [a, b]` with `u ≺_{E*} φ` on `∂_P`, and
`p ∈ E* ∩ (V × (a, b])`.

* The boundary margin gives `u < φ - δ` on `E* ∩ ∂_P`, and a gradient margin gives `θ₀ > 1` with
  `θ₀ |∇φ|² ≤ Q²` on `{0 < φ ≤ r}`. For `θ̂ ∈ (1, θ₀]`, `Ψ_{ε,θ̂}(φ - δ)` is a classical
  supersolution of the semilinear equation in `V × (a, b]` for small `ε` (`profileSuperEps_ineq`;
  only `{φ > δ/2}` is constrained, where `φ` is a strict supersolution), and on `∂_P`,
  `u_j ≤ Ψ_{ε_j,θ̂}(φ - δ)` eventually: on `{u_j > κ_θ̂ ε_j}` by Lemma 5.2 (its `limsup*` lies in
  `E*`), elsewhere because `Ψ_{ε,θ̂} > κ_θ̂ ε`. This repairs the boundary step of the paper's
  proof. Comparison gives
  `u_j ≤ Ψ_{ε_j,θ̂}(φ - δ)` in `V̄ × [a, b]` (`eventually_le_profileSuperEps_of_bdry`).
* Case `φ(p) > 0`: as in the paper, `u_j(p) ≤ (φ(p) - δ)₊ + ε_j` contradicts `u(p) ≥ φ(p)`.
* Case `φ(p) ≤ 0`: `p ∈ E*` gives `κ ∈ (0, 1]` and points of `{u_j > κ ε_j}` near `p` where
  `φ - δ < -δ/2`; we choose `θ̂` with `κ_θ̂ < κ` (`exists_superKappa_lt`) and use
  `Ψ_{ε,θ̂}(-δ/2) < κ ε` for small `ε` (Lemma A.3(iii)).

The paper's case (ii) takes a neighbourhood of `p` inside `V × (a, b]`, which is impossible when
`p` lies at the top time `b`. We first enlarge the cylinder to `V × (a, b']`, `b' > b`, when
`b < T` (`exists_extend_cyl`, compactness); when `b = T` the approximating points automatically
have time `≤ b`.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-! ### The floor of the super-profile -/

/-- The floor `κ_θ̂` of the super-profile tends to `0` as `θ̂ ↓ 1`: for every `κ > 0` and `θ₀ > 1`
there is `θ̂ ∈ (1, θ₀]` with `κ_θ̂ < κ` (since `2𝓑(κ_θ̂) = (θ̃ - 1)/θ̃ ≤ (θ̂ - 1)/2`). -/
theorem exists_superKappa_lt {β : ℝ → ℝ} (hβ : IsReactionProfile β) {κ θ₀ : ℝ} (hκ : 0 < κ)
    (hθ₀ : 1 < θ₀) : ∃ θh : ℝ, 1 < θh ∧ θh ≤ θ₀ ∧ superKappa β θh < κ := by
  rcases le_or_gt 1 κ with h1 | h1
  · exact ⟨θ₀, hθ₀, le_rfl, (superKappa_lt_one hβ hθ₀).trans_le h1⟩
  have hB : 0 < bigBEps β 1 κ := hβ.bigB_pos hκ
  set m := min (θ₀ - 1) (bigBEps β 1 κ) with hm_def
  have hm : 0 < m := lt_min (by linarith) hB
  have hmB : m ≤ bigBEps β 1 κ := min_le_right _ _
  refine ⟨1 + m, by linarith, by linarith [min_le_left (θ₀ - 1) (bigBEps β 1 κ)], ?_⟩
  have hθh : 1 < 1 + m := by linarith
  by_contra hle
  push Not at hle
  have h1' := hβ.bigB_monotone hle
  have h2 := (superKappa_spec hβ hθh).2
  have ht : superTheta (1 + m) = 1 + m / 2 := by rw [superTheta]; ring
  have h3 : (superTheta (1 + m) - 1) / superTheta (1 + m) ≤ superTheta (1 + m) - 1 :=
    div_le_self (by rw [ht]; linarith) (by rw [ht]; linarith)
  rw [ht] at h3 h2
  linarith

/-! ### A gradient margin for strict supersolutions -/

/-- **Gradient margin.** If `|∇ₓφ| < Q` on `∂{φ > 0} ∩ K` (`K` compact), there are `θ₀ > 1` and
`r > 0` with `θ₀ |∇ₓφ|² ≤ Q²` on `K ∩ {0 < φ ≤ r}`. -/
theorem exists_super_grad_margin {φ : E d × ℝ → ℝ} {K : Set (E d × ℝ)} {Q : E d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hK : IsCompact K) (hQc : ContinuousOn (fun p : E d × ℝ ↦ Q p.1) K)
    {M2 : ℝ} (hQ : ∀ p ∈ K, Q p.1 ^ 2 ≤ M2)
    (h2 : ∀ p ∈ frontier {q | 0 < φ q} ∩ K, ‖gradₓ φ p‖ < Q p.1) :
    ∃ θ₀ > 1, ∃ r > 0, ∀ p ∈ K, 0 < φ p → φ p ≤ r → θ₀ * ‖gradₓ φ p‖ ^ 2 ≤ Q p.1 ^ 2 := by
  set P := {q | 0 < φ q} with hP
  have hPo : IsOpen P := isOpen_lt continuous_const hφ.continuous
  set f : E d × ℝ → ℝ := fun p ↦ Q p.1 ^ 2 - ‖gradₓ φ p‖ ^ 2 with hf_def
  have hfc : ContinuousOn f K := (hQc.pow 2).sub ((continuous_gradₓ hφ).norm.pow 2).continuousOn
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_isCompact (s := frontier P ∩ K)
    (hK.of_isClosed_subset (isClosed_frontier.inter hK.isClosed) inter_subset_right)
    (hfc.mono inter_subset_right) (fun p hp ↦ by
      have := h2 p hp
      have h0 : 0 ≤ ‖gradₓ φ p‖ := norm_nonneg _
      simp only [hf_def, sub_pos]
      exact pow_lt_pow_left₀ this h0 two_ne_zero)
  -- the bad set
  set B := (K ∩ closure P) ∩ f ⁻¹' Iic (m / 2) with hB_def
  have hBc : IsCompact B :=
    hK.of_isClosed_subset ((hfc.mono inter_subset_left).preimage_isClosed_of_isClosed
      (hK.isClosed.inter isClosed_closure) isClosed_Iic) (inter_subset_left.trans inter_subset_left)
  obtain ⟨r₀, hr₀, hr₀le⟩ := exists_pos_le_of_isCompact hBc hφ.continuous.continuousOn
    (fun p hp ↦ by
      have hge : 0 ≤ φ p := by
        have hcl : closure P ⊆ {q | 0 ≤ φ q} :=
          closure_minimal (fun q (hq : 0 < φ q) ↦ hq.le) (isClosed_le continuous_const
            hφ.continuous)
        exact hcl hp.1.2
      rcases hge.lt_or_eq with h | h
      · exact h
      · exfalso
        have hfr : p ∈ frontier P ∩ K := by
          refine ⟨?_, hp.1.1⟩
          rw [frontier, hPo.interior_eq]
          exact ⟨hp.1.2, fun h' ↦ by have : (0 : ℝ) < φ p := h'; linarith⟩
        have h1 := hmle p hfr
        have h2' : f p ≤ m / 2 := hp.2
        linarith)
  refine ⟨1 + m / (2 * (|M2| + 1)), by have : 0 < m / (2 * (|M2| + 1)) := by positivity
                                       linarith, r₀ / 2, by positivity, ?_⟩
  intro p hpK hφp hφr
  have hfp : m / 2 < f p := by
    by_contra hc
    push Not at hc
    have := hr₀le p ⟨⟨hpK, subset_closure hφp⟩, hc⟩
    linarith
  have hQp := hQ p hpK
  simp only [hf_def] at hfp
  set G := ‖gradₓ φ p‖ ^ 2 with hG
  have hG0 : 0 ≤ G := by positivity
  have hGM : G ≤ |M2| + 1 := by linarith [le_abs_self M2]
  have hkey : m / (2 * (|M2| + 1)) * G ≤ m / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    have : m * G ≤ m * (|M2| + 1) := mul_le_mul_of_nonneg_left hGM hm.le
    nlinarith
  nlinarith

/-! ### Enlarging a test cylinder in time -/

/-- A closed set missing `V̄ × [a, b]` (`V` bounded) also misses `V̄ × [a, b']` for some
`b' > b`. -/
theorem exists_gt_forall_notMem_cyl {V : Set (E d)} (hVb : Bornology.IsBounded V)
    {B : Set (E d × ℝ)} (hB : IsClosed B) {a b : ℝ}
    (h : ∀ q ∈ B, q ∉ closure V ×ˢ Icc a b) :
    ∃ b' > b, ∀ q ∈ B, q ∉ closure V ×ˢ Icc a b' := by
  set C := B ∩ (closure V ×ˢ Icc a (b + 1)) with hC
  have hCc : IsCompact C := (hVb.isCompact_closure.prod isCompact_Icc).inter_left hB
  rcases C.eq_empty_or_nonempty with h0 | hne
  · refine ⟨b + 1, by linarith, fun q hq hqK ↦ ?_⟩
    have : q ∈ C := ⟨hq, hqK⟩
    rw [h0] at this
    exact this
  obtain ⟨q₀, hq₀, hmin⟩ := hCc.exists_isMinOn hne continuous_snd.continuousOn
  have hq₀b : b < q₀.2 := by
    by_contra hc
    push Not at hc
    exact h q₀ hq₀.1 ⟨hq₀.2.1, hq₀.2.2.1, hc⟩
  have hq₀1 : q₀.2 ≤ b + 1 := hq₀.2.2.2
  refine ⟨(b + q₀.2) / 2, by linarith, fun q hq hqK ↦ ?_⟩
  have hqC : q ∈ C := ⟨hq, hqK.1, hqK.2.1, by linarith [hqK.2.2]⟩
  have := hmin hqC
  simp only [Set.mem_ofPred_eq] at this
  linarith [hqK.2.2]

section Star

variable {S : Setting d} {β : ℝ → ℝ} {T : ℝ} {εs : ℕ → ℝ} {us : ℕ → E d × ℝ → ℝ}
  {u : E d × ℝ → ℝ}

/-- **Enlarging the cylinder.** If `b < T`, a strict supersolution `φ` on `V̄ × [a, b]` with
`u ≺_E φ` on `∂_P(V × (a, b])` (`E` closed) is still a strict supersolution on `V̄ × [a, b']`
with `u ≺_E φ` on `∂_P(V × (a, b'])`, for some `b' ∈ (b, T]`. -/
theorem exists_extend_cyl {Eset : Set (E d × ℝ)} (hE : IsClosed Eset)
    (hucont : ContinuousOn u (S.U ×ˢ Ioc 0 T))
    {V : Set (E d)} {a b : ℝ} {φ : E d × ℝ → ℝ} (hcyl : AdmissibleCyl S.U (Ioc 0 T) V a b)
    (hφ : IsClassicalStrictParaSuper S.Q φ V a b) (hbd : PrecOn u φ Eset (parBdry V a b))
    (hbT : b < T) :
    ∃ b' > b, AdmissibleCyl S.U (Ioc 0 T) V a b' ∧ IsClassicalStrictParaSuper S.Q φ V a b' ∧
      PrecOn u φ Eset (parBdry V a b') := by
  obtain ⟨hVo, hVb, hab, hKΩ⟩ := hcyl
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (WithTop.coe_le_coe.2 le_top)
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨L, hLip⟩ := S.lip
  have hVU : ∀ x ∈ closure V, x ∈ S.U ∧ 0 < a := fun x hx ↦ by
    have := hKΩ (show (x, a) ∈ closure V ×ˢ Icc a b from ⟨hx, left_mem_Icc.2 hab.le⟩)
    exact ⟨this.1, this.2.1⟩
  -- (1) the heat inequality
  obtain ⟨b₁, hb₁, h₁⟩ := exists_gt_forall_notMem_cyl hVb
    (B := closure {q | 0 < φ q} ∩ {q | dₜ φ q - lapₓ φ q ≤ 0})
    (isClosed_closure.inter (isClosed_le ((continuous_dₜ hφ1).sub (continuous_lapₓ hφ2))
      continuous_const))
    (fun q hq hqK ↦ by
      have h1 := hφ.2.1 q ⟨hq.1, hqK⟩
      have h2 : dₜ φ q - lapₓ φ q ≤ 0 := hq.2
      linarith)
  -- (2) the gradient inequality
  have hc2 : ContinuousOn (fun q : E d × ℝ ↦ ‖gradₓ φ q‖ - S.Q q.1) (closure S.U ×ˢ univ) :=
    (continuous_gradₓ hφ1).norm.continuousOn.sub
      (hLip.continuousOn.comp continuous_fst.continuousOn fun q hq ↦ hq.1)
  obtain ⟨b₂, hb₂, h₂⟩ := exists_gt_forall_notMem_cyl hVb
    (B := (frontier {q | 0 < φ q} ∩ (closure S.U ×ˢ univ)) ∩
      (fun q : E d × ℝ ↦ ‖gradₓ φ q‖ - S.Q q.1) ⁻¹' Ici 0)
    ((hc2.mono inter_subset_right).preimage_isClosed_of_isClosed
      (isClosed_frontier.inter (isClosed_closure.prod isClosed_univ)) isClosed_Ici)
    (fun q hq hqK ↦ by
      have h1 := hφ.2.2 q ⟨hq.1.1, hqK⟩
      have h2 : (0 : ℝ) ≤ ‖gradₓ φ q‖ - S.Q q.1 := hq.2
      linarith)
  -- (3) the boundary ordering on the lateral boundary
  have hsub3 : Eset ∩ (frontier V ×ˢ Icc a T) ⊆ S.U ×ˢ Ioc 0 T := fun q hq ↦ by
    obtain ⟨hU, ha⟩ := hVU q.1 (frontier_subset_closure hq.2.1)
    exact ⟨hU, ha.trans_le hq.2.2.1, hq.2.2.2⟩
  obtain ⟨b₃, hb₃, h₃⟩ := exists_gt_forall_notMem_cyl hVb
    (B := (Eset ∩ (frontier V ×ˢ Icc a T)) ∩ (fun q ↦ u q - φ q) ⁻¹' Ici 0)
    (((hucont.mono hsub3).sub hφ.1.continuous.continuousOn).preimage_isClosed_of_isClosed
      (hE.inter (isClosed_frontier.prod isClosed_Icc)) isClosed_Ici)
    (fun q hq hqK ↦ by
      have h1 := hbd q ⟨hq.1.1, Or.inr ⟨hq.1.2.1, hqK.2⟩⟩
      have h2 : (0 : ℝ) ≤ u q - φ q := hq.2
      linarith)
  set b' := min (min b₁ b₂) (min b₃ T) with hb'_def
  have hb'1 : b' ≤ b₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hb'2 : b' ≤ b₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hb'3 : b' ≤ b₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hb'T : b' ≤ T := (min_le_right _ _).trans (min_le_right _ _)
  have hbb' : b < b' := lt_min (lt_min hb₁ hb₂) (lt_min hb₃ hbT)
  refine ⟨b', hbb', ⟨hVo, hVb, hab.trans hbb', fun q hq ↦ ?_⟩, ⟨hφ.1, fun q hq ↦ ?_, fun q hq ↦ ?_⟩,
    fun q ⟨hqE, hqP⟩ ↦ ?_⟩
  · obtain ⟨hU, ha⟩ := hVU q.1 hq.1
    exact ⟨hU, ha.trans_le hq.2.1, hq.2.2.trans hb'T⟩
  · by_contra hc
    push Not at hc
    exact h₁ q ⟨hq.1, hc⟩ ⟨hq.2.1, hq.2.2.1, hq.2.2.2.trans hb'1⟩
  · by_contra hc
    push Not at hc
    exact h₂ q ⟨⟨hq.1, subset_closure (hVU q.1 hq.2.1).1, mem_univ _⟩, sub_nonneg.2 hc⟩
      ⟨hq.2.1, hq.2.2.1, hq.2.2.2.trans hb'2⟩
  · rcases hqP with h | h
    · exact hbd q ⟨hqE, Or.inl h⟩
    · by_contra hc
      push Not at hc
      exact h₃ q ⟨⟨hqE, h.1, h.2.1, h.2.2.trans hb'T⟩, sub_nonneg.2 hc⟩
        ⟨frontier_subset_closure h.1, h.2.1, h.2.2.trans hb'3⟩

/-! ### The comparison with `Ψ_{ε,θ̂}(φ - δ)` -/

/-- **Comparison with the super-profile (Step 1 of Proposition 5.3, repaired).** Let `φ` be a
classical strict supersolution on `V̄ × [a, b]` with `θ₀ |∇ₓφ|² ≤ Q²` on `{0 < φ ≤ r}`, let
`1 < θ̂ ≤ θ₀`, `0 < δ`, `2δ ≤ r`, and suppose `u < φ - δ` on `∂_P ∩ limsup* {u_j > κ_θ̂ ε_j}`.
Then eventually `u_j ≤ Ψ_{ε_j,θ̂}(φ - δ)` on `V̄ × [a, b]`. -/
theorem eventually_le_profileSuperEps_of_bdry (hβ : IsReactionProfile β)
    (hεpos : ∀ j, 0 < εs j) (hεlim : Tendsto εs atTop (𝓝 0))
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T))
    {V : Set (E d)} {a b : ℝ} {φ : E d × ℝ → ℝ} (hcyl : AdmissibleCyl S.U (Ioc 0 T) V a b)
    (hφ : IsClassicalStrictParaSuper S.Q φ V a b) {θ₀ r : ℝ}
    (hgrad : ∀ p ∈ closure V ×ˢ Icc a b, 0 < φ p → φ p ≤ r →
      θ₀ * ‖gradₓ φ p‖ ^ 2 ≤ S.Q p.1 ^ 2)
    {θh δ : ℝ} (hθh : 1 < θh) (hθh₀ : θh ≤ θ₀) (hδ : 0 < δ) (hδr : 2 * δ ≤ r)
    (hL : ∀ q ∈ upperKLimit (fun j ↦ {p ∈ S.U ×ˢ Ioc 0 T | superKappa β θh * εs j < us j p})
        atTop ∩ parBdry V a b, u q < φ q - δ) :
    ∀ᶠ j in atTop, ∀ q ∈ closure V ×ˢ Icc a b,
      us j q ≤ profileSuperEps β θh (εs j) (φ q - δ) := by
  obtain ⟨hVo, hVb, hab, hKΩ⟩ := hcyl
  set Ω := S.U ×ˢ Ioc 0 T with hΩ_def
  set K := closure V ×ˢ Icc a b with hK_def
  set P := parBdry V a b with hP_def
  have hKc : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hPK : P ⊆ K := parBdry_subset hab.le
  have hPc : IsCompact P := hKc.of_isClosed_subset (isClosed_parBdry V a b) hPK
  have hucont := continuousOn_semilinearLimit hsol hconv
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (WithTop.coe_le_coe.2 le_top)
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (WithTop.coe_le_coe.2 le_top)
  set κh := superKappa β θh with hκh
  -- (1) the boundary ordering on `{u_j > κ_θ̂ ε_j}` (Lemma 5.2)
  have hunifP : TendstoUniformlyOn us u atTop P :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hPc).1
      (hconv.mono (hPK.trans hKΩ))
  have hbd1 := precOn_eventually_of_tendsto
    (E := upperKLimit (fun j ↦ {p ∈ Ω | κh * εs j < us j p}) atTop)
    (E' := fun j ↦ {p ∈ Ω | κh * εs j < us j p}) (v := fun q ↦ φ q - δ)
    (vs := fun _ q ↦ φ q - δ) hPc (hucont.mono (hPK.trans hKΩ))
    (hφ.1.continuous.sub continuous_const).continuousOn hL hunifP
    (Metric.tendstoUniformlyOn_iff.2 fun c hc ↦ Eventually.of_forall fun _ x _ ↦ by simpa using hc)
    subset_rfl
  -- (2) constants for the profile inequality
  obtain ⟨L, hLip⟩ := S.lip
  have hVU : closure V ⊆ S.U := fun x hx ↦
    (hKΩ (show (x, a) ∈ K from ⟨hx, left_mem_Icc.2 hab.le⟩)).1
  have hVU' : V ⊆ S.U := subset_closure.trans hVU
  obtain ⟨Gmax, hGmax⟩ := hKc.exists_bound_of_continuousOn
    ((continuous_gradₓ hφ1).norm.pow 2).continuousOn
  obtain ⟨D, hD⟩ := hKc.exists_bound_of_continuousOn
    ((continuous_lapₓ hφ2).sub (continuous_dₜ hφ1)).continuousOn
  obtain ⟨ε₀, hε₀, hineq⟩ := profileSuperEps_ineq hβ (a₀ := δ / 2) (Gmax := Gmax) (D := D)
    (by positivity) hθh S.Qmin_pos
  have hev : ∀ᶠ j in atTop, εs j ≤ ε₀ := hεlim.eventually (ge_mem_nhds hε₀)
  filter_upwards [hbd1, hev] with j hj1 hj2 q hq
  have hε := hεpos j
  set w : E d × ℝ → ℝ := fun q ↦ profileSuperEps β θh (εs j) (φ q - δ) with hw_def
  set f : ℝ → ℝ := fun s ↦ profileSuperEps β θh (εs j) (s - δ) with hf_def
  have hΨc : ContDiff ℝ 2 (profileSuperEps β θh (εs j)) :=
    (profileSuperEps_contDiff hβ hθh).of_le (WithTop.coe_le_coe.2 le_top)
  have hfc : ContDiff ℝ 2 f := hΨc.comp (contDiff_id.sub contDiff_const)
  have hwc : ContDiff ℝ 2 w := hfc.comp hφ2
  have hdf : deriv f = fun s ↦ deriv (profileSuperEps β θh (εs j)) (s - δ) :=
    funext fun s ↦ deriv_comp_sub_const _ _ _
  have hddf : ∀ s, deriv (deriv f) s = deriv (deriv (profileSuperEps β θh (εs j))) (s - δ) :=
    fun s ↦ by rw [hdf]; exact deriv_comp_sub_const _ _ _
  -- (3) `w` is a viscosity supersolution in `V × (a, b]`
  have hsuper : IsSemilinearViscSuperOn V S.Q β (εs j) (Ioc a b) w := by
    refine isSemilinearViscSuperOn_of_local hVo Ioc_leftNhds hwc.continuous.continuousOn
      fun p hp ↦ ⟨w, hwc, rfl, Eventually.of_forall fun _ ↦ le_rfl, ?_⟩
    have hpK : p ∈ K := ⟨subset_closure hp.1, Ioc_subset_Icc_self hp.2⟩
    have hwf : w = fun q ↦ f (φ q) := rfl
    rw [hwf, heat_comp hfc hφ2, hddf, hdf]
    have hQp := S.Q_mem p.1 (subset_closure (hVU hpK.1))
    have hG := hGmax p hpK
    have hDp := hD p hpK
    simp only [Real.norm_eq_abs] at hG hDp
    have h := hineq (εs j) ⟨hε, hj2⟩ (φ p - δ) (‖gradₓ φ p‖ ^ 2) (lapₓ φ p - dₜ φ p) (S.Q p.1)
      (fun hs ↦ by
        have hpos : 0 < φ p := by linarith
        have := hφ.2.1 p ⟨subset_closure hpos, hpK⟩
        linarith)
      (fun hs ↦ by
        have hs' := abs_le.1 hs
        exact (mul_le_mul_of_nonneg_right hθh₀ (by positivity)).trans
          (hgrad p hpK (by linarith) (by linarith)))
      (by positivity) ((le_abs_self _).trans hG) hDp hQp.1
    linarith
  -- (4) `u_j` is a viscosity subsolution in `V × (a, b]`
  have hIoc : Ioc a b ⊆ Ioc 0 T := fun t ht ↦
    (hKΩ (show (q.1, t) ∈ K from ⟨hq.1, Ioc_subset_Icc_self ht⟩)).2
  have hsub := Registry.isSemilinearViscSubOn_of_solOn hVo Ioc_leftNhds
    ((hsol j).mono_domain hVU' hIoc)
  -- (5) the boundary ordering
  have hbdry : ∀ p ∈ parBdry V a b, us j p ≤ w p := by
    intro p hp
    by_cases hp' : κh * εs j < us j p
    · have := hj1 p ⟨⟨hKΩ (hPK hp), hp'⟩, hp⟩
      exact this.le.trans ((le_max_left _ _).trans (max_le_profileSuperEps hβ hθh hε _))
    · push Not at hp'
      have := mul_kappa_lt_profileSuperEps hβ hθh hε (φ p - δ)
      rw [mul_comm] at this
      exact hp'.trans this.le
  exact Registry.semilinear_comparison hVo hVb hab ⟨L, hLip.mono (closure_mono hVU')⟩ hβ hε
    ((hsol j).1.mono hKΩ) hwc.continuous.continuousOn hsub hsuper hbdry q hq

/-! ### Step 1 with `E*` -/

/-- **Core of Step 1 with `E*`.** Let `φ` be a strict supersolution on `V̄ × [a, b]` with
`u ≺_{E*} φ` on `∂_P`, and `p ∈ E* ∩ (V × (a, b])` such that points of `U × (0, T]` near `p`
have time `≤ b`. Then `u(p) < φ(p)`. -/
theorem relaxedSub_star_core (hβ : IsReactionProfile β) (hεpos : ∀ j, 0 < εs j)
    (hεlim : Tendsto εs atTop (𝓝 0))
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T))
    {V : Set (E d)} {a b : ℝ} {φ : E d × ℝ → ℝ} (hcyl : AdmissibleCyl S.U (Ioc 0 T) V a b)
    (hφ : IsClassicalStrictParaSuper S.Q φ V a b)
    (hbd : PrecOn u φ (semilinearLimitSetStar S.U (Ioc 0 T) εs us) (parBdry V a b))
    {p : E d × ℝ} (hpE : p ∈ semilinearLimitSetStar S.U (Ioc 0 T) εs us)
    (hpcyl : p ∈ cyl V a b) (htime : ∀ᶠ q in 𝓝 p, q ∈ S.U ×ˢ Ioc 0 T → q.2 ≤ b) :
    u p < φ p := by
  set Ω := S.U ×ˢ Ioc 0 T with hΩ_def
  set Estar := semilinearLimitSetStar S.U (Ioc 0 T) εs us with hEstar
  set Lk : ℝ → Set (E d × ℝ) := fun κ ↦
    upperKLimit (fun j ↦ {q ∈ Ω | κ * εs j < us j q}) atTop with hLk_def
  have hLk : ∀ κ ∈ Ioc (0 : ℝ) 1, Lk κ ⊆ Estar := fun κ hκ ↦
    (subset_iUnion₂ (s := fun κ (_ : κ ∈ Ioc (0 : ℝ) 1) ↦ Lk κ) κ hκ).trans subset_closure
  have hcyl' := hcyl
  obtain ⟨hVo, hVb, hab, hKΩ⟩ := hcyl'
  set K := closure V ×ˢ Icc a b with hK_def
  set P := parBdry V a b with hP_def
  have hKc : IsCompact K := hVb.isCompact_closure.prod isCompact_Icc
  have hPK : P ⊆ K := parBdry_subset hab.le
  have hPc : IsCompact P := hKc.of_isClosed_subset (isClosed_parBdry V a b) hPK
  have hucont := continuousOn_semilinearLimit hsol hconv
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (WithTop.coe_le_coe.2 le_top)
  -- boundary margin
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_of_isCompact (s := Estar ∩ P)
    (hPc.inter_left isClosed_closure) (f := fun q ↦ φ q - u q)
    (hφ.1.continuous.continuousOn.sub
      (hucont.mono (inter_subset_right.trans (hPK.trans hKΩ))))
    (fun q hq ↦ sub_pos.2 (hbd q hq))
  -- gradient margin
  obtain ⟨L, hLip⟩ := S.lip
  have hVU : closure V ⊆ S.U := fun x hx ↦
    (hKΩ (show (x, a) ∈ K from ⟨hx, left_mem_Icc.2 hab.le⟩)).1
  have hQc : ContinuousOn (fun q : E d × ℝ ↦ S.Q q.1) K :=
    (hLip.continuousOn.mono (hVU.trans subset_closure)).comp continuous_fst.continuousOn
      fun q hq ↦ hq.1
  have hQK : ∀ q ∈ K, S.Qmin ≤ S.Q q.1 ∧ S.Q q.1 ≤ S.Qmax := fun q hq ↦
    S.Q_mem _ (subset_closure (hVU hq.1))
  obtain ⟨θ₀, hθ₀, r, hr, hgrad⟩ := exists_super_grad_margin hφ1 hKc hQc (M2 := S.Qmax ^ 2)
    (fun q hq ↦ pow_le_pow_left₀ (S.Qmin_pos.le.trans (hQK q hq).1) (hQK q hq).2 2)
    (fun q hq ↦ hφ.2.2 q hq)
  -- the comparison, for admissible `θ̂, δ`
  have hcomp : ∀ θh δ : ℝ, 1 < θh → θh ≤ θ₀ → 0 < δ → 2 * δ ≤ r → δ < μ →
      ∀ᶠ j in atTop, ∀ q ∈ K, us j q ≤ profileSuperEps β θh (εs j) (φ q - δ) := by
    intro θh δ hθh hθh₀ hδ hδr hδμ
    refine eventually_le_profileSuperEps_of_bdry hβ hεpos hεlim hsol hconv hcyl hφ hgrad hθh
      hθh₀ hδ hδr ?_
    rintro q ⟨hqL, hqP⟩
    have hqE : q ∈ Estar :=
      hLk _ ⟨superKappa_pos hβ hθh, (superKappa_lt_one hβ hθh).le⟩ hqL
    have := hμle q ⟨hqE, hqP⟩
    linarith
  have hpK : p ∈ K := cyl_subset hpcyl
  rcases lt_or_ge 0 (φ p) with hφp | hφp
  · -- case (i): `φ(p) > 0`
    by_contra hle
    push Not at hle
    set δ := min (min (μ / 2) (r / 2)) (φ p / 2) with hδ_def
    have hδ : 0 < δ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
    have hδμ : δ < μ := by
      have := min_le_left (min (μ / 2) (r / 2)) (φ p / 2)
      have := min_le_left (μ / 2) (r / 2); linarith
    have hδr : 2 * δ ≤ r := by
      have := min_le_left (min (μ / 2) (r / 2)) (φ p / 2)
      have := min_le_right (μ / 2) (r / 2); linarith
    have hδφ : 2 * δ ≤ φ p := by
      have := min_le_right (min (μ / 2) (r / 2)) (φ p / 2); linarith
    have hev := hcomp θ₀ δ hθ₀ le_rfl hδ hδr hδμ
    have ht : ∀ᶠ j in atTop, us j p ∈ ball (u p) (δ / 3) :=
      (hconv.tendsto_at (hKΩ hpK)).eventually (ball_mem_nhds _ (by positivity))
    have hε3 : ∀ᶠ j in atTop, εs j < δ / 3 := hεlim.eventually (gt_mem_nhds (by positivity))
    obtain ⟨j, hj1, hj2, hj3⟩ := (hev.and (ht.and hε3)).exists
    have h1 := hj1 p hpK
    have h2 := (abs_le.1 (abs_profileSuperEps_sub_le hβ hθ₀ (hεpos j) (φ p - δ))).2
    rw [max_eq_left (by linarith)] at h2
    rw [mem_ball, Real.dist_eq, abs_lt] at hj2
    linarith
  · -- case (ii): `φ(p) ≤ 0`
    set δ := min (μ / 2) (r / 2) with hδ_def
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    have hδμ : δ < μ := by have := min_le_left (μ / 2) (r / 2); linarith
    have hδr : 2 * δ ≤ r := by have := min_le_right (μ / 2) (r / 2); linarith
    set N := {q | φ q < δ / 2} ∩ (V ×ˢ Ioi a) ∩ {q | q ∈ Ω → q.2 ≤ b} with hN_def
    have hN : N ∈ 𝓝 p := by
      refine inter_mem (inter_mem ?_ ((hVo.prod isOpen_Ioi).mem_nhds ⟨hpcyl.1, hpcyl.2.1⟩))
        htime
      exact (isOpen_lt hφ.1.continuous continuous_const).mem_nhds
        (show φ p < δ / 2 by linarith)
    obtain ⟨q, hqN, hqU⟩ := mem_closure_iff_nhds.1 hpE (interior N) (interior_mem_nhds.2 hN)
    rw [mem_iUnion₂] at hqU
    obtain ⟨κ, hκ, hqL⟩ := hqU
    obtain ⟨θh, hθh, hθh₀, hκθ⟩ := exists_superKappa_lt hβ hκ.1 hθ₀
    have hev := hcomp θh δ hθh hθh₀ hδ hδr hδμ
    -- the exponential tail: `Ψ_{1,θ̂}(-δ/(2ε)) < κ` for small `ε`
    have htail : ∀ᶠ j in atTop, profileSuper β θh (-(δ / 2) / εs j) < κ := by
      have h1 : Tendsto εs atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨hεlim, Eventually.of_forall hεpos⟩
      have h2 : Tendsto (fun j ↦ -(δ / 2) / εs j) atTop atBot := by
        have := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop_of_neg
          (show -(δ / 2) < 0 by linarith)
        simpa [div_eq_mul_inv] using this
      exact ((tendsto_profileSuper_atBot hβ hθh).comp h2).eventually (gt_mem_nhds hκθ)
    have hfreq := hqL (interior N) (isOpen_interior.mem_nhds hqN)
    obtain ⟨j, ⟨q', ⟨hq'Ω, hq'κ⟩, hq'N⟩, hj1, hj2⟩ :=
      (hfreq.and_eventually (hev.and htail)).exists
    obtain ⟨⟨hφq', hq'V⟩, hq'b⟩ := interior_subset hq'N
    have hφq'' : φ q' < δ / 2 := hφq'
    have hq'K : q' ∈ K := ⟨subset_closure hq'V.1, le_of_lt hq'V.2, hq'b hq'Ω⟩
    have h1 := hj1 q' hq'K
    have hε := hεpos j
    have h2 : profileSuperEps β θh (εs j) (φ q' - δ) ≤
        profileSuperEps β θh (εs j) (-(δ / 2)) := by
      unfold profileSuperEps
      exact mul_le_mul_of_nonneg_left ((profileSuper_strictMono hβ hθh).monotone
        (div_le_div_of_nonneg_right (by linarith) hε.le)) hε.le
    have h3 : profileSuperEps β θh (εs j) (-(δ / 2)) < κ * εs j := by
      unfold profileSuperEps
      rw [mul_comm κ]
      exact mul_lt_mul_of_pos_left hj2 hε
    have h4 : κ * εs j < us j q' := hq'κ
    linarith

/-- **Proposition 5.3, Step 1, with `E*`** (the authors' corrected set): for any
sequence of nonnegative solutions `u_j` with `ε_j → 0` and `u_j → u` locally uniformly in
`U × (0, T]`, `(u, E*)` with `E* = \overline{⋃_{0<κ≤1} limsup* {u_j > κ ε_j}}` is a relaxed
viscosity subsolution of (3.1) in `U × (0, T]`. -/
theorem semilinear_limit_isParaRelaxedSub_star (hβ : IsReactionProfile β)
    (hεpos : ∀ j, 0 < εs j) (hεlim : Tendsto εs atTop (𝓝 0))
    (hsol : ∀ j, IsSemilinearSolOn S.U S.Q β (εs j) (Ioc 0 T) (us j))
    (hnn : ∀ j, ∀ p ∈ S.U ×ˢ Ioc 0 T, 0 ≤ us j p)
    (hconv : TendstoLocallyUniformlyOn us u atTop (S.U ×ˢ Ioc 0 T)) :
    IsParaRelaxedSub S.U S.Q (Ioc 0 T) u (semilinearLimitSetStar S.U (Ioc 0 T) εs us) := by
  have hucont := continuousOn_semilinearLimit hsol hconv
  have hunn := semilinearLimit_nonneg hnn hconv
  refine ⟨hucont, hunn, isClosed_closure, ?_, ?_, ?_⟩
  · refine closure_minimal (iUnion₂_subset fun κ _ ↦ ?_) (isClosed_closure.prod isClosed_closure)
    rw [← closure_prod_eq]
    exact upperKLimit_subset_closure_of_eventually (Eventually.of_forall fun j ↦ sep_subset _ _)
  · intro q hq
    refine subset_closure (mem_iUnion₂.2 ⟨1, ⟨one_pos, le_rfl⟩, ?_⟩)
    have := posSetP_subset_semilinearLimitSet hεlim hconv hq
    simpa [semilinearLimitSet] using this
  · rintro V a b φ hcyl hφ hbd p ⟨hpE, hpcyl⟩
    have hbT : b ≤ T := (hcyl.2.2.2 (show (p.1, b) ∈ closure V ×ˢ Icc a b from
      ⟨subset_closure hpcyl.1, hcyl.2.2.1.le, le_rfl⟩)).2.2
    rcases hbT.lt_or_eq with hbT | hbT
    · obtain ⟨b', hb', hcyl', hφ', hbd'⟩ :=
        exists_extend_cyl isClosed_closure hucont hcyl hφ hbd hbT
      have hpb : p.2 < b' := hpcyl.2.2.trans_lt hb'
      exact relaxedSub_star_core hβ hεpos hεlim hsol hconv hcyl' hφ' hbd' hpE
        ⟨hpcyl.1, hpcyl.2.1, hpb.le⟩
        ((continuous_snd.continuousAt.eventually (gt_mem_nhds hpb)).mono fun q hq _ ↦ hq.le)
    · exact relaxedSub_star_core hβ hεpos hεlim hsol hconv hcyl hφ hbd hpE hpcyl
        (Eventually.of_forall fun q hq ↦ hbT ▸ hq.2.2)

end Star

end PerronVariational

end
