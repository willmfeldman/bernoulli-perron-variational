/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.SemilinearEstimates
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Topology.UniformSpace.Ascoli
import PerronVariational.Inner.ReactionBound
import PerronVariational.Semilinear.Calculus

/-!
# Arzelà–Ascoli compactness for the semilinear approximation

Compactness step of the proof of Proposition 4.1 of F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981.

* `Inner.exists_tendstoLocallyUniformlyOn_subseq`: a pointwise bounded, pointwise equicontinuous
  sequence of functions continuous on an open set `Ω` of a locally compact second countable metric
  space has a subsequence converging locally uniformly on `Ω` to a function continuous on `Ω`
  (Arzelà–Ascoli in the compact-open topology plus metrizability of `C(Ω, ℝ)`; this replaces the
  explicit diagonal argument over an exhaustion).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal Interval

@[expose] public section

namespace PerronVariational

namespace Inner

section Subseq

variable {α β ι : Type*} [UniformSpace β] [TopologicalSpace α]

/-- Locally uniform convergence passes to reparametrizations `F ∘ φ` with `φ → ∞`. -/
theorem TendstoLocallyUniformlyOn.comp_tendsto {F : ℕ → α → β} {f : α → β} {s : Set α}
    (h : TendstoLocallyUniformlyOn F f atTop s) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) f atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := h u hu x hx
  exact ⟨t, ht, hφ.eventually hev⟩

end Subseq

section ArzelaAscoli

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]

/-- **Arzelà–Ascoli, sequential form on an open set.** Let `Ω` be open in a locally compact second
countable metric space and `f n` continuous on `Ω`, pointwise bounded on `Ω`, and equicontinuous at
every point of `Ω`. Then a subsequence converges locally uniformly on `Ω` to a function continuous
on `Ω`. -/
theorem exists_tendstoLocallyUniformlyOn_subseq {Ω : Set X} (hΩ : IsOpen Ω) (f : ℕ → X → ℝ)
    (hcont : ∀ n, ContinuousOn (f n) Ω) (hbdd : ∀ x ∈ Ω, ∃ B : ℝ, ∀ n, |f n x| ≤ B)
    (heq : ∀ x ∈ Ω, ∀ η > 0, ∀ᶠ y in 𝓝 x, ∀ n, |f n y - f n x| < η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : X → ℝ, ContinuousOn f₀ Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ f (φ n)) f₀ atTop Ω := by
  classical
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  -- pointwise bounds and equicontinuity neighbourhoods, as functions on the subtype
  choose B hB using fun x : Ω ↦ hbdd x x.2
  have hN : ∀ (x : Ω) (η : ℝ), ∃ N ∈ 𝓝 x, 0 < η → ∀ n, ∀ y ∈ N, |f n y - f n x| < η := by
    intro x η
    by_cases hη : 0 < η
    · have := heq x x.2 η hη
      exact ⟨Subtype.val ⁻¹' {y | ∀ n, |f n y - f n x| < η},
        continuous_subtype_val.continuousAt.preimage_mem_nhds this, fun _ n y hy ↦ hy n⟩
    · exact ⟨univ, univ_mem, fun h ↦ absurd h hη⟩
  choose N hNmem hNlt using hN
  let F : ℕ → C(Ω, ℝ) := fun n ↦
    ⟨fun x ↦ f n x, (continuousOn_iff_continuous_domRestrict.1 (hcont n))⟩
  let S : Set C(Ω, ℝ) := {g | (∀ x, |g x| ≤ B x) ∧ ∀ x η, 0 < η → ∀ y ∈ N x η, |g y - g x| ≤ η}
  have hFS : ∀ n, F n ∈ S := fun n ↦
    ⟨fun x ↦ hB x n, fun x η hη y hy ↦ (hNlt x η hη n y hy).le⟩
  have hS1 : IsCompact (ContinuousMap.toFun '' S) := by
    have hsub : ContinuousMap.toFun '' S ⊆ Set.pi univ (fun x ↦ Icc (-B x) (B x)) := by
      rintro _ ⟨g, hg, rfl⟩ x -
      exact abs_le.1 (hg.1 x)
    refine (isCompact_univ_pi fun x ↦ isCompact_Icc).of_isClosed_subset ?_ hsub
    have hcont_of : ∀ g : Ω → ℝ, (∀ x η, 0 < η → ∀ y ∈ N x η, |g y - g x| ≤ η) →
        Continuous g := by
      intro g hg
      refine continuous_iff_continuousAt.2 fun x ↦ Metric.tendsto_nhds.2 fun η hη ↦ ?_
      filter_upwards [hNmem x (η / 2)] with y hy
      rw [Real.dist_eq]
      exact (hg x (η / 2) (half_pos hη) y hy).trans_lt (half_lt_self hη)
    have : ContinuousMap.toFun '' S = {g : Ω → ℝ | (∀ x, |g x| ≤ B x) ∧
        ∀ x η, 0 < η → ∀ y ∈ N x η, |g y - g x| ≤ η} := by
      ext g
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hg
        exact ⟨⟨g, hcont_of g hg.2⟩, hg, rfl⟩
    rw [this, Set.ofPred_and]
    refine IsClosed.inter ?_ ?_
    · rw [Set.ofPred_forall]
      exact isClosed_iInter fun x ↦ isClosed_le (continuous_apply x).abs continuous_const
    · simp only [Set.ofPred_forall]
      refine isClosed_iInter fun x ↦ isClosed_iInter fun η ↦ isClosed_iInter fun _ ↦
        isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦ ?_
      exact isClosed_le ((continuous_apply y).sub (continuous_apply x)).abs continuous_const
  have hS2 : Equicontinuous ((↑) : S → Ω → ℝ) := by
    intro x U hU
    obtain ⟨η, hη, hηU⟩ := Metric.mem_uniformity_dist.1 hU
    filter_upwards [hNmem x (η / 2)] with y hy g
    apply hηU
    rw [Real.dist_eq, abs_sub_comm]
    exact (g.2.2 x (η / 2) (half_pos hη) y hy).trans_lt (half_lt_self hη)
  have hScpt : IsCompact S := ArzelaAscoli.isCompact_of_equicontinuous S hS1 hS2
  obtain ⟨g, -, φ, hφ, hlim⟩ := hScpt.tendsto_subseq hFS
  refine ⟨φ, hφ, fun x ↦ if hx : x ∈ Ω then g ⟨x, hx⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    refine g.continuous.congr fun x ↦ ?_
    simp [x.2]
  · rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have := (ContinuousMap.tendsto_iff_tendstoLocallyUniformly).1 hlim
    have e : (fun x ↦ if hx : x ∈ Ω then g ⟨x, hx⟩ else 0) ∘ ((↑) : Ω → X) = ⇑g := by
      funext x
      simp [x.2]
    rw [e]
    exact this

end ArzelaAscoli

section Semilinear

variable {d : ℕ}

/-- **Compactness of the semilinear approximations** (proof of Proposition 4.1(i)): a sequence
satisfying the interior Lipschitz estimate (3.9) with a common constant, bounded in `[0, M]` on
`U_∞`, with differentiable time slices and uniformly equicontinuous in time at each point of `U_∞`,
has a subsequence converging locally uniformly on `U_∞`; the limit is continuous, in `[0, M]`, and
locally Lipschitz in space. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_lip {U : Set (E d)} (hU : IsOpen U)
    {v : ℕ → E d × ℝ → ℝ} {C M : ℝ} (hlip : ∀ n, InteriorLipEst U (v n) C)
    (hvd : ∀ n, ∀ t > 0, DifferentiableOn ℝ (fun x ↦ v n (x, t)) U)
    (hvc : ∀ n, ContinuousOn (v n) (UInf U)) (hbd : ∀ n, ∀ q ∈ UInf U, 0 ≤ v n q ∧ v n q ≤ M)
    (htime : ∀ p ∈ UInf U, ∀ η > 0, ∃ δ > 0, ∀ n, ∀ s : ℝ, |s - p.2| < δ →
      |v n (p.1, s) - v n p| < η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : E d × ℝ → ℝ, ContinuousOn u (UInf U) ∧
      TendstoLocallyUniformlyOn (fun n ↦ v (φ n)) u atTop (UInf U) ∧
      (∀ q ∈ UInf U, 0 ≤ u q ∧ u q ≤ M) ∧ LocLipₓ (UInf U) u := by
  have hUo : IsOpen (UInf U) := hU.prod isOpen_Ioi
  have habs : ∀ n, ∀ q ∈ UInf U, |v n q| ≤ M := fun n q hq ↦
    abs_le.2 ⟨by linarith [(hbd n q hq).1, (hbd n q hq).2], (hbd n q hq).2⟩
  choose! r hr L hbox hlipbox using fun p (hp : p ∈ UInf U) ↦
    exists_box_lipschitz_of_interiorLipEst hU C M hp
  have hlip : ∀ n, ∀ p ∈ UInf U, ∀ x ∈ ball p.1 (r p), ∀ y ∈ ball p.1 (r p),
      ∀ t ∈ Ioo (p.2 - r p) (p.2 + r p), |v n (x, t) - v n (y, t)| ≤ L p * ‖x - y‖ :=
    fun n p hp ↦ hlipbox p hp (v n) (hlip n) (hvd n) (habs n)
  have heq : ∀ p ∈ UInf U, ∀ η > 0, ∀ᶠ q in 𝓝 p, ∀ n, |v n q - v n p| < η := by
    intro p hp η hη
    obtain ⟨δ, hδ, hδv⟩ := htime p hp (η / 2) (half_pos hη)
    set r' : ℝ := min (r p) (η / (2 * (|L p| + 1))) with hr'
    have hr'0 : 0 < r' := lt_min (hr p hp) (by positivity)
    set τ : ℝ := min (r p) δ with hτ
    have hτ0 : 0 < τ := lt_min (hr p hp) hδ
    have hN : ball p.1 r' ×ˢ Ioo (p.2 - τ) (p.2 + τ) ∈ 𝓝 p :=
      prod_mem_nhds (ball_mem_nhds _ hr'0) (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hN] with q hq n
    obtain ⟨hq1, hq2⟩ := hq
    simp only [mem_Ioo] at hq2
    have hq1' : q.1 ∈ ball p.1 (r p) := Metric.ball_subset_ball (min_le_left _ _) hq1
    have hq2' : q.2 ∈ Ioo (p.2 - r p) (p.2 + r p) :=
      ⟨by linarith [min_le_left (r p) δ], by linarith [min_le_left (r p) δ]⟩
    have h1 := hlip n p hp q.1 hq1' p.1 (mem_ball_self (hr p hp)) q.2 hq2'
    have h2 := hδv n q.2 (abs_lt.2 ⟨by linarith [min_le_right (r p) δ],
      by linarith [min_le_right (r p) δ]⟩)
    have hdist : ‖q.1 - p.1‖ < r' := by rw [← dist_eq_norm]; exact hq1
    have h3 : L p * ‖q.1 - p.1‖ < η / 2 := by
      have hLabs : L p * ‖q.1 - p.1‖ ≤ |L p| * r' :=
        (le_abs_self _).trans (by rw [abs_mul, abs_norm]; gcongr)
      have hr'le : r' ≤ η / (2 * (|L p| + 1)) := min_le_right _ _
      have : |L p| * r' ≤ |L p| * (η / (2 * (|L p| + 1))) := by gcongr
      have h4 : |L p| * (η / (2 * (|L p| + 1))) < η / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
        linarith [abs_nonneg (L p)]
      by_cases hq : ‖q.1 - p.1‖ = 0
      · rw [hq, mul_zero]; exact half_pos hη
      · have hpos : 0 < ‖q.1 - p.1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq)
        have : |L p| * ‖q.1 - p.1‖ < |L p| * r' ∨ L p = 0 := by
          rcases eq_or_ne (L p) 0 with h0 | h0
          · exact Or.inr h0
          · exact Or.inl (mul_lt_mul_of_pos_left hdist (abs_pos.2 h0))
        rcases this with h5 | h5
        · exact (le_abs_self _).trans_lt (by rw [abs_mul, abs_norm]; linarith)
        · rw [h5, zero_mul]; exact half_pos hη
    calc |v n q - v n p| = |(v n (q.1, q.2) - v n (p.1, q.2)) + (v n (p.1, q.2) - v n p)| := by
          ring_nf
      _ ≤ |v n (q.1, q.2) - v n (p.1, q.2)| + |v n (p.1, q.2) - v n p| := abs_add_le _ _
      _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt (h1.trans h3.le) h2
      _ = η := add_halves η
  obtain ⟨φ, hφ, u, hucont, hconv⟩ := exists_tendstoLocallyUniformlyOn_subseq hUo v hvc
    (fun q hq ↦ ⟨M, fun n ↦ habs n q hq⟩) heq
  refine ⟨φ, hφ, u, hucont, hconv, fun q hq ↦ ?_, fun p hp ↦ ?_⟩
  · have hmem : u q ∈ Icc 0 M := isClosed_Icc.mem_of_tendsto (hconv.tendsto_at hq)
      (Eventually.of_forall fun n ↦ hbd (φ n) q hq)
    exact hmem
  · refine ⟨L p, ball p.1 (r p) ×ˢ Ioo (p.2 - r p) (p.2 + r p),
      prod_mem_nhds (ball_mem_nhds _ (hr p hp))
        (Ioo_mem_nhds (by linarith [hr p hp]) (by linarith [hr p hp])),
      fun q hq q' hq' hqq ↦ ?_⟩
    have hqU := hbox p hp hq
    have hq'U := hbox p hp hq'
    have hlim := ((hconv.tendsto_at hqU).sub (hconv.tendsto_at hq'U)).abs
    refine le_of_tendsto' hlim fun n ↦ ?_
    have := hlip (φ n) p hp q.1 hq.1 q'.1 hq'.1 q.2 hq.2
    have e : q' = (q'.1, q.2) := Prod.ext rfl hqq.symm
    rw [e]
    exact this

/-! ### Interior time-equicontinuity -/

/-- **Interior time-equicontinuity for arbitrary solutions.** There is `ε₁ > 0` (depending only on
the setting and `β`) such that for every bound `M`, finite energy bound `E0`, point `p ∈ U_∞` and
`η > 0` there is `δ > 0` with `|u(p.1, s) - u(p)| < η` for `|s - p.2| < δ`, for every solution `u`
of (3.4) with `0 < ε < ε₁`, data `0 ≤ gε ≤ M`, `gε ∈ H¹(U)` and `∫_U |∇gε|² + Q_max² |U| ≤ E0`.

The paper's proof of Proposition 4.1 invokes Proposition 3.8(v) (a modulus of continuity up to
the parabolic boundary), which the paper proves only for the well-prepared data and does *not*
include in the list of estimates valid for arbitrary solutions (the remark before (4.1)). Here we
use instead this interior version, which follows from the interior Lipschitz bound (3.9), the
bound (4.1) and the dissipation estimate (3.8): averaging
over a small ball `B_ρ(x₀)`,
`|B_ρ| |u(x₀, s) - u(x₀, t₀)| ≤ 2 L ρ |B_ρ| + ∫_{B_ρ} ∫_{t₀}^{s} |∂ₜu|` and
`|∂ₜu| ≤ (∂ₜu)² / (2λ) + λ / 2`. -/
theorem semilinear_time_equicontinuous (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (M : ℝ) (E0 : ℝ≥0∞), E0 ≠ ⊤ → ∀ p ∈ UInf S.U, ∀ η > 0, ∃ δ > 0,
      ∀ ε ∈ Ioo 0 ε₁, ∀ (gε : E d → ℝ) (Gε : E d → E d) (u : E d × ℝ → ℝ),
        MemH1 S.U gε Gε → energyBound S Gε ≤ E0 → IsSemilinearSolution S.U S.Q β ε gε u →
        (∀ x ∈ S.U, 0 ≤ gε x ∧ gε x ≤ M) → ∀ s : ℝ, |s - p.2| < δ → |u (p.1, s) - u p| < η := by
  obtain ⟨C, ε₁, hε₁, hLip⟩ := semilinear_interiorLipEst S hβ
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, fun M E0 hE0 p hp η hη ↦ ?_⟩
  obtain ⟨r, hr, L, hbox, hlip⟩ := exists_box_lipschitz_of_interiorLipEst S.isOpen C (max M 1) hp
  set L' := max L 0 with hL'def
  have hL'0 : 0 ≤ L' := le_max_right _ _
  set ρ := min r (η / (6 * (L' + 1))) with hρdef
  have hρ : 0 < ρ := lt_min hr (by positivity)
  set B := ball p.1 ρ with hBdef
  have hBr : B ⊆ ball p.1 r := ball_subset_ball (min_le_left _ _)
  have hBm : MeasurableSet B := measurableSet_ball
  have hvolB : volume B ≠ ⊤ := measure_ball_lt_top.ne
  set vρ := (volume B).toReal with hvρdef
  have hvρ : 0 < vρ := ENNReal.toReal_pos (measure_ball_pos _ _ hρ).ne' hvolB
  set Eb := E0.toReal / 2 with hEdef
  have hE : 0 ≤ Eb := by positivity
  set lam := 3 * Eb / (2 * η * vρ) + 1 with hlamdef
  have hlam : 0 < lam := by positivity
  set δ := min r (2 * η / (3 * lam)) with hδdef
  refine ⟨δ, lt_min hr (by positivity), fun ε hε gε Gε u hH1 hEn hu hg s hs ↦ ?_⟩
  have hεpos : 0 < ε := hε.1
  have hsol := hu.2.1
  have hboxm : ∀ x ∈ ball p.1 r, ∀ t ∈ Ioo (p.2 - r) (p.2 + r), (x, t) ∈ UInf S.U :=
    fun x hx t ht ↦ hbox (mk_mem_prod hx ht)
  have hbd : ∀ q ∈ UInf S.U, |u q| ≤ max M 1 := fun q hq ↦ by
    have h := semilinear_nonneg_le_max S hβ hεpos hu hg q
      ⟨subset_closure hq.1, mem_Ici.2 (le_of_lt hq.2)⟩
    rw [abs_of_nonneg h.1]
    exact h.2.trans (max_le_max le_rfl (hε.2.trans_le (min_le_right _ _)).le)
  have hL := hlip u (hLip ε ⟨hεpos, hε.2.trans_le (min_le_left _ _)⟩ M gε u hu hg)
    (fun t ht ↦ (hsol.2.1 t ht).differentiableOn (by norm_num)) hbd
  have hs' : |s - p.2| < r := hs.trans_le (min_le_left _ _)
  have hsr : s ∈ Ioo (p.2 - r) (p.2 + r) := by
    rw [abs_lt] at hs'
    constructor <;> linarith
  have ht₀r : p.2 ∈ Ioo (p.2 - r) (p.2 + r) := ⟨by linarith, by linarith⟩
  have hspos : 0 < s := (hboxm p.1 (mem_ball_self hr) s hsr).2
  have ht₀pos : (0 : ℝ) < p.2 := hp.2
  -- the pointwise decomposition
  set a := u (p.1, s) - u p with hadef
  have hLρ : ∀ x ∈ B, ∀ t ∈ Ioo (p.2 - r) (p.2 + r), |u (p.1, t) - u (x, t)| ≤ L' * ρ := by
    intro x hx t ht
    have hx' : ‖p.1 - x‖ < ρ := by
      rw [← dist_eq_norm, dist_comm]
      exact hx
    refine (hL p.1 (mem_ball_self hr) x (hBr hx) t ht).trans ?_
    calc L * ‖p.1 - x‖ ≤ L' * ‖p.1 - x‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ L' * ρ := mul_le_mul_of_nonneg_left hx'.le hL'0
  have hpt : ∀ x ∈ B, ENNReal.ofReal |a| ≤
      ENNReal.ofReal (L' * ρ + L' * ρ) + ‖u (x, s) - u (x, p.2)‖ₑ := by
    intro x hx
    have h1 := hLρ x hx s hsr
    have h3 := hLρ x hx p.2 ht₀r
    have : |a| ≤ L' * ρ + L' * ρ + |u (x, s) - u (x, p.2)| := by
      have he : a = (u (p.1, s) - u (x, s)) - (u (p.1, p.2) - u (x, p.2)) +
          (u (x, s) - u (x, p.2)) := by rw [hadef]; ring
      rw [he]
      refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 h3)) le_rfl)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal this
  -- the fundamental theorem of calculus in time
  set I := Ι p.2 s with hIdef
  have hIIcc : ∀ τ ∈ uIcc p.2 s, 0 < τ := fun τ hτ ↦
    (lt_min ht₀pos hspos).trans_le hτ.1
  have hI : I ⊆ Ioc 0 (p.2 + r) := fun τ hτ ↦
    ⟨hIIcc τ (uIoc_subset_uIcc hτ), hτ.2.trans (max_le (by linarith) hsr.2.le)⟩
  have hIm : MeasurableSet I := measurableSet_uIoc
  have hftc : ∀ x ∈ B, ‖u (x, s) - u (x, p.2)‖ₑ ≤ ∫⁻ τ in I,
      (ENNReal.ofReal (1 / (2 * lam)) * ENNReal.ofReal (dₜ u (x, τ) ^ 2) +
        ENNReal.ofReal (lam / 2)) := by
    intro x hx
    have hxU : x ∈ S.U := (hboxm x (hBr hx) p.2 ht₀r).1
    have hderiv : ∀ τ ∈ uIcc p.2 s, HasDerivAt (fun τ ↦ u (x, τ)) (dₜ u (x, τ)) τ :=
      fun τ hτ ↦ (hsol.2.2.2.2.1 (x, τ) ⟨hxU, hIIcc τ hτ⟩).hasDerivAt
    have hcont : ContinuousOn (fun τ ↦ dₜ u (x, τ)) (uIcc p.2 s) :=
      hsol.2.2.2.2.2.1.comp (continuous_const.prodMk continuous_id).continuousOn
        fun τ hτ ↦ ⟨hxU, hIIcc τ hτ⟩
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [← h, ← ofReal_norm, intervalIntegral.norm_integral_eq_norm_integral_uIoc, ofReal_norm]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun τ ↦ ?_)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq := sq_nonneg (|dₜ u (x, τ)| - lam)
    rw [sub_sq, sq_abs] at hsq
    rw [div_mul_eq_mul_div, one_mul, div_add_div _ _ (by positivity) (by norm_num),
      le_div_iff₀ (by positivity)]
    linarith
  -- the dissipation bound
  have hdis := semilinear_dissipation S hβ hεpos hH1 hu (p.2 + r) (by linarith)
  have hBI : B ×ˢ I ⊆ S.U ×ˢ Ioc 0 (p.2 + r) :=
    prod_mono (fun x hx ↦ (hboxm x (hBr hx) p.2 ht₀r).1) hI
  have hD : ∫⁻ q in B ×ˢ I, ENNReal.ofReal (dₜ u q ^ 2) ≤ ENNReal.ofReal Eb := by
    refine (lintegral_mono_set hBI).trans (le_add_self.trans (hdis.trans ?_))
    rw [hEdef, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hE0, ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_div_right hEn 2
  have hmeasF : AEMeasurable (fun q : E d × ℝ ↦ ENNReal.ofReal (1 / (2 * lam)) *
      ENNReal.ofReal (dₜ u q ^ 2) + ENNReal.ofReal (lam / 2)) (volume.restrict (B ×ˢ I)) := by
    have hsub : B ×ˢ I ⊆ UInf S.U := hBI.trans (prod_mono le_rfl Ioc_subset_Ioi_self)
    have hg : AEMeasurable (fun q ↦ ENNReal.ofReal (dₜ u q ^ 2)) (volume.restrict (B ×ˢ I)) :=
      (ENNReal.continuous_ofReal.comp_continuousOn
        ((hsol.2.2.2.2.2.1.mono hsub).pow 2)).aemeasurable (hBm.prod hIm)
    exact (hg.const_mul _).add_const _
  have hvolBI : volume (B ×ˢ I) = volume B * ENNReal.ofReal |s - p.2| := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_uIoc]
  have key : ENNReal.ofReal |a| * volume B ≤ ENNReal.ofReal (L' * ρ + L' * ρ) * volume B +
      (ENNReal.ofReal (1 / (2 * lam)) * ENNReal.ofReal Eb +
        ENNReal.ofReal (lam / 2) * (volume B * ENNReal.ofReal |s - p.2|)) := by
    calc ENNReal.ofReal |a| * volume B = ∫⁻ _ in B, ENNReal.ofReal |a| :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in B, (ENNReal.ofReal (L' * ρ + L' * ρ) + ‖u (x, s) - u (x, p.2)‖ₑ) :=
          setLIntegral_mono' hBm hpt
      _ = ENNReal.ofReal (L' * ρ + L' * ρ) * volume B + ∫⁻ x in B, ‖u (x, s) - u (x, p.2)‖ₑ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const]
      _ ≤ ENNReal.ofReal (L' * ρ + L' * ρ) * volume B + ∫⁻ x in B, ∫⁻ τ in I,
            (ENNReal.ofReal (1 / (2 * lam)) * ENNReal.ofReal (dₜ u (x, τ) ^ 2) +
              ENNReal.ofReal (lam / 2)) := by
          exact add_le_add_right (setLIntegral_mono' hBm hftc) _
      _ = ENNReal.ofReal (L' * ρ + L' * ρ) * volume B + ∫⁻ q in B ×ˢ I,
            (ENNReal.ofReal (1 / (2 * lam)) * ENNReal.ofReal (dₜ u q ^ 2) +
              ENNReal.ofReal (lam / 2)) := by
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ ?_]
          rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
          exact hmeasF
      _ ≤ _ := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const, hvolBI]
          gcongr
  -- back to real numbers
  have hvB : volume B = ENNReal.ofReal vρ := (ENNReal.ofReal_toReal hvolB).symm
  have hP1 : 0 ≤ L' * ρ + L' * ρ := add_nonneg (mul_nonneg hL'0 hρ.le) (mul_nonneg hL'0 hρ.le)
  have hP2 : 0 ≤ 1 / (2 * lam) := div_nonneg zero_le_one (mul_pos two_pos hlam).le
  have hP3 : 0 ≤ lam / 2 := div_nonneg hlam.le zero_le_two
  have hP4 : 0 ≤ 1 / (2 * lam) * Eb := mul_nonneg hP2 hE
  have hP5 : 0 ≤ lam / 2 * (vρ * |s - p.2|) := mul_nonneg hP3 (mul_nonneg hvρ.le (abs_nonneg _))
  have hP6 : 0 ≤ (L' * ρ + L' * ρ) * vρ := mul_nonneg hP1 hvρ.le
  rw [hvB, ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hP1,
    ← ENNReal.ofReal_mul hP2, ← ENNReal.ofReal_mul hvρ.le,
    ← ENNReal.ofReal_mul hP3, ← ENNReal.ofReal_add hP4 hP5,
    ← ENNReal.ofReal_add hP6 (add_nonneg hP4 hP5),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg hP6 (add_nonneg hP4 hP5))] at key
  -- arithmetic
  have h1 : 2 * (L' * ρ) ≤ η / 3 := by
    have : ρ ≤ η / (6 * (L' + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have h2 : 1 / (2 * lam) * Eb ≤ η * vρ / 3 := by
    have hl : 3 * Eb / (2 * η * vρ) ≤ lam := by rw [hlamdef]; linarith
    rw [div_le_iff₀ (by positivity)] at hl
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have h3 : lam / 2 * |s - p.2| < η / 3 := by
    have : |s - p.2| < 2 * η / (3 * lam) := hs.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hfin : |a| * vρ < η * vρ := by
    have h3' : lam / 2 * (vρ * |s - p.2|) < η / 3 * vρ := by
      rw [← mul_assoc, mul_comm (lam / 2) vρ, mul_assoc]
      rw [mul_comm (η / 3) vρ]
      exact mul_lt_mul_of_pos_left h3 hvρ
    have h1' : (L' * ρ + L' * ρ) * vρ ≤ η / 3 * vρ :=
      mul_le_mul_of_nonneg_right (by linarith) hvρ.le
    have : η / 3 * vρ + η * vρ / 3 + η / 3 * vρ = η * vρ := by ring
    linarith
  exact lt_of_mul_lt_mul_right hfin hvρ.le

end Semilinear

end Inner

end PerronVariational

end
