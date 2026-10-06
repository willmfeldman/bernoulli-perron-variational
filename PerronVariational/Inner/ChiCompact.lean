/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.MeasureTheory.Group.Integral
import PerronVariational.Inner.EnergyConv
import PerronVariational.Inner.ReactionBound
import PerronVariational.Inner.SemilinearEstimates
import PerronVariational.Registry.FunctionalAnalysis
import PerronVariational.Semilinear.Profiles

/-!
# `L¹_loc` compactness of `χ_ε` (Lemma 4.3)

The compactness part of **Lemma 4.3** of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

* `Inner.exists_tendstoLpLoc_subseq_of_translation`: a sequence of functions bounded by `1` on an
  open `Ω ⊆ ℝᵈ × ℝ`, continuous on `Ω`, and uniformly `L¹`-continuous under translations on every
  compact subset of `Ω`, has a subsequence converging in `L¹_loc(Ω)` (the Fréchet–Kolmogorov
  theorem from gmt-foundations v0.1.0, applied to cut-offs, plus a diagonal argument over a compact
  exhaustion).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-! ### Fréchet–Kolmogorov on `L¹_loc` -/

/-- A compact exhaustion of an open set `Ω ≠ univ`: every compact subset of `Ω` lies in some
`K m`. -/
theorem exists_compact_exhaustion {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) (hΩc : Ωᶜ.Nonempty) :
    ∃ K : ℕ → Set (E d × ℝ), (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ Ω) ∧ Monotone K ∧
      ∀ A ⊆ Ω, IsCompact A → ∃ m, A ⊆ K m := by
  refine ⟨fun m ↦ closedBall 0 m ∩ {p | ((m : ℝ) + 1)⁻¹ ≤ infDist p Ωᶜ}, fun m ↦ ?_,
    fun m ↦ ?_, fun m m' hmm' ↦ ?_, fun A hA hAc ↦ ?_⟩
  · exact (isCompact_closedBall 0 m).inter_right
      (isClosed_le continuous_const (continuous_infDist_pt _))
  · rintro p ⟨-, hp⟩
    by_contra h
    have : infDist p Ωᶜ = 0 := infDist_zero_of_mem h
    simp only [Set.mem_ofPred_eq, this] at hp
    exact absurd hp (not_le.2 (by positivity))
  · rintro p ⟨h1, h2⟩
    have hm : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    refine ⟨closedBall_subset_closedBall hm h1, ?_⟩
    change ((m' : ℝ) + 1)⁻¹ ≤ infDist p Ωᶜ
    exact le_trans (inv_anti₀ (by positivity) (by linarith)) h2
  · rcases A.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, empty_subset _⟩
    obtain ⟨R, hR⟩ := hAc.isBounded.subset_closedBall 0
    have hpos : ∀ p ∈ A, 0 < infDist p Ωᶜ := fun p hp ↦
      (hΩ.isClosed_compl.notMem_iff_infDist_pos hΩc).1 fun h ↦ h (hA hp)
    obtain ⟨q, hqA, hq⟩ := hAc.exists_isMinOn hne (continuous_infDist_pt _).continuousOn
    obtain ⟨m, hm⟩ := exists_nat_gt (max R (infDist q Ωᶜ)⁻¹)
    refine ⟨m, fun p hp ↦ ⟨closedBall_subset_closedBall ?_ (hR hp), ?_⟩⟩
    · linarith [le_max_left R (infDist q Ωᶜ)⁻¹]
    · change ((m : ℝ) + 1)⁻¹ ≤ infDist p Ωᶜ
      have h1 : infDist q Ωᶜ ≤ infDist p Ωᶜ := hq hp
      have h2 : ((m : ℝ) + 1)⁻¹ ≤ infDist q Ωᶜ := by
        rw [inv_le_comm₀ (by positivity) (hpos q hqA)]
        linarith [le_max_right R (infDist q Ωᶜ)⁻¹]
      linarith

/-- **Fréchet–Kolmogorov for a cut-off**: under uniform `L¹`-continuity under
translations on compact subsets of `Ω`, the cut-off sequence `f_n ζ` has an `L¹`-convergent
subsequence. -/
theorem exists_subseq_tendsto_L1_cutoff {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    {f : ℕ → E d × ℝ → ℝ} (hfc : ∀ n, ContinuousOn (f n) Ω) (hfb : ∀ n, ∀ p ∈ Ω, |f n p| ≤ 1)
    (htrans : ∀ A ⊆ Ω, IsCompact A → ∀ η > 0, ∃ ρ > 0, ∀ n, ∀ w : E d × ℝ, ‖w‖ < ρ →
      ∫⁻ p in A, ‖f n (p + w) - f n p‖ₑ ≤ ENNReal.ofReal η)
    {ζ : E d × ℝ → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hζs : tsupport ζ ⊆ Ω)
    (hζ01 : ∀ p, 0 ≤ ζ p ∧ ζ p ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : E d × ℝ → ℝ, Integrable F ∧
      Tendsto (fun n ↦ eLpNorm ((fun p ↦ f (φ n) p * ζ p) - F) 1 volume) atTop (𝓝 0) := by
  set L := tsupport ζ with hLdef
  have hL : IsCompact L := hζc
  have hLm : MeasurableSet L := (isClosed_tsupport ζ).measurableSet
  obtain ⟨r, hr, hrΩ⟩ := hL.exists_cthickening_subset_open hΩ hζs
  set A := cthickening r L with hAdef
  have hA : IsCompact A := hL.cthickening
  have hAm : MeasurableSet A := hA.isClosed.measurableSet
  have hAfin : volume A ≠ ⊤ := hA.measure_lt_top.ne
  obtain ⟨Lζ, hLζ⟩ := hζ.lipschitzWith_of_hasCompactSupport hζc one_ne_zero
  have hζ0 : ∀ p ∉ L, ζ p = 0 := fun p hp ↦ image_eq_zero_of_notMem_tsupport hp
  set F : ℕ → E d × ℝ → ℝ := fun n p ↦ f n p * ζ p with hFdef
  have hFc : ∀ n, Continuous (F n) := fun n ↦
    continuous_mul_of_tsupport_subset hΩ (hfc n) hζ.continuous hζs
  have hFsupp : ∀ n, ∀ p ∉ L, F n p = 0 := fun n p hp ↦ by simp [F, hζ0 p hp]
  have hFcs : ∀ n, HasCompactSupport (F n) := fun n ↦ hζc.mul_left
  have hFi : ∀ n, Integrable (F n) := fun n ↦ (hFc n).integrable_of_hasCompactSupport (hFcs n)
  have hFb : ∀ n, ∀ p, |F n p| ≤ 1 := fun n p ↦ by
    by_cases hp : p ∈ L
    · rw [abs_mul, abs_of_nonneg (hζ01 p).1]
      calc |f n p| * ζ p ≤ 1 * 1 := mul_le_mul (hfb n p (hζs hp)) (hζ01 p).2 (hζ01 p).1
            zero_le_one
        _ = 1 := one_mul 1
    · simp [hFsupp n p hp]
  have hC : ∀ n, ∫ x, |F n x| ≤ (volume L).toReal := fun n ↦ by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ by simp [hFsupp n p hp]]
    calc ∫ x in L, |F n x| ≤ ∫ _ in L, (1 : ℝ) :=
          setIntegral_mono_on (hFi n).abs.integrableOn
            (integrableOn_const hL.measure_lt_top.ne) hLm fun p _ ↦ hFb n p
      _ = (volume L).toReal := by simp [Measure.real]
  have htransFK : ∀ δ > 0, ∃ ρ > 0, ∀ n, ∀ h : E d × ℝ, ‖h‖ < ρ →
      ∫ x, |F n (x + h) - F n x| < δ := by
    intro δ hδ
    obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := htrans A hrΩ hA (δ / 2) (half_pos hδ)
    set c : ℝ := (Lζ : ℝ) * (volume A).toReal + 1 with hcdef
    have hc : 0 < c := by positivity
    refine ⟨min (min ρ₁ r) (δ / (4 * c)), by positivity, fun n h hh ↦ ?_⟩
    have hh1 : ‖h‖ < ρ₁ := hh.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hh2 : ‖h‖ < r := hh.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hh3 : ‖h‖ < δ / (4 * c) := hh.trans_le (min_le_right _ _)
    -- pointwise bound
    have hpt : ∀ x, ENNReal.ofReal |F n (x + h) - F n x| ≤
        A.indicator (fun x ↦ ‖f n (x + h) - f n x‖ₑ + ENNReal.ofReal (Lζ * ‖h‖)) x := by
      intro x
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx]
        have hxΩ : x ∈ Ω := hrΩ hx
        have h1 : |F n (x + h) - F n x| ≤ |f n (x + h) - f n x| + Lζ * ‖h‖ := by
          have hζl : |ζ (x + h) - ζ x| ≤ Lζ * ‖h‖ := by
            have := hLζ.dist_le_mul (x + h) x
            rwa [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at this
          calc |F n (x + h) - F n x|
              = |(f n (x + h) - f n x) * ζ (x + h) + f n x * (ζ (x + h) - ζ x)| := by
                simp only [F]
                ring_nf
            _ ≤ |f n (x + h) - f n x| * 1 + 1 * (Lζ * ‖h‖) := by
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_mul]
                gcongr
                · rw [abs_of_nonneg (hζ01 _).1]
                  exact (hζ01 _).2
                · exact hfb n x hxΩ
            _ = |f n (x + h) - f n x| + Lζ * ‖h‖ := by ring
        calc ENNReal.ofReal |F n (x + h) - F n x|
            ≤ ENNReal.ofReal (|f n (x + h) - f n x| + Lζ * ‖h‖) := ENNReal.ofReal_le_ofReal h1
          _ = ‖f n (x + h) - f n x‖ₑ + ENNReal.ofReal (Lζ * ‖h‖) := by
              rw [ENNReal.ofReal_add (abs_nonneg _) (by positivity), ← Real.norm_eq_abs,
                ofReal_norm]
      · have hxL : x ∉ L := fun h' ↦ hx (self_subset_cthickening L h')
        have hxhL : x + h ∉ L := fun h' ↦ hx (mem_cthickening_of_dist_le x (x + h) r L h'
          (by rw [dist_eq_norm, sub_add_cancel_left, norm_neg]; exact hh2.le))
        simp [hFsupp n x hxL, hFsupp n _ hxhL]
    have hlin : ∫⁻ x, ENNReal.ofReal |F n (x + h) - F n x| ≤
        ENNReal.ofReal (δ / 2) + ENNReal.ofReal (Lζ * ‖h‖) * volume A := by
      refine (lintegral_mono hpt).trans ?_
      rw [lintegral_indicator hAm, lintegral_add_right _ measurable_const, setLIntegral_const]
      exact add_le_add (hρ₁' n h hh1) le_rfl
    have hint : Integrable (fun x ↦ |F n (x + h) - F n x|) :=
      (((hFi n).comp_add_right h).sub (hFi n)).abs
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ abs_nonneg _)
      hint.aestronglyMeasurable]
    have hfin : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (Lζ * ‖h‖) * volume A ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin⟩
    refine lt_of_le_of_lt (ENNReal.toReal_mono hfin hlin) ?_
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (half_pos hδ).le,
      ENNReal.toReal_ofReal (by positivity)]
    have : (Lζ : ℝ) * ‖h‖ * (volume A).toReal ≤ c * ‖h‖ := by
      rw [hcdef]
      linarith [norm_nonneg h, ENNReal.toReal_nonneg (a := volume A), Lζ.coe_nonneg]
    have h4 : c * ‖h‖ < δ / 4 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      rw [lt_div_iff₀ (by positivity)] at hh3
      linarith
    linarith
  obtain ⟨φ, hφ, F₀, hF₀, hconv⟩ := Registry.frechetKolmogorov_exists_subseq volume F hFi
    (volume L).toReal hC L hL hFsupp htransFK
  exact ⟨φ, hφ, F₀, hF₀, hconv⟩

/-- **`L¹_loc` compactness from uniform translation continuity** (Fréchet–Kolmogorov on cut-offs,
and a diagonal argument over a compact exhaustion of `Ω`). -/
theorem exists_tendstoLpLoc_subseq_of_translation {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    (hΩc : Ωᶜ.Nonempty) {f : ℕ → E d × ℝ → ℝ} (hfc : ∀ n, ContinuousOn (f n) Ω)
    (hfb : ∀ n, ∀ p ∈ Ω, |f n p| ≤ 1)
    (htrans : ∀ A ⊆ Ω, IsCompact A → ∀ η > 0, ∃ ρ > 0, ∀ n, ∀ w : E d × ℝ, ‖w‖ < ρ →
      ∫⁻ p in A, ‖f n (p + w) - f n p‖ₑ ≤ ENNReal.ofReal η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀ : E d × ℝ → ℝ, Measurable χ₀ ∧
      TendstoLpLoc 1 volume Ω (fun n ↦ f (φ n)) χ₀ atTop := by
  classical
  obtain ⟨K, hKc, hKΩ, hKmono, hKall⟩ := exists_compact_exhaustion hΩ hΩc
  have hKm : ∀ m, MeasurableSet (K m) := fun m ↦ (hKc m).isClosed.measurableSet
  choose ζ hζ hζc hζs hζ01 hζ1 using fun m ↦ exists_cutoff (hKc m) hΩ (hKΩ m)
  have key : ∀ (m : ℕ) (σ : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ F : E d × ℝ → ℝ,
      Integrable F ∧ Tendsto (fun n ↦ eLpNorm ((fun p ↦ f (σ (ψ n)) p * ζ m p) - F) 1 volume)
        atTop (𝓝 0) := fun m σ ↦
    exists_subseq_tendsto_L1_cutoff hΩ (f := fun n ↦ f (σ n)) (fun n ↦ hfc _) (fun n ↦ hfb _)
      (fun A hA hAc η hη ↦ by
        obtain ⟨ρ, hρ, h⟩ := htrans A hA hAc η hη
        exact ⟨ρ, hρ, fun n ↦ h (σ n)⟩) (hζ m) (hζc m) (hζs m) (hζ01 m)
  choose ψ hψ F hFi hFt using key
  -- nested subsequences `Φ (m + 1) = Φ m ∘ ψ`
  let Φ : ℕ → ℕ → ℕ := fun m ↦
    Nat.rec (motive := fun _ ↦ ℕ → ℕ) (ψ 0 id) (fun m Φm ↦ Φm ∘ ψ (m + 1) Φm) m
  let prev : ℕ → ℕ → ℕ := fun m ↦ Nat.casesOn (motive := fun _ ↦ ℕ → ℕ) m id fun m ↦ Φ m
  have hΦeq : ∀ m, Φ m = prev m ∘ ψ m (prev m) := by
    intro m
    cases m with
    | zero => rfl
    | succ m => rfl
  have hΦmono : ∀ m, StrictMono (Φ m) := by
    intro m
    induction m with
    | zero => exact hψ 0 id
    | succ m ih => exact ih.comp (hψ (m + 1) (Φ m))
  set G : ℕ → E d × ℝ → ℝ := fun m ↦ F m (prev m) with hGdef
  have hGconv : ∀ m, Tendsto (fun n ↦ eLpNorm ((fun p ↦ f (Φ m n) p * ζ m p) - G m) 1 volume)
      atTop (𝓝 0) := by
    intro m
    have h := hFt m (prev m)
    rw [hΦeq m]
    exact h
  -- the diagonal subsequence
  set D : ℕ → ℕ := fun k ↦ Φ k k with hDdef
  have hD : StrictMono D := by
    refine strictMono_nat_of_lt_succ fun k ↦ ?_
    change Φ k k < Φ (k + 1) (k + 1)
    have : Φ (k + 1) (k + 1) = Φ k (ψ (k + 1) (Φ k) (k + 1)) := rfl
    rw [this]
    exact hΦmono k (lt_of_lt_of_le (Nat.lt_succ_self k) ((hψ _ _).id_le _))
  have hsub : ∀ m j, ∃ τ : ℕ → ℕ, StrictMono τ ∧ Φ (m + j) = Φ m ∘ τ := by
    intro m j
    induction j with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ j ih =>
      obtain ⟨τ, hτ, hτeq⟩ := ih
      refine ⟨τ ∘ ψ (m + j + 1) (Φ (m + j)), hτ.comp (hψ _ _), ?_⟩
      change Φ (m + j) ∘ ψ (m + j + 1) (Φ (m + j)) = _
      rw [hτeq]
      rfl
  have hDconv : ∀ m, Tendsto (fun k ↦ eLpNorm ((fun p ↦ f (D k) p * ζ m p) - G m) 1 volume)
      atTop (𝓝 0) := by
    intro m
    choose τ hτ hτeq using hsub m
    have hr : Tendsto (fun j ↦ τ j (m + j)) atTop atTop :=
      tendsto_atTop_mono (fun j ↦ (Nat.le_add_left j m).trans ((hτ j).id_le (m + j)))
        tendsto_id
    have h1 := (hGconv m).comp hr
    have h2 : Tendsto (fun j ↦ eLpNorm ((fun p ↦ f (D (j + m)) p * ζ m p) - G m) 1 volume)
        atTop (𝓝 0) := by
      refine h1.congr fun j ↦ ?_
      simp only [Function.comp_apply, D]
      rw [add_comm j m, hτeq j]
      rfl
    exact (tendsto_add_atTop_iff_nat m).1 h2
  -- measurability of the approximants
  have hfζm : ∀ m k, AEStronglyMeasurable (fun p ↦ f (D k) p * ζ m p) volume := fun m k ↦
    (continuous_mul_of_tsupport_subset hΩ (hfc _) (hζ m).continuous (hζs m)).aestronglyMeasurable
  have hGm : ∀ m, AEStronglyMeasurable (G m) volume := fun m ↦ (hFi m (prev m)).aestronglyMeasurable
  -- consistency of the limits
  have hcons : ∀ m M, m ≤ M → G m =ᵐ[volume.restrict (K m)] G M := by
    intro m M hmM
    have hle : ∀ k, eLpNorm (G m - G M) 1 (volume.restrict (K m)) ≤
        eLpNorm ((fun p ↦ f (D k) p * ζ m p) - G m) 1 volume +
          eLpNorm ((fun p ↦ f (D k) p * ζ M p) - G M) 1 volume := by
      intro k
      have heq : (G m - G M) =ᵐ[volume.restrict (K m)]
          ((fun p ↦ f (D k) p * ζ M p) - G M) - ((fun p ↦ f (D k) p * ζ m p) - G m) := by
        filter_upwards [ae_restrict_mem (hKm m)] with p hp
        simp only [Pi.sub_apply, hζ1 m p hp, hζ1 M p (hKmono hmM hp)]
        ring
      rw [eLpNorm_congr_ae heq]
      refine (eLpNorm_sub_le le_rfl).trans ?_
      rw [add_comm]
      exact add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
        (eLpNorm_mono_measure _ Measure.restrict_le_self)
    have hlim := (hDconv m).add (hDconv M)
    rw [add_zero] at hlim
    have h0 : eLpNorm (G m - G M) 1 (volume.restrict (K m)) = 0 :=
      le_antisymm (ge_of_tendsto' hlim hle) zero_le
    rw [eLpNorm_eq_zero_iff one_ne_zero] at h0
    exact (sub_ae_eq_zero _ _).1 h0
  -- measurable representatives and the limit `χ₀`
  set H : ℕ → E d × ℝ → ℝ := fun m ↦ (hGm m).mk (G m) with hHdef
  have hHmeas : ∀ m, Measurable (H m) := fun m ↦ (hGm m).stronglyMeasurable_mk.measurable
  have hHeq : ∀ m, G m =ᵐ[volume] H m := fun m ↦ (hGm m).ae_eq_mk
  have hex : ∀ p, ∃ m, p ∈ K m ∨ p ∉ Ω := fun p ↦ by
    by_cases hp : p ∈ Ω
    · obtain ⟨m, hm⟩ := hKall {p} (singleton_subset_iff.2 hp) isCompact_singleton
      exact ⟨m, Or.inl (hm rfl)⟩
    · exact ⟨0, Or.inr hp⟩
  set χ₀ : E d × ℝ → ℝ := fun p ↦ H (Nat.find (hex p)) p with hχ₀def
  have hχm : Measurable χ₀ := by
    convert Measurable.find hHmeas (p := fun m p ↦ p ∈ K m ∨ p ∉ Ω)
      (fun m ↦ (hKm m).union hΩ.measurableSet.compl) hex
  have hχK : ∀ M, χ₀ =ᵐ[volume.restrict (K M)] H M := by
    intro M
    have hall : ∀ᵐ p ∂(volume.restrict (K M)), ∀ m, m ≤ M → p ∈ K m → H m p = H M p := by
      rw [ae_all_iff]
      intro m
      by_cases hmM : m ≤ M
      · have h2 : ∀ᵐ p ∂volume, p ∈ K m → G m p = G M p :=
          (ae_restrict_iff' (hKm m)).1 (hcons m M hmM)
        filter_upwards [ae_restrict_of_ae h2, ae_restrict_of_ae (hHeq m),
          ae_restrict_of_ae (hHeq M)] with p hp h3p h4p _ hpK
        rw [← h3p, ← h4p]
        exact hp hpK
      · exact Eventually.of_forall fun p h ↦ absurd h hmM
    filter_upwards [hall, ae_restrict_mem (hKm M)] with p hp hpK
    have hfind : Nat.find (hex p) ≤ M := Nat.find_min' (hex p) (Or.inl hpK)
    have hpm : p ∈ K (Nat.find (hex p)) :=
      (Nat.find_spec (hex p)).resolve_right (not_not.2 (hKΩ M hpK))
    exact hp _ hfind hpm
  refine ⟨D, hD, χ₀, hχm, fun A hA hAc ↦ ?_⟩
  obtain ⟨M, hAM⟩ := hKall A hA hAc
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hDconv M)
    (fun _ ↦ zero_le) fun k ↦ ?_
  have heq : (f (D k) - χ₀) =ᵐ[volume.restrict A] ((fun p ↦ f (D k) p * ζ M p) - G M) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAM (hχK M),
      ae_restrict_of_ae (hHeq M), ae_restrict_mem hAm] with p h1 h2 hp
    simp only [Pi.sub_apply, hζ1 M p (hAM hp), mul_one, h1, h2]
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-! ### Translations in space and in time -/

/-- Uniform `L¹`-continuity under translations from separate uniform continuity under spatial
and temporal translations. -/
theorem translation_of_space_time {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {f : ℕ → E d × ℝ → ℝ}
    (hfc : ∀ n, ContinuousOn (f n) Ω)
    (hsp : ∀ A ⊆ Ω, IsCompact A → ∀ η > 0, ∃ ρ > 0, ∀ n, ∀ h : E d, ‖h‖ < ρ →
      ∫⁻ p in A, ‖f n (p + (h, 0)) - f n p‖ₑ ≤ ENNReal.ofReal η)
    (htm : ∀ A ⊆ Ω, IsCompact A → ∀ η > 0, ∃ ρ > 0, ∀ n, ∀ s : ℝ, |s| < ρ →
      ∫⁻ p in A, ‖f n (p + (0, s)) - f n p‖ₑ ≤ ENNReal.ofReal η) :
    ∀ A ⊆ Ω, IsCompact A → ∀ η > 0, ∃ ρ > 0, ∀ n, ∀ w : E d × ℝ, ‖w‖ < ρ →
      ∫⁻ p in A, ‖f n (p + w) - f n p‖ₑ ≤ ENNReal.ofReal η := by
  intro A hA hAc η hη
  obtain ⟨r, hr, hrΩ⟩ := hAc.exists_cthickening_subset_open hΩ hA
  set A' := cthickening r A with hA'def
  have hA' : IsCompact A' := hAc.cthickening
  obtain ⟨ρ₁, hρ₁, h₁⟩ := hsp A' hrΩ hA' (η / 2) (half_pos hη)
  obtain ⟨ρ₂, hρ₂, h₂⟩ := htm A hA hAc (η / 2) (half_pos hη)
  refine ⟨min r (min ρ₁ ρ₂), by positivity, fun n w hw ↦ ?_⟩
  have hw1 : ‖w.1‖ < ρ₁ := (norm_fst_le w).trans_lt
    (hw.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hw2 : |w.2| < ρ₂ := by
    have := (norm_snd_le w).trans_lt (hw.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    rwa [Real.norm_eq_abs] at this
  have hwr : |w.2| ≤ r := by
    have := (norm_snd_le w).trans (hw.trans_le (min_le_left _ _)).le
    rwa [Real.norm_eq_abs] at this
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  have hsplit : ∀ p : E d × ℝ, ‖f n (p + w) - f n p‖ₑ ≤
      ‖f n (p + (0, w.2) + (w.1, 0)) - f n (p + (0, w.2))‖ₑ +
        ‖f n (p + (0, w.2)) - f n p‖ₑ := by
    intro p
    have hpw : p + w = p + (0, w.2) + (w.1, 0) := by
      ext <;> simp [add_comm]
    rw [hpw]
    calc ‖f n (p + (0, w.2) + (w.1, 0)) - f n p‖ₑ
        = ‖(f n (p + (0, w.2) + (w.1, 0)) - f n (p + (0, w.2))) +
            (f n (p + (0, w.2)) - f n p)‖ₑ := by ring_nf
      _ ≤ _ := enorm_add_le _ _
  have hmemA' : ∀ p ∈ A, p + (0, w.2) ∈ A' := fun p hp ↦
    mem_cthickening_of_dist_le _ p r A hp (by
      rw [dist_eq_norm, add_sub_cancel_left, Prod.norm_def, norm_zero, Real.norm_eq_abs]
      exact max_le (abs_nonneg _ |>.trans hwr) hwr)
  have hshift : ∫⁻ p in A, ‖f n (p + (0, w.2) + (w.1, 0)) - f n (p + (0, w.2))‖ₑ ≤
      ∫⁻ q in A', ‖f n (q + (w.1, 0)) - f n q‖ₑ :=
    setLIntegral_comp_add_le hAm hA'.isClosed.measurableSet
      (fun q ↦ ‖f n (q + (w.1, 0)) - f n q‖ₑ) (0, w.2) hmemA'
  calc ∫⁻ p in A, ‖f n (p + w) - f n p‖ₑ
      ≤ ∫⁻ p in A, (‖f n (p + (0, w.2) + (w.1, 0)) - f n (p + (0, w.2))‖ₑ +
          ‖f n (p + (0, w.2)) - f n p‖ₑ) := lintegral_mono hsplit
    _ = (∫⁻ p in A, ‖f n (p + (0, w.2) + (w.1, 0)) - f n (p + (0, w.2))‖ₑ) +
          ∫⁻ p in A, ‖f n (p + (0, w.2)) - f n p‖ₑ := by
        refine lintegral_add_right' _ (ContinuousOn.aemeasurable ?_ hAm)
        exact (((hfc n).comp (continuous_add_const _).continuousOn fun p hp ↦
          hrΩ (hmemA' p hp)).sub ((hfc n).mono hA)).enorm
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add (hshift.trans (h₁ n w.1 hw1)) (h₂ n w.2 hw2)
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le, add_halves]

/-- **Fundamental theorem of calculus along a spatial segment** for `χ_ε = 2 𝓑_ε(v)`:
`|χ(p + (h, 0)) - χ(p)| ≤ ∫₀¹ 2 L |h| β_ε(v(p + r (h, 0))) dr` if `|∇v| ≤ L` on the segment. -/
theorem abs_chiEps_add_sub_le {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ} {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {ε : ℝ} (hε : 0 < ε) {v : E d × ℝ → ℝ}
    (hsol : IsSemilinearSolOn U Q β ε (Ioi 0) v) {p : E d × ℝ} {h : E d}
    (hseg : ∀ r ∈ Icc (0 : ℝ) 1, p + r • ((h, 0) : E d × ℝ) ∈ UInf U) {L : ℝ}
    (hL : ∀ r ∈ Icc (0 : ℝ) 1, ‖gradₓ v (p + r • ((h, 0) : E d × ℝ))‖ ≤ L) :
    |chiEps β ε v (p + (h, 0)) - chiEps β ε v p| ≤
      ∫ r in (0 : ℝ)..1, 2 * L * ‖h‖ * betaEps β ε (v (p + r • ((h, 0) : E d × ℝ))) := by
  set q : ℝ → E d × ℝ := fun r ↦ p + r • ((h, 0) : E d × ℝ) with hqdef
  have hq : ∀ r, q r = (p.1 + r • h, p.2) := fun r ↦ by
    ext <;> simp [q]
  have hqc : Continuous q := continuous_const.add (continuous_id.smul continuous_const)
  have hΩ : IsOpen (UInf U) := hU.prod isOpen_Ioi
  set γ' : ℝ → ℝ := fun r ↦ 2 * betaEps β ε (v (q r)) * ⟪gradₓ v (q r), h⟫ with hγ'def
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r ↦ chiEps β ε v (q r)) (γ' r) r := by
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    have hqU : (p.1 + r • h, p.2) ∈ UInf U := by
      rw [← hq r]
      exact hseg r hr
    have hsl : DifferentiableAt ℝ (fun y ↦ v (y, p.2)) (p.1 + r • h) :=
      ((hsol.2.1 p.2 hqU.2).differentiableOn (by norm_num)).differentiableAt
        (hU.mem_nhds hqU.1)
    have hline : HasDerivAt (fun r : ℝ ↦ p.1 + r • h) h r := by
      simpa using ((hasDerivAt_id r).smul_const h).const_add p.1
    have h1 := hsl.hasFDerivAt.comp_hasDerivAt r hline
    have h2 := ((hβ.hasDerivAt_bigBEps ε _).comp r h1).const_mul 2
    have hfun : (fun r ↦ chiEps β ε v (q r)) = fun r ↦ 2 * bigBEps β ε (v (p.1 + r • h, p.2)) := by
      funext r'
      simp only [chiEps, hq r']
    rw [hfun]
    convert h2 using 1
    · rfl
    simp only [γ', hq r, gradₓ, ← inner_gradient_eq_fderiv, Function.comp_def]
    ring
  have hγc : ContinuousOn γ' (uIcc 0 1) := by
    have hmaps : MapsTo q (uIcc 0 1) (UInf U) := fun r hr ↦ by
      rw [uIcc_of_le zero_le_one] at hr
      exact hseg r hr
    exact (continuousOn_const.mul ((hβ.continuous_betaEps ε).comp_continuousOn
      (hsol.1.comp hqc.continuousOn hmaps))).mul
      ((hsol.2.2.1.comp hqc.continuousOn hmaps).inner continuousOn_const)
  have hRc : ContinuousOn (fun r ↦ 2 * L * ‖h‖ * betaEps β ε (v (q r))) (uIcc 0 1) := by
    have hmaps : MapsTo q (uIcc 0 1) (UInf U) := fun r hr ↦ by
      rw [uIcc_of_le zero_le_one] at hr
      exact hseg r hr
    exact continuousOn_const.mul ((hβ.continuous_betaEps ε).comp_continuousOn
      (hsol.1.comp hqc.continuousOn hmaps))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hγc.intervalIntegrable
  have h01 : chiEps β ε v (p + (h, 0)) - chiEps β ε v p =
      chiEps β ε v (q 1) - chiEps β ε v (q 0) := by simp [q, Prod.mk_zero_zero]
  rw [h01, ← hftc]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
    (intervalIntegral.integral_mono_on zero_le_one hγc.intervalIntegrable.abs
      hRc.intervalIntegrable fun r hr ↦ ?_)
  have hb0 : 0 ≤ betaEps β ε (v (q r)) := hβ.betaEps_nonneg ε _ hε.le
  simp only [γ', abs_mul, abs_two, abs_of_nonneg hb0]
  have := (abs_real_inner_le_norm (gradₓ v (q r)) h).trans
    (mul_le_mul_of_nonneg_right (hL r hr) (norm_nonneg _))
  nlinarith

/-! ### Lemma 4.3: `L¹_loc` compactness of `χ_ε` -/

section ChiEps

variable {β : ℝ → ℝ}

/-- **Spatial translation estimate for `χ_ε`** (the BV bound (4.7), used as in (4.9)):
uniformly in `n` (large), `∫_A |χ_n(x + h, t) - χ_n(x, t)|` is small for small `h`. -/
theorem chiEps_space_translation (S : Setting d) (hβ : IsReactionProfile β)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) {g : ℕ → E d → ℝ}
    {G : ℕ → E d → E d} {v : ℕ → E d × ℝ → ℝ} {M : ℝ} {E0 : ℝ≥0∞}
    (hE0 : E0 ≠ ⊤) (hv : ∀ n, IsSemilinearSolution S.U S.Q β (ε n) (g n) (v n))
    (hg : ∀ n, MemH1 S.U (g n) (G n)) (hgE : ∀ n, energyBound S (G n) ≤ E0)
    (hgM : ∀ n, ∀ x ∈ S.U, 0 ≤ g n x ∧ g n x ≤ M) :
    ∃ N : ℕ, ∀ A ⊆ UInf S.U, IsCompact A → ∀ η > 0, ∃ ρ > 0, ∀ n ≥ N, ∀ h : E d, ‖h‖ < ρ →
      ∫⁻ p in A, ‖chiEps β (ε n) (v n) (p + (h, 0)) - chiEps β (ε n) (v n) p‖ₑ ≤
        ENNReal.ofReal η := by
  have hΩ : IsOpen (UInf S.U) := S.isOpen.prod isOpen_Ioi
  obtain ⟨C, ε₁, hε₁, hLip⟩ := semilinear_interiorLipEst S hβ
  obtain ⟨ε₂, hε₂, hBeta⟩ := semilinear_betaEps_lintegral_le S hβ
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hε0.eventually (gt_mem_nhds (lt_min (lt_min hε₁ hε₂) one_pos)))
  refine ⟨N, fun A hA hAc η hη ↦ ?_⟩
  obtain ⟨r, hr, hrΩ⟩ := hAc.exists_cthickening_subset_open hΩ hA
  set A'' := cthickening r A with hA''def
  have hA'' : IsCompact A'' := hAc.cthickening
  obtain ⟨L, hL⟩ := exists_bound_gradₓ_of_interiorLipEst S.isOpen C (max M 1) hA'' hrΩ
  obtain ⟨Cβ, hCβ⟩ := hBeta M E0 hE0 A'' hrΩ hA''
  have hεN : ∀ n ≥ N, ε n < ε₁ ∧ ε n < ε₂ ∧ ε n < 1 := fun n hn ↦ by
    have := hN n hn
    exact ⟨this.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
      this.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
      this.trans_le (min_le_right _ _)⟩
  have hLn : ∀ n ≥ N, ∀ q ∈ A'', ‖gradₓ (v n) q‖ ≤ L := fun n hn ↦
    hL (v n) (hLip (ε n) ⟨hε n, (hεN n hn).1⟩ M (g n) (v n) (hv n) (hgM n))
      (fun t ht ↦ ((hv n).2.1.2.1 t ht).differentiableOn (by norm_num))
      (fun q hq ↦ by
        have h := semilinear_nonneg_le_max S hβ (hε n) (hv n) (hgM n) q
          ⟨subset_closure hq.1, mem_Ici.2 (le_of_lt hq.2)⟩
        rw [abs_of_nonneg h.1]
        exact h.2.trans (max_le_max le_rfl (hεN n hn).2.2.le))
  have hβn : ∀ n ≥ N, ∫⁻ p in A'', ENNReal.ofReal (betaEps β (ε n) (v n p)) ≤
      ENNReal.ofReal Cβ := fun n hn ↦
    hCβ (ε n) ⟨hε n, (hεN n hn).2.1⟩ (g n) (G n) (v n) (hg n) (hgE n) (hv n) (hgM n)
  set L' := max L 0 with hL'def
  set C' := max Cβ 0 with hC'def
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨min r (η / (2 * L' * C' + 1)), by positivity, fun n hn h hh ↦ ?_⟩
  have hhr : ‖h‖ < r := hh.trans_le (min_le_left _ _)
  have hhη : ‖h‖ < η / (2 * L' * C' + 1) := hh.trans_le (min_le_right _ _)
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  have hA''m : MeasurableSet A'' := hA''.isClosed.measurableSet
  have hnorm : ‖((h, 0) : E d × ℝ)‖ = ‖h‖ := by
    rw [Prod.norm_def]
    simp
  have hsegA : ∀ p ∈ A, ∀ ρ ∈ Icc (0 : ℝ) 1, p + ρ • ((h, 0) : E d × ℝ) ∈ A'' :=
    fun p hp ρ hρ ↦ mem_cthickening_of_dist_le _ p r A hp (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1,
        hnorm]
      nlinarith [norm_nonneg h, hρ.2])
  have hvc : ContinuousOn (v n) (UInf S.U) := (hv n).2.1.1
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * L' * ‖h‖) with hcdef
  set F : E d × ℝ → ℝ → ℝ≥0∞ := fun p ρ ↦
    ENNReal.ofReal (betaEps β (ε n) (v n (p + ρ • ((h, 0) : E d × ℝ)))) with hFdef
  have hpt : ∀ p ∈ A, ‖chiEps β (ε n) (v n) (p + (h, 0)) - chiEps β (ε n) (v n) p‖ₑ ≤
      ∫⁻ ρ in Ioc (0 : ℝ) 1, c * F p ρ := by
    intro p hp
    have h1 := abs_chiEps_add_sub_le S.isOpen hβ (hε n) (hv n).2.1 (p := p) (h := h)
      (fun ρ hρ ↦ hrΩ (hsegA p hp ρ hρ)) (L := L')
      (fun ρ hρ ↦ (hLn n hn _ (hsegA p hp ρ hρ)).trans (le_max_left _ _))
    rw [Real.enorm_eq_ofReal_abs]
    refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
    have hmaps : MapsTo (fun ρ : ℝ ↦ p + ρ • ((h, 0) : E d × ℝ)) (Icc 0 1) (UInf S.U) :=
      fun ρ hρ ↦ hrΩ (hsegA p hp ρ hρ)
    have hcont : ContinuousOn (fun ρ : ℝ ↦ 2 * L' * ‖h‖ *
        betaEps β (ε n) (v n (p + ρ • ((h, 0) : E d × ℝ)))) (Icc 0 1) :=
      continuousOn_const.mul ((hβ.continuous_betaEps _).comp_continuousOn
        (hvc.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
          hmaps))
    rw [intervalIntegral.integral_of_le zero_le_one, ofReal_integral_eq_lintegral_ofReal
      ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
      (ae_of_all _ fun ρ ↦ mul_nonneg (by positivity) (hβ.betaEps_nonneg _ _ (hε n).le))]
    refine lintegral_congr fun ρ ↦ ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have hmeas : AEMeasurable (Function.uncurry fun p ρ ↦ c * F p ρ)
      ((volume.restrict A).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.aemeasurable ?_ (hAm.prod measurableSet_Ioc)
    have hmaps : MapsTo (fun x : (E d × ℝ) × ℝ ↦ x.1 + x.2 • ((h, 0) : E d × ℝ))
        (A ×ˢ Ioc (0 : ℝ) 1) (UInf S.U) := fun x hx ↦
      hrΩ (hsegA x.1 hx.1 x.2 (Ioc_subset_Icc_self hx.2))
    exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_continuousOn
      (ENNReal.continuous_ofReal.comp_continuousOn ((hβ.continuous_betaEps _).comp_continuousOn
        (hvc.comp (continuous_fst.add (continuous_snd.smul continuous_const)).continuousOn
          hmaps)))
  have hinner : ∀ ρ ∈ Ioc (0 : ℝ) 1, ∫⁻ p in A, c * F p ρ ≤ c * ENNReal.ofReal Cβ := by
    intro ρ hρ
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_right ((setLIntegral_comp_add_le hAm hA''m
      (fun q ↦ ENNReal.ofReal (betaEps β (ε n) (v n q))) _
      fun p hp ↦ hsegA p hp ρ (Ioc_subset_Icc_self hρ)).trans (hβn n hn)) _
  calc ∫⁻ p in A, ‖chiEps β (ε n) (v n) (p + (h, 0)) - chiEps β (ε n) (v n) p‖ₑ
      ≤ ∫⁻ p in A, ∫⁻ ρ in Ioc (0 : ℝ) 1, c * F p ρ :=
        lintegral_mono_ae ((ae_restrict_iff' hAm).2 (Eventually.of_forall hpt))
    _ = ∫⁻ ρ in Ioc (0 : ℝ) 1, ∫⁻ p in A, c * F p ρ := lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ ρ in Ioc (0 : ℝ) 1, c * ENNReal.ofReal Cβ :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall hinner))
    _ = c * ENNReal.ofReal Cβ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
    _ ≤ ENNReal.ofReal η := by
        rw [hcdef, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 2 * L' * ‖h‖ * Cβ ≤ 2 * L' * C' * ‖h‖ := by
          have := le_max_left Cβ 0
          linarith [mul_nonneg (mul_nonneg hL'0 (norm_nonneg h)) (sub_nonneg.2 this)]
        have h2 : 2 * L' * C' * ‖h‖ ≤ η := by
          rw [lt_div_iff₀ (by positivity)] at hhη
          linarith [norm_nonneg h]
        linarith

end ChiEps

end Inner

end PerronVariational

end
