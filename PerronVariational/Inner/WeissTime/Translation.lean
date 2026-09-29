/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Inner.WeissTime.EnergyMoment
public import PerronVariational.Inner.SliceHeat
import GMTFoundations.Sobolev.Cutoff
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Inner.Common

/-!
# Time regularity of the energy density: translation estimates

Part of the proof of **Lemma 4.3** of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981
((4.8)–(4.10)): `L¹`-continuity of translations,
time translations of the mollified energy density (`lintegral_energyMoment_time_translate_le`),
the spatial mollification error (`lintegral_sub_mollify_le`) and auxiliary lemmas for the
assembly in `Inner/WeissTime/ChiEps.lean`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace

@[expose] public section

namespace PerronVariational

namespace Inner

variable {d : ℕ}

/-! ### Translation continuity -/

/-- `L¹`-continuity of translations for a single function continuous on `Ω`, on a compact
`A ⊆ Ω`. -/
theorem eventually_lintegral_translate_le {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {F : Type*}
    [NormedAddCommGroup F] {g : E d × ℝ → F} (hg : ContinuousOn g Ω) {A : Set (E d × ℝ)}
    (hA : A ⊆ Ω) (hAc : IsCompact A) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ w in 𝓝 (0 : E d × ℝ), ∫⁻ p in A, ‖g (p + w) - g p‖ₑ ≤ ENNReal.ofReal η := by
  obtain ⟨r, hr, hrΩ⟩ := hAc.exists_cthickening_subset_open hΩ hA
  have hA'c : IsCompact (cthickening r A) := hAc.cthickening
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  set m := (volume A).toReal with hmdef
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hη' : 0 < η / (m + 1) := by positivity
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
    (hA'c.uniformContinuousOn_of_continuous (hg.mono hrΩ)) _ hη'
  filter_upwards [ball_mem_nhds (0 : E d × ℝ) (lt_min hr hδ)] with w hw
  have hw' : ‖w‖ < min r δ := mem_ball_zero_iff.1 hw
  have hpt : ∀ p ∈ A, ‖g (p + w) - g p‖ₑ ≤ ENNReal.ofReal (η / (m + 1)) := by
    intro p hp
    have hpw : p + w ∈ cthickening r A := mem_cthickening_of_dist_le _ p r A hp (by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hw'.le.trans (min_le_left _ _))
    have h := hδu (p + w) hpw p (self_subset_cthickening A hp) (by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hw'.trans_le (min_le_right _ _))
    rw [dist_eq_norm] at h
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h.le
  calc ∫⁻ p in A, ‖g (p + w) - g p‖ₑ ≤ ∫⁻ _ in A, ENNReal.ofReal (η / (m + 1)) :=
        setLIntegral_mono' hAm hpt
    _ = ENNReal.ofReal (η / (m + 1)) * volume A := setLIntegral_const _ _
    _ = ENNReal.ofReal (η / (m + 1) * m) := by
        rw [ENNReal.ofReal_mul hη'.le, hmdef, ENNReal.ofReal_toReal hAc.measure_lt_top.ne]
    _ ≤ ENNReal.ofReal η := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

/-- **Uniform `L¹`-continuity of translations** for a sequence of functions continuous on `Ω`
converging in `L¹_loc(Ω)`. -/
theorem eventually_translation_of_tendstoLpLoc {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω) {F : Type*}
    [NormedAddCommGroup F] {f : ℕ → E d × ℝ → F} {f₀ : E d × ℝ → F}
    (hfc : ∀ n, ContinuousOn (f n) Ω) (hf₀ : LocallyIntegrableOn f₀ Ω volume)
    (hconv : TendstoLpLoc 1 volume Ω f f₀ atTop) {A : Set (E d × ℝ)} (hA : A ⊆ Ω)
    (hAc : IsCompact A) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ w in 𝓝 (0 : E d × ℝ), ∀ n, ∫⁻ p in A, ‖f n (p + w) - f n p‖ₑ ≤ ENNReal.ofReal η := by
  obtain ⟨r, hr, hrΩ⟩ := hAc.exists_cthickening_subset_open hΩ hA
  set A' := cthickening r A with hA'def
  have hA'c : IsCompact A' := hAc.cthickening
  have hA'm : MeasurableSet A' := hA'c.isClosed.measurableSet
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  have hmem : ∀ᶠ w in 𝓝 (0 : E d × ℝ), ∀ p ∈ A, p + w ∈ A' := by
    filter_upwards [ball_mem_nhds (0 : E d × ℝ) hr] with w hw p hp
    exact mem_cthickening_of_dist_le _ p r A hp (by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact (mem_ball_zero_iff.1 hw).le)
  have hev : ∀ᶠ n in atTop, eLpNorm (f n - f₀) 1 (volume.restrict A') ≤ ENNReal.ofReal (η / 8) :=
    (hconv A' hrΩ hA'c).eventually (Iic_mem_nhds (ENNReal.ofReal_pos.2 (by positivity)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hf₀m : AEStronglyMeasurable f₀ (volume.restrict A') :=
    (hf₀.mono_set hrΩ).aestronglyMeasurable
  have hfm : ∀ n, AEStronglyMeasurable (f n) (volume.restrict A') := fun n ↦
    ((hfc n).mono hrΩ).aestronglyMeasurable hA'm
  have hcauchy : ∀ n ≥ N, ∫⁻ q in A', ‖f n q - f N q‖ₑ ≤ ENNReal.ofReal (η / 4) := by
    intro n hn
    calc ∫⁻ q in A', ‖f n q - f N q‖ₑ
        ≤ ∫⁻ q in A', (‖f n q - f₀ q‖ₑ + ‖f N q - f₀ q‖ₑ) := lintegral_mono fun q ↦ by
          rw [enorm_sub_rev (f N q)]
          calc ‖f n q - f N q‖ₑ = ‖(f n q - f₀ q) + (f₀ q - f N q)‖ₑ := by
                rw [sub_add_sub_cancel]
            _ ≤ _ := enorm_add_le _ _
      _ = eLpNorm (f n - f₀) 1 (volume.restrict A') +
          eLpNorm (f N - f₀) 1 (volume.restrict A') := by
          rw [lintegral_add_left' (f := fun q ↦ ‖f n q - f₀ q‖ₑ) ((hfm n).sub hf₀m).enorm,
            eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
          rfl
      _ ≤ ENNReal.ofReal (η / 8) + ENNReal.ofReal (η / 8) := add_le_add (hN n hn) (hN N le_rfl)
      _ = ENNReal.ofReal (η / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  have hfin : ∀ᶠ w in 𝓝 (0 : E d × ℝ), ∀ n ∈ Finset.range (N + 1),
      ∫⁻ p in A, ‖f n (p + w) - f n p‖ₑ ≤ ENNReal.ofReal (η / 4) :=
    (eventually_all_finset _).2 fun n _ ↦
      eventually_lintegral_translate_le hΩ (hfc n) hA hAc (by positivity)
  filter_upwards [hfin, hmem] with w hw hwm n
  rcases lt_or_ge n (N + 1) with hn | hn
  · exact (hw n (Finset.mem_range.2 hn)).trans (ENNReal.ofReal_le_ofReal (by linarith))
  · have hnN : N ≤ n := by omega
    have hcont : ∀ k, ContinuousOn (fun p ↦ f k (p + w)) A := fun k ↦
      (hfc k).comp (continuous_add_const w).continuousOn fun p hp ↦ hrΩ (hwm p hp)
    have hsplit : ∀ p, ‖f n (p + w) - f n p‖ₑ ≤ ‖f n (p + w) - f N (p + w)‖ₑ +
        ‖f N (p + w) - f N p‖ₑ + ‖f N p - f n p‖ₑ := fun p ↦ by
      calc ‖f n (p + w) - f n p‖ₑ = ‖(f n (p + w) - f N (p + w)) + (f N (p + w) - f N p) +
            (f N p - f n p)‖ₑ := by congr 1; abel
        _ ≤ _ := (enorm_add_le _ _).trans (add_le_add_left (enorm_add_le _ _) _)
    have h1 : ∫⁻ p in A, ‖f n (p + w) - f N (p + w)‖ₑ ≤ ENNReal.ofReal (η / 4) :=
      (setLIntegral_comp_add_le hAm hA'm (fun q ↦ ‖f n q - f N q‖ₑ) w hwm).trans
        (hcauchy n hnN)
    have h3 : ∫⁻ p in A, ‖f N p - f n p‖ₑ ≤ ENNReal.ofReal (η / 4) := by
      refine (lintegral_mono_set (self_subset_cthickening (δ := r) A)).trans ?_
      refine le_of_eq_of_le (lintegral_congr fun q ↦ enorm_sub_rev (f N q) (f n q)) ?_
      exact hcauchy n hnN
    have h2 := hw N (Finset.mem_range.2 (Nat.lt_succ_self N))
    have hm1 : AEMeasurable (fun p ↦ ‖f n (p + w) - f N (p + w)‖ₑ) (volume.restrict A) :=
      ((hcont n).sub (hcont N)).enorm.aemeasurable hAm
    have hm2 : AEMeasurable (fun p ↦ ‖f N (p + w) - f N p‖ₑ) (volume.restrict A) :=
      ((hcont N).sub ((hfc N).mono (hA))).enorm.aemeasurable hAm
    calc ∫⁻ p in A, ‖f n (p + w) - f n p‖ₑ
        ≤ ∫⁻ p in A, (‖f n (p + w) - f N (p + w)‖ₑ + ‖f N (p + w) - f N p‖ₑ +
            ‖f N p - f n p‖ₑ) := lintegral_mono hsplit
      _ = (∫⁻ p in A, ‖f n (p + w) - f N (p + w)‖ₑ) + (∫⁻ p in A, ‖f N (p + w) - f N p‖ₑ) +
            ∫⁻ p in A, ‖f N p - f n p‖ₑ := by
          rw [lintegral_add_left' (hm1.add hm2), lintegral_add_left' hm1]
      _ ≤ ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) := by
          gcongr
      _ ≤ ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Time translations of the mollified energy density -/

theorem hasCompactSupport_mollAt (k : ℕ) (q : E d) : HasCompactSupport (LongTime.mollAt k q) :=
  HasCompactSupport.intro (isCompact_closedBall q (LongTime.bumpRad k))
    fun _ hx ↦ LongTime.mollAt_eq_zero hx

theorem tsupport_mollAt_subset (k : ℕ) (q : E d) :
    tsupport (LongTime.mollAt k q) ⊆ closedBall q (LongTime.bumpRad k) :=
  closure_minimal (fun _ hy ↦ by_contra fun h' ↦ hy (LongTime.mollAt_eq_zero h'))
    isClosed_closedBall

theorem exists_bound_mollAt' (k : ℕ) :
    ∃ C, ∀ q x : E d, |LongTime.mollAt k q x| ≤ C ∧ ‖∇ (LongTime.mollAt k q) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := LongTime.exists_bound_moll (d := d) k
  refine ⟨C, fun q x ↦ ⟨(hC (x - q)).1, ?_⟩⟩
  have : fderiv ℝ (LongTime.mollAt k q) x = fderiv ℝ (LongTime.moll d k) (x - q) := by
    rw [show LongTime.mollAt k q = fun x ↦ LongTime.moll d k (x - q) from rfl, fderiv_comp_sub]
  simpa [gradient, this] using (hC (x - q)).2

/-- **Time translations of the mollified energy density** ((4.8),
integrated over a box): with `m(x, t) = ∫ e(z, t) φ_δ(z - x) dz`,
`∫_{K₁ × J} |m(x, t + s) - m(x, t)| ≤ 2 Cψ (1 + L) |K₁| s ∫_{K₂ × [a, b]} ((∂ₜv)² + 1)`. -/
theorem lintegral_energyMoment_time_translate_le {U : Set (E d)} (hU : IsOpen U) {Q : E d → ℝ}
    (hQ : ContinuousOn Q U) {β : ℝ → ℝ} (hβ : IsReactionProfile β) {ε : ℝ}
    {v : E d × ℝ → ℝ} (hv : IsSemilinearSolOn U Q β ε (Ioi 0) v) (k : ℕ)
    {K₁ K₂ : Set (E d)} (hK₁m : MeasurableSet K₁) (hK₂c : IsCompact K₂) (hK₂U : K₂ ⊆ U)
    (hK₁₂ : ∀ x ∈ K₁, closedBall x (LongTime.bumpRad k) ⊆ K₂) {a b s : ℝ} (ha : 0 < a)
    (hs : 0 ≤ s) {J : Set ℝ} (hJm : MeasurableSet J) (hJ : ∀ t ∈ J, a ≤ t ∧ t + s ≤ b)
    {Cψ L : ℝ} (hCψ : ∀ q x : E d, |LongTime.mollAt k q x| ≤ Cψ ∧
      ‖∇ (LongTime.mollAt k q) x‖ ≤ Cψ) (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ K₂, ∀ τ ∈ Icc a b, ‖gradₓ v (x, τ)‖ ≤ L) :
    ∫⁻ p in K₁ ×ˢ J, ‖energyMoment Q β ε v (LongTime.mollAt k p.1) (p.2 + s) -
        energyMoment Q β ε v (LongTime.mollAt k p.1) p.2‖ₑ ≤
      ENNReal.ofReal (2 * Cψ * (1 + L)) * volume K₁ * ENNReal.ofReal s *
        ∫⁻ q in K₂ ×ˢ Icc a b, (ENNReal.ofReal (dₜ v q ^ 2) + 1) := by
  classical
  set c := 2 * Cψ * (1 + L) with hcdef
  have hK₂m : MeasurableSet K₂ := hK₂c.isClosed.measurableSet
  have hBm : MeasurableSet (K₂ ×ˢ Icc a b) := hK₂m.prod measurableSet_Icc
  have hBU : K₂ ×ˢ Icc a b ⊆ U ×ˢ Ioi 0 := prod_mono hK₂U fun τ hτ ↦ ha.trans_le hτ.1
  set Φ : E d × ℝ → ℝ≥0∞ :=
    (K₂ ×ˢ Icc a b).indicator (fun q ↦ ENNReal.ofReal (dₜ v q ^ 2) + 1) with hΦdef
  have hΦm : Measurable Φ := by
    rw [hΦdef, ← piecewise_eq_indicator]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hBm
    exact (ENNReal.continuous_ofReal.comp_continuousOn
      ((hv.2.2.2.2.2.1.mono hBU).pow 2)).add continuousOn_const
  set G : ℝ → ℝ≥0∞ := fun τ ↦ ∫⁻ x, Φ (x, τ) with hGdef
  have hGm : Measurable G := hΦm.lintegral_prod_left'
  have hGeq : ∀ τ ∈ Icc a b,
      ∫⁻ x in K₂, (ENNReal.ofReal (dₜ v (x, τ) ^ 2) + 1) = G τ := by
    intro τ hτ
    rw [hGdef, ← lintegral_indicator hK₂m]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ K₂
    · simp [hΦdef, indicator_of_mem hx, indicator_of_mem (show (x, τ) ∈ K₂ ×ˢ Icc a b from
        ⟨hx, hτ⟩)]
    · simp [hΦdef, indicator_of_notMem hx, indicator_of_notMem (show (x, τ) ∉ K₂ ×ˢ Icc a b from
        fun h ↦ hx h.1)]
  set H : ℝ → ℝ≥0∞ := fun t ↦ ∫⁻ σ in Ioc 0 s, G (t + σ) with hHdef
  have hpt : ∀ p ∈ K₁ ×ˢ J, ‖energyMoment Q β ε v (LongTime.mollAt k p.1) (p.2 + s) -
      energyMoment Q β ε v (LongTime.mollAt k p.1) p.2‖ₑ ≤ ENNReal.ofReal c * H p.2 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have hts : tsupport (LongTime.mollAt k x) ⊆ K₂ :=
      (tsupport_mollAt_subset k x).trans (hK₁₂ x hx)
    have hat := (hJ t ht).1
    have htb := (hJ t ht).2
    have h := enorm_energyMoment_sub_le hU hQ hβ hv (ψ := LongTime.mollAt k x)
      ((LongTime.contDiff_mollAt k x).of_le (by norm_num)) (hasCompactSupport_mollAt k x)
      (hts.trans hK₂U) hK₂m hts (fun y ↦ (hCψ x y).1) (fun y ↦ (hCψ x y).2) hL0
      (t₁ := t) (t₂ := t + s) (ha.trans_le hat) (by linarith)
      (fun y hy τ hτ ↦ hL y (hts hy) τ ⟨hat.trans hτ.1, hτ.2.trans htb⟩)
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [setLIntegral_congr_fun measurableSet_Ioc (fun τ hτ ↦ hGeq τ
      ⟨hat.trans hτ.1.le, hτ.2.trans htb⟩), hHdef]
    simp only
    rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
      ← lintegral_add_left_eq_self ((Ioc t (t + s)).indicator G) t]
    refine lintegral_congr fun σ ↦ ?_
    by_cases hσ : σ ∈ Ioc 0 s
    · rw [indicator_of_mem hσ, indicator_of_mem (show t + σ ∈ Ioc t (t + s) from
        ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)]
    · rw [indicator_of_notMem hσ, indicator_of_notMem (show t + σ ∉ Ioc t (t + s) from
        fun h ↦ hσ ⟨by linarith [h.1], by linarith [h.2]⟩)]
  have hswap : ∫⁻ t, H t = ENNReal.ofReal s * ∫⁻ τ, G τ := by
    simp only [hHdef]
    rw [lintegral_lintegral_swap (f := fun t σ ↦ G (t + σ))
      ((hGm.comp measurable_add).aemeasurable)]
    simp_rw [lintegral_add_right_eq_self G]
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  have hGint : ∫⁻ τ, G τ = ∫⁻ q in K₂ ×ˢ Icc a b, (ENNReal.ofReal (dₜ v q ^ 2) + 1) := by
    rw [hGdef, ← lintegral_indicator hBm, ← hΦdef, Measure.volume_eq_prod,
      lintegral_prod_symm' _ hΦm]
  calc ∫⁻ p in K₁ ×ˢ J, ‖energyMoment Q β ε v (LongTime.mollAt k p.1) (p.2 + s) -
        energyMoment Q β ε v (LongTime.mollAt k p.1) p.2‖ₑ
      ≤ ∫⁻ p in K₁ ×ˢ J, ENNReal.ofReal c * H p.2 := setLIntegral_mono' (hK₁m.prod hJm) hpt
    _ ≤ ∫⁻ x in K₁, ∫⁻ t in J, ENNReal.ofReal c * H t := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_le _
    _ = volume K₁ * ∫⁻ t in J, ENNReal.ofReal c * H t := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ volume K₁ * (ENNReal.ofReal c * ∫⁻ t, H t) := by
        gcongr
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact Measure.restrict_le_self
    _ = _ := by
        rw [hswap, hGint]
        ring

/-! ### Spatial mollification error -/

theorem moll_eq_zero_of_notMem {k : ℕ} {y : E d} (hy : y ∉ closedBall (0 : E d)
    (LongTime.bumpRad k)) : LongTime.moll d k y = 0 :=
  image_eq_zero_of_notMem_tsupport (by rwa [LongTime.tsupport_moll])

theorem prod_add_mk_zero (p : E d × ℝ) (y : E d) : p + ((y, 0) : E d × ℝ) = (p.1 + y, p.2) := by
  ext <;> simp

/-- **Spatial mollification error** ((4.9), (4.10)): if the
spatial translations of `e` by vectors of length `≤ δ` are `L¹(B)`-small (by `c`), then so is
`e - e * φ_δ`. -/
theorem lintegral_sub_mollify_le {Ω : Set (E d × ℝ)} {e : E d × ℝ → ℝ} (hec : ContinuousOn e Ω)
    {B : Set (E d × ℝ)} (hBm : MeasurableSet B) {k : ℕ}
    (hBΩ : ∀ p ∈ B, ∀ y ∈ closedBall (0 : E d) (LongTime.bumpRad k), p + (y, 0) ∈ Ω)
    {c : ℝ≥0∞} (htr : ∀ y ∈ closedBall (0 : E d) (LongTime.bumpRad k),
      ∫⁻ p in B, ‖e (p + (y, 0)) - e p‖ₑ ≤ c) :
    ∫⁻ p in B, ‖e p - ∫ z, e (z, p.2) * LongTime.mollAt k p.1 z‖ₑ ≤ c := by
  set cB := closedBall (0 : E d) (LongTime.bumpRad k) with hcBdef
  have hcBc : IsCompact cB := isCompact_closedBall _ _
  have hcBm : MeasurableSet cB := measurableSet_closedBall
  have hmi : Integrable (LongTime.moll d k) :=
    (LongTime.contDiff_moll k).continuous.integrable_of_hasCompactSupport
      (LongTime.hasCompactSupport_moll k)
  set F : E d × ℝ → E d → ℝ≥0∞ := fun p y ↦
    ‖e (p + (y, 0)) - e p‖ₑ * ENNReal.ofReal (LongTime.moll d k y) with hFdef
  have hpt : ∀ p ∈ B, ‖e p - ∫ z, e (z, p.2) * LongTime.mollAt k p.1 z‖ₑ ≤ ∫⁻ y in cB, F p y := by
    intro p hp
    have hcont : ContinuousOn (fun y ↦ e (p + (y, 0))) cB :=
      hec.comp ((continuous_const.add (continuous_id.prodMk continuous_const)).continuousOn)
        fun y hy ↦ hBΩ p hp y hy
    have h1 : ∫ z, e (z, p.2) * LongTime.mollAt k p.1 z =
        ∫ y, e (p + (y, 0)) * LongTime.moll d k y := by
      rw [← integral_add_left_eq_self (fun z ↦ e (z, p.2) * LongTime.mollAt k p.1 z) p.1]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only [LongTime.mollAt, add_sub_cancel_left, prod_add_mk_zero]
    have h2 : e p = ∫ y, e p * LongTime.moll d k y := by
      rw [integral_const_mul, LongTime.integral_moll, mul_one]
    have hi2 : Integrable fun y ↦ e (p + (y, 0)) * LongTime.moll d k y :=
      GMTFoundations.integrable_of_continuousOn_of_zero hcBc
        (hcont.mul (LongTime.contDiff_moll k).continuous.continuousOn)
        fun y hy ↦ by simp [moll_eq_zero_of_notMem hy]
    rw [h1, h2, ← integral_sub (hmi.const_mul _) hi2]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    rw [setLIntegral_eq_of_support_subset]
    · refine lintegral_congr fun y ↦ ?_
      rw [← sub_mul, enorm_mul, enorm_sub_rev, hFdef,
        Real.enorm_of_nonneg (LongTime.moll_nonneg k y)]
    · intro y hy
      by_contra hy'
      exact hy (by simp [hFdef, moll_eq_zero_of_notMem hy'])
  have hmeas :
      AEMeasurable (Function.uncurry F) ((volume.restrict B).prod (volume.restrict cB)) := by
    rw [Measure.prod_restrict]
    have hB : ∀ q ∈ B ×ˢ cB, q.1 ∈ Ω := fun q hq ↦ by
      simpa [Prod.mk_zero_zero] using hBΩ q.1 hq.1 0
        (mem_closedBall_self (LongTime.bumpRad_pos k).le)
    have h1 : AEMeasurable (fun q : (E d × ℝ) × E d ↦ ‖e (q.1 + (q.2, 0)) - e q.1‖ₑ)
        (volume.restrict (B ×ˢ cB)) :=
      ContinuousOn.aemeasurable (((hec.comp (continuous_fst.add
        (continuous_snd.prodMk continuous_const)).continuousOn
        fun q hq ↦ hBΩ q.1 hq.1 q.2 hq.2).sub (hec.comp continuous_fst.continuousOn hB)).enorm)
        (hBm.prod hcBm)
    have h2 : Measurable (fun q : (E d × ℝ) × E d ↦ ENNReal.ofReal (LongTime.moll d k q.2)) :=
      (ENNReal.continuous_ofReal.comp
        ((LongTime.contDiff_moll k).continuous.comp continuous_snd)).measurable
    exact h1.mul h2.aemeasurable
  have hone : ∫⁻ y, ENNReal.ofReal (LongTime.moll d k y) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hmi (ae_of_all _ (LongTime.moll_nonneg k)),
      LongTime.integral_moll, ENNReal.ofReal_one]
  calc ∫⁻ p in B, ‖e p - ∫ z, e (z, p.2) * LongTime.mollAt k p.1 z‖ₑ
      ≤ ∫⁻ p in B, ∫⁻ y in cB, F p y := setLIntegral_mono' hBm hpt
    _ = ∫⁻ y in cB, ∫⁻ p in B, F p y := lintegral_lintegral_swap hmeas
    _ = ∫⁻ y in cB,
          (∫⁻ p in B, ‖e (p + (y, 0)) - e p‖ₑ) * ENNReal.ofReal (LongTime.moll d k y) := by
        refine lintegral_congr fun y ↦ ?_
        rw [hFdef, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y in cB, c * ENNReal.ofReal (LongTime.moll d k y) :=
        setLIntegral_mono' hcBm fun y hy ↦ by gcongr; exact htr y hy
    _ ≤ ∫⁻ y, c * ENNReal.ofReal (LongTime.moll d k y) := setLIntegral_le_lintegral _ _
    _ = c := by
        rw [lintegral_const_mul (f := fun y ↦ ENNReal.ofReal (LongTime.moll d k y)) _
          (ENNReal.continuous_ofReal.comp (LongTime.contDiff_moll k).continuous).measurable,
          hone, mul_one]

/-! ### Auxiliary lemmas for the assembly -/

/-- `L²_loc` convergence implies `L¹_loc` convergence. -/
theorem tendstoLpLoc_one_of_two {Ω : Set (E d × ℝ)} {F : Type*} [NormedAddCommGroup F]
    {f : ℕ → E d × ℝ → F} {f₀ : E d × ℝ → F} (hfc : ∀ n, ContinuousOn (f n) Ω)
    (hf₀ : LocallyIntegrableOn f₀ Ω volume) (h : TendstoLpLoc 2 volume Ω f f₀ atTop) :
    TendstoLpLoc 1 volume Ω f f₀ atTop := by
  intro K hK hKc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hm : ∀ n, AEStronglyMeasurable (f n - f₀) (volume.restrict K) := fun n ↦
    (((hfc n).mono hK).aestronglyMeasurable hKm).sub (hf₀.mono_set hK).aestronglyMeasurable
  set c : ℝ≥0∞ := (volume.restrict K) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hc : c ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
    rw [Measure.restrict_apply_univ]
    exact hKc.measure_lt_top.ne
  have h2 := ENNReal.Tendsto.mul_const (h K hK hKc) (Or.inr hc)
  rw [zero_mul] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n ↦ zero_le)
    fun n ↦ eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) (hm n)

/-- Translations of `|f_n|²` from translations of `f_n` and a uniform bound. -/
theorem eventually_translation_normSq {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    {f : ℕ → E d × ℝ → E d} {f₀ : E d × ℝ → E d} (hfc : ∀ n, ContinuousOn (f n) Ω)
    (hf₀ : LocallyIntegrableOn f₀ Ω volume) (hconv : TendstoLpLoc 1 volume Ω f f₀ atTop)
    {A A' : Set (E d × ℝ)} (hA : A ⊆ Ω) (hAc : IsCompact A)
    (hAA' : ∀ᶠ w in 𝓝 (0 : E d × ℝ), ∀ p ∈ A, p + w ∈ A') (hAA'' : A ⊆ A') {N : ℕ} {L : ℝ}
    (hL : ∀ n ≥ N, ∀ q ∈ A', ‖f n q‖ ≤ L) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ w in 𝓝 (0 : E d × ℝ), ∀ n ≥ N,
      ∫⁻ p in A, ‖‖f n (p + w)‖ ^ 2 - ‖f n p‖ ^ 2‖ₑ ≤ ENNReal.ofReal η := by
  set L' := max L 0 with hL'def
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  have hc : 0 < 2 * L' + 1 := by positivity
  filter_upwards [eventually_translation_of_tendstoLpLoc hΩ hfc hf₀ hconv hA hAc
    (div_pos hη hc), hAA'] with w hw hwA n hn
  have hpt : ∀ p ∈ A, ‖‖f n (p + w)‖ ^ 2 - ‖f n p‖ ^ 2‖ₑ ≤
      ENNReal.ofReal (2 * L' + 1) * ‖f n (p + w) - f n p‖ₑ := by
    intro p hp
    have h1 : ‖f n (p + w)‖ ≤ L' := (hL n hn _ (hwA p hp)).trans (le_max_left _ _)
    have h2 : ‖f n p‖ ≤ L' := (hL n hn _ (hAA'' hp)).trans (le_max_left _ _)
    have h3 := abs_norm_sub_norm_le (f n (p + w)) (f n p)
    have key : |‖f n (p + w)‖ ^ 2 - ‖f n p‖ ^ 2| ≤ (2 * L' + 1) * ‖f n (p + w) - f n p‖ := by
      rw [show ‖f n (p + w)‖ ^ 2 - ‖f n p‖ ^ 2 =
        (‖f n (p + w)‖ - ‖f n p‖) * (‖f n (p + w)‖ + ‖f n p‖) by ring, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ ‖f n (p + w)‖ + ‖f n p‖)]
      calc |‖f n (p + w)‖ - ‖f n p‖| * (‖f n (p + w)‖ + ‖f n p‖)
          ≤ ‖f n (p + w) - f n p‖ * (2 * L' + 1) :=
            mul_le_mul h3 (by linarith) (by positivity) (norm_nonneg _)
        _ = _ := by ring
    rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm, ← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal key
  calc ∫⁻ p in A, ‖‖f n (p + w)‖ ^ 2 - ‖f n p‖ ^ 2‖ₑ
      ≤ ∫⁻ p in A, ENNReal.ofReal (2 * L' + 1) * ‖f n (p + w) - f n p‖ₑ :=
        setLIntegral_mono' hAm hpt
    _ = ENNReal.ofReal (2 * L' + 1) * ∫⁻ p in A, ‖f n (p + w) - f n p‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * L' + 1) * ENNReal.ofReal (η / (2 * L' + 1)) := by gcongr; exact hw n
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_mul hc.le, mul_div_cancel₀ _ hc.ne']

/-- Two-sided temporal translation estimates from one-sided ones (on larger compacts). -/
theorem time_translation_of_nonneg {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    {f : ℕ → E d × ℝ → ℝ} {N : ℕ}
    (h : ∀ A ⊆ Ω, IsCompact A → ∀ η > 0, ∃ ρ > 0, ∀ n ≥ N, ∀ s : ℝ, 0 ≤ s → s < ρ →
      ∫⁻ p in A, ‖f n (p + (0, s)) - f n p‖ₑ ≤ ENNReal.ofReal η) :
    ∀ A ⊆ Ω, IsCompact A → ∀ η > 0, ∃ ρ > 0, ∀ n ≥ N, ∀ s : ℝ, |s| < ρ →
      ∫⁻ p in A, ‖f n (p + (0, s)) - f n p‖ₑ ≤ ENNReal.ofReal η := by
  intro A hA hAc η hη
  obtain ⟨r, hr, hrΩ⟩ := hAc.exists_cthickening_subset_open hΩ hA
  obtain ⟨ρ, hρ, hρh⟩ := h _ hrΩ hAc.cthickening η hη
  refine ⟨min r ρ, lt_min hr hρ, fun n hn s hs ↦ ?_⟩
  have hsr : |s| < r := hs.trans_le (min_le_left _ _)
  have hsρ : |s| < ρ := hs.trans_le (min_le_right _ _)
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  rcases le_or_gt 0 s with h0 | h0
  · exact (lintegral_mono_set (self_subset_cthickening A)).trans
      (hρh n hn s h0 (by rwa [abs_of_nonneg h0] at hsρ))
  · have hmem : ∀ p ∈ A, p + ((0 : E d), s) ∈ cthickening r A := fun p hp ↦
      mem_cthickening_of_dist_le _ p r A hp (by
        rw [dist_eq_norm, add_sub_cancel_left, Prod.norm_def, norm_zero, Real.norm_eq_abs]
        exact max_le (abs_nonneg _ |>.trans hsr.le) hsr.le)
    have h1 := setLIntegral_comp_add_le hAm hAc.cthickening.isClosed.measurableSet
      (fun q ↦ ‖f n (q + (0, -s)) - f n q‖ₑ) (0, s) hmem
    have h2 := hρh n hn (-s) (by linarith) (by rw [abs_of_neg h0] at hsρ; exact hsρ)
    refine le_trans (le_of_eq ?_) (h1.trans h2)
    refine lintegral_congr fun p ↦ ?_
    have : p + ((0 : E d), s) + (0, -s) = p := by ext <;> simp
    simp only [this]
    rw [enorm_sub_rev]

/-- `Q² χ` differences from energy-density differences (pointwise). -/
theorem abs_sub_le_of_energy {q c₁ c₂ f₁ f₂ m : ℝ} (hm : 0 < m) (hq : m ≤ q) :
    |c₁ - c₂| ≤ (1 / m) * (|(f₁ + q * c₁) - (f₂ + q * c₂)| + |f₁ - f₂|) := by
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm]
  have h1 : q * |c₁ - c₂| ≤ |(f₁ + q * c₁) - (f₂ + q * c₂)| + |f₁ - f₂| := by
    have : q * (c₁ - c₂) = ((f₁ + q * c₁) - (f₂ + q * c₂)) - (f₁ - f₂) := by ring
    rw [← abs_of_pos (hm.trans_le hq), ← abs_mul, this, abs_of_pos (hm.trans_le hq)]
    exact abs_sub _ _
  nlinarith [abs_nonneg (c₁ - c₂)]

/-- Spatial differences of the energy density (pointwise). -/
theorem abs_energy_sub_le {F₁ F₂ q₁ q₂ c₁ c₂ Qm : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1)
    (hq₂ : 0 ≤ q₂) (hq₂' : q₂ ≤ Qm) :
    |(F₁ + q₁ * c₁) - (F₂ + q₂ * c₂)| ≤ |F₁ - F₂| + |q₁ - q₂| + Qm * |c₁ - c₂| := by
  have : (F₁ + q₁ * c₁) - (F₂ + q₂ * c₂) = (F₁ - F₂) + (q₁ - q₂) * c₁ + q₂ * (c₁ - c₂) := by ring
  rw [this]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
  · rw [abs_mul, abs_of_nonneg hc₁]
    nlinarith [abs_nonneg (q₁ - q₂)]
  · rw [abs_mul, abs_of_nonneg hq₂]
    exact mul_le_mul_of_nonneg_right hq₂' (abs_nonneg _)

/-- A mollification of a measurable function is strongly measurable in `(x, t)`. -/
theorem stronglyMeasurable_mollify {e : E d × ℝ → ℝ} (he : Measurable e) (k : ℕ) :
    StronglyMeasurable fun p : E d × ℝ ↦ ∫ z, e (z, p.2) * LongTime.mollAt k p.1 z := by
  refine StronglyMeasurable.integral_prod_right (f := fun (p : E d × ℝ) (z : E d) ↦
    e (z, p.2) * LongTime.mollAt k p.1 z) ?_
  refine Measurable.stronglyMeasurable ?_
  exact (he.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
    ((LongTime.contDiff_moll k).continuous.measurable.comp
      (measurable_snd.sub (measurable_fst.comp measurable_fst)))

/-- Temporal translations of `χ` from those of the energy density `e = F + Q² χ` (through its
mollification `mt`, with measurable version `mm`) and of `F` (pointwise algebra and
integration). -/
theorem lintegral_time_translate_of_energy {B B' : Set (E d × ℝ)} (hBm : MeasurableSet B)
    (hB'm : MeasurableSet B') (hBB' : B ⊆ B') {s : ℝ}
    (hmemB' : ∀ p ∈ B, p + ((0 : E d), s) ∈ B') {χ Fn e mm mt : E d × ℝ → ℝ} {Q2 : E d → ℝ}
    {m η₁ : ℝ} (hm : 0 < m) (hη₁ : 0 ≤ η₁) (hQ2 : ∀ p ∈ B, m ≤ Q2 p.1)
    (he : ∀ p, e p = Fn p + Q2 p.1 * χ p) (hmm_eq : ∀ p ∈ B', mm p = mt p)
    (hem : AEMeasurable (fun p ↦ e (p + ((0 : E d), s))) (volume.restrict B))
    (he0 : AEMeasurable e (volume.restrict B)) (hmmm : Measurable mm)
    (hmoll : ∫⁻ p in B', ‖e p - mt p‖ₑ ≤ ENNReal.ofReal η₁)
    (htime : ∫⁻ p in B, ‖mt (p + (0, s)) - mt p‖ₑ ≤ ENNReal.ofReal η₁)
    (hF : ∫⁻ p in B, ‖Fn (p + (0, s)) - Fn p‖ₑ ≤ ENNReal.ofReal η₁) :
    ∫⁻ p in B, ‖χ (p + (0, s)) - χ p‖ₑ ≤ ENNReal.ofReal (4 * η₁ / m) := by
  have hpt : ∀ p ∈ B, ‖χ (p + (0, s)) - χ p‖ₑ ≤
      ENNReal.ofReal (1 / m) * (‖e (p + (0, s)) - mm (p + (0, s))‖ₑ +
        ‖mm (p + (0, s)) - mm p‖ₑ + ‖mm p - e p‖ₑ + ‖Fn (p + (0, s)) - Fn p‖ₑ) := by
    intro p hp
    have h := abs_sub_le_of_energy (c₁ := χ (p + (0, s))) (c₂ := χ p) (f₁ := Fn (p + (0, s)))
      (f₂ := Fn p) hm (hQ2 p hp)
    have he1 : e (p + (0, s)) = Fn (p + (0, s)) + Q2 p.1 * χ (p + (0, s)) := by
      rw [he]
      simp
    rw [← he1, ← he p] at h
    have htri : |e (p + (0, s)) - e p| ≤ |e (p + (0, s)) - mm (p + (0, s))| +
        |mm (p + (0, s)) - mm p| + |mm p - e p| := by
      have : e (p + (0, s)) - e p = (e (p + (0, s)) - mm (p + (0, s))) +
          (mm (p + (0, s)) - mm p) + (mm p - e p) := by ring
      rw [this]
      exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    simp only [Real.enorm_eq_ofReal_abs]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (abs_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (abs_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    linarith
  have ha1 : AEMeasurable (fun p ↦ ‖e (p + (0, s)) - mm (p + (0, s))‖ₑ) (volume.restrict B) :=
    (hem.sub (hmmm.comp (measurable_add_const _)).aemeasurable).enorm
  have ha2 : AEMeasurable (fun p ↦ ‖mm (p + (0, s)) - mm p‖ₑ) (volume.restrict B) :=
    ((hmmm.comp (measurable_add_const _)).sub hmmm).enorm.aemeasurable
  have ha3 : AEMeasurable (fun p ↦ ‖mm p - e p‖ₑ) (volume.restrict B) :=
    (hmmm.aemeasurable.sub he0).enorm
  have hc1 : ∀ q ∈ B', ‖e q - mm q‖ₑ = ‖e q - mt q‖ₑ := fun q hq ↦ by rw [hmm_eq q hq]
  have hc3 : ∀ q ∈ B', ‖mm q - e q‖ₑ = ‖e q - mt q‖ₑ := fun q hq ↦ by
    rw [hmm_eq q hq, enorm_sub_rev]
  have hc2 : ∀ p ∈ B, ‖mm (p + (0, s)) - mm p‖ₑ = ‖mt (p + (0, s)) - mt p‖ₑ :=
    fun p hp ↦ by rw [hmm_eq _ (hmemB' p hp), hmm_eq p (hBB' hp)]
  have hI1 : ∫⁻ p in B, ‖e (p + (0, s)) - mm (p + (0, s))‖ₑ ≤ ENNReal.ofReal η₁ := by
    refine (setLIntegral_comp_add_le hBm hB'm (fun q ↦ ‖e q - mm q‖ₑ) _ hmemB').trans ?_
    rw [setLIntegral_congr_fun hB'm hc1]
    exact hmoll
  have hI2 : ∫⁻ p in B, ‖mm (p + (0, s)) - mm p‖ₑ ≤ ENNReal.ofReal η₁ := by
    rw [setLIntegral_congr_fun hBm hc2]
    exact htime
  have hI3 : ∫⁻ p in B, ‖mm p - e p‖ₑ ≤ ENNReal.ofReal η₁ := by
    refine (lintegral_mono_set hBB').trans ?_
    rw [setLIntegral_congr_fun hB'm hc3]
    exact hmoll
  calc ∫⁻ p in B, ‖χ (p + (0, s)) - χ p‖ₑ
      ≤ ∫⁻ p in B, ENNReal.ofReal (1 / m) * (‖e (p + (0, s)) - mm (p + (0, s))‖ₑ +
        ‖mm (p + (0, s)) - mm p‖ₑ + ‖mm p - e p‖ₑ + ‖Fn (p + (0, s)) - Fn p‖ₑ) :=
        setLIntegral_mono' hBm hpt
    _ = ENNReal.ofReal (1 / m) * ((∫⁻ p in B, ‖e (p + (0, s)) - mm (p + (0, s))‖ₑ) +
        (∫⁻ p in B, ‖mm (p + (0, s)) - mm p‖ₑ) + (∫⁻ p in B, ‖mm p - e p‖ₑ) +
        ∫⁻ p in B, ‖Fn (p + (0, s)) - Fn p‖ₑ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left' ((ha1.add ha2).add ha3), lintegral_add_left' (ha1.add ha2),
          lintegral_add_left' ha1]
    _ ≤ ENNReal.ofReal (1 / m) * (ENNReal.ofReal η₁ + ENNReal.ofReal η₁ + ENNReal.ofReal η₁ +
        ENNReal.ofReal η₁) := by gcongr
    _ = ENNReal.ofReal (4 * η₁ / m) := by
        rw [← ENNReal.ofReal_add hη₁ hη₁, ← ENNReal.ofReal_add (by positivity) hη₁,
          ← ENNReal.ofReal_add (by positivity) hη₁, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

end Inner

end PerronVariational

end
