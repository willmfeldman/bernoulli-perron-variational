/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import GMTFoundations.Sobolev.Mollify
import Mathlib.Order.CompletePartialOrder
import PerronVariational.Stationary.TwoPlane.Basic

/-!
# Two-plane functions: the one-dimensional problem

Part of **Proposition 2.14** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981, Step 3: the
one-dimensional downward minimality for absolutely continuous competitors (`oneDim_core`,
`oneDim_downward`) and weak derivatives on the line (`exists_primitive_of_weakDeriv`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal Convolution

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

section OneDim

/-- Cauchy–Schwarz on an interval: `(∫_a^b g)² ≤ (b - a) ∫_a^b g²`. -/
theorem sq_intervalIntegral_le {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun s ↦ g s ^ 2) volume a b) :
    (∫ s in a..b, g s) ^ 2 ≤ (b - a) * ∫ s in a..b, g s ^ 2 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  set m := (∫ s in a..b, g s) / (b - a) with hm
  have hba : 0 < b - a := sub_pos.2 hlt
  have h0 : 0 ≤ ∫ s in a..b, (g s - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun s _ ↦ sq_nonneg _
  have hexp : ∫ s in a..b, (g s - m) ^ 2 =
      (∫ s in a..b, g s ^ 2) - 2 * m * (∫ s in a..b, g s) + m ^ 2 * (b - a) := by
    have e : (fun s ↦ (g s - m) ^ 2) = fun s ↦ (g s ^ 2 - 2 * m * g s) + m ^ 2 := by
      funext s; ring
    rw [e, intervalIntegral.integral_add (hg2.sub (hg.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hg2 (hg.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hexp] at h0
  have hmI : m * (b - a) = ∫ s in a..b, g s := by rw [hm]; field_simp
  nlinarith [hmI]

/-- Scaled Step 3 inequality: `(α T)²/x + q² x ≥ (α² + q²) T` for `x ∈ (0, T]`, `q² ≤ α²`. -/
theorem ratio_ineq_scaled {α q T x : ℝ} (hx : 0 < x) (hxT : x ≤ T) (hqα : q ^ 2 ≤ α ^ 2) :
    (α ^ 2 + q ^ 2) * T ≤ (α * T) ^ 2 / x + q ^ 2 * x := by
  have hT : 0 < T := hx.trans_le hxT
  have h := ratio_ineq (α := α) (q := q) (x := x / T) (div_pos hx hT)
    ((div_le_one hT).2 hxT) hqα
  have e1 : (α * T) ^ 2 / x + q ^ 2 * x = T * (α ^ 2 / (x / T) + q ^ 2 * (x / T)) := by
    field_simp
  rw [e1, mul_comm]
  exact mul_le_mul_of_nonneg_left h hT.le

/-- **Proposition 2.14, Step 3, one side**. On `[c, T]` with `0 ≤ c ≤ T`, a continuous
`w = ∫ g` with `w ≤ α|s|`, `w(T) = αT`, and `w(c) ≤ 0` or `w(c) = αc`, has
`∫_c^T g² + q² 1_{w > 0} ≥ (α² + q²)(T - c)` when `0 < q ≤ α`. -/
theorem oneDim_core {α q c T : ℝ} (hq : 0 < q) (hqα : q ≤ α) (hc : 0 ≤ c) (hcT : c ≤ T)
    {w g : ℝ → ℝ} (hwg : ∀ a b, IntervalIntegrable g volume a b ∧ w b - w a = ∫ s in a..b, g s)
    (hT : w T = α * T) (hc' : w c ≤ 0 ∨ w c = α * c) :
    ENNReal.ofReal ((α ^ 2 + q ^ 2) * (T - c)) ≤
      ∫⁻ s in Ioo c T, ENNReal.ofReal (g s ^ 2 + q ^ 2 * {s | 0 < w s}.indicator 1 s) := by
  rcases hcT.eq_or_lt with rfl | hcT
  · simp
  have hα : 0 < α := hq.trans_le hqα
  have hqα2 : q ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ hq.le hqα 2
  have hwc : Continuous w := by
    have : w = fun s ↦ w 0 + ∫ t in (0 : ℝ)..s, g t := by
      funext s; have := (hwg 0 s).2; linarith
    rw [this]
    exact continuous_const.add
      (intervalIntegral.continuous_primitive (fun a b ↦ (hwg a b).1) 0)
  set F : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (g s ^ 2 + q ^ 2 * {s | 0 < w s}.indicator 1 s)
    with hFdef
  have hind0 : ∀ s, 0 ≤ q ^ 2 * {s | 0 < w s}.indicator (1 : ℝ → ℝ) s := fun s ↦
    mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  -- if the Dirichlet part is infinite there is nothing to prove
  by_cases hfin : ∫⁻ s in Ioo c T, ENNReal.ofReal (g s ^ 2) = (⊤ : ℝ≥0∞)
  · calc _ ≤ (⊤ : ℝ≥0∞) := le_top
      _ = ∫⁻ s in Ioo c T, ENNReal.ofReal (g s ^ 2) := hfin.symm
      _ ≤ ∫⁻ s in Ioo c T, F s := lintegral_mono fun s ↦
          ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hind0 s))
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioo c T)) :=
    ((hwg c T).1.1.mono_set Ioo_subset_Ioc_self).aestronglyMeasurable
  have hg2 : IntegrableOn (fun s ↦ g s ^ 2) (Ioo c T) :=
    (lintegral_ofReal_ne_top_iff_integrable (hgm.pow 2)
      (Eventually.of_forall fun s ↦ sq_nonneg _)).1 hfin
  -- the basic estimate on a terminal interval where `w > 0`
  have claim : ∀ s₁, c ≤ s₁ → s₁ < T → (∀ s ∈ Ioo s₁ T, 0 < w s) →
      ENNReal.ofReal ((w T - w s₁) ^ 2 / (T - s₁) + q ^ 2 * (T - s₁)) ≤ ∫⁻ s in Ioo c T, F s := by
    intro s₁ hcs hsT hpos
    have hsub : Ioo s₁ T ⊆ Ioo c T := Ioo_subset_Ioo_left hcs
    have hg2' : IntegrableOn (fun s ↦ g s ^ 2) (Ioo s₁ T) := hg2.mono_set hsub
    have hF : ∫⁻ s in Ioo s₁ T, F s = ∫⁻ s in Ioo s₁ T, ENNReal.ofReal (g s ^ 2 + q ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun s hs ↦ ?_
      simp only [hFdef]
      rw [indicator_of_mem (show s ∈ {s | 0 < w s} from hpos s hs), Pi.one_apply, mul_one]
    have hc2 : IntegrableOn (fun _ ↦ q ^ 2) (Ioo s₁ T) := integrableOn_const measure_Ioo_lt_top.ne
    have hI : ∫⁻ s in Ioo s₁ T, ENNReal.ofReal (g s ^ 2 + q ^ 2) =
        ENNReal.ofReal ((∫ s in s₁..T, g s ^ 2) + q ^ 2 * (T - s₁)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (f := fun s ↦ g s ^ 2 + q ^ 2)
        (by exact hg2'.add hc2)
        (Eventually.of_forall fun s ↦ by positivity)]
      congr 1
      rw [integral_add hg2' hc2, setIntegral_const, intervalIntegral.integral_of_le hsT.le,
        integral_Ioc_eq_integral_Ioo, Real.volume_real_Ioo_of_le hsT.le, smul_eq_mul, mul_comm]
    have hCS := sq_intervalIntegral_le hsT.le (hwg s₁ T).1
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hsT.le).2 hg2')
    rw [← (hwg s₁ T).2] at hCS
    have hts : 0 < T - s₁ := sub_pos.2 hsT
    calc ENNReal.ofReal ((w T - w s₁) ^ 2 / (T - s₁) + q ^ 2 * (T - s₁))
        ≤ ENNReal.ofReal ((∫ s in s₁..T, g s ^ 2) + q ^ 2 * (T - s₁)) := by
          refine ENNReal.ofReal_le_ofReal (add_le_add_left ?_ _)
          rw [div_le_iff₀ hts, mul_comm]
          linarith
      _ = ∫⁻ s in Ioo s₁ T, F s := by rw [hF, hI]
      _ ≤ ∫⁻ s in Ioo c T, F s := lintegral_mono_set hsub
  have hαT : 0 < α * T := mul_pos hα (hc.trans_lt hcT)
  set Z : Set ℝ := Icc c T ∩ {s | w s ≤ 0} with hZdef
  have hZc : IsCompact Z := isCompact_Icc.inter_right (isClosed_le hwc continuous_const)
  rcases Z.eq_empty_or_nonempty with hZ | hZ
  · -- `w > 0` on `[c, T]`
    have hpos : ∀ s ∈ Icc c T, 0 < w s := fun s hs ↦ by
      by_contra h
      have : s ∈ Z := ⟨hs, not_lt.1 h⟩
      rw [hZ] at this; exact this
    have hwc' : w c = α * c := hc'.resolve_left (not_le.2 (hpos c ⟨le_rfl, hcT.le⟩))
    refine le_trans (le_of_eq ?_) (claim c le_rfl hcT fun s hs ↦ hpos s (Ioo_subset_Icc_self hs))
    congr 1
    rw [hT, hwc']
    have : T - c ≠ 0 := (sub_pos.2 hcT).ne'
    field_simp
  · set s₀ := sSup Z with hs₀
    have hs₀Z : s₀ ∈ Z := hZc.sSup_mem hZ
    have hbdd : BddAbove Z := hZc.bddAbove
    have hws₀ : w s₀ ≤ 0 := hs₀Z.2
    have hs₀T : s₀ < T := by
      refine lt_of_le_of_ne hs₀Z.1.2 fun h ↦ ?_
      rw [h, hT] at hws₀; linarith
    have hpos : ∀ s ∈ Ioo s₀ T, 0 < w s := fun s hs ↦ by
      by_contra h
      have : s ∈ Z := ⟨⟨hs₀Z.1.1.trans hs.1.le, hs.2.le⟩, not_lt.1 h⟩
      exact absurd (le_csSup hbdd this) (not_le.2 hs.1)
    refine le_trans ?_ (claim s₀ hs₀Z.1.1 hs₀T hpos)
    have hx : 0 < T - s₀ := sub_pos.2 hs₀T
    have hxT : T - s₀ ≤ T := by linarith [hs₀Z.1.1]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (α ^ 2 + q ^ 2) * (T - c) ≤ (α ^ 2 + q ^ 2) * T := by
          have : 0 ≤ α ^ 2 + q ^ 2 := by positivity
          nlinarith
      _ ≤ (α * T) ^ 2 / (T - s₀) + q ^ 2 * (T - s₀) := ratio_ineq_scaled hx hxT hqα2
      _ ≤ (w T - w s₀) ^ 2 / (T - s₀) + q ^ 2 * (T - s₀) := by
          gcongr
          rw [hT]; linarith

theorem continuous_of_forall_intervalIntegral {w g : ℝ → ℝ}
    (hwg : ∀ a b, IntervalIntegrable g volume a b ∧ w b - w a = ∫ s in a..b, g s) :
    Continuous w := by
  have : w = fun s ↦ w 0 + ∫ t in (0 : ℝ)..s, g t := by
    funext s; have := (hwg 0 s).2; linarith
  rw [this]
  exact continuous_const.add (intervalIntegral.continuous_primitive (fun a b ↦ (hwg a b).1) 0)

/-- Reflection `s ↦ -s` of a primitive. -/
theorem forall_intervalIntegral_comp_neg {w g : ℝ → ℝ}
    (hwg : ∀ a b, IntervalIntegrable g volume a b ∧ w b - w a = ∫ s in a..b, g s) :
    ∀ a b, IntervalIntegrable (fun s ↦ -g (-s)) volume a b ∧
      w (-b) - w (-a) = ∫ s in a..b, -g (-s) := by
  intro a b
  refine ⟨?_, ?_⟩
  · have := (IntervalIntegrable.iff_comp_neg (f := g) (a := -a) (b := -b)).1 (hwg (-a) (-b)).1
    have h := this.neg
    simp only [neg_neg] at h
    exact h
  · rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg, ← (hwg (-b) (-a)).2]
    ring

theorem setLIntegral_Ioo_comp_neg (f : ℝ → ℝ≥0∞) (c T : ℝ) :
    ∫⁻ s in Ioo c T, f (-s) = ∫⁻ s in Ioo (-T) (-c), f s := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.neg ℝ).measurableEmbedding f (Ioo (-T) (-c))
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioo (-T) (-c) = Ioo c T := by
    ext s
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hpre] at h
  exact h

/-- **Proposition 2.14, Step 3** in one dimension: if `0 < q ≤ α` and `w = ∫ g` is a
downward competitor for `α|s|` on `(a, b)` (`w ≤ α|s|` a.e., `w = α|s|` a.e. off `(a, b)`), then
`∫_a^b g² + q² 1_{w > 0} ≥ (α² + q²)(b - a) = J(α|·|; (a, b))`. -/
theorem oneDim_downward {α q a b : ℝ} (hq : 0 < q) (hqα : q ≤ α) (hab : a ≤ b)
    {w g : ℝ → ℝ} (hwg : ∀ a b, IntervalIntegrable g volume a b ∧ w b - w a = ∫ s in a..b, g s)
    (hle : ∀ᵐ s, w s ≤ α * |s|) (hout : ∀ᵐ s, s ∉ Ioo a b → w s = α * |s|) :
    ENNReal.ofReal ((α ^ 2 + q ^ 2) * (b - a)) ≤
      ∫⁻ s in Ioo a b, ENNReal.ofReal (g s ^ 2 + q ^ 2 * {s | 0 < w s}.indicator 1 s) := by
  have hwc := continuous_of_forall_intervalIntegral hwg
  have hφc : Continuous fun s : ℝ ↦ α * |s| := continuous_const.mul continuous_abs
  -- everywhere versions of the constraints
  have hle' : ∀ s, w s ≤ α * |s| := by
    have hU : IsOpen {s | α * |s| < w s} := isOpen_lt hφc hwc
    have h0 : volume {s | α * |s| < w s} = 0 := by
      rw [← ae_iff.1 hle]; congr 1; ext s; simp
    rw [hU.measure_eq_zero_iff volume] at h0
    intro s; by_contra h
    have : s ∈ {s | α * |s| < w s} := not_le.1 h
    rw [h0] at this; exact this
  have hout' : ∀ s, s < a ∨ b < s → w s = α * |s| := by
    have hU : IsOpen ({s | s < a ∨ b < s} ∩ {s | w s ≠ α * |s|}) :=
      ((isOpen_lt continuous_id continuous_const).union
        (isOpen_lt continuous_const continuous_id)).inter (isOpen_ne_fun hwc hφc)
    have h0 : volume ({s | s < a ∨ b < s} ∩ {s | w s ≠ α * |s|}) = 0 := by
      refine measure_mono_null (fun s hs ↦ ?_) (ae_iff.1 hout)
      simp only [mem_inter_iff, Set.mem_ofPred_eq] at hs ⊢
      exact fun h ↦ hs.2 (h fun hm ↦ by rcases hs.1 with h1 | h1 <;> linarith [hm.1, hm.2])
    rw [hU.measure_eq_zero_iff volume] at h0
    intro s hs; by_contra h
    have : s ∈ {s | s < a ∨ b < s} ∩ {s | w s ≠ α * |s|} := ⟨hs, h⟩
    rw [h0] at this; exact this
  have hclosed : IsClosed {s | w s = α * |s|} := isClosed_eq hwc hφc
  have hwa : w a = α * |a| := by
    have : Iio a ⊆ {s | w s = α * |s|} := fun s hs ↦ hout' s (Or.inl hs)
    have := hclosed.closure_subset_iff.2 this
    rw [closure_Iio] at this
    exact this (le_refl a)
  have hwb : w b = α * |b| := by
    have : Ioi b ⊆ {s | w s = α * |s|} := fun s hs ↦ hout' s (Or.inr hs)
    have := hclosed.closure_subset_iff.2 this
    rw [closure_Ioi] at this
    exact this (le_refl b)
  -- reflected data
  set w' : ℝ → ℝ := fun s ↦ w (-s) with hw'
  set g' : ℝ → ℝ := fun s ↦ -g (-s) with hg'
  have hwg' : ∀ a b, IntervalIntegrable g' volume a b ∧ w' b - w' a = ∫ s in a..b, g' s :=
    forall_intervalIntegral_comp_neg hwg
  set F : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (g s ^ 2 + q ^ 2 * {s | 0 < w s}.indicator 1 s)
    with hFdef
  have hF' : ∀ s, ENNReal.ofReal (g' s ^ 2 + q ^ 2 * {s | 0 < w' s}.indicator 1 s) = F (-s) := by
    intro s
    simp only [hFdef, hg', hw', neg_sq]
    congr 2
  have refl : ∀ c T, 0 ≤ c → c ≤ T → (w' c ≤ 0 ∨ w' c = α * c) → w' T = α * T →
      ENNReal.ofReal ((α ^ 2 + q ^ 2) * (T - c)) ≤ ∫⁻ s in Ioo (-T) (-c), F s := by
    intro c T hc hcT hc' hT
    have := oneDim_core hq hqα hc hcT hwg' hT hc'
    simp_rw [hF'] at this
    rwa [setLIntegral_Ioo_comp_neg] at this
  rcases le_or_gt 0 a with ha | ha
  · -- `0 ≤ a`
    exact oneDim_core hq hqα ha hab hwg (by rw [hwb, abs_of_nonneg (ha.trans hab)])
      (Or.inr (by rw [hwa, abs_of_nonneg ha]))
  rcases le_or_gt b 0 with hb | hb
  · -- `b ≤ 0`
    have := refl (-b) (-a) (neg_nonneg.2 hb) (neg_le_neg hab)
      (Or.inr (by simp only [hw', neg_neg]; rw [hwb, abs_of_nonpos hb]))
      (by simp only [hw', neg_neg]; rw [hwa, abs_of_neg ha])
    simpa [neg_neg, sub_neg_eq_add, add_comm, sub_eq_add_neg] using this
  · -- `a < 0 < b`: split at `0`
    have h0 : w 0 ≤ 0 := by simpa using hle' 0
    have hR : ENNReal.ofReal ((α ^ 2 + q ^ 2) * (b - 0)) ≤ ∫⁻ s in Ioo 0 b, F s :=
      oneDim_core hq hqα le_rfl hb.le hwg (by rw [hwb, abs_of_pos hb]) (Or.inl h0)
    have hL := refl 0 (-a) le_rfl (neg_nonneg.2 ha.le) (Or.inl (by simpa [hw'] using h0))
      (by simp only [hw', neg_neg]; rw [hwa, abs_of_neg ha])
    simp only [neg_neg, neg_zero] at hL
    have hdisj : Disjoint (Ioo a 0) (Ioo 0 b) :=
      Set.disjoint_left.2 fun s h1 h2 ↦ by linarith [h1.2, h2.1]
    calc ENNReal.ofReal ((α ^ 2 + q ^ 2) * (b - a))
        = ENNReal.ofReal ((α ^ 2 + q ^ 2) * (-a - 0)) +
            ENNReal.ofReal ((α ^ 2 + q ^ 2) * (b - 0)) := by
          rw [← ENNReal.ofReal_add (by nlinarith [sq_nonneg α, sq_nonneg q])
            (by nlinarith [sq_nonneg α, sq_nonneg q])]
          congr 1; ring
      _ ≤ (∫⁻ s in Ioo a 0, F s) + ∫⁻ s in Ioo 0 b, F s := add_le_add hL hR
      _ = ∫⁻ s in Ioo a 0 ∪ Ioo 0 b, F s := by rw [lintegral_union measurableSet_Ioo hdisj]
      _ ≤ ∫⁻ s in Ioo a b, F s := lintegral_mono_set
          (union_subset (Ioo_subset_Ioo_right hb.le) (Ioo_subset_Ioo_left ha.le))

end OneDim

/-! ### The ACL property along `e` (for Step 3) -/

section OneDimWeak

/-! Weak derivatives on the line. The `L¹` mollification lemmas are those of gmt-foundations v0.1.0
(`GMTFoundations/Sobolev/Mollify.lean`), which hold on `ℝ` as well as on `E d`. -/

/-- One-dimensional mollifiers `ρ_k`, supported in `[-1/(k+1), 1/(k+1)]`. -/
noncomputable def bumpR (k : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (2 * ((k : ℝ) + 1)), 1 / ((k : ℝ) + 1), by positivity, by
    rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]; linarith⟩

theorem bumpR_rOut (k : ℕ) : (bumpR k).rOut = 1 / ((k : ℝ) + 1) := rfl

theorem tendsto_bumpR_rOut : Tendsto (fun k ↦ (bumpR k).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem bumpR_rOut_le (k : ℕ) : (bumpR k).rOut ≤ 2 * (bumpR k).rIn := by
  simp only [bumpR]
  rw [mul_one_div, ← div_div, div_self two_ne_zero]

theorem bumpR_rOut_le_one (k : ℕ) : (bumpR k).rOut ≤ 1 := by
  rw [bumpR_rOut, div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Mollifications converge in `L¹` (`GMTFoundations.tendsto_integral_norm_normed_convolution_sub`
on `ℝ`). -/
theorem tendsto_integral_norm_bumpR_convolution_sub {k : ℝ → ℝ} (hk : Integrable k) :
    Tendsto
      (fun n ↦ ∫ x, ‖((bumpR n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x - k x‖)
      atTop (𝓝 0) :=
  GMTFoundations.tendsto_integral_norm_normed_convolution_sub tendsto_bumpR_rOut hk

/-- The test functions `s ↦ ρ_k(a - s)`. -/
noncomputable def testR (k : ℕ) (a : ℝ) (s : ℝ) : ℝ := (bumpR k).normed volume (a - s)

theorem contDiff_testR (k : ℕ) (a : ℝ) : ContDiff ℝ ∞ (testR k a) :=
  (bumpR k).contDiff_normed.comp (contDiff_const.sub contDiff_id)

theorem hasCompactSupport_testR (k : ℕ) (a : ℝ) : HasCompactSupport (testR k a) := by
  have h := (bumpR k).hasCompactSupport_normed (μ := volume)
  have : testR k a = (bumpR k).normed volume ∘ (Homeomorph.subLeft a) := rfl
  rw [this]
  exact h.comp_homeomorph _

/-- **Weak derivatives in one dimension.** If `h, g ∈ L¹_loc(ℝ)` and `∫ h χ' = -∫ g χ` for the
countable family of test functions `χ = ρ_k(a - ·)`, `k ∈ ℕ`, `a ∈ ℚ`, then `h` agrees a.e. with a
primitive of `g`. -/
theorem exists_primitive_of_weakDeriv {h g : ℝ → ℝ} (hh : LocallyIntegrable h)
    (hg : LocallyIntegrable g)
    (H : ∀ (k : ℕ) (a : ℚ), ∫ s, h s * deriv (testR k a) s = -∫ s, g s * testR k a s) :
    ∃ w : ℝ → ℝ, (∀ᵐ s, w s = h s) ∧
      ∀ a c, IntervalIntegrable g volume a c ∧ w c - w a = ∫ s in a..c, g s := by
  set ρ : ℕ → ℝ → ℝ := fun k ↦ (bumpR k).normed volume with hρ
  have hgI : ∀ a c, IntervalIntegrable g volume a c := fun a c ↦
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hρc : ∀ k, ContDiff ℝ ∞ (ρ k) := fun k ↦ (bumpR k).contDiff_normed
  have hρs : ∀ k, HasCompactSupport (ρ k) := fun k ↦ (bumpR k).hasCompactSupport_normed
  set M : ℕ → ℝ → ℝ := fun k ↦ ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h with hM
  set N : ℕ → ℝ → ℝ := fun k ↦ ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g with hN
  set P : ℕ → ℝ → ℝ := fun k ↦ deriv (ρ k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h with hP
  have hPN_rat : ∀ k (a : ℚ), P k a = N k a := by
    intro k a
    have H' := H k a
    have hd : ∀ s, deriv (testR k a) s = -deriv (ρ k) (a - s) := fun s ↦
      deriv_comp_const_sub (ρ k) (a : ℝ) s
    simp only [hd, mul_neg, integral_neg, neg_inj] at H'
    simp only [hP, hN, convolution_eq_swap, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    simp only [testR] at H'
    rw [show (fun t ↦ deriv (ρ k) ((a : ℝ) - t) * h t) = fun t ↦ h t * deriv (ρ k) (a - t) from
      funext fun t ↦ mul_comm _ _, H']
    congr 1; funext t; exact mul_comm _ _
  have hPc : ∀ k, Continuous (P k) := fun k ↦
    (hρs k).deriv.continuous_convolution_left _ ((hρc k).continuous_deriv (by simp)) hh
  have hNc : ∀ k, Continuous (N k) := fun k ↦
    (hρs k).continuous_convolution_left _ (hρc k).continuous hg
  have hPN : ∀ k, P k = N k := fun k ↦
    (hPc k).ext_on Rat.denseRange_cast (hNc k) fun x ⟨q, hq⟩ ↦ hq ▸ hPN_rat k q
  have hMd : ∀ k x, HasDerivAt (M k) (N k x) x := by
    intro k x
    have := (hρs k).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hρc k).of_le (by simp)) hh x
    rw [← hPN k]; exact this
  have hFTC : ∀ k a c, M k c - M k a = ∫ x in a..c, N k x := fun k a c ↦
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hMd k x)
      ((hNc k).intervalIntegrable a c)).symm
  -- convergence of `∫ N_k`
  have hNlim : ∀ a c, Tendsto (fun k ↦ ∫ x in a..c, N k x) atTop (𝓝 (∫ x in a..c, g x)) := by
    intro a c
    set m := min a c - 1
    set m' := max a c + 1
    set gh : ℝ → ℝ := (Icc m m').indicator g with hgh
    have hgi : Integrable gh :=
      (hg.integrableOn_isCompact isCompact_Icc).integrable_indicator measurableSet_Icc
    have hNeq : ∀ k, ∀ x ∈ uIcc a c,
        N k x = (ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] gh) x := by
      intro k x hx
      simp only [hN, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      congr 1; funext t
      by_cases ht : ρ k t = 0
      · simp [ht]
      · have ht' : t ∈ ball (0 : ℝ) (bumpR k).rOut := by
          rw [← (bumpR k).support_normed_eq (μ := volume)]; exact ht
        rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht'
        have ht1 : |t| < 1 := ht'.trans_le (bumpR_rOut_le_one k)
        rw [abs_lt] at ht1
        have hmem : x - t ∈ Icc m m' := by
          rw [mem_uIcc] at hx
          constructor
          · rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [m] <;>
              linarith [min_le_left a c, min_le_right a c]
          · rcases hx with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp only [m'] <;>
              linarith [le_max_left a c, le_max_right a c]
        rw [hgh, indicator_of_mem hmem]
    have hgeq : ∫ x in a..c, g x = ∫ x in a..c, gh x := by
      refine intervalIntegral.integral_congr fun x hx ↦ ?_
      have hmem : x ∈ Icc m m' := by
        rw [mem_uIcc] at hx
        constructor
        · rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [m] <;>
            linarith [min_le_left a c, min_le_right a c]
        · rcases hx with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp only [m'] <;>
            linarith [le_max_left a c, le_max_right a c]
      simp [hgh, indicator_of_mem hmem]
    have hlim := tendsto_integral_norm_bumpR_convolution_sub hgi
    rw [hgeq]
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun k ↦ ?_) hlim)
    have hci : Integrable (ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] gh) :=
      (bumpR k).integrable_normed.integrable_convolution _ hgi
    rw [intervalIntegral.integral_congr (hNeq k), ← intervalIntegral.integral_sub
      (hci.intervalIntegrable) hgi.intervalIntegrable]
    refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
    exact setIntegral_le_integral (hci.sub hgi).norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
  -- a.e. convergence of `M_k`
  have hMlim : ∀ᵐ x, Tendsto (fun k ↦ M k x) atTop (𝓝 (h x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable tendsto_bumpR_rOut
      (Eventually.of_forall bumpR_rOut_le) hh
  obtain ⟨a₀, ha₀⟩ := hMlim.exists
  refine ⟨fun c ↦ h a₀ + ∫ s in a₀..c, g s, ?_, fun a c ↦ ⟨hgI a c, ?_⟩⟩
  · filter_upwards [hMlim] with c hc
    have h1 : Tendsto (fun k ↦ M k c - M k a₀) atTop (𝓝 (h c - h a₀)) := hc.sub ha₀
    have h2 : Tendsto (fun k ↦ M k c - M k a₀) atTop (𝓝 (∫ s in a₀..c, g s)) := by
      simp_rw [hFTC]; exact hNlim a₀ c
    have := tendsto_nhds_unique h1 h2
    linarith
  · simp only
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      (hgI _ _) (hgI _ _)]

end OneDimWeak

end PerronVariational

end
