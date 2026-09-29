/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Statements.Intermediate
public import PerronVariational.Registry.Semilinear
public import PerronVariational.Semilinear.WellPrepared
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Registry.FunctionalAnalysis
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.NullLevelSet

/-!
# Well-prepared data for the semilinear problem (Proposition 3.8(i), (i'))

The properties of the regularized data `g_ε` used in the proof of Proposition 3.8 of F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the
Bernoulli one-phase problem*, arXiv:2609.14981, collected in the structure `IsWellPreparedData`,
and the existence statement `exists_isWellPreparedData`, obtained from Lemma A.4
(`exists_wellPrepared_sub`, `exists_wellPrepared_super` in `WellPrepared.lean`) with
`g_ε = (Φ_{ε,θ}(g))₊`, resp. `g_ε = Ψ_{ε,θ̂}(g)`.

The fields are items (i)–(iv) of Lemma A.4, the `H¹` statements (i') of the formal
Proposition 3.8, and `le_of_nonpos`: there is `μ ∈ (0, 1)` with `g_ε ≤ (1 - μ) ε` on
`{g ≤ 0}`, the hypothesis of Lemma A.11 on that region
(`μ = (1 - Φ_{1,θ}(0)₊)/2`, resp. `μ = (1 - Ψ_{1,θ̂}(0))/2`).

Item (i') (`g_ε ∈ H¹(U)` and `g_ε → g₊` in `H¹(U)`) is not in the paper's Proposition 3.8. The
paper's proof of Theorem 3.9 applies Proposition 4.1, which assumes `g_ε → g₊` in `H¹`, but only
checks `L²` convergence; here the `H¹` convergence is added to the statement and proved.

## Main results

* `memH1_gradient_of_lipschitzOnWith`: a Lipschitz function on `Ū` with bounded gradient is in
  `H¹(U)` with weak gradient its pointwise gradient (for Lipschitz functions the a.e. gradient
  is the weak gradient, from gmt-foundations v0.1.0).
* `memH1_max_zero`: `g₊ ∈ H¹(U)` with weak gradient `1_{g > 0} ∇g` for `g ∈ C¹` (the pointwise
  gradient of `g₊` is `1_{g > 0} ∇g` *everywhere*, with the convention `∇f = 0` at points of
  non-differentiability).
* `tendsto_H1_of_isWellPreparedSub`, `tendsto_H1_of_isWellPreparedSuper`: `g_ε → g₊` in
  `H¹(U)`, by dominated convergence, using that regular level sets are null
  (`measure_zero_levelSet_gradient_ne_zero`).
* `exists_isWellPreparedData`.
-/

open Set Filter Topology MeasureTheory
open scoped Gradient

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- Properties of the well-prepared data `gε ε`, `0 < ε < ε₀`, of Lemma A.4 for a smooth strict
subsolution (`increasing = true`) or supersolution (`increasing = false`) `g`; see the module
docstring. -/
structure IsWellPreparedData (S : Setting d) (g : E d → ℝ) (β : ℝ → ℝ) (increasing : Bool)
    (ε₀ : ℝ) (gε : ℝ → E d → ℝ) : Prop where
  pos : 0 < ε₀
  /-- A.4(i): Lipschitz constants of `g` on `Ū` are Lipschitz constants of `g_ε`. -/
  lipschitz : ∀ ε ∈ Ioo 0 ε₀, ∀ K, LipschitzOnWith K g (closure S.U) →
    LipschitzOnWith K (gε ε) (closure S.U)
  /-- A.4(ii): `g₊ ≤ g_ε ≤ g₊ + ε` on `Ū`. -/
  bounds : ∀ ε ∈ Ioo 0 ε₀, ∀ x ∈ closure S.U, max (g x) 0 ≤ gε ε x ∧ gε ε x ≤ max (g x) 0 + ε
  /-- A.4(i), pointwise form: `|∇g_ε| ≤ |∇g|` in `U`. -/
  norm_gradient_le : ∀ ε ∈ Ioo 0 ε₀, ∀ x ∈ S.U, ‖∇ (gε ε) x‖ ≤ ‖∇ g x‖
  /-- `g_ε ∈ H¹(U)` with weak gradient the pointwise gradient (part of (i')). -/
  memH1 : ∀ ε ∈ Ioo 0 ε₀, MemH1 S.U (gε ε) (∇ (gε ε))
  /-- A.4(iv): `J(g_ε, χ⁰_ε; U) ≤ E₀` with `χ⁰_ε = 2 𝓑_ε(g_ε)`. -/
  energy_le : ∀ ε ∈ Ioo 0 ε₀,
    energyJχ S.U S.Q (∇ (gε ε)) (fun x ↦ 2 * bigBEps β ε (gε ε x)) ≤ energyBound S (∇ g)
  /-- A.4(iii): `g_ε` is a stationary viscosity subsolution (resp. supersolution) of
  `Δv = Q² β_ε(v)` in `U`. -/
  visc : ∀ ε ∈ Ioo 0 ε₀, if increasing then IsSemilinearViscSubStat S.U S.Q β ε (gε ε)
    else IsSemilinearViscSuperStat S.U S.Q β ε (gε ε)
  /-- `g_ε ≤ (1 - μ) ε` on `{g ≤ 0}` (input of Lemma A.11). -/
  le_of_nonpos : ∃ μ ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo 0 ε₀, ∀ x ∈ closure S.U, g x ≤ 0 →
    gε ε x ≤ (1 - μ) * ε
  /-- Increasing case: `g_ε = 0` on `{g ≤ -c ε}` (Lemma A.4(v), `{g_ε > 0} ⊆ {g > -c_θ ε}`;
  input of Proposition 3.8(vi*)). -/
  eq_zero_of_le : increasing = true → ∃ c > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ x ∈ closure S.U,
    g x ≤ -(c * ε) → gε ε x = 0
  /-- (i'): `g₊ ∈ H¹(U)` with weak gradient `1_{g > 0} ∇g`. -/
  memH1_pos : MemH1 S.U (fun x ↦ max (g x) 0) ({x | 0 < g x}.indicator (∇ g))
  /-- (i'): `g_ε → g₊` in `H¹(U)` as `ε → 0⁺`. -/
  tendsto_H1 : Tendsto (fun ε ↦ eLpNorm (fun x ↦ gε ε x - max (g x) 0) 2 (volume.restrict S.U) +
      eLpNorm (fun x ↦ ∇ (gε ε) x - {x | 0 < g x}.indicator (∇ g) x) 2 (volume.restrict S.U))
    (𝓝[>] 0) (𝓝 0)

/-- A `C¹` function on `ℝᵈ` is Lipschitz on the closure of a bounded set. -/
theorem exists_lipschitzOnWith_closure {f : E d → ℝ} (hf : ContDiff ℝ 1 f) {U : Set (E d)}
    (hU : Bornology.IsBounded U) : ∃ K, LipschitzOnWith K f (closure U) :=
  (hf.locallyLipschitz.locallyLipschitzOn).exists_lipschitzOnWith_of_compact
    hU.isCompact_closure

/-! ### Sobolev membership -/

section Sobolev

variable {S : Setting d}

instance Setting.isFiniteMeasure_restrict (S : Setting d) :
    IsFiniteMeasure (volume.restrict S.U) :=
  MeasureTheory.isFiniteMeasure_restrict.2 S.isBounded.measure_lt_top.ne

/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient_of_contDiff {f : E d → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (∇ f) := by
  have : ∇ f = fun x ↦ (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

/-- The gradient of any function is measurable. -/
theorem measurable_gradient (f : E d → ℝ) : Measurable (∇ f) := by
  have : ∇ f = fun x ↦ (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

/-- The gradient of a `C¹` function is bounded on `Ū`. -/
theorem exists_norm_gradient_le {f : E d → ℝ} (hf : ContDiff ℝ 1 f) (S : Setting d) :
    ∃ L, ∀ x ∈ closure S.U, ‖∇ f x‖ ≤ L :=
  S.isBounded.isCompact_closure.exists_bound_of_continuousOn
    (continuous_gradient_of_contDiff hf).continuousOn

/-- A function Lipschitz on `Ū` with bounded pointwise gradient on `U` belongs to `H¹(U)`, with
weak gradient its pointwise gradient (via `Registry.memH1Loc_gradient_of_locallyLipschitzOn`,
from gmt-foundations v0.1.0). -/
theorem memH1_gradient_of_lipschitzOnWith {f : E d → ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f (closure S.U)) {C : ℝ} (hC : ∀ x ∈ S.U, ‖∇ f x‖ ≤ C) :
    MemH1 S.U f (∇ f) := by
  have hloc : LocallyLipschitzOn S.U f := fun _ _ ↦
    ⟨K, S.U, self_mem_nhdsWithin, hf.mono subset_closure⟩
  obtain ⟨M, hM⟩ := S.isBounded.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨MemLp.of_bound ((hf.continuousOn.mono subset_closure).aestronglyMeasurable
    S.isOpen.measurableSet) M ?_, MemLp.of_bound (measurable_gradient f).aestronglyMeasurable C ?_,
    (Registry.memH1Loc_gradient_of_locallyLipschitzOn S.isOpen hloc).1⟩
  · exact ae_restrict_of_forall_mem S.isOpen.measurableSet fun x hx ↦ hM x (subset_closure hx)
  · exact ae_restrict_of_forall_mem S.isOpen.measurableSet hC

/-- The pointwise gradient of `g₊` is `1_{g > 0} ∇g` everywhere, for continuous `g` (with
the convention `∇f(x) = 0` where `f` is not differentiable). -/
theorem gradient_max_zero {g : E d → ℝ} (hg : Continuous g) (x : E d) :
    ∇ (fun y ↦ max (g y) 0) x = {y | 0 < g y}.indicator (∇ g) x := by
  rcases lt_trichotomy (g x) 0 with hx | hx | hx
  · have hev : (fun y ↦ max (g y) 0) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hg.continuousAt.eventually (gt_mem_nhds hx)] with y hy
      exact max_eq_right hy.le
    rw [indicator_of_notMem (by simpa using hx.le), gradient, hev.fderiv_eq]
    simp
  · rw [indicator_of_notMem (by simp [hx])]
    by_cases hd : DifferentiableAt ℝ (fun y ↦ max (g y) 0) x
    · have hmin : IsLocalMin (fun y ↦ max (g y) 0) x :=
        Filter.Eventually.of_forall fun y ↦ by simp [hx]
      rw [gradient, hmin.fderiv_eq_zero]; simp
    · rw [gradient, fderiv_zero_of_not_differentiableAt hd]; simp
  · have hev : (fun y ↦ max (g y) 0) =ᶠ[𝓝 x] g := by
      filter_upwards [hg.continuousAt.eventually (lt_mem_nhds hx)] with y hy
      exact max_eq_left hy.le
    rw [indicator_of_mem (by simpa using hx), gradient, hev.fderiv_eq]
    rfl

/-- `g₊ ∈ H¹(U)` with weak gradient `1_{g > 0} ∇g`, for `g ∈ C¹(ℝᵈ)` (item (i') of the formal
Proposition 3.8). -/
theorem memH1_max_zero {g : E d → ℝ} (hg : ContDiff ℝ 1 g) :
    MemH1 S.U (fun x ↦ max (g x) 0) ({x | 0 < g x}.indicator (∇ g)) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_closure hg S.isBounded
  have hK' : LipschitzOnWith K (fun x ↦ max (g x) 0) (closure S.U) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ (by
      simpa [Real.dist_eq] using (abs_max_sub_max_le_abs (g x) (g y) 0).trans
        (by simpa [Real.dist_eq] using hK.dist_le_mul x hx y hy))
  obtain ⟨L, hL⟩ := exists_norm_gradient_le hg S
  have hgrad : ∇ (fun y ↦ max (g y) 0) = {x | 0 < g x}.indicator (∇ g) :=
    funext (gradient_max_zero hg.continuous)
  rw [← hgrad]
  refine memH1_gradient_of_lipschitzOnWith hK' (C := L) fun x hx ↦ ?_
  rw [hgrad]
  by_cases h : 0 < g x
  · rw [indicator_of_mem (show x ∈ {x | 0 < g x} from h)]; exact hL x (subset_closure hx)
  · rw [indicator_of_notMem (show x ∉ {x | 0 < g x} from h), norm_zero]
    exact (norm_nonneg _).trans (hL x (subset_closure hx))

end Sobolev

/-! ### `H¹` convergence of the data (item (i')) -/

/-- Dominated convergence in `L²` for a uniformly bounded family on a finite measure space. -/
theorem tendsto_eLpNorm_two_of_bound {X Y : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [NormedAddCommGroup Y] {l : Filter ℝ} [l.IsCountablyGenerated]
    {f : ℝ → X → Y} (C : ℝ) (hmeas : ∀ᶠ ε in l, AEStronglyMeasurable (f ε) μ)
    (hbd : ∀ᶠ ε in l, ∀ᵐ x ∂μ, ‖f ε x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun ε ↦ ‖f ε x‖) l (𝓝 0)) :
    Tendsto (fun ε ↦ eLpNorm (f ε) 2 μ) l (𝓝 0) := by
  have hfin : ∫⁻ _ : X, ENNReal.ofReal C ^ (2 : ℝ) ∂μ ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      (measure_ne_top μ _)
  have hlim' : ∀ᵐ x ∂μ, Tendsto (fun ε ↦ ‖f ε x‖ₑ ^ (2 : ℝ)) l (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have h1 : Tendsto (fun ε ↦ ENNReal.ofReal ‖f ε x‖) l (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hx
    have h2 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h1
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr fun ε ↦ ?_
    simp [ofReal_norm]
  have key : Tendsto (fun ε ↦ ∫⁻ x, ‖f ε x‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ)
      (F := fun ε x ↦ ‖f ε x‖ₑ ^ (2 : ℝ)) (f := fun _ ↦ 0)
      (fun _ ↦ ENNReal.ofReal C ^ (2 : ℝ))
      (hmeas.mono fun ε h ↦ h.enorm.pow_const _)
      (hbd.mono fun ε h ↦ h.mono fun x hx ↦ by
        simp only
        rw [← ofReal_norm]
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx) (by norm_num))
      hfin hlim'
    simpa using this
  have h3 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp key
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
  refine h3.congr fun ε ↦ ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp

/-- The `L²` part of (i'): `|g_ε - g₊| ≤ ε` gives `g_ε → g₊` in `L²(U)`. -/
private theorem tendsto_eLpNorm_sub_max (S : Setting d) {g : E d → ℝ} (hg : ContDiff ℝ 1 g)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) {gε : ℝ → E d → ℝ}
    (hlip : ∀ ε ∈ Ioc 0 ε₀, ∀ K, LipschitzOnWith K g (closure S.U) →
      LipschitzOnWith K (gε ε) (closure S.U))
    (hbd : ∀ ε ∈ Ioc 0 ε₀, ∀ x, max (g x) 0 ≤ gε ε x ∧ gε ε x ≤ max (g x) 0 + ε) :
    Tendsto (fun ε ↦ eLpNorm (fun x ↦ gε ε x - max (g x) 0) 2 (volume.restrict S.U))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_closure hg S.isBounded
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioc 0 ε₀ := Ioc_mem_nhdsGT hε₀
  have hle : ∀ ε ∈ Ioc 0 ε₀, ∀ x, ‖gε ε x - max (g x) 0‖ ≤ ε := fun ε hε x ↦ by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hbd ε hε x]
  refine tendsto_eLpNorm_two_of_bound ε₀ (hev.mono fun ε hε ↦ ?_)
    (hev.mono fun ε hε ↦ Eventually.of_forall fun x ↦ (hle ε hε x).trans hε.2) ?_
  · exact (((hlip ε hε K hK).continuousOn.mono subset_closure).sub
      (hg.continuous.max continuous_const).continuousOn).aestronglyMeasurable
      S.isOpen.measurableSet
  · refine Eventually.of_forall fun x ↦ squeeze_zero' (Eventually.of_forall fun _ ↦
      norm_nonneg _) (hev.mono fun ε hε ↦ hle ε hε x) ?_
    exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

/-- The gradient part of (i'), generic form: if `∇g_ε(x) → 1_{g>0}∇g(x)` for a.e. `x ∈ U` and
`|∇g_ε| ≤ |∇g|` on `U`, then `∇g_ε → 1_{g>0}∇g` in `L²(U)`. -/
private theorem tendsto_eLpNorm_gradient (S : Setting d) {g : E d → ℝ} (hg : ContDiff ℝ 1 g)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) {gε : ℝ → E d → ℝ}
    (hgrad : ∀ ε ∈ Ioc 0 ε₀, ∀ x, ‖∇ (gε ε) x‖ ≤ ‖∇ g x‖)
    (hlim : ∀ᵐ x ∂(volume.restrict S.U),
      Tendsto (fun ε ↦ ‖∇ (gε ε) x - {x | 0 < g x}.indicator (∇ g) x‖) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε ↦ eLpNorm (fun x ↦ ∇ (gε ε) x - {x | 0 < g x}.indicator (∇ g) x) 2
      (volume.restrict S.U)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L, hL⟩ := exists_norm_gradient_le hg S
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioc 0 ε₀ := Ioc_mem_nhdsGT hε₀
  have hmeasI : Measurable ({x | 0 < g x}.indicator (∇ g)) :=
    (measurable_gradient g).indicator (measurableSet_lt measurable_const hg.continuous.measurable)
  refine tendsto_eLpNorm_two_of_bound (2 * L) (Eventually.of_forall fun ε ↦
    ((measurable_gradient _).sub hmeasI).aestronglyMeasurable) (hev.mono fun ε hε ↦ ?_) hlim
  refine ae_restrict_of_forall_mem S.isOpen.measurableSet fun x hx ↦ ?_
  have h1 := hgrad ε hε x
  have h2 := hL x (subset_closure hx)
  have h3 : ‖{x | 0 < g x}.indicator (∇ g) x‖ ≤ ‖∇ g x‖ := by
    by_cases h : 0 < g x
    · rw [indicator_of_mem (show x ∈ {x | 0 < g x} from h)]
    · rw [indicator_of_notMem (show x ∉ {x | 0 < g x} from h), norm_zero]; exact norm_nonneg _
  linarith [norm_sub_le (∇ (gε ε) x) ({x | 0 < g x}.indicator (∇ g) x)]

/-- A.e. in `U`, either `g ≠ 0` or `∇g = 0` (regular level sets are null). -/
private theorem ae_ne_zero_or_gradient_eq_zero (S : Setting d) {g : E d → ℝ}
    (hg : ContDiff ℝ 1 g) :
    ∀ᵐ x ∂(volume.restrict S.U), x ∈ S.U ∧ (g x ≠ 0 ∨ ∇ g x = 0) := by
  have hnull := measure_zero_levelSet_gradient_ne_zero (volume : Measure (E d)) g
  have h1 : ∀ᵐ x ∂(volume : Measure (E d)), g x ≠ 0 ∨ ∇ g x = 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx ↦ ?_) hnull
    simp only [mem_setOf_eq, not_or, not_not] at hx
    exact ⟨hx.1, (hg.differentiable one_ne_zero) x, hx.2⟩
  filter_upwards [ae_restrict_mem S.isOpen.measurableSet, ae_restrict_of_ae h1] with x hx h
  exact ⟨hx, h⟩

/-- Where `g > 0`, the data eventually agree with `g` near `x`. -/
private theorem tendsto_of_pos {g : E d → ℝ} (hg : Continuous g) {ε₀ : ℝ} {gε : ℝ → E d → ℝ}
    (heq : ∀ ε ∈ Ioc 0 ε₀, ∀ x, ε ≤ g x → gε ε x = g x) (hε₀ : 0 < ε₀) {x : E d}
    (hx : 0 < g x) :
    Tendsto (fun ε ↦ ‖∇ (gε ε) x - {x | 0 < g x}.indicator (∇ g) x‖) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hx hε₀)] with ε hε
  have hε' : ε ∈ Ioc 0 ε₀ := ⟨hε.1, hε.2.le.trans (min_le_right _ _)⟩
  have hev : gε ε =ᶠ[𝓝 x] g := by
    filter_upwards [hg.continuousAt.eventually (lt_mem_nhds
      (hε.2.trans_le (min_le_left _ _)))] with y hy
    exact heq ε hε' y hy.le
  rw [indicator_of_mem (show x ∈ {x | 0 < g x} from hx), gradient, gradient, hev.fderiv_eq]
  simp

/-- Where `g = 0 = ∇g`, the gradient bound forces `∇g_ε(x) = 0`. -/
private theorem tendsto_of_gradient_eq_zero {g : E d → ℝ} {ε₀ : ℝ} {gε : ℝ → E d → ℝ}
    (hgrad : ∀ ε ∈ Ioc 0 ε₀, ∀ x, ‖∇ (gε ε) x‖ ≤ ‖∇ g x‖) (hε₀ : 0 < ε₀) {x : E d}
    (hx : g x = 0) (hx' : ∇ g x = 0) :
    Tendsto (fun ε ↦ ‖∇ (gε ε) x - {x | 0 < g x}.indicator (∇ g) x‖) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hε₀] with ε hε
  have h := hgrad ε hε x
  rw [hx', norm_zero] at h
  rw [indicator_of_notMem (show x ∉ {x | 0 < g x} by simp [hx]), norm_le_zero_iff.1 h]
  simp

/-- Item (i') of the formal Proposition 3.8 in the subsolution case: for the data
`g_ε` of Lemma A.4 (`IsWellPreparedSub`), `g_ε → g₊` in `H¹(U)` as `ε → 0⁺`.
Proof: `|g_ε - g₊| ≤ ε`; a.e. pointwise convergence of `∇g_ε` (`g_ε = g` near `{g > ε}`,
`g_ε = 0` near `{g < -c_θ ε}`, and on `{g = 0}` either `∇g = 0` or the point lies in a null set);
dominated convergence with `|∇g_ε| ≤ |∇g|`. -/
theorem tendsto_H1_of_isWellPreparedSub (S : Setting d) {β : ℝ → ℝ} {g : E d → ℝ}
    (hg : ContDiff ℝ 1 g) {ε₀ s₀ cθ : ℝ} (hε₀ : 0 < ε₀) {gε : ℝ → E d → ℝ}
    (hW : ∀ ε ∈ Ioc 0 ε₀, IsWellPreparedSub S.U S.Q β ε S.Qmax g (gε ε) s₀ cθ) :
    Tendsto (fun ε ↦ eLpNorm (fun x ↦ gε ε x - max (g x) 0) 2 (volume.restrict S.U) +
      eLpNorm (fun x ↦ ∇ (gε ε) x - {x | 0 < g x}.indicator (∇ g) x) 2 (volume.restrict S.U))
      (𝓝[>] 0) (𝓝 0) := by
  have hgrad : ∀ ε ∈ Ioc 0 ε₀, ∀ x, ‖∇ (gε ε) x‖ ≤ ‖∇ g x‖ := fun ε hε ↦
    (hW ε hε).norm_gradient_le
  have hA := tendsto_eLpNorm_sub_max S hg hε₀ (fun ε hε ↦ (hW ε hε).lipschitz)
    (fun ε hε ↦ (hW ε hε).bounds)
  have hB := tendsto_eLpNorm_gradient S hg hε₀ hgrad ?_
  · simpa using hA.add hB
  obtain ⟨hc0, -⟩ := (hW ε₀ ⟨hε₀, le_rfl⟩).s₀_mem
  filter_upwards [ae_ne_zero_or_gradient_eq_zero S hg] with x hx'
  obtain ⟨-, hx⟩ := hx'
  rcases lt_trichotomy (g x) 0 with hneg | hzero | hpos
  · -- `g(x) < 0`: `g_ε = 0` near `x` once `(c_θ + 1) ε < -g(x)/2`
    have hcθ : 0 ≤ cθ := by linarith [(hW ε₀ ⟨hε₀, le_rfl⟩).s₀_mem.2]
    set δ := -g x / (2 * (cθ + 1)) with hδ
    have hδ0 : 0 < δ := div_pos (by linarith) (by positivity)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ0 hε₀)] with ε hε
    have hε' : ε ∈ Ioc 0 ε₀ := ⟨hε.1, hε.2.le.trans (min_le_right _ _)⟩
    have hεδ : (cθ + 1) * ε < -g x / 2 := by
      have := hε.2.trans_le (min_le_left _ _)
      rw [hδ, lt_div_iff₀ (by positivity)] at this
      linarith
    have hev : gε ε =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hg.continuous.continuousAt.eventually (gt_mem_nhds
        (show g x < g x / 2 by linarith))] with y hy
      have hs : ε * s₀ ≥ -(cθ * ε) := by nlinarith [(hW ε hε').s₀_mem.1, hε.1]
      have hnot : ¬ 0 < gε ε y := fun h ↦ by
        have := ((hW ε hε').pos_iff y).1 h
        linarith [hε.1]
      exact le_antisymm (not_lt.1 hnot) ((le_max_right _ _).trans ((hW ε hε').bounds y).1)
    rw [indicator_of_notMem (show x ∉ {x | 0 < g x} by simp [hneg.le]), gradient, hev.fderiv_eq]
    simp
  · exact tendsto_of_gradient_eq_zero hgrad hε₀ hzero (hx.resolve_left (not_not.2 hzero))
  · exact tendsto_of_pos hg.continuous (fun ε hε ↦ (hW ε hε).eq_of_le) hε₀ hpos

/-- Item (i') of the formal Proposition 3.8 in the supersolution case: for
`g_ε = Ψ_{ε,θ̂}(g)` with the properties of Lemma A.4 (`IsWellPreparedSuper`),
`g_ε → g₊` in `H¹(U)`. On `{g < 0}`, `|∇g_ε| = Ψ₁'(g/ε)|∇g| ≤ C e^{c g/ε}|∇g| → 0` (exponential
tail, Lemma A.3(iv)). (For strict supersolutions Definition 2.2 gives no lower bound on `|∇g|` on
`{g = 0}`, so the argument used for subsolutions does not apply there; the null-set argument
covers this.) -/
theorem tendsto_H1_of_isWellPreparedSuper (S : Setting d) {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) {g : E d → ℝ} (hg : ContDiff ℝ 1 g) {δ₀ ε₀ κ : ℝ}
    (hδ₀ : δ₀ ∈ Ioo (0 : ℝ) 1) (hε₀ : 0 < ε₀)
    (hW : ∀ ε ∈ Ioc 0 ε₀,
      IsWellPreparedSuper S.U S.Q β ε S.Qmax g (wellPreparedSuperData β δ₀ ε g) κ) :
    Tendsto (fun ε ↦
      eLpNorm (fun x ↦ wellPreparedSuperData β δ₀ ε g x - max (g x) 0) 2 (volume.restrict S.U) +
      eLpNorm (fun x ↦ ∇ (wellPreparedSuperData β δ₀ ε g) x - {x | 0 < g x}.indicator (∇ g) x) 2
        (volume.restrict S.U)) (𝓝[>] 0) (𝓝 0) := by
  have hgrad : ∀ ε ∈ Ioc 0 ε₀, ∀ x, ‖∇ (wellPreparedSuperData β δ₀ ε g) x‖ ≤ ‖∇ g x‖ :=
    fun ε hε ↦ (hW ε hε).norm_gradient_le
  have hA := tendsto_eLpNorm_sub_max S hg hε₀ (fun ε hε ↦ (hW ε hε).lipschitz)
    (fun ε hε ↦ (hW ε hε).bounds)
  have hB := tendsto_eLpNorm_gradient S hg hε₀ hgrad ?_
  · simpa using hA.add hB
  have hθh : 1 < 1 / (1 - δ₀) := by
    rw [lt_div_iff₀ (by linarith [hδ₀.2])]; linarith [hδ₀.1]
  obtain ⟨C, c, hc, -, -, htail⟩ := profileSuper_tail hβ hθh
  filter_upwards [ae_ne_zero_or_gradient_eq_zero S hg] with x hx'
  obtain ⟨-, hx⟩ := hx'
  rcases lt_trichotomy (g x) 0 with hneg | hzero | hpos
  · -- `g(x) < 0`: `|∇g_ε(x)| ≤ C e^{c g(x)/ε} |∇g(x)| → 0`
    rw [indicator_of_notMem (show x ∉ {x | 0 < g x} by simp [hneg.le])]
    simp only [sub_zero]
    have hbound : ∀ ε > 0, ‖∇ (wellPreparedSuperData β δ₀ ε g) x‖ ≤
        C * Real.exp (c * (g x / ε)) * ‖∇ g x‖ := by
      intro ε hε
      have hd : HasFDerivAt (wellPreparedSuperData β δ₀ ε g)
          (deriv (profileSuper β (1 / (1 - δ₀))) (g x / ε) • fderiv ℝ g x) x :=
        (profileSuperEps_hasDerivAt hβ hθh hε (g x)).comp_hasFDerivAt x
          ((hg.differentiable one_ne_zero) x).hasFDerivAt
      rw [norm_gradient_eq_norm_fderiv, hd.fderiv, norm_smul, norm_gradient_eq_norm_fderiv,
        Real.norm_eq_abs]
      have hmem := profileSuper_deriv_mem hβ hθh (g x / ε)
      rw [abs_of_pos hmem.1]
      exact mul_le_mul_of_nonneg_right
        (htail (g x / ε) (div_nonpos_of_nonpos_of_nonneg hneg.le hε.le)).2.1 (norm_nonneg _)
    have hlim : Tendsto (fun ε : ℝ ↦ C * Real.exp (c * (g x / ε)) * ‖∇ g x‖) (𝓝[>] 0)
        (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ ↦ c * g x * ε⁻¹) (𝓝[>] 0) atBot :=
        tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (by nlinarith)
      have h2 := Real.tendsto_exp_atBot.comp h1
      have h3 := (h2.const_mul C).mul_const ‖∇ g x‖
      simp only [mul_zero, zero_mul] at h3
      refine h3.congr fun ε ↦ ?_
      simp only [Function.comp_apply, div_eq_mul_inv, mul_assoc]
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun ε hε ↦ hbound ε hε) hlim
  · exact tendsto_of_gradient_eq_zero hgrad hε₀ hzero (hx.resolve_left (not_not.2 hzero))
  · exact tendsto_of_pos hg.continuous (fun ε hε ↦ (hW ε hε).eq_of_le) hε₀ hpos

/-! ### Existence of well-prepared data -/

/-- `Φ_{ε,θ}(s)₊ ≤ ε Φ_{1,θ}(0)₊` for `s ≤ 0`. -/
private theorem wellPreparedSubData_le {β : ℝ → ℝ} (hβ : IsReactionProfile β) {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) {ε : ℝ} (hε : 0 < ε) {g : E d → ℝ} {x : E d} (hx : g x ≤ 0) :
    wellPreparedSubData β δ₀ ε g x ≤ ε * max (profileSub β (1 / (1 + δ₀)) 0) 0 := by
  have hθ : 0 < 1 / (1 + δ₀) := by positivity
  have hθ1 : 1 / (1 + δ₀) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hmono := (profileSub_strictMono hβ hθ hθ1).monotone
    (show g x / ε ≤ 0 from div_nonpos_of_nonpos_of_nonneg hx hε.le)
  simp only [wellPreparedSubData, profileSubEps]
  rw [mul_max_of_nonneg _ _ hε.le, mul_zero]
  exact max_le_max (mul_le_mul_of_nonneg_left hmono hε.le) le_rfl

/-- **Lemma A.4** in the form used for Proposition 3.8(i),
(i'): for a reaction profile `β` and a smooth strict subsolution `g` (`increasing = true`), resp.
supersolution (`increasing = false`), there are `ε₀ > 0` and data `gε` with the properties
`IsWellPreparedData`. -/
theorem exists_isWellPreparedData (S : Setting d) {g : E d → ℝ} {β : ℝ → ℝ}
    (hβ : IsReactionProfile β) (increasing : Bool)
    (hg : if increasing then IsStrictSub S.U S.Q g else IsStrictSuper S.U S.Q g) :
    ∃ (ε₀ : ℝ) (gε : ℝ → E d → ℝ), IsWellPreparedData S g β increasing ε₀ gε := by
  cases increasing with
  | true =>
    simp only [if_true] at hg
    have hg1 : ContDiff ℝ 1 g := hg.1.of_le (by norm_num)
    obtain ⟨L, hL⟩ := exists_norm_gradient_le hg1 S
    obtain ⟨Kg, hKg⟩ := exists_lipschitzOnWith_closure hg1 S.isBounded
    obtain ⟨δ₀, hδ₀, ε₀, hε₀, hW⟩ := exists_wellPrepared_sub hβ S hg
    have hW' : ∀ ε ∈ Ioo 0 ε₀, _ := fun ε (hε : ε ∈ Ioo 0 ε₀) ↦ hW ε ⟨hε.1, hε.2.le⟩
    have hθ : 0 < 1 / (1 + δ₀) := by positivity
    have hθ1 : 1 / (1 + δ₀) < 1 := by rw [div_lt_one (by positivity)]; linarith
    set m := max (profileSub β (1 / (1 + δ₀)) 0) 0 with hm
    have hm1 : m < 1 := by
      have := profileSub_strictMono hβ hθ hθ1 one_pos
      rw [profileSub_one hβ hθ hθ1] at this
      exact max_lt this one_pos
    have hm0 : 0 ≤ m := le_max_right _ _
    refine ⟨ε₀, fun ε ↦ wellPreparedSubData β δ₀ ε g,
      { pos := hε₀
        lipschitz := fun ε hε ↦ (hW' ε hε).lipschitz
        bounds := fun ε hε x _ ↦ (hW' ε hε).bounds x
        norm_gradient_le := fun ε hε x _ ↦ (hW' ε hε).norm_gradient_le x
        memH1 := fun ε hε ↦ memH1_gradient_of_lipschitzOnWith ((hW' ε hε).lipschitz Kg hKg)
          fun x hx ↦ ((hW' ε hε).norm_gradient_le x).trans (hL x (subset_closure hx))
        energy_le := fun ε hε ↦ (hW' ε hε).energy
        visc := fun ε hε ↦ by simpa using (hW' ε hε).viscSub
        le_of_nonpos := ⟨(1 - m) / 2, ⟨by linarith, by linarith⟩, fun ε hε x _ hx ↦
          (wellPreparedSubData_le hβ hδ₀ hε.1 hx).trans (by nlinarith [hε.1])⟩
        eq_zero_of_le := fun _ ↦ ⟨subConst (1 / (1 + δ₀)) + 1, by
          linarith [subConst_nonneg hθ hθ1], fun ε hε x _ hx ↦ by
          refine le_antisymm (not_lt.1 fun hpos ↦ ?_) ((le_max_right _ _).trans
            ((hW' ε hε).bounds x).1)
          have := (hW' ε hε).subset_pos x hpos
          linarith [hε.1]⟩
        memH1_pos := memH1_max_zero hg1
        tendsto_H1 := tendsto_H1_of_isWellPreparedSub S hg1 hε₀ hW }⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at hg
    have hg1 : ContDiff ℝ 1 g := hg.1.of_le (by norm_num)
    obtain ⟨L, hL⟩ := exists_norm_gradient_le hg1 S
    obtain ⟨Kg, hKg⟩ := exists_lipschitzOnWith_closure hg1 S.isBounded
    obtain ⟨δ₀, hδ₀, ε₀, hε₀, hW⟩ := exists_wellPrepared_super hβ S hg
    have hW' : ∀ ε ∈ Ioo 0 ε₀, _ := fun ε (hε : ε ∈ Ioo 0 ε₀) ↦ hW ε ⟨hε.1, hε.2.le⟩
    have hθh : 1 < 1 / (1 - δ₀) := by
      rw [lt_div_iff₀ (by linarith [hδ₀.2])]; linarith [hδ₀.1]
    set m := profileSuper β (1 / (1 - δ₀)) 0 with hm
    have hm1 : m < 1 := profileSuper_lt_one hβ hθh one_pos
    have hm0 : 0 < m := (superKappa_pos hβ hθh).trans (kappa_lt_profileSuper hβ hθh 0)
    refine ⟨ε₀, fun ε ↦ wellPreparedSuperData β δ₀ ε g,
      { pos := hε₀
        lipschitz := fun ε hε ↦ (hW' ε hε).lipschitz
        bounds := fun ε hε x _ ↦ (hW' ε hε).bounds x
        norm_gradient_le := fun ε hε x _ ↦ (hW' ε hε).norm_gradient_le x
        memH1 := fun ε hε ↦ memH1_gradient_of_lipschitzOnWith ((hW' ε hε).lipschitz Kg hKg)
          fun x hx ↦ ((hW' ε hε).norm_gradient_le x).trans (hL x (subset_closure hx))
        energy_le := fun ε hε ↦ (hW' ε hε).energy
        visc := fun ε hε ↦ by
          simpa using (⟨(hW' ε hε).classicalSuper.1.continuousOn, (hW' ε hε).viscSuper⟩ :
            IsSemilinearViscSuperStat S.U S.Q β ε (wellPreparedSuperData β δ₀ ε g))
        le_of_nonpos := ⟨(1 - m) / 2, ⟨by linarith, by linarith⟩, fun ε hε x _ hx ↦ by
          have hmono := (profileSuper_strictMono hβ hθh).monotone
            (show g x / ε ≤ 0 from div_nonpos_of_nonpos_of_nonneg hx hε.1.le)
          have : wellPreparedSuperData β δ₀ ε g x ≤ ε * m :=
            mul_le_mul_of_nonneg_left hmono hε.1.le
          nlinarith [hε.1]⟩
        eq_zero_of_le := fun h ↦ absurd h Bool.false_ne_true
        memH1_pos := memH1_max_zero hg1
        tendsto_H1 := tendsto_H1_of_isWellPreparedSuper S hβ hg1 hδ₀ hε₀ hW }⟩

namespace IsWellPreparedData

variable {S : Setting d} {g : E d → ℝ} {β : ℝ → ℝ} {increasing : Bool} {ε₀ : ℝ}
  {gε : ℝ → E d → ℝ}

/-- The data are Lipschitz on `Ū` with a constant independent of `ε`. -/
theorem exists_lipschitzOnWith (h : IsWellPreparedData S g β increasing ε₀ gε)
    (hg : ContDiff ℝ 1 g) :
    ∃ K, ∀ ε ∈ Ioo 0 ε₀, LipschitzOnWith K (gε ε) (closure S.U) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_closure hg S.isBounded
  exact ⟨K, fun ε hε ↦ h.lipschitz ε hε K hK⟩

/-- `g_ε ≥ 0` on `Ū`. -/
theorem nonneg (h : IsWellPreparedData S g β increasing ε₀ gε) {ε : ℝ} (hε : ε ∈ Ioo 0 ε₀)
    {x : E d} (hx : x ∈ closure S.U) : 0 ≤ gε ε x :=
  (le_max_right _ _).trans (h.bounds ε hε x hx).1

/-- Shrinking `ε₀` preserves well-preparedness. -/
theorem mono (h : IsWellPreparedData S g β increasing ε₀ gε) {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hle : ε₁ ≤ ε₀) : IsWellPreparedData S g β increasing ε₁ gε := by
  have hsub : Ioo 0 ε₁ ⊆ Ioo 0 ε₀ := Ioo_subset_Ioo_right hle
  obtain ⟨μ, hμ, hμ'⟩ := h.le_of_nonpos
  exact
    { pos := hε₁
      lipschitz := fun ε hε ↦ h.lipschitz ε (hsub hε)
      bounds := fun ε hε ↦ h.bounds ε (hsub hε)
      norm_gradient_le := fun ε hε ↦ h.norm_gradient_le ε (hsub hε)
      memH1 := fun ε hε ↦ h.memH1 ε (hsub hε)
      energy_le := fun ε hε ↦ h.energy_le ε (hsub hε)
      visc := fun ε hε ↦ h.visc ε (hsub hε)
      le_of_nonpos := ⟨μ, hμ, fun ε hε ↦ hμ' ε (hsub hε)⟩
      eq_zero_of_le := fun hinc ↦ by
        obtain ⟨c, hc, hc'⟩ := h.eq_zero_of_le hinc
        exact ⟨c, hc, fun ε hε ↦ hc' ε (hsub hε)⟩
      memH1_pos := h.memH1_pos
      tendsto_H1 := h.tendsto_H1 }

end IsWellPreparedData

end PerronVariational

end
