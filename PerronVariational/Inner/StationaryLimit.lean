/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Defs.Stationary
import GMTFoundations.BV.TotalVariation
import GMTFoundations.Sobolev.Cutoff
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import PerronVariational.Inner.GradConv
import PerronVariational.Inner.SliceInnerVar
import PerronVariational.Inner.Truncation
import PerronVariational.Inner.WeakHarmonic

/-!
# Stationary cores of the limit passages for inner variational solutions

These are the parts of the long-time limit (proof of **Theorem 3.10** of F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
one-phase problem*, arXiv:2609.14981; `Inner/LongTimeSteps.lean`) that do not involve time: they
apply verbatim to a sequence `vₙ` of locally Lipschitz functions on an open set `U`, and are shared
by the long-time limit and by the compactness of inner variational solutions (the paper's
**Lemma 2.10**, `Inner/InnerVarCompactness.lean`), whose proof follows the first paragraph of the
proof of Theorem 9.3 in D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure,
and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
545–591, doi:10.1002/cpa.22226, arXiv:2306.10131.

## Main results

* `StationaryLimit.lipschitzOnWith_sq`: `Q²` is Lipschitz on `U` if `Q` is Lipschitz and bounded
  in `[0, C]` on `U`.
* `StationaryLimit.ae_pos_imp_eq_one`: `1_{vₙ > 0} ≤ χₙ` passes to the limit.
* `StationaryLimit.integral_energy_eq_zero`: the energy identity `∫ |∇f|² η + f ∇f · ∇η = 0`
  for `f ≥ 0` weakly harmonic in `{f > 0}`.
* `StationaryLimit.tendstoLpLoc_gradient_of_energy`: if `vₙ → u₀` locally uniformly, the
  gradients are locally bounded (eventually), and the energy identities
  `∫ |∇vₙ|² η + vₙ ∇vₙ · ∇η → 0` and `∫ |∇u₀|² η + u₀ ∇u₀ · ∇η = 0` hold for smooth cut-offs
  `η`, then `∇vₙ → ∇u₀` in `L²_loc(U)`.
* `StationaryLimit.tendsto_integral_innerVarIntegrand`: if `∇vₙ → ∇u₀` in `L²_loc(U)`,
  `χₙ → χ₀` in `L¹_loc(U)`, `|χₙ| ≤ 1` on `U` and the gradients are locally bounded (eventually),
  then the integrals of the inner variation integrand (2.5) converge, for every `ξ ∈ C¹_c(U)`.
* `StationaryLimit.innerVar_lipschitz`: (2.5) for `C¹_c` fields implies (2.5) for Lipschitz
  fields with compact support (density of translated bumps).
-/

open Set Filter Topology MeasureTheory Metric
open scoped Gradient ENNReal ContDiff NNReal

@[expose] public section

namespace PerronVariational

namespace StationaryLimit

open LongTime

variable {d : ℕ}

/-! ### `Q²` is Lipschitz -/

/-- `Q²` is Lipschitz on `U` if `Q` is `K`-Lipschitz on `U` with `0 ≤ Q ≤ C` there. -/
theorem lipschitzOnWith_sq {U : Set (E d)} {Q : E d → ℝ} {K : ℝ≥0} {C : ℝ}
    (hL : LipschitzOnWith K Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x) (hQC : ∀ x ∈ U, Q x ≤ C) :
    LipschitzOnWith (Real.toNNReal (2 * C) * K) (fun y ↦ Q y ^ 2) U := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hQx0 := hQ0 x hx
  have hQy0 := hQ0 y hy
  have hQxC := hQC x hx
  have hQyC := hQC y hy
  have hd := hL.dist_le_mul x hx y hy
  rw [Real.dist_eq] at hd ⊢
  have h1 : Q x ^ 2 - Q y ^ 2 = (Q x + Q y) * (Q x - Q y) := by ring
  rw [h1, abs_mul, NNReal.coe_mul, Real.coe_toNNReal _ (by linarith), mul_assoc]
  have h2 : |Q x + Q y| ≤ 2 * C := by
    rw [abs_of_nonneg (by linarith)]; linarith
  exact mul_le_mul h2 hd (abs_nonneg _) (by linarith)

/-- `Q²` is locally Lipschitz on `U` if `Q` is Lipschitz on `U` with `0 ≤ Q ≤ C` there. -/
theorem locallyLipschitzOn_sq {U : Set (E d)} {Q : E d → ℝ} (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQ0 : ∀ x ∈ U, 0 ≤ Q x) {C : ℝ} (hQC : ∀ x ∈ U, Q x ≤ C) :
    LocallyLipschitzOn U fun y ↦ Q y ^ 2 := by
  obtain ⟨K, hK⟩ := hQ
  exact fun x _ ↦ ⟨_, U, self_mem_nhdsWithin, lipschitzOnWith_sq hK hQ0 hQC⟩

/-! ### Local-to-global and positivity -/

/-- Locally uniform convergence passes to reparametrizations `F ∘ g` with `g → p`. -/
theorem tendstoLocallyUniformlyOn_comp {α β ι ι' : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {s : Set α} {p : Filter ι}
    (h : TendstoLocallyUniformlyOn F f p s) {g : ι' → ι} {l : Filter ι'} (hg : Tendsto g l p) :
    TendstoLocallyUniformlyOn (fun n ↦ F (g n)) f l s := fun V hV x hx ↦
  let ⟨t, ht, hev⟩ := h V hV x hx
  ⟨t, ht, hg.eventually hev⟩

/-- **Local-to-global for a.e. properties on open sets**: a property holding a.e. on every
compact subset of the open set `U` holds a.e. on `U` (second countability). -/
theorem ae_restrict_of_forall_isCompact {U : Set (E d)} (hU : IsOpen U) {P : E d → Prop}
    (h : ∀ K ⊆ U, IsCompact K → ∀ᵐ x ∂(volume.restrict K), P x) :
    ∀ᵐ x ∂(volume.restrict U), P x := by
  rw [ae_restrict_iff' hU.measurableSet]
  have hB : volume {x | x ∈ U ∧ ¬ P x} = 0 := by
    refine measure_null_of_locally_null _ fun x hx ↦ ?_
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx.1
    have hcl : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
    refine ⟨{x | x ∈ U ∧ ¬ P x} ∩ ball x (r / 2),
      inter_mem_nhdsWithin _ (ball_mem_nhds x (by linarith)), ?_⟩
    have h1 := h _ hcl (isCompact_closedBall x (r / 2))
    rw [ae_restrict_iff' measurableSet_closedBall, ae_iff] at h1
    exact measure_mono_null (fun y hy ↦ fun hy' ↦ hy.1.2 (hy' (ball_subset_closedBall hy.2))) h1
  rw [ae_iff]
  exact measure_mono_null (fun y hy ↦ by
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy ⊢; exact hy) hB

/-- **`1_{u₀ > 0} ≤ χ₀`** in the limit (proof of Theorem 3.10, Step 4): if `vₙ → u₀` locally
uniformly on `U`, `1_{vₙ > 0} ≤ χₙ` a.e. on `U` and `χₙ → χ₀` in `L¹_loc(U)`, then
`1_{u₀ > 0} ≤ χ₀` a.e. on `U` (on compact subsets of `{u₀ > 0}`, eventually `vₙ > 0`, hence
`χₙ = 1` a.e.). -/
theorem ae_pos_imp_eq_one {U : Set (E d)} (hU : IsOpen U) {v χ : ℕ → E d → ℝ}
    {u₀ χ₀ : E d → ℝ} (hu₀ : ContinuousOn u₀ U) (hconv : TendstoLocallyUniformlyOn v u₀ atTop U)
    (hpos : ∀ n, ∀ᵐ x ∂(volume.restrict U), 0 < v n x → χ n x = 1)
    (hχ : TendstoLpLoc 1 volume U χ χ₀ atTop) (_hχm : Measurable χ₀) :
    ∀ᵐ x ∂(volume.restrict U), 0 < u₀ x → χ₀ x = 1 := by
  have hW : IsOpen (posSet u₀ U) := hu₀.isOpen_inter_preimage hU isOpen_Ioi
  have hWU : posSet u₀ U ⊆ U := fun x hx ↦ hx.1
  have key : ∀ᵐ x ∂(volume.restrict (posSet u₀ U)), χ₀ x = 1 := by
    refine ae_restrict_of_forall_isCompact hW fun K hKW hK ↦ ?_
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · subst hKe; simp
    obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne (hu₀.mono (hKW.trans hWU))
    have hc : 0 < u₀ x₀ := (hKW hx₀K).2
    have hunif : TendstoUniformlyOn v u₀ atTop K :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv K (hKW.trans hWU) hK
    have hev : ∀ᶠ n in atTop, ∀ x ∈ K, 0 < v n x := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif _ hc] with n hn x hx
      have h1 := hn x hx
      rw [Real.dist_eq] at h1
      have h2 : u₀ x₀ ≤ u₀ x := hmin hx
      linarith [le_abs_self (u₀ x - v n x)]
    have heq : ∀ᶠ n in atTop, eLpNorm (χ n - χ₀) 1 (volume.restrict K) =
        eLpNorm (fun x ↦ 1 - χ₀ x) 1 (volume.restrict K) := by
      filter_upwards [hev] with n hn
      refine eLpNorm_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hKW.trans hWU) (hpos n),
        ae_restrict_mem hK.measurableSet] with x hx hxK
      simp [hx (hn x hxK)]
    have hzero : eLpNorm (fun x ↦ 1 - χ₀ x) 1 (volume.restrict K) = 0 :=
      tendsto_const_nhds_iff.1 ((hχ K (hKW.trans hWU) hK).congr' heq)
    rw [eLpNorm_eq_zero_iff one_ne_zero] at hzero
    filter_upwards [hzero] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  rw [ae_restrict_iff' hW.measurableSet] at key
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [key] with x hx hxU hpos using hx ⟨hxU, hpos⟩

/-! ### The energy identity -/

/-- **Energy identity** for `f ≥ 0`, locally Lipschitz on `U` and weakly harmonic in `{f > 0}`:
`∫_U |∇f|² η + f ∇f · ∇η = 0` for `η ∈ C¹_c(U)` (truncation at small levels,
`integral_truncation_identity`). -/
theorem integral_energy_eq_zero {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : LocallyLipschitzOn U f) (hf0 : ∀ x ∈ U, 0 ≤ f x)
    (hweak : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ posSet f U →
      ∫ x in posSet f U, inner ℝ (∇ f x) (∇ φ x) = 0)
    {η : E d → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, (‖∇ f x‖ ^ 2 * η x + f x * inner ℝ (∇ f x) (∇ η x)) = 0 := by
  have hUm : MeasurableSet U := hU.measurableSet
  have hWo : IsOpen (posSet f U) := hf.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hWU : posSet f U ⊆ U := fun x hx ↦ hx.1
  have hid := integral_truncation_identity hU hf hf0 (a := fun _ ↦ 0)
    (fun K _ _ ↦ integrableOn_zero)
    (fun ζ hζ hζc hζW ↦ by
      have h0 := setIntegral_inner_gradient_eq_zero_of_lipschitz hWo
        (GMTFoundations.measurable_gradient f)
        (fun K' hK' hK'W ↦ by
          obtain ⟨b, hb⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hf hK'
            (hK'W.trans hWU)
          exact ⟨b, fun x hx ↦ by rw [gradient, LinearIsometryEquiv.norm_map]; exact hb x hx⟩)
        hweak hζ hζc hζW
      have e : ∫ x in U, inner ℝ (∇ f x) (∇ ζ x) =
          ∫ x in posSet f U, inner ℝ (∇ f x) (∇ ζ x) :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUm hWU fun x hx ↦ by
          simp [gradient, fderiv_of_notMem_tsupport ℝ fun h' ↦ hx.2 (hζW h')]
      rw [e, h0]
      simp) hη hηc hηU
  simp only [zero_mul, integral_zero] at hid
  linarith

/-! ### Strong `L²_loc` convergence of the gradients -/

/-- **Strong convergence of the gradients from the energy identities** (proof of Theorem 3.10,
Step 2, and the first paragraph of the proof of [Kriventsov–Weiss, Theorem 9.3]). Let `vₙ → u₀`
locally uniformly on the open set `U`, all locally Lipschitz on `U`, with `vₙ` locally bounded
and `∇vₙ` locally bounded for large `n`. Suppose that for every smooth cut-off `η` with compact
support in `U`,
`∫_U |∇vₙ|² η + vₙ ∇vₙ · ∇η → 0` and `∫_U |∇u₀|² η + u₀ ∇u₀ · ∇η = 0`.
Then `∇vₙ → ∇u₀` in `L²_loc(U)`.

Proof: with `η = 1` on `K`, `∫ η |∇vₙ|² → -∫ u₀ ∇u₀ · ∇η = ∫ η |∇u₀|²` (uniform convergence of
`vₙ` and weak convergence of the gradients, `tendsto_integral_inner_gradient`), and the cross
term `∫ η ∇vₙ · ∇u₀ → ∫ η |∇u₀|²`; hence `∫ η |∇vₙ - ∇u₀|² → 0`. -/
theorem tendstoLpLoc_gradient_of_energy {U : Set (E d)} (hU : IsOpen U)
    {v : ℕ → E d → ℝ} {u₀ : E d → ℝ} (hvL : ∀ n, LocallyLipschitzOn U (v n))
    (hu₀ : LocallyLipschitzOn U u₀)
    (hconvK : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn v u₀ atTop K)
    (hBF : ∀ K, IsCompact K → K ⊆ U → ∃ B, ∀ᶠ n in atTop, ∀ x ∈ K, ‖∇ (v n) x‖ ≤ B)
    (hvb : ∀ K, IsCompact K → K ⊆ U → ∃ M, ∀ n, ∀ x ∈ K, |v n x| ≤ M)
    (hE : ∀ η : E d → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) →
      Tendsto (fun n ↦ ∫ x in U, (‖∇ (v n) x‖ ^ 2 * η x + v n x * inner ℝ (∇ (v n) x) (∇ η x)))
        atTop (𝓝 0))
    (hE₀ : ∀ η : E d → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) →
      ∫ x in U, (‖∇ u₀ x‖ ^ 2 * η x + u₀ x * inner ℝ (∇ u₀ x) (∇ η x)) = 0) :
    TendstoLpLoc 2 volume U (fun n ↦ ∇ (v n)) (∇ u₀) atTop := by
  intro K hKU hK
  have hUm : MeasurableSet U := hU.measurableSet
  -- a cutoff `η = 1` on `K`
  obtain ⟨η, hηs, hηc, hηU, hη01, hη1⟩ := GMTFoundations.exists_smooth_cutoff hK hU hKU
  set K'' := tsupport η
  have hK'' : IsCompact K'' := hηc.isCompact
  have hK''m : MeasurableSet K'' := hK''.measurableSet
  have : IsFiniteMeasure (volume.restrict K'') :=
    isFiniteMeasure_restrict.2 hK''.measure_lt_top.ne
  have hη0 : ∀ x ∉ K'', η x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hgη0 : ∀ x ∉ K'', ∇ η x = 0 := fun x hx ↦ by
    simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
  have hgηc : Continuous (∇ η) :=
    (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp (hηs.continuous_fderiv (by simp))
  obtain ⟨Bη, hBη⟩ := hK''.exists_bound_of_continuousOn hgηc.continuousOn
  have hBη0 : ∀ x, ‖∇ η x‖ ≤ max Bη 0 := fun x ↦ by
    by_cases hx : x ∈ K''
    · exact (hBη x hx).trans (le_max_left _ _)
    · simp [hgη0 x hx]
  have hgradb : ∀ {g : E d → ℝ}, LocallyLipschitzOn U g → ∃ b, ∀ x ∈ K'', ‖∇ g x‖ ≤ b :=
    fun {g} hg ↦ by
      obtain ⟨b, hb⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hg hK'' hηU
      exact ⟨b, fun x hx ↦ by rw [gradient, LinearIsometryEquiv.norm_map]; exact hb x hx⟩
  obtain ⟨B', hB'⟩ := hgradb hu₀
  obtain ⟨MI, hMI⟩ := hK''.exists_bound_of_continuousOn (hu₀.continuousOn.mono hηU)
  obtain ⟨M, hM⟩ := hvb K'' hK'' hηU
  -- measurability and bounds
  have hηm : Measurable η := hηs.continuous.measurable
  have hvc : ∀ n, AEStronglyMeasurable (v n) (volume.restrict K'') := fun n ↦
    ((hvL n).continuousOn.mono hηU).aestronglyMeasurable hK''m
  have huc : AEStronglyMeasurable u₀ (volume.restrict K'') :=
    (hu₀.continuousOn.mono hηU).aestronglyMeasurable hK''m
  have hηb : ∀ x, ‖η x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_of_nonneg (hη01 x).1]; exact (hη01 x).2
  have hvb' : ∀ n, ∀ x ∈ K'', ‖v n x‖ ≤ M := fun n x hx ↦ by
    rw [Real.norm_eq_abs]; exact hM n x hx
  have hMI' : ∀ x ∈ K'', ‖u₀ x‖ ≤ max MI 0 := fun x hx ↦ (hMI x hx).trans (le_max_left _ _)
  have hB'' : ∀ x ∈ K'', ‖∇ u₀ x‖ ≤ max B' 0 := fun x hx ↦ (hB' x hx).trans (le_max_left _ _)
  -- integrability
  have hiA : ∀ {g : E d → ℝ}, LocallyLipschitzOn U g →
      IntegrableOn (fun x ↦ ‖∇ g x‖ ^ 2 * η x) U := fun {g} hg ↦ by
    obtain ⟨b, hb⟩ := hgradb hg
    refine integrableOn_of_bound_of_vanish hUm hK''
      (((GMTFoundations.measurable_gradient g).norm.pow_const 2).mul hηm).aestronglyMeasurable
      (c := b ^ 2 * 1) (fun x hx ↦ ?_) fun x hx ↦ by simp [hη0 x hx]
    rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hb x hx) 2) (hηb x) (norm_nonneg _)
      (sq_nonneg _)
  have hiB : ∀ {g : E d → ℝ}, LocallyLipschitzOn U g → ∀ {Mg : ℝ},
      (∀ x ∈ K'', ‖g x‖ ≤ Mg) →
      IntegrableOn (fun x ↦ g x * inner ℝ (∇ g x) (∇ η x)) U := fun {g} hg {Mg} hMg ↦ by
    obtain ⟨b, hb⟩ := hgradb hg
    refine integrableOn_of_bound_of_vanish hUm hK''
      (((hg.continuousOn.mono hηU).aestronglyMeasurable hK''m).mul
        ((GMTFoundations.measurable_gradient g).inner hgηc.measurable).aestronglyMeasurable)
      (c := Mg * (b * max Bη 0)) (fun x hx ↦ ?_) fun x hx ↦ by simp [hgη0 x hx]
    rw [norm_mul]
    exact mul_le_mul (hMg x hx) ((norm_inner_le_norm _ _).trans (mul_le_mul (hb x hx)
      (hBη0 x) (norm_nonneg _) ((norm_nonneg _).trans (hb x hx)))) (norm_nonneg _)
      ((norm_nonneg _).trans (hMg x hx))
  -- the quantities
  set IA : ℕ → ℝ := fun n ↦ ∫ x in U, ‖∇ (v n) x‖ ^ 2 * η x
  set IB : ℕ → ℝ := fun n ↦ ∫ x in U, v n x * inner ℝ (∇ (v n) x) (∇ η x)
  set c := ∫ x in U, ‖∇ u₀ x‖ ^ 2 * η x
  set cB := ∫ x in U, u₀ x * inner ℝ (∇ u₀ x) (∇ η x)
  have hIE : Tendsto (fun n ↦ IA n + IB n) atTop (𝓝 0) := by
    refine (hE η hηs hηc hηU hη01).congr fun n ↦ ?_
    simp only [IA, IB]
    rw [integral_add (hiA (hvL n)) (hiB (hvL n) (hvb' n))]
  have hc : c = -cB := by
    have hidInf := hE₀ η hηs hηc hηU hη01
    rw [integral_add (hiA hu₀) (hiB hu₀ hMI')] at hidInf
    linarith
  -- fields vanishing outside `K''` are globally a.e.-strongly measurable
  have haesm : ∀ {G : E d → E d}, AEStronglyMeasurable G (volume.restrict K'') →
      (∀ x ∉ K'', G x = 0) → AEStronglyMeasurable G volume := fun {G} hG hG0 ↦ by
    have : G = K''.indicator G := by
      ext x
      by_cases hx : x ∈ K''
      · simp [hx]
      · simp [hx, hG0 x hx]
    rw [this]
    exact (aestronglyMeasurable_indicator_iff hK''m).2 hG
  -- `∫ vₙ ∇vₙ · ∇η → ∫ u₀ ∇u₀ · ∇η` (weak convergence of the gradients)
  obtain ⟨B, hB⟩ := hBF K'' hK'' hηU
  have hlimB : Tendsto IB atTop (𝓝 cB) := by
    set G1 : E d → E d := fun x ↦ u₀ x • ∇ η x
    set G2 : ℕ → E d → E d := fun n x ↦ (v n x - u₀ x) • ∇ η x
    have hG1v : ∀ x ∉ K'', G1 x = 0 := fun x hx ↦ by simp [G1, hgη0 x hx]
    have hG2v : ∀ n, ∀ x ∉ K'', G2 n x = 0 := fun n x hx ↦ by simp [G2, hgη0 x hx]
    have hG1m : AEStronglyMeasurable G1 volume :=
      haesm (huc.smul hgηc.aestronglyMeasurable) hG1v
    have hG2m : ∀ n, AEStronglyMeasurable (G2 n) volume := fun n ↦
      haesm (((hvc n).sub huc).smul hgηc.aestronglyMeasurable) (hG2v n)
    have hG1b : ∀ x, ‖G1 x‖ ≤ max MI 0 * max Bη 0 := fun x ↦ by
      by_cases hx : x ∈ K''
      · rw [norm_smul]
        exact mul_le_mul (hMI' x hx) (hBη0 x) (norm_nonneg _) (le_max_right _ _)
      · rw [hG1v x hx, norm_zero]; positivity
    have hG2b : ∀ n x, ‖G2 n x‖ ≤ (max M 0 + max MI 0) * max Bη 0 := fun n x ↦ by
      by_cases hx : x ∈ K''
      · rw [norm_smul]
        refine mul_le_mul ((norm_sub_le _ _).trans (add_le_add
          ((hvb' n x hx).trans (le_max_left _ _)) (hMI' x hx))) (hBη0 x) (norm_nonneg _) ?_
        positivity
      · rw [hG2v n x hx, norm_zero]; positivity
    have hsplitB : ∀ n, IB n = (∫ x in U, inner ℝ (∇ (v n) x) (G1 x)) +
        ∫ x in U, inner ℝ (∇ (v n) x) (G2 n x) := fun n ↦ by
      rw [← integral_add (integrableOn_inner_gradient hU (hvL n) hK'' hηU hG1m hG1b hG1v)
        (integrableOn_inner_gradient hU (hvL n) hK'' hηU (hG2m n) (hG2b n) (hG2v n))]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [G1, G2, inner_smul_right]
      ring
    have h1 : Tendsto (fun n ↦ ∫ x in U, inner ℝ (∇ (v n) x) (G1 x)) atTop (𝓝 cB) := by
      have := tendsto_integral_inner_gradient hU hvL hu₀ hconvK hBF hK'' hηU hG1m hG1b hG1v
      rwa [show cB = ∫ x in U, inner ℝ (∇ u₀ x) (G1 x) from
        integral_congr_ae (Eventually.of_forall fun x ↦ by simp [G1, inner_smul_right])]
    have hψs : tsupport (fun x ↦ ‖∇ η x‖) ⊆ K'' :=
      closure_minimal (fun x hx ↦ by
        by_contra h'
        exact hx (by simp [hgη0 x h'])) hK''.isClosed
    have hint : Tendsto (fun n ↦ ∫ x in K'', |v n x - u₀ x| * ‖∇ η x‖) atTop (𝓝 0) := by
      have := tendsto_setIntegral_mul_of_tendstoUniformlyOn hK''m (ψ := fun x ↦ ‖∇ η x‖)
        hgηc.norm (hK''.of_isClosed_subset (isClosed_tsupport _) hψs) hψs
        (F := fun n x ↦ |v n x - u₀ x|) (f := fun _ ↦ 0)
        (Eventually.of_forall fun n ↦ (((hvL n).continuousOn.mono hηU).sub
          (hu₀.continuousOn.mono hηU)).abs.mono hψs) continuousOn_const ?_
      · simpa using this
      · rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconvK K'' hK'' hηU) ε hε] with n hn x hx
        have := hn x (hψs hx)
        rw [Real.dist_eq] at this ⊢
        rwa [zero_sub, abs_neg, abs_abs, abs_sub_comm]
    have h2 : Tendsto (fun n ↦ ∫ x in U, inner ℝ (∇ (v n) x) (G2 n x)) atTop (𝓝 0) := by
      have hB0 := hint.const_mul B
      rw [mul_zero] at hB0
      refine squeeze_zero_norm' ?_ hB0
      filter_upwards [hB] with n hn
      have hi2 : IntegrableOn (G2 n) K'' :=
        IntegrableOn.of_bound hK''.measure_lt_top (hG2m n).restrict _
          (Eventually.of_forall (hG2b n))
      refine (norm_setIntegral_inner_gradient_le hUm hK''m hηU hi2 (hG2v n) hn).trans
        (le_of_eq ?_)
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [G2, norm_smul, Real.norm_eq_abs]
    have := h1.add h2
    rw [add_zero] at this
    exact this.congr fun n ↦ (hsplitB n).symm
  -- the cross term `∫ η ∇vₙ · ∇u₀ → ∫ η |∇u₀|²`
  set G3 : E d → E d := fun x ↦ η x • ∇ u₀ x
  have hG3v : ∀ x ∉ K'', G3 x = 0 := fun x hx ↦ by simp [G3, hη0 x hx]
  have hG3m : AEStronglyMeasurable G3 volume :=
    (hηm.smul (GMTFoundations.measurable_gradient u₀)).aestronglyMeasurable
  have hG3b : ∀ x, ‖G3 x‖ ≤ max B' 0 := fun x ↦ by
    by_cases hx : x ∈ K''
    · rw [norm_smul]
      calc ‖η x‖ * ‖∇ u₀ x‖ ≤ 1 * max B' 0 :=
            mul_le_mul (hηb x) (hB'' x hx) (norm_nonneg _) zero_le_one
        _ = max B' 0 := one_mul _
    · rw [hG3v x hx, norm_zero]; positivity
  set IC : ℕ → ℝ := fun n ↦ ∫ x in U, inner ℝ (∇ (v n) x) (G3 x)
  have hlimC : Tendsto IC atTop (𝓝 c) := by
    have := tendsto_integral_inner_gradient hU hvL hu₀ hconvK hBF hK'' hηU hG3m hG3b hG3v
    rwa [show c = ∫ x in U, inner ℝ (∇ u₀ x) (G3 x) from
      integral_congr_ae (Eventually.of_forall fun x ↦ by
        simp only [G3, inner_smul_right, real_inner_self_eq_norm_sq]; ring)]
  -- `∫ η |∇vₙ|² → ∫ η |∇u₀|²`
  have hlimA : Tendsto IA atTop (𝓝 c) := by
    have h := hIE.sub hlimB
    rw [zero_sub, ← hc] at h
    exact h.congr fun n ↦ by ring
  -- `∫ η |∇vₙ - ∇u₀|² → 0`
  set D : ℕ → ℝ := fun n ↦ ∫ x in U, η x * ‖∇ (v n) x - ∇ u₀ x‖ ^ 2
  have hD : ∀ n, D n = IA n - 2 * IC n + c := fun n ↦ by
    have hiC := integrableOn_inner_gradient hU (hvL n) hK'' hηU hG3m hG3b hG3v
    simp only [D, IA, IC]
    have e : ∫ x in U, η x * ‖∇ (v n) x - ∇ u₀ x‖ ^ 2 =
        ∫ x in U, ((‖∇ (v n) x‖ ^ 2 * η x - 2 * inner ℝ (∇ (v n) x) (G3 x)) +
          ‖∇ u₀ x‖ ^ 2 * η x) := by
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [G3, inner_smul_right, norm_sub_sq_real]
      ring
    have hiC2 : IntegrableOn (fun x ↦ 2 * inner ℝ (∇ (v n) x) (G3 x)) U := hiC.const_mul 2
    have hi1 : IntegrableOn
        (fun x ↦ ‖∇ (v n) x‖ ^ 2 * η x - 2 * inner ℝ (∇ (v n) x) (G3 x)) U :=
      (hiA (hvL n)).sub hiC2
    rw [e, integral_add hi1 (hiA hu₀), integral_sub (hiA (hvL n)) hiC2, integral_const_mul]
  have hlimD : Tendsto D atTop (𝓝 0) := by
    have h := (hlimA.sub (hlimC.const_mul 2)).add_const c
    rw [show c - 2 * c + c = 0 by ring] at h
    exact h.congr fun n ↦ (hD n).symm
  -- conclusion
  have hiD : ∀ n, IntegrableOn (fun x ↦ η x * ‖∇ (v n) x - ∇ u₀ x‖ ^ 2) U := fun n ↦ by
    obtain ⟨b, hb⟩ := hgradb (hvL n)
    refine integrableOn_of_bound_of_vanish hUm hK''
      (hηm.mul (((GMTFoundations.measurable_gradient _).sub
        (GMTFoundations.measurable_gradient u₀)).norm.pow_const 2)).aestronglyMeasurable
      (c := 1 * (b + max B' 0) ^ 2) (fun x hx ↦ ?_) fun x hx ↦ by simp [hη0 x hx]
    rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul (hηb x) (pow_le_pow_left₀ (norm_nonneg _)
      ((norm_sub_le _ _).trans (add_le_add (hb x hx) (hB'' x hx))) 2) (by positivity)
      zero_le_one
  have hup : Tendsto (fun n ↦ ENNReal.ofReal (D n) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto _).comp
      (ENNReal.tendsto_ofReal hlimD)
    rwa [Function.comp_def, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ ↦ bot_le)
    fun n ↦ ?_
  exact eLpNorm_two_le_of_weight hKU (fun x ↦ (hη01 x).1) hη1 hK.measurableSet
    ((GMTFoundations.measurable_gradient _).sub
      (GMTFoundations.measurable_gradient u₀)).aestronglyMeasurable (hiD n)

/-! ### Passing to the limit in the inner variation integrand -/

/-- The inner variation integrand is a.e.-strongly measurable on a compact `K ⊆ U` on which `Q²`
is continuous, for measurable `χ` and `ξ ∈ C¹`. -/
theorem aestronglyMeasurable_innerVarIntegrand {K : Set (E d)} (hKm : MeasurableSet K)
    {Q : E d → ℝ} (hQc : ContinuousOn (fun y ↦ Q y ^ 2) K) (w : E d → ℝ) {c : E d → ℝ}
    (hc : Measurable c) {ξ : E d → E d} (hξ : ContDiff ℝ 1 ξ) :
    AEStronglyMeasurable (innerVarIntegrand Q w c ξ) (volume.restrict K) := by
  have hg := (GMTFoundations.measurable_gradient w).aestronglyMeasurable (μ := volume.restrict K)
  have hDξ : AEStronglyMeasurable (fun x ↦ fderiv ℝ ξ x (∇ w x)) (volume.restrict K) := by
    simpa using (ContinuousLinearMap.apply ℝ (E d)).aestronglyMeasurable_comp₂ hg
      (hξ.continuous_fderiv one_ne_zero).aestronglyMeasurable
  have hDQ : AEStronglyMeasurable (fun x ↦ fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x))
      (volume.restrict K) := by
    simpa using (ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
      hξ.continuous.aestronglyMeasurable (measurable_fderiv ℝ _).aestronglyMeasurable
  unfold innerVarIntegrand
  exact ((((hg.norm.pow 2).add ((hQc.aestronglyMeasurable hKm).mul
    hc.aestronglyMeasurable)).mul
      (GMTFoundations.continuous_divergence hξ).aestronglyMeasurable).sub
    (aestronglyMeasurable_const.mul (hg.inner hDξ))).add (hDQ.mul hc.aestronglyMeasurable)

/-- Along a subsequence, the integrals of the inner variation integrand converge (dominated
convergence after extracting a.e. convergent subsequences); see
`tendsto_integral_innerVarIntegrand`. -/
theorem exists_subseq_tendsto_integral_innerVarIntegrand {U : Set (E d)} (hU : IsOpen U)
    {Q : E d → ℝ} (hQ : LocallyLipschitzOn U fun y ↦ Q y ^ 2)
    {v χ : ℕ → E d → ℝ} {u₀ χ₀ : E d → ℝ} (hχm : ∀ n, Measurable (χ n))
    (_hχ₀m : Measurable χ₀) (hχb : ∀ n, ∀ x ∈ U, |χ n x| ≤ 1)
    (hBF : ∀ K, IsCompact K → K ⊆ U → ∃ B, ∀ᶠ n in atTop, ∀ x ∈ K, ‖∇ (v n) x‖ ≤ B)
    (hgrad : TendstoLpLoc 2 volume U (fun n ↦ ∇ (v n)) (∇ u₀) atTop)
    (hχ : TendstoLpLoc 1 volume U χ χ₀ atTop)
    {ξ : E d → E d} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ) (hξU : tsupport ξ ⊆ U) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun k ↦ ∫ x in U, innerVarIntegrand Q (v (ψ k)) (χ (ψ k)) ξ x) atTop
        (𝓝 (∫ x in U, innerVarIntegrand Q u₀ χ₀ ξ x)) := by
  set K := tsupport ξ with hKdef
  have hK : IsCompact K := hξc.isCompact
  have hKm : MeasurableSet K := hK.measurableSet
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hUm : MeasurableSet U := hU.measurableSet
  have hred : ∀ w c : E d → ℝ, ∫ x in U, innerVarIntegrand Q w c ξ x =
      ∫ x in K, innerVarIntegrand Q w c ξ x := fun w c ↦
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUm hξU fun x hx ↦
      innerVarIntegrand_eq_zero_of_notMem _ _ _ hx.2
  simp only [hred]
  -- a subsequence along which `∇vₙ → ∇u₀` and `χₙ → χ₀` a.e. on `K`
  obtain ⟨ns1, hns1, hae1⟩ := (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
    (hgrad K hξU hK)).exists_seq_tendsto_ae
  obtain ⟨ns2, hns2, hae2⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    ((hχ K hξU hK).comp hns1.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨fun k ↦ ns1 (ns2 k), hns1.comp hns2, ?_⟩
  -- bounds on `K`
  obtain ⟨B, hB⟩ := hBF K hK hξU
  have hBev : ∀ᶠ k in atTop, ∀ x ∈ K, ‖∇ (v (ns1 (ns2 k))) x‖ ≤ B :=
    (hns1.comp hns2).tendsto_atTop.eventually hB
  obtain ⟨Cdiv, hCdiv⟩ :=
    hK.exists_bound_of_continuousOn (GMTFoundations.continuous_divergence hξ).continuousOn
  obtain ⟨CD, hCD⟩ := hK.exists_bound_of_continuousOn
    (hξ.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨Cξ, hCξ⟩ := hK.exists_bound_of_continuousOn hξ.continuous.continuousOn
  obtain ⟨CQ2, hCQ2⟩ := hK.exists_bound_of_continuousOn (hQ.continuousOn.mono hξU)
  obtain ⟨CQ, hCQ⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hQ hK hξU
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ ↦ (B ^ 2 + CQ2) * Cdiv + 2 * B * (CD * B) + CQ * Cξ)
    (Eventually.of_forall fun k ↦ aestronglyMeasurable_innerVarIntegrand hKm
      (hQ.continuousOn.mono hξU) _ (hχm _) hξ) ?_ (integrable_const _) ?_
  · filter_upwards [hBev] with k hk
    filter_upwards [ae_restrict_mem hKm] with x hx
    have hg : ‖∇ (v (ns1 (ns2 k))) x‖ ≤ B := hk x hx
    have hB0 : 0 ≤ B := (norm_nonneg _).trans hg
    have hχx := hχb (ns1 (ns2 k)) x (hξU hx)
    have hdiv := hCdiv x hx
    have hD := hCD x hx
    have hξx := hCξ x hx
    have hQ2 := hCQ2 x hx
    have hDQ := hCQ x hx
    have hCQ20 : 0 ≤ CQ2 := (norm_nonneg _).trans hQ2
    have hD0 : 0 ≤ CD := (norm_nonneg _).trans hD
    set w := v (ns1 (ns2 k))
    set c := χ (ns1 (ns2 k))
    have t1 : ‖(‖∇ w x‖ ^ 2 + Q x ^ 2 * c x) * divergence ξ x‖ ≤ (B ^ 2 + CQ2) * Cdiv := by
      rw [norm_mul]
      refine mul_le_mul ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hdiv (norm_nonneg _)
        (by positivity)
      · rw [norm_pow, norm_norm]; gcongr
      · rw [norm_mul, Real.norm_eq_abs (c x)]
        calc ‖Q x ^ 2‖ * |c x| ≤ CQ2 * 1 := mul_le_mul hQ2 hχx (abs_nonneg _) hCQ20
          _ = CQ2 := mul_one _
    have t2 : ‖2 * inner ℝ (∇ w x) (fderiv ℝ ξ x (∇ w x))‖ ≤ 2 * B * (CD * B) := by
      rw [norm_mul, Real.norm_two, mul_assoc]
      refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (by norm_num)
      exact mul_le_mul hg ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hD hg (norm_nonneg _) hD0)) (norm_nonneg _) hB0
    have t3 : ‖fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x) * c x‖ ≤ CQ * Cξ := by
      rw [norm_mul, Real.norm_eq_abs (c x)]
      calc ‖fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x)‖ * |c x| ≤ (CQ * Cξ) * 1 := by
            refine mul_le_mul ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hDQ hξx (norm_nonneg _) ((norm_nonneg _).trans hDQ))) hχx
              (abs_nonneg _) (mul_nonneg ((norm_nonneg _).trans hDQ) ((norm_nonneg _).trans hξx))
        _ = CQ * Cξ := mul_one _
    simp only [innerVarIntegrand]
    exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)
  · filter_upwards [hae1, hae2] with x hx1 hx2
    have ha : Tendsto (fun k ↦ ∇ (v (ns1 (ns2 k))) x) atTop (𝓝 (∇ u₀ x)) :=
      hx1.comp hns2.tendsto_atTop
    simp only [innerVarIntegrand]
    exact ((((ha.norm.pow 2).add (tendsto_const_nhds.mul hx2)).mul tendsto_const_nhds).sub
      (tendsto_const_nhds.mul (ha.inner
        (((fderiv ℝ ξ x).continuous.tendsto _).comp ha)))).add (tendsto_const_nhds.mul hx2)

/-- **Passage to the limit in the inner variation identity** (proof of Theorem 3.10, Step 4, and
[Kriventsov–Weiss, proof of Theorem 9.3]). If `∇vₙ → ∇u₀` in `L²_loc(U)`, `χₙ → χ₀` in `L¹_loc(U)`,
`|χₙ| ≤ 1` on `U`, the gradients `∇vₙ` are bounded on compact subsets of `U` for large `n`, and
`Q²` is locally Lipschitz on `U`, then for `ξ ∈ C¹_c(U; ℝᵈ)` the integrals of the inner
variation integrand (2.5) of `(vₙ, χₙ)` converge to that of `(u₀, χ₀)`. -/
theorem tendsto_integral_innerVarIntegrand {U : Set (E d)} (hU : IsOpen U)
    {Q : E d → ℝ} (hQ : LocallyLipschitzOn U fun y ↦ Q y ^ 2)
    {v χ : ℕ → E d → ℝ} {u₀ χ₀ : E d → ℝ} (hχm : ∀ n, Measurable (χ n))
    (hχ₀m : Measurable χ₀) (hχb : ∀ n, ∀ x ∈ U, |χ n x| ≤ 1)
    (hBF : ∀ K, IsCompact K → K ⊆ U → ∃ B, ∀ᶠ n in atTop, ∀ x ∈ K, ‖∇ (v n) x‖ ≤ B)
    (hgrad : TendstoLpLoc 2 volume U (fun n ↦ ∇ (v n)) (∇ u₀) atTop)
    (hχ : TendstoLpLoc 1 volume U χ χ₀ atTop)
    {ξ : E d → E d} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ) (hξU : tsupport ξ ⊆ U) :
    Tendsto (fun n ↦ ∫ x in U, innerVarIntegrand Q (v n) (χ n) ξ x) atTop
      (𝓝 (∫ x in U, innerVarIntegrand Q u₀ χ₀ ξ x)) := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ψ, -, hψ⟩ := exists_subseq_tendsto_integral_innerVarIntegrand hU hQ
    (v := fun n ↦ v (ns n)) (χ := fun n ↦ χ (ns n)) (fun n ↦ hχm (ns n)) hχ₀m
    (fun n ↦ hχb (ns n))
    (fun K hK hKU ↦ (hBF K hK hKU).imp fun _ hB ↦ hns.eventually hB)
    (fun K hKU hK ↦ (hgrad K hKU hK).comp hns) (fun K hKU hK ↦ (hχ K hKU hK).comp hns)
    hξ hξc hξU
  exact ⟨ψ, hψ⟩

/-! ### From `C¹` to Lipschitz test fields -/

/-- **From `C¹` to Lipschitz test fields** (Definition 2.8(iv) is stated for `ξ ∈ C^{0,1}_c(U)`): if
(2.5) holds for all `ξ ∈ C¹_c(U; ℝᵈ)`, `v` is locally Lipschitz on `U`, `Q²` is locally
Lipschitz on `U` and `χ` is bounded measurable, then it holds for Lipschitz `ξ` with compact
support in `U` (mollify `ξ`: `Dξ_ε → Dξ` a.e. and boundedly, dominated convergence). -/
theorem innerVar_lipschitz {U : Set (E d)} (hU : IsOpen U) {Q v χ₁ : E d → ℝ}
    (hQ : LocallyLipschitzOn U fun y ↦ Q y ^ 2) (hv : LocallyLipschitzOn U v)
    (hχm : Measurable χ₁) (hχb : ∀ x, |χ₁ x| ≤ 1)
    (hC1 : ∀ ξ : E d → E d, ContDiff ℝ 1 ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
      ∫ x in U, innerVarIntegrand Q v χ₁ ξ x = 0) :
    ∀ ξ : E d → E d, (∃ K, LipschitzWith K ξ) → HasCompactSupport ξ → tsupport ξ ⊆ U →
      ∫ x in U, innerVarIntegrand Q v χ₁ ξ x = 0 := by
  intro ξ hξ hξc hξU
  obtain ⟨D, -, hD⟩ := TopologicalSpace.exists_countable_dense (E d)
  have hb : ∀ i n, ∀ q ∈ D, closedBall q (bumpRad n) ⊆ U →
      ∫ x in U, (ivCoeffA Q χ₁ (coordVec i) x * mollAt n q x +
        fderiv ℝ (mollAt n q) x (ivCoeffG Q v χ₁ (coordVec i) x)) = 0 := by
    intro i n q _ hB
    have hc : HasCompactSupport fun y ↦ mollAt n q y • coordVec i :=
      HasCompactSupport.intro (isCompact_closedBall q (bumpRad n)) fun x hx ↦ by
        simp [mollAt_eq_zero hx]
    rw [← hC1 (fun y ↦ mollAt n q y • coordVec i)
      (((contDiff_mollAt n q).smul contDiff_const).of_le (by simp)) hc
      ((tsupport_mollAt_smul_subset n q _).trans hB)]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ (innerVarIntegrand_smul_const _ _ _
      ((contDiff_mollAt n q).differentiable (by simp) x) _).symm)
  have hA : ∀ i, ∀ K, IsCompact K → K ⊆ U → IntegrableOn (ivCoeffA Q χ₁ (coordVec i)) K :=
    fun i K hK hKU ↦ by
      obtain ⟨CQ, hCQ⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hQ hK hKU
      exact integrableOn_ivCoeffA hK hCQ hχm (fun x _ ↦ hχb x) _
  have hG : ∀ i, ∀ K, IsCompact K → K ⊆ U →
      IntegrableOn (ivCoeffG Q v χ₁ (coordVec i)) K := fun i K hK hKU ↦ by
    obtain ⟨B, hB⟩ := GMTFoundations.exists_bound_fderiv_of_locallyLipschitzOn hU hv hK hKU
    refine integrableOn_ivCoeffG hK (hQ.continuousOn.mono hKU) hχm (fun x _ ↦ hχb x)
      (B := B) (fun x hx ↦ ?_) _
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact hB x hx
  obtain ⟨-, h0⟩ := sum_coord_firstOrder_eq_zero hU hD hA hG hb hξ hξc hξU
  obtain ⟨K, hK⟩ := hξ
  rw [integral_congr_ae (ae_restrict_of_ae (hK.ae_differentiableAt.mono fun x hx ↦
    innerVarIntegrand_eq_sum_coord _ _ _ hx))]
  exact h0

end StationaryLimit

end PerronVariational

end
