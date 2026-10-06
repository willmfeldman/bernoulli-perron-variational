/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Sobolev
import GMTFoundations.DeGiorgi.DeGiorgi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import PerronVariational.Main.Directional
import PerronVariational.Registry.FunctionalAnalysis

/-!
# Stability of directional minimality: preliminaries

Part of the proof of **Lemma 2.12** of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties
of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981: elementary
Sobolev helpers, the lower semicontinuity of the Dirichlet energy `energyJ_le_liminf` (weak
compactness and Fatou), the lattice identity `energyJ_add_le_of_swap`, shrinking annuli, the
approximating data `StabData`, the competitors `v_n = u_n ∓ φ (u_n - v)_±` and the energy on the
annulus `B_R \ B_s`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal NNReal

@[expose] public section

namespace PerronVariational

namespace DirectionalStable

variable {d : ℕ}

/-! ### Elementary Sobolev helpers -/

section Helpers

/-- Restriction of a weak gradient to an open subset. -/
theorem hasWeakGradient_mono {U W : Set (E d)} {f : E d → ℝ} {G : E d → E d}
    (hf : HasWeakGradient U f G) (hWU : W ⊆ U) : HasWeakGradient W f G :=
  GMTFoundations.HasWeakGradient.of_integral_eq (hf.1.mono_set hWU) (hf.2.1.mono_set hWU)
    fun _ hφ hφc hφW v ↦ hf.integral_eq hφ hφc (hφW.trans hWU) v

/-- Restriction of `H¹_loc` to an open subset. -/
theorem memH1Loc_mono {U W : Set (E d)} {f : E d → ℝ} {G : E d → E d}
    (hf : MemH1Loc U f G) (hWU : W ⊆ U) : MemH1Loc W f G :=
  ⟨hasWeakGradient_mono hf.1 hWU, fun K hK hKc ↦ hf.2 K (hK.trans hWU) hKc⟩

/-- `‖G‖_{L²}` in terms of the lower integral of `‖G‖²`. -/
theorem eLpNorm_two_eq {X : Type*} [MeasurableSpace X] {F : Type*} [NormedAddCommGroup F]
    (G : X → F) (μ : Measure X) (hG : AEStronglyMeasurable G μ) :
    eLpNorm G 2 μ = (∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hG]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  norm_cast

/-- If `fₙ → f` uniformly a.e. on `W` and `ψ` is integrable on `W`, then
`∫_W fₙ ψ → ∫_W f ψ`. -/
theorem tendsto_setIntegral_mul_of_ae_bound {W : Set (E d)} {f : ℕ → E d → ℝ} {f₀ ψ : E d → ℝ}
    (hf : ∀ n, IntegrableOn (fun x ↦ f n x * ψ x) W)
    (hf₀ : IntegrableOn (fun x ↦ f₀ x * ψ x) W) (hψ : IntegrableOn ψ W)
    (hconv : ∀ δ > 0, ∀ᶠ n in atTop, ∀ᵐ x ∂(volume.restrict W), |f n x - f₀ x| ≤ δ) :
    Tendsto (fun n ↦ ∫ x in W, f n x * ψ x) atTop (𝓝 (∫ x in W, f₀ x * ψ x)) := by
  set C := ∫ x in W, ‖ψ x‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ ↦ norm_nonneg _
  rw [Metric.tendsto_nhds]
  intro η hη
  have hδ : 0 < η / (C + 1) := div_pos hη (by linarith)
  filter_upwards [hconv _ hδ] with n hn
  rw [dist_eq_norm]
  have hbd : ‖(∫ x in W, f n x * ψ x) - ∫ x in W, f₀ x * ψ x‖ ≤ η / (C + 1) * C := by
    rw [← integral_sub (hf n) hf₀, hC, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hψ.norm.const_mul _) ?_
    filter_upwards [hn] with x hx
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  refine hbd.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

end Helpers

/-! ### Lower semicontinuity of the Dirichlet energy -/

section LSC

/-- **Lower semicontinuity of the Dirichlet energy**. Let `W` be open with finite measure,
`fₙ, f₀` with weak gradients `Fₙ, F₀` in `W`, `Fₙ ∈ L²(W)`, and `|fₙ - f₀| ≤ δ` a.e. on
`W` for large `n`, for every `δ > 0`. Then `∫_W |F₀|² ≤ liminf ∫_W |Fₙ|²`.

Proof: if not, a subsequence has `∫_W |Fₙ|² < c < ∫_W |F₀|²`; by weak compactness in `L²`
(gmt-foundations v0.1.0) a further subsequence converges weakly in `L²(W)` to some `g₀`, which is a
weak gradient of `f₀` (test against `φ e`, `φ ∈ C_c^∞(W)`), hence `g₀ = F₀` a.e.; weak lower
semicontinuity of the norm gives `∫_W |F₀|² ≤ c`. -/
theorem lintegral_norm_sq_le_liminf {W : Set (E d)} (hW : IsOpen W) (hWf : volume W ≠ ⊤)
    {f : ℕ → E d → ℝ} {F : ℕ → E d → E d} {f₀ : E d → ℝ} {F₀ : E d → E d}
    (hF : ∀ n, HasWeakGradient W (f n) (F n)) (hFL : ∀ n, MemLp (F n) 2 (volume.restrict W))
    (hF₀ : HasWeakGradient W f₀ F₀)
    (hconv : ∀ δ > 0, ∀ᶠ n in atTop, ∀ᵐ x ∂(volume.restrict W), |f n x - f₀ x| ≤ δ) :
    ∫⁻ x in W, ENNReal.ofReal (‖F₀ x‖ ^ 2) ≤
      liminf (fun n ↦ ∫⁻ x in W, ENNReal.ofReal (‖F n x‖ ^ 2)) atTop := by
  have : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.2 hWf
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  have hfreq := frequently_lt_of_liminf_lt (by isBoundedDefault) hc1
  obtain ⟨ψ, hψ, hψc⟩ := extraction_of_frequently_atTop hfreq
  have hctop : c ≠ ⊤ := ne_top_of_lt hc2
  -- `L²` bound along the subsequence
  have hbound : ∀ k, eLpNorm (F (ψ k)) 2 (volume.restrict W) ≤
      ENNReal.ofReal (c.toReal ^ (1 / (2 : ℝ))) := by
    intro k
    rw [eLpNorm_two_eq _ _ (hFL _).aestronglyMeasurable,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hctop]
    exact ENNReal.rpow_le_rpow (hψc k).le (by norm_num)
  obtain ⟨φ₂, hφ₂, g₀, hg₀⟩ := Registry.exists_tendstoWeakL2_subseq volume W
    (fun k ↦ F (ψ k)) _ (fun k ↦ hFL _) hbound
  have hnt : Tendsto (fun k ↦ ψ (φ₂ k)) atTop atTop := (hψ.comp hφ₂).tendsto_atTop
  -- identification of the weak limit
  have hg₀int : IntegrableOn g₀ W := hg₀.2.1.integrable one_le_two
  have hg₀W : HasWeakGradient W f₀ g₀ := by
    refine ⟨hF₀.1, hg₀int.locallyIntegrableOn, fun φ hφ hφc hφW v ↦ ?_⟩
    have hφ' : Continuous (fun x ↦ fderiv ℝ φ x v) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hφ'c : HasCompactSupport (fun x ↦ fderiv ℝ φ x v) := hφc.fderiv_apply (𝕜 := ℝ) v
    have hφ'W : tsupport (fun x ↦ fderiv ℝ φ x v) ⊆ W :=
      (tsupport_fderiv_apply_subset ℝ v).trans hφW
    have hlhs : Tendsto (fun k ↦ ∫ x in W, f (ψ (φ₂ k)) x * fderiv ℝ φ x v) atTop
        (𝓝 (∫ x in W, f₀ x * fderiv ℝ φ x v)) := by
      refine tendsto_setIntegral_mul_of_ae_bound
        (fun k ↦ integrableOn_mul_of_tsupport_subset hW (hF _).1 hφ' hφ'c hφ'W)
        (integrableOn_mul_of_tsupport_subset hW hF₀.1 hφ' hφ'c hφ'W)
        (hφ'.integrable_of_hasCompactSupport hφ'c).integrableOn
        fun δ hδ ↦ hnt.eventually (hconv δ hδ)
    have hrhs : Tendsto (fun k ↦ ∫ x in W, inner ℝ (F (ψ (φ₂ k)) x) v * φ x) atTop
        (𝓝 (∫ x in W, inner ℝ (g₀ x) v * φ x)) := by
      have htest : MemLp (fun x ↦ φ x • v) 2 (volume.restrict W) :=
        ((hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport
          (hφc.smul_right)).restrict _
      have h := hg₀.2.2 _ htest
      have e : ∀ G : E d → E d, (fun x ↦ inner ℝ (G x) (φ x • v)) =
          fun x ↦ inner ℝ (G x) v * φ x := fun G ↦ funext fun x ↦ by
        rw [real_inner_smul_right, mul_comm]
      simpa only [e] using h
    have heq : ∀ k, ∫ x in W, f (ψ (φ₂ k)) x * fderiv ℝ φ x v =
        -∫ x in W, inner ℝ (F (ψ (φ₂ k)) x) v * φ x := fun k ↦ (hF _).2.2 φ hφ hφc hφW v
    exact tendsto_nhds_unique hlhs (hrhs.neg.congr fun k ↦ (heq k).symm)
  have hae := HasWeakGradient.ae_eq_of_eqOn hW hW subset_rfl hg₀W hF₀ fun _ _ ↦ rfl
  have hlsc := Registry.lintegral_weighted_sq_le_liminf volume W _ g₀ hg₀ (fun _ ↦ (1 : ℝ))
    measurable_const (fun _ ↦ zero_le_one) 1 fun _ ↦ le_rfl
  simp only [one_mul] at hlsc
  have e1 : ∫⁻ x in W, ENNReal.ofReal (‖F₀ x‖ ^ 2) = ∫⁻ x in W, ENNReal.ofReal (‖g₀ x‖ ^ 2) :=
    lintegral_congr_ae (hae.mono fun x hx ↦ by simp only [hx])
  have hle : liminf (fun k ↦ ∫⁻ x in W, ENNReal.ofReal (‖F (ψ (φ₂ k)) x‖ ^ 2)) atTop ≤ c :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun k ↦ (hψc _).le)
  exact absurd ((e1 ▸ hlsc).trans hle) (not_le.2 hc2)

/-- Superadditivity of `liminf` in `ℝ≥0∞`. -/
theorem ennreal_liminf_add_le (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n ↦ u n + v n) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  have hmono : ∀ w : ℕ → ℝ≥0∞, Monotone fun n ↦ ⨅ i ≥ n, w i := fun w a b hab ↦
    biInf_mono fun i hi ↦ hab.trans hi
  rw [ENNReal.iSup_add_iSup_of_monotone (hmono u) (hmono v)]
  exact iSup_mono fun n ↦ le_iInf₂ fun i hi ↦ add_le_add (iInf₂_le i hi) (iInf₂_le i hi)

/-- Splitting `J_Q(f; W)` into its Dirichlet and its measure part. -/
theorem energyJ_eq_add {W : Set (E d)} {Q f : E d → ℝ} {G : E d → E d}
    (hG : AEStronglyMeasurable G (volume.restrict W)) :
    energyJ W Q f G = (∫⁻ x in W, ENNReal.ofReal (‖G x‖ ^ 2)) +
      ∫⁻ x in W, ENNReal.ofReal (Q x ^ 2 * (posSet f W).indicator 1 x) := by
  unfold energyJ
  have h : AEMeasurable (fun x ↦ ENNReal.ofReal (‖G x‖ ^ 2)) (volume.restrict W) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hG.norm.aemeasurable).pow_const 2)
  rw [← lintegral_add_left' h]
  refine lintegral_congr fun x ↦ ?_
  have h1 : 0 ≤ (posSet f W).indicator (1 : E d → ℝ) x :=
    indicator_nonneg (fun _ _ ↦ zero_le_one) x
  exact ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (sq_nonneg _) h1)

/-- **Fatou's lemma for the measure term.** If `Qₙ → Q` pointwise on `W` and a.e. on `W`,
`f₀(x) > 0` implies `fₙ(x) > 0` for large `n`, then
`∫_W Q² 1_{f₀ > 0} ≤ liminf ∫_W Qₙ² 1_{fₙ > 0}`. -/
theorem lintegral_indicator_le_liminf {W : Set (E d)} (hWm : MeasurableSet W)
    {f : ℕ → E d → ℝ} {f₀ : E d → ℝ} {Q : E d → ℝ} {Qn : ℕ → E d → ℝ}
    (hfm : ∀ n, AEMeasurable (f n) (volume.restrict W))
    (hQm : ∀ n, AEMeasurable (Qn n) (volume.restrict W))
    (hQconv : ∀ x ∈ W, Tendsto (fun n ↦ Qn n x) atTop (𝓝 (Q x)))
    (hpos : ∀ᵐ x ∂(volume.restrict W), 0 < f₀ x → ∀ᶠ n in atTop, 0 < f n x) :
    ∫⁻ x in W, ENNReal.ofReal (Q x ^ 2 * (posSet f₀ W).indicator 1 x) ≤
      liminf (fun n ↦ ∫⁻ x in W, ENNReal.ofReal (Qn n x ^ 2 * (posSet (f n) W).indicator 1 x))
        atTop := by
  refine le_trans ?_ (lintegral_liminf_le' fun n ↦ ?_)
  · refine lintegral_mono_ae ?_
    filter_upwards [hpos, ae_restrict_mem hWm] with x hx hxW
    by_cases h0 : 0 < f₀ x
    · have hin : x ∈ posSet f₀ W := ⟨hxW, h0⟩
      rw [indicator_of_mem hin, Pi.one_apply, mul_one]
      have hev : ∀ᶠ n in atTop, ENNReal.ofReal (Qn n x ^ 2) =
          ENNReal.ofReal (Qn n x ^ 2 * (posSet (f n) W).indicator 1 x) := by
        filter_upwards [hx h0] with n hn
        have hin' : x ∈ posSet (f n) W := ⟨hxW, hn⟩
        rw [indicator_of_mem hin', Pi.one_apply, mul_one]
      have ht : Tendsto (fun n ↦ ENNReal.ofReal (Qn n x ^ 2)) atTop
          (𝓝 (ENNReal.ofReal (Q x ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((hQconv x hxW).pow 2)
      rw [(ht.congr' hev).liminf_eq]
    · have hnot : x ∉ posSet f₀ W := fun h ↦ h0 h.2
      rw [indicator_of_notMem hnot, mul_zero, ENNReal.ofReal_zero]
      exact bot_le
  · have hs : NullMeasurableSet (posSet (f n) W) (volume.restrict W) :=
      hWm.nullMeasurableSet.inter ((hfm n).nullMeasurable measurableSet_Ioi)
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((hQm n).pow_const 2).mul (aemeasurable_const.indicator₀ hs))

/-- **Lower semicontinuity of `J`** along sequences as in `lintegral_norm_sq_le_liminf` and
`lintegral_indicator_le_liminf`. -/
theorem energyJ_le_liminf {W : Set (E d)} (hW : IsOpen W) (hWf : volume W ≠ ⊤)
    {f : ℕ → E d → ℝ} {F : ℕ → E d → E d} {f₀ : E d → ℝ} {F₀ : E d → E d}
    (hF : ∀ n, HasWeakGradient W (f n) (F n)) (hFL : ∀ n, MemLp (F n) 2 (volume.restrict W))
    (hF₀ : HasWeakGradient W f₀ F₀) (hF₀m : AEStronglyMeasurable F₀ (volume.restrict W))
    (hconv : ∀ δ > 0, ∀ᶠ n in atTop, ∀ᵐ x ∂(volume.restrict W), |f n x - f₀ x| ≤ δ)
    (hfm : ∀ n, AEMeasurable (f n) (volume.restrict W))
    {Q : E d → ℝ} {Qn : ℕ → E d → ℝ} (hQm : ∀ n, AEMeasurable (Qn n) (volume.restrict W))
    (hQconv : ∀ x ∈ W, Tendsto (fun n ↦ Qn n x) atTop (𝓝 (Q x)))
    (hpos : ∀ᵐ x ∂(volume.restrict W), 0 < f₀ x → ∀ᶠ n in atTop, 0 < f n x) :
    energyJ W Q f₀ F₀ ≤ liminf (fun n ↦ energyJ W (Qn n) (f n) (F n)) atTop := by
  rw [energyJ_eq_add hF₀m]
  simp_rw [energyJ_eq_add (hFL _).aestronglyMeasurable]
  refine le_trans (add_le_add (lintegral_norm_sq_le_liminf hW hWf hF hFL hF₀ hconv)
    (lintegral_indicator_le_liminf hW.measurableSet hfm hQm hQconv hpos)) ?_
  exact ennreal_liminf_add_le _ _

end LSC

/-! ### The lattice identity -/

section Lattice

theorem indicator_posSet_congr {V : Set (E d)} {f g : E d → ℝ} {x : E d} (hx : x ∈ V)
    (h : f x = g x) : (posSet f V).indicator (1 : E d → ℝ) x = (posSet g V).indicator 1 x := by
  by_cases hf : 0 < f x
  · have h1 : x ∈ posSet f V := ⟨hx, hf⟩
    have h2 : x ∈ posSet g V := ⟨hx, h ▸ hf⟩
    rw [indicator_of_mem h1, indicator_of_mem h2]
  · have h1 : x ∉ posSet f V := fun h' ↦ hf h'.2
    have h2 : x ∉ posSet g V := fun h' ↦ hf (h ▸ h'.2)
    rw [indicator_of_notMem h1, indicator_of_notMem h2]

/-- **Lattice inequality for `J`.** If at every point of `V` the pair of (value, gradient) data
`(f₁, G₁), (f₂, G₂)` is a permutation of `(g₁, H₁), (g₂, H₂)`, then
`J(f₁) + J(f₂) ≤ J(g₁) + J(g₂)` on `V` (equality holds; one inequality suffices and avoids a
measurability hypothesis on the `f`'s). Applied with `f₁ = max{v, u}`, `f₂ = min{v, u}`. -/
theorem energyJ_add_le_of_swap {V : Set (E d)} (hV : MeasurableSet V) {Q : E d → ℝ}
    {f₁ f₂ g₁ g₂ : E d → ℝ} {G₁ G₂ H₁ H₂ : E d → E d}
    (hswap : ∀ x ∈ V, (f₁ x = g₁ x ∧ G₁ x = H₁ x ∧ f₂ x = g₂ x ∧ G₂ x = H₂ x) ∨
      (f₁ x = g₂ x ∧ G₁ x = H₂ x ∧ f₂ x = g₁ x ∧ G₂ x = H₁ x))
    (hm : AEMeasurable (fun x ↦ ENNReal.ofReal (‖H₁ x‖ ^ 2 + Q x ^ 2 *
      (posSet g₁ V).indicator 1 x)) (volume.restrict V)) :
    energyJ V Q f₁ G₁ + energyJ V Q f₂ G₂ ≤ energyJ V Q g₁ H₁ + energyJ V Q g₂ H₂ := by
  unfold energyJ
  refine (le_lintegral_add _ _).trans (le_of_eq ?_)
  rw [← lintegral_add_left' hm]
  refine setLIntegral_congr_fun hV fun x hx ↦ ?_
  rcases hswap x hx with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · rw [indicator_posSet_congr hx h1, indicator_posSet_congr hx h3, h2, h4]
  · rw [indicator_posSet_congr hx h1, indicator_posSet_congr hx h3, h2, h4, add_comm]

end Lattice

/-! ### Shrinking annuli -/

section Annulus

/-- The radii `s_k = R - R / (k + 2) ∈ [R/2, R)`, `s_k → R`. -/
noncomputable def annRad (R : ℝ) (k : ℕ) : ℝ := R - R / ((k : ℝ) + 2)

theorem annRad_lt {R : ℝ} (hR : 0 < R) (k : ℕ) : annRad R k < R := by
  unfold annRad
  have : 0 < R / ((k : ℝ) + 2) := div_pos hR (by positivity)
  linarith

theorem half_le_annRad {R : ℝ} (hR : 0 < R) (k : ℕ) : R / 2 ≤ annRad R k := by
  unfold annRad
  have h2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [k.cast_nonneg (α := ℝ)]
  have : R / ((k : ℝ) + 2) ≤ R / 2 := div_le_div_of_nonneg_left hR.le (by norm_num) h2
  linarith

theorem annRad_mono {R : ℝ} (hR : 0 < R) : Monotone (annRad R) := by
  intro a b hab
  unfold annRad
  have ha : (0 : ℝ) < (a : ℝ) + 2 := by positivity
  have : R / ((b : ℝ) + 2) ≤ R / ((a : ℝ) + 2) :=
    div_le_div_of_nonneg_left hR.le ha (by exact_mod_cast Nat.add_le_add_right hab 2)
  linarith

theorem tendsto_annRad {R : ℝ} : Tendsto (annRad R) atTop (𝓝 R) := by
  have h : Tendsto (fun k : ℕ ↦ R / ((k : ℝ) + 2)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h' := (tendsto_const_nhds (x := R)).sub h
  rw [sub_zero] at h'
  exact h'

/-- `∫_{B_R \ B_{s_k}} g → 0` for `g` with finite integral on `B_R`. -/
theorem tendsto_lintegral_annulus {x : E d} {R : ℝ} (hR : 0 < R) {g : E d → ℝ≥0∞}
    (hg : ∫⁻ y in ball x R, g y ≠ ⊤) :
    Tendsto (fun k ↦ ∫⁻ y in ball x R \ ball x (annRad R k), g y) atTop (𝓝 0) := by
  set μ := volume.withDensity g
  have hμ : ∀ k, μ (ball x R \ ball x (annRad R k)) =
      ∫⁻ y in ball x R \ ball x (annRad R k), g y := fun k ↦
    withDensity_apply _ (measurableSet_ball.diff measurableSet_ball)
  have hanti : Antitone fun k ↦ ball x R \ ball x (annRad R k) := fun a b hab ↦
    Set.sdiff_subset_sdiff_right (ball_subset_ball (annRad_mono hR hab))
  have hfin : ∃ k, μ (ball x R \ ball x (annRad R k)) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    rw [hμ]
    exact ne_top_of_le_ne_top hg (lintegral_mono_set Set.sdiff_subset)
  have hempty : (⋂ k, ball x R \ ball x (annRad R k)) = ∅ := by
    refine eq_empty_of_forall_notMem fun y hy ↦ ?_
    have hyR : dist y x < R := (mem_iInter.1 hy 0).1
    obtain ⟨k, hk⟩ := (tendsto_order.1 tendsto_annRad).1 _ hyR |>.exists
    exact (mem_iInter.1 hy k).2 hk
  have := tendsto_measure_iInter_atTop (μ := μ)
    (fun k ↦ (measurableSet_ball.diff measurableSet_ball).nullMeasurableSet) hanti hfin
  rw [hempty, measure_empty] at this
  simpa only [Function.comp_def, hμ] using this

end Annulus

/-! ### The approximating sequence near a ball -/

section Data

/-- `∫ |G|² < ∞` for `G ∈ L²`. -/
theorem lintegral_norm_sq_ne_top {X : Type*} [MeasurableSpace X] {F : Type*}
    [NormedAddCommGroup F] {G : X → F} {μ : Measure X} (hG : MemLp G 2 μ) :
    ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μ ≠ ⊤ := by
  have h := hG.eLpNorm_lt_top
  rw [eLpNorm_two_eq _ _ hG.aestronglyMeasurable] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h |>.ne

/-- The data of Lemma 2.12 near a ball `B_R(x)`, with `B̄_t(x) ⊆ U`, `t > R`: functions `uₙ`
defined on open sets `Uₙ ⊇ B̄_t(x)`, locally Lipschitz on `Uₙ` with gradients bounded uniformly
on `B_t(x)`, converging uniformly on `B̄_R(x)` to `u`, and coefficients `Qₙ` continuous and bounded
on `B̄_R(x)`, converging pointwise to `Q`. (For Lemma 2.12 itself `Uₙ = U`; the general `Uₙ`
serve Corollary 2.13.) -/
structure StabData (U : Set (E d)) (x : E d) (R t : ℝ) (u Q : E d → ℝ) (un Qn : ℕ → E d → ℝ)
    (Un : ℕ → Set (E d)) (L : ℝ≥0) (Qmax : ℝ) : Prop where
  isOpen : IsOpen U
  pos : 0 < R
  lt : R < t
  subset : closedBall x t ⊆ U
  isOpen_n : ∀ n, IsOpen (Un n)
  subset_n : ∀ n, closedBall x t ⊆ Un n
  gradBd : ∀ n, ∀ y ∈ ball x t, ‖∇ (un n) y‖ ≤ L
  locLip : ∀ n, LocallyLipschitzOn (Un n) (un n)
  conv : TendstoUniformlyOn un u atTop (closedBall x R)
  Qcont : ∀ n, ContinuousOn (Qn n) (closedBall x R)
  Qbd : ∀ n, ∀ y ∈ closedBall x R, |Qn n y| ≤ Qmax
  Qconv : ∀ y ∈ closedBall x R, Tendsto (fun n ↦ Qn n y) atTop (𝓝 (Q y))

namespace StabData

variable {U : Set (E d)} {x : E d} {R t : ℝ} {u Q : E d → ℝ} {un Qn : ℕ → E d → ℝ}
  {Un : ℕ → Set (E d)} {L : ℝ≥0} {Qmax : ℝ}
  (D : StabData U x R t u Q un Qn Un L Qmax)
include D

theorem closedBall_subset_ball : closedBall x R ⊆ ball x t :=
  Metric.closedBall_subset_ball D.lt

theorem ball_subset : ball x t ⊆ U := ball_subset_closedBall.trans D.subset

theorem norm_gradient_le (n : ℕ) {y : E d} (hy : y ∈ ball x t) : ‖∇ (un n) y‖ ≤ L :=
  D.gradBd n y hy

theorem memH1Loc_n (n : ℕ) : MemH1Loc (Un n) (un n) (∇ (un n)) :=
  Registry.memH1Loc_gradient_of_locallyLipschitzOn (D.isOpen_n n) (D.locLip n)

theorem memH1Loc_ball (n : ℕ) : MemH1Loc (ball x t) (un n) (∇ (un n)) :=
  memH1Loc_mono (D.memH1Loc_n n) (ball_subset_closedBall.trans (D.subset_n n))

theorem abs_Q_le {y : E d} (hy : y ∈ closedBall x R) : |Q y| ≤ Qmax :=
  le_of_tendsto' ((continuous_abs.tendsto _).comp (D.Qconv y hy)) fun n ↦ D.Qbd n y hy

theorem eventually_abs_sub_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ y ∈ closedBall x R, |un n y - u y| ≤ δ := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 D.conv δ hδ] with n hn y hy
  rw [abs_sub_comm, ← Real.dist_eq]
  exact (hn y hy).le

theorem eventually_pos {y : E d} (hy : y ∈ closedBall x R) (hu : 0 < u y) :
    ∀ᶠ n in atTop, 0 < un n y := by
  filter_upwards [D.eventually_abs_sub_le (half_pos hu)] with n hn
  have := hn y hy
  rw [abs_le] at this
  linarith

theorem continuousOn_n (n : ℕ) : ContinuousOn (un n) (ball x t) :=
  (D.locLip n).continuousOn.mono (ball_subset_closedBall.trans (D.subset_n n))

end StabData

end Data

/-! ### The competitors -/

section Competitor

/-- The downward competitor `vₙ = uₙ - φ (uₙ - v)₊ = φ min{v, uₙ} + (1 - φ) uₙ`. -/
noncomputable def downComp (w v φ : E d → ℝ) : E d → ℝ := fun y ↦ w y - φ y * max (w y - v y) 0

/-- The weak gradient of `downComp`. -/
noncomputable def downCompGrad (w v φ : E d → ℝ) (Gv : E d → E d) : E d → E d := fun y ↦
  ∇ w y - (φ y • {y | 0 < w y - v y}.indicator (fun y ↦ ∇ w y - Gv y) y +
    max (w y - v y) 0 • ∇ φ y)

/-- The upward competitor `vₙ = uₙ + φ (v - uₙ)₊ = φ max{v, uₙ} + (1 - φ) uₙ`. -/
noncomputable def upComp (w v φ : E d → ℝ) : E d → ℝ := fun y ↦ w y + φ y * max (v y - w y) 0

/-- The weak gradient of `upComp`. -/
noncomputable def upCompGrad (w v φ : E d → ℝ) (Gv : E d → E d) : E d → E d := fun y ↦
  ∇ w y + (φ y • {y | 0 < v y - w y}.indicator (fun y ↦ Gv y - ∇ w y) y +
    max (v y - w y) 0 • ∇ φ y)

variable {U : Set (E d)} {x : E d} {R t : ℝ} {u Q : E d → ℝ} {un Qn : ℕ → E d → ℝ}
  {Un : ℕ → Set (E d)} {L : ℝ≥0} {Qmax : ℝ}

/-- A cut-off product supported in `B_R(x)`, in `H¹_loc(B_t(x))`, is in `H¹_loc(Uₙ)`. -/
theorem memH1Loc_of_vanish (D : StabData U x R t u Q un Qn Un L Qmax) (n : ℕ)
    {g : E d → ℝ} {Gg : E d → E d} (hg : MemH1Loc (ball x t) g Gg)
    (hg0 : ∀ y ∉ ball x R, g y = 0) (hG0 : ∀ y ∉ ball x R, Gg y = 0) : MemH1Loc (Un n) g Gg := by
  have hRt := D.lt
  have hsub : closedBall x ((R + t) / 2) ⊆ ball x t := Metric.closedBall_subset_ball (by linarith)
  have hwu : HasWeakGradient univ g Gg :=
    hg.1.univ_of_vanish D.pos.le (by linarith) hsub hg0 hG0
  have hK := hg.2 _ D.closedBall_subset_ball (isCompact_closedBall x R)
  have hout : ∀ y ∉ closedBall x R, y ∉ ball x R := fun y hy h ↦ hy (ball_subset_closedBall h)
  have hgL : MemLp g 2 volume := GMTFoundations.memLp_of_vanish hK.1 fun y hy ↦ hg0 y (hout y hy)
  have hGL : MemLp Gg 2 volume := GMTFoundations.memLp_of_vanish hK.2 fun y hy ↦ hG0 y (hout y hy)
  exact ⟨hasWeakGradient_mono hwu (subset_univ _), fun K _ _ ↦ ⟨hgL.restrict K, hGL.restrict K⟩⟩

/-- Cutoff hypotheses: `φ` smooth, vanishing with its gradient outside `B_R(x)`. -/
theorem downComp_memH1Loc (D : StabData U x R t u Q un Qn Un L Qmax) {v : E d → ℝ}
    {Gv : E d → E d} (hv : MemH1Loc U v Gv) {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : ∀ y ∉ ball x R, φ y = 0 ∧ ∇ φ y = 0) (n : ℕ) :
    MemH1Loc (Un n) (downComp (un n) v φ) (downCompGrad (un n) v φ Gv) := by
  have h1 := (D.memH1Loc_ball n).sub (memH1Loc_mono hv D.ball_subset)
  have h3 := (memH1Loc_posPart isOpen_ball h1).mul_smooth isOpen_ball hφ
  refine (D.memH1Loc_n n).sub (memH1Loc_of_vanish D n h3 (fun y hy ↦ ?_) fun y hy ↦ ?_)
  · simp [(hφ0 y hy).1]
  · simp [(hφ0 y hy).1, (hφ0 y hy).2]

theorem upComp_memH1Loc (D : StabData U x R t u Q un Qn Un L Qmax) {v : E d → ℝ}
    {Gv : E d → E d} (hv : MemH1Loc U v Gv) {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : ∀ y ∉ ball x R, φ y = 0 ∧ ∇ φ y = 0) (n : ℕ) :
    MemH1Loc (Un n) (upComp (un n) v φ) (upCompGrad (un n) v φ Gv) := by
  have h1 := (memH1Loc_mono hv D.ball_subset).sub (D.memH1Loc_ball n)
  have h3 := (memH1Loc_posPart isOpen_ball h1).mul_smooth isOpen_ball hφ
  refine (D.memH1Loc_n n).add (memH1Loc_of_vanish D n h3 (fun y hy ↦ ?_) fun y hy ↦ ?_)
  · simp [(hφ0 y hy).1]
  · simp [(hφ0 y hy).1, (hφ0 y hy).2]

end Competitor

/-! ### The energy on the annulus -/

section AnnulusEnergy

/-- Real-variable form of the cutoff estimate. -/
theorem annulus_real_bound {N a L g z M w δ q Qmax : ℝ} (hN0 : 0 ≤ N)
    (hN : N ≤ 2 * a + g + z * M) (ha : 0 ≤ a) (haL : a ≤ L) (hz : 0 ≤ z)
    (hM : 0 ≤ M) (hzw : z ≤ w + δ) (hMδ : M * δ ≤ 1)
    (hq : q ≤ Qmax ^ 2) :
    N ^ 2 + q ≤ (12 * L ^ 2 + Qmax ^ 2 + 6) + 3 * g ^ 2 + 6 * M ^ 2 * w ^ 2 := by
  have h1 : N ^ 2 ≤ (2 * a + g + z * M) ^ 2 := pow_le_pow_left₀ hN0 hN 2
  have h2 : (2 * a + g + z * M) ^ 2 ≤ 3 * ((2 * a) ^ 2 + g ^ 2 + (z * M) ^ 2) := by
    nlinarith [sq_nonneg (2 * a - g), sq_nonneg (2 * a - z * M), sq_nonneg (g - z * M)]
  have hzM : z * M ≤ w * M + 1 := by nlinarith
  have hzM0 : 0 ≤ z * M := mul_nonneg hz hM
  have h3 : (z * M) ^ 2 ≤ 2 * (w * M) ^ 2 + 2 := by
    have := pow_le_pow_left₀ hzM0 hzM 2
    nlinarith [sq_nonneg (w * M - 1)]
  have h4 : a ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ ha haL 2
  nlinarith

/-- Pointwise bound of the competitor gradient `∇w ∓ (φ c + z ∇φ)` with `‖c‖ ≤ ‖∇w‖ + ‖Gv‖`. -/
theorem norm_comp_grad_le {a b c e p : E d} {φ z : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hz : 0 ≤ z)
    (hc : ‖c‖ ≤ ‖a‖ + ‖b‖) (he : e = a - (φ • c + z • p) ∨ e = a + (φ • c + z • p)) :
    ‖e‖ ≤ 2 * ‖a‖ + ‖b‖ + z * ‖p‖ := by
  have hc' : ‖φ • c‖ ≤ ‖a‖ + ‖b‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hφ0]
    nlinarith [norm_nonneg c]
  have hz' : ‖z • p‖ = z * ‖p‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hz]
  have hs : ‖φ • c + z • p‖ ≤ ‖a‖ + ‖b‖ + z * ‖p‖ := (norm_add_le _ _).trans (by rw [hz']; linarith)
  rcases he with he | he <;> rw [he]
  · linarith [norm_sub_le a (φ • c + z • p)]
  · linarith [norm_add_le a (φ • c + z • p)]

/-- Integrated form of the annulus estimate. -/
theorem energyJ_le_of_pointwise {A : Set (E d)} {q w h : E d → ℝ} {Gw Gv : E d → E d}
    (hGv : AEStronglyMeasurable Gv (volume.restrict A)) (hh : AEMeasurable h (volume.restrict A))
    {c₀ κ : ℝ} (hc₀ : 0 ≤ c₀) (hκ : 0 ≤ κ)
    (hpt : ∀ᵐ y ∂(volume.restrict A), ‖Gw y‖ ^ 2 + q y ^ 2 * (posSet w A).indicator 1 y ≤
      c₀ + 3 * ‖Gv y‖ ^ 2 + κ * h y ^ 2) :
    energyJ A q w Gw ≤ (∫⁻ _ in A, ENNReal.ofReal c₀) +
      (∫⁻ y in A, ENNReal.ofReal (3 * ‖Gv y‖ ^ 2)) +
        ENNReal.ofReal κ * ∫⁻ y in A, ENNReal.ofReal (h y ^ 2) := by
  have hm1 : AEMeasurable (fun y ↦ ENNReal.ofReal (3 * ‖Gv y‖ ^ 2)) (volume.restrict A) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hGv.norm.aemeasurable.pow_const 2).const_mul 3)
  have hm2 : AEMeasurable (fun y ↦ ENNReal.ofReal (h y ^ 2)) (volume.restrict A) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hh.pow_const 2)
  calc energyJ A q w Gw ≤ ∫⁻ y in A, (ENNReal.ofReal c₀ + ENNReal.ofReal (3 * ‖Gv y‖ ^ 2) +
        ENNReal.ofReal κ * ENNReal.ofReal (h y ^ 2)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt] with y hy
        rw [← ENNReal.ofReal_mul hκ, ← ENNReal.ofReal_add hc₀ (by positivity),
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg hκ (sq_nonneg _))]
        exact ENNReal.ofReal_le_ofReal hy
    _ = _ := by
        rw [lintegral_add_right' _ (hm2.const_mul _), lintegral_add_right' _ hm1,
          lintegral_const_mul'' _ hm2]

end AnnulusEnergy

end DirectionalStable

end PerronVariational

end
