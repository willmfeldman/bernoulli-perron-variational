/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.ProfileSuper
public import PerronVariational.Defs.Stationary
public import PerronVariational.Semilinear.Profiles
import PerronVariational.Semilinear.Calculus

/-!
# Well-prepared data (Lemma A.4)

Lemma A.4 of F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal
solutions in the Bernoulli one-phase problem*, arXiv:2609.14981.

For a smooth strict subsolution (resp. supersolution) `g` (Definition 2.2, with parameters
`a₀, δ₀`), `θ = 1/(1 + δ₀)` (resp. `θ̂ = 1/(1 - δ₀)`) and

  `g_ε = (Φ_{ε,θ}(g))₊`   (resp. `g_ε = Ψ_{ε,θ̂}(g)`),

there is `ε₀ > 0`, depending only on the listed parameters, such that for `ε ∈ (0, ε₀]` the five
items of Lemma A.4 hold. The statements quantify `ε₀` *before* the data `(U, Q, g)`, which makes
the dependence of `ε₀` explicit: on `(a₀, δ₀, β)` in the subsolution case, and on
`(a₀, δ₀, Q_min, β, L, D)` with `|∇g| ≤ L`, `|Δg| ≤ D` on `U` in the supersolution case
(the paper: `‖g‖_{C²(Ū)}`).

Conventions and deviations:
* Item (i): the gradient bound is proved pointwise everywhere, `|∇g_ε(x)| ≤ |∇g(x)|` (with the
  convention `∇f(x) = 0` where `f` is not differentiable), which implies the `L^∞` bound; the
  Lipschitz property is: every Lipschitz constant of `g` on `Ū` is one for `g_ε`.
* Item (ii) holds on all of `ℝᵈ`.
* Item (iii), subsolution case: the viscosity inequality is stated for `C²` test functions
  touching from above in `U` (the stationary semilinear viscosity notion, inlined).
  Supersolution case: `g_ε ∈ C²` and the classical inequality `Δg_ε ≤ Q² β_ε(g_ε)` in `U`, plus
  the corresponding viscosity form (test functions touching from below).
* Item (iv): `E₀ = ∫_U (|∇g|² + Q_max²)`.
* Case 2 of the paper's supersolution proof uses `|∇g|² ≤ Q² - δ₀`, whereas Definition 2.2 gives
  `|∇g|² ≤ (1 - δ₀)Q²`; here we use Definition 2.2 as written, with `θ̂ = 1/(1 - δ₀)`, and the
  computation goes through. The paper leaves `δ₀ < 1` implicit; we assume it (WLOG, since
  `δ₀ ≥ 1` forces `∇g = 0` on `{|g| ≤ a₀}`, and the wrapper `exists_wellPrepared_super` shrinks
  `δ₀`).
* The supersolution proof's case split is `g > -a₀` / `g ≤ -a₀` (the paper's `-a₀ ≤ g < ε` uses
  `Δg ≤ 0` at `g = -a₀`, where Definition 2.2 gives no information; the exponential case covers
  it).
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff Gradient Laplacian ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- The subsolution well-prepared datum `g_ε = (Φ_{ε,θ}(g))₊`, `θ = 1/(1 + δ₀)`. -/
noncomputable def wellPreparedSubData (β : ℝ → ℝ) (δ₀ ε : ℝ) (g : E d → ℝ) : E d → ℝ :=
  fun x ↦ max (profileSubEps β (1 / (1 + δ₀)) ε (g x)) 0

/-- The supersolution well-prepared datum `g_ε = Ψ_{ε,θ̂}(g)`, `θ̂ = 1/(1 - δ₀)`. -/
noncomputable def wellPreparedSuperData (β : ℝ → ℝ) (δ₀ ε : ℝ) (g : E d → ℝ) : E d → ℝ :=
  fun x ↦ profileSuperEps β (1 / (1 - δ₀)) ε (g x)

/-- The conclusions of **Lemma A.4** in the subsolution case, for
`g_ε` with zero level `s₀` of the profile and constant `c_θ`. -/
structure IsWellPreparedSub (U : Set (E d)) (Q : E d → ℝ) (β : ℝ → ℝ) (ε Qmax : ℝ)
    (g gε : E d → ℝ) (s₀ cθ : ℝ) : Prop where
  /-- (i) Lipschitz constants of `g` on `Ū` are Lipschitz constants of `g_ε`. -/
  lipschitz : ∀ K, LipschitzOnWith K g (closure U) → LipschitzOnWith K gε (closure U)
  /-- (i) `|∇g_ε| ≤ |∇g|` pointwise. -/
  norm_gradient_le : ∀ x, ‖∇ gε x‖ ≤ ‖∇ g x‖
  /-- (i) `g_ε = g` on `{g ≥ ε}`. -/
  eq_of_le : ∀ x, ε ≤ g x → gε x = g x
  /-- (ii) `g₊ ≤ g_ε ≤ g₊ + ε`. -/
  bounds : ∀ x, max (g x) 0 ≤ gε x ∧ gε x ≤ max (g x) 0 + ε
  /-- (iii) `g_ε` is a viscosity subsolution of `Δv = Q² β_ε(v)` in `U`. -/
  viscSub : ContinuousOn gε U ∧ ∀ ψ : E d → ℝ, ContDiff ℝ 2 ψ → ∀ x ∈ U,
    TouchesAbove ψ gε U x → Q x ^ 2 * betaEps β ε (gε x) ≤ Δ ψ x
  /-- (iv) `J(g_ε, 2𝓑_ε(g_ε); U) ≤ E₀`. -/
  energy : energyJχ U Q (∇ gε) (fun x ↦ 2 * bigBEps β ε (gε x)) ≤
    ∫⁻ x in U, ENNReal.ofReal (‖∇ g x‖ ^ 2 + Qmax ^ 2)
  /-- (v) `{g_ε > 0} = {g > ε s₀}`. -/
  pos_iff : ∀ x, 0 < gε x ↔ ε * s₀ < g x
  /-- (v) `ε s₀ ∈ [-c_θ ε, 0]`. -/
  s₀_mem : s₀ ∈ Icc (-cθ) 0
  /-- (v) `{g > 0} ⊆ {g_ε > 0} ⊆ {g > -c_θ ε}`. -/
  pos_subset : ∀ x, 0 < g x → 0 < gε x
  subset_pos : ∀ x, 0 < gε x → -(cθ * ε) < g x

/-- The conclusions of **Lemma A.4** in the supersolution case. -/
structure IsWellPreparedSuper (U : Set (E d)) (Q : E d → ℝ) (β : ℝ → ℝ) (ε Qmax : ℝ)
    (g gε : E d → ℝ) (κ : ℝ) : Prop where
  /-- (i) Lipschitz constants of `g` on `Ū` are Lipschitz constants of `g_ε`. -/
  lipschitz : ∀ K, LipschitzOnWith K g (closure U) → LipschitzOnWith K gε (closure U)
  /-- (i) `|∇g_ε| ≤ |∇g|` pointwise. -/
  norm_gradient_le : ∀ x, ‖∇ gε x‖ ≤ ‖∇ g x‖
  /-- (i) `g_ε = g` on `{g ≥ ε}`. -/
  eq_of_le : ∀ x, ε ≤ g x → gε x = g x
  /-- (ii) `g₊ ≤ g_ε ≤ g₊ + ε`. -/
  bounds : ∀ x, max (g x) 0 ≤ gε x ∧ gε x ≤ max (g x) 0 + ε
  /-- (iii) `g_ε ∈ C²` is a classical supersolution of `Δv = Q² β_ε(v)` in `U`. -/
  classicalSuper : ContDiffOn ℝ 2 gε U ∧ ∀ x ∈ U, Δ gε x ≤ Q x ^ 2 * betaEps β ε (gε x)
  /-- (iii) the viscosity form: `C²` test functions touching from below. -/
  viscSuper : ∀ ψ : E d → ℝ, ContDiff ℝ 2 ψ → ∀ x ∈ U,
    TouchesBelow ψ gε U x → Δ ψ x ≤ Q x ^ 2 * betaEps β ε (gε x)
  /-- (iv) `J(g_ε, 2𝓑_ε(g_ε); U) ≤ E₀`. -/
  energy : energyJχ U Q (∇ gε) (fun x ↦ 2 * bigBEps β ε (gε x)) ≤
    ∫⁻ x in U, ENNReal.ofReal (‖∇ g x‖ ^ 2 + Qmax ^ 2)
  /-- `g_ε > ε κ > 0`. -/
  kappa_lt : ∀ x, ε * κ < gε x

/-! ### Common lemmas -/

/-- The energy estimate (iv), from `|∇g_ε| ≤ |∇g|`, `0 ≤ 2𝓑_ε ≤ 1` and `|Q| ≤ Q_max`. -/
theorem energyJχ_le_of_norm_gradient_le {β : ℝ → ℝ} (hβ : IsReactionProfile β) {U : Set (E d)}
    (hU : MeasurableSet U) {Q g gε : E d → ℝ} {ε Qmax : ℝ} (hε : 0 < ε)
    (hQ : ∀ x ∈ U, |Q x| ≤ Qmax) (hgrad : ∀ x, ‖∇ gε x‖ ≤ ‖∇ g x‖) :
    energyJχ U Q (∇ gε) (fun x ↦ 2 * bigBEps β ε (gε x)) ≤
      ∫⁻ x in U, ENNReal.ofReal (‖∇ g x‖ ^ 2 + Qmax ^ 2) := by
  refine setLIntegral_mono' hU fun x hx ↦ ENNReal.ofReal_le_ofReal ?_
  have h1 : ‖∇ gε x‖ ^ 2 ≤ ‖∇ g x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hgrad x) 2
  have h2 := hβ.bigBEps_nonneg hε.ne' (gε x)
  have h3 := hβ.bigBEps_le_half hε.ne' (gε x)
  have h4 : Q x ^ 2 ≤ Qmax ^ 2 := by
    have := hQ x hx
    have h0 : 0 ≤ Qmax := (abs_nonneg _).trans this
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h5 : Q x ^ 2 * (2 * bigBEps β ε (gε x)) ≤ Q x ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg _) (by linarith)
  linarith

/-- Gradient of a composition `f ∘ g` with `|f'| ≤ 1`. -/
theorem norm_gradient_comp_le {f : ℝ → ℝ} {g : E d → ℝ} {x : E d}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) (hf1 : |deriv f (g x)| ≤ 1) :
    ‖∇ (fun y ↦ f (g y)) x‖ ≤ ‖∇ g x‖ := by
  have h : HasFDerivAt (fun y ↦ f (g y)) (deriv f (g x) • fderiv ℝ g x) x :=
    hf.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt
  rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv, h.fderiv, norm_smul,
    Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) hf1

/-- `e^{-y} ≤ 1/y` for `y > 0`, in the form `exp(-c a₀/ε) ≤ ε/(c a₀)`. -/
theorem exp_neg_div_le {c a ε : ℝ} (hc : 0 < c) (ha : 0 < a) (hε : 0 < ε) :
    Real.exp (-(c * a / ε)) ≤ ε / (c * a) := by
  have hy : 0 < c * a / ε := by positivity
  have h1 := Real.add_one_le_exp (c * a / ε)
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  linarith

/-! ### Lemma A.4, subsolution case -/

/-- **Lemma A.4**, subsolution case. Given `a₀, δ₀ > 0` there is
`ε₀ = a₀/(1 + c_θ) > 0` (`θ = 1/(1 + δ₀)`) such that for every open `U`, every `g ∈ C²` satisfying
the strict subsolution conditions of Definition 2.2 with parameters `a₀, δ₀`, every `Q` with
`|Q| ≤ Q_max` on `U`, and every `ε ∈ (0, ε₀]`, the datum `g_ε = (Φ_{ε,θ}(g))₊` satisfies
(i)–(v). -/
theorem wellPrepared_sub {β : ℝ → ℝ} (hβ : IsReactionProfile β) {a₀ δ₀ Qmax : ℝ}
    (ha₀ : 0 < a₀) (hδ₀ : 0 < δ₀) :
    ∃ ε₀ > 0, ∀ {d : ℕ} (U : Set (E d)) (Q g : E d → ℝ), IsOpen U → ContDiff ℝ 2 g →
      (∀ x ∈ closure U, -a₀ < g x → 0 ≤ Δ g x) →
      (∀ x ∈ closure U, |g x| ≤ a₀ → (1 + δ₀) * Q x ^ 2 ≤ ‖∇ g x‖ ^ 2) →
      (∀ x ∈ U, |Q x| ≤ Qmax) →
      ∀ ε ∈ Ioc 0 ε₀, IsWellPreparedSub U Q β ε Qmax g (wellPreparedSubData β δ₀ ε g)
        (profileSubZero β (1 / (1 + δ₀))) (subConst (1 / (1 + δ₀))) := by
  set θ := 1 / (1 + δ₀) with hθ_def
  have hθ : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ_def, div_lt_one (by linarith)]; linarith
  have hθδ : θ * (1 + δ₀) = 1 := by rw [hθ_def]; field_simp
  set c := subConst θ with hc_def
  have hc : 0 ≤ c := subConst_nonneg hθ hθ1
  have hs₀ := profileSubZero_mem hβ hθ hθ1
  set s₀ := profileSubZero β θ with hs₀_def
  refine ⟨a₀ / (1 + c), div_pos ha₀ (by linarith), ?_⟩
  intro d U Q g hU hg hΔ hgrad hQ ε hε
  obtain ⟨hε0, hεle⟩ := hε
  have hε1 : ε * (1 + c) ≤ a₀ := (le_div_iff₀ (by linarith)).1 hεle
  have hεa : ε ≤ a₀ := by nlinarith
  have hcε : c * ε < a₀ := by nlinarith
  have hεs₀ : -(c * ε) ≤ ε * s₀ := by nlinarith [hs₀.1]
  have hεs₀' : ε * s₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε0.le hs₀.2
  set gε := wellPreparedSubData β δ₀ ε g with hgε_def
  have hgε : ∀ x, gε x = max (profileSubEps β θ ε (g x)) 0 := fun x ↦ rfl
  have hΦc : ContDiff ℝ 2 (profileSubEps β θ ε) :=
    (profileSubEps_contDiff hβ hθ hθ1).of_le (WithTop.coe_le_coe.2 le_top)
  have hΦgc : Continuous fun y ↦ profileSubEps β θ ε (g y) :=
    (profileSubEps_continuous hβ hθ hθ1).comp hg.continuous
  have hcont : Continuous gε := hΦgc.max continuous_const
  have hloc : ∀ x, 0 < profileSubEps β θ ε (g x) →
      gε =ᶠ[𝓝 x] fun y ↦ profileSubEps β θ ε (g y) := by
    intro x hx
    filter_upwards [hΦgc.continuousAt.eventually (lt_mem_nhds hx)] with y hy
    exact max_eq_left hy.le
  have hgrad_le : ∀ x, ‖∇ gε x‖ ≤ ‖∇ g x‖ := by
    intro x
    rcases lt_or_ge 0 (profileSubEps β θ ε (g x)) with hpos | hnp
    · rw [norm_gradient_eq_norm_fderiv, (hloc x hpos).fderiv_eq, ← norm_gradient_eq_norm_fderiv]
      refine norm_gradient_comp_le (hΦc.differentiable (by norm_num) _)
        (hg.differentiable (by norm_num) x) ?_
      obtain ⟨h1, h2⟩ := profileSubEps_deriv_mem hβ hθ hθ1 hε0 (g x)
      rw [abs_of_pos h1]; exact h2
    · have hmin : IsLocalMin gε x := Eventually.of_forall fun y ↦ by
        change gε x ≤ gε y
        rw [hgε, hgε, max_eq_right hnp]; exact le_max_right _ _
      rw [norm_gradient_eq_norm_fderiv, hmin.fderiv_eq_zero, norm_zero]; exact norm_nonneg _
  refine
    { lipschitz := ?_
      norm_gradient_le := hgrad_le
      eq_of_le := ?_
      bounds := ?_
      viscSub := ⟨hcont.continuousOn, ?_⟩
      energy := energyJχ_le_of_norm_gradient_le hβ hU.measurableSet hε0 hQ hgrad_le
      pos_iff := ?_
      s₀_mem := hs₀
      pos_subset := ?_
      subset_pos := ?_ }
  · intro K hK
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    rw [Real.dist_eq, hgε, hgε]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    refine (abs_profileSubEps_sub_le hβ hθ hθ1 hε0 (g y) (g x)).trans ?_
    rw [← Real.dist_eq]; exact hK.dist_le_mul x hx y hy
  · intro x hx
    rw [hgε, profileSubEps_of_le hβ hθ hθ1 hε0 hx, max_eq_left (hε0.le.trans hx)]
  · intro x
    rw [hgε]
    refine ⟨max_le_max (self_le_profileSubEps hβ hθ hθ1 hε0 _) le_rfl, ?_⟩
    have := (abs_le.1 (abs_max_profileSubEps_sub_le hβ hθ hθ1 hε0 (g x))).2
    linarith
  · intro ψ hψ x hxU ht
    obtain ⟨-, hψx, hle⟩ := ht
    rw [hU.nhdsWithin_eq hxU] at hle
    rcases lt_or_ge 0 (profileSubEps β θ ε (g x)) with hpos | hnp
    · have hgεx : gε x = profileSubEps β θ ε (g x) := max_eq_left hpos.le
      have hle' : ∀ᶠ y in 𝓝 x, profileSubEps β θ ε (g y) ≤ ψ y := by
        filter_upwards [hle, hloc x hpos] with y h1 h2
        rw [← h2]; exact h1
      have hcomp := laplacian_le_of_eventually_le (u := fun y ↦ profileSubEps β θ ε (g y))
        (hΦc.comp hg).contDiffAt hψ.contDiffAt (by rw [hψx, hgεx]) hle'
      rw [laplacian_comp hΦc.contDiffAt hg.contDiffAt,
        profileSubEps_deriv_deriv hβ hθ hθ1 hε0] at hcomp
      rw [hgεx]
      refine le_trans ?_ hcomp
      have hgx : ε * s₀ < g x := (profileSubEps_pos_iff hβ hθ hθ1 hε0 _).1 hpos
      have hga : -a₀ < g x := by linarith
      have hΔx := hΔ x (subset_closure hxU) hga
      have hd := (profileSubEps_deriv_mem hβ hθ hθ1 hε0 (g x)).1
      have hterm2 : 0 ≤ deriv (profileSubEps β θ ε) (g x) * Δ g x := mul_nonneg hd.le hΔx
      have hB := hβ.betaEps_nonneg ε (profileSubEps β θ ε (g x)) hε0.le
      rcases hB.eq_or_lt with h0 | hpos'
      · rw [← h0]; simp only [mul_zero, zero_mul]; linarith
      · obtain ⟨h1, h2⟩ := mem_of_betaEps_profileSubEps_pos hβ hθ hθ1 hε0 hpos'
        have habs : |g x| ≤ a₀ := abs_le.2 ⟨by linarith, by linarith⟩
        have hG := hgrad x (subset_closure hxU) habs
        have hθB : 0 ≤ θ * betaEps β ε (profileSubEps β θ ε (g x)) := mul_nonneg hθ.le hB
        have h3 : θ * betaEps β ε (profileSubEps β θ ε (g x)) * ((1 + δ₀) * Q x ^ 2) ≤
            θ * betaEps β ε (profileSubEps β θ ε (g x)) * ‖∇ g x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hG hθB
        have h4 : θ * betaEps β ε (profileSubEps β θ ε (g x)) * ((1 + δ₀) * Q x ^ 2) =
            Q x ^ 2 * betaEps β ε (profileSubEps β θ ε (g x)) := by
          calc _ = θ * (1 + δ₀) * (Q x ^ 2 * betaEps β ε (profileSubEps β θ ε (g x))) := by ring
            _ = _ := by rw [hθδ, one_mul]
        linarith
    · have hgεx : gε x = 0 := max_eq_right hnp
      rw [hgεx, hβ.betaEps_zero, mul_zero]
      have hmin : IsLocalMin ψ x := by
        filter_upwards [hle] with y hy
        rw [hψx, hgεx]; exact (le_max_right _ _).trans hy
      exact laplacian_nonneg_of_isLocalMin hmin hψ.contDiffAt
  · intro x
    rw [hgε, lt_max_iff, lt_self_iff_false, or_false]
    exact profileSubEps_pos_iff hβ hθ hθ1 hε0 _
  · intro x hx
    rw [hgε, lt_max_iff]
    exact Or.inl ((profileSubEps_pos_iff hβ hθ hθ1 hε0 _).2 (by linarith))
  · intro x hx
    rw [hgε, lt_max_iff, lt_self_iff_false, or_false,
      profileSubEps_pos_iff hβ hθ hθ1 hε0] at hx
    linarith

/-! ### Lemma A.4, supersolution case -/

/-- **Lemma A.4**, supersolution case. Given `a₀ > 0`,
`δ₀ ∈ (0, 1)`, `Q_min > 0`, and bounds `L, D`, there is `ε₀ > 0` (depending only on these and
`β`) such that for every open `U`, every `g ∈ C²` satisfying the strict supersolution
conditions of Definition 2.2 with parameters `a₀, δ₀` and `|∇g| ≤ L`, `|Δg| ≤ D` on `U`, every
`Q` with `Q_min ≤ Q`, `|Q| ≤ Q_max` on `U`, and every `ε ∈ (0, ε₀]`, the datum `g_ε = Ψ_{ε,θ̂}(g)`
(`θ̂ = 1/(1 - δ₀)`) satisfies (i)–(iv) and `g_ε > εκ`. -/
theorem wellPrepared_super {β : ℝ → ℝ} (hβ : IsReactionProfile β) {a₀ δ₀ Qmin Qmax L D : ℝ}
    (ha₀ : 0 < a₀) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1) (hQmin : 0 < Qmin) :
    ∃ ε₀ > 0, ∀ {d : ℕ} (U : Set (E d)) (Q g : E d → ℝ), IsOpen U → ContDiff ℝ 2 g →
      (∀ x ∈ closure U, -a₀ < g x → Δ g x ≤ 0) →
      (∀ x ∈ closure U, |g x| ≤ a₀ → ‖∇ g x‖ ^ 2 ≤ (1 - δ₀) * Q x ^ 2) →
      (∀ x ∈ U, Qmin ≤ Q x ∧ |Q x| ≤ Qmax) →
      (∀ x ∈ U, ‖∇ g x‖ ≤ L) → (∀ x ∈ U, |Δ g x| ≤ D) →
      ∀ ε ∈ Ioc 0 ε₀, IsWellPreparedSuper U Q β ε Qmax g (wellPreparedSuperData β δ₀ ε g)
        (superKappa β (1 / (1 - δ₀))) := by
  set θh := 1 / (1 - δ₀) with hθh_def
  have hθh : 1 < θh := by rw [hθh_def, one_lt_div (by linarith)]; linarith
  have hθδ : θh * (1 - δ₀) = 1 := by rw [hθh_def]; field_simp [(by linarith : (1 - δ₀) ≠ 0)]
  set κ := superKappa β θh with hκ_def
  have hκ0 : 0 < κ := superKappa_pos hβ hθh
  have hκ1 : κ < 1 := superKappa_lt_one hβ hθh
  obtain ⟨C, c, hc0, -, hC1, htail⟩ := profileSuper_tail hβ hθh
  obtain ⟨b, hb0, hb⟩ := hβ.exists_pos_le hκ0 (show (1 + κ) / 2 < 1 by linarith)
  set A := L ^ 2 + |D| with hA_def
  have hA : 0 ≤ A := by positivity
  have hC0 : 0 < C := by linarith
  set ε₀ := min (min a₀ 1) (min (c * a₀ * (1 - κ) / (2 * C))
    (c * a₀ * (Qmin ^ 2 * b) / (C * A + 1))) with hε₀_def
  have hε₀ : 0 < ε₀ := by
    refine lt_min (lt_min ha₀ one_pos) (lt_min ?_ ?_)
    · exact div_pos (mul_pos (mul_pos hc0 ha₀) (by linarith)) (by linarith)
    · exact div_pos (mul_pos (mul_pos hc0 ha₀) (by positivity)) (by positivity)
  refine ⟨ε₀, hε₀, ?_⟩
  intro d U Q g hU hg hΔ hgrad hQ hL hD ε hε
  obtain ⟨hε0, hεle⟩ := hε
  have hεa : ε ≤ a₀ := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε2 : ε ≤ c * a₀ * (1 - κ) / (2 * C) :=
    hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε ≤ c * a₀ * (Qmin ^ 2 * b) / (C * A + 1) :=
    hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the exponential smallness `E = C e^{-c a₀/ε}`
  set E := C * Real.exp (-(c * a₀ / ε)) with hE_def
  have hE0 : 0 ≤ E := by positivity
  have hEle : E ≤ C * ε / (c * a₀) := by
    calc E ≤ C * (ε / (c * a₀)) :=
          mul_le_mul_of_nonneg_left (exp_neg_div_le hc0 ha₀ hε0) hC0.le
      _ = C * ε / (c * a₀) := by ring
  have hca : 0 < c * a₀ := mul_pos hc0 ha₀
  have hE1 : E ≤ (1 - κ) / 2 := by
    refine hEle.trans ?_
    rw [div_le_div_iff₀ hca two_pos]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)).1 hε2
    linarith
  have hE2 : E * A ≤ Qmin ^ 2 * b := by
    have h1 : E * A ≤ C * ε / (c * a₀) * A := mul_le_mul_of_nonneg_right hEle hA
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < C * A + 1)).1 hε3
    have h3 : C * ε / (c * a₀) * A ≤ Qmin ^ 2 * b := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hca]
      linarith
    linarith
  set Ψ := profileSuperEps β θh ε with hΨ_def
  set gε := wellPreparedSuperData β δ₀ ε g with hgε_def
  have hgε : ∀ x, gε x = profileSuperEps β θh ε (g x) := fun x ↦ rfl
  have hΨc : ContDiff ℝ 2 (profileSuperEps β θh ε) :=
    (profileSuperEps_contDiff hβ hθh).of_le (WithTop.coe_le_coe.2 le_top)
  have hgεc : ContDiff ℝ 2 gε := hΨc.comp hg
  have hgrad_le : ∀ x, ‖∇ gε x‖ ≤ ‖∇ g x‖ := by
    intro x
    refine norm_gradient_comp_le (hΨc.differentiable (by norm_num) _)
      (hg.differentiable (by norm_num) x) ?_
    obtain ⟨h1, h2⟩ := profileSuperEps_deriv_mem hβ hθh hε0 (g x)
    rw [abs_of_pos h1]; exact h2
  -- the classical supersolution inequality
  have hmain : ∀ x ∈ U, Δ gε x ≤ Q x ^ 2 * betaEps β ε (gε x) := by
    intro x hxU
    have hlap : Δ gε x = deriv (deriv (profileSuperEps β θh ε)) (g x) * ‖∇ g x‖ ^ 2 +
        deriv (profileSuperEps β θh ε) (g x) * Δ g x :=
      laplacian_comp hΨc.contDiffAt hg.contDiffAt
    rw [hlap, hgε]
    obtain ⟨hP2a, hP2b⟩ := profileSuperEps_deriv_deriv_mem hβ hθh hε0 (g x)
    have hP1 := profileSuperEps_deriv_mem hβ hθh hε0 (g x)
    have hB := hβ.betaEps_nonneg ε (profileSuperEps β θh ε (g x)) hε0.le
    have hQ2 : 0 ≤ Q x ^ 2 := sq_nonneg _
    rcases lt_or_ge (-a₀) (g x) with hga | hga
    · -- `g > -a₀`: `Δg ≤ 0`
      have hΔx := hΔ x (subset_closure hxU) hga
      have hterm2 : deriv (profileSuperEps β θh ε) (g x) * Δ g x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hP1.1.le hΔx
      have hterm1 : deriv (deriv (profileSuperEps β θh ε)) (g x) * ‖∇ g x‖ ^ 2 ≤
          Q x ^ 2 * betaEps β ε (profileSuperEps β θh ε (g x)) := by
        rcases lt_or_ge (g x) ε with hgε' | hgε'
        · have habs : |g x| ≤ a₀ := abs_le.2 ⟨hga.le, by linarith⟩
          have hG := hgrad x (subset_closure hxU) habs
          calc _ ≤ deriv (deriv (profileSuperEps β θh ε)) (g x) * ((1 - δ₀) * Q x ^ 2) :=
                mul_le_mul_of_nonneg_left hG hP2a
            _ ≤ θh * betaEps β ε (profileSuperEps β θh ε (g x)) * ((1 - δ₀) * Q x ^ 2) :=
                mul_le_mul_of_nonneg_right hP2b (mul_nonneg (by linarith) hQ2)
            _ = θh * (1 - δ₀) * (Q x ^ 2 * betaEps β ε (profileSuperEps β θh ε (g x))) := by
                ring
            _ = _ := by rw [hθδ, one_mul]
        · have hzero : betaEps β ε (profileSuperEps β θh ε (g x)) = 0 := by
            rw [profileSuperEps_of_le hβ hθh hε0 hgε', betaEps,
              hβ.eq_zero_of_one_le ((one_le_div hε0).2 hgε'), zero_div]
          rw [hzero, mul_zero] at hP2b ⊢
          have : deriv (deriv (profileSuperEps β θh ε)) (g x) = 0 := le_antisymm hP2b hP2a
          rw [this, zero_mul]
      linarith
    · -- `g ≤ -a₀`: exponential tail
      set s := g x / ε with hs_def
      have hs0 : s ≤ -(a₀ / ε) := by
        rw [hs_def, neg_div' ]; exact div_le_div_of_nonneg_right (by linarith) hε0.le
      have hsn : s ≤ 0 := hs0.trans (neg_nonpos.2 (by positivity))
      obtain ⟨t1, t2, t3⟩ := htail s hsn
      have hexp : C * Real.exp (c * s) ≤ E := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0.le
        calc c * s ≤ c * -(a₀ / ε) := mul_le_mul_of_nonneg_left hs0 hc0.le
          _ = -(c * a₀ / ε) := by ring
      have hΨ2 : deriv (deriv (profileSuperEps β θh ε)) (g x) ≤ E / ε := by
        rw [profileSuperEps_deriv_deriv hβ hθh hε0]
        exact div_le_div_of_nonneg_right (t3.trans hexp) hε0.le
      have hΨ1 : deriv (profileSuperEps β θh ε) (g x) ≤ E := by
        rw [profileSuperEps_deriv hβ hθh hε0]; exact t2.trans hexp
      have hG2 : ‖∇ g x‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hL x hxU) 2
      have hΔD : Δ g x ≤ |D| := (le_abs_self _).trans ((hD x hxU).trans (le_abs_self _))
      -- left side `≤ E A / ε`
      have hlhs : deriv (deriv (profileSuperEps β θh ε)) (g x) * ‖∇ g x‖ ^ 2 +
          deriv (profileSuperEps β θh ε) (g x) * Δ g x ≤ E * A / ε := by
        have h1 : deriv (deriv (profileSuperEps β θh ε)) (g x) * ‖∇ g x‖ ^ 2 ≤ E / ε * L ^ 2 :=
          mul_le_mul hΨ2 hG2 (sq_nonneg _) (by positivity)
        have h2 : deriv (profileSuperEps β θh ε) (g x) * Δ g x ≤ E * |D| := by
          rcases le_total (Δ g x) 0 with hn | hn
          · exact (mul_nonpos_of_nonneg_of_nonpos hP1.1.le hn).trans (by positivity)
          · exact mul_le_mul hΨ1 hΔD hn hE0
        have h3 : E * |D| ≤ E / ε * |D| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [le_div_iff₀ hε0]; linarith [mul_le_mul_of_nonneg_left hε1 hE0]
        have h4 : E / ε * L ^ 2 + E / ε * |D| = E * A / ε := by rw [hA_def]; ring
        linarith
      -- right side `≥ Q_min² b / ε`
      have hΨs : profileSuper β θh s ∈ Icc κ ((1 + κ) / 2) := by
        refine ⟨(kappa_lt_profileSuper hβ hθh s).le, ?_⟩
        have := t1.trans hexp
        linarith
      have hrhs : Qmin ^ 2 * b / ε ≤ Q x ^ 2 * betaEps β ε (profileSuperEps β θh ε (g x)) := by
        rw [betaEps, profileSuperEps_div hε0, ← hs_def, mul_div_assoc']
        refine div_le_div_of_nonneg_right ?_ hε0.le
        have hQx := (hQ x hxU).1
        have hQ2' : Qmin ^ 2 ≤ Q x ^ 2 := pow_le_pow_left₀ hQmin.le hQx 2
        exact mul_le_mul hQ2' (hb _ hΨs) hb0.le hQ2
      have hmid : E * A / ε ≤ Qmin ^ 2 * b / ε := div_le_div_of_nonneg_right hE2 hε0.le
      linarith
  refine
    { lipschitz := ?_
      norm_gradient_le := hgrad_le
      eq_of_le := ?_
      bounds := ?_
      classicalSuper := ⟨hgεc.contDiffOn, hmain⟩
      viscSuper := ?_
      energy := energyJχ_le_of_norm_gradient_le hβ hU.measurableSet hε0
        (fun x hx ↦ (hQ x hx).2) hgrad_le
      kappa_lt := fun x ↦ mul_kappa_lt_profileSuperEps hβ hθh hε0 _ }
  · intro K hK
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    rw [Real.dist_eq, hgε, hgε]
    refine (abs_profileSuperEps_sub_le' hβ hθh hε0 (g y) (g x)).trans ?_
    rw [← Real.dist_eq]; exact hK.dist_le_mul x hx y hy
  · intro x hx
    rw [hgε, profileSuperEps_of_le hβ hθh hε0 hx]
  · intro x
    rw [hgε]
    refine ⟨max_le_profileSuperEps hβ hθh hε0 _, ?_⟩
    have := (abs_le.1 (abs_profileSuperEps_sub_le hβ hθh hε0 (g x))).2
    linarith
  · intro ψ hψ x hxU ht
    obtain ⟨-, hψx, hle⟩ := ht
    rw [hU.nhdsWithin_eq hxU] at hle
    exact (laplacian_le_of_eventually_le hψ.contDiffAt hgεc.contDiffAt hψx hle).trans
      (hmain x hxU)

/-! ### Wrappers from Definition 2.2 in the standing setting -/

theorem Setting.abs_Q_le (S : Setting d) {x : E d} (hx : x ∈ S.U) : |S.Q x| ≤ S.Qmax := by
  obtain ⟨h1, h2⟩ := S.Q_mem x (subset_closure hx)
  rw [abs_of_nonneg (S.Qmin_pos.le.trans h1)]; exact h2

/-- **Lemma A.4**, subsolution case, in the standing setting: for a smooth strict subsolution
`g` (Definition 2.2) there are `δ₀ > 0` (a parameter of Definition 2.2) and `ε₀ > 0` such that
`g_ε = (Φ_{ε,1/(1+δ₀)}(g))₊` satisfies (i)–(v) for `ε ∈ (0, ε₀]`. -/
theorem exists_wellPrepared_sub {β : ℝ → ℝ} (hβ : IsReactionProfile β) (S : Setting d)
    {g : E d → ℝ} (hg : IsStrictSub S.U S.Q g) :
    ∃ δ₀ > 0, ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      IsWellPreparedSub S.U S.Q β ε S.Qmax g (wellPreparedSubData β δ₀ ε g)
        (profileSubZero β (1 / (1 + δ₀))) (subConst (1 / (1 + δ₀))) := by
  obtain ⟨hg2, a₀, ha₀, δ₀, hδ₀, hΔ, hgrad⟩ := hg
  obtain ⟨ε₀, hε₀, h⟩ := wellPrepared_sub (Qmax := S.Qmax) hβ ha₀ hδ₀
  exact ⟨δ₀, hδ₀, ε₀, hε₀, h S.U S.Q g S.isOpen hg2 hΔ hgrad (fun x hx ↦ S.abs_Q_le hx)⟩

/-- **Lemma A.4**, supersolution case, in the standing setting: for a smooth strict
supersolution `g` (Definition 2.2) there are `δ₀ ∈ (0, 1)` (a parameter of Definition 2.2,
shrunk if necessary) and `ε₀ > 0` such that `g_ε = Ψ_{ε,1/(1-δ₀)}(g)` satisfies (i)–(iv) for
`ε ∈ (0, ε₀]`. -/
theorem exists_wellPrepared_super {β : ℝ → ℝ} (hβ : IsReactionProfile β) (S : Setting d)
    {g : E d → ℝ} (hg : IsStrictSuper S.U S.Q g) :
    ∃ δ₀ ∈ Ioo (0 : ℝ) 1, ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      IsWellPreparedSuper S.U S.Q β ε S.Qmax g (wellPreparedSuperData β δ₀ ε g)
        (superKappa β (1 / (1 - δ₀))) := by
  obtain ⟨hg2, a₀, ha₀, δ₀, hδ₀, hΔ, hgrad⟩ := hg
  have hK : IsCompact (closure S.U) := S.isBounded.isCompact_closure
  have hgradc : Continuous (∇ g) := by
    have : ∇ g = fun x ↦ (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ g x) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp
      (hg2.continuous_fderiv (by norm_num))
  have hΔc : Continuous (Δ g) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    exact continuous_finsetSum _ fun i _ ↦
      (continuous_eval_const _).comp (hg2.continuous_iteratedFDeriv le_rfl)
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hgradc.continuousOn
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hΔc.continuousOn
  set δ₁ := min δ₀ (1 / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ₀ (by norm_num)
  have hδ₁1 : δ₁ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨ε₀, hε₀, h⟩ := wellPrepared_super (Qmax := S.Qmax) (L := L) (D := D) hβ ha₀ hδ₁0 hδ₁1
    S.Qmin_pos
  refine ⟨δ₁, ⟨hδ₁0, hδ₁1⟩, ε₀, hε₀, h S.U S.Q g S.isOpen hg2 hΔ ?_ ?_ ?_ ?_⟩
  · intro x hx hgx
    refine (hgrad x hx hgx).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    linarith [min_le_left δ₀ (1 / 2)]
  · exact fun x hx ↦ ⟨(S.Q_mem x (subset_closure hx)).1, S.abs_Q_le hx⟩
  · exact fun x hx ↦ hL x (subset_closure hx)
  · exact fun x hx ↦ by simpa [Real.norm_eq_abs] using hD x (subset_closure hx)

end PerronVariational

end
