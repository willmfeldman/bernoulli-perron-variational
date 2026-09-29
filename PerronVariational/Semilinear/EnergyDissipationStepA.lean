/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.EnergyDissipationIBP
public import PerronVariational.Defs.Semilinear
import GMTFoundations.Sobolev.Lattice
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Energy dissipation, part 2: the energy bound near `t = 0` (Step A)

Step A of the proof of the energy dissipation inequality (A.1) of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981.
Let `u` solve (3.4) with `H¹ ∩ C(Ū)` data `g` (weak gradient
`G`), and `w = u - g`, which is continuous on `Ū × [0, ∞)` and vanishes on the parabolic boundary.
Testing the equation at time `t` with the truncation `T_σ(w(t))` (compact support in `U`) and
integrating in time gives
`∫₀ˢ ∫_U T_σ'(w) ∇u · (∇u - G) = -∫_U Ψ_σ(w(s)) - ∫₀ˢ ∫_U f T_σ(w) ≤ s M δ |U|`,
where `|f| ≤ M` and `|w| ≤ δ` on `U × (0, s]`. Letting `σ → 0` (Fatou) and using `∇u = G` a.e. on
`{w = 0}` gives

`∫₀ˢ ∫_U |∇u|² ≤ s ‖G‖²_{L²(U)} + 2 s M δ |U|`   (`lintegral_energy_le`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient Laplacian RealInnerProductSpace ContDiff

@[expose] public section

namespace PerronVariational

namespace EnergyDissipation

variable {d : ℕ}

/-! ### Generic helpers -/

/-- The set where `|F| ≥ σ` inside a compact set on which `F` is continuous is compact. -/
theorem isCompact_setOf_le_abs {X : Type*} [TopologicalSpace X] [T2Space X] {C : Set X}
    (hC : IsCompact C) {F : X → ℝ} (hF : ContinuousOn F C) (σ : ℝ) :
    IsCompact {p ∈ C | σ ≤ |F p|} :=
  hC.of_isClosed_subset (hF.abs.preimage_isClosed_of_isClosed hC.isClosed isClosed_Ici)
    fun _ hp ↦ hp.1

/-- If `F` vanishes on `C \ V` and `σ > 0`, then `{|F| ≥ σ} ∩ C ⊆ V`. -/
theorem setOf_le_abs_subset {X : Type*} {C V : Set X} {F : X → ℝ}
    (hF : ∀ p ∈ C, p ∉ V → F p = 0) {σ : ℝ} (hσ : 0 < σ) : {p ∈ C | σ ≤ |F p|} ⊆ V := by
  intro p hp
  by_contra h
  have := hp.2
  rw [hF p hp.1 h, abs_zero] at this
  linarith

/-- `x ∈ Ū \ U` means `x ∈ ∂U` for open `U`. -/
theorem mem_frontier_of_mem_closure {U : Set (E d)} (hU : IsOpen U) {x : E d}
    (hx : x ∈ closure U) (hxU : x ∉ U) : x ∈ frontier U := by
  rw [frontier, hU.interior_eq]; exact ⟨hx, hxU⟩

/-- Integrability of `⟪F, Ψ⟫` for `F` continuous on a compact `K` and `Ψ` integrable on `K`,
vanishing off `K`. -/
theorem integrable_inner_of_continuousOn {K : Set (E d)} (hK : IsCompact K) {F Ψ : E d → E d}
    (hF : ContinuousOn F K) (hΨ : IntegrableOn Ψ K) (hΨ0 : ∀ x ∉ K, Ψ x = 0) :
    Integrable (fun x ↦ ⟪F x, Ψ x⟫) := by
  have : IntegrableOn (fun x ↦ ⟪F x, Ψ x⟫) K := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
    refine Integrable.mono' (hΨ.norm.const_mul C) ?_ ?_
    · exact (hF.aestronglyMeasurable hK.measurableSet).inner hΨ.aestronglyMeasurable
    · refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _))
  exact (integrableOn_iff_integrable_of_support_subset fun x hx ↦
    by_contra fun h ↦ hx (by simp [hΨ0 x h])).1 this

/-- The pointwise inequality behind Step A: for `0 ≤ τ`, `0 ≤ c`, `c + τ ≤ 1`,
`τ |a|² + c |G|² ≤ |G|² + 2 a · τ (a - G)`. -/
theorem key_ineq (a G : E d) {τ c : ℝ} (hτ : 0 ≤ τ) (_hc : 0 ≤ c) (hcτ : c + τ ≤ 1) :
    τ * ‖a‖ ^ 2 + c * ‖G‖ ^ 2 ≤ ‖G‖ ^ 2 + 2 * ⟪a, τ • (a - G)⟫ := by
  have h1 : ⟪a, τ • (a - G)⟫ = τ * (‖a‖ ^ 2 - ⟪a, G⟫) := by
    rw [real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq]
  have h2 : 0 ≤ ‖a - G‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real] at h2
  rw [h1]
  have h3 : c * ‖G‖ ^ 2 ≤ (1 - τ) * ‖G‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  nlinarith [mul_nonneg hτ h2]

/-! ### The reaction term -/

/-- The reaction term `f = Q² β_ε(u)` of (3.4). -/
noncomputable def reaction (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ) (u : E d × ℝ → ℝ)
    (p : E d × ℝ) : ℝ :=
  Q p.1 ^ 2 * betaEps β ε (u p)

theorem continuousOn_reaction {U : Set (E d)} {I : Set ℝ} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ}
    {u : E d × ℝ → ℝ} (hQ : ContinuousOn Q U) (hβ : Continuous β)
    (hu : ContinuousOn u (U ×ˢ I)) : ContinuousOn (reaction Q β ε u) (U ×ˢ I) := by
  have hβε : Continuous (betaEps β ε) := (hβ.comp (continuous_id.div_const ε)).div_const ε
  exact ((hQ.comp continuousOn_fst fun p hp ↦ hp.1).pow 2).mul
    (hβε.comp_continuousOn hu)

section Solution

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ}
  {u : E d × ℝ → ℝ}

/-- `lapₓ u = ∂ₜu + f` on `U × (0, ∞)`. -/
theorem lapₓ_eq (hu : IsSemilinearSolution U Q β ε g u) {p : E d × ℝ} (hp : p ∈ U ×ˢ Ioi 0) :
    lapₓ u p = dₜ u p + reaction Q β ε u p := by
  rw [hu.2.1.2.2.2.2.2.2 p hp, reaction]; ring

/-- The data are continuous on `Ū`. -/
theorem continuousOn_data (hu : IsSemilinearSolution U Q β ε g u) : ContinuousOn g (closure U) :=
  ((hu.1.comp (continuous_id.prodMk continuous_const).continuousOn
    fun _ hx ↦ ⟨hx, mem_Ici.2 le_rfl⟩)).congr fun x hx ↦ (hu.2.2.1 x hx).symm

/-- Continuity of a time slice on `Ū`. -/
theorem continuousOn_slice (hu : IsSemilinearSolution U Q β ε g u) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun x ↦ u (x, t)) (closure U) :=
  hu.1.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hx ↦ ⟨hx, ht⟩

/-- `w = u - g` is continuous on `Ū × [0, ∞)`. -/
theorem continuousOn_sub_data (hu : IsSemilinearSolution U Q β ε g u) :
    ContinuousOn (fun p ↦ u p - g p.1) (closure U ×ˢ Ici 0) :=
  hu.1.sub ((continuousOn_data hu).comp continuousOn_fst fun _ hp ↦ hp.1)

/-- `w = u - g` vanishes on `(Ū × {0}) ∪ (∂U × [0, ∞))`. -/
theorem sub_data_eq_zero (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    {p : E d × ℝ} (hp : p ∈ closure U ×ˢ Ici 0) (hp' : p ∉ U ×ˢ Ioi 0) : u p - g p.1 = 0 := by
  by_cases hx : p.1 ∈ U
  · have ht : p.2 = 0 := by
      by_contra h
      exact hp' ⟨hx, lt_of_le_of_ne (mem_Ici.1 hp.2) (Ne.symm h)⟩
    have := hu.2.2.1 p.1 hp.1
    rw [show p = (p.1, 0) from Prod.ext rfl ht, this, sub_self]
  · rw [hu.2.2.2 p.1 (mem_frontier_of_mem_closure hU hp.1 hx) p.2 hp.2, sub_self]

end Solution

/-! ### The test function at a fixed time -/

/-- `K_t = {x ∈ Ū : |u(x, t) - g(x)| ≥ σ}`. -/
def sliceSet (U : Set (E d)) (u : E d × ℝ → ℝ) (g : E d → ℝ) (σ t : ℝ) : Set (E d) :=
  {x ∈ closure U | σ ≤ |u (x, t) - g x|}

/-- The test function `T_σ(u(·, t) - g)` (extended by `0` off `U`). -/
noncomputable def sliceTest (U : Set (E d)) (u : E d × ℝ → ℝ) (g : E d → ℝ) (σ t : ℝ) :
    E d → ℝ :=
  U.indicator fun x ↦ trunc σ (u (x, t) - g x)

/-- Its weak gradient `T_σ'(u(·, t) - g) (∇u(·, t) - G)` (extended by `0` off `U`). -/
noncomputable def sliceGrad (U : Set (E d)) (u : E d × ℝ → ℝ) (g : E d → ℝ) (G : E d → E d)
    (σ t : ℝ) : E d → E d :=
  U.indicator fun x ↦ truncDeriv σ (u (x, t) - g x) • (gradₓ u (x, t) - G x)

section Slice

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {G : E d → E d}
  {u : E d × ℝ → ℝ}

theorem isCompact_sliceSet (hUb : Bornology.IsBounded U) (hu : IsSemilinearSolution U Q β ε g u)
    (σ : ℝ) {t : ℝ} (ht : 0 ≤ t) : IsCompact (sliceSet U u g σ t) :=
  isCompact_setOf_le_abs hUb.isCompact_closure
    ((continuousOn_slice hu ht).sub (continuousOn_data hu)) σ

theorem sliceSet_subset (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u) {σ : ℝ}
    (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) : sliceSet U u g σ t ⊆ U :=
  setOf_le_abs_subset (fun x hx hxU ↦ by
    rw [hu.2.2.2 x (mem_frontier_of_mem_closure hU hx hxU) t ht, sub_self]) hσ

theorem abs_lt_of_notMem_sliceSet {σ t : ℝ} {x : E d} (hx : x ∈ closure U)
    (hxK : x ∉ sliceSet U u g σ t) : |u (x, t) - g x| < σ := by
  by_contra h
  exact hxK ⟨hx, not_lt.1 h⟩

theorem sliceTest_eq_zero {σ t : ℝ} (hσ : 0 < σ) {x : E d} (hxK : x ∉ sliceSet U u g σ t) :
    sliceTest U u g σ t x = 0 := by
  by_cases hx : x ∈ U
  · rw [sliceTest, indicator_of_mem hx]
    exact trunc_eq_zero hσ (abs_lt_of_notMem_sliceSet (subset_closure hx) hxK).le
  · rw [sliceTest, indicator_of_notMem hx]

theorem sliceGrad_eq_zero {σ t : ℝ} (hσ : 0 < σ) {x : E d} (hxK : x ∉ sliceSet U u g σ t) :
    sliceGrad U u g G σ t x = 0 := by
  by_cases hx : x ∈ U
  · rw [sliceGrad, indicator_of_mem hx,
      truncDeriv_eq_zero hσ (abs_lt_of_notMem_sliceSet (subset_closure hx) hxK).le, zero_smul]
  · rw [sliceGrad, indicator_of_notMem hx]

/-- The time slice `u(·, t)` has the weak gradient `∇ₓu(·, t)` in `U`. -/
theorem hasWeakGradient_slice (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u) {t : ℝ}
    (ht : 0 < t) : HasWeakGradient U (fun x ↦ u (x, t)) (fun x ↦ gradₓ u (x, t)) :=
  hasWeakGradient_of_contDiffOn hU ((hu.2.1.2.1 t ht).of_le (by norm_num))

theorem hasWeakGradient_sliceTest (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    (hg : HasWeakGradient U g G) (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasWeakGradient U (sliceTest U u g σ t) (sliceGrad U u g G σ t) := by
  have h := ((hasWeakGradient_slice hU hu ht).sub hg).comp hU (contDiff_trunc σ)
    (nnnorm_deriv_trunc_le σ)
  simp only [deriv_trunc] at h
  refine (h.congr_fun_ae ?_).congr_ae ?_
  · exact (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun x hx ↦ by
      rw [sliceTest, indicator_of_mem hx])
  · exact (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun x hx ↦ by
      rw [sliceGrad, indicator_of_mem hx])

/-- **The slice identity** (Step A, integration by parts at a fixed time `t > 0`):
`∫_U T_σ'(w) ∇u · (∇u - G) = -∫_U (∂ₜu + f) T_σ(w)`. -/
theorem integral_slice_identity (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) (hg : HasWeakGradient U g G) {σ : ℝ} (hσ : 0 < σ)
    {t : ℝ} (ht : 0 < t) :
    ∫ x, ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫ =
      -∫ x, (dₜ u (x, t) + reaction Q β ε u (x, t)) * sliceTest U u g σ t x := by
  have h := integral_laplacian_mul_eq_neg_of_hasWeakGradient hU (hu.2.1.2.1 t ht)
    (hasWeakGradient_sliceTest hU hu hg σ ht) (isCompact_sliceSet hUb hu σ ht.le)
    (sliceSet_subset hU hu hσ ht.le) (fun x hx ↦ sliceTest_eq_zero hσ hx)
    (fun x hx ↦ sliceGrad_eq_zero hσ hx)
  have e : ∀ x, Δ (fun y ↦ u (y, t)) x * sliceTest U u g σ t x =
      (dₜ u (x, t) + reaction Q β ε u (x, t)) * sliceTest U u g σ t x := by
    intro x
    by_cases hx : x ∈ U
    · rw [show Δ (fun y ↦ u (y, t)) x = lapₓ u (x, t) from rfl, lapₓ_eq hu (p := (x, t)) ⟨hx, ht⟩]
    · simp [sliceTest, indicator_of_notMem hx]
  simp_rw [e] at h
  rw [h, neg_neg]
  rfl

theorem integrable_inner_sliceGrad (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) (hg : HasWeakGradient U g G) {σ : ℝ} (hσ : 0 < σ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x ↦ ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫) := by
  have hK := isCompact_sliceSet hUb hu σ ht.le
  have hKU := sliceSet_subset hU hu hσ ht.le
  refine integrable_inner_of_continuousOn hK ?_
    ((hasWeakGradient_sliceTest hU hu hg σ ht).2.1.integrableOn_compact_subset hKU hK)
    fun x hx ↦ sliceGrad_eq_zero hσ hx
  exact (hu.2.1.2.2.1.comp (continuous_id.prodMk continuous_const).continuousOn
    fun x hx ↦ ⟨hKU hx, ht⟩)

end Slice

/-! ### The energy inequality at a fixed time -/

/-- The truncation levels `σₙ = 1/(n+1)`. -/
noncomputable def lev (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem lev_pos (n : ℕ) : 0 < lev n := by unfold lev; positivity

theorem tendsto_lev : Tendsto lev atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n ↦ lev_pos n⟩

/-- `‖G‖² ∈ L¹(U)` for `G ∈ L²(U)`. -/
theorem integrable_norm_sq_of_memLp {U : Set (E d)} {G : E d → E d}
    (hG : MemLp G 2 (volume.restrict U)) : IntegrableOn (fun x ↦ ‖G x‖ ^ 2) U :=
  (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG

section FixedTime

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {G : E d → E d}
  {u : E d × ℝ → ℝ}

/-- `I_σ(t) = ∫_U T_σ'(w) ∇u · (∇u - G)`. -/
noncomputable def sliceInt (U : Set (E d)) (u : E d × ℝ → ℝ) (g : E d → ℝ) (G : E d → E d)
    (σ t : ℝ) : ℝ :=
  ∫ x, ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫

theorem sliceBound_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) (hg : MemH1 U g G) {σ : ℝ} (hσ : 0 < σ)
    {t : ℝ} (ht : 0 < t) : 0 ≤ (∫ x in U, ‖G x‖ ^ 2) + 2 * sliceInt U u g G σ t := by
  have hnn : ∀ x ∈ U, 0 ≤ ‖G x‖ ^ 2 + 2 * ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫ := by
    intro x hx
    rw [sliceGrad, indicator_of_mem hx]
    have := key_ineq (gradₓ u (x, t)) (G x) (truncDeriv_nonneg σ (u (x, t) - g x)) le_rfl
      (by simpa using truncDeriv_le_one σ (u (x, t) - g x))
    nlinarith [truncDeriv_nonneg σ (u (x, t) - g x), sq_nonneg ‖gradₓ u (x, t)‖]
  have hI := integrable_inner_sliceGrad hU hUb hu hg.2.2 hσ ht
  have hS : ∫ x in U, ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫ = sliceInt U u g G σ t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp [sliceGrad, indicator_of_notMem hx]
  rw [← hS, ← integral_const_mul, ← integral_add (integrable_norm_sq_of_memLp hg.2.1)
    (hI.integrableOn.const_mul 2)]
  exact setIntegral_nonneg hU.measurableSet hnn

/-- **(c)**: `∫_U T_σ'(w) |∇u|² + ∫_{U ∩ {w = 0}} |G|² ≤ ‖G‖² + 2 I_σ(t)`. -/
theorem lintegral_trunc_energy_le (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) (hg : MemH1 U g G) {σ : ℝ} (hσ : 0 < σ)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ x in U, ENNReal.ofReal (truncDeriv σ (u (x, t) - g x) * ‖gradₓ u (x, t)‖ ^ 2)) +
        ∫⁻ x in U, ENNReal.ofReal
          ({x | u (x, t) - g x = 0}.indicator (fun x ↦ ‖G x‖ ^ 2) x) ≤
      ENNReal.ofReal ((∫ x in U, ‖G x‖ ^ 2) + 2 * sliceInt U u g G σ t) := by
  have hpt : ∀ x ∈ U, truncDeriv σ (u (x, t) - g x) * ‖gradₓ u (x, t)‖ ^ 2 +
      {x | u (x, t) - g x = 0}.indicator (fun x ↦ ‖G x‖ ^ 2) x ≤
        ‖G x‖ ^ 2 + 2 * ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫ := by
    intro x hx
    rw [sliceGrad, indicator_of_mem hx]
    by_cases h0 : u (x, t) - g x = 0
    · rw [indicator_of_mem (show x ∈ {x | u (x, t) - g x = 0} from h0)]
      have := key_ineq (gradₓ u (x, t)) (G x) (truncDeriv_nonneg σ (u (x, t) - g x))
        zero_le_one (by rw [h0, truncDeriv_zero hσ]; norm_num)
      simpa using this
    · rw [indicator_of_notMem (show x ∉ {x | u (x, t) - g x = 0} from h0)]
      have := key_ineq (gradₓ u (x, t)) (G x) (truncDeriv_nonneg σ (u (x, t) - g x)) le_rfl
        (by simpa using truncDeriv_le_one σ (u (x, t) - g x))
      simpa using this
  have hnn : ∀ x ∈ U, 0 ≤ ‖G x‖ ^ 2 + 2 * ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫ := by
    intro x hx
    rw [sliceGrad, indicator_of_mem hx]
    have := key_ineq (gradₓ u (x, t)) (G x) (truncDeriv_nonneg σ (u (x, t) - g x)) le_rfl
      (by simpa using truncDeriv_le_one σ (u (x, t) - g x))
    nlinarith [truncDeriv_nonneg σ (u (x, t) - g x), sq_nonneg ‖gradₓ u (x, t)‖]
  have hI := integrable_inner_sliceGrad hU hUb hu hg.2.2 hσ ht
  have hint : IntegrableOn
      (fun x ↦ ‖G x‖ ^ 2 + 2 * ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫) U :=
    (integrable_norm_sq_of_memLp hg.2.1).add (hI.integrableOn.const_mul 2)
  calc _ ≤ ∫⁻ x in U, (ENNReal.ofReal (truncDeriv σ (u (x, t) - g x) * ‖gradₓ u (x, t)‖ ^ 2) +
          ENNReal.ofReal ({x | u (x, t) - g x = 0}.indicator (fun x ↦ ‖G x‖ ^ 2) x)) :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ x in U, ENNReal.ofReal
          (‖G x‖ ^ 2 + 2 * ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫) := by
        refine setLIntegral_mono' hU.measurableSet fun x hx ↦ ?_
        rw [← ENNReal.ofReal_add (mul_nonneg (truncDeriv_nonneg _ _) (sq_nonneg _))
          (indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)]
        exact ENNReal.ofReal_le_ofReal (hpt x hx)
    _ = ENNReal.ofReal (∫ x in U,
          (‖G x‖ ^ 2 + 2 * ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall hnn))).symm
    _ = _ := by
        have hS : ∫ x in U, ⟪gradₓ u (x, t), sliceGrad U u g G σ t x⟫ =
            sliceInt U u g G σ t :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
            simp [sliceGrad, indicator_of_notMem hx]
        rw [integral_add (integrable_norm_sq_of_memLp hg.2.1) (hI.integrableOn.const_mul 2),
          integral_const_mul, hS]

/-- **(d)**: level set and Fatou at a fixed time. -/
theorem lintegral_grad_sq_le_liminf (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u)
    (hg : MemH1 U g G) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, t)‖ ^ 2) ≤
      liminf (fun n ↦ ∫⁻ x in U,
        ENNReal.ofReal (truncDeriv (lev n) (u (x, t) - g x) * ‖gradₓ u (x, t)‖ ^ 2)) atTop +
      ∫⁻ x in U, ENNReal.ofReal ({x | u (x, t) - g x = 0}.indicator (fun x ↦ ‖G x‖ ^ 2) x) := by
  have hae := HasWeakGradient.ae_eq_zero_of_eq_zero hU ((hasWeakGradient_slice hU hu ht).sub hg.2.2)
  have hwc : ContinuousOn (fun x ↦ u (x, t) - g x) U :=
    ((continuousOn_slice hu ht.le).sub (continuousOn_data hu)).mono subset_closure
  have hgc : ContinuousOn (fun x ↦ ‖gradₓ u (x, t)‖ ^ 2) U :=
    (hu.2.1.2.2.1.comp (continuous_id.prodMk continuous_const).continuousOn
      fun x hx ↦ ⟨hx, ht⟩).norm.pow 2
  set Z := U ∩ (fun x ↦ u (x, t) - g x) ⁻¹' {0}ᶜ with hZ
  have hZo : IsOpen Z := hwc.isOpen_inter_preimage hU isOpen_compl_singleton
  set A : E d → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    ({x | u (x, t) - g x ≠ 0}.indicator (fun x ↦ ‖gradₓ u (x, t)‖ ^ 2) x) with hA
  have hAm : AEMeasurable A (volume.restrict U) := by
    have h1 : AEMeasurable (Z.indicator fun x ↦ ‖gradₓ u (x, t)‖ ^ 2) (volume.restrict U) :=
      (hgc.aemeasurable hU.measurableSet).indicator hZo.measurableSet
    refine (ENNReal.measurable_ofReal.comp_aemeasurable h1).congr ?_
    refine (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
    by_cases h0 : u (x, t) - g x = 0
    · have hx0 : x ∉ {x | u (x, t) - g x ≠ 0} := fun h ↦ h h0
      simp [hA, hZ, h0]
    · simp [hA, hZ, h0, hx]
  have hsplit : ∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, t)‖ ^ 2) = ∫⁻ x in U, (A x +
      ENNReal.ofReal ({x | u (x, t) - g x = 0}.indicator (fun x ↦ ‖G x‖ ^ 2) x)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    by_cases h0 : u (x, t) - g x = 0
    · have : gradₓ u (x, t) = G x := sub_eq_zero.1 (hx h0)
      have hx0 : x ∉ {x | u (x, t) - g x ≠ 0} := fun h ↦ h h0
      simp [hA, indicator_of_notMem hx0,
        indicator_of_mem (show x ∈ {x | u (x, t) - g x = 0} from h0), this]
    · simp [hA, h0]
  rw [hsplit, lintegral_add_left' hAm]
  gcongr
  have hlim : ∀ x, Tendsto (fun n ↦ ENNReal.ofReal
      (truncDeriv (lev n) (u (x, t) - g x) * ‖gradₓ u (x, t)‖ ^ 2)) atTop (𝓝 (A x)) := by
    intro x
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    by_cases h0 : u (x, t) - g x = 0
    · rw [indicator_of_notMem (show x ∉ {x | u (x, t) - g x ≠ 0} from fun h ↦ h h0)]
      refine tendsto_const_nhds.congr fun n ↦ ?_
      rw [h0, truncDeriv_zero (lev_pos n), zero_mul]
    · rw [indicator_of_mem (show x ∈ {x | u (x, t) - g x ≠ 0} from h0)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_lev.eventually (eventually_truncDeriv_eq_one h0)] with n hn
      rw [hn, one_mul]
  calc ∫⁻ x in U, A x = ∫⁻ x in U, liminf (fun n ↦ ENNReal.ofReal
        (truncDeriv (lev n) (u (x, t) - g x) * ‖gradₓ u (x, t)‖ ^ 2)) atTop :=
        lintegral_congr fun x ↦ ((hlim x).liminf_eq).symm
    _ ≤ _ := by
        refine lintegral_liminf_le' fun n ↦ ?_
        exact ENNReal.measurable_ofReal.comp_aemeasurable
          (((continuous_truncDeriv _).comp_continuousOn hwc).mul hgc |>.aemeasurable
            hU.measurableSet)

/-- **Step A at a fixed time**: `∫_U |∇u(t)|² ≤ liminf_n (‖G‖² + 2 I_{σₙ}(t))`. -/
theorem lintegral_grad_sq_le_liminf_sliceInt (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) (hg : MemH1 U g G) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, t)‖ ^ 2) ≤
      liminf (fun n ↦ ENNReal.ofReal ((∫ x in U, ‖G x‖ ^ 2) + 2 * sliceInt U u g G (lev n) t))
        atTop := by
  refine (lintegral_grad_sq_le_liminf hU hu hg ht).trans ?_
  rw [← liminf_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault)]
  exact liminf_le_liminf (Eventually.of_forall fun n ↦
    lintegral_trunc_energy_le hU hUb hu hg (lev_pos n) ht)

end FixedTime

/-! ### Integration in time -/

/-- A compact subset of `U × (0, s]` stays away from `t = 0`. -/
theorem exists_time_gap {K : Set (E d × ℝ)} (hK : IsCompact K) (hK0 : ∀ p ∈ K, 0 < p.2)
    {s : ℝ} (hs : 0 < s) : ∃ τ, 0 < τ ∧ τ < s ∧ ∀ p ∈ K, τ < p.2 := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨s / 2, half_pos hs, half_lt_self hs, by simp [h]⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
  have hm := hK0 p₀ hp₀
  refine ⟨min p₀.2 s / 2, by positivity, ?_, fun p hp ↦ ?_⟩
  · linarith [min_le_right p₀.2 s]
  · have : p₀.2 ≤ p.2 := hmin hp
    have : min p₀.2 s / 2 < p₀.2 := by
      have := min_le_left p₀.2 s
      have : 0 < min p₀.2 s := lt_min hm hs
      linarith
    linarith

section TimeIntegral

variable {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ} {G : E d → E d}
  {u : E d × ℝ → ℝ}

/-- `K_σ = {(x, t) ∈ Ū × [0, s] : |u - g| ≥ σ}`. -/
def bigSet (U : Set (E d)) (u : E d × ℝ → ℝ) (g : E d → ℝ) (σ s : ℝ) : Set (E d × ℝ) :=
  {p ∈ closure U ×ˢ Icc 0 s | σ ≤ |u p - g p.1|}

theorem isCompact_bigSet (hUb : Bornology.IsBounded U) (hu : IsSemilinearSolution U Q β ε g u)
    (σ s : ℝ) : IsCompact (bigSet U u g σ s) :=
  isCompact_setOf_le_abs (hUb.isCompact_closure.prod isCompact_Icc)
    ((continuousOn_sub_data hu).mono (prod_mono le_rfl Icc_subset_Ici_self)) σ

theorem bigSet_subset (hU : IsOpen U) (hu : IsSemilinearSolution U Q β ε g u) {σ : ℝ}
    (hσ : 0 < σ) (s : ℝ) : bigSet U u g σ s ⊆ U ×ˢ Ioc 0 s := by
  intro p hp
  have h1 : p ∈ U ×ˢ Ioi 0 := setOf_le_abs_subset (C := closure U ×ˢ Icc 0 s)
    (fun p hp hp' ↦ sub_data_eq_zero hU hu ⟨hp.1, hp.2.1⟩ hp') hσ hp
  exact ⟨h1.1, h1.2, hp.1.2.2⟩

/-- The two space-time integrands `∂ₜu T_σ(w)` and `f T_σ(w)` on `U × (0, s]`. -/
noncomputable def dtTerm (U : Set (E d)) (u : E d × ℝ → ℝ) (g : E d → ℝ) (σ s : ℝ) :
    E d × ℝ → ℝ :=
  (U ×ˢ Ioc 0 s).indicator fun p ↦ dₜ u p * trunc σ (u p - g p.1)

noncomputable def rxnTerm (U : Set (E d)) (Q : E d → ℝ) (β : ℝ → ℝ) (ε : ℝ)
    (u : E d × ℝ → ℝ) (g : E d → ℝ) (σ s : ℝ) : E d × ℝ → ℝ :=
  (U ×ˢ Ioc 0 s).indicator fun p ↦ reaction Q β ε u p * trunc σ (u p - g p.1)

theorem trunc_eq_zero_of_notMem_bigSet {σ s : ℝ} (hσ : 0 < σ) {p : E d × ℝ}
    (hp : p ∈ closure U ×ˢ Icc 0 s) (hpK : p ∉ bigSet U u g σ s) : trunc σ (u p - g p.1) = 0 :=
  trunc_eq_zero hσ (not_le.1 fun h ↦ hpK ⟨hp, h⟩).le

theorem integrable_spacetime_term (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) {σ s : ℝ} (hσ : 0 < σ) {a : E d × ℝ → ℝ}
    (ha : ContinuousOn a (U ×ˢ Ioi 0)) :
    Integrable ((U ×ˢ Ioc 0 s).indicator fun p ↦ a p * trunc σ (u p - g p.1)) := by
  have hK := isCompact_bigSet hUb hu σ s
  have hKU := bigSet_subset hU hu hσ s
  have hKU' : bigSet U u g σ s ⊆ U ×ˢ Ioi 0 := fun p hp ↦ ⟨(hKU hp).1, (hKU hp).2.1⟩
  refine integrable_of_continuousOn_of_eq_zero hK ?_ fun p hp ↦ ?_
  · refine ContinuousOn.congr ?_ fun p hp ↦ indicator_of_mem (hKU hp) _
    exact (ha.mono hKU').mul ((continuous_trunc σ).comp_continuousOn
      ((continuousOn_sub_data hu).mono fun p hp ↦
        ⟨subset_closure (hKU' hp).1, mem_Ici.2 (hKU' hp).2.le⟩))
  · by_cases hpU : p ∈ U ×ˢ Ioc 0 s
    · rw [indicator_of_mem hpU, trunc_eq_zero_of_notMem_bigSet hσ
        ⟨subset_closure hpU.1, hpU.2.1.le, hpU.2.2⟩ hp, mul_zero]
    · rw [indicator_of_notMem hpU]

theorem integrable_dtTerm (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    Integrable (dtTerm U u g σ s) :=
  integrable_spacetime_term hU hUb hu hσ hu.2.1.2.2.2.2.2.1

theorem integrable_rxnTerm (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hQ : ContinuousOn Q U)
    (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u) {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    Integrable (rxnTerm U Q β ε u g σ s) :=
  integrable_spacetime_term hU hUb hu hσ (continuousOn_reaction hQ hβ hu.2.1.1)

theorem integrable_slice_term (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) {σ s : ℝ} (hσ : 0 < σ) {a : E d × ℝ → ℝ}
    (ha : ContinuousOn a (U ×ˢ Ioi 0)) {t : ℝ} (ht : t ∈ Ioc 0 s) :
    Integrable (fun x ↦ (U ×ˢ Ioc 0 s).indicator (fun p ↦ a p * trunc σ (u p - g p.1)) (x, t)) := by
  have hK := isCompact_sliceSet hUb hu σ ht.1.le
  have hKU := sliceSet_subset hU hu hσ ht.1.le
  refine integrable_of_continuousOn_of_eq_zero hK ?_ fun x hx ↦ ?_
  · refine ContinuousOn.congr ?_ fun x hx ↦ indicator_of_mem (show (x, t) ∈ U ×ˢ Ioc 0 s from
      ⟨hKU hx, ht⟩) _
    have hemb : ContinuousOn (fun x : E d ↦ (x, t)) (sliceSet U u g σ t) :=
      (continuous_id.prodMk continuous_const).continuousOn
    exact (ha.comp hemb fun x hx ↦ ⟨hKU hx, ht.1⟩).mul ((continuous_trunc σ).comp_continuousOn
      ((continuousOn_sub_data hu).comp hemb fun x hx ↦ ⟨subset_closure (hKU hx), ht.1.le⟩))
  · by_cases hxU : x ∈ U
    · rw [indicator_of_mem (show (x, t) ∈ U ×ˢ Ioc 0 s from ⟨hxU, ht⟩),
        trunc_eq_zero hσ (abs_lt_of_notMem_sliceSet (subset_closure hxU) hx).le, mul_zero]
    · rw [indicator_of_notMem (fun h ↦ hxU h.1)]

/-- `I_σ(t) = -∫ (∂ₜu + f) T_σ(w)(·, t)` for `t ∈ (0, s]`. -/
theorem sliceInt_eq (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hQ : ContinuousOn Q U)
    (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u) (hg : HasWeakGradient U g G)
    {σ s : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : t ∈ Ioc 0 s) :
    sliceInt U u g G σ t =
      -((∫ x, dtTerm U u g σ s (x, t)) + ∫ x, rxnTerm U Q β ε u g σ s (x, t)) := by
  have h1 : Integrable (fun x ↦ dtTerm U u g σ s (x, t)) :=
    integrable_slice_term hU hUb hu hσ hu.2.1.2.2.2.2.2.1 ht
  have h2 : Integrable (fun x ↦ rxnTerm U Q β ε u g σ s (x, t)) :=
    integrable_slice_term hU hUb hu hσ (continuousOn_reaction hQ hβ hu.2.1.1) ht
  rw [sliceInt, integral_slice_identity hU hUb hu hg hσ ht.1, ← integral_add h1 h2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  by_cases hxU : x ∈ U
  · simp only [dtTerm, rxnTerm, sliceTest]
    rw [indicator_of_mem hxU, indicator_of_mem (show (x, t) ∈ U ×ˢ Ioc 0 s from ⟨hxU, ht⟩),
      indicator_of_mem (show (x, t) ∈ U ×ˢ Ioc 0 s from ⟨hxU, ht⟩)]
    ring
  · simp only [dtTerm, rxnTerm, sliceTest]
    rw [indicator_of_notMem hxU, indicator_of_notMem (fun h ↦ hxU h.1),
      indicator_of_notMem (fun h ↦ hxU h.1)]
    ring

/-- `∫_I ∫ F(x, t) dx dt = ∫ F` for integrable `F` vanishing for `t ∉ I`. -/
theorem setIntegral_integral_eq {F : E d × ℝ → ℝ} (hF : Integrable F) {I : Set ℝ}
    (hI0 : ∀ x, ∀ t ∉ I, F (x, t) = 0) : ∫ t in I, ∫ x, F (x, t) = ∫ p, F p := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by simp [hI0 _ t ht]]
  rw [Measure.volume_eq_prod] at hF ⊢
  exact (integral_prod_symm F hF).symm

theorem integrableOn_integral_slice {F : E d × ℝ → ℝ} (hF : Integrable F) (I : Set ℝ) :
    IntegrableOn (fun t ↦ ∫ x, F (x, t)) I := by
  rw [Measure.volume_eq_prod] at hF
  exact hF.integral_prod_right.integrableOn

/-- `∫₀ˢ I_σ = -(∫∫ ∂ₜu T_σ(w) + ∫∫ f T_σ(w))`. -/
theorem setIntegral_sliceInt (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    (hg : HasWeakGradient U g G) {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    ∫ t in Ioc 0 s, sliceInt U u g G σ t =
      -((∫ p, dtTerm U u g σ s p) + ∫ p, rxnTerm U Q β ε u g σ s p) := by
  have h1 := integrable_dtTerm hU hUb hu hσ s
  have h2 := integrable_rxnTerm hU hUb hQ hβ hu hσ s
  rw [setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ sliceInt_eq hU hUb hQ hβ hu hg hσ ht,
    integral_neg, integral_add (integrableOn_integral_slice h1 _)
      (integrableOn_integral_slice h2 _),
    setIntegral_integral_eq h1 fun x t ht ↦ indicator_of_notMem (fun h ↦ ht h.2) _,
    setIntegral_integral_eq h2 fun x t ht ↦ indicator_of_notMem (fun h ↦ ht h.2) _]

theorem integrableOn_sliceInt (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    (hg : HasWeakGradient U g G) {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    IntegrableOn (fun t ↦ sliceInt U u g G σ t) (Ioc 0 s) := by
  have h1 := integrable_dtTerm hU hUb hu hσ s
  have h2 := integrable_rxnTerm hU hUb hQ hβ hu hσ s
  refine (((integrableOn_integral_slice h1 _).add (integrableOn_integral_slice h2 _)).neg).congr_fun
    (fun t ht ↦ (sliceInt_eq hU hUb hQ hβ hu hg hσ ht).symm) measurableSet_Ioc

/-- The time integral of `∂ₜu T_σ(w)` at a fixed `x` is `Ψ_σ(w(x, s)) ≥ 0`. -/
theorem integral_dtTerm_slice_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x : E d) :
    0 ≤ ∫ t, dtTerm U u g σ s (x, t) := by
  by_cases hx : x ∉ U
  · simp [dtTerm, indicator_of_notMem (fun h : (x, _) ∈ U ×ˢ Ioc 0 s ↦ hx h.1)]
  push Not at hx
  obtain ⟨τ, hτ, hτs, hτK⟩ := exists_time_gap (isCompact_bigSet hUb hu σ s)
    (fun p hp ↦ (bigSet_subset hU hu hσ s hp).2.1) hs
  have hslice : ∀ t, dtTerm U u g σ s (x, t) =
      (Ioc τ s).indicator (fun t ↦ dₜ u (x, t) * trunc σ (u (x, t) - g x)) t := by
    intro t
    by_cases ht : t ∈ Ioc 0 s
    · rw [dtTerm, indicator_of_mem (show (x, t) ∈ U ×ˢ Ioc 0 s from ⟨hx, ht⟩)]
      by_cases htτ : t ∈ Ioc τ s
      · rw [indicator_of_mem htτ]
      · rw [indicator_of_notMem htτ]
        have htle : t ≤ τ := by
          by_contra h; exact htτ ⟨lt_of_not_ge h, ht.2⟩
        rw [trunc_eq_zero_of_notMem_bigSet hσ (s := s)
          ⟨subset_closure hx, ht.1.le, ht.2⟩ fun hK ↦ by linarith [hτK _ hK], mul_zero]
    · rw [dtTerm, indicator_of_notMem (fun h ↦ ht h.2), indicator_of_notMem
        (fun h ↦ ht ⟨hτ.trans h.1, h.2⟩)]
  have hcont : ContinuousOn (fun t ↦ dₜ u (x, t) * trunc σ (u (x, t) - g x)) (Ioi 0) := by
    have hemb : ContinuousOn (fun t : ℝ ↦ (x, t)) (Ioi 0) :=
      (continuous_const.prodMk continuous_id).continuousOn
    exact (hu.2.1.2.2.2.2.2.1.comp hemb fun t ht ↦ ⟨hx, ht⟩).mul
      ((continuous_trunc σ).comp_continuousOn
        ((hu.2.1.1.comp hemb fun t ht ↦ ⟨hx, ht⟩).sub continuousOn_const))
  have hderiv : ∀ t ∈ uIcc τ s, HasDerivAt (fun t ↦ truncPrim σ (u (x, t) - g x))
      (dₜ u (x, t) * trunc σ (u (x, t) - g x)) t := by
    intro t ht
    rw [uIcc_of_le hτs.le] at ht
    have ht0 : 0 < t := hτ.trans_le ht.1
    have hd : HasDerivAt (fun t ↦ u (x, t)) (dₜ u (x, t)) t :=
      (hu.2.1.2.2.2.2.1 (x, t) ⟨hx, ht0⟩).hasDerivAt
    have := (hasDerivAt_truncPrim σ (u (x, t) - g x)).comp t (hd.sub_const (g x))
    rw [mul_comm] at this
    exact this
  have hint : IntervalIntegrable (fun t ↦ dₜ u (x, t) * trunc σ (u (x, t) - g x)) volume τ s :=
    (hcont.mono fun t ht ↦ by
      rw [uIcc_of_le hτs.le] at ht; exact hτ.trans_le ht.1).intervalIntegrable
  have hτ0 : truncPrim σ (u (x, τ) - g x) = 0 := by
    refine truncPrim_eq_zero hσ (not_le.1 fun h ↦ ?_).le
    have := hτK (x, τ) ⟨⟨subset_closure hx, hτ.le, hτs.le⟩, h⟩
    exact lt_irrefl _ this
  simp_rw [hslice]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hτs.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, hτ0, sub_zero]
  exact truncPrim_nonneg σ _

theorem integral_dtTerm_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : IsSemilinearSolution U Q β ε g u) {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) :
    0 ≤ ∫ p, dtTerm U u g σ s p := by
  have h1 := integrable_dtTerm hU hUb hu hσ s
  rw [Measure.volume_eq_prod] at h1 ⊢
  rw [integral_prod _ h1]
  exact integral_nonneg fun x ↦ integral_dtTerm_slice_nonneg hU hUb hu hσ hs x

theorem measureReal_prod_Ioc {U : Set (E d)} {s : ℝ} (hs : 0 ≤ s) :
    volume.real (U ×ˢ Ioc (0 : ℝ) s) = volume.real U * s := by
  rw [measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), sub_zero, measureReal_def]

/-- The reaction term is bounded by `M δ |U| s`. -/
theorem neg_integral_rxnTerm_le (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    {σ s δ M : ℝ} (hσ : 0 < σ) (hs : 0 < s)
    (hδ : ∀ x ∈ U, ∀ t ∈ Ioc 0 s, |u (x, t) - g x| ≤ δ)
    (hM : ∀ x ∈ U, ∀ t ∈ Ioc 0 s, |reaction Q β ε u (x, t)| ≤ M) :
    -∫ p, rxnTerm U Q β ε u g σ s p ≤ M * δ * (volume.real U * s) := by
  have h2 := integrable_rxnTerm hU hUb hQ hβ hu hσ s
  have hm : MeasurableSet (U ×ˢ Ioc (0 : ℝ) s) := hU.measurableSet.prod measurableSet_Ioc
  have hfin : volume (U ×ˢ Ioc (0 : ℝ) s) < ⊤ :=
    (hUb.prod (Metric.isBounded_Ioc 0 s)).measure_lt_top
  have hbd : Integrable ((U ×ˢ Ioc (0 : ℝ) s).indicator fun _ ↦ M * δ) :=
    (integrable_indicator_iff hm).2 (integrableOn_const hfin.ne)
  rw [← integral_neg, ← measureReal_prod_Ioc hs.le, mul_comm (M * δ),
    ← smul_eq_mul, ← integral_indicator_const _ hm]
  refine integral_mono h2.neg hbd fun p ↦ ?_
  by_cases hp : p ∈ U ×ˢ Ioc 0 s
  · simp only [rxnTerm, indicator_of_mem hp]
    have h1 := hM p.1 hp.1 p.2 hp.2
    have h3 := (abs_trunc_le σ (u p - g p.1)).trans (hδ p.1 hp.1 p.2 hp.2)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans h1
    calc -(reaction Q β ε u p * trunc σ (u p - g p.1))
        ≤ |reaction Q β ε u p * trunc σ (u p - g p.1)| := neg_le_abs _
      _ = |reaction Q β ε u p| * |trunc σ (u p - g p.1)| := abs_mul _ _
      _ ≤ M * δ := mul_le_mul h1 h3 (abs_nonneg _) hM0
  · simp [rxnTerm, indicator_of_notMem hp]

end TimeIntegral

/-! ### Step A -/

/-- **Step A**: if `|u - g| ≤ δ` and `|f| ≤ M` on `U × (0, s]`, then
`∫₀ˢ ∫_U |∇u|² ≤ s ‖G‖²_{L²(U)} + 2 M δ |U| s`. -/
theorem lintegral_energy_le {U : Set (E d)} {Q : E d → ℝ} {β : ℝ → ℝ} {ε : ℝ} {g : E d → ℝ}
    {G : E d → E d} {u : E d × ℝ → ℝ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hQ : ContinuousOn Q U) (hβ : Continuous β) (hu : IsSemilinearSolution U Q β ε g u)
    (hg : MemH1 U g G) {s δ M : ℝ} (hs : 0 < s)
    (hδ : ∀ x ∈ U, ∀ t ∈ Ioc 0 s, |u (x, t) - g x| ≤ δ)
    (hM : ∀ x ∈ U, ∀ t ∈ Ioc 0 s, |reaction Q β ε u (x, t)| ≤ M) :
    ∫⁻ t in Ioc 0 s, ∫⁻ x in U, ENNReal.ofReal (‖gradₓ u (x, t)‖ ^ 2) ≤
      ENNReal.ofReal (s * (∫ x in U, ‖G x‖ ^ 2) + 2 * (M * δ * (volume.real U * s))) := by
  set φ : ℕ → ℝ → ℝ := fun n t ↦ (∫ x in U, ‖G x‖ ^ 2) + 2 * sliceInt U u g G (lev n) t
    with hφ
  have hφi : ∀ n, IntegrableOn (φ n) (Ioc 0 s) := fun n ↦
    (integrableOn_const (by simp)).add
      ((integrableOn_sliceInt hU hUb hQ hβ hu hg.2.2 (lev_pos n) s).const_mul 2)
  calc _ ≤ ∫⁻ t in Ioc 0 s, liminf (fun n ↦ ENNReal.ofReal (φ n t)) atTop :=
        setLIntegral_mono' measurableSet_Ioc fun t ht ↦
          lintegral_grad_sq_le_liminf_sliceInt hU hUb hu hg ht.1
    _ ≤ liminf (fun n ↦ ∫⁻ t in Ioc 0 s, ENNReal.ofReal (φ n t)) atTop :=
        lintegral_liminf_le' fun n ↦ (hφi n).aemeasurable.ennreal_ofReal
    _ ≤ _ := by
        refine (liminf_le_liminf (Eventually.of_forall fun n ↦ ?_)).trans (liminf_const _).le
        rw [← ofReal_integral_eq_lintegral_ofReal (hφi n)
          ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht ↦
            sliceBound_nonneg hU hUb hu hg (lev_pos n) ht.1))]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := setIntegral_sliceInt hU hUb hQ hβ hu hg.2.2 (lev_pos n) s
        have h2 := integral_dtTerm_nonneg hU hUb hu (lev_pos n) hs (g := g)
        have h3 := neg_integral_rxnTerm_le hU hUb hQ hβ hu (lev_pos n) hs hδ hM
        have hc : Integrable (fun _ : ℝ ↦ ∫ x in U, ‖G x‖ ^ 2) (volume.restrict (Ioc 0 s)) :=
          integrableOn_const (by simp)
        have hi : Integrable (fun t ↦ 2 * sliceInt U u g G (lev n) t)
            (volume.restrict (Ioc 0 s)) :=
          (integrableOn_sliceInt hU hUb hQ hβ hu hg.2.2 (lev_pos n) s).const_mul 2
        simp only [hφ]
        rw [integral_add hc hi, integral_const_mul, h1, setIntegral_const, Real.volume_real_Ioc,
          sub_zero,
          max_eq_left hs.le, smul_eq_mul]
        linarith

end EnergyDissipation

end PerronVariational

end
