/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.BV
public import GMTFoundations.Sobolev.Lipschitz
public import GMTFoundations.Sobolev.WeakL2
public import GMTFoundations.BV.TotalVariation
public import GMTFoundations.Sobolev.FrechetKolmogorov
public import GMTFoundations.Sobolev.FrechetKolmogorovCompact
public import GMTFoundations.Sobolev.Rellich
public import GMTFoundations.BV.Compactness
public import GMTFoundations.Sobolev.AnnulusPoincare
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Order.LiminfLimsup

/-!
# Registry: functional-analytic facts

Textbook facts, in the generality needed for the compactness arguments in F. Abedin,
W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the
Bernoulli one-phase problem*, arXiv:2609.14981 ("the paper"): the ε → 0 and t → ∞ limits
(Prop 4.1, Thm 3.10), Lemma 6.3, and directional stability (Lemma 2.12).

References: L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in
Mathematics 19, AMS, 2010, doi:10.1090/gsm/019; L. C. Evans and R. F. Gariepy, *Measure Theory
and Fine Properties of Functions*, revised ed., CRC Press, 2015, doi:10.1201/b18333;
L. Ambrosio, N. Fusco and D. Pallara, *Functions of Bounded Variation and Free Discontinuity
Problems*, Oxford University Press, 2000, doi:10.1093/oso/9780198502456.001.0001; H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
Springer, 2011, doi:10.1007/978-0-387-70914-7.

* `Registry.exists_tendstoWeakL2_subseq` (weak sequential compactness in `L²`) and
  `Registry.lintegral_weighted_sq_le_liminf` (weighted weak lower semicontinuity of `∫ |f|²`),
  `Registry.exists_tendstoLpLoc_subseq_of_H1Loc` (local Rellich compactness).
* `Registry.exists_tendstoLpLoc_subseq_of_TV` (BV compactness in `L¹_loc`),
  `Registry.weightedTV_le_liminf`, `Registry.weightedTVₓ_le_liminf` (lower semicontinuity of the
  weighted total variation, defined by duality), `Registry.frechetKolmogorov_uniform_translation`
  and `Registry.frechetKolmogorov_exists_subseq` (Riesz–Fréchet–Kolmogorov).
* `Registry.memH1Loc_gradient_of_locallyLipschitzOn` (Lipschitz functions are Sobolev).
* `Registry.poincare_annulus_zero_outer` (Poincaré inequality on an annulus).

All ten items are proved in gmt-foundations v0.1.0. Each body is a one-line call to the
`GMTFoundations` theorem of the same name; the docstrings give the file there.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Gradient

@[expose] public section

namespace PerronVariational

namespace Registry

/-! ### Weak `L²` compactness, lower semicontinuity, Rellich -/

section WeakL2

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Weak sequential compactness in `L²`.** A sequence bounded in `L²(Ω, μ; F)`
(`F` a finite-dimensional real inner product space) has a subsequence converging weakly in
`L²(Ω, μ; F)`.

A result from the literature: Evans, Appendix D.4, Theorem 3 (weak compactness in reflexive
spaces; `L²` is a Hilbert space). Paper: proof of Prop 4.1 ("along a subsequence `u_ε` weakly
converges ... in `H¹_loc(U_∞)`", and `∂ₜu_ε ⇀ ∂ₜu` weakly in `L²(U_∞)`), proof of Thm 3.10,
Step 1; proof of Cor 2.13.

Proved in gmt-foundations v0.1.0 (`GMTFoundations/Sobolev/WeakL2.lean`):
`GMTFoundations.exists_tendstoWeakL2_subseq`, via sequential Banach–Alaoglu. -/
theorem exists_tendstoWeakL2_subseq (μ : Measure X) (Ω : Set X) (f : ℕ → X → F) (C : ℝ)
    (hf : ∀ n, MemLp (f n) 2 (μ.restrict Ω))
    (hC : ∀ n, eLpNorm (f n) 2 (μ.restrict Ω) ≤ ENNReal.ofReal C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : X → F, TendstoWeakL2 μ Ω (fun n ↦ f (φ n)) f₀ atTop :=
  GMTFoundations.exists_tendstoWeakL2_subseq μ Ω f C hf hC

-- keep the registry signature (with `[FiniteDimensional ℝ F]`) unchanged
set_option linter.unusedSectionVars false in
/-- **Weighted weak lower semicontinuity of `∫ |f|²`.** If `f_i ⇀ f₀` weakly in
`L²(Ω, μ; F)` along a filter `l`, and `η` is measurable with `0 ≤ η ≤ C`, then
`∫_Ω η |f₀|² ≤ liminf_l ∫_Ω η |f_i|²`. (With `η = 1` and `f = ∇u` this is the weak lower
semicontinuity of the Dirichlet energy.)

A result from the literature: Evans, Appendix D.4 (weak convergence: the norm is weakly lower
semicontinuous), applied to the weighted inner product `∫ η ⟨·, ·⟩`. Paper: proof of Lemma 4.2,
the dissipation inequality in Prop 4.1, proof of Lemma 2.12, proof of Thm 3.10, Step 2.

Proved in gmt-foundations v0.1.0 (`GMTFoundations/Sobolev/WeakL2.lean`):
`GMTFoundations.lintegral_weighted_sq_le_liminf` (integrate `η |f_i - f₀|² ≥ 0` and test the weak
convergence against `η f₀`). -/
theorem lintegral_weighted_sq_le_liminf {ι : Type*} {l : Filter ι} (μ : Measure X) (Ω : Set X)
    (f : ι → X → F) (f₀ : X → F) (hf : TendstoWeakL2 μ Ω f f₀ l) (η : X → ℝ)
    (hη : Measurable η) (hη0 : ∀ x, 0 ≤ η x) (C : ℝ) (hηC : ∀ x, η x ≤ C) :
    ∫⁻ x in Ω, ENNReal.ofReal (η x * ‖f₀ x‖ ^ 2) ∂μ ≤
      liminf (fun i ↦ ∫⁻ x in Ω, ENNReal.ofReal (η x * ‖f i x‖ ^ 2) ∂μ) l :=
  GMTFoundations.lintegral_weighted_sq_le_liminf μ Ω f f₀ hf η hη hη0 C hηC

end WeakL2

variable {d : ℕ}

/-- **Local Rellich compactness.** Let `U ⊆ ℝᵈ` be open and `u_n ∈ H¹_loc(U)` with weak gradients
`G_n` (carried as explicit data), bounded in `L²(K)` together with `G_n` for every compact `K ⊆ U`.
Then a subsequence converges in `L²_loc(U)`.

A result from the literature: Rellich–Kondrachov, Evans, §5.7, Theorem 1 (on balls `B ⊂⊂ U`),
plus a diagonal argument over a countable cover of `U` by balls. Paper: proofs of Prop 4.1 and
Lemma 4.2 ("strong convergence of `u_ε` in `L²`"), proof of Thm 3.10, Step 1.

Proved in gmt-foundations v0.1.0 (`GMTFoundations/Sobolev/Rellich.lean`):
`GMTFoundations.exists_tendstoLpLoc_subseq_of_H1Loc` (cut-offs `ζ u_n`, the translation estimate
`‖w(· + h) - w‖₂ ≤ |h| ‖∇w‖₂` by duality, Fréchet–Kolmogorov in `L²`, and compactness of a countable
product of compact sets in place of the diagonal argument). -/
theorem exists_tendstoLpLoc_subseq_of_H1Loc {U : Set (E d)} (hU : IsOpen U)
    (u : ℕ → E d → ℝ) (G : ℕ → E d → E d) (hG : ∀ n, MemH1Loc U (u n) (G n))
    (hbdd : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ, ∀ n,
      eLpNorm (u n) 2 (volume.restrict K) ≤ ENNReal.ofReal C ∧
        eLpNorm (G n) 2 (volume.restrict K) ≤ ENNReal.ofReal C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ : E d → ℝ, Measurable u₀ ∧
      TendstoLpLoc 2 volume U (fun n ↦ u (φ n)) u₀ atTop :=
  GMTFoundations.exists_tendstoLpLoc_subseq_of_H1Loc hU u G hG hbdd

/-! ### BV compactness, lower semicontinuity of total variation, Fréchet–Kolmogorov -/

/-- **BV compactness in `L¹_loc`.** Let `U ⊆ ℝᵈ` be open and `χ_n` measurable
with `|χ_n| ≤ M` on `U` and `sup_n ∫_V |∇χ_n| < ∞` for every open `V ⊂⊂ U` (total variation
defined by duality). Then a subsequence converges in `L¹_loc(U)`.

A result from the literature: Ambrosio–Fusco–Pallara, Theorem 3.23 (compactness in `BV_loc`).
Paper: proof of Thm 3.10, Step 3 ("Applying compactness in BV").

Proved in gmt-foundations v0.1.0 (`GMTFoundations/BV/Compactness.lean`):
`GMTFoundations.exists_tendstoLpLoc_subseq_of_TV` (cut-offs `ζ χ_n` have total variation on `ℝᵈ`
bounded by `TV_V(χ_n) + M ‖∇ζ‖₁`; `∫ |w(· + h) - w| ≤ |h| TV(w)` by duality; then Fréchet–Kolmogorov
in `L¹` as for `exists_tendstoLpLoc_subseq_of_H1Loc`). -/
theorem exists_tendstoLpLoc_subseq_of_TV {U : Set (E d)} (hU : IsOpen U) (χ : ℕ → E d → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (χ n) (volume.restrict U))
    (hbdd : ∃ M : ℝ, ∀ n, ∀ x ∈ U, |χ n x| ≤ M)
    (hTV : ∀ V, IsOpen V → CompactlyContained V U → ∃ P : ℝ, ∀ n,
      totalVariationOn V (χ n) ≤ ENNReal.ofReal P) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀ : E d → ℝ, Measurable χ₀ ∧
      TendstoLpLoc 1 volume U (fun n ↦ χ (φ n)) χ₀ atTop :=
  GMTFoundations.exists_tendstoLpLoc_subseq_of_TV hU χ hmeas hbdd hTV

-- keep the registry signature (with the unused `IsOpen` hypothesis) unchanged
set_option linter.unusedVariables false in
/-- **Lower semicontinuity of the weighted total variation.** Let `U ⊆ ℝᵈ` be
open, `χ_i, χ₀` locally integrable on `U` with `χ_i → χ₀` in `L¹_loc(U)` along `l`. Then for any
weight `η`, `∫_U η |∇χ₀| ≤ liminf_l ∫_U η |∇χ_i|` (weighted total variation defined by duality,
`sup {∫ χ div ψ : ψ ∈ C¹_c, |ψ| ≤ η}`).

A result from the literature: Ambrosio–Fusco–Pallara, Remark 3.5 / Proposition 3.6 (lower
semicontinuity of the variation measure under `L¹_loc` convergence); immediate from the duality
definition. Paper: Prop 4.1(iii), Thm 3.10, Step 3.

Proved in gmt-foundations v0.1.0 (`GMTFoundations/BV/TotalVariation.lean`):
`GMTFoundations.weightedTV_le_liminf` (sup of `L¹_loc`-continuous functionals; the hypothesis `hU`
is not needed). -/
theorem weightedTV_le_liminf {ι : Type*} {l : Filter ι} {U : Set (E d)} (hU : IsOpen U)
    (η : E d → ℝ) (χ : ι → E d → ℝ) (χ₀ : E d → ℝ) (hχ : ∀ i, LocallyIntegrableOn (χ i) U)
    (hχ₀ : LocallyIntegrableOn χ₀ U) (hconv : TendstoLpLoc 1 volume U χ χ₀ l) :
    weightedTV U η χ₀ ≤ liminf (fun i ↦ weightedTV U η (χ i)) l :=
  GMTFoundations.weightedTV_le_liminf η χ χ₀ hχ hχ₀ hconv

-- keep the registry signature (with the unused `IsOpen` hypothesis) unchanged
set_option linter.unusedVariables false in
/-- **Lower semicontinuity of the space-time weighted spatial total variation.** Space-time
analogue of `weightedTV_le_liminf` for `weightedTVₓ` (paper (3.13)).

A result from the literature: as for `weightedTV_le_liminf`. Paper: proof of Prop 4.1(iii) ("the
lower semicontinuity of the weighted total variation under `L¹_loc` convergence").

Proved in gmt-foundations v0.1.0 (`GMTFoundations/BV/TotalVariation.lean`):
`GMTFoundations.weightedTVₓ_le_liminf`. -/
theorem weightedTVₓ_le_liminf {ι : Type*} {l : Filter ι} {Ω : Set (E d × ℝ)} (hΩ : IsOpen Ω)
    (η : E d × ℝ → ℝ) (χ : ι → E d × ℝ → ℝ) (χ₀ : E d × ℝ → ℝ)
    (hχ : ∀ i, LocallyIntegrableOn (χ i) Ω) (hχ₀ : LocallyIntegrableOn χ₀ Ω)
    (hconv : TendstoLpLoc 1 volume Ω χ χ₀ l) :
    weightedTVₓ Ω η χ₀ ≤ liminf (fun i ↦ weightedTVₓ Ω η (χ i)) l :=
  GMTFoundations.weightedTVₓ_le_liminf η χ χ₀ hχ hχ₀ hconv

section FrechetKolmogorov

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Fréchet–Kolmogorov, necessity.** In a finite-dimensional real normed space
with an additive Haar measure `μ`, if `f_n → f` in `L¹(μ)` (all integrable), then the family
`{f_n}` is uniformly continuous under translations:
`sup_n ‖f_n(· + h) - f_n‖_{L¹} → 0` as `h → 0`.

A result from the literature: Brezis, Theorem 4.26 and Corollary 4.27 (Riesz–Fréchet–Kolmogorov),
necessity part (relatively compact sets in `L^p` are uniformly `L^p`-equicontinuous under
translations). Paper: proof of Lemma 4.3, (4.10).

Proved in gmt-foundations v0.1.0 (`GMTFoundations/Sobolev/FrechetKolmogorov.lean`):
`GMTFoundations.frechetKolmogorov_uniform_translation` (continuity of translation in `L¹` via
compactly supported continuous approximants). -/
theorem frechetKolmogorov_uniform_translation (μ : Measure V) [μ.IsAddHaarMeasure]
    (f : ℕ → V → ℝ) (f₀ : V → ℝ) (hf : ∀ n, Integrable (f n) μ) (hf₀ : Integrable f₀ μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (f n - f₀) 1 μ) atTop (𝓝 0)) :
    ∀ δ > 0, ∃ ρ > 0, ∀ n, ∀ h : V, ‖h‖ < ρ →
      ∫ x, |f n (x + h) - f n x| ∂μ < δ :=
  GMTFoundations.frechetKolmogorov_uniform_translation μ f f₀ hf hf₀ hconv

/-- **Fréchet–Kolmogorov, sufficiency.** In a finite-dimensional real normed
space with an additive Haar measure `μ`, a sequence of integrable functions, bounded in `L¹`,
vanishing outside a fixed compact set `K`, and uniformly continuous under translations in `L¹`,
has a subsequence converging in `L¹(μ)`.

A result from the literature: Brezis, Theorem 4.26 and Corollary 4.27 (Riesz–Fréchet–Kolmogorov).
Paper: proof of Lemma 4.3 (compactness of `e_ε`).

Proved in gmt-foundations v0.1.0 (`GMTFoundations/Sobolev/FrechetKolmogorovCompact.lean`):
`GMTFoundations.frechetKolmogorov_exists_subseq` (ball averages + Arzelà–Ascoli). -/
theorem frechetKolmogorov_exists_subseq (μ : Measure V) [μ.IsAddHaarMeasure] (f : ℕ → V → ℝ)
    (hf : ∀ n, Integrable (f n) μ) (C : ℝ) (hC : ∀ n, ∫ x, |f n x| ∂μ ≤ C) (K : Set V)
    (hK : IsCompact K) (hsupp : ∀ n, ∀ x ∉ K, f n x = 0)
    (htrans : ∀ δ > 0, ∃ ρ > 0, ∀ n, ∀ h : V, ‖h‖ < ρ → ∫ x, |f n (x + h) - f n x| ∂μ < δ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : V → ℝ, Integrable f₀ μ ∧
      Tendsto (fun n ↦ eLpNorm (f (φ n) - f₀) 1 μ) atTop (𝓝 0) :=
  GMTFoundations.frechetKolmogorov_exists_subseq μ f hf C hC K hK hsupp htrans

end FrechetKolmogorov

/-! ### Lipschitz functions are Sobolev -/

/-- **For locally Lipschitz `u`, the a.e. gradient is the weak gradient.** If
`U ⊆ ℝᵈ` is open and `u` is locally Lipschitz on `U`, then `u ∈ H¹_loc(U)` with weak gradient
equal to the pointwise gradient `∇u` (which exists a.e. by Rademacher's theorem; `∇u = 0` at
points of non-differentiability).

A result from the literature: Evans–Gariepy, Theorem 3.2 (Rademacher) and Theorem 4.5 (locally
Lipschitz functions belong to `W^{1,∞}_loc`, with weak gradient equal to the a.e. gradient). Proved
in gmt-foundations v0.1.0 (`GMTFoundations/Sobolev/Lipschitz.lean`):
`GMTFoundations.memH1Loc_gradient_of_locallyLipschitzOn` (McShane extension + Mathlib's
`LipschitzWith.integral_lineDeriv_mul_eq`). Paper: used implicitly whenever `J_Q(u; ·)` or `∇u` is
taken for a locally Lipschitz `u` (e.g. Def 2.11 for the Perron solutions in Lemma 6.3; Lemma 2.12;
Prop 2.14). -/
theorem memH1Loc_gradient_of_locallyLipschitzOn {U : Set (E d)} {u : E d → ℝ} (hU : IsOpen U)
    (hu : LocallyLipschitzOn U u) : MemH1Loc U u (∇ u) :=
  GMTFoundations.memH1Loc_gradient_of_locallyLipschitzOn hU hu

/-! ### Poincaré inequality on an annulus -/

/-- **Poincaré inequality on an annulus with zero outer trace.** There is a
constant `C ≥ 0` (depending only on `d`) such that: if `U` is open, `w ∈ H¹_loc(U)` with weak
gradient `G`, `B_R(x) ⊂⊂ U` (`closedBall x R ⊆ U`), `w = 0` a.e. on `U \ B_R(x)` (zero trace on
`∂B_R`, encoded as vanishing a.e. outside the ball), and `R / 2 ≤ r < R`, then
`∫_{B_R \ B_r} w² ≤ C (R - r)² ∫_{B_R \ B_r} |G|²`.

A standard result (one-dimensional Poincaré inequality along rays, integrated in polar coordinates;
e.g. Evans, §5.6.1, Theorem 3 for the method). Paper: proof of Lemma 2.12, Step 1 ("the Poincaré
inequality on the annular domain `B₁ \ B_r` with zero outer-trace"). Proved in gmt-foundations
v0.1.0 (`GMTFoundations/Sobolev/AnnulusPoincare.lean`):
`GMTFoundations.poincare_annulus_zero_outer`, with `C = 4`. -/
theorem poincare_annulus_zero_outer (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (E d)) (w : E d → ℝ) (G : E d → E d) (x : E d) (R r : ℝ),
      IsOpen U → MemH1Loc U w G → 0 < R → closedBall x R ⊆ U → R / 2 ≤ r → r < R →
      (∀ᵐ y ∂(volume.restrict (U \ ball x R)), w y = 0) →
      ∫⁻ y in ball x R \ ball x r, ENNReal.ofReal (w y ^ 2) ≤
        ENNReal.ofReal (C * (R - r) ^ 2) *
          ∫⁻ y in ball x R \ ball x r, ENNReal.ofReal (‖G y‖ ^ 2) :=
  GMTFoundations.poincare_annulus_zero_outer d

end Registry

end PerronVariational

end
