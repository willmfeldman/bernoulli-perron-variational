# Differences between the formalization and the paper

This file lists every place where the Lean formalization differs from

> F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
> the Bernoulli one-phase problem*, [arXiv:2609.14981](https://arxiv.org/abs/2609.14981).

Numbers are those of arXiv:2609.14981v2. The second line of each **Result** cell is the result's
label in the TeX source. **Lean** names the main declarations; their docstrings give the details.
Routine formalization work (measurability, integrability, a.e. representatives) is not listed.

**Kinds of difference**

| Kind | Meaning |
|---|---|
| Encoding | The same notion, written differently (equivalent, or a standard convention). |
| Stronger | The Lean statement implies the paper's (weaker hypotheses or more conclusions). |
| Weaker | The Lean statement proves less than the paper's, but what is used. |
| Variant | Different hypotheses or conclusions; neither statement implies the other. |
| Route | Same statement, different proof. |
| Filled in | Lean proves a step the paper leaves implicit or sketches, or a case it does not discuss. |
| Not formalized | Not in Lean, and not needed. |

**Summary.** Theorem 1.1 and Corollary 1.2 hold in Lean as stated in the paper, and also for a
larger class of data (see [Data class](#data-class)). No difference weakens a headline result.

## Contents

- [Conventions used throughout](#conventions-used-throughout)
- [Data class](#data-class)
- [Section 1: main results](#section-1-main-results)
- [Section 2: stationary problem](#section-2-stationary-problem)
- [Section 3: parabolic problem](#section-3-parabolic-problem)
- [Section 4: the inner-variational limit](#section-4-the-inner-variational-limit)
- [Section 5: viscosity limits](#section-5-viscosity-limits)
- [Section 6: proof of the main theorem](#section-6-proof-of-the-main-theorem)
- [Appendix B: the semilinear problem](#appendix-b-the-semilinear-problem)
- [Results from the literature](#results-from-the-literature)
- [Examples](#examples)

## Conventions used throughout

All of these are **Encoding** differences.

| Notion | Paper | Lean | Declarations |
|---|---|---|---|
| C² domain (§1.2) | `∂U` is C² | `U = {ρ < 0}` for some `ρ ∈ C²(ℝᵈ)` with `∇ρ ≠ 0` on `∂U` | `HasC2Boundary`, `Setting` |
| Test functions (Defs 2.1, 2.4, 3.3, 3.5) | `C^∞(U)` or `C^∞(V̄ × [a, b])`, touching as a maximum on `E` | `C^∞` on all of `ℝᵈ` or `ℝᵈ × ℝ`, local touching; equivalent by cutoff. Subsolutions are tested with `φ₊` on `closure {u > 0}` (equivalent as `u ≥ 0`) | `IsViscSub`, `IsViscSuper`, `IsRelaxedSub` |
| Data `g` (Def 2.3) | `C²(Ū)` | `C²(ℝᵈ)`; a `C²(Ū)` function on a C² domain extends | `IsStrictSub` |
| Sobolev functions and energies | `H¹`, `H¹_loc`; finite energies | The weak gradient is carried as data; energies are `ℝ≥0∞`-valued lower integrals | `MemH1`, `MemH1Loc` |
| `u − v ∈ H¹₀(B)` (Def 2.15, Proposition 6.3) | Sobolev trace zero on a ball `B` | `v = u` a.e. on `U \ B` | `IsDownwardMinimizer` |
| `H¹₀(U)` (Figure 1) | Sobolev space | The extension by zero is in `H¹(ℝᵈ)` | `MemH10` |
| One-sided minimizers (Def 2.15) | Downward competitors `0 ≤ v ≤ u`; `u ≥ 0` continuous | Competitors `v ≤ u` (equivalent via `v₊`); `u ≥ 0` and continuity are not part of the predicate, and come from Thm 1.1(i) where it is used | `IsDownwardMinimizer`, `IsUpwardMinimizer` |
| Parabolic barriers (Def 3.2) | `C^{2,1}` near `V̄ × [a, b]` | `C^∞` on `ℝᵈ × ℝ`; the sets `{φ > −a₀}`, `{\|φ\| ≤ a₀}` are taken in all of space-time | `IsClassicalStrictParaSubWith` |
| Parabolic notions (Defs 3.3, 3.5) | On `U × (0, T]` | On `U × I` for a general time set `I`; a test cylinder means `V` open bounded, `a < b`, `V̄ × [a, b] ⊆ U × I` | `IsParaSub`, `IsParaSuper`, `AdmissibleCyl` |
| Parabolic inner variational solutions (Def 3.8) | Any `T ≤ ∞`; `∇u ∈ L^∞_loc` | `T = ∞` only; local Lipschitz bounds in space; `∂ₜu` carried as data | `IsParaInnerVarSolution`, `HasWeakTimeDeriv` |
| Semilinear solutions (3.4) | Classical | `C^{2,1}` (`C¹` jointly, `C²` in `x`), two-sided time derivative; not `C^∞` since `Q` is only Lipschitz | `IsSemilinearSolution` |
| Weighted perimeter `∫ η \|∇χ\|` (3.14), Lemma 4.3 | Total variation | Defined by duality: sup of `∫ χ div ψ` over `ψ ∈ C¹_c`, `\|ψ\| ≤ η` | `weightedTVₓ` |
| Energy dissipation, Prop 3.12(ii), (B.1) | Equality | Inequality `≤`, which is all that is used | `IsWellPreparedFamily` |

## Data class

| Result | Kind | Difference | Lean |
|---|---|---|---|
| Definition 2.3<br>`d.strict-sub` | Stronger | The paper asks `Δg ≥ δ₀` (resp. `≤ −δ₀`) in `{g > −a₀}` and `a₀, δ₀ ≤ 1/2`. The main results are proved for the larger class with `Δg ≥ 0` (resp. `≤ 0`) and no bound on `a₀, δ₀`, which contains harmonic data. Used in Thm 1.1, Cor 1.2, Prop 3.12, Thm 3.13, Cor 5.4, Props 6.1, 6.2. The versions for the paper's class are `…_unif`. | `IsStrictSub`, `IsStrictSuper`; paper's class: `IsUnifStrictSub`, `main_smallest_unif` |

## Section 1: main results

| Result | Kind | Difference | Lean |
|---|---|---|---|
| Theorem 1.1<br>`t.main` | Stronger | Larger data class (above). | `main_smallest`, `main_largest` |
| | Encoding | "Minimizer locally around each free boundary point": for each free boundary point `x` there is `r > 0` with `B̄_r(x) ⊆ U` and `u` a minimizer in `B_r(x)`. | `MainSmallestStatement` |
| | Filled in | Part (iii) applies Proposition 6.3 to the problem restricted to a ball, with a C² defining function for the ball. | `main_smallest_of` |
| Corollary 1.2<br>`c.2d-structure` | Encoding | "Classical near `x₀`": `C^{1,γ}` free boundary graph, `u` C² harmonic in `{u > 0}`, `∇u` continuous up to the free boundary with `\|∇u\| = Q`. Blow-ups are locally uniform limits of `r⁻¹u(x₀ + r·)`. | `IsClassicalNear`, `IsBlowupLimit` |
| | Route | Smallest case: the blow-up `0` is excluded by Thm 2.9 (in a uniform form) rather than Thm 2.17, and flatness follows from that uniform non-degeneracy, without the Hausdorff convergence of Cor 2.18(i) or Lemma 2.19. | `flat_of_halfPlane_blowup` |
| | Route | Largest case: Lemma 2.19 only in the plane; `χ₀` is identified from the blow-up sequence of `χ` and the planar classification [Jerison–Kamburov]. | `perronLargest_flat_of_halfPlane` |
| | Filled in | Blow-ups of the smallest supersolution are supersolutions with slope `Q(x₀) + δ` for every `δ > 0`; `Q(x₀)\|y · e\|` with a larger slope is not a supersolution (explicit test function). | `isViscSuper_of_isBlowupLimit`, `not_isViscSuper_twoPlane` |

## Section 2: stationary problem

| Result | Kind | Difference | Lean |
|---|---|---|---|
| Lemma 2.5 (stability)<br>`l.super-stability` | Stronger | `Q` only continuous; limits along any filter. Proved here rather than cited. | `isViscSuper_of_tendstoLocallyUniformlyOn` |
| | Not formalized | The last sentence of (ii) (monotone sequences of subsolutions); see Prop 6.1. | |
| Lemma 2.6 (extremal solutions are viscosity solutions)<br>`l.extremal-viscosity` | Variant | Not a separate declaration; its conclusions are part of Props 6.1 and 6.2, which also give continuity on `Ū`. | `InnerSmallestStatement` |
| Lemma 2.8 (local minimality)<br>`l.local-minimality` | Weaker | `u` is assumed a viscosity super- (resp. sub-)solution, which the paper takes from Lemma 2.6. | `IsViscSuper.lt_of_isUnifStrictSub` |
| | Filled in | `g` is only C², so the proof tests with a smooth function with the same 1-jet and Laplacian lowered by less than `δ₀`; the maximum principle for viscosity subsolutions is proved. | `exists_smooth_le_of_contDiff_two`, `IsViscSub.le_of_laplacian_neg` |
| | Route | Larger data class: "`u > g`" becomes "`g < 0` at zeros of `u`" (polynomial test function); largest case by comparison with `g + ε(r² − \|y − x\|²)`. | `IsViscSuper.strictSub_lt_zero`, `IsViscSub.le_max_of_isStrictSuperWith` |
| Theorem 2.9 (non-degeneracy, smallest)<br>`t.smallest-super-non-degen` | Variant | Proved for Perron's smallest supersolution only (the case used), uniformly at points of `closure {u > 0}` near a free boundary point, for `r ≤ R/4`, sup over `B̄_r`. | `Setting.perronSmallest_uniformlyNondegenerate` |
| | Route | Barrier `A(1 − (ρ/\|x − z\|)^{2d})₊` instead of a harmonic function on an annulus (App. A.1). | |
| Theorem 2.10 (non-degeneracy, largest)<br>`t.largest-sub-non-degen` | Weaker | `d = 2` (as stated), `u` Lipschitz, C² and harmonic in `{u > 0}`, `r ≤ R/2`, sup over `B̄_r`; the constant depends on the Lipschitz constant. Prop 6.2 supplies the hypotheses. | `exists_le_of_isLocalLargestSub`, `Setting.perronLargest_nondegenerate_near_fb` |
| | Variant | App. A.2: Lemma A.1 in every dimension; Lemma A.2 in `d = 2`, in the directions used; Lemma A.3 with the same regularity. | `exists_le_of_exteriorBall`, `exists_notMem_closure_posSet_sphere` |
| | Filled in | The Riesz measure `Δu` and the spherical mean formula are constructed; the glued harmonic lift is shown to be a subsolution; in the covering, radii in `[T/2, T]` keep all balls in `B_{6T}`. | `exists_isRieszMeasure`, `mass_lower_bound_of_covering` |
| Lemma 2.12 (inner variational ⇒ subsolution)<br>`l.inner-variational-implies-subsoln` | Filled in | The Kriventsov–Weiss results are proved for Lipschitz `Q` (see [literature](#results-from-the-literature)). | `Registry.innerVar_dichotomy` |
| | Route | Closedness of `Σ^H` is not used; positive lower density of `{φ < 0}` from a scaled cone instead of density `1/2`. | `not_tendsto_density_one` |
| Lemma 2.13 (perimeter bound)<br>`l.perimeter-bound` | Variant | Bound `C L² r^{d−1}`, `C = C(d, Q_min)`, from the proof of Kriventsov–Weiss, Lemma 3.3, instead of `C(L + r‖∇Q²‖) r^{d−1}`; both give what Lemma 2.14 needs. | `PerimeterBound.perimeter_bound` |
| Lemma 2.14 (compactness)<br>`l.inner-compactness-stability` | Route | Proved here instead of citing Kriventsov–Weiss, Thm 9.3: Arzelà–Ascoli, BV compactness, Weyl's lemma, strong `L²_loc` gradient convergence by truncation, density from `C¹_c` to Lipschitz fields. | `InnerVarCompactness.innerVar_compactness_of_gradient_bound` |
| Lemma 2.16 (stability of one-sided minimizers)<br>`l.directionalStable` | Stronger | Varying `Qₙ` proved in full (the paper sketches it), with `Qₙ → Q` pointwise and `\|Qₙ\| ≤ Q_max`. | `isDownwardMinimizer_of_tendsto` |
| | Filled in | Harmonicity of the limit by Weyl's lemma (App. A.3). | `harmonic_of_tendsto` |
| Theorem 2.17 (non-degeneracy of downward minimizers)<br>`t.downward-min-non-degen` | Not formalized | Cor 1.2 uses Thm 2.9 instead. | |
| Corollary 2.18 (blow-ups)<br>`c.blow-up-directional` | Variant | The Hausdorff convergence in (i) is not stated (not used); precompactness is a separate lemma; hypotheses: `u` locally Lipschitz, `Q` continuous and bounded. | `blowup_isDownwardMinimizer`, `exists_isBlowupLimit` |
| | Filled in | Scaling invariance of Def 2.15, and Lemma 2.16 on domains exhausting `ℝᵈ`. | `isDownwardMinimizer_of_exhaust` |
| Lemma 2.19 (one-plane limit)<br>`l.one-plane-limit` | Weaker | Planar case only; see Cor 1.2. | `flat_or_pos_of_halfPlane_blowup` |
| Proposition 2.20 (two-plane solutions)<br>`p.two-plane-minimizing-props` | Route | (1): competitor `φ_α + tη`, `η = ((1 − \|x\|²)₊)²`, instead of harmonic replacement. (2): `L = 1`, competitor `min(φ_α, A(\|x · e\| − εη)₊)`. | `twoPlane_not_upwardMinimizer`, `twoPlane_not_downwardMinimizer_of_lt` |
| | Filled in | (3): absolute continuity of `H¹_loc` on lines in direction `e`; all slopes `q > 0` and directions (App. A.4). | `ae_slice_hasPrimitive`, `twoPlane_downwardMinimizer_iff` |

## Section 3: parabolic problem

| Result | Kind | Difference | Lean |
|---|---|---|---|
| Remark 3.4 (stationary ⇒ parabolic)<br>`r.statToPara` | Filled in | Both cases proved; (i) of Def 3.2 applies at the crossing point since `φ = u ≥ 0 > −a₀`, and (ii) only where `φ = 0`. | `IsViscSub.isParaSub_const`, `IsViscSuper.isParaSuper_const` |
| Proposition 3.6 (non-degeneracy of relaxed subsolutions)<br>`p.monotone-nondegen-relaxed` | Stronger | No continuity on `Ū × [0, T]`; any initial trace `u₀ ≤ u(·, t)` with `E₀ ∩ U ⊆ closure {u₀ > 0}`; also `E = closure {u > 0}`. | `IsParaRelaxedSub.isParaSub_of_monotone`, `IsParaRelaxedSub.eq_closure_posSetP_of_monotone` |
| | Route | Barrier `A(1 − exp(K − λ\|y − x₀\|²))` at scale `r`, no rescaling. | `nondegSpatialBarrier` |
| | Filled in | The test cylinder starts at a small positive time, as Def 3.5 requires. | |
| Theorem 3.7 (comparison)<br>`t.comparison` | Route | Proved in the dependency bernoulli-parabolic-comparison with pointwise strict barriers; the two barrier notions give the same sub- and supersolutions. | `Registry.para_strict_comparison`, `isParaSub_iff_bpc` |
| Definition 3.8 (parabolic inner variational solution)<br>`d.parabolic-inner` | Variant | Item (iv), `∂ₜu = Δu` in `{u > 0}`, is a separate predicate in weak form (4.6): concluded in Prop 4.1 and Thm 3.13, assumed in Thms 3.14, 3.16(ii) and Lemma 5.8. Thm 3.14 needs it: `u = 1 + \|x₁\|`, `χ ≡ 1` satisfies the rest. | `WeakHeatInPos` |
| Lemma 3.10 (supersolution profile)<br>`l.profile-super` | Route | Explicit reparametrization `η(p) = (1 + σ)p²/(p + σ)`; `Ψ` built by inverting a time map (no ODE theorem). | `profileSuper`, `profileSuper_tail` |
| | Weaker | Of (v), only what is used: `κ_θ̂` can be made small, and close to `1`. | `exists_superKappa_lt`, `exists_lt_superKappa` |
| Lemma 3.11 (well-prepared data)<br>`l.well-prepared` | Variant | Endpoint values `θ = 1/(1 + δ₀)`, `θ̂ = 1/(1 − δ₀)`; larger data class; `ε₀` depends on `(a₀, δ₀, β)`, resp. also `Q_min` and bounds on `\|∇g\|`, `\|Δg\|`. | `wellPrepared_sub`, `wellPrepared_super` |
| | Filled in | Parabolic versions used in Prop 5.3. | `profileSubEps_ineq`, `profileSuperEps_ineq` |
| Proposition 3.12 (semilinear well-posedness)<br>`p.semilinear-wellposed` | Variant | The data clause (Lemma 3.11) adds a Lipschitz-constant-on-`Ū` clause (a gradient bound does not give it for non-convex `U`); (iv) an `ε`-independent modulus; `ε < min(ε₀, 1)`; constants independent of `ε` and `g`. | `IsWellPreparedFamily`, `semilinear_wellposed` |
| | Variant | (vi) at level `ε` in both cases for `K ⊆ Ū \ closure {g > 0}`, and at every level `κ` in the increasing case for interior compact `K` (what Cor 5.4 uses). | `IsWellPreparedData.positivity_trace_small` |
| | Filled in | The bound in (ii) by comparison with `0` and `M + ε`; strong `H¹` convergence `g_ε → g₊`. | `IsSemilinearSolution.mem_Icc`, `tendsto_H1_of_isWellPreparedSub` |
| Theorem 3.13 (parabolic existence)<br>`t.parabolic-existence` | Stronger | Larger data class; extra conclusions: the weak heat equation (4.6), and `u = 0` on `K × [0, τ]` for compact `K ⊆ Ū \ closure {g > 0}` (increasing case); the constant in (3.13) does not depend on `g`. | `ParabolicExistenceStatement`, `ParabolicExistenceBddStatement` |
| | Variant | Bound `0 ≤ u ≤ M` for any `M ≥ sup_U \|g\|`; the modulus depends on a Lipschitz constant of `g` on `Ū` and on `M`. | `ParabolicExistenceBddStatement` |
| | Filled in | Gluing the limits on `U × (0, T]` to `U × (0, ∞)`, and extension to `Ū × [0, ∞)`. | `exists_limit_extension` |
| Theorem 3.14 (long-time limit, variational form)<br>`t.longtime-inner` | Variant | The weak heat equation (4.6) is a hypothesis (Def 3.8); `C_V` depends on `V`, the bound on `u`, `E₀` and the constants of (3.13), (3.14). | `LongtimeInnerStatement` |
| | Filled in | Step 1: passing (3.13) to (3.15) needs the backward time slices to converge too; proved from `∂ₜu ∈ L²` and the spatial Lipschitz bound. | `eventually_abs_sub_le_window`, `norm_gradient_le_of_tendsto_seq` |
| | Route | Step 2: (4.9) by localizing (4.6) in time (one null set of times), then truncating at levels `δ` with `\|{u = δ}\| = 0`; C² in `{u_∞ > 0}` by Weyl's lemma. | `ae_heat_slice`, `harmonic_limit` |
| | Filled in | Step 3: the slicing inequality and independence of the time translate. Step 4: density from `C¹_c` to Lipschitz fields. | `setLIntegral_sliceTV_le`, `innerVar_lipschitz` |
| | Stronger | The full limit `t → ∞` for monotone flows (remark after Lemma 5.8) is stated separately. | `LongtimeInnerMonotoneStatement` |
| Theorem 3.16 (long-time limit, viscosity form)<br>`t.longtime-viscosity` | Variant | (i): boundedness not used. (ii): the weak heat equation is a hypothesis. | `LongtimeViscIncreasingStatement`, `LongtimeViscInnerStatement` |

## Section 4: the inner-variational limit

| Result | Kind | Difference | Lean |
|---|---|---|---|
| Estimates for arbitrary solutions (after Prop 4.1)<br>`eqn:inftyBound` | Filled in | (3.10) for any bounded continuous data, by approximation; (3.9) for any `H¹` data. | `semilinear_interiorLipEst`, `semilinear_dissipation` |
| | Route | Interior equicontinuity in time directly from (3.10), (4.1), (3.9). | `semilinear_time_equicontinuous` |
| | Weaker | (4.1) as `u ≤ max(M, ε)` for `M ≥ sup g_ε`, which suffices. | `semilinear_nonneg_le_max` |
| Identity (4.2)<br>`eqn:innerVarEps` | Filled in | Proved for `ξ ∈ C¹_c`; `Q²` replaced near `spt ξ` by a bounded Lipschitz extension, since `∇(Q²)` exists only a.e. | `semilinear_innerVar_identity` |
| Proposition 4.1 (`ε → 0` limit)<br>`p.eps-inner-limit` | Variant | Lean also assumes a limit `g ∈ H¹` with `g_ε ⇀ g` (unused); (i) records weak `L²(U × (0, T))` convergence of `∇u_{ε_j}` (strong `L²_loc` is Lemma 4.2); (ii) also gives (4.6). | `EpsInnerLimitStatement`, `eps_inner_limit` |
| | Filled in | (3.13) passes to the limit on shrinking cylinders; dissipation by Fatou on time slices and weak lower semicontinuity. | `interiorLipEst_of_tendsto`, `dissipationIneq_of_tendsto` |
| Lemma 4.2 (strong gradient convergence)<br>`lem:strongGrad` | Variant | Hypotheses: local uniform convergence, weak `L²` convergence of `∇uₙ`, `∂ₜuₙ`, energy bounds on slices; holds for the whole sequence. | `tendstoLpLoc_gradₓ_semilinear` |
| | Route | No time chain rule for the limit; (4.6) proved directly in weak form. | `weakHeat_of_tendsto` |
| Lemma 4.3 (convergence of `χ_ε`)<br>`lem:chiConverge` | Route | `∂ₜ∇u_ε` is not available when `Q` is only Lipschitz: integrate by parts in `x` first, then difference quotients in `t` (App. A.5). | `integral_norm_grad_sq_sub_mul` |
| | Route | Compactness from `L¹` translation estimates and Fréchet–Kolmogorov, instead of a Cauchy argument. | `exists_tendstoLpLoc_chiEps_subseq` |
| | Filled in | (4.7) and the perimeter bound for `C¹_c` weights, as (3.14) requires. | |

## Section 5: viscosity limits

| Result | Kind | Difference | Lean |
|---|---|---|---|
| Lemmas 5.1, 5.2 (limits of maxima, ordering)<br>`l.limit-max`, `l.prec-ordering-convergence` | Stronger | Suprema in `[−∞, ∞]` (covers `E* ∩ F = ∅`); no closedness of `E_j` or `E`, no continuity of `w_j`; any filter. | `limsup_max_eq`, `precOn_eventually_of_tendsto` |
| Proposition 5.3 (`ε → 0` limit, viscosity form)<br>`p.semilinear-limit-viscosity` | Stronger | Only the equation on `U × (0, T]` and `u_j ≥ 0`; no boundary or initial data. | `SemilinearLimitRelaxedStatement` |
| | Filled in | Step 1: a first crossing at the top time `t₀ = b`, by enlarging the cylinder. Parabolic versions of Lemma 3.11. | `exists_extend_cyl` |
| | Route | Step 2: no first touching point; compactness margins replace two uses of Lemma 5.2. | `exists_bdry_margin`, `exists_infDist_lt_of_neg_lt` |
| Corollary 5.4 (increasing case)<br>`cor:increasing` | Variant | `E = closure {u > 0}` on `U × [0, T]` (including `t = 0`); continuity and boundary values come from Thm 3.13 instead. | `SemilinearLimitIncreasingStatement` |
| | Route | Uses Prop 3.12(v) on interior compact sets and `u ≥ g₊`, not (iv). | |
| Propositions 5.5, 5.6, Corollary 5.7 (long-time limits)<br>`p.subsolution-limit`, `p.supersolution-limit`, `c.monotone-long-time` | Stronger | `u` need not be bounded. | `longtime_relaxedSub`, `longtime_super`, `longtime_sub_increasing` |
| | Filled in | The unbounded test cylinders `B_r × (T, ∞)` are replaced by bounded ones, as Def 3.5 requires. | |
| Lemma 5.8 (inner + viscosity limit)<br>`l.subsolution-inner-limit` | Variant | Formalized as Thm 3.16(ii): time monotonicity replaces the convergence hypothesis; the weak heat equation is a hypothesis. The remark's "locally uniform by Arzelà–Ascoli" is proved. | `longtime_viscosity_inner_of`, `lipschitzOnWith_of_norm_gradient_le` |

## Section 6: proof of the main theorem

| Result | Kind | Difference | Lean |
|---|---|---|---|
| Proposition 6.1 (smallest supersolution)<br>`p.inner-smallest` | Stronger | Also concludes `u ∈ C(Ū)`. | `InnerSmallestStatement` |
| | Route | The subsolution property of `û` comes from Lemma 2.12 (Kriventsov–Weiss), not from Thm 3.16(i) and Lemma 2.5(ii), so the monotonicity of `a ↦ u_{a,∞}` is not needed; the `a → 0` compactness uses only the `L^∞` bound and (3.15). | `inner_smallest_of`, `exists_innerVar_limit` |
| | Filled in | Restriction from `(0, ∞)` to `(0, T]`; strict ordering near the parabolic boundary from pointwise strictness. | `IsParaSub.Ioc_of_Ioi`, `mem_nhdsSet_precOn` |
| Proposition 6.2 (largest subsolution)<br>`p.inner-largest` | Filled in | Strict ordering on the parabolic boundary checked on `closure {v > 0}`, then on a neighbourhood. | `inner_largest_of`, `largest_shift` |
| Proposition 6.3 (one-sided minimality)<br>`p.downward` | Weaker | `u` assumed locally Lipschitz, C² and harmonic in `{u > 0}` (the paper cites these for local extremal solutions); Thm 1.1(ii) supplies them. | `DirectionalStatement`, `directional` |
| | Route | Continuity of the obstacle minimizer up to `∂B` by Caccioppoli and De Giorgi boundary oscillation decay, instead of citing [Giusti]. | `obstacle_below_continuousOn` |
| | Route | Step 2: the perturbation is applied in a slightly larger ball, so touching points on `∂B` need no separate case. | `upwardMinimizer_of_localLargest` |

## Appendix B: the semilinear problem

| Result | Kind | Difference | Lean |
|---|---|---|---|
| §B.1 (existence, comparison)<br>`s.basic-properties` | Route | From the dependency parabolic-basic-theory. | `Registry.semilinear_exists`, `Registry.semilinear_comparison` |
| (B.1) (energy dissipation)<br>`eqn:dissipation` | Route | As an inequality for `H¹` data, by truncation and Steklov averages, with only interior integrations by parts. | `semilinear_energy_dissipation` |
| Proposition B.2 (interior Lipschitz)<br>`p.localLip` | Variant | Smooth `Q` locally; Lipschitz `Q` for solutions of (3.4) with Lipschitz data, by approximation. Constant independent of `Q_min`; all `ε > 0`. | `bernstein_interior_smooth`, `exists_interiorLipEst` |
| | Route | No rescaling; one space-time cutoff; cross term handled by `∇z = 0` at the maximum; `ψ` only continuous. | `zmax_bound` |
| Proposition B.3 (Lipschitz up to `t = 0`)<br>`p.localLip-initial-data` | Stronger | No restriction `T ≤ 4r²` (smooth `Q`). | `bernstein_initial_smooth` |
| Lemma B.4 (global Lipschitz)<br>`l.lipschitz-initial` | Route | Prop B.3 for all `t > 0`; mollification by quantitative comparison. | `exists_norm_gradₓ_le` |
| (B.11) (exterior balls)<br>`e.exterior-ball` | Encoding | Used for the single radius `ρ₀`. | `Setting.exists_uniformExteriorBall` |
| Lemma B.6 (lateral boundary modulus)<br>`l.attainment-lateral` | Route | Exponential barrier `η`. Lower bound: the composed barrier `(Φ_{ε,1/2}(g(x₀) − 2σ − Aη))₊` for `c_{1/2}ε ≤ σ`, and for larger `ε` the classical subsolution `g(x₀) − 2σ − A′η` with a second constant `A′`, instead of the split at `ε = σ/4` with `w` itself. | `exists_boundary_estimate` |
| Lemma B.7, Proposition B.5 (time modulus)<br>`l.initial-L2`, `p.attainment` | Route | Lemma B.7 not formalized; the time modulus from barriers only (restart at time `s`, caloric upper barrier, time-dependent composed lower barrier). | `exists_modulus`, `exists_initial_estimate` |
| Lemma B.8, Corollary B.9 (no outward jump)<br>`l.positivity-trace`, `c.positivity-no-jump` | Weaker | The levels used: `κ = 1` for `μ < 1`, all `κ` for `μ = 1`; `τ` also depends on a Lipschitz constant; Cor B.9 for interior points (via Prop 3.12(v)). | `Semilinear/PositivityTrace.lean` |
| | Stronger | Any radius `r > 0` (the paper assumes `r ≤ 1`). | |
| | Route | Heat barrier on `∂B_{2r}` instead of Prop B.5; the explicit radial barrier `b(1 − exp((d + 1)(1 − \|x − x₀\|²/(2r²))))` with `a₀ = b`, instead of the extended `η`. | `trapBarrier` |

## Results from the literature

Each cited result is stated in `PerronVariational/Registry/` and proved here or in a dependency.
Only the ones used in a different form are listed.

| Cited result | Used in | Difference | Lean |
|---|---|---|---|
| Kriventsov–Weiss, Thm 1.2(i), Prop 3.5, Lemma 8.3 | Lemma 2.12 | Stated for `Q ≡ 1`; proved for Lipschitz `Q` with positive bounds, as the paper says they extend. | `Registry.innerVar_dichotomy`, `Registry.isViscSolution_diff_highDensitySet` |
| `ε`-regularity [Caffarelli; De Silva] | Cor 1.2 | Two-sided flatness form of De Silva. | `Registry.isClassicalNear_of_flat` |
| Weiss monotonicity, homogeneous blow-ups | Cor 1.2 | Proved for Lipschitz `Q`. | `Registry.blowup_homogeneous` |
| Lipschitz estimate [Caffarelli–Salsa, Lemma 11.19] | Cor 1.2, Proposition 6.3 | Qualitative form. | `Registry.locallyLipschitzOn_of_isViscSolution` |
| Obstacle problems [Giusti] | Proposition 6.3 | Continuity in the open ball only; continuity up to `∂B` proved separately. | `Registry.obstacle_below_exists` |
| Boundary modulus of harmonic functions | App. B | Proved with exterior-ball barriers. | `Registry.dirichlet_harmonic_modulus` |

## Examples

| Result | Kind | Difference | Lean |
|---|---|---|---|
| Figure 1 (necklace)<br>`f.necklace` | Variant | `N = 100` holes of radius `1/20` on the circle of radius `(1/10)/sin(π/100)`, inside `B₄(0)`, `Q ≡ 1`; the figure has 18 unit discs and no outer boundary. Separating the largest subsolution from the minimizer needs about 40 holes or more, and the outer circle makes `U` bounded. Data `gSub`, `gSuper` agree on `∂U`, in the larger data class. | `necklace_example`, `NecklaceExampleStatement` |
| | Stronger | Also proves that a minimizer exists, that the three solutions are pairwise distinct, and that the smallest supersolution has two-plane points (Remark 1.3). | |
| Two-disc example | — | Not in the paper. | `model_example` |
| Figure 2<br>`fig:precFail` | Not formalized | | |
