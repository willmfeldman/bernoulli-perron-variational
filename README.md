# bernoulli-perron-variational

`PerronVariational` is a Lean 4 / Mathlib formalization of

> F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
> the Bernoulli one-phase problem*, [arXiv:2609.14981](https://arxiv.org/abs/2609.14981).

The paper studies the one-phase Bernoulli free boundary problem

  Δu = 0 in {u > 0} ∩ U,   |∇u| = Q(x) on ∂{u > 0} ∩ U,

on a bounded C² domain `U ⊂ ℝᵈ`, with a Lipschitz coefficient `0 < Qmin ≤ Q ≤ Qmax`. Its main
theorem says that Perron's extremal solutions are also variational. The smallest supersolution
above a strict subsolution, and the largest subsolution below a strict supersolution, are
viscosity solutions and inner variational solutions. They are also one-sided minimizers of the
Alt–Caffarelli energy `J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}` near every free boundary point. The
proof runs through a semilinear parabolic approximation, its singular limit, and the long-time limit.
In the plane this gives the structure of the free boundary: the largest subsolution is classical,
and the smallest supersolution is classical except on a closed set where every blow-up is a
two-plane solution.

The library has about 58,000 lines of Lean in 170 files. It is
sorry-free, and the headline theorems depend only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Headline theorems

Result numbers are those of arXiv:2609.14981v2. Each statement is a `…Statement : Prop` in
`PerronVariational/Statements/`, proved by the theorem listed. `formalization.yaml` states the
certified results in words.

| Result | Paper | Lean theorem |
|---|---|---|
| The smallest supersolution above a strict subsolution is a viscosity solution, an inner variational solution, and a local downward minimizer of `J_Q` near each free boundary point | Theorem 1.1 | `main_smallest` |
| The largest subsolution below a strict supersolution is a viscosity solution, an inner variational solution, and a local upward minimizer of `J_Q` near each free boundary point | Theorem 1.1 | `main_largest` |
| In `ℝ²`, the free boundary of the smallest supersolution splits into a relatively open regular part, where the solution is classical, and a part where every blow-up is `Q(x₀)\|y · e\|` | Corollary 1.2(i) | `corollary_2d_smallest` |
| In `ℝ²`, the largest subsolution is classical near every free boundary point | Corollary 1.2(ii) | `corollary_2d_largest` |

The paper explains the ideas of the proof. `formalization.yaml` lists the main intermediate results
(Theorem 3.13, Propositions 3.12 and 4.1, Theorem 3.14, Proposition 6.3, Theorem 2.10) with their Lean
names.

## Deviations from the paper

[`DEVIATIONS.md`](DEVIATIONS.md) lists every place where the formalization differs from the paper,
result by result: equivalent encodings, statements that are stronger, weaker or differently
hypothesized, different proof routes, and steps the paper leaves implicit that are proved here.
The docstring of each declaration concerned gives the details. The main points:

- **Data class of the main theorems.** `main_smallest`, `main_largest` and Corollary 1.2 take `g`
  in a larger class than Definition 2.3: condition (i) is `Δg ≥ 0` (resp. `Δg ≤ 0`) instead of
  `Δg ≥ δ₀` (resp. `Δg ≤ −δ₀`), and `a₀, δ₀` need not be at most `1/2`, so harmonic data are
  allowed. These theorems therefore strengthen the paper's. The versions for the paper's class are
  `main_smallest_unif`, `main_largest_unif`, `corollary_2d_smallest_unif` and
  `corollary_2d_largest_unif`. The two examples use harmonic data, so they need the larger class.
- **Encodings.** "`U` has C² boundary" is encoded as `U = {ρ < 0}` for some `ρ ∈ C²(ℝᵈ)` with
  `∇ρ ≠ 0` on `∂U`. Test functions are smooth on all of `ℝᵈ` (or `ℝᵈ × ℝ`), and data are
  `C²(ℝᵈ)`. An `H¹` function carries its weak gradient as data, energies are `ℝ≥0∞`-valued, and
  "`u − v ∈ H¹₀(B)`" for a ball `B` is encoded as "`v = u` a.e. off `B`". For parabolic inner
  variational solutions, "`∇u ∈ L^∞_loc`" is encoded as local Lipschitz bounds in space, `∂ₜu` is
  carried as data, and `∫ η |∇χ|` is defined by duality.
- **The heat equation in Definition 3.8.** Item (iv) of Definition 3.8 is not part of the Lean
  definition. Its weak form is a separate predicate, which Proposition 4.1 and Theorem 3.13
  provide and Theorems 3.14 and 3.16(ii) assume.
- **Proof routes.** Several steps are proved by a different argument from the paper's, mostly to
  avoid regularity that a Lipschitz `Q` does not give, or to replace a citation by a proof. For
  example: the boundary and initial moduli of Appendix B use barriers only; Lemma 4.3 integrates
  by parts before differentiating in time; and in Proposition 6.1 the subsolution property of the
  limit comes from Lemma 2.12.
- **Examples.** The necklace example (Figure 1) is formalized with different parameters
  (100 holes inside the disc of radius 4, instead of 18 unit discs in the plane).

## Results from the literature

`PerronVariational/Registry/` states the results the paper cites from the literature, each with
its citation. In this release every one of them is proved, either in this library or by a
dependency (see [Building](#building)). The registry theorems are thin wrappers around those
proofs.

## Verification

- **No `sorry`.** The library contains no `sorry`, `admit`, `native_decide` or `axiom`
  declaration. CI scans the sources, with comments and strings masked.
- **Axioms.** Each declaration listed in `formalization.yaml` depends on exactly `propext`,
  `Classical.choice` and `Quot.sound`. CI checks this with `#print axioms`
  (`scripts/check-formalization-manifest.rb`).
- **CI.** `.github/workflows/ci.yml` runs on every push and pull request. It:
  - fetches the Mathlib cache and builds the library, treating warnings as errors;
  - scans the library sources (comments and strings masked) for `sorry`, `admit`, `axiom` and
    `native_decide`, and checks that every library file is a Lean module
    (`scripts/check_integrity.py`);
  - checks that no library file reaches 1000 lines;
  - validates `formalization.yaml`: every Lean name resolves, each target depends on exactly the
    three axioms above, and the challenge inventory matches `challenges/*/config.json`
    (`scripts/check-formalization-manifest.rb`);
  - elaborates every challenge workspace and checks the axioms of every solution theorem
    (`scripts/check-challenges.sh`);
  - checks that every `.lean` file in the repository is a module, that each `Challenge.lean`
    repeats its workspace's vocabulary verbatim and imports Mathlib only, and the size of each
    `Challenge.lean` (`scripts/challenge-prep.py check`).

## Comparator challenges

`challenges/` holds one standalone [Comparator](https://github.com/leanprover/comparator)
workspace, `main-results`. It restates the main results of the paper over Mathlib only, with its own
vocabulary in `Vocabulary.lean`: Theorem 1.1, Corollary 1.2, and the necklace example (Figure 1 of
the paper, with different parameters), which also shows that the hypotheses of the other claims can
be met. `formalization.yaml` lists them. See [`challenges/README.md`](challenges/README.md) for the challenge set and the acceptance
procedure.

- Ordinary CI only elaborates these files.
- The release workflow `.github/workflows/release-comparator.yml` (`scripts/release-comparator.sh`)
  establishes exact statement equality and the permitted-axiom check. It runs Comparator with
  pinned tool revisions and uploads an attestation.

The result of the release run is recorded in [`challenges/README.md`](challenges/README.md).

## Building

The toolchain and dependencies are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`:

- Lean `v4.35.0-rc3`;
- Mathlib `v4.35.0-rc3` (commit `c55e6e7`),
  [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4);
- viscosity-solution-theory `v0.4.0` (Lake package `viscosity_solns`),
  [willmfeldman/viscosity-solution-theory](https://github.com/willmfeldman/viscosity-solution-theory):
  viscosity solutions, Perron's method and Weyl's lemma. It pulls in
  aleksandrov-differentiability `v0.4.0`,
  [willmfeldman/aleksandrov-differentiability](https://github.com/willmfeldman/aleksandrov-differentiability);
- parabolic-basic-theory `v0.3.0` (Lake package `parabolic_basic_theory`),
  [willmfeldman/parabolic-basic-theory](https://github.com/willmfeldman/parabolic-basic-theory):
  semilinear parabolic well-posedness and comparison;
- bernoulli-parabolic-comparison `v0.3.0` (Lake package `bernoulli_parabolic_comparison`),
  [willmfeldman/bernoulli-parabolic-comparison](https://github.com/willmfeldman/bernoulli-parabolic-comparison):
  strict comparison for the parabolic one-phase problem;
- elliptic-bernoulli-foundations `v0.4.0` (Lake package `elliptic_bernoulli_foundations`),
  [willmfeldman/elliptic-bernoulli-foundations](https://github.com/willmfeldman/elliptic-bernoulli-foundations):
  obstacle problems, energy perturbations, the Lipschitz estimate, non-degeneracy, flatness
  regularity and the planar classification. It pulls in elliptic-schauder-theory `v0.1.0`,
  [willmfeldman/elliptic-schauder-theory](https://github.com/willmfeldman/elliptic-schauder-theory);
- gmt-foundations `v0.3.0` (Lake package `gmt_foundations`),
  [willmfeldman/gmt-foundations](https://github.com/willmfeldman/gmt-foundations): Sobolev and BV
  compactness, De Giorgi iteration;
- bernoulli-rectifiability `v0.4.2` (Lake package `inner_variational`),
  [willmfeldman/bernoulli-rectifiability](https://github.com/willmfeldman/bernoulli-rectifiability):
  the Kriventsov–Weiss theory for a Lipschitz coefficient.

The other packages in `lake-manifest.json` are Mathlib's own dependencies (batteries, aesop, Qq,
ProofWidgets, plausible, LeanSearchClient, import-graph, lean4-cli). All dependencies are
Apache-2.0.

```bash
lake exe cache get
lake build
```

`lake build` builds the root module `PerronVariational`, which imports every module of the
library.

## Layout

| Path | Contents |
|---|---|
| `PerronVariational/Basic/`, `Defs/` | Vocabulary: the setting, Sobolev and BV notions, viscosity, variational and parabolic notions, Perron's extremal solutions |
| `PerronVariational/Statements/` | Statements of the main and intermediate results |
| `PerronVariational/Semilinear/` | The semilinear approximation (Proposition 3.12, Appendix B) and its viscosity limits (Section 5) |
| `PerronVariational/Parabolic/` | The parabolic problem: existence (Theorem 3.13) and long-time limits |
| `PerronVariational/Inner/` | Inner variational solutions: the singular limit (Proposition 4.1), long-time limits (Theorem 3.14), compactness |
| `PerronVariational/Stationary/` | Stationary solutions: inner variational ⇒ viscosity sub/supersolution, two-plane solutions, directional minimizers |
| `PerronVariational/Main/` | Propositions 6.1 and 6.2, Proposition 6.3, Theorem 1.1 and Corollary 1.2 |
| `PerronVariational/Appendix/` | Non-degeneracy (Theorems 2.9 and 2.10, Appendix A) |
| `PerronVariational/Examples/` | Two planar examples. `TwoDisc` (`model_example`), not in the paper: a domain and data with distinct smallest and largest solutions, the smallest one having a two-plane point. `Necklace` (`necklace_example`), the configuration of Figure 1 with different parameters (100 holes instead of 18, inside a disc of radius 4): the smallest supersolution, the largest subsolution and every energy minimizer with the same boundary data are pairwise distinct, and the smallest one has two-plane points |
| `PerronVariational/Analysis/`, `Regularity/`, `Topology/` | Toolkits |
| `PerronVariational/Foundations/` | Interfaces to the dependencies |
| `PerronVariational/Registry/` | Results cited from the literature, each proved here or by a dependency |
| `challenges/`, `formalization.yaml` | Comparator workspaces and the theorem manifest |
| `DEVIATIONS.md` | Differences between the formalization and the paper |
| `scripts/` | Integrity, manifest, challenge and release-comparator checks used by CI and the release workflow |

## References

- F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
- H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
- L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Oxford Math. Monogr., Oxford University Press, 2000.
- H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011.
- L. A. Caffarelli, *A Harnack inequality approach to the regularity of free boundaries. III.
  Existence theory, compactness, and dependence on X*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 15
  (1988), no. 4, 583–602.
- L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
- L. A. Caffarelli, J. L. Vázquez, *A free-boundary problem for the heat equation arising in flame
  propagation*, Trans. Amer. Math. Soc. 347 (1995), no. 2, 411–441.
- M. G. Crandall, H. Ishii, P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. (N.S.) 27 (1992), no. 1, 1–67.
- D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
- L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  CRC Press, 2015.
- W. M. Feldman, I. C. Kim, N. Požár, *An obstacle approach to rate-independent droplet
  evolution*, Forum Math. Sigma 14 (2026), Paper No. e38.
- W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
- M. Giaquinta, E. Giusti, *Quasi-minima*, Ann. Inst. H. Poincaré Anal. Non Linéaire 1 (1984),
  no. 2, 79–107.
- D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001.
- E. Giusti, *Direct Methods in the Calculus of Variations*, World Scientific, 2003.
- D. Jerison, N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math. Res.
  Not. IMRN 2016, no. 19, 5922–5987; arXiv:1412.4106.
- I. C. Kim, *A free boundary problem arising in flame propagation*, J. Differential Equations 191
  (2003), no. 2, 470–489.
- D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131. Result numbers are those of arXiv:2306.10131v2.
- O. A. Ladyzhenskaya, V. A. Solonnikov, N. N. Ural'ceva, *Linear and Quasilinear Equations of
  Parabolic Type*, Transl. Math. Monogr. 23, Amer. Math. Soc., 1968.
- G. M. Lieberman, *Second Order Parabolic Differential Equations*, World Scientific, 1996.
- B. Orcan-Ekmekci, *On the geometry and regularity of largest subsolutions for a free boundary
  problem in ℝ²: elliptic case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3–4,
  937–962.
- G. S. Weiss, *Partial regularity for weak solutions of an elliptic free boundary problem*, Comm.
  Partial Differential Equations 23 (1998), no. 3–4, 439–455.
- G. S. Weiss, *A singular limit arising in combustion theory: fine properties of the free
  boundary*, Calc. Var. Partial Differential Equations 17 (2003), no. 3, 311–340.

Each Lean file's module docstring gives the full reference for the results it uses.

## Credits

The library contains no code copied or adapted from other projects. Its Lake dependencies are
listed under [Building](#building) and in [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).

The Lean proofs were written by AI coding agents (Claude, by Anthropic) under the author's
mathematical direction and review. The theorem statements and proof routes were reviewed by the
author. Correctness rests on Lean's kernel check, together with the comparator challenges in
`challenges/`.

## Citation

If you use this formalization, please cite it using the metadata in [`CITATION.cff`](CITATION.cff),
and cite the paper above.

## License

Apache License 2.0 ([LICENSE](LICENSE)). Adapted third-party code is listed in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
