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

The library has about 51,200 lines of Lean in 151 files. It is
sorry-free, and the headline theorems depend only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Headline theorems

Result numbers are those of arXiv:2609.14981. Each statement is a `…Statement : Prop` in
`PerronVariational/Statements/`, proved by the theorem listed. `formalization.yaml` states the
certified results in words.

| Result | Paper | Lean theorem |
|---|---|---|
| The smallest supersolution above a strict subsolution is a viscosity solution, an inner variational solution, and a local downward minimizer of `J_Q` near each free boundary point | Theorem 1.1 | `main_smallest` |
| The largest subsolution below a strict supersolution is a viscosity solution, an inner variational solution, and a local upward minimizer of `J_Q` near each free boundary point | Theorem 1.1 | `main_largest` |
| In `ℝ²`, the free boundary of the smallest supersolution splits into a relatively open regular part, where the solution is classical, and a part where every blow-up is `Q(x₀)|y · e|` | Corollary 1.2(i) | `corollary_2d_smallest` |
| In `ℝ²`, the largest subsolution is classical near every free boundary point | Corollary 1.2(ii) | `corollary_2d_largest` |

The paper explains the ideas of the proof. `formalization.yaml` lists the main intermediate results
(Theorem 3.9, Propositions 3.8 and 4.1, Theorem 3.10, Lemma 6.3, Theorem B.1) with their Lean names.

## Deviations from the paper

Each docstring states where its statement deviates from the paper. The main deviations are:

- **Domain.** "`U` has C² boundary" is encoded as `U = {ρ < 0}` for some `ρ ∈ C²(ℝᵈ)` with
  `∇ρ ≠ 0` on `∂U`.
- **Test functions and data.** Test functions are smooth on all of `ℝᵈ` (or `ℝᵈ × ℝ`), not only on
  `U`. This is equivalent, because every condition is local. Strict sub- and supersolutions are
  `C²(ℝᵈ)`, not `C²(Ū)`; a `C²(Ū)` function on a C² domain extends.
- **Sobolev spaces and energies.** An `H¹` function carries its weak gradient as explicit data.
  The energies are `ℝ≥0∞`-valued lower integrals, so no integrability side conditions are needed.
  "`u − v ∈ H¹₀(B)`" for a ball `B` is encoded as "`u = v` a.e. off `B`".
- **One-sided minimizers.** The paper's Definition 2.11 compares energies on `U` for `H¹(U)`
  competitors. Here the competitors are `H¹_loc(U)` and the energies are compared on the ball.
  The two agree when `J_Q(u; U) < ∞`. The paper's literal version cannot apply on `U = ℝᵈ`,
  where two-plane functions are not in `H¹`, and the paper uses it there.
- **Parabolic regularity.** "`∇u ∈ L^∞_loc`" is encoded as local uniform Lipschitz bounds in
  space, and `∂ₜu` is carried as data. Semilinear solutions are `C^{2,1}` rather than `C^∞`
  (`C^∞` would need a smooth `Q`).
- **Weighted perimeter.** `∫ η |∇χ|` is defined by duality, as the supremum of `∫ χ div ψ` over
  `ψ ∈ C¹_c` with `|ψ| ≤ η`.
- **Corrected statements.** In a few places the paper's statement or argument needs a
  correction; each is explained at the corresponding declaration.
  - Proposition 5.3 is false for the paper's set `E`. It is proved for `E = closure(U × (0, T])`,
    and Corollary 5.4 is stated inside `U × [0, T]`.
  - Theorem 3.10 also assumes boundedness, monotonicity in time, and the weak heat equation (4.5)
    in `{u > 0}`; without the last, `1 + |x₁|` is a counterexample. Convergence is along a
    sequence of good times.
  - Lemma 2.10 needs a local `L^∞` bound on the sequence (`u_k ≡ k` is a counterexample
    without it).
  - Lemma 2.7: the intermediate claim `u > g` does not follow; the proof needs only `g < 0` at
    free boundary points. The largest-subsolution case, not proved in the paper, is proved here
    with a strict barrier.
  - Lemma 6.3 carries additional hypotheses, and the continuity of the obstacle minimizer is proved
    by a De Giorgi argument.
  - Propositions 6.1 and 6.2: the continuity of the Perron solutions on `Ū` comes from the uniform
    modulus of Proposition A.8.
  - Corollary 1.2(ii): two-sided flatness at a half-plane blow-up uses the non-degeneracy of
    Theorem B.1 and the convergence of the phases `χ` along the blow-up sequence.

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
    `native_decide` (`scripts/check_integrity.py`);
  - checks that no library file reaches 1000 lines;
  - validates `formalization.yaml`: every Lean name resolves, each target depends on exactly the
    three axioms above, and the challenge inventory matches `challenges/*/config.json`
    (`scripts/check-formalization-manifest.rb`);
  - elaborates every challenge workspace and checks the axioms of every solution theorem
    (`scripts/check-challenges.sh`).

## Comparator challenges

`challenges/` holds standalone [Comparator](https://github.com/leanprover/comparator) workspaces.
They restate the headline statements over Mathlib only, and `formalization.yaml` lists them. See
[`challenges/README.md`](challenges/README.md) for the challenge set and the acceptance procedure.

- Ordinary CI only elaborates these files.
- The release workflow `.github/workflows/release-comparator.yml` (`scripts/release-comparator.sh`)
  establishes exact statement equality and the permitted-axiom check. It runs Comparator with
  pinned tool revisions and uploads an attestation.

TODO: the Comparator release result.

## Building

The toolchain and dependencies are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`:

- Lean `v4.30.0`;
- Mathlib `v4.30.0` (commit `c5ea003`),
  [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4);
- viscosity-solution-theory `v0.2.0` (Lake package `viscosity_solns`),
  [willmfeldman/viscosity-solution-theory](https://github.com/willmfeldman/viscosity-solution-theory):
  viscosity solutions, Perron's method and Weyl's lemma. It pulls in
  aleksandrov-differentiability (commit `730e7e9`),
  [willmfeldman/aleksandrov-differentiability](https://github.com/willmfeldman/aleksandrov-differentiability);
- parabolic-basic-theory `v0.1.0` (Lake package `parabolic_basic_theory`),
  [willmfeldman/parabolic-basic-theory](https://github.com/willmfeldman/parabolic-basic-theory):
  semilinear parabolic well-posedness and comparison;
- bernoulli-parabolic-comparison `v0.1.0` (Lake package `bernoulli_parabolic_comparison`),
  [willmfeldman/bernoulli-parabolic-comparison](https://github.com/willmfeldman/bernoulli-parabolic-comparison):
  strict comparison for the parabolic one-phase problem;
- elliptic-bernoulli-foundations `v0.1.0` (Lake package `elliptic_bernoulli_foundations`),
  [willmfeldman/elliptic-bernoulli-foundations](https://github.com/willmfeldman/elliptic-bernoulli-foundations):
  obstacle problems, energy perturbations, the Lipschitz estimate, non-degeneracy, flatness
  regularity and the planar classification;
- gmt-foundations `v0.1.0` (Lake package `gmt_foundations`),
  [willmfeldman/gmt-foundations](https://github.com/willmfeldman/gmt-foundations): Sobolev and BV
  compactness, De Giorgi iteration;
- bernoulli-rectifiability `v0.2.0` (Lake package `inner_variational`),
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
| `PerronVariational/Semilinear/` | The semilinear approximation (Proposition 3.8) and its viscosity limits (Section 5) |
| `PerronVariational/Parabolic/` | The parabolic problem: existence (Theorem 3.9) and long-time limits |
| `PerronVariational/Inner/` | Inner variational solutions: the singular limit (Proposition 4.1), long-time limits (Theorem 3.10), compactness |
| `PerronVariational/Stationary/` | Stationary solutions: inner variational ⇒ viscosity sub/supersolution, two-plane solutions, directional minimizers |
| `PerronVariational/Main/` | Propositions 6.1 and 6.2, Lemma 6.3, Theorem 1.1 and Corollary 1.2 |
| `PerronVariational/Appendix/` | Appendix B: non-degeneracy |
| `PerronVariational/Examples/` | A model example, not in the paper: a planar domain and data with distinct smallest and largest solutions, the smallest one having a two-plane point |
| `PerronVariational/Analysis/`, `Regularity/`, `Topology/` | Toolkits |
| `PerronVariational/Foundations/` | Interfaces to the dependencies |
| `PerronVariational/Registry/` | Results cited from the literature, each proved here or by a dependency |
| `challenges/`, `formalization.yaml` | Comparator workspaces and the theorem manifest |
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

Some files contain code adapted from other Apache-2.0 Lean projects. Each such file keeps the
upstream copyright line and has a `## Provenance` section, and
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) lists them.

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
