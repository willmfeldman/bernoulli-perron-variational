# Comparator challenges

This directory contains three standalone [Comparator](https://github.com/leanprover/comparator)
workspaces for `PerronVariational`, the formalization of

> F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
> the Bernoulli one-phase problem*, [arXiv:2609.14981](https://arxiv.org/abs/2609.14981).

Comparator checks that a solution proves exactly the statement of a trusted challenge, that it
passes the kernel, and that it uses only the permitted axioms `propext`, `Quot.sound` and
`Classical.choice`.

## Workspaces

| Workspace | Kind | Paper | Challenge theorems | Proved from |
|---|---|---|---|---|
| `main-theorem` | headline theorem | Theorem 1.1 | `challenge_main_smallest`, `challenge_main_largest` | `PerronVariational.main_smallest`, `PerronVariational.main_largest` |
| `planar-structure` | headline theorem | Corollary 1.2 | `challenge_corollary_2d_smallest`, `challenge_corollary_2d_largest` | `PerronVariational.corollary_2d_smallest`, `PerronVariational.corollary_2d_largest` |
| `model-cases` | model example | none (not in the paper) | `challenge_model_example` | `PerronVariational.TwoDisc.model_example` |

- `main-theorem`: for the smallest supersolution above a smooth strict subsolution `g` with
  `g > 0` on `∂U`, and for the largest subsolution below a smooth strict supersolution `g`: the
  solution is a viscosity solution, an inner variational solution, and a downward (resp. upward)
  minimizer of the Alt–Caffarelli energy on a ball around each free boundary point.
- `planar-structure`: in `ℝ²`, the free boundary of the smallest supersolution splits into a
  relatively open part near which the solution is classical and a part where every blow-up limit
  is a two-plane function `Q(x₀)|y · e|`; the largest subsolution is classical near every free
  boundary point.
- `model-cases`: a model example, not a result of the paper. In `ℝ²` with `Q ≡ 1`, a domain and
  data `g_sub`, `g_super` meeting the hypotheses of Theorem 1.1, with `g_sub = g_super` on `∂U`,
  whose smallest supersolution `u_min` and largest subsolution `u_max` are both nontrivial (each is
  positive somewhere, vanishes somewhere and has a nonempty free boundary) and differ; `0` is a
  two-plane point of `u_min` (its blow-ups converge to `|y₁|`). The domain is the unit disc minus
  two small discs whose radial solutions have free boundaries touching at `0`. It is not counted as
  coverage of the paper.

The hypotheses of the paper's standing setting (`d ≥ 2`; `U` open, bounded and connected with `C²`
boundary; `Q` Lipschitz on `Ū` with `0 < Q_min ≤ Q ≤ Q_max` on `Ū`) are stated as separate,
readable hypotheses in each claim, not as a bundled structure.

## Files

Each workspace has these files:

- `Statement.lean`: the trusted claims, importing Mathlib only. The same file, byte for byte, is
  used by all three workspaces. Every notion the claims use is defined in it from Mathlib, so a
  reader can check the meaning of each claim without reading the library. These notions are
  viscosity solutions, strict sub- and supersolutions, Perron's extremal solutions, inner
  variational solutions, one-sided minimizers of the Alt–Caffarelli energy, blow-ups and classical
  solutions. The docstrings list each difference from the printed paper and why it is harmless.
- `Challenge.lean`: the trusted wrapper, importing `Statement` only and stating each claim with
  `sorry`.
- `Solution.lean`: the untrusted proof. It imports `Statement` and the library, and proves the
  same theorems.
- `config.json`: the theorem names and the permitted axioms.
- `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`: a Lake workspace whose default
  targets are the trusted modules `Statement` and `Challenge` only. It shares the root workspace's
  dependency checkouts (`packagesDir = "../../.lake/packages"`), and its manifest locks the same
  revisions as the root manifest.

The trusted files are `Statement.lean`, `Challenge.lean`, `config.json` and the workspace
`lakefile.toml`. `Solution.lean` is untrusted.

## What ordinary CI establishes

`scripts/check-challenges.sh`, run by CI on every push, builds `Statement`, `Challenge` and
`Solution` in every workspace. It then runs `#print axioms` on every theorem in each `config.json`
and requires exactly the permitted axioms. This catches elaboration, missing-proof and axiom
regressions. It does not check that the challenge and the solution state the same theorems: only
the release Comparator workflow establishes exact statement equality.

For local development, `scripts/build-challenges.sh --trusted-all` builds the same targets, and
`scripts/build-challenges.sh --challenge-only` builds only the trusted modules.

## Release verification

The release workflow `.github/workflows/release-comparator.yml` (`scripts/release-comparator.sh`,
with pinned tool revisions) does the following:
1. validates the challenge inventory against `formalization.yaml`;
2. builds the library and each workspace's trusted modules (`Statement`, `Challenge`) outside the
   sandbox, on a standard GitHub-hosted Linux runner;
3. runs Comparator in its sandbox on each workspace;
4. uploads an attestation, which records the tool revisions, the per-workspace results and the
   sandbox caveats.

It never builds `Solution` before Comparator processes it.

TODO: the Comparator result (date, tool revisions and per-workspace result), after the release
run.
