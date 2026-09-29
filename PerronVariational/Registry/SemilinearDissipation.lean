/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.EnergyDissipation

/-!
# Registry: the semilinear energy dissipation inequality

The energy dissipation inequality (A.1), i.e. (3.8) of Prop 3.8(iii), for the semilinear equation
`∂ₜu = Δu - Q(x)² β_ε(u)` (first line of (3.4) in F. Abedin, W. M. Feldman, K. Stinson,
*Variational properties of Perron's extremal solutions in the Bernoulli one-phase problem*,
arXiv:2609.14981, "the paper").

References: L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in
Mathematics 19, AMS, 2010, doi:10.1090/gsm/019; O. A. Ladyženskaja, V. A. Solonnikov and
N. N. Ural'ceva, *Linear and quasilinear equations of parabolic type*, Translations of
Mathematical Monographs 23, AMS, 1968 ("LSU").

* `Registry.semilinear_energy_dissipation`: the energy dissipation inequality (A.1)/(3.8) for `H¹`
  data (Evans §7.1, LSU Ch. III). Proved here (`Semilinear/EnergyDissipation.lean`).

This entry is kept apart from `PerronVariational.Registry.Semilinear` so that modules that only
need the viscosity notions and well-posedness do not wait for the energy-dissipation proof.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

namespace Registry

/-! ### Energy dissipation inequality -/

/-- **Energy dissipation inequality.** Under the standing assumptions, let `ε > 0`, let the
time-independent data `g ∈ H¹(U)` have weak gradient `G` (carried as explicit data), and let `u`
solve (3.4) in the sense of `IsSemilinearSolution` (so `g = u(·, 0)` is continuous on `Ū`). Then for
every `T > 0`, `½ J(u(T), χ_ε(T); U) + ∫₀ᵀ ∫_U (∂ₜu)² ≤ ½ J(g, χ_ε(0); U)`, where `χ_ε = 2 𝓑_ε(u)`
and `J` is computed with the classical gradient of `u(·, T)` and with `G` for the data.

This is the energy dissipation (A.1), i.e. (3.8) of Prop 3.8(iii). The paper states it as an
equality; here we prove the inequality `≤`, because only the inequality is used. It also covers
arbitrary `H¹` data, which the proof of Prop 4.1 uses: the paper asserts the estimates there "for
any solution", but proves them only for well-prepared data.

A result from the literature: Evans, §7.1.3, Theorem 5; LSU Chapter III §§2–4.
Proved here: `PerronVariational.semilinear_energy_dissipation`
(`Semilinear/EnergyDissipation.lean`), by truncating `u − g` and the Steklov quotient `D_h u` in the
values (both vanish on `∂U`), so every integration by parts is interior. -/
theorem semilinear_energy_dissipation (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {ε : ℝ} (hε : 0 < ε) {g : E d → ℝ} {G : E d → E d} (hg : MemH1 S.U g G)
    {u : E d × ℝ → ℝ} (hu : IsSemilinearSolution S.U S.Q β ε g u) {T : ℝ} (hT : 0 < T) :
    energyJχ S.U S.Q (fun x ↦ gradₓ u (x, T)) (fun x ↦ chiEps β ε u (x, T)) / 2 +
        ∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ u p ^ 2) ≤
      energyJχ S.U S.Q G (fun x ↦ chiEps β ε u (x, 0)) / 2 :=
  _root_.PerronVariational.semilinear_energy_dissipation S hβ hε hg hu hT

end Registry

end PerronVariational

end
