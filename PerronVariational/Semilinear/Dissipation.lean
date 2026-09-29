/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.Sobolev
public import PerronVariational.Defs.Semilinear
import PerronVariational.Registry.SemilinearDissipation
import PerronVariational.Semilinear.Calculus
import PerronVariational.Semilinear.WellPosedData

/-!
# Energy dissipation for the semilinear problem (Proposition 3.8(iii))

The energy dissipation identity (A.1) of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981
(Appendix A.2), which is (3.8) of Proposition 3.8(iii).

The paper's argument is one line ("multiplying the equation by `∂ₜu_ε` and integrating on
`U × [0, T]`"). Justifying it needs regularity of `u_ε` up to `t = 0` and up to `∂U` that the
classical `C^{2,1}(U_∞)` solution does not carry by definition (`∂ₜu_ε = 0` on the lateral boundary,
`u_ε ∈ C([0, T]; H¹(U))`, the integration by parts `∫_U ∂ₜu Δu = -½ d/dt ∫_U |∇u|²`), i.e. the
variational theory of O. A. Ladyzhenskaya, V. A. Solonnikov, N. N. Ural'ceva, *Linear and
Quasilinear Equations of Parabolic Type*, AMS Transl. Math. Monogr. 23, 1968, Ch. III and V, or
L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, doi:10.1090/gsm/019, §7.1.
The general statement, for `H¹` data, is `Registry.semilinear_energy_dissipation`, proved in
`Semilinear/EnergyDissipation.lean` by truncation and Steklov averages. Here it is specialized to
Lipschitz data, whose pointwise gradient is the weak gradient (from gmt-foundations v0.1.0).
-/

open Set Filter Topology MeasureTheory
open scoped Gradient ENNReal

@[expose] public section

namespace PerronVariational

variable {d : ℕ}

/-- **Energy dissipation inequality** (A.1), i.e. (3.8) of Proposition 3.8(iii): for a solution
`u` of (3.4) with Lipschitz data `g` on `Ū` and every `T > 0`,
`½ J(u(T), χ_ε(T); U) + ∫₀ᵀ ∫_U (∂ₜu)² ≤ ½ J(g, χ_ε(0); U)`, with `χ_ε = 2 𝓑_ε(u)`.
The paper states (A.1) as an equality; here we prove only the inequality `≤`, because only `≤` is
used later, and the truncation argument gives it without regularity of `u` up to `∂U` or `t = 0`.

From `Registry.semilinear_energy_dissipation` (see the module docstring). -/
theorem IsSemilinearSolution.dissipation (S : Setting d) {β : ℝ → ℝ} (hβ : IsReactionProfile β)
    {ε : ℝ} (hε : 0 < ε) {g : E d → ℝ} (hg : ∃ K, LipschitzOnWith K g (closure S.U))
    {u : E d × ℝ → ℝ} (hu : IsSemilinearSolution S.U S.Q β ε g u) {T : ℝ} (hT : 0 < T) :
    energyJχ S.U S.Q (fun x ↦ gradₓ u (x, T)) (fun x ↦ chiEps β ε u (x, T)) / 2 +
        ∫⁻ p in S.U ×ˢ Ioc 0 T, ENNReal.ofReal (dₜ u p ^ 2) ≤
      energyJχ S.U S.Q (∇ g) (fun x ↦ chiEps β ε u (x, 0)) / 2 := by
  obtain ⟨K, hK⟩ := hg
  have hbd : ∀ x ∈ S.U, ‖∇ g x‖ ≤ K := fun x hx ↦ by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitzOn ℝ (S.isOpen.mem_nhds hx)
      (hK.mono subset_closure)
  exact Registry.semilinear_energy_dissipation S hβ hε
    (memH1_gradient_of_lipschitzOnWith hK hbd) hu hT

end PerronVariational

end
