/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Semilinear.DirDeriv
public import PerronVariational.Defs.Semilinear
import Mathlib.Data.Real.StarOrdered
import PerronVariational.Semilinear.BernsteinPoint

/-!
# The Bernstein computation at a maximum point (Steps 1 and 3)

Steps 1 and 3 of the joint proof of Propositions A.5 and A.6 of
F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
in the Bernoulli one-phase problem*, arXiv:2609.14981 (Appendix A.4):
Step 1 is the equation for `v`, where `u = Φ(v)`, and the equation (A.8) for `w = |∇v|²`;
Step 3 is the derivative tests at a maximum of `z = η² w`.

Here `Φ : ℝ → ℝ` is any smooth function with `Φ' > 0` and a smooth inverse `Ψ`; `u` is a smooth
solution of `∂ₜu = Δu - Q² β_ε(u)` on an open set `O`, and `v = Ψ ∘ u`. With
`ℓ = Φ''/Φ'` and `B = β_ε(Φ)/Φ'` the function `v` solves
`∂ₜv = Δv + ℓ(v)|∇v|² - Q² B(v)` (`veq`), and `w = |∇v|²` satisfies
`∂ₜw - Δw - 2ℓ(v)∇v·∇w ≤ 2ℓ'(v) w² - 2 ∇v·∇ₓk - 2 ∂ᵥk w`, `k = Q² B(v)` (`weq_le`).
-/

open Set Filter Topology Finset
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace PerronVariational

namespace BernsteinMax

variable {d : ℕ} {β : ℝ → ℝ} {ε : ℝ} {Q : E d → ℝ} {Φ Ψ : ℝ → ℝ} {O : Set (E d × ℝ)}
  {u : E d × ℝ → ℝ}

/-- `ℓ = Φ''/Φ'`. -/
noncomputable def ellOf (Φ : ℝ → ℝ) (s : ℝ) : ℝ := deriv (deriv Φ) s / deriv Φ s

/-- `B = β_ε(Φ)/Φ'`. -/
noncomputable def bOf (β : ℝ → ℝ) (ε : ℝ) (Φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  betaEps β ε (Φ s) / deriv Φ s

theorem contDiff_betaEps (hβ : ContDiff ℝ ∞ β) (ε : ℝ) : ContDiff ℝ ∞ (betaEps β ε) := by
  unfold betaEps
  exact (hβ.comp (contDiff_id.div_const ε)).div_const ε

theorem contDiff_deriv' {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.1 hf).2

theorem contDiff_ellOf (hΦ : ContDiff ℝ ∞ Φ) (hΦ' : ∀ s, 0 < deriv Φ s) :
    ContDiff ℝ ∞ (ellOf Φ) :=
  (contDiff_deriv' (contDiff_deriv' hΦ)).div (contDiff_deriv' hΦ) fun s ↦ (hΦ' s).ne'

theorem contDiff_bOf (hβ : ContDiff ℝ ∞ β) (hΦ : ContDiff ℝ ∞ Φ) (hΦ' : ∀ s, 0 < deriv Φ s) :
    ContDiff ℝ ∞ (bOf β ε Φ) :=
  ((contDiff_betaEps hβ ε).comp hΦ).div (contDiff_deriv' hΦ) fun s ↦ (hΦ' s).ne'

/-- `W = ∑ᵢ (∂ᵢ v)²`. -/
noncomputable def wOf (v : E d × ℝ → ℝ) (q : E d × ℝ) : ℝ :=
  ∑ i : Idx d, dd (spaceDir i) v q ^ 2

variable (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O) (hQ : ContDiff ℝ ∞ Q)
  (hβ : ContDiff ℝ ∞ β) (hΦ : ContDiff ℝ ∞ Φ) (hΦ' : ∀ s, 0 < deriv Φ s)
  (hΨ : ContDiff ℝ ∞ Ψ) (hΦΨ : ∀ s, Φ (Ψ s) = s)
  (heq : ∀ q ∈ O, dₜ u q = lapₓ u q - Q q.1 ^ 2 * betaEps β ε (u q))

include hu hΨ in
theorem contDiffOn_v : ContDiffOn ℝ ∞ (fun q ↦ Ψ (u q)) O := hΨ.comp_contDiffOn hu

include hO hu hΨ in
theorem contDiffOn_dd_v (a : E d × ℝ) : ContDiffOn ℝ ∞ (dd a (fun q ↦ Ψ (u q))) O :=
  (contDiffOn_v hu hΨ).dd hO a

include hO hu hΨ in
theorem contDiffOn_wOf : ContDiffOn ℝ ∞ (wOf (fun q ↦ Ψ (u q))) O := by
  unfold wOf
  exact ContDiffOn.sum fun i _ ↦ (contDiffOn_dd_v hO hu hΨ _).pow 2

include hO hu hΦ hΦ' hΨ hΦΨ heq in
/-- **The equation for `v = Ψ(u)`** (Step 1): `∂ₜv = Δv + ℓ(v)|∇v|² - Q² B(v)` on `O`. -/
theorem veq : ∀ q ∈ O, dd timeDir (fun q ↦ Ψ (u q)) q =
    ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) (fun q ↦ Ψ (u q))) q +
      ellOf Φ (Ψ (u q)) * wOf (fun q ↦ Ψ (u q)) q - Q q.1 ^ 2 * bOf β ε Φ (Ψ (u q)) := by
  intro q hq
  set v : E d × ℝ → ℝ := fun q ↦ Ψ (u q) with hv
  have hvs : ContDiffOn ℝ ∞ v O := contDiffOn_v hu hΨ
  have huv : u = fun q ↦ Φ (v q) := funext fun q ↦ (hΦΨ (u q)).symm
  have hΦd : ∀ s, DifferentiableAt ℝ Φ s := fun s ↦ hΦ.differentiable (by simp) s
  have hΦ'c : ContDiff ℝ ∞ (deriv Φ) := contDiff_deriv' hΦ
  -- first derivatives of `u`
  have hdu : ∀ a, EqOn (dd a u) (fun q ↦ deriv Φ (v q) * dd a v q) O := fun a ↦ by
    rw [huv]; exact dd_comp_eqOn hO hΦ hvs a
  -- second spatial derivatives of `u`
  have hddu : ∀ i : Idx d, dd (spaceDir i) (dd (spaceDir i) u) q =
      deriv Φ (v q) * dd (spaceDir i) (dd (spaceDir i) v) q +
        deriv (deriv Φ) (v q) * dd (spaceDir i) v q ^ 2 := fun i ↦ by
    rw [dd_congr (hdu _) hO hq]
    have h1 : DifferentiableAt ℝ (fun q ↦ deriv Φ (v q)) q :=
      (hΦ'c.differentiable (by simp) _).comp q (hvs.differentiableAt' hO hq)
    rw [dd_mul h1 ((hvs.dd hO _).differentiableAt' hO hq),
      dd_comp (hΦ'c.differentiable (by simp) _) (hvs.differentiableAt' hO hq)]
    ring
  have hu2 : ContDiffAt ℝ 2 u q := hu.contDiffAt_two hO hq
  have hlap : lapₓ u q = deriv Φ (v q) * ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) v) q +
      deriv (deriv Φ) (v q) * wOf v q := by
    rw [lapₓ_eq_sum_dd hu2, wOf, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ hddu i
  have hdt : dₜ u q = deriv Φ (v q) * dd timeDir v q := by
    rw [dₜ_eq_dd (hu2.differentiableAt (by norm_num))]; exact hdu _ hq
  have h := heq q hq
  rw [hlap, hdt, show u q = Φ (v q) from (hΦΨ (u q)).symm] at h
  have hpos := hΦ' (v q)
  change dd timeDir v q = ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) v) q +
      ellOf Φ (v q) * wOf v q - Q q.1 ^ 2 * bOf β ε Φ (v q)
  simp only [ellOf, bOf]
  field_simp
  linarith

/-! ### The equation for `w = |∇v|²` -/

section Weq

variable {v : E d × ℝ → ℝ} {ℓ B : ℝ → ℝ}

omit hu hβ hΦ hΦ' hΨ hΦΨ heq in
include hO in
/-- `D_a w = ∑ⱼ 2 ∂ⱼv D_a ∂ⱼv` on `O`. -/
theorem dd_wOf_eqOn (hv : ContDiffOn ℝ ∞ v O) (a : E d × ℝ) :
    EqOn (dd a (wOf v)) (fun q ↦ ∑ j : Idx d, 2 * dd (spaceDir j) v q *
      dd a (dd (spaceDir j) v) q) O := by
  intro q hq
  have h1 := dd_sum_eqOn hO (s := univ) (F := fun j q ↦ dd (spaceDir j) v q ^ 2)
    (fun j _ ↦ (hv.dd hO _).pow 2) a hq
  change dd a (fun q ↦ ∑ i : Idx d, dd (spaceDir i) v q ^ 2) q = _
  rw [h1]
  exact sum_congr rfl fun j _ ↦ dd_sq ((hv.dd hO _).differentiableAt' hO hq) a

omit hu hβ hΦ hΦ' hΨ hΦΨ heq in
include hO in
/-- **The equation (A.8) for `w = |∇v|²`**, with the Hessian term dropped: if `v` is smooth
on `O` and `∂ₜv = Δv + ℓ(v)|∇v|² - Q² B(v)` there, then at every `p ∈ O`
`∂ₜw - Δw - 2ℓ(v)∇v·∇w ≤ -2(-ℓ'(v)) w² - 2 ∇v·(B(v)∇(Q²)) - 2 Q² B'(v) w`. -/
theorem weq_le (hv : ContDiffOn ℝ ∞ v O) (hℓ : ContDiff ℝ ∞ ℓ) (hB : ContDiff ℝ ∞ B)
    (hQ : ContDiff ℝ ∞ Q)
    (hveq : ∀ q ∈ O, dd timeDir v q = ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) v) q +
      ℓ (v q) * wOf v q - Q q.1 ^ 2 * B (v q))
    {p : E d × ℝ} (hp : p ∈ O) :
    dd timeDir (wOf v) p - ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) (wOf v)) p -
        2 * ℓ (v p) * ∑ i : Idx d, dd (spaceDir i) v p * dd (spaceDir i) (wOf v) p ≤
      -2 * (-deriv ℓ (v p)) * wOf v p ^ 2 -
        2 * ∑ i : Idx d, dd (spaceDir i) v p * (B (v p) * dd (spaceDir i) (fun q ↦ Q q.1 ^ 2) p) -
        2 * (Q p.1 ^ 2 * deriv B (v p)) * wOf v p := by
  set G : Idx d → E d × ℝ → ℝ := fun j ↦ dd (spaceDir j) v with hG
  have hGs : ∀ j, ContDiffOn ℝ ∞ (G j) O := fun j ↦ hv.dd hO _
  have hddGs : ∀ a j, ContDiffOn ℝ ∞ (dd a (G j)) O := fun a j ↦ (hGs j).dd hO a
  have hWs : ContDiffOn ℝ ∞ (wOf v) O := ContDiffOn.sum fun i _ ↦ (hGs i).pow 2
  have diff : ∀ {f : E d × ℝ → ℝ}, ContDiffOn ℝ ∞ f O → DifferentiableAt ℝ f p :=
    fun hf ↦ hf.differentiableAt' hO hp
  have hQ2 : ContDiff ℝ ∞ (fun q : E d × ℝ ↦ Q q.1 ^ 2) := (hQ.comp contDiff_fst).pow 2
  -- (b) time derivative of `w`
  have hwt : dd timeDir (wOf v) p = ∑ j, 2 * G j p * dd timeDir (G j) p :=
    dd_wOf_eqOn hO hv _ hp
  -- (c) second spatial derivatives of `w`
  have hwxx : ∀ i, dd (spaceDir i) (dd (spaceDir i) (wOf v)) p =
      ∑ j, (2 * dd (spaceDir i) (G j) p ^ 2 +
        2 * G j p * dd (spaceDir i) (dd (spaceDir i) (G j)) p) := by
    intro i
    rw [dd_congr (dd_wOf_eqOn hO hv _) hO hp]
    rw [dd_sum univ (F := fun j q ↦ 2 * dd (spaceDir j) v q * dd (spaceDir i) (dd (spaceDir j) v) q)
      (fun j _ ↦ ((diff (hGs j)).const_mul 2).fun_mul (diff (hddGs _ j))) _]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [dd_mul (f := fun q ↦ 2 * dd (spaceDir j) v q)
      (g := dd (spaceDir i) (dd (spaceDir j) v)) ((diff (hGs j)).const_mul 2) (diff (hddGs _ j)),
      dd_const_mul (diff (hGs j))]
    ring
  have hwx : ∀ i, dd (spaceDir i) (wOf v) p = ∑ j, 2 * G j p * dd (spaceDir i) (G j) p :=
    fun i ↦ dd_wOf_eqOn hO hv _ hp
  -- (d) the differentiated equation
  have hdeq : ∀ j, dd timeDir (G j) p =
      ∑ i, dd (spaceDir i) (dd (spaceDir i) (G j)) p + ℓ (v p) * dd (spaceDir j) (wOf v) p +
        wOf v p * (deriv ℓ (v p) * G j p) -
        (Q p.1 ^ 2 * (deriv B (v p) * G j p) +
          B (v p) * dd (spaceDir j) (fun q ↦ Q q.1 ^ 2) p) := by
    intro j
    have hv2 : ContDiffAt ℝ 2 v p := hv.contDiffAt_two hO hp
    -- `∂ₜ∂ⱼv = ∂ⱼ∂ₜv`
    have h1 : dd timeDir (G j) p = dd (spaceDir j) (dd timeDir v) p := dd_comm hv2 _ _
    rw [h1, dd_congr hveq hO hp]
    have hA : DifferentiableAt ℝ (fun q ↦ ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) v) q) p :=
      diff (ContDiffOn.sum fun i _ ↦ (hGs i).dd hO _)
    have hℓv : DifferentiableAt ℝ (fun q ↦ ℓ (v q)) p :=
      (hℓ.differentiable (by simp) _).comp p (diff hv)
    have hBv : DifferentiableAt ℝ (fun q ↦ B (v q)) p :=
      (hB.differentiable (by simp) _).comp p (diff hv)
    have hQd : DifferentiableAt ℝ (fun q : E d × ℝ ↦ Q q.1 ^ 2) p :=
      hQ2.differentiable (by simp) p
    rw [dd_sub (f := fun q ↦ ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) v) q + ℓ (v q) * wOf v q)
      (g := fun q ↦ Q q.1 ^ 2 * B (v q)) (hA.fun_add (hℓv.fun_mul (diff hWs))) (hQd.fun_mul hBv),
      dd_add (f := fun q ↦ ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) v) q)
        (g := fun q ↦ ℓ (v q) * wOf v q) hA (hℓv.fun_mul (diff hWs)),
      dd_sum univ (F := fun i ↦ dd (spaceDir i) (dd (spaceDir i) v))
        (fun i _ ↦ diff ((hGs i).dd hO _)),
      dd_mul (f := fun q ↦ ℓ (v q)) (g := wOf v) hℓv (diff hWs),
      dd_mul (f := fun q ↦ Q q.1 ^ 2) (g := fun q ↦ B (v q)) hQd hBv,
      dd_comp (hℓ.differentiable (by simp) _) (diff hv),
      dd_comp (hB.differentiable (by simp) _) (diff hv)]
    -- third derivatives commute
    have h3 : ∀ i, dd (spaceDir j) (dd (spaceDir i) (dd (spaceDir i) v)) p =
        dd (spaceDir i) (dd (spaceDir i) (G j)) p := by
      intro i
      rw [dd_comm ((hGs i).contDiffAt_two hO hp)]
      refine dd_congr (fun q hq ↦ ?_) hO hp _
      exact dd_comm (hv.contDiffAt_two hO hq) _ _
    rw [sum_congr rfl fun i _ ↦ h3 i]
    ring
  -- (e) combine
  have hH : 0 ≤ ∑ j, ∑ i, dd (spaceDir i) (G j) p ^ 2 :=
    sum_nonneg fun j _ ↦ sum_nonneg fun i _ ↦ sq_nonneg _
  have hW : wOf v p = ∑ j, G j p ^ 2 := rfl
  have hlhs : dd timeDir (wOf v) p - ∑ i, dd (spaceDir i) (dd (spaceDir i) (wOf v)) p =
      ∑ j, 2 * G j p * (dd timeDir (G j) p - ∑ i, dd (spaceDir i) (dd (spaceDir i) (G j)) p) -
        2 * ∑ j, ∑ i, dd (spaceDir i) (G j) p ^ 2 := by
    rw [hwt, sum_congr rfl fun i _ ↦ hwxx i, sum_comm, mul_sum, ← sum_sub_distrib,
      ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [mul_sub, mul_sum, sum_add_distrib, ← mul_sum, mul_sum]
    ring
  have e : ∀ j, 2 * G j p * (dd timeDir (G j) p - ∑ i, dd (spaceDir i) (dd (spaceDir i) (G j)) p) =
      2 * ℓ (v p) * (G j p * dd (spaceDir j) (wOf v) p) +
        2 * deriv ℓ (v p) * wOf v p * G j p ^ 2 - 2 * (Q p.1 ^ 2 * deriv B (v p)) * G j p ^ 2 -
        2 * (G j p * (B (v p) * dd (spaceDir j) (fun q ↦ Q q.1 ^ 2) p)) := fun j ↦ by
    rw [hdeq j]; ring
  rw [hlhs, sum_congr rfl fun j _ ↦ e j]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [← hW]
  change _ ≤ -2 * -deriv ℓ (v p) * wOf v p ^ 2 -
    2 * ∑ i : Idx d, G i p * (B (v p) * dd (spaceDir i) (fun q ↦ Q q.1 ^ 2) p) -
    2 * (Q p.1 ^ 2 * deriv B (v p)) * wOf v p
  nlinarith

end Weq

/-! ### The inequality at a maximum of `z = η² w` -/

section MaxPoint

variable {v : E d × ℝ → ℝ} {ℓ B : ℝ → ℝ} {η : E d × ℝ → ℝ}

omit hu hβ hΦ hΦ' hΨ hΦΨ heq in
include hO in
/-- `D_a(η² W) = η² D_a W + W (2 η D_a η)` on `O`. -/
theorem dd_z_eqOn (hW : ContDiffOn ℝ ∞ (wOf v) O) (hη : ContDiff ℝ ∞ η) (a : E d × ℝ) :
    EqOn (dd a (fun q ↦ η q ^ 2 * wOf v q))
      (fun q ↦ η q ^ 2 * dd a (wOf v) q + wOf v q * (2 * η q * dd a η q)) O := by
  intro q hq
  have hηd : DifferentiableAt ℝ η q := hη.differentiable (by simp) q
  rw [dd_mul (f := fun q ↦ η q ^ 2) (g := wOf v) (hηd.pow 2) (hW.differentiableAt' hO hq),
    dd_sq hηd]

omit hu hβ hΦ hΦ' hΨ hΦΨ heq in
include hO in
/-- **The Bernstein inequality at a maximum point** (Step 3, (A.10)): at a point
`p ∈ O` where `z = η² w` has a local maximum relative to the parabolic past, with
`0 < η(p) ≤ 1`, `w(p) ≥ 1`, `ℓ'(v) < 0` and `ℓ(v)² ≤ 2|ℓ'(v)|`:
`|ℓ'(v)| z ≤ C_η + 2 η² (|Q² B'(v)| + K)` where `|B(v) ∇(Q²)| ≤ K` and
`C_η = 16 |∇η|² + 2|∂ₜη| + 2|Δη|`. -/
theorem max_point_bound (hv : ContDiffOn ℝ ∞ v O) (hℓ : ContDiff ℝ ∞ ℓ) (hB : ContDiff ℝ ∞ B)
    (hQ : ContDiff ℝ ∞ Q)
    (hveq : ∀ q ∈ O, dd timeDir v q = ∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) v) q +
      ℓ (v q) * wOf v q - Q q.1 ^ 2 * B (v q))
    (hη : ContDiff ℝ ∞ η) {p : E d × ℝ} (hp : p ∈ O) (hηp : 0 < η p) (hη1 : η p ≤ 1)
    (hmax : ∀ᶠ q in 𝓝 p, q.2 ≤ p.2 → η q ^ 2 * wOf v q ≤ η p ^ 2 * wOf v p)
    (hW1 : 1 ≤ wOf v p) (ha : 0 < -deriv ℓ (v p)) (hℓ2 : ℓ (v p) ^ 2 ≤ 2 * -deriv ℓ (v p))
    {K : ℝ} (hK : 0 ≤ K)
    (hkx : ∑ i : Idx d, (B (v p) * dd (spaceDir i) (fun q ↦ Q q.1 ^ 2) p) ^ 2 ≤ K ^ 2) :
    -deriv ℓ (v p) * (η p ^ 2 * wOf v p) ≤
      16 * ∑ i : Idx d, dd (spaceDir i) η p ^ 2 + 2 * |dd timeDir η p| +
        2 * |∑ i : Idx d, dd (spaceDir i) (dd (spaceDir i) η) p| +
        2 * η p ^ 2 * (|Q p.1 ^ 2 * deriv B (v p)| + K) := by
  have hWs : ContDiffOn ℝ ∞ (wOf v) O := ContDiffOn.sum fun i _ ↦ (hv.dd hO _).pow 2
  set z : E d × ℝ → ℝ := fun q ↦ η q ^ 2 * wOf v q with hz
  have hzs : ContDiffOn ℝ ∞ z O := (hη.contDiffOn.pow 2).mul hWs
  have hz2 : ContDiffAt ℝ 2 z p := hzs.contDiffAt_two hO hp
  have hηd : ∀ q, DifferentiableAt ℝ η q := fun q ↦ hη.differentiable (by simp) q
  have hddη : ∀ a, ContDiff ℝ ∞ (dd a η) := fun a ↦
    contDiffOn_univ.1 ((hη.contDiffOn (s := univ)).dd isOpen_univ a)
  -- first-order expansion
  have hz1 : ∀ a, dd a z p = 2 * η p * dd a η p * wOf v p + η p ^ 2 * dd a (wOf v) p := by
    intro a; rw [dd_z_eqOn hO hWs hη a hp]; ring
  -- second-order expansion
  have hzz : ∀ a, dd a (dd a z) p = (2 * dd a η p ^ 2 + 2 * η p * dd a (dd a η) p) * wOf v p +
      4 * η p * dd a η p * dd a (wOf v) p + η p ^ 2 * dd a (dd a (wOf v)) p := by
    intro a
    rw [dd_congr (dd_z_eqOn hO hWs hη a) hO hp]
    have h1 : DifferentiableAt ℝ (fun q ↦ η q ^ 2) p := (hηd p).pow 2
    have h2 : DifferentiableAt ℝ (dd a (wOf v)) p := (hWs.dd hO a).differentiableAt' hO hp
    have h3 : DifferentiableAt ℝ (wOf v) p := hWs.differentiableAt' hO hp
    have h4 : DifferentiableAt ℝ (fun q ↦ 2 * η q * dd a η q) p :=
      ((hηd p).const_mul 2).fun_mul ((hddη a).differentiable (by simp) p)
    rw [dd_add (f := fun q ↦ η q ^ 2 * dd a (wOf v) q)
        (g := fun q ↦ wOf v q * (2 * η q * dd a η q)) (h1.fun_mul h2) (h3.fun_mul h4),
      dd_mul (f := fun q ↦ η q ^ 2) (g := dd a (wOf v)) h1 h2,
      dd_mul (f := wOf v) (g := fun q ↦ 2 * η q * dd a η q) h3 h4,
      dd_mul (f := fun q ↦ 2 * η q) (g := dd a η) ((hηd p).const_mul 2)
        ((hddη a).differentiable (by simp) p),
      dd_const_mul (hηd p), dd_sq (hηd p)]
    ring
  have hmax' : ∀ᶠ q in 𝓝 p, q.2 ≤ p.2 → z q ≤ z p := hmax
  -- the derivative tests
  have hC : ∀ i : Idx d, 2 * η p * dd (spaceDir i) η p * (∑ j : Idx d, dd (spaceDir j) v p ^ 2) +
      η p ^ 2 * dd (spaceDir i) (wOf v) p = 0 := fun i ↦ by
    rw [← dd_spaceDir_eq_zero_of_max hz2 hmax' i, hz1]; rfl
  have hD : ∑ i : Idx d, ((2 * dd (spaceDir i) η p ^ 2 + 2 * η p * dd (spaceDir i)
      (dd (spaceDir i) η) p) * (∑ j : Idx d, dd (spaceDir j) v p ^ 2) +
      4 * η p * dd (spaceDir i) η p * dd (spaceDir i) (wOf v) p +
      η p ^ 2 * dd (spaceDir i) (dd (spaceDir i) (wOf v)) p) ≤ 0 := by
    have := sum_dd_spaceDir_nonpos_of_max hz2 hmax'
    rw [sum_congr rfl fun i _ ↦ hzz (spaceDir i)] at this
    exact this
  have hE : 0 ≤ 2 * η p * dd timeDir η p * (∑ j : Idx d, dd (spaceDir j) v p ^ 2) +
      η p ^ 2 * dd timeDir (wOf v) p := by
    have := dd_timeDir_nonneg_of_max hz2 hmax'
    rw [hz1] at this
    exact this
  have hBw := weq_le hO hv hℓ hB hQ hveq hp
  have key := bernstein_point_algebra (ι := Idx d) (fun i ↦ dd (spaceDir i) v p)
    (fun i ↦ dd (spaceDir i) η p) (fun i ↦ dd (spaceDir i) (dd (spaceDir i) η) p)
    (fun i ↦ dd (spaceDir i) (wOf v) p) (fun i ↦ dd (spaceDir i) (dd (spaceDir i) (wOf v)) p)
    (fun i ↦ B (v p) * dd (spaceDir i) (fun q ↦ Q q.1 ^ 2) p)
    (ηt := dd timeDir η p) (wt := dd timeDir (wOf v) p) (ℓ := ℓ (v p))
    (kv := Q p.1 ^ 2 * deriv B (v p)) hηp hη1 ha hℓ2 hK hkx hW1 hBw hC hD hE
  exact key

end MaxPoint

end BernsteinMax

end PerronVariational

end
