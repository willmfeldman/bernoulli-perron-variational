/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import PerronVariational.Basic.KLimit
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Upper Kuratowski limits: API and Lemmas 5.1–5.2

Basic API for `upperKLimit` (the `limsup*` of sets) along an arbitrary filter, and the two
technical lemmas (Lemmas 5.1 and 5.2) of F. Abedin, W. M. Feldman, K. Stinson, *Variational
properties of Perron's extremal solutions in the Bernoulli one-phase problem*, arXiv:2609.14981
("the paper").

## Main results

* `isClosed_upperKLimit`, `upperKLimit_const`, `upperKLimit_mono`,
  `upperKLimit_inter_subset`: basic API.
* `mem_upperKLimit_of_tendsto`, `mem_upperKLimit_iff_exists_seq`,
  `mem_upperKLimit_atTop_iff`: sequential characterizations (first-countable spaces).
* `inter_upperKLimit_nonempty_of_isCompact`: if `A i` meets a compact `K` frequently, then
  `upperKLimit A l` meets `K`.
* `eventually_forall_lt_of_tendstoUniformlyOn`: the "upper half" of Lemma 5.1.
* `limsup_max_eq`: Lemma 5.1, stated with `EReal`-valued suprema, so
  that it also covers the case `E* ∩ F = ∅` ignored by the paper.
* `precOn_eventually_of_tendsto`: Lemma 5.2, for an
  arbitrary filter.
* `upperKLimit_iInter_subset_closure_iUnion`: the inclusion `E_∞ ⊆ closure (⋃ t, E_t)` used in
  Cor 5.7.

No countability assumptions are needed for Lemmas 5.1–5.2: the compactness step uses finite
subcovers rather than subsequences.
-/

open Set Filter Topology

@[expose] public section

namespace PerronVariational

variable {X ι κ : Type*} [TopologicalSpace X]

section Basic

variable {A B : ι → Set X} {l l' : Filter ι} {x : X}

theorem mem_upperKLimit :
    x ∈ upperKLimit A l ↔ ∀ N ∈ 𝓝 x, ∃ᶠ i in l, (A i ∩ N).Nonempty := Iff.rfl

/-- Membership in `upperKLimit` tested on a basis of neighbourhoods. -/
theorem mem_upperKLimit_iff_hasBasis {p : κ → Prop} {s : κ → Set X} (h : (𝓝 x).HasBasis p s) :
    x ∈ upperKLimit A l ↔ ∀ k, p k → ∃ᶠ i in l, (A i ∩ s k).Nonempty := by
  refine ⟨fun hx k hk ↦ hx _ (h.mem_of_mem hk), fun hx N hN ↦ ?_⟩
  obtain ⟨k, hk, hkN⟩ := h.mem_iff.1 hN
  exact (hx k hk).mono fun i ⟨y, hyA, hyk⟩ ↦ ⟨y, hyA, hkN hyk⟩

/-- The upper Kuratowski limit is closed. -/
theorem isClosed_upperKLimit : IsClosed (upperKLimit A l) := by
  refine isClosed_of_closure_subset fun x hx N hN ↦ ?_
  obtain ⟨O, hON, hO, hxO⟩ := mem_nhds_iff.1 hN
  obtain ⟨y, hyO, hy⟩ := mem_closure_iff.1 hx O hO hxO
  exact (hy O (hO.mem_nhds hyO)).mono fun i ⟨z, hzA, hzO⟩ ↦ ⟨z, hzA, hON hzO⟩

theorem closure_upperKLimit : closure (upperKLimit A l) = upperKLimit A l :=
  isClosed_upperKLimit.closure_eq

/-- Monotonicity in the family (eventual inclusion suffices). -/
theorem upperKLimit_mono_of_eventually (h : ∀ᶠ i in l, A i ⊆ B i) :
    upperKLimit A l ⊆ upperKLimit B l := fun _ hx N hN ↦
  (hx N hN).mp <| h.mono fun _ hAB ⟨y, hyA, hyN⟩ ↦ ⟨y, hAB hyA, hyN⟩

/-- Monotonicity in the family. -/
theorem upperKLimit_mono (h : ∀ i, A i ⊆ B i) : upperKLimit A l ⊆ upperKLimit B l :=
  upperKLimit_mono_of_eventually (Eventually.of_forall h)

theorem upperKLimit_congr (h : ∀ᶠ i in l, A i = B i) : upperKLimit A l = upperKLimit B l :=
  (upperKLimit_mono_of_eventually (h.mono fun _ h ↦ h.le)).antisymm
    (upperKLimit_mono_of_eventually (h.mono fun _ h ↦ h.ge))

/-- Monotonicity in the filter. -/
theorem upperKLimit_mono_filter (h : l ≤ l') : upperKLimit A l ⊆ upperKLimit A l' :=
  fun _ hx N hN ↦ (hx N hN).filter_mono h

@[simp]
theorem upperKLimit_bot : upperKLimit A ⊥ = ∅ := by
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro hx
  simpa using hx univ univ_mem

/-- Reindexing along a map tending to `l` (e.g. passing to a subsequence) can only shrink the
upper Kuratowski limit. -/
theorem upperKLimit_comp_subset {m : Filter κ} {ψ : κ → ι} (hψ : Tendsto ψ m l) :
    upperKLimit (A ∘ ψ) m ⊆ upperKLimit A l := fun _ hx N hN ↦ hψ.frequently (hx N hN)

/-- `upperKLimit A l ⊆ closure S` as soon as eventually `A i ⊆ S`. -/
theorem upperKLimit_subset_closure_of_eventually {S : Set X} (h : ∀ᶠ i in l, A i ⊆ S) :
    upperKLimit A l ⊆ closure S := by
  intro x hx
  refine mem_closure_iff_nhds.2 fun N hN ↦ ?_
  obtain ⟨i, ⟨y, hyA, hyN⟩, hi⟩ := ((hx N hN).and_eventually h).exists
  exact ⟨y, hyN, hi hyA⟩

theorem upperKLimit_subset_of_eventually {S : Set X} (hS : IsClosed S) (h : ∀ᶠ i in l, A i ⊆ S) :
    upperKLimit A l ⊆ S :=
  (upperKLimit_subset_closure_of_eventually h).trans hS.closure_subset

theorem upperKLimit_subset_closure_iUnion : upperKLimit A l ⊆ closure (⋃ i, A i) :=
  upperKLimit_subset_closure_of_eventually (Eventually.of_forall fun i ↦ subset_iUnion A i)

/-- Upper Kuratowski limit of a constant family. -/
theorem upperKLimit_const [l.NeBot] (S : Set X) : upperKLimit (fun _ ↦ S) l = closure S := by
  refine (upperKLimit_subset_closure_of_eventually
    (Eventually.of_forall fun _ ↦ subset_rfl)).antisymm fun x hx N hN ↦ ?_
  obtain ⟨y, hyN, hyS⟩ := mem_closure_iff_nhds.1 hx N hN
  exact frequently_const.2 ⟨y, hyS, hyN⟩

theorem upperKLimit_inter_subset_inter :
    upperKLimit (fun i ↦ A i ∩ B i) l ⊆ upperKLimit A l ∩ upperKLimit B l :=
  subset_inter (upperKLimit_mono fun _ ↦ inter_subset_left)
    (upperKLimit_mono fun _ ↦ inter_subset_right)

theorem upperKLimit_inter_subset_closure (F : Set X) :
    upperKLimit (fun i ↦ A i ∩ F) l ⊆ upperKLimit A l ∩ closure F :=
  subset_inter (upperKLimit_mono fun _ ↦ inter_subset_left)
    (upperKLimit_subset_closure_of_eventually (Eventually.of_forall fun _ ↦ inter_subset_right))

/-- `limsup* (A_i ∩ F) ⊆ (limsup* A_i) ∩ F` for closed `F` (used in Prop 5.3). -/
theorem upperKLimit_inter_subset {F : Set X} (hF : IsClosed F) :
    upperKLimit (fun i ↦ A i ∩ F) l ⊆ upperKLimit A l ∩ F :=
  fun _ hx ↦ let h := upperKLimit_inter_subset_closure F hx; ⟨h.1, hF.closure_subset h.2⟩

theorem upperKLimit_union :
    upperKLimit (fun i ↦ A i ∪ B i) l = upperKLimit A l ∪ upperKLimit B l := by
  refine Subset.antisymm (fun x hx ↦ ?_)
    (union_subset (upperKLimit_mono fun _ ↦ subset_union_left)
      (upperKLimit_mono fun _ ↦ subset_union_right))
  by_contra hxAB
  simp only [mem_union, not_or, mem_upperKLimit, not_forall, not_frequently,
    not_nonempty_iff_eq_empty] at hxAB
  obtain ⟨⟨N, hN, hAN⟩, ⟨M, hM, hBM⟩⟩ := hxAB
  obtain ⟨i, ⟨y, hyAB, hyN, hyM⟩, hA, hB⟩ :=
    ((hx (N ∩ M) (inter_mem hN hM)).and_eventually (hAN.and hBM)).exists
  rcases hyAB with hy | hy
  · exact (eq_empty_iff_forall_notMem.1 hA) y ⟨hy, hyN⟩
  · exact (eq_empty_iff_forall_notMem.1 hB) y ⟨hy, hyM⟩

end Basic

section Sequential

variable {A : ι → Set X} {l : Filter ι} {x : X}

/-- Limits of points `y k ∈ A (ψ k)` with `ψ k → l` lie in the upper Kuratowski limit. -/
theorem mem_upperKLimit_of_tendsto {m : Filter κ} [m.NeBot] {ψ : κ → ι} {y : κ → X}
    (hψ : Tendsto ψ m l) (hy : Tendsto y m (𝓝 x)) (hyA : ∀ᶠ k in m, y k ∈ A (ψ k)) :
    x ∈ upperKLimit A l := by
  intro N hN
  refine hψ.frequently (Eventually.frequently ?_)
  filter_upwards [hy hN, hyA] with k hkN hkA using ⟨y k, hkA, hkN⟩

/-- Sequential characterization of `upperKLimit` along a countably generated filter in a
first-countable space. -/
theorem mem_upperKLimit_iff_exists_seq [FirstCountableTopology X] [l.IsCountablyGenerated] :
    x ∈ upperKLimit A l ↔
      ∃ ψ : ℕ → ι, Tendsto ψ atTop l ∧ ∃ y : ℕ → X, (∀ n, y n ∈ A (ψ n)) ∧
        Tendsto y atTop (𝓝 x) := by
  refine ⟨fun hx ↦ ?_, fun ⟨ψ, hψ, y, hyA, hy⟩ ↦
    mem_upperKLimit_of_tendsto hψ hy (Eventually.of_forall hyA)⟩
  obtain ⟨s, hs⟩ := l.exists_antitone_basis
  obtain ⟨t, ht⟩ := (𝓝 x).exists_antitone_basis
  have key : ∀ n, ∃ i, i ∈ s n ∧ (A i ∩ t n).Nonempty := fun n ↦
    (((hx _ (ht.mem n)).and_eventually (hs.mem n)).exists).imp fun _ h ↦ ⟨h.2, h.1⟩
  choose ψ hψs hψA using key
  choose y hyA hyt using hψA
  exact ⟨ψ, hs.tendsto hψs, y, hyA, ht.tendsto hyt⟩

/-- Sequential characterization of `upperKLimit A atTop` for sequences of sets in a
first-countable space: `x` is the limit of `y k ∈ A (φ k)` along a subsequence `φ`. -/
theorem mem_upperKLimit_atTop_iff [FirstCountableTopology X] {A : ℕ → Set X} :
    x ∈ upperKLimit A atTop ↔
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → X, (∀ k, y k ∈ A (φ k)) ∧
        Tendsto y atTop (𝓝 x) := by
  refine ⟨fun hx ↦ ?_, fun ⟨φ, hφ, y, hyA, hy⟩ ↦
    mem_upperKLimit_of_tendsto hφ.tendsto_atTop hy (Eventually.of_forall hyA)⟩
  obtain ⟨ψ, hψ, y, hyA, hy⟩ := mem_upperKLimit_iff_exists_seq.1 hx
  obtain ⟨φ, hφ, hψφ⟩ := strictMono_subseq_of_tendsto_atTop hψ
  exact ⟨ψ ∘ φ, hψφ, y ∘ φ, fun k ↦ hyA (φ k), hy.comp hφ.tendsto_atTop⟩

end Sequential

section Compact

variable {A : ι → Set X} {l : Filter ι} {K : Set X}

/-- If `A i` meets the compact set `K` for frequently many `i`, then so does `upperKLimit A l`.
(No countability is needed: the proof uses finite subcovers.) -/
theorem inter_upperKLimit_nonempty_of_isCompact (hK : IsCompact K)
    (h : ∃ᶠ i in l, (A i ∩ K).Nonempty) : (upperKLimit A l ∩ K).Nonempty := by
  by_contra hne
  have hx : ∀ x ∈ K, ∃ N ∈ 𝓝 x, ∀ᶠ i in l, A i ∩ N = ∅ := by
    intro x hxK
    have hx : x ∉ upperKLimit A l := fun hx ↦ hne ⟨x, hx, hxK⟩
    simpa [mem_upperKLimit, not_frequently, not_nonempty_iff_eq_empty] using hx
  choose! N hN hAN using hx
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover N hN
  have hev : ∀ᶠ i in l, ∀ x ∈ t, A i ∩ N x = ∅ :=
    (eventually_all_finset t).2 fun x hx ↦ hAN x (htK x hx)
  refine h.mp (hev.mono fun i hi ⟨y, hyA, hyK⟩ ↦ ?_) |>.exists.elim fun _ h ↦ h
  obtain ⟨x, hxt, hyN⟩ := mem_iUnion₂.1 (hKt hyK)
  exact absurd (hi x hxt ▸ ⟨hyA, hyN⟩ : y ∈ (∅ : Set X)) (notMem_empty y)

/-- Contrapositive form of `inter_upperKLimit_nonempty_of_isCompact`: if `upperKLimit A l` misses
the compact set `K`, then eventually `A i` misses `K`. -/
theorem eventually_inter_eq_empty_of_isCompact (hK : IsCompact K)
    (h : upperKLimit A l ∩ K = ∅) : ∀ᶠ i in l, A i ∩ K = ∅ := by
  by_contra hev
  simp only [not_eventually, ← nonempty_iff_ne_empty] at hev
  exact (inter_upperKLimit_nonempty_of_isCompact hK hev).ne_empty h

/-- `limsup* A ∩ K` is compact for compact `K` (so continuous functions attain their maximum on
it, as used in the paper's Lemma 5.1). -/
theorem isCompact_upperKLimit_inter (hK : IsCompact K) : IsCompact (upperKLimit A l ∩ K) :=
  hK.inter_left isClosed_upperKLimit

end Compact

section Uniform

variable {A E : ι → Set X} {l : Filter ι} {F : Set X} {w : X → ℝ} {ws : ι → X → ℝ}

/-- Semicontinuity of sublevel sets under uniform convergence: if eventually `c ≤ ws i` on
`A i ⊆ F`, `ws i → w` uniformly on `F` and `w` is continuous on `F`, then `c ≤ w` on
`upperKLimit A l ∩ F`. -/
theorem le_of_mem_upperKLimit (hw : ContinuousOn w F) (hws : TendstoUniformlyOn ws w l F)
    {c : ℝ} (hA : ∀ᶠ i in l, ∀ p ∈ A i, p ∈ F ∧ c ≤ ws i p) {x : X}
    (hx : x ∈ upperKLimit A l) (hxF : x ∈ F) : c ≤ w x := by
  by_contra! hlt
  set ε := (c - w x) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hN : {p | p ∈ F → w p < w x + ε} ∈ 𝓝 x :=
    eventually_nhdsWithin_iff.1 <| (hw x hxF).eventually (Iio_mem_nhds (by linarith))
  obtain ⟨i, ⟨p, hpA, hpN⟩, hA, hunif⟩ :=
    ((hx _ hN).and_eventually (hA.and (Metric.tendstoUniformlyOn_iff.1 hws ε hεpos))).exists
  obtain ⟨hpF, hcp⟩ := hA p hpA
  have h1 := hpN hpF
  have h2 := hunif p hpF
  rw [Real.dist_eq, abs_lt] at h2
  linarith

/-- Upper half of Lemma 5.1: if `w < c` on `E* ∩ F` with
`E* = limsup* E_i`, `F` compact, `w` continuous on `F` and `ws i → w` uniformly on `F`, then
eventually `ws i < c` on `E i ∩ F`. -/
theorem eventually_forall_lt_of_tendstoUniformlyOn (hF : IsCompact F) (hw : ContinuousOn w F)
    (hws : TendstoUniformlyOn ws w l F) {c : ℝ} (hc : ∀ p ∈ upperKLimit E l ∩ F, w p < c) :
    ∀ᶠ i in l, ∀ p ∈ E i ∩ F, ws i p < c := by
  set B : ι → Set X := fun i ↦ {p ∈ E i ∩ F | c ≤ ws i p}
  have hB : ∀ᶠ i in l, B i ∩ F = ∅ := by
    refine eventually_inter_eq_empty_of_isCompact hF
      (eq_empty_of_forall_notMem fun x ⟨hxB, hxF⟩ ↦ ?_)
    have hcx : c ≤ w x := le_of_mem_upperKLimit hw hws
      (Eventually.of_forall fun i p hp ↦ ⟨hp.1.2, hp.2⟩) hxB hxF
    have hxE : x ∈ upperKLimit E l := upperKLimit_mono (fun i p hp ↦ hp.1.1) hxB
    exact (hc x ⟨hxE, hxF⟩).not_ge hcx
  filter_upwards [hB] with i hi p hp
  by_contra! hcp
  exact (eq_empty_iff_forall_notMem.1 hi) p ⟨⟨hp, hcp⟩, hp.2⟩

/-- Lower half of Lemma 5.1: if `p ∈ E* ∩ F` and `c < w p`, then frequently some point of
`E i ∩ F` has `c < ws i`. Needs `E i ⊆ F` eventually (the paper's "`E_j` closed in `F`"). -/
theorem frequently_exists_lt_of_mem_upperKLimit (hEF : ∀ᶠ i in l, E i ⊆ F)
    (hw : ContinuousOn w F) (hws : TendstoUniformlyOn ws w l F) {x : X}
    (hx : x ∈ upperKLimit E l ∩ F) {c : ℝ} (hc : c < w x) :
    ∃ᶠ i in l, ∃ p ∈ E i ∩ F, c < ws i p := by
  set ε := (w x - c) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hN : {p | p ∈ F → w x - ε < w p} ∈ 𝓝 x :=
    eventually_nhdsWithin_iff.1 <| (hw x hx.2).eventually (Ioi_mem_nhds (by linarith))
  refine ((hx.1 _ hN).and_eventually (hEF.and
    (Metric.tendstoUniformlyOn_iff.1 hws ε hεpos))).mono ?_
  rintro i ⟨⟨p, hpE, hpN⟩, hEF, hunif⟩
  have hpF := hEF hpE
  have h1 := hpN hpF
  have h2 := hunif p hpF
  rw [Real.dist_eq, abs_lt] at h2
  exact ⟨p, ⟨hpE, hpF⟩, by linarith⟩

/-- **Lemma 5.1**. Let `F` be compact, `E i ⊆ F` eventually,
`w` continuous on `F`, and `ws i → w` uniformly on `F`. With `E* = limsup* E_i`,
`sup_{E* ∩ F} w = limsup_i sup_{E i ∩ F} ws i`.

The suprema are taken in `EReal`, so that the empty cases are covered (sup over `∅` is `⊥`);
when `E* ∩ F ≠ ∅` the left-hand side is the paper's `max` (a continuous function on a nonempty
compact set). Closedness of `E i` and continuity of `ws i` are not needed. -/
theorem limsup_max_eq (hF : IsCompact F) (hEF : ∀ᶠ i in l, E i ⊆ F) (hw : ContinuousOn w F)
    (hws : TendstoUniformlyOn ws w l F) :
    ⨆ p ∈ upperKLimit E l ∩ F, (w p : EReal) =
      limsup (fun i ↦ ⨆ p ∈ E i ∩ F, (ws i p : EReal)) l := by
  apply le_antisymm
  · refine iSup₂_le fun x hx ↦ ?_
    refine le_of_forall_lt fun c hc ↦ ?_
    obtain ⟨c', hcc', hc'⟩ := EReal.lt_iff_exists_real_btwn.1 hc
    refine hcc'.trans_le (le_limsup_of_frequently_le' ?_)
    refine (frequently_exists_lt_of_mem_upperKLimit hEF hw hws hx
      (EReal.coe_lt_coe_iff.1 hc')).mono fun i ⟨p, hp, hlt⟩ ↦ ?_
    exact (EReal.coe_le_coe_iff.2 hlt.le).trans (le_iSup₂ (f := fun p _ ↦ (ws i p : EReal)) p hp)
  · refine le_of_forall_gt fun c hc ↦ ?_
    obtain ⟨c', hc', hc'c⟩ := EReal.lt_iff_exists_real_btwn.1 hc
    refine (limsup_le_of_le (by isBoundedDefault) ?_).trans_lt hc'c
    have : ∀ p ∈ upperKLimit E l ∩ F, w p < c' := fun p hp ↦
      EReal.coe_lt_coe_iff.1 ((le_iSup₂ (f := fun p _ ↦ (w p : EReal)) p hp).trans_lt hc')
    filter_upwards [eventually_forall_lt_of_tendstoUniformlyOn hF hw hws this] with i hi
    exact iSup₂_le fun p hp ↦ EReal.coe_le_coe_iff.2 (hi p hp).le

end Uniform

section PrecOn

/-- **Lemma 5.2**. Let `F` be compact, `u, v` continuous
on `F` with `u ≺_E v` on `F`, `us i → u` and `vs i → v` uniformly on `F`, and
`limsup* E' ⊆ E` along the filter `l`. Then eventually `us i ≺_{E' i} vs i` on `F`.

Stated for an arbitrary filter `l` (used with `j → ∞`, `t → ∞` and `δ → 0⁺`). The paper's
hypothesis "`E` closed in `F`" is not needed. The paper's proof has `v` in place of `v_j` in its
last line; here the statement is proved with `vs i`. -/
theorem precOn_eventually_of_tendsto {l : Filter ι} {F E : Set X} {E' : ι → Set X}
    {u v : X → ℝ} {us vs : ι → X → ℝ} (hF : IsCompact F) (hu : ContinuousOn u F)
    (hv : ContinuousOn v F) (huv : PrecOn u v E F) (hus : TendstoUniformlyOn us u l F)
    (hvs : TendstoUniformlyOn vs v l F) (hE' : upperKLimit E' l ⊆ E) :
    ∀ᶠ i in l, PrecOn (us i) (vs i) (E' i) F := by
  have h := eventually_forall_lt_of_tendstoUniformlyOn (E := E') (c := 0) hF (hu.sub hv)
    (hus.sub hvs) fun p hp ↦ sub_neg.2 (huv p ⟨hE' hp.1, hp.2⟩)
  exact h.mono fun i hi p hp ↦ sub_neg.1 (hi p hp)

end PrecOn

section Iinter

variable {ι : Type*} [Preorder ι] {S : ι → Set X}

/-- The inclusion `E_∞ ⊆ closure (⋃ t, E_t)` of Cor 5.7, for any filter. No
monotonicity of `S` is needed. -/
theorem upperKLimit_iInter_subset_closure_iUnion (l : Filter ι) :
    upperKLimit (fun T ↦ ⋂ t ≥ T, S t) l ⊆ closure (⋃ t, S t) :=
  upperKLimit_subset_closure_of_eventually <| Eventually.of_forall fun T ↦
    (biInter_subset_of_mem le_rfl).trans (subset_iUnion S T)

/-- Variant of `upperKLimit_iInter_subset_closure_iUnion` with the union over `t ≥ a`. -/
theorem upperKLimit_iInter_subset_closure_biUnion_ge (a : ι) :
    upperKLimit (fun T ↦ ⋂ t ≥ T, S t) atTop ⊆ closure (⋃ t ≥ a, S t) :=
  upperKLimit_subset_closure_of_eventually <| (eventually_ge_atTop a).mono fun _ hT ↦
    (biInter_subset_of_mem le_rfl).trans (subset_biUnion_of_mem (u := S) hT)

/-- Variant of `upperKLimit_iInter_subset_closure_iUnion` with the union over `t > a`
(e.g. `⋃ t > 0` as in Cor 5.7). -/
theorem upperKLimit_iInter_subset_closure_biUnion_gt [NoMaxOrder ι] (a : ι) :
    upperKLimit (fun T ↦ ⋂ t ≥ T, S t) atTop ⊆ closure (⋃ t > a, S t) :=
  upperKLimit_subset_closure_of_eventually <| (eventually_gt_atTop a).mono fun _ hT ↦
    (biInter_subset_of_mem le_rfl).trans (subset_biUnion_of_mem (u := S) hT)

end Iinter

end PerronVariational

end
