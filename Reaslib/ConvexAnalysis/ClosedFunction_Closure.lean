/-
Copyright (c) 2025  Yifan Bai, Yunxi Duan, Zichen Wang, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yifan Bai, Yunxi Duan, Zichen Wang, Chenyi Li
-/
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Reaslib.ConvexAnalysis.IntrinsicInterior
import Reaslib.ConvexAnalysis.Epigraph

/-!
# Closure of a convex function
This file explores the closedness and closure of functions,
establishes the relationship between closure and the lower semicontinuous hull,
and proves several fundamental properties of both closures and lower semicontinuous hulls.
Its significance lies in the fact that closure theory and the relative interiors of convex sets
can be used to derive important topological properties of convex functions.

## References

* Chapter 7 of [R. T. Rockafellar, *Convex Analysis*][rockafellar1970].
-/

open Filter Set Topology Function Module EReal Inner

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

section def_closed


/-!
Definition. A function `g : E → EReal` is said to be closed on a set `s`
if its epigraph over `s` is closed in the topological space `E × ℝ`.
Purpose: provide a topological characterization of closedness for functions,
linking the property of the function to the closedness of its epigraph.
-/
def Function.IsClosed [TopologicalSpace E] (g : E → EReal) (s : Set E) : Prop :=
  _root_.IsClosed (g.Epi s)

/-!
Definition. The lower semicontinuous hull of a function `g : E → EReal`
on a set `s` is the pointwise supremum of all functions `f` that are
lower semicontinuous on `s` and satisfy `f z ≤ g z` for all `z ∈ s`.
Purpose: construct the “best” lower semicontinuous function lying below `g`,
which is useful in analysis and optimization for regularizing or approximating
functions by lower semicontinuous ones.
-/
noncomputable def Function.LowerSemicontinuousHull [TopologicalSpace E]
    (s : Set E) (g : E → EReal) : E → EReal :=
  ⨆ (f : E → EReal) (_ : LowerSemicontinuousOn f s) (_ : ∀ z ∈ s, f z ≤ g z ) , f

/-!
Definition. The closure of a function `g : E → EReal` on a set `s` is defined as follows:
1. If `g` is proper on `s`, its closure is the lower semicontinuous hull of `g`.
2. If `g` is not proper but attains `⊥` somewhere on `s`, its closure is identically `⊥`.
3. Otherwise (not proper and does not attain `⊥`), its closure is identically `⊤`.
Purpose: provide a unified notion of closure for extended-real-valued functions,
capturing both proper and degenerate cases, while ensuring that the resulting
function behaves well topologically (lower semicontinuous) when `g` is proper.
-/
noncomputable def Function.closure [TopologicalSpace E]
    (g : E → EReal) (s : Set E) : E → EReal :=
  letI : Decidable (ProperFunction s g) := Classical.propDecidable (ProperFunction s g)
  letI : Decidable (∃ x ∈ s, g x = ⊥) := Classical.propDecidable (∃ x ∈ s, g x = ⊥)
  if ProperFunction s g then g.LowerSemicontinuousHull s
  else if ∃ x ∈ s, g x = ⊥ then ⊥
  else ⊤

/-!
Lemma. A function `f : E → EReal` is closed on a set `s`
if and only if its epigraph over `s` is closed in the product topology.
Purpose: give an equivalent characterization of closedness of a function
in terms of the topological closedness of its epigraph.
-/
lemma epiclosed [TopologicalSpace E] (f : E → EReal) (s : Set E) :
    f.IsClosed s ↔ _root_.IsClosed (f.Epi s) := Eq.to_iff rfl

/-!
Lemma. If a function `f : E → EReal` is not proper on `univ` and
the closure of `f` attains `⊥` at some point, then the closure of `f` is identically `⊥`.
Purpose: show that for non-proper functions, if the closure takes the bottom value anywhere,
it must take the bottom value everywhere; this helps handle degenerate cases
when working with closures of extended-real-valued functions.
-/
lemma non_proper_closure_exist_bot [NormedAddCommGroup E] (f : E → EReal)
    (hnp : ¬ ProperFunction univ f) (h : ∃ x, f.closure univ x = ⊥) :
    f.closure univ = ⊥ := by
  simp [Function.closure]
  split_ifs with h1
  · simp
  exfalso
  rcases h with ⟨x, hx⟩
  simp [Function.closure, hnp] at hx
  rw [ProperFunction.to_neg] at hnp
  rcases hnp with hl | hr
  · exact h1 hl
  simp at hr
  have : ¬ ∃ x ∈ univ, f x = ⊥ := by push_neg; intro x _; rw [hr x]; simp
  split_ifs at hx
  simp at hx

end def_closed

section le_self

variable [TopologicalSpace E]

/-!
Theorem. For a function `f : E → EReal` on a set `s`,
the lower semicontinuous hull of `f` at any point `x ∈ s`
is less than or equal to the value of `f` at that point.
Purpose: establish that the lower semicontinuous hull provides a pointwise
under-approximation of `f`, which is useful when constructing
the “best” lower semicontinuous function below `f`.
-/
theorem lowersemicontinuoushull_le_self_of_proper
      {s : Set E} (f : E → EReal) :
    ∀ x ∈ s, LowerSemicontinuousHull s f x ≤ f x := by
  intro x hx
  simp [LowerSemicontinuousHull]
  intro i _ hz
  apply hz x hx

/-!
Theorem. If `f : E → EReal` is proper on a set `s`, then
the closure of `f` at any point `x ∈ s` is less than or equal to `f x`.
Purpose: show that taking the closure of a proper function
produces a pointwise under-approximation of the original function,
preserving values below or equal to the original on the domain.
-/
theorem closure_le_self_of_proper (s : Set E) (f : E → EReal)
    [hsf : ProperFunction s f] :
    ∀ x ∈ s, (f.closure s) x ≤ f x := by
  intro x hx
  simp [Function.closure, hsf]
  exact lowersemicontinuoushull_le_self_of_proper f x hx

/-!
Theorem. For any function `f : E → EReal` on a set `s`,
the closure of `f` at any point `x ∈ s` is less than or equal to `f x`.
Purpose: generalize the pointwise under-approximation property of closures
to all functions, handling both proper and non-proper cases uniformly.
-/
theorem closure_le_self (s : Set E) (f : E → EReal) :
    ∀ x ∈ s, (f.closure s) x ≤ f x := by
  intro x hx
  by_cases hsf : ProperFunction s f
  · exact closure_le_self_of_proper s f x hx
  simp [Function.closure, hsf]
  by_cases hf : ∃ x ∈ s, f x = ⊥
  · simp [hf]
  simp [hf]
  push_neg at hf
  apply top_of_ne_bot_of_ne_proper hsf hf hx

end le_self


section low_lowersemicontinous_aux

variable [TopologicalSpace E] {s : Set E} {f : E → EReal}

/-!
Structure `low_lowersemicontinous s f`.
Purpose:
Packages together a function `h : E → EReal` with the properties:
* `h` is lower semicontinuous on the set `s`,
* `h z ≤ f z` for all `z ∈ s`.
This structure is the natural data bundled when constructing the
lower semicontinuous hull of a function, since the hull is defined
as the supremum of all such `h`.
-/
variable (s f) in
structure low_lowersemicontinous where
  h : E → EReal
  hs : LowerSemicontinuousOn h s
  hfz : ∀ z ∈ s, h z ≤ f z

/-!
Instance. There is always a trivial element of `low_lowersemicontinous s f`,
given by the constant bottom function `⊥`.
Purpose: This shows that the collection of admissible lower semicontinuous minorants is nonempty.
-/
instance : Nonempty (low_lowersemicontinous s f) := by
  use ⊥
  · refine lowerSemicontinuousOn_iff_le_liminf.mpr ?hs.a
    simp
  simp

/-!
Lemma. The lower semicontinuous hull can equivalently be written as a supremum
over the bundled structure `low_lowersemicontinous s f`.
`LowerSemicontinuousHull s f = ⨆ (i : low_lowersemicontinous s f), i.h`.
Purpose: This reformulation packages the data `(h, hs, hzs)` into a structure,
so that the hull is expressed as a clean single `⨆` rather than a triple.
-/
lemma low_lowersemicontinous_eq_structure :
    (LowerSemicontinuousHull s f) =
    ⨆ i : (low_lowersemicontinous s f) , i.h := by
  ext x
  rw[le_antisymm_iff]
  simp [LowerSemicontinuousHull]
  constructor
  · intro h hs hzs
    apply le_iSup_iff.mpr
    intro b hb
    let i : low_lowersemicontinous s f := ⟨h, hs, hzs⟩
    exact LE.le.trans_eq' (hb i) rfl
  intro i
  refine le_iSup_iff.mpr ?h.right.a
  intro b hi
  have ht : i.h x ≤ ⨆ (_ : LowerSemicontinuousOn i.h s), ⨆ (_ : ∀ z ∈ s, i.h z ≤ f z), i.h x :=
    le_iSup₂_of_le i.hs (fun z a ↦ i.hfz z a) (le_refl (i.h x))
  apply le_trans ht (hi i.h)

end low_lowersemicontinous_aux

section lowersemicontinuoushull_eq_self

variable [TopologicalSpace E]

/-!
Theorem. If `f` is lower semicontinuous on `s`, then its lower semicontinuous hull
coincides pointwise with `f`:
`∀ x ∈ s, LowerSemicontinuousHull s f x = f x`.
Purpose: This shows that the hull operator is an idempotent closure operator:
if `f` already has the required property (lower semicontinuity), the hull
does nothing.
-/
theorem lowersemicontinuoushull_eq_self_of_proper {s : Set E}
    {f : E → EReal}
    (hfcl : LowerSemicontinuousOn f s) :
    ∀ x ∈ s, LowerSemicontinuousHull s f x = f x := by
  intro x hx
  rw[le_antisymm_iff]
  constructor
  · exact lowersemicontinuoushull_le_self_of_proper f x hx
  rw[low_lowersemicontinous_eq_structure]
  simp
  rw[le_iSup_iff]
  intro b hb
  let i : low_lowersemicontinous s f := ⟨f, hfcl, by simp⟩
  apply hb i

/-!
Theorem. If `f` is proper on `s` and lower semicontinuous on `s`, then the closure
of `f` coincides pointwise with `f`:
`∀ x ∈ s, (f.closure s) x = f x`.
Purpose: This shows that the closure operator is idempotent on proper, lower
semicontinuous functions: applying `closure` to such a function does not
change its values.
-/
theorem closure_eq_self_of_proper {s : Set E} {f : E → EReal}
    [hsf : ProperFunction s f] (hfcl : LowerSemicontinuousOn f s) :
    ∀ x ∈ s, (f.closure s) x = f x := by
  intro x hx
  simp [Function.closure, hsf]
  exact lowersemicontinuoushull_eq_self_of_proper hfcl x hx

/-!
Theorem. Let `E` be a normed real vector space. Suppose `f : E → EReal` is convex on `univ`
and lower semicontinuous. Then the closure of `f` over `univ` coincides with `f`:
`∀ x, (f.closure univ) x = f x`.
Purpose: This generalizes `closure_eq_self_of_proper` to convex functions without assuming
properness a priori. It shows that the closure of a lower semicontinuous convex function
is itself, even if the function may take `⊥` or `⊤`.
-/
theorem closure_eq_self' [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : E → EReal} (hfcl : LowerSemicontinuous f) (hc : ConvexOn ℝ univ f) :
    ∀ x, (f.closure univ) x = f x := by
  intro x
  by_cases hsf : ProperFunction univ f
  · apply closure_eq_self_of_proper
    · exact lowerSemicontinuousOn_univ_iff.mpr hfcl
    trivial
  simp [Function.closure, hsf]
  by_cases h1 : ∀ x ∈ univ, f x ≠ ⊥
  · simp [h1]
    exact Eq.symm (top_of_ne_bot_of_ne_proper hsf h1 trivial)
  push_neg at h1
  have h' : ∀ x, f x = ⊥ := by
    apply bot_of_exist_bot_of_convex_of_univ
    exact hc
    refine mem_range.mp ?hx.a
    exact mem_range_of_mem_image f univ h1
  simp [h']

/-!
Theorem. Let `E` be a normed real vector space. If `f : E → EReal` is convex on `univ`
and lower semicontinuous, then `f` coincides with its closure over `univ`:
`f = f.closure univ`.
Purpose: This is a convenient global version of `closure_eq_self'`, giving a function-level equality
rather than pointwise. It shows that the closure operator does not change
lower semicontinuous convex functions.
-/
theorem ccp_closure_is_self [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}
    (hfc : ConvexOn ℝ univ f) (hf : LowerSemicontinuous f) :
    f = f.closure univ := by
  ext x
  exact Eq.symm (closure_eq_self' hf hfc x)

end lowersemicontinuoushull_eq_self

section special_function

variable [TopologicalSpace E] [AddCommMonoid E]

/-!
Theorem. The closure of the constant top function `⊤` is itself:
`(⊤ : E → EReal).closure univ = ⊤`.
Purpose: This shows that the closure operator preserves the top function.
Since `⊤` is already “maximal,” the hull/closure does not change it.
-/
theorem top_lowersemicontinuoushull_eq_top : (⊤ : E → EReal).closure univ = ⊤ := by
  simp [Function.closure]
  intro h; exfalso
  obtain h1 := h.2; simp at h1

/-!
Theorem. The closure of the constant bottom function `⊥` is itself:
`(⊥ : E → EReal).closure univ = ⊥`.
Purpose: This shows that the closure operator preserves the bottom function.
Since `⊥` is already minimal, the hull/closure does not change it.
-/
theorem bot_lowersemicontinuoushull_eq_bot : (⊥ : E → EReal).closure univ = ⊥ := by
  simp [Function.closure]
  intro h; exfalso
  obtain h1 := h.1; simp at h1

/-!
Theorem. For any real constant `a`, the closure of the constant function
`fun (_ : E) ↦ (a : EReal)` is itself:
`(fun (_ : E) ↦ (a : EReal)).closure univ = fun (_ : E) ↦ (a : EReal)`.
Purpose: This is a special case of `closure_eq_self_of_proper` for constant functions.
Since constant functions are proper and lower semicontinuous, the closure
does not change their values.
-/
omit [AddCommMonoid E] in
theorem const_lowersemicontinuoushull_eq_const (a : ℝ) : (fun (_ : E) ↦ (a : EReal)).closure univ
    = fun (_ : E) ↦ (a : EReal) := by
  have : ProperFunction univ (fun (_ : E) ↦ (a : EReal)) := RealFun_is_ProperFun
  ext x; rw [closure_eq_self_of_proper]
  · apply LowerSemicontinuous.lowerSemicontinuousOn
    exact lowerSemicontinuous_const
  trivial


end special_function

section LowerSemicontinuous_closed

variable [NormedAddCommGroup E] {s : Set E} {f : E → EReal}
/-!
Theorem. If `f : E → EReal` is lower semicontinuous on a closed set `s`,
then the epigraph of `f` over `s` is closed:
`IsClosed (f.Epi s)`.
Purpose: This establishes the classical result that lower semicontinuity of a function
on a closed domain implies that its epigraph is closed in the product topology.
-/
theorem epi_is_closed_of_lowersemicontinuous
    (hs : IsClosed s) (hf : LowerSemicontinuousOn f s) :
    IsClosed (f.Epi s) := by
  rw [lowerSemicontinuousOn_iff_le_liminf] at hf
  rw [isClosed_iff_forall_filter]
  rintro ⟨x, y⟩ F F_ne h h'
  rw [nhds_prod_eq, le_prod] at h'
  simp [Function.Epi]
  have Fsub : F ≤ comap Prod.fst (𝓟 s) := by
    simp
    refine exists_mem_subset_iff.mp ?_
    simp [Function.Epi] at h
    use {p | p.1 ∈ s ∧ f p.1 ≤ ↑p.2}, h
    exact sep_subset (fun x ↦ s _) fun x ↦ _
  have hxs : x ∈ s := by
   apply IsClosed.mem_of_frequently_of_tendsto hs _ h'.1
   apply Eventually.frequently <| tendsto_principal.mp <| tendsto_iff_comap.mpr Fsub
  exact ⟨hxs,
    calc
    _ ≤ liminf f (𝓝[s] x) := hf x hxs
    _ ≤ liminf f (map Prod.fst F ⊓ 𝓟 s) := by
      apply liminf_le_liminf_of_le _
      simp [nhdsWithin]
      exact inf_le_of_left_le <| map_le_iff_le_comap.mpr <| Tendsto.le_comap h'.1
    _ ≤ liminf (f ∘ Prod.fst) F := by
      rw[Filter.liminf_comp]
      apply liminf_le_liminf_of_le _
      simpa using Fsub
    _ ≤ liminf (fun x => (Prod.snd x).toEReal) F := by
      apply liminf_le_liminf _
      have := (eventually_principal.2 fun (_ : _ × _) ↦ id).filter_mono h
      change ∀ᶠ (a : E × ℝ) in F, (f ∘ Prod.fst) a ≤ ↑a.2
      simp [Function.Epi] at this
      simpa using this.2
    _ ≤ liminf Prod.snd F := by
      rw[Tendsto.liminf_eq h'.2, Tendsto.liminf_eq (tendsto_coe.mpr h'.2)]
    _ = y := EReal.coe_eq_coe_iff.mpr
      <| Tendsto.liminf_eq h'.2
    ⟩


end LowerSemicontinuous_closed



section LowerSemicontinuous_aux_lemma

variable [NormedAddCommGroup E] {s : Set E} {f : E → EReal}

/-!
Theorem. `f` is lower semicontinuous on `s` if and only if
for every `x ∈ s` and every `y < f x`,
there exists an open neighborhood `u` of `x` such that for all `z ∈ u ∩ s`, we have `y < f z`.
Purpose: give a open set characterization of lower semicontinuity.
-/
theorem lowerSemicontinuousOn_iff :
    LowerSemicontinuousOn f s ↔
    ∀ x ∈ s, ∀ y, f x ∈ Ioi y → ∃ u, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ f ⁻¹' Ioi y := by
  simp [LowerSemicontinuousOn, LowerSemicontinuousWithinAt]
  exact forall₃_congr fun a _ c ↦
    imp_congr_right fun _ ↦ ⟨fun hx ↦ mem_nhdsWithin.mp hx,
    fun ⟨u, hu⟩ ↦ eventually_iff_exists_mem.mpr
    ⟨u ∩ s, mem_nhdsWithin.mpr ⟨u, hu.1, hu.2.1 , by simp⟩, fun _ hy => hu.2.2 hy⟩⟩

/-!
Theorem. `f` is lower semicontinuous at `x` within `s` if and only if the restriction of `f` to `s`
is lower semicontinuous at `x`.
Purpose: relate lower semicontinuity within a set to lower semicontinuity of the restricted
function.
-/
variable (f) in
theorem lowerSemicontinuousWithinAt_iff_lowerSemicontinuousAt_restrict {x} (h : x ∈ s) :
    LowerSemicontinuousWithinAt f s x ↔ LowerSemicontinuousAt (s.restrict f) ⟨x, h⟩ := by
  simp [LowerSemicontinuousWithinAt, LowerSemicontinuousAt]
  refine forall₂_congr ?h
  intro a ha
  rw [eventually_nhds_subtype_iff s ⟨x, h⟩ (fun x' => a < f x')]

/-!
Theorem. `f` is lower semicontinuous on `s` if and only if the restriction of `f` to `s`
is lower semicontinuous.
Purpose: relate lower semicontinuity on a set to lower semicontinuity of the restricted function.
-/
theorem lowerSemicontinuousOn_iff_lowerSemicontinuousOn_restrict :
    LowerSemicontinuousOn f s ↔ LowerSemicontinuous (s.restrict f) := by
  rw [LowerSemicontinuousOn, LowerSemicontinuous]
  constructor
  · rintro h ⟨x, xs⟩
    exact (lowerSemicontinuousWithinAt_iff_lowerSemicontinuousAt_restrict f xs).mp (h x xs)
  intro h x xs
  exact (lowerSemicontinuousWithinAt_iff_lowerSemicontinuousAt_restrict f xs).mpr (h ⟨x, xs⟩)

/-!
Theorem. `f` is lower semicontinuous on `s` if and only if
for every `y`, the preimage of the interval `(y, ∞)` under `f`, intersected with `s`,
can be expressed as the intersection of `s` with an open set.
Purpose: show that lower semicontinuity on a set can be characterized by preimages of open sets.
-/
theorem lowerSemicontinuousOn_iff_isOpen_preimage :
    LowerSemicontinuousOn f s ↔
    ∀ y, ∃ u, IsOpen u ∧ f ⁻¹' Ioi y ∩ s = u ∩ s := by
  have : ∀ t, IsOpen (s.restrict f ⁻¹' t) ↔ ∃ u , IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s := by
    intro t
    rw [isOpen_induced_iff, Set.restrict_eq, Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff]
    constructor <;>
      · rintro ⟨u, ou, useq⟩
        exact ⟨u, ou, by simpa only [Set.inter_comm, eq_comm] using useq⟩
  rw [lowerSemicontinuousOn_iff_lowerSemicontinuousOn_restrict,
    lowerSemicontinuous_iff_isOpen_preimage]; simp only [this]

/-!
Theorem. `f` is lower semicontinuous on `s` if and only if
for every `y`, the preimage of the interval `(-∞, y]` under `f`, intersected with `s`,
can be expressed as the intersection of `s` with a closed set.
Purpose: show that lower semicontinuity on a set can be characterized by preimages of closed sets.
-/
theorem lowerSemicontinuousOn_iff_isClosed_preimage :
    LowerSemicontinuousOn f s ↔
    ∀ y, ∃ u, IsClosed u ∧ f ⁻¹' Iic y ∩ s = u ∩ s := by
  have : ∀ t, IsClosed (s.restrict f ⁻¹' t) ↔ ∃ u , IsClosed u ∧ f ⁻¹' t ∩ s = u ∩ s := by
    intro t
    rw [isClosed_induced_iff, Set.restrict_eq, Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff]
    constructor <;>
      · rintro ⟨u, ou, useq⟩
        exact ⟨u, ou, by simpa only [Set.inter_comm, eq_comm] using useq⟩
  rw [lowerSemicontinuousOn_iff_lowerSemicontinuousOn_restrict,
    lowerSemicontinuous_iff_isClosed_preimage]; simp only [this]

/-!
Lemma. If `f` is closed on `s` and `s` is closed,
then `f` is lower semicontinuous on `s`.
Purpose: derive lower semicontinuity from closedness of the function and the domain.
-/
lemma LowerSemicontinuousOn_of_hfcl (hfcl : f.IsClosed s) (hs : IsClosed s) :
    LowerSemicontinuousOn f s := by
  rw [lowerSemicontinuousOn_iff_isClosed_preimage]
  simp [Function.IsClosed, Function.Epi] at hfcl
  intro y
  use ((fun x ↦ (x, y)) ⁻¹' {p | p.1 ∈ s ∧ f p.1 ≤ p.2})
  have hf : IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
    EReal_epi_closed_of_Real_epi_closed hfcl hs
  constructor
  · exact hf.preimage (Continuous.prodMk_left y)
  refine inter_congr_right (fun _ hx ↦ hx.1.2) (fun _ hx ↦ ⟨hx.2, hx.1⟩)

/-!
Lemma. If the epigraph of `f` over `s` is closed,
then `f` is lower semicontinuous on `s`.
Purpose: derive lower semicontinuity from closedness of the epigraph.
-/
lemma LowerSemicontinuousOn_of_hf (hf : IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}) :
    LowerSemicontinuousOn f s := by
  rw [lowerSemicontinuousOn_iff_isClosed_preimage]
  intro y
  -- the closedness of the epigraph gives us the closed set we need
  use ((fun x ↦ (x, y)) ⁻¹' {p | p.1 ∈ s ∧ f p.1 ≤ p.2})
  constructor
  · exact hf.preimage (Continuous.prodMk_left y)
  refine inter_congr_right (fun _ hx ↦ hx.1.2) (fun _ hx ↦ ⟨hx.2,hx.1⟩)

/-!
Lemma. If `s` is closed, then `f` is lower semicontinuous on `s` if and only if
the epigraph of `f` over `s` is closed.
Purpose: establish the equivalence between lower semicontinuity and closedness of the epigraph,
given closedness of the domain.
-/
lemma LowerSemicontinuousOn_iff_IsClosed_epigraph_of_closed (hs : _root_.IsClosed s) :
    LowerSemicontinuousOn f s ↔ IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  constructor
  · rw [EReal_epi_closed_Real_epi_closed]
    intro hfs
    constructor
    · exact hs
    apply epi_is_closed_of_lowersemicontinuous hs hfs
  exact fun a ↦ LowerSemicontinuousOn_of_hf a

/-!
Theorem. The epigraph of the lower semicontinuous hull of `f` on `s` equals
the intersection of the epigraphs of all lower semicontinuous functions that `≤ f` on `s`.
Purpose: characterize the epigraph of the lower semicontinuous hull as an intersection.
-/
theorem lowersemicontinuoushul_intersection_of_closed (s : Set E) (f : E → EReal) :
    {p : E × EReal | p.1 ∈ s ∧ LowerSemicontinuousHull s f p.1 ≤ p.2} =
    ⋂ i : low_lowersemicontinous s f, {p : E × EReal | p.1 ∈ s ∧ i.h p.1 ≤ p.2} := by
  simp [LowerSemicontinuousHull]
  rw [Set.iInter_setOf]
  ext x
  simp
  constructor
  · rintro ⟨hx, hi⟩ i
    exact ⟨hx, hi i.h i.hs i.hfz⟩
  intro hi
  rw [forall_and_left] at hi
  constructor
  · exact hi.1
  intro i his hz
  let ih : low_lowersemicontinous s f := ⟨i, his, hz⟩
  apply hi.2 ih

/-!
Theorem. If `f` is proper on `s`, then the epigraph of the closure of `f` on `s` equals
the intersection of the epigraphs of all lower semicontinuous functions that `≤ f` on `s`.
Purpose: because the closure and the lower semicontinuous hull coincide for proper functions,
we can characterize the epigraph of the closure as an intersection.
-/
theorem closure_intersection_of_closed_of_proper (s : Set E) (f : E → EReal)
    [hsf : ProperFunction s f] :
    {p : E × EReal | p.1 ∈ s ∧ (f.closure s) p.1 ≤ p.2} =
    ⋂ i : low_lowersemicontinous s f, {p : E × EReal | p.1 ∈ s ∧ i.h p.1 ≤ p.2} := by
  simp [Function.closure, hsf]
  exact lowersemicontinuoushul_intersection_of_closed s f

/-!
Theorem. If `s` is closed,
then the epigraph of the lower semicontinuous hull of `f` on `s` is closed.
Purpose: deduce closedness of the epigraph of the lower semicontinuous hull from
closedness of the domain.
-/
theorem lowersemicontinuoushull_isClosed_epigraph_of_closed {s : Set E} (f : E → EReal)
    (hs : IsClosed s) :
    IsClosed {p : E × EReal | p.1 ∈ s ∧ LowerSemicontinuousHull s f p.1 ≤ p.2} := by
  rw [lowersemicontinuoushul_intersection_of_closed]
  apply isClosed_iInter
  intro i
  rw [← LowerSemicontinuousOn_iff_IsClosed_epigraph_of_closed hs]
  apply i.2

/-!
Theorem. If `f` is proper on `s` and `s` is closed,
then the epigraph of the closure of `f` on `s` is closed.
Purpose: because the closure and the lower semicontinuous hull coincide for proper functions,
we can deduce closedness of the epigraph of the closure from closedness of the domain.
-/
theorem closure_isClosed_epigraph_of_closed_of_proper {s : Set E} (f : E → EReal)
    [hsf : ProperFunction s f] (hs : _root_.IsClosed s) :
    IsClosed {p : E × EReal | p.1 ∈ s ∧ (f.closure s) p.1 ≤ p.2} := by
  simp [Function.closure, hsf]
  exact lowersemicontinuoushull_isClosed_epigraph_of_closed f hs

/-!
Theorem. The lower semicontinuous hull of `f` on `s` is lower semicontinuous on `s`.
Purpose: establish lower semicontinuity of the lower semicontinuous hull.
-/
theorem lowersemicontinuoushull_islowersemicontinuous {s : Set E} (f : E → EReal) :
    LowerSemicontinuousOn (LowerSemicontinuousHull s f) s := by
  rw [low_lowersemicontinous_eq_structure]
  apply lowerSemicontinuousOn_iSup
  intro i
  -- Each function in the family is lower semicontinuous on `s`
  have : ∀ h ∈ range fun i : low_lowersemicontinous s f ↦ i.h, LowerSemicontinuousOn h s := by
    rintro h ⟨hy, hr⟩
    simp at hr
    rw [← hr]
    exact hy.hs
  apply this (↑i) i.2

/-!
Theorem. If `s` is closed, then the epigraph of the closure of `f` on `s` is closed.
Purpose: deduce closedness of the epigraph of the closure from closedness of the domain.
-/
theorem closure_isClosed_epigraph_of_closed {s : Set E} (f : E → EReal) (hs : _root_.IsClosed s) :
    IsClosed {p : E × EReal | p.1 ∈ s ∧ (f.closure s) p.1 ≤ p.2} := by
  by_cases hsf : ProperFunction s f
  · exact closure_isClosed_epigraph_of_closed_of_proper f hs
  simp [Function.closure, hsf]
  by_cases hfe : ∃ x ∈ s, f x = ⊥
  · simp [hfe]
    let h : Continuous (Prod.fst (α := E) (β := EReal)) := continuous_fst
    apply IsClosed.preimage h hs
  simp [hfe]
  let h : Continuous (Prod.fst (α := E) (β := EReal)) := continuous_fst
  have := IsClosed.preimage h hs
  exact IsClosed.isClosed_eq this continuousOn_snd continuousOn_const

/-!
Theorem 7.1.
If `s` is closed, then the following are equivalent:
  `f` is lower semicontinuous on `s`;
  the epigraph of `f` over `s` is closed in `E × EReal`;
  the epigraph of `f` over `s` is closed in `E × ℝ`.
Purpose: show the equivalence between lower semicontinuity and closedness of the epigraph.
-/
theorem lowerSemicontinuousOn_tfae_of_closed (hs : _root_.IsClosed s) :
  [LowerSemicontinuousOn f s,
  IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2},
  IsClosed {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}].TFAE :=  by
  tfae_have 1 ↔ 2 := LowerSemicontinuousOn_iff_IsClosed_epigraph_of_closed hs
  tfae_have 2 ↔ 3 := by
    constructor
    · exact fun a ↦ Real_epi_closed_of_EReal_epi_closed a
    exact fun a ↦ EReal_epi_closed_of_Real_epi_closed a hs
  tfae_finish

/-!
Theorem. If `f` is lower semicontinuous on `s` and `g` equals `f` on `s₁ ⊆ s`,
then `g` is lower semicontinuous on `s₁`.
Purpose: show that lower semicontinuity is preserved under pointwise equality on subsets.
-/
theorem lowerSemicontinuousOn.congr_mono {α : Type*} {β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [Preorder β] {f g : α → β} {s s₁ : Set α} (h : LowerSemicontinuousOn f s)
    (h' : EqOn g f s₁) (h₁ : s₁ ⊆ s) :
    LowerSemicontinuousOn g s₁ := by
  intro x hx
  unfold LowerSemicontinuousWithinAt
  -- A : LowerSemicontinuousWithinAt f s₁ x
  have A := (h x (h₁ hx)).mono h₁
  unfold LowerSemicontinuousWithinAt at A
  rw [← h' hx] at A
  intro y hy
  apply Filter.Eventually.congr (A y hy)
  refine eventually_nhdsWithin_of_forall ?h
  intro z hz
  rw [h' hz]

/-!
Theorem. If `f` is lower semicontinuous on `s` and `g` equals `f` on `s`,
then `g` is lower semicontinuous on `s`.
Purpose: show that lower semicontinuity is preserved under pointwise equality.
-/
theorem lowerSemicontinuousOn.congr {α : Type*} {β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [Preorder β] {f g : α → β} {s : Set α} (h : LowerSemicontinuousOn f s)
    (h' : EqOn g f s) :
    LowerSemicontinuousOn g s :=
  lowerSemicontinuousOn.congr_mono h h' (fun _ a ↦ a)

/-!
Theorem. The following are equivalent:
  `f` is lower semicontinuous on `s`;
  `∀ x ∈ s`, `f x` is less than or equal to the limit inferior of `f` near `x` within `s`;
  `∀ x ∈ s` and `∀ y < f x`, there exists an open neighborhood `u` of `x` such that
  for all `z ∈ u ∩ s`, we have `y < f z`;
  `∀ y`, the preimage of the interval `(y, ∞)` under `f`, intersected with `s`,
  can be expressed as the intersection of `s` with an open set;
  `∀ y`, the preimage of the interval `(-∞, y]` under `f`, intersected with `s`,
  can be expressed as the intersection of `s` with a closed set;
  `∀ x ∈ s`, the lower semicontinuous hull of `f` equals `f` at `x`.
Purpose: give several equivalent characterizations of lower semicontinuity on a set.
-/
theorem lowerSemicontinuousOn_tfae :
    [LowerSemicontinuousOn f s,
    ∀ x ∈ s, f x ≤ Filter.liminf f (nhdsWithin x s),
    ∀ x ∈ s, ∀ y, f x ∈ Ioi y → ∃ u, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ f ⁻¹' Ioi y,
    ∀ y, ∃ u, IsOpen u ∧ f ⁻¹' Ioi y ∩ s = u ∩ s,
    ∀ y, ∃ u, IsClosed u ∧ f ⁻¹' Iic y ∩ s = u ∩ s,
    ∀ x ∈ s, (f.LowerSemicontinuousHull s) x = f x].TFAE := by
  tfae_have 1 ↔ 2 := lowerSemicontinuousOn_iff_le_liminf
  tfae_have 1 ↔ 3 := lowerSemicontinuousOn_iff
  tfae_have 1 ↔ 4 := lowerSemicontinuousOn_iff_isOpen_preimage
  tfae_have 1 ↔ 5 := lowerSemicontinuousOn_iff_isClosed_preimage
  tfae_have 1 ↔ 6 := ⟨fun a x a_1 ↦ lowersemicontinuoushull_eq_self_of_proper a x a_1,
    by
      intro hx
      apply lowerSemicontinuousOn.congr
      apply lowersemicontinuoushull_islowersemicontinuous f
      exact EqOn.symm hx
    ⟩
  tfae_finish

/-!
Theorem. If `f` is lower semicontinuous on `s`,
then for any constant `c`, the function `x ↦ f x - c` is lower semicontinuous on `s`.
Purpose: show that lower semicontinuity is preserved under subtraction of a constant.
-/
theorem lowerSemicontinuousOn_sub_const (hfs : LowerSemicontinuousOn f s) (c : ℝ) :
    LowerSemicontinuousOn (fun x => f x - c) s := by
  let g := fun x : EReal => x - c
  change LowerSemicontinuousOn (g ∘ f) s
  apply Continuous.comp_lowerSemicontinuousOn
  · exact EReal.continuous_sub c
  · exact hfs
  apply Monotone.add_const
  exact fun ⦃a b⦄ a ↦ a

end LowerSemicontinuous_aux_lemma

section closure_closed

variable [NormedAddCommGroup E] {s : Set E} {f : E → EReal}

/-!
Theorem. If `f` is proper on `s` and `s` is closed,
then the epigraph of the closure of `f` on `s` is closed.
Purpose: deduce closedness of the epigraph of the closure from properness of the function and
closedness of the domain.
-/
theorem epi_is_closed_of_closure (f) [hsf : ProperFunction s f] (hs : IsClosed s) :
    IsClosed ((f.closure s).Epi s) := by
  simp [Function.closure, hsf]
  rw [low_lowersemicontinous_eq_structure, point_sup_iff_epi_inter_of_nonempty']
  exact isClosed_iInter fun i => (epi_is_closed_of_lowersemicontinuous hs i.2)

/-!
Theorem. If `f` is proper on `s` and `s` is closed, then the closure of `f` on `s` is closed.
Purpose: deduce closedness of the closure from properness of the function and
closedness of the domain.
-/
theorem closure_is_closed_of_proper (f) [hsf : ProperFunction s f] (hs : IsClosed s) :
    (f.closure s).IsClosed s := by
  simp [Function.IsClosed]
  exact epi_is_closed_of_closure f hs

/-!
Theorem. If `s` is closed, then the closure of `f` on `s` is closed.
Purpose: deduce closedness of the closure from closedness of the domain.
-/
theorem closure_is_closed (f : E → EReal) (hs : IsClosed s) :
    (f.closure s).IsClosed s := by
  by_cases hsf : ProperFunction s f
  · exact closure_is_closed_of_proper f hs
  simp [Function.closure, hsf]
  by_cases hf : ∃ x ∈ s, f x = ⊥
  · simp [hf]; simp [Function.IsClosed]
    have h1 : Epi ⊥ s = s ×ˢ (univ : Set ℝ) := by
      ext ⟨x, _⟩
      simp [Function.Epi]
    rw [h1]
    apply IsClosed.prod hs isClosed_univ
  simp [hf]; simp [Function.IsClosed]
  have h' : Epi ⊤ s = ∅ := by
    ext ⟨x, _⟩; simp [Function.Epi]
  rw [h']
  exact isClosed_empty

end closure_closed

section finite
/-!
Theorem. If `f` is lower semicontinuous on `s` and `f` is finite on `s`,
then the closure of `f` on `s` is finite on `s`.
Purpose: show that the closure preserves finiteness of the lower semicontinuous function.
-/
theorem cl_finite_of_finite [TopologicalSpace E] {f : E → EReal} {s : Set E}
    (hfs : LowerSemicontinuousOn f s) (hf : ∀ x ∈ s, ⊥ < f x ∧ f x < ⊤) :
    ∀ x ∈ s, ⊥ < f.closure s x ∧ f.closure s x < ⊤ := by
  intro x hx
  letI hsf : ProperFunction s f := instProperFunctionOfForallMemSetAndLtERealBotTop hf
  constructor
  · simpa [closure_eq_self_of_proper hfs _ hx] using (hf x hx).1
  calc _
    _ ≤ f x := closure_le_self_of_proper s f x hx
    _ < _ := (hf x hx).2

end finite

section cl_epi_eq_epi_cl

section closure_epi

variable [NormedAddCommGroup E] {s : Set E} {f : E → EReal}
/-!
Theorem. If `s` is closed, then the function `closure_epi s f` is lower semicontinuous on `s`.
Purpose: establish the lower semicontinuity of `closure_epi s f` on closed domain.
-/
theorem closure_epi_lowersemicontinuoushull (hs : IsClosed s) :
    LowerSemicontinuousOn (closure_epi s f) s := by
  refine LowerSemicontinuousOn_of_hf ?hf
  rw [epi_closure_epi_eq_cl_epi hs]
  exact isClosed_closure

/-!
Theorem. If `s` is closed and `f` is lower semicontinuous on `s`,
then the epigraph of `f` on `s` equals the closure of the epigraph of `f` on `s`.
Purpose: for lower semicontinuous functions on closed domains, the epigraph is already closed,
so it equals its closure.
-/
theorem epi_eq_closure (hfs : LowerSemicontinuousOn f s) (hs : IsClosed s) :
    {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} = closure {p | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  refine Eq.symm (IsClosed.closure_eq ?h)
  exact (LowerSemicontinuousOn_iff_IsClosed_epigraph_of_closed hs).mp hfs

/-!
Theorem. If `s` is closed, then for any `x ∈ s`, the value of `closure_epi s f x` equals
the value of the lower semicontinuous hull of `f` on `s` at `x`.
Purpose: relate `closure_epi` to the lower semicontinuous hull on closed domain.
-/
theorem closure_epi_eq_cl_f (hs : IsClosed s) :
    ∀ x ∈ s, closure_epi s f x = (f.LowerSemicontinuousHull s) x := by
  intro x hx
  rw [le_antisymm_iff]
  constructor
  · rw [low_lowersemicontinous_eq_structure]
    rw [iSup_apply, le_iSup_iff]
    intro b hi
    let i : low_lowersemicontinous s f :=
      ⟨closure_epi s f, closure_epi_lowersemicontinuoushull hs, closure_epi_le_f f ⟩
    apply hi i
  simp [LowerSemicontinuousHull]
  intro i his hiz
  have : ∀ x ∈ s, i x ≤ closure_epi s f x :=by
    rw [le_iff_epi_sub, epi_closure_epi_eq_cl_epi hs, epi_eq_closure his hs]
    refine closure_mono ?h
    rwa [← le_iff_epi_sub]
  exact this x hx

/-!
Theorem. If `s` is closed, then the closure of the epigraph of `f` on `s` equals
the epigraph of the lower semicontinuous hull of `f` on `s`.
Purpose: relate the closure of the epigraph to the epigraph of the lower semicontinuous hull
on closed domain.
-/
theorem closure_epi_eq_epi_closure (hs : IsClosed s) :
    closure {(x, y) : E × EReal | x ∈ s ∧ f x ≤ y} =
    {(x, y) : E × EReal | x ∈ s ∧ (f.LowerSemicontinuousHull s) x ≤ y} := by
  rw [← epi_closure_epi_eq_cl_epi hs]
  ext x
  simp
  intro hx
  rwa [closure_epi_eq_cl_f hs]

/-!
Theorem. If `f` is proper on `s` and `s` is closed, then the closure of the epigraph of `f` on `s`
equals the epigraph of the closure of `f` on `s`.
Purpose: relate the closure of the epigraph to the epigraph of the closure, under properness of
the function and closedness of the domain.
-/
theorem closure_epi_eq_epi_closure' [hsf : ProperFunction s f] (hs : IsClosed s) :
    closure {(x, y) : E × EReal | x ∈ s ∧ f x ≤ y} =
    {(x, y) : E × EReal | x ∈ s ∧ Function.closure f s x ≤ y} := by
  rw [closure_epi_eq_epi_closure]
  · simp [Function.closure, hsf]
  trivial

end closure_epi

section Real
/-
This section proves that the epigraph of the closure of a function equals
the closure of the epigraph of the function (real version).
-/
variable [NormedAddCommGroup E] {s : Set E} {f : E → EReal}

def topline (s : Set E) := {(x, y) : E × EReal | x ∈ s ∧ y = ⊤}

def botline (s : Set E) := {(x, y) : E × EReal | x ∈ s ∧ y = ⊥}

/-!
Lemma. The union of the epigraph of `f` on `s` and the top line equals
the set of points `(x, y)` such that `x ∈ s` and `f x ≤ y` minus the bottom line.
Purpose: the only difference between the epigraphs in real version and EReal version
is the topline and botline.
-/
lemma epi_real_cup_topline_eq_epi_ereal_diff_botline (s : Set α) (f : α → EReal) :
    (Prod.map id Real.toEReal '' f.Epi s) ∪ (topline s) =
    {(x, y) : α × EReal | x ∈ s ∧ f x ≤ y} \ (botline s):= by
  ext x
  simp [Epi]
  constructor
  · intro hx
    rcases hx with ⟨a, b, hab⟩ | hx
    · simp_rw [← hab.2]
      exact ⟨hab.1, by simp [botline]⟩
    simp [topline] at hx
    simp [hx.2]
    refine ⟨hx.1, ?_⟩
    simp [botline]
    intro _
    simp [hx.2]
  intro hx
  by_cases hx2 : x.2 = ⊤
  · right
    simpa [topline] using ⟨hx.1.1, hx2⟩
  left
  use x.1, x.2.toReal
  simp [botline] at hx
  simpa [coe_toReal hx2 (hx.2 hx.1.1)] using hx.1

/-!
Lemma. If `(x, y)` lies in the closure of the epigraph of `f` on `s`, with `y ∈ ℝ`,
then `(x, y.toReal)` lies in the image of the closure of the epigraph of `f` on `s` under
`Prod.map id Real.toEReal`.
Purpose: relate closure membership in the EReal version to the Real version,
excluding the bottom and top lines.
-/
lemma cl_epi_real_of_netop_of_nebot_of_in_cl_epi (x : E × EReal)
    (hx : x ∈ closure {(x, y) : E × EReal | x ∈ s ∧ f x ≤ y}) (hxbot : x.2 ≠ ⊥) (hxtop : x.2 ≠ ⊤) :
    x ∈ Prod.map id Real.toEReal '' closure (Epi f s) := by
  simp [mem_closure_iff_seq_limit] at hx
  rcases hx with ⟨w, hw, h⟩
  simp [mem_closure_iff_seq_limit]
  use x.1, x.2.toReal
  simp [Prod.tendsto_iff] at h
  rw [← coe_toReal hxtop hxbot] at h
  have ⟨N, hN⟩ := Eventually.exists_forall_of_atTop <| eventually_coe_of_Real h.2
  constructor
  · use (Prod.map id EReal.toReal) ∘ w ∘ (fun n => n + N)
    simp
    constructor
    · intro n
      simpa [Epi, hN (b := n + N) (by simp)] using hw (n + N)
    simp [Prod.tendsto_iff]
    constructor
    · have := h.1
      rwa [← tendsto_add_atTop_iff_nat N] at this
    apply tendsto_coe_of_Real
    have := h.2
    rwa [← tendsto_add_atTop_iff_nat N] at this
  rw [coe_toReal hxtop hxbot]

/-!
Theorem. The union of the image of the closure of the epigraph of `f` on `s` under
`Prod.map id Real.toEReal` and the topline of the closure of `s` is contained in
the closure of the set of points `(x, y)` such that `x ∈ s` and `f x ≤ y`
minus the botline of the closure of `s`.
Purpose: proof of one direction of the equality relating the closure of the epigraph
in EReal version to the Real version.
-/
theorem cl_cup_top_cl_sub_cl_epi_diff_bot (s : Set E) (f : E → EReal) :
    (Prod.map id Real.toEReal '' closure (f.Epi s)) ∪ (topline (closure s))
    ⊆ closure {(x, y) : E × EReal | x ∈ s ∧ f x ≤ y} \ (botline (closure s)) := by
  intro x hx
  simp [mem_closure_iff_seq_limit] at *
  rcases hx with ⟨a, b, ⟨w, hw⟩, hx⟩ | hx
  · constructor
    · use (Prod.map id Real.toEReal) ∘ w
      constructor
      · intro n
        simpa using hw.1 n
      rw [← hx]
      change Tendsto (Prod.map id Real.toEReal ∘ w) atTop (𝓝 (Prod.map id Real.toEReal (a, b)))
      rw [← IsOpenEmbedding.tendsto_nhds_iff]
      · exact hw.2
      exact IsOpenEmbedding.prodMap IsOpenEmbedding.id isOpenEmbedding_coe
    simp [botline]
    intro _
    simp [← hx]
  simp [topline] at hx
  constructor
  · simp [mem_closure_iff_seq_limit] at hx
    rcases hx with ⟨⟨w, hw⟩, hx2⟩
    use (fun n => (w n, ⊤))
    constructor
    · intro n
      simpa using hw.1 n
    rw [Prod.tendsto_iff]
    simp [hx2, hw.2]
  simp [botline, hx.2]

/-!
Theorem. The closure of the `EReal` epigraph without the bottom line equals
the union of the closure of the `Real` epigraph and the top line.
Purpose: relate the closure of the epigraph in EReal version to the Real version.
-/
theorem cl_epi_diff_bot_eq_cl_cup_top_cl :
    closure {(x, y) : E × EReal | x ∈ s ∧ f x ≤ y} \ (botline (closure s))
    = (Prod.map id Real.toEReal '' closure (f.Epi s)) ∪ (topline (closure s))  := by
  rw [Subset.antisymm_iff]
  refine ⟨?_, cl_cup_top_cl_sub_cl_epi_diff_bot s f⟩
  intro x hx
  have hxold := hx.1
  simp [mem_closure_iff_seq_limit] at hx
  rcases hx with ⟨⟨w, hw, h⟩, hx⟩
  simp [botline] at hx
  have hx1 : x.1 ∈ closure s := by
    rw [mem_closure_iff_seq_limit]
    use Prod.fst ∘ w
    simpa using ⟨fun n ↦ (hw n).1, Tendsto.fst_nhds h⟩
  by_cases hx2 : x.2 = ⊤
  · right
    simpa [topline] using ⟨hx1, hx2⟩
  left
  exact cl_epi_real_of_netop_of_nebot_of_in_cl_epi x hxold (hx hx1) hx2

/-!
Lemma. If `s` is closed, then the union of the image of the epigraph of the lower semicontinuous
hull of `f` on `s` under `Prod.map id Real.toEReal` and the topline of `s` equals
the union of the image of the closure of the epigraph of `f` on `s` under the same map
and the topline of `s`.
Purpose: relate the epigraph of the lower semicontinuous hull to the closure of the epigraph
when both are embedded into `EReal`, under closedness of the domain.
-/
lemma epi_real_cl_cup_topline_eq_cl_epi_real (f : E → EReal) (hs : IsClosed s) :
    (Prod.map id Real.toEReal '' (f.LowerSemicontinuousHull s).Epi s) ∪ (topline s) =
    (Prod.map id Real.toEReal '' closure (f.Epi s)) ∪ (topline s) := by
  rw [epi_real_cup_topline_eq_epi_ereal_diff_botline s _, ← closure_epi_eq_epi_closure hs]
  nth_rw 2 4 [← closure_eq_iff_isClosed.mpr hs]
  apply cl_epi_diff_bot_eq_cl_cup_top_cl

/-!
Lemma. The intersection of any set `α × ℝ` and the topline of set `α` is empty.
Purpose: show that the topline has no intersection with Real-valued points.
-/
lemma aux_topline_inter_eq_empty (s : Set α) (t : Set (α × ℝ)) :
    (Prod.map id Real.toEReal '' t) ∩ (topline s) = ∅ := by
  by_contra!
  simp [topline] at this

/-!
Lemma. If the union of two sets `s ∪ a` equals `t ∪ a`, and both `s` and `t`
are disjoint from `a`, then `s` equals `t`.
Purpose: a set-theoretic lemma to help prove the main theorem.
-/
lemma aux_set_eq_of_cup {s t a : Set α} (h : s ∪ a = t ∪ a) (hs : s ∩ a = ∅) (ht : t ∩ a = ∅) :
    s = t := by
  simp [← disjoint_iff_inter_eq_empty, Set.union_eq_union_iff_right] at *
  have h1:= Disjoint.subset_left_of_subset_union h.1 hs
  have h2:= Disjoint.subset_left_of_subset_union h.2 ht
  exact Subset.antisymm h1 h2

/-!
Lemma. If `s` is closed, then the epigraph of the lower semicontinuous hull of `f` on `s` equals
the closure of the epigraph of `f` on `s`.
Purpose: relate the epigraph of the lower semicontinuous hull to the closure of the epigraph
when both are embedded into `EReal`, under closedness of the domain.
-/
lemma epi_real_cl_eq_cl_epi_real_aux (f : E → EReal) (hs : IsClosed s) :
    (Prod.map id Real.toEReal '' (f.LowerSemicontinuousHull s).Epi s) =
    (Prod.map id Real.toEReal '' closure (f.Epi s)) := by
  have := epi_real_cl_cup_topline_eq_cl_epi_real f hs
  have h1 := aux_topline_inter_eq_empty s (Epi (f.LowerSemicontinuousHull s) s)
  have h2 := aux_topline_inter_eq_empty s (closure (Epi f s))
  apply aux_set_eq_of_cup this h1 h2

/-!
Theorem. If `s` is closed, then the closure of the epigraph of `f` on `s` equals
the epigraph of the lower semicontinuous hull of `f` on `s`.
Purpose: relate the closure of the epigraph to the epigraph of the lower semicontinuous hull
on closed domain.
-/
theorem closure_epi_real_eq_epi_real_closure (f : E → EReal) (hs : IsClosed s) :
    closure (f.Epi s) = (f.LowerSemicontinuousHull s).Epi s := by
  rw [← Set.image_eq_image (f := Prod.map id Real.toEReal)]
  · simp [epi_real_cl_eq_cl_epi_real_aux f hs]
  refine Injective.prodMap (fun _ _ a ↦ a) coe_injective

/-!
Theorem. If `s` is closed and `f` is a proper function,
then the closure of the epigraph of `f` equals the epigraph of the closure of `f` on `s`.
Purpose: relate the closure of the epigraph to the epigraph of the closure,
under properness of the function and closedness of the domain.
-/
theorem closure_epi_real_eq_epi_real_closure' (f : E → EReal) [hsf : ProperFunction s f]
    (hs : IsClosed s) :
    closure (f.Epi s) = (f.closure s).Epi s := by
  rw [closure_epi_real_eq_epi_real_closure]
  · simp [Function.closure, hsf]
  trivial

end Real

end cl_epi_eq_epi_cl

section cl_liminf
/-
This section mainly proves: (cl f) x = liminf_{y → x} f (y)
-/
variable [NormedAddCommGroup E]

/-!
Theorem. If `f` is proper on `univ`, then the closure of `f` on `univ` is lower semicontinuous.
Purpose: establish the lower semicontinuity of the closure of `proper` functions.
-/
theorem univ_closure_semicontinuous_of_proper (f : E → EReal) [hp : ProperFunction univ f] :
    LowerSemicontinuous (Function.closure f univ) := by
  rw [lowerSemicontinuous_iff_isClosed_epigraph]
  have : {p : E × EReal | Function.closure f univ p.1 ≤ p.2}
      = {(x, y) : E × EReal | x ∈ univ ∧ LowerSemicontinuousHull univ f x ≤ y} := by
    ext x; simp [Function.closure, hp]
  rw [this, ← closure_epi_eq_epi_closure isClosed_univ]
  apply isClosed_closure

/-!
Theorem. The closure of `f` is lower semicontinuous.
Purpose: establish the lower semicontinuity of the closure of `any` function.
-/
theorem univ_closure_semicontinuous (f : E → EReal) :
    LowerSemicontinuous (Function.closure f univ) := by
  by_cases hp : ProperFunction univ f
  · apply univ_closure_semicontinuous_of_proper f
  simp [Function.closure, hp]
  by_cases h : ∃ x ∈ univ, f x = ⊥
  · rw [if_pos h]
    refine Continuous.lowerSemicontinuous ?_
    exact continuous_of_const fun x ↦ congrFun rfl
  rw [if_neg h]
  refine Continuous.lowerSemicontinuous ?_
  exact continuous_of_const fun x ↦ congrFun rfl

/-!
Theorem. For any `x`, the value of the closure of `f` on `univ` at `x` is less than or equal to
the liminf of `f` as `y` approaches `x`.
Purpose: proof of one direction of the equality relating closure and liminf.
-/
theorem closure_le_liminf (f : E → EReal) (x) : Function.closure f univ x ≤ liminf f (𝓝 x) := by
  calc _
    _ ≤ liminf (Function.closure f univ) (𝓝 x) := by
      refine LowerSemicontinuous.le_liminf ?_ x
      exact univ_closure_semicontinuous f
    _ ≤  _ := by
      have : Function.closure f univ ≤ f := by
        rw [@Pi.le_def]
        intro z
        exact closure_le_self univ f z trivial
      apply Filter.liminf_le_liminf
      · exact Eventually.of_forall this
      repeat isBoundedDefault

/-!
Theorem. For any `x`, the liminf of `f` at `x` is less than or equal to
the value of the closure of `f` on `univ` at `x`.
Purpose: proof of the other direction of the equality relating closure and liminf.
-/
theorem liminf_le_closure (f : E → EReal) [hf : ProperFunction univ f] (x) :
    liminf f (𝓝 x) ≤ Function.closure f univ x  := by
  simp [Function.closure, hf]
  rw [← closure_epi_eq_cl_f (by simp) x (by simp), closure_epi, ← le_of_forall_lt_iff_le]
  simp
  intro z hz
  refine liminf_le_of_frequently_le' ?h
  rw [sInf_lt_iff] at hz
  rcases hz with ⟨u, hu, huz⟩
  simp at *
  rw [mem_closure_iff_seq_limit] at hu
  rcases hu with ⟨w, hwn, hlim⟩
  rw [frequently_iff_seq_frequently]
  use (fun n => (w n).1)
  rw [Prod.tendsto_iff] at hlim
  simp at *
  constructor
  · exact hlim.1
  have ⟨N, hN⟩ := tendsto_atTop_nhds.1 hlim.2 (Iio z) (by simp [huz]) isOpen_Iio
  rw [frequently_atTop]
  intro a
  use a + N
  constructor
  · simp
  simp at *
  exact le_trans (hwn (a + N)) <| le_of_lt (hN _ (by simp))

/-!
Theorem. For any `x`, if `f` is proper on `univ`, then the value of the closure of `f` at `x`
equals the liminf of `f` as `y` approaches `x`.
Purpose: the main equality relating closure and liminf.
-/
theorem closure_eq_liminf (f : E → EReal) [hf : ProperFunction univ f] (x) :
    Function.closure f univ x = liminf f (𝓝 x) := by
  simpa [le_antisymm_iff] using ⟨closure_le_liminf f x, liminf_le_closure f x⟩

end cl_liminf

section cl_mono

variable [NormedAddCommGroup E]

/-!
Lemma. For two proper functions `f₁, f₂` and a closed set `s`,
if for any `x ∈ s, f₁ x ≤ f₂ x`, then for any `x ∈ s, cl(f₁) x ≤ cl(f₂) x`.
Purpose: a special case of `f_mono_closure_mono` where both `f₁` and `f₂` are proper.
-/
lemma f_mono_closure_mono_of_proper {f₁ f₂ : E → EReal}
  [hsf1 : ProperFunction s f₁] [hsf2 : ProperFunction s f₂]
  (mono : ∀ x ∈ s, f₁ x ≤ f₂ x) (hs : IsClosed s) :
  ∀ x ∈ s, f₁.closure s x ≤ f₂.closure s x := by
  rw [le_iff_epi_sub]; repeat rw [← closure_epi_eq_epi_closure' hs]
  exact closure_mono (fun x hx => ⟨hx.1, le_trans (mono x.1 hx.1) hx.2⟩)

/-!
For proper function `f₁`, extended real valued function `f₂`, and a closed set `s`,
if for any `x ∈ s, f₁ x ≤ f₂ x`, then for any `x ∈ s, cl(f₁) x ≤ cl(f₂) x`.
Purpose: a special case of `f_mono_closure_mono` where `f₁` is proper.
-/
lemma f_mono_closure_mono_pre_proper {f₁ f₂ : E → EReal} [hsf1 : ProperFunction s f₁]
  (mono : ∀ x ∈ s, f₁ x ≤ f₂ x) (hs : IsClosed s) : ∀ x ∈ s, f₁.closure s x ≤ f₂.closure s x := by
  intro x xs
  by_cases hsf : ProperFunction s f₂
  · exact f_mono_closure_mono_of_proper mono hs x xs
  simp [Function.closure, hsf]
  by_cases hf : ∃ x ∈ s, f₂ x = ⊥
  · rcases hf with ⟨x, hx, hfx⟩
    specialize mono x hx
    exfalso
    have : f₁ x = ⊥ := by
      rw [hfx] at mono
      exact le_bot_iff.mp mono
    have gtbot := hsf1.1 x hx
    rw [this] at gtbot
    exact (lt_self_iff_false ⊥).mp gtbot
  simp [hf]

/-!
Theorem. For any extended real-value function `f₁, f₂` and a closed set `s`,
if for any `x ∈ s, f₁ x ≤ f₂ x`, then for any `x ∈ s, cl(f₁) x ≤ cl(f₂) x`.
Purpose: a statement on the top of Page 53.
-/
theorem f_mono_closure_mono
   {f₁ f₂ : E → EReal}
   (mono : ∀ x ∈ s, f₁ x ≤ f₂ x) (hs : IsClosed s) :
    ∀ x ∈ s, f₁.closure s x ≤ f₂.closure s x := by
  by_cases hs' : s = ∅
  ·  simp [hs']
  intro x xs
  by_cases hsf : ProperFunction s f₁
  · exact f_mono_closure_mono_pre_proper mono hs x xs
  simp [Function.closure, hsf]
  by_cases hf : ∃ x ∈ s, f₁ x = ⊥
  · simp [hf]
  simp [hf]; push_neg at hf
  have xsf1x : ∀ x ∈ s, f₁ x = ⊤ := fun x a ↦ top_of_ne_bot_of_ne_proper hsf hf a
  have xsf2x : ∀ x ∈ s, f₂ x = ⊤ := by
    intro z hz; specialize mono z hz
    simp [xsf1x z hz] at mono; exact mono
  have : ¬ ∃ x ∈ s, f₂ x = ⊥ := by
    simpa using fun x a ↦ ne_bot_of_le_ne_bot (hf x a) (mono x a)
  simp [neg_proper_of_top xsf2x hs', this]

/-!
Theorem. For any extended real-value function `f₁, f₂`,
if for any `x ∈ univ, f₁ x ≤ f₂ x`, then for any `x ∈ s, cl(f₁) x ≤ cl(f₂) x`.
Purpose: a special case of f_mono_closure_mono on univ.
-/
theorem f_mono_closure_mono_univ {f₁ f₂ : E → EReal}
  (mono : f₁ ≤ f₂) : f₁.closure univ ≤ f₂.closure univ := by
  intro x; apply f_mono_closure_mono (by simpa using mono) (by simp); simp

end cl_mono
