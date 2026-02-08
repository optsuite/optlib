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
import Reaslib.Basic.ProperFunction

/-!
# Epigraph of a convex function
This file develops the basic theory of epigraphs of extended-real–valued functions.
It introduces the definition of the epigraph, studies how intersections of epigraphs
correspond to pointwise suprema of functions, and establishes equivalences between
these set-theoretic and functional characterizations.

Furthermore, the file proves classical results linking convexity of a function with
convexity of its epigraph, and conversely shows that convex epigraphs imply convexity
of the underlying function on its effective domain. Special attention is given to cases
where the function attains `-∞`, ensuring the convexity inequalities remain valid.

Finally, the file connects closedness of real epigraphs with lower semicontinuity in
the extended-real setting, providing the foundations needed for later analysis of
closed convex functions.

## References

* Chapter 4 of [R. T. Rockafellar, *Convex Analysis*][rockafellar1970].
-/

open Filter BigOperators Set Topology Function Module EReal Inner Pointwise
open scoped Pointwise
/-!
Definition. Epigraph of a EReal function `f` over a set `s` is the region
above the graph of `f` on `s`.
-/
def Function.Epi (f : E → EReal) (s : Set E) : Set (E × ℝ) :=
  {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}


section sup_aux

/-!
Lemma. Given a function `f : ι₁ → ι₂ → α` over a complete lattice `α`
and a predicate `h : ι₁ → ι₂ → Prop`, if `h i j` holds for some `i, j`,
then `f i j` is less than or equal to the triple supremum of `f` over
all `i, j` satisfying `h`.
Purpose: provide a convenient inequality for manipulating nested suprema
(over two indices and a predicate), which is useful in proofs involving
upper bounds in complete lattices.
-/
lemma le_triSup {ι₁ ι₂ : Type*} [CompleteLattice α]
     (f : ι₁ → ι₂ → α) (i : ι₁) (j : ι₂) (h : ι₁ → ι₂ → Prop) (hij : h i j) :
    f i j ≤ ⨆ i, ⨆ j, ⨆ (_ : h i j), f i j := by
  apply le_iSup₂_of_le i j
  exact le_iSup_iff.mpr fun b a ↦ a hij

variable {s : Set E} {f : E → EReal}

variable {ι : Type*} (g : ι → E → EReal)

/-!
Theorem. The epigraph of a function `f` over a set `s` equals the intersection
of the epigraphs of a family of functions `(g i)` if and only if, for all `x ∈ s`
and `w ∈ ℝ`, the inequality `f x ≤ w` holds exactly when `g i x ≤ w` holds for all `i`.
Purpose: provide a pointwise characterization of when an epigraph is the intersection
of other epigraphs, which is useful for reasoning about function inequalities and
intersections in convex and topological analysis.
-/
theorem epi_inter_iff_forall :
    f.Epi s = ⋂ i, ((g i).Epi s) ↔
    (∀ (x : E) (w : ℝ), (x ∈ s ∧ f x ≤ w ↔ (∀ i, x ∈ s ∧ g i x ≤ w))) := by
  simp [Function.Epi]
  rw[Set.iInter_setOf, Set.ext_iff]
  simp

/-!
Lemma. Suppose `ι` is nonempty. Then for `x ∈ E` and `w ∈ ℝ`,
the equivalence
    x ∈ s ∧ f x ≤ w ↔ ∀ i, x ∈ s ∧ g i x ≤ w
is equivalent to
    ∀ (_ : x ∈ s), f x ≤ w ↔ ∀ i, g i x ≤ w
Purpose: simplify pointwise statements involving a conjunction with membership
in a set `s`, allowing one to move `x ∈ s` outside of the universal quantifier.
This is useful when working with intersections of epigraphs or pointwise inequalities.
-/
lemma forall_in_and_iff_forall_in [Nonempty ι] (x : E) (w : ℝ) :
    (x ∈ s ∧ f x ≤ w ↔ (∀ i, x ∈ s ∧ g i x ≤ w)) ↔
    ∀ (_ : x ∈ s), (f x ≤ w ↔ (∀ i, g i x ≤ w)) := by
  rw[forall_and_left,and_congr_right_iff]

/-!
Lemma. Suppose `ι` is nonempty. Then the statement
    ∀ (x : E) (w : ℝ), x ∈ s ∧ f x ≤ w ↔ ∀ i, x ∈ s ∧ g i x ≤ w
is equivalent to
    ∀ (x : E) (w : ℝ) (_ : x ∈ s), f x ≤ w ↔ ∀ i, g i x ≤ w
Purpose: lift the simplification of set membership in conjunctions
(from `forall_in_and_iff_forall_in`) to the level of universal quantification
over all `x` and `w`. This provides a cleaner formulation of
epigraph intersection conditions.
-/
lemma forall_in_and_iff_forall_in' [Nonempty ι] :
    (∀ (x : E) (w : ℝ), (x ∈ s ∧ f x ≤ w ↔ (∀ i, x ∈ s ∧ g i x ≤ w))) ↔
    ∀ (x : E) (w : ℝ) (_ : x ∈ s), (f x ≤ w ↔ (∀ i, g i x ≤ w)) := by
  apply forall₂_congr
  intro a b
  rw[forall_and_left,and_congr_right_iff]

/-!
Theorem. Suppose `f.Epi s = ⋂ i, (g i).Epi s` (the epigraph of `f` is the
intersection of the epigraphs of the family `g i`).
Then for every `x ∈ s`, we have: f(x) = ⨆ i, g i(x).
Purpose:
This result connects pointwise values of `f` with the pointwise supremum of the family `g i`,
using the fact that epigraph intersections encode pointwise `⨆`.
-/
theorem point_sup_of_epi_inter_of_nonempty {g : ι → E → EReal} [Nonempty ι]
    (hepi : f.Epi s = ⋂ i, ((g i).Epi s)) : ∀ x ∈ s, f x = ⨆ i, g i x := by
  rw[epi_inter_iff_forall, forall_in_and_iff_forall_in'] at hepi
  intro x hx
  symm
  apply iSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro i
    by_cases hfx : f x = ⊤
    · rw[hfx];simp
    by_cases hfx2 : f x = ⊥
    · rw[hfx2, ←le_of_forall_lt_iff_le]
      intro z _hz
      have := (hepi x z hx).1 (StrictMono.minimal_preimage_bot (fun _ _ a ↦ a) hfx2 ↑z)
      exact this i
    rw[← coe_toReal hfx hfx2]
    exact (hepi x (f x).toReal hx).1 (le_coe_toReal hfx) i
  intro w hw
  have hwtop : w ≠ ⊤ := LT.lt.ne_top hw
  by_cases hwbot : w = ⊥
  · rw[hwbot];
    by_contra! hgi
    simp at hgi
    have : f x = ⊥ := by
      apply (eq_bot_iff_forall_lt (f x)).mpr
      intro y
      have := (hepi x (y - 1) hx).2 (by intro i;rw[hgi i];simp)
      apply lt_of_le_of_lt this <| EReal.coe_lt_coe_iff.mpr <| sub_one_lt y
    rw[this, hwbot] at hw
    exact (lt_self_iff_false ⊥).mp hw
  by_contra! hi
  rw[← coe_toReal hwtop hwbot, ← hepi x w.toReal hx] at hi
  rw[← coe_toReal hwtop hwbot, ← not_le] at hw
  exact hw hi

/-!
Theorem. Suppose `f.Epi s = ⋂ i, (g i).Epi s`.
Then for all `x ∈ s`,
  f(x) = ⨆ i, g i(x).
This version removes the `Nonempty ι` assumption by handling the empty-index case.
Purpose: To extend `point_sup_of_epi_inter_of_nonempty` so that it holds for arbitrary index sets,
including when `ι` is empty.
-/
theorem point_sup_of_epi_inter {g : ι → E → EReal} (hepi : f.Epi s = ⋂ i, ((g i).Epi s)) :
    ∀ x ∈ s, f x = ⨆ i, g i x := by
  by_cases hl : Nonempty ι
  · exact fun x a ↦ point_sup_of_epi_inter_of_nonempty hepi x a
  simp at hl
  simp [Function.Epi] at *
  intro x _hx
  apply (eq_bot_iff_forall_lt (f x)).mpr
  intro y
  have : (x, y - 1) ∈ univ := trivial
  rw[← hepi] at this;simp at this
  apply lt_of_le_of_lt this.2
  change y - (1 : ℝ).toEReal < y
  rw[← EReal.coe_sub, EReal.coe_lt_coe_iff]
  exact sub_one_lt y

/-!
Theorem. Suppose for all `x ∈ s` we have
  f(x) = ⨆ i, g i(x).
Then the epigraph of `f` satisfies
  f.Epi s = ⋂ i, (g i).Epi s,
provided the index type `ι` is nonempty.
Purpose: This is the converse of `point_sup_of_epi_inter_of_nonempty`.
It characterizes the epigraph of a pointwise supremum in terms of the intersection of epigraphs.
-/
theorem epi_inter_of_point_sup_of_nonempty {g : ι → E → EReal} [Nonempty ι]
    (hsup : ∀ x ∈ s, f x = ⨆ i, g i x) : f.Epi s = ⋂ i, ((g i).Epi s) := by
  rw[epi_inter_iff_forall, forall_in_and_iff_forall_in']
  intro x w hx
  exact
  ⟨fun hfw i ↦ Preorder.le_trans _ _ _ ((hsup x hx) ▸ (le_iSup_iff.mpr fun _ a ↦ a i)) hfw,
  fun hig ↦ (hsup x hx) ▸ (iSup_le hig)⟩

/-!
Theorem. Assume the index type `ι` is nonempty.
Then the following are equivalent:
1. For all `x ∈ s`, we have
   `f x = ⨆ i, g i x`.
2. The epigraph of `f` equals the intersection of the epigraphs of the `g i`:
   `f.Epi s = ⋂ i, (g i).Epi s`.
Purpose: This gives a clean equivalence between pointwise supremum representation
and epigraph intersection.
-/
theorem point_sup_iff_epi_inter_of_nonempty {g : ι → E → EReal} [Nonempty ι] :
    (∀ x ∈ s, f x = ⨆ i, g i x ) ↔ f.Epi s = ⋂ i, ((g i).Epi s) := by
  constructor
  · exact fun a ↦ epi_inter_of_point_sup_of_nonempty  a
  exact fun a x a_1 ↦ point_sup_of_epi_inter a x a_1

/-!
Theorem. If the index type `ι` is nonempty, then the epigraph of the pointwise supremum
equals the intersection of the epigraphs:
`(⨆ i, g i).Epi s = ⋂ i, (g i).Epi s`.
Purpose: This is the direct "epi–sup" law: taking the pointwise supremum commutes with
forming the epigraph (over a set).
-/
theorem point_sup_iff_epi_inter_of_nonempty'
    {g : ι → E → EReal} [Nonempty ι] :
    (⨆ i, g i).Epi s = ⋂ i, ((g i).Epi s) :=
  (point_sup_iff_epi_inter_of_nonempty).mp (fun _ _ ↦ iSup_apply)

end sup_aux


section epigraph

variable [NormedAddCommGroup E] {s : Set E} {f : E → EReal}

/-!
Lemma. If `f : E → EReal` is convex on `s ⊆ E`, then the epigraph of `f` over `s`
is convex in the product space `E × ℝ`:
`Convex ℝ (f.Epi s)`.
Purpose: This is the classical fact that convex functions have convex epigraphs.
It allows reasoning about convexity of sets derived from functions in
optimization and analysis.
-/
lemma EReal.convex_epigraph [NormedSpace ℝ E] (hf : ConvexOn ℝ s f) :
    Convex ℝ (f.Epi s) := by
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • r + b • t := by
      apply add_le_add
      · refine mul_le_mul_of_nonneg_left hr <| EReal.coe_nonneg.mpr ha
      refine mul_le_mul_of_nonneg_left ht <| EReal.coe_nonneg.mpr hb

/-!
Lemma. If `f : E → EReal` is convex on `s ⊆ E`, then the set
`{p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}`
(i.e., the epigraph of `f` over `s`) is convex in the product space `E × EReal`.
Purpose: This formalizes the classical result that the epigraph of a convex function
is a convex set, which is fundamental in convex analysis.
-/
lemma Convex_epigraph_ereal [NormedSpace ℝ E] (hf : ConvexOn ℝ s f) :
    Convex ℝ {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • r + b • t := by
      apply add_le_add
      · refine mul_le_mul_of_nonneg_left hr <| EReal.coe_nonneg.mpr ha
      refine mul_le_mul_of_nonneg_left ht <| EReal.coe_nonneg.mpr hb

/-!
Lemma. If the epigraph of `f` over `s` is convex, then the domain of `f` over `s`
(i.e., the set of points `x ∈ s` where `f x < ⊤`) is also convex:
`Convex ℝ (dom s f)`.
Purpose: This shows that convexity of the epigraph implies convexity of the effective domain.
It is a standard fact in convex analysis: the “projection” of a convex set
onto the first coordinate preserves convexity.
-/
lemma convex_epigraph_dom_convex [NormedSpace ℝ E] (hf : Convex ℝ (f.Epi s)) :
    Convex ℝ (dom s f) := by
  intro x hx y hy a b ha hb hab
  let g1 := (f x).toReal
  let g2 := (f y).toReal
  have h1 : f x ≤ g1 ∧ f y ≤ g2 := by /- wyj -/
    exact ⟨le_coe_toReal (LT.lt.ne_top hx.2), le_coe_toReal (LT.lt.ne_top hy.2)⟩
  have h2 : (x, g1) ∈ f.Epi s ∧ (y, g2) ∈ f.Epi s := by
    simp [Epi]
    exact ⟨⟨hx.1, h1.1⟩, ⟨hy.1, h1.2⟩⟩
  simp [dom]
  constructor
  · exact (hf h2.1 h2.2 ha hb hab).1
  apply lt_of_le_of_lt
  · exact (hf h2.1 h2.2 ha hb hab).2
  exact coe_lt_top (a • (x, g1) + b • (y, g2)).2

/-!
Lemma. Suppose `f : E → EReal` has a convex epigraph over `s` and its domain `dom s f` is convex.
If at some point `m ∈ dom s f` the function attains `-∞` (`f m = ⊥`),
then for any `n ∈ dom s f` and convex combination weights `p, q > 0` with `p + q = 1`,
the function value at the convex combination satisfies:
`f (p • m + q • n) ≤ p • f m + q • f n`.
Purpose: This lemma handles the special case where one endpoint of a convex combination
attains `-∞`. It formalizes that the convex combination respects the epigraph inequality.
-/
lemma convex_epi_convex_ineq_of_bot_within [NormedSpace ℝ E] (hf : Convex ℝ (Epi f s))
    {m : E} (hm : m ∈ dom s f) (h_dom : Convex ℝ (dom s f))
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq0 : p ≠ 0 ∧ q ≠ 0) (hpq : p + q = 1) (h : f m = ⊥) :
    ∀ n ∈ dom s f, f (p • m + q • n) ≤ p • f m + q • f n := by /- wyj -/
  /-
  epigraph is convex and dom s f is convex, one endpoint function value is ⊥,
  the function value of the convex combination holds less than or equal to
  the convex combination of function values inside the line segment.
  -/
  intro n hn
  simp [h]
  have : ↑p * ⊥ + ↑q * f n = ⊥ := by
    refine EReal.add_eq_bot_iff.mpr ?_
    left; exact coe_mul_bot_of_pos (lt_of_le_of_ne hp hpq0.1.symm)
  rw [this]
  by_contra! not_bot
  let r := (f (p • m + q • n)).toReal
  /-
  Since it is greater than -∞, and p • m + q • n ∈ dom s f, there is a real number r
  equal to the function value of the convex combination.
  -/
  obtain h1 := Eq.symm (coe_toReal (LT.lt.ne_top (x_dom_lt_top (h_dom hm hn hp hq hpq)))
    (LT.lt.ne_bot (not_bot)))
  let rn := (f n).toReal -- find a real number rn above the function value at n
  have h2 : (n, rn) ∈ f.Epi s := ⟨mem_of_mem_inter_left hn, le_coe_toReal (LT.lt.ne_top hn.2)⟩
  /-
  Note that since f m = -∞, any real number is in the epigraph at point m.
  We have (p • m + q • n, r = f (p • m + q • n)) ∈ f.Epi s and (n, rn) ∈ f.Epi s.
  Now, using f m = -∞, we can find a number (r - q • rn)/p - 1 in the epigraph at m,
  such that the convex combination
  p • (n, rn) + q • (m, (r - q • rn)/p - 1) = (p • m + q • n, p • ((r - q • rn)/p - 1) + q • rn)
  holds, and r > p • ((r - q • rn)/p - 1) + q • rn, which contradicts the convexity of the epigraph.
  -/
  have h3 : (m, (r - q • rn)/p - 1) ∈ f.Epi s := by
    exact ⟨mem_of_mem_inter_left hm, by simp [h]⟩
  obtain h4 := (hf h3 h2 hp hq hpq).2
  simp at h4; rw [h1] at h4; norm_cast at h4
  have h5 : ¬ r ≤ p • ((r - q • rn)/p - 1) + q • rn := by
    push_neg at *
    rw [smul_sub p ((r - q • rn) / p) 1]
    simp; field_simp [hpq0.1]
    have : r - q * rn - p + q * rn = r - p := by linarith
    rw [this]
    exact sub_lt_self r (lt_of_le_of_ne hp hpq0.1.symm)
  exact h5 h4

/-!
Theorem. Suppose `f : E → EReal` has a convex epigraph over `s` and its domain `dom s f` is convex.
If at least one endpoint of a convex combination attains `-∞` (`f x = ⊥` or `f y = ⊥`),
then for any convex combination `a • x + b • y` with `a, b ≥ 0` and `a + b = 1`, we have:
`f (a • x + b • y) ≤ a • f x + b • f y`.
Purpose: This lemma generalizes `convex_epi_convex_ineq_of_bot_within` to handle either
endpoint of the line segment being `-∞`.
-/
theorem convex_epi_convex_ineq_of_bot [NormedSpace ℝ E] (hf : Convex ℝ (Epi f s))
    {x y : E} (hx : x ∈ dom s f) (hy : y ∈ dom s f) (h_dom : Convex ℝ (dom s f))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h : f x = ⊥ ∨ f y = ⊥) :
    f (a • x + b • y) ≤ a • f x + b • f y := by /- wyj -/
  -- First consider the case when one of the endpoints is zero.
  by_cases c1 : a = 0 ∨ b = 0
  · rcases c1 with ha0 | hb0
    · simp [ha0] at hab ⊢
      rw [hab]
      simp
    · simp [hb0] at hab ⊢
      rw [hab]
      simp
  /-
  Then consider any point inside the line segment of the convex combination.
  Since f x = -∞ or f y = -∞, we transform the proof goal to f (a • x + b • y) ≤ -∞.
  -/
  push_neg at c1
  rcases h with hx_bot | hy_bot /- First consider f x = ⊥, actually x and y are symmetric,
  so we write a lemma here. -/
  · exact convex_epi_convex_ineq_of_bot_within hf hx h_dom ha hb c1 hab hx_bot y hy
  rw [add_comm (a • x) (b • y), add_comm (a • f x) (b • f y)]
  rw [add_comm] at hab
  exact convex_epi_convex_ineq_of_bot_within hf hy h_dom hb ha c1.symm hab hy_bot x hx

/-!
Lemma. If `f : E → EReal` has a convex epigraph over a set `s`, then `f` is convex on its domain.
Purpose: This lemma lifts convexity of the epigraph (a set in `E × EReal`)
to convexity of the function itself.
Formally, it shows `ConvexOn ℝ (dom s f) f`.
-/
lemma convex_epigraph_convex [NormedSpace ℝ E] (hf : Convex ℝ (f.Epi s)) :
    ConvexOn ℝ (dom s f) f := by /- wyj -/
  simp only [ConvexOn]
  /-
  Now we prove the two parts of the definition of ConvexOn:
  1. dom s f is convex (already proved in a previous lemma),
  2. the function value at any convex combination of two points
     in dom s f is less than or equal to the convex combination of the function values
     at those two points (to be proved now).
  -/
  constructor
  · exact convex_epigraph_dom_convex hf -- Previous lemma: dom s f is convex.
  intro x hx y hy a b ha hb hab
  by_cases h :  f x = ⊥ ∨ f y = ⊥ /-
  It is necessary to discuss separately the case where the function value at
  one of the points x and y is -∞, and a lemma has been written for this.
  -/
  · exact convex_epi_convex_ineq_of_bot hf hx hy (convex_epigraph_dom_convex hf) ha hb hab h
  push_neg at h
  /-
  The case where f x ≠ -∞ and f y ≠ -∞.
  Since we are considering on dom s f, we have -∞ < f x, f y < ∞,
  so we only need to handle the conversion from EReal to ℝ.
  -/
  let g1 := (f x).toReal
  let g2 := (f y).toReal
  have h1: g1 = f x ∧ g2 = f y := by
    exact ⟨coe_toReal (LT.lt.ne_top (x_dom_lt_top hx)) (h.1),
    coe_toReal (LT.lt.ne_top (x_dom_lt_top hy)) (h.2) ⟩
  rw [← h1.1, ← h1.2]
  have h2 : (x, g1) ∈ f.Epi s ∧ (y, g2) ∈ f.Epi s := by
    simp [Epi, h1]
    exact ⟨hx.1, hy.1⟩
  exact (hf h2.1 h2.2 ha hb hab).2

section epi_EReal_and_epi_Real

/-!
Theorem. If the epigraph of a function f over a set s is closed in E × ℝ,
then sequences in the epigraph converging to a limit (x, y) with y = -∞
satisfy f x = -∞.
Purpose: show that closedness of the real epigraph yields lower semicontinuity.
-/
theorem EReal_epi_closed_of_Real_epi_closed_of_bot
    {xn : ℕ → E × EReal} {x : E} {y : EReal} (hy : y = ⊥)
    (hxy : ∀ (n : ℕ), (xn n).1 ∈ s ∧ f (xn n).1 ≤ (xn n).2)
    (hlim : Tendsto xn atTop (𝓝 (x, y)))
    (h : _root_.IsClosed {p : E × ℝ| p.1 ∈ s ∧ f p.1 ≤ p.2}) :
    f x = ⊥ := by
  rw[hy] at *
  rw[← isSeqClosed_iff_isClosed] at *
  simp [IsSeqClosed] at *
  simp [Prod.tendsto_iff] at hlim
  by_contra! hfx
  have hxnin : ∀ (n : ℕ), (xn n).1 ∈ s := fun n ↦ (hxy n).1
  have heven : ∀ᶠ (n : ℕ) in atTop, f (xn n).1 ≤ ↑(f x).toReal - 1 := by
    apply Filter.Eventually.mp (tendsto_coe_nhds_top hlim.2 ((f x).toReal - 1))
    apply Filter.Eventually.of_forall
    intro z hz
    apply le_trans (hxy z).2 hz
  rw[Filter.eventually_atTop] at heven
  obtain ⟨N, hN⟩ := heven
  let xn' : ℕ → E × ℝ := fun n => ⟨(xn (n + N)).1, (f x).toReal - 1⟩
  have hxy' : (∀ (n : ℕ), (xn' n).1 ∈ s ∧ f (xn' n).1 ≤ (xn' n).2) := by
    intro n
    simp [xn']
    constructor
    · apply hxnin
    exact hN (n + N) (by simp)
  have hlim' : Tendsto xn' atTop (𝓝 (x, (f x).toReal - 1)) := by
    rw[Prod.tendsto_iff]
    simp
    rw[Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ (xn n).1) N]
    use hlim.1
    rw [tendsto_const_nhds_iff]
  have key := h (x := xn') x ((f x).toReal - 1) hxy'  hlim'
  have := key.2
  by_cases hftop : f x = ⊤
  · simp [hftop] at this
    have tl: (1 : EReal) ≠ ⊥ := ((fun {x} ↦ add_top_iff_ne_bot.mp) rfl)
    exact tl this
  nth_rw 1 [← EReal.coe_toReal hftop hfx] at this
  rw[EReal.coe_le_coe_iff] at this
  linarith

/-!
Theorem 7.1.
If the epigraph of `f` over `s` is closed in `E × ℝ`,
then sequences in the epigraph converging to a limit `(x, y)` with `y ∈ ℝ` satisfy `f x ≤ y`.
Purpose: show that closedness of the real epigraph yields lower semicontinuity.
-/
theorem EReal_epi_closed_of_Real_epi_closed_of_nebot_netop {xn : ℕ → E × EReal} {x : E} {y : EReal}
    (hybot : y ≠ ⊥) (hytop : y ≠ ⊤) (hxy : ∀ (n : ℕ), (xn n).1 ∈ s ∧ f (xn n).1 ≤ (xn n).2)
    (hlim : Tendsto xn atTop (𝓝 (x, y)))
    (h : _root_.IsClosed {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}) :
    f x ≤ y := by
  lift y to Real using ⟨hytop, hybot⟩
  -- Define g, mapping the second coordinate from EReal to Real
  let g := Prod.map (@id E) EReal.toReal
  have in_and_le : ∃ᶠ (x : ℕ) in atTop, (g (xn x)).1 ∈ s ∧ f (g (xn x)).1 ≤ (g (xn x)).2 := by
    simp [g]
    refine Eventually.and_frequently ?hp ?hq
    refine Filter.Eventually.of_forall ?hp.hp
    intro n
    apply (hxy n).1
    refine frequently_atTop.mpr ?hq.a
    intro N
    by_cases hxntop : ∀ b ≥ N, (xn b).2 = ⊤
    · simp [Prod.tendsto_iff] at hlim
      have key : y = (⊤ : EReal) :=
        tendsto_nhds_unique hlim.2 (tendsto_atTop_of_eventually_const hxntop)
      exact False.elim (hytop key)
    simp at hxntop
    obtain ⟨b, hb⟩ := hxntop
    use b
    simp
    constructor
    · exact hb.1
    by_cases hfb : f (xn b).1 = ⊥
    · rw [hfb]; simp
    by_cases hxnbot : (xn b).2 = ⊥
    · have : f (xn b).1 = ⊥ := bot_unique <| hxnbot ▸ (hxy b).2
      exact False.elim (hfb this)
    rw [EReal.coe_toReal hb.2 hxnbot]
    apply (hxy b).2
  have glim :Tendsto (g ∘ xn) atTop (𝓝 (x, y)) := by
    simp [Prod.tendsto_iff] at *
    simp [g]
    exact ⟨hlim.left, tendsto_coe_of_Real hlim.right⟩
  have := IsClosed.mem_of_frequently_of_tendsto h in_and_le glim
  simp at this
  exact this.2

/-!
Theorem. If the epigraph of `f` over `s` is closed in `E × ℝ`, and `s` is closed,
then the corresponding epigraph in `E × EReal` is also closed.
Purpose: extend closedness of the epigraph from the real case to the extended real case.
-/
theorem EReal_epi_closed_of_Real_epi_closed
    (h : _root_.IsClosed {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}) (hs : _root_.IsClosed s) :
    _root_.IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  simp [← isSeqClosed_iff_isClosed, IsSeqClosed]
  intro xn x y hxy hlim
  constructor
  · simp [Prod.tendsto_iff] at hlim
    apply IsClosed.mem_of_tendsto hs hlim.1
    refine Filter.Eventually.of_forall ?left.hp
    intro n
    apply (hxy n).1
  by_cases hytop : y = ⊤
  · rw [hytop]; simp
  by_cases hybot : y = ⊥
  · rw [hybot]; simp
    exact EReal_epi_closed_of_Real_epi_closed_of_bot hybot hxy hlim h
  exact EReal_epi_closed_of_Real_epi_closed_of_nebot_netop hybot hytop hxy hlim h

/-!
Theorem. If the epigraph of `f` over `s` is closed in `E × EReal`,
then the corresponding epigraph in `E × ℝ` is also closed.
Purpose: reduce closedness of the epigraph in the extended real case back to the real case.
-/
theorem Real_epi_closed_of_EReal_epi_closed
    (h : _root_.IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}) :
    _root_.IsClosed {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  simp [← isSeqClosed_iff_isClosed, IsSeqClosed] at *
  intro xn x y hxy hlim
  simp [Prod.tendsto_iff] at hlim
  -- Define g, mapping the second coordinate from Real to EReal
  let g := Prod.map (@id E) Real.toEReal
  have inandle: ∀ (n : ℕ), ((g ∘ xn) n).1 ∈ s ∧ f ((g ∘ xn) n).1 ≤ ((g ∘ xn) n).2 := by
    simp [g]
    intro n
    exact hxy n
  have glim : Tendsto (g ∘ xn) atTop (𝓝 (x, ↑y)) := by
    simp [Prod.tendsto_iff] at *
    simp [g]
    exact ⟨hlim.1, tendsto_coe.mpr hlim.2⟩
  exact h (x := g ∘ xn) x y inandle glim

/-!
Theorem. If the epigraph of `f` in `E × EReal` is closed,
then the domain `s` is closed.
Purpose: deduce closedness of the domain from closedness of the epigraph.
-/
theorem domain_closed_of_epi_EReal_closed (h : IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}) :
    IsClosed s := by
  -- Define g, fix the first coordinate and replace the second by top
  let g := Continuous.prodMk_left (X := E) (⊤ : EReal)
  -- I is the "top slice" { (x, ⊤) | x ∈ E }
  let I := {x : E × EReal | x.2 = ⊤}
  -- The intersection of the epigraph with I is closed
  have hclo : _root_.IsClosed ({p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} ∩ I) := by
    refine IsClosed.inter h ?h₂
    refine isClosed_eq ?h₂.hf ?h₂.hg
    exact continuous_snd
    apply continuous_const
  -- The domain s is the preimage of this intersection under g, hence s is closed
  have := IsClosed.preimage g hclo
  simp [I] at this
  exact this

/-!
Theorem. Closedness of the epigraph in `E × EReal` is equivalent to
closedness of `s` and closedness of the epigraph in `E × ℝ`.
Purpose: give the equivalence between `EReal` and `Real` epigraph closedness.
-/
theorem EReal_epi_closed_Real_epi_closed :
    _root_.IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} ↔
    _root_.IsClosed s ∧ _root_.IsClosed {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  constructor
  · intro h
    exact ⟨domain_closed_of_epi_EReal_closed h, Real_epi_closed_of_EReal_epi_closed h⟩
  intro h
  refine EReal_epi_closed_of_Real_epi_closed h.2 h.1

end epi_EReal_and_epi_Real

end epigraph


section EReal

variable [NormedAddCommGroup E] {s : Set E} {f : E → EReal}

/-!
Lemma. If `(x, a)` lies in the closure of the epigraph of `f` on `s`, with `a = ⊥` and `a ≤ b ≠ ⊤`,
then `(x, b)` also lies in the closure.
Purpose: extend closure membership from `⊥` to any finite `b` above it.
-/
lemma in_of_le_sinf_of_bot {x : E} {a b : EReal}
    (ha : (x, a) ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}) (hab : a ≤ b)
    (habot : a = ⊥) (hbtop : b ≠ ⊤) :
    (x, b) ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  rcases le_iff_eq_or_lt.1 hab with hab | hab
  · rwa [← hab]
  rw [mem_closure_iff_seq_limit] at ha
  -- obtain a sequence converging to (x, a)
  obtain ⟨xn, hxn, hlim⟩ := ha
  rw [mem_closure_iff_seq_limit]
  simp [Prod.tendsto_iff] at hlim
  have := hlim.2
  rw [habot, tendsto_nhds_bot_iff_real] at this
  lift b to ℝ using ⟨hbtop, LT.lt.ne_bot hab⟩
  have hn := this b
  rw [eventually_atTop] at hn
  have ⟨N, hN⟩ := hn
  -- construct a sequence converging to (x, b)
  let xn' : ℕ → E × EReal := fun n => ((xn (n + N)).1, b)
  use xn'
  constructor
  · simp [xn'] at *
    intro n
    constructor
    · apply (hxn (n + N)).1
    apply le_trans (hxn (n + N)).2
    apply le_of_lt
    apply hN
    simp
  simp [Prod.tendsto_iff] at *
  have := hlim.1
  rw [Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ (xn n).1) N]
  refine ⟨this, ?_⟩
  exact tendsto_const_nhds

/-!
Lemma. For any `x ∈ s`, the point `(x, ⊤)` lies in the closure of the epigraph of `f` on `s`.
Purpose: show that the closure contains all points with second component `⊤`.
-/
lemma in_of_le_sinf_of_b_top (hx : x ∈ s) :
    (x, ⊤) ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  apply subset_closure
  simpa

/-!
Lemma. For any `x ∈ s`, if `(x, a)` lies in the closure of the epigraph of `f` on `s` and `a ≤ b`,
then `(x, b)` also lies in the closure of the epigraph of `f` on `s`.
Purpose: extend closure membership from `a` to any `b` above it.
-/
lemma in_of_le_sinf (hx : x ∈ s) (ha : (x, a) ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2})
    (hab : a ≤ b) :
    (x, b) ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  by_cases hatop : a = ⊤
  · simp [hatop] at hab
    rw [hatop] at ha
    simpa [hab]
  by_cases hbtop : b = ⊤
  · rw [hbtop]; exact in_of_le_sinf_of_b_top hx
  by_cases habot : a = ⊥
  · exact in_of_le_sinf_of_bot ha hab habot hbtop
  lift a to ℝ using ⟨hatop, habot⟩
  lift b to ℝ using ⟨hbtop, ne_bot_of_le_ne_bot habot hab⟩
  rw [mem_closure_iff_seq_limit] at ha
  -- obtain a sequence converging to (x, a), where xn is in the epigraph
  obtain ⟨xn, hxn, hlim⟩ := ha
  rw [mem_closure_iff_seq_limit]
  -- construct a new sequence by shifting the second component up by (b - a)
  let xn' : ℕ → E × EReal := fun n => ((xn n).1, (xn n).2 + (b - a))
  have hable : b - a ≥ 0 := by
    rw [@EReal.coe_le_coe_iff] at hab
    exact sub_nonneg_of_le hab
  -- show the new sequence lies in the epigraph
  use xn'
  constructor
  · simp [xn'] at *
    intro n
    constructor
    · apply (hxn n).1
    -- Use transitivity of ≤ to show f(xn n).1 ≤ (xn n).2 + (b - a)
    apply le_trans (hxn n).2
    rw [← EReal.coe_sub]
    apply EReal.sub_le_of_ge_zero
    exact (sub_nonneg_of_le hab)
  rw [Prod.tendsto_iff] at *
  constructor
  · apply hlim.1
  simp [xn']
  have : b = a + (b - a) := by simp
  nth_rw 2 [this]
  -- Define addition function on EReal × EReal
  let g := (fun p : EReal × EReal => p.1 + p.2)
  -- Pair sequence values with b - a
  let h : ℕ → EReal × EReal := (fun n ↦ ((xn n).2, (b - a)))
  -- reformulate the goal using g and h
  change Tendsto (g ∘ h) atTop (𝓝 (g (a, (b - a))))
  apply Tendsto.comp
  · apply continuousAt_add (by simp) (by simp)
  simpa [h, Prod.tendsto_iff] using hlim.2

/-!
Lemma. For any `x ∈ s`, the point `(x, f x)` lies in the closure of the epigraph of `f` on `s`.
Purpose: show that the closure contains all points `(x, f x)` for `x` in the domain.
-/
lemma x_fx_in_closure (s : Set E) (f : E → EReal) {x : E} (hx : x ∈ s) :
    (x, f x) ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  apply subset_closure
  simpa

/-
This defines a function `closure_epi` that maps each point `x` in `E` to the infimum of the set of
`w` such that `(x, w)` lies in the closure of the epigraph of `f` on `s`.
Purpose: An equivalent way to describe the closure.
-/
noncomputable def closure_epi (s : Set E) (f : E → EReal) :=
    fun x => sInf {w | (x, w) ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}}

/-!
Theorem. For any `x ∈ s`, there exists `y` such that `(x, y)` lies in the closure of the epigraph
of `f` on `s`, and `y` equals the value of `closure_epi s f x`.
Purpose: show that the infimum in the definition of `closure_epi` is attained for points in `s`.
-/
theorem exist_eq_closure_epi (s : Set E) (f : E → EReal) {x : E} (hx : x ∈ s) :
    ∃ (y : EReal), (x, y) ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} ∧
    closure_epi s f x = y := by
  have : closure_epi s f x ∈ {w | (x, w) ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}} := by
    apply IsClosed.sInf_mem
    use ⊤; simp
    apply subset_closure; simp
    apply hx
    refine IsClosed.preimage ?hc.hf ?hc.h
    exact Continuous.prodMk_right x
    exact isClosed_closure
  simp at this
  use closure_epi s f x

/-!
Theorem. If `s` is closed and `(p.1, p.2)` lies in the closure of the epigraph of `f` on `s`,
then `p.1` lies in `s`.
Purpose: show that the closure of the epigraph does not introduce new points in the first component
when the domain is closed.
-/
theorem in_of_closed_in_closure (hs : IsClosed s)
    (hp : p ∈ closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}) :
    p.1 ∈ s := by
  rw [← isSeqClosed_iff_isClosed] at hs
  rw [mem_closure_iff_seq_limit] at hp
  obtain ⟨x, hxn, hlim⟩ := hp
  simp at hxn
  have hxn' : ∀ (n : ℕ), (x n).1 ∈ s:= by
    intro n; apply (hxn n).1
  apply hs hxn'
  rw [Prod.tendsto_iff] at hlim
  apply hlim.1

/-!
Theorem. If `s` is closed, then the set of points `(p.1, p.2)` such that `p.1 ∈ s` and
`closure_epi s f p.1 ≤ p.2` equals
the closure of the set of points `(p.1, p.2)` such that `p.1 ∈ s` and `f p.1 ≤ p.2`.
Purpose: relate the epigraph of `closure_epi` to the closure of the epigraph.
-/
theorem epi_closure_epi_eq_cl_epi (hs : IsClosed s) :
    {p : E × EReal | p.1 ∈ s ∧ closure_epi s f p.1 ≤ p.2} =
    closure {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  rw [le_antisymm_iff]
  constructor
  · intro p hp
    simp at *
    obtain ⟨y, hy1, hy2⟩ := exist_eq_closure_epi s f hp.1
    apply in_of_le_sinf hp.1 hy1
    rw [← hy2]
    apply hp.2
  intro p hp
  simp at *
  simp [closure_epi]
  constructor
  · exact in_of_closed_in_closure hs hp
  apply sInf_le
  exact hp


/-!
Theorem. For any `x ∈ s`, the value of `closure_epi s f x` is less than or equal to `f x`.
Purpose: show that `closure_epi s f` is pointwise less than or equal to `f` on `s`.
-/
theorem closure_epi_le_f (f) :
    ∀ x ∈ s, closure_epi s f x ≤ f x := by
  intro x hx
  apply sInf_le
  exact x_fx_in_closure s f hx

/-!
Theorem. For any `x ∈ s`, `f x ≤ g x` if and only if
the epigraph of `g` is contained in the epigraph of `f` on `s`.
Purpose: relate pointwise comparison of functions to inclusion of their epigraphs.
-/
omit [NormedAddCommGroup E] in
theorem le_iff_epi_sub (s : Set E) (f g : E → EReal) :
    (∀ x ∈ s, f x ≤ g x) ↔
    {p : E × EReal | p.1 ∈ s ∧ g p.1 ≤ p.2} ⊆ {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  constructor
  · intro h x hx
    simp at *
    exact ⟨hx.left, le_trans (h x.1 hx.left) hx.right⟩
  intro h x hx
  have : (x, g x) ∈ {p | p.1 ∈ s ∧ g p.1 ≤ p.2} := by simpa
  have := h this
  simp at this
  apply this.2

end EReal


/-!
Lemma. Let `f` be a proper function over `s`, and `x ∈ s` such that `f x < ⊤`,
then `(x, f(x))` is in the epigraph of `f` over `s`.
Purpose: a trivial property of epigraph.
-/
lemma xfxinepif [hsf : ProperFunction s f] (htop : f x < ⊤) (hx : x ∈ s) :
    (x, (f x).toReal) ∈ f.Epi s := by
  simp [Function.Epi]
  rw[← EReal.coe_toReal (x := f x) (LT.lt.ne_top htop) (LT.lt.ne_bot (hsf.uninfinity x hx))]
  simpa

/-!
Lemma. Let `f` be a proper function over `s`, and `x ∈ s` such that `f x < ⊤`,
then `(x, f(x) - 1)` is not an element of epigraph of `f` over `s`.
Purpose: a trivial property of epigraph.
-/
lemma disj [hsf : ProperFunction s f] (htop : f x < ⊤) (hx : x ∈ s) :
    (x, (f x).toReal - 1) ∉ f.Epi s := by
  simp [Function.Epi]
  intro _
  nth_rw 2 [← EReal.coe_toReal (x := f x) (LT.lt.ne_top htop) (LT.lt.ne_bot (hsf.uninfinity x hx))]
  change (f x).toReal.toEReal - (1 : ℝ) < (f x).toReal
  rw[← EReal.coe_sub, EReal.coe_lt_coe_iff]; simp
