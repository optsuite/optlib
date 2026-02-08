/-
Copyright (c) 2025  Zichen Wang, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Zichen Wang, Chenyi Li
-/
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.Semicontinuous
import Reaslib.Basic.EReal
/-!
# Definitions of the proper functions
This file contains the definitions and properties of the proper functions

## References

-/

open Filter BigOperators Set EReal
open scoped Pointwise Topology

@[mk_iff]
class ProperFunction {α : Type*} (s : Set α) (f : α → EReal) : Prop where
  -- f(x) > -∞
  uninfinity: (∀ x ∈ s, f x > ⊥)
  -- exist a x such that f(x) < +∞
  -- by_cases s is empty or nonempty
  existence_of_finite_value : (s = ∅) ∨ (∃ x ∈ s , f x < ⊤)

theorem ProperFunction.to_neg {α : Type*} (s : Set α) (f : α → EReal) :
  ¬ (ProperFunction s f) ↔ (∃ x ∈ s, f x = ⊥) ∨ (s ≠ ∅ ∧ ∀ x ∈ s, f x = ⊤) := by
  rw [properFunction_iff]
  simp
  constructor
  · intro h
    by_cases h1 : ∃ x ∈ s, f x = ⊥
    · left; exact h1
    push_neg at h1
    obtain h2 := h (fun x a ↦ Ne.bot_lt' fun a_1 ↦ h1 x a (id (Eq.symm a_1)))
    right; exact h2
  intro h h1
  rcases h with h | h
  · rcases h with ⟨x, hx, hx1⟩
    exfalso
    obtain h2 := h1 x hx
    rw [hx1] at h2; simp at h2
  exact h

--[Extend s f]
class Extend {α : Type*} (s : Set α) (f : α → EReal) where
  not_in_domain_is_infinity : ∀ x ∉ s, f x = ⊤

@[simp]
def dom {α : Type*} (s : Set α) (f : α → EReal) : Set α :=
    {x ∈ s | f x < ⊤}

theorem x_dom_lt_top {α : Type*} {x : α} {s : Set α} {f : α → EReal}
    (hx : x ∈ dom s f) : f x < ⊤ := hx.2

theorem dom_eq_smul (s : Set E) (f : E → EReal) {m : ℝ} (hm : m > 0) :
    dom s (m • f) = dom s f := by
  simp; ext x; simp
  exact fun _ ↦ mul_lt_top_iff_lt_top hm

theorem univ_proper_dom_not_empty {α : Type*} [AddCommMonoid α] (f : α → EReal)
    [h : ProperFunction univ f] : (dom univ f).Nonempty := by
  obtain h1 := h.2; simp at h1
  rcases h1 with ⟨x, hx⟩; use x; simp [hx]

lemma convexOn_s_of_convexOn_dom_s_f {f : α → EReal} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [hsf : ProperFunction univ f] (hf : ConvexOn ℝ (dom univ f) f) : ConvexOn ℝ univ f := by
  constructor
  · apply convex_univ
  intro x _ y _ a b ha hb hab
  by_cases h1 : f x = ⊤
  · rw [h1]; by_cases ha1 : a = 0
    · rw [ha1]; simp;
      have hb : b = 1 := by rwa [ha1, zero_add] at hab
      rw [hb]; simp
    have ha : a > 0 := by positivity
    simp; rw [EReal.coe_mul_top_of_pos ha]
    rw [top_add_of_ne_bot (LT.lt.ne_bot <| mul_pos_gt_bot hb (hsf.1 y trivial))]; simp
  by_cases h2 : f y = ⊤
  · rw [h2]; by_cases hb1 : b = 0
    · rw [hb1]; simp;
      have ha : a = 1 := by rwa [hb1, add_zero] at hab
      rw [ha]; simp
    have hb1 : b > 0 := by positivity
    simp; rw [EReal.coe_mul_top_of_pos hb1]
    rw [add_top_of_ne_bot (LT.lt.ne_bot <| mul_pos_gt_bot ha (hsf.1 x trivial))]; simp
  have hx : x ∈ dom univ f := by simp; exact Ne.lt_top' fun a ↦ h1 (id (Eq.symm a))
  have hy : y ∈ dom univ f := by simp; exact Ne.lt_top' fun a ↦ h2 (id (Eq.symm a))
  exact hf.2 hx hy ha hb hab

lemma convexOn_dom_s_f_of_convexOn_s {f : α → EReal} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (hf : ConvexOn ℝ univ f) : ConvexOn ℝ (dom univ f) f := by
  constructor
  · apply Convex.inter hf.1
    intro x hx y hy a b ha hb hab
    obtain hf2 := hf.2 (x := x) (y := y) trivial trivial ha hb hab
    suffices f (a • x + b • y) < ⊤ by exact this
    apply lt_of_le_of_lt hf2
    exact EReal.add_lt_top (mul_pos_lt_top ha hx).ne_top (mul_pos_lt_top hb hy).ne_top
  exact fun x _ y _ a b ha hb hab ↦ hf.2 (x := x) (y := y) trivial trivial ha hb hab

namespace Function

def toReal {α : Type*} (f : α → EReal) : α → ℝ :=
  fun x => (f x).toReal

end Function

lemma ProperFunctionConvexOn_iff_ConvexOn {α : Type*} [AddCommMonoid α] [SMul ℝ α]
    (s : Set α) (f : α → ℝ) : ConvexOn ℝ s f ↔ ConvexOn ℝ s (fun x => (f x).toEReal) :=
  ⟨fun h ↦ ⟨h.1, fun _ hx _ hy _ _ ha hb hab => EReal.coe_le_coe_iff.mpr <| h.2 hx hy ha hb hab⟩,
    fun h ↦ ⟨h.1, fun _ hx _ hy _ _ ha hb hab => EReal.coe_le_coe_iff.mp <| h.2 hx hy ha hb hab⟩⟩

instance (hsf : ProperFunction s f) (m : ℝ) (hm : m ≥ 0) : ProperFunction s (m • f) where
  uninfinity := by
    intro x hs
    simp only [Pi.smul_apply, gt_iff_lt]
    exact EReal.smul_gt_bot_of_ge_zero hm (hsf.1 x hs)
  existence_of_finite_value := by
    by_cases hs : s = ∅
    · left;exact hs
    right;
    rcases hsf.2 with hsw | ⟨x, hx⟩
    · exact False.elim (hs hsw)
    use x
    constructor
    · exact hx.1
    simp only [Pi.smul_apply]
    refine EReal.smul_lt_top_of_ge_zero hx.2 (hsf.1 x hx.1)

lemma ProperFunctionConvexOn.add {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {s : Set E} {f g : E → EReal}
    [hsf : ProperFunction s f] [hsg : ProperFunction s g]
    (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (f + g) :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ a • f x + b • f y + (a • g x + b • g y) :=
      add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    _ = a • (f x + g x) + b • (f y + g y) := by
      rw [EReal.smul_add a (hsf.uninfinity x hx) (hsg.uninfinity x hx),
        EReal.smul_add b (hsf.uninfinity y hy) (hsg.uninfinity y hy), add_add_add_comm]⟩

theorem ProperFunctionConvexOn.smul {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {s : Set E} {f : E → EReal} [hsf : ProperFunction s f]
    {c : ℝ} (hc : 0 ≤ c) (hf : ConvexOn ℝ s f) : ConvexOn ℝ s (c • f) :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      c • f (a • x + b • y) ≤ c • (a • f x + b • f y) :=by
        simp
        apply mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab)
        exact EReal.coe_nonneg.mpr hc
      _ = a • c • f x + b • c • f y := by
        rw [EReal.smul_add]
        · simp
          nth_rw 1[mul_left_comm]
          nth_rw 2[mul_left_comm]
        · simp only [gt_iff_lt]
          refine EReal.smul_gt_bot_of_ge_zero ha (hsf.1 x hx)
        refine EReal.smul_gt_bot_of_ge_zero hb (hsf.1 y hy)⟩

lemma ConvexOn.sum {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
    [AddCommMonoid α] [SMul 𝕜 α]
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {t : ι → α → 𝕜} {d : Set α}
    (h : ∀ i ∈ s, ConvexOn 𝕜 d (t i)) (hd : Convex 𝕜 d) :
    ConvexOn 𝕜 d (fun x => ∑ i ∈ s, t i x) := by
  induction s using Finset.induction with
  | empty =>
    apply convexOn_const AddMonoid.toZero.1 hd
  | insert i s hi hs =>
    have : (fun x ↦ ∑ i ∈ insert i s, t i x) = fun x ↦ (t i x) + ∑ i ∈ s, t i x := funext
      fun x ↦ Finset.sum_insert hi
    rw[this]
    apply ConvexOn.add (h i (Finset.mem_insert_self i s))
      <| hs (fun j hj => h j (Finset.mem_insert_of_mem hj))


instance ProperFun_of_subset {α : Type*} {s t : Set α} {f : α → EReal}
    {hsf : ProperFunction s f} (hs : t ⊆ (dom s f)) : ProperFunction t f where
  uninfinity := by
    intro x hx
    have h := hs hx
    simp only [dom, Set.mem_setOf_eq] at h
    exact hsf.uninfinity x h.1
  existence_of_finite_value := by
    by_cases ht : t = ∅
    · left; exact ht
    right;
    have ⟨x, hx⟩ := Set.nonempty_def.mp <| Set.nonempty_iff_ne_empty.mpr ht
    use x,hx
    exact x_dom_lt_top (hs hx)
-- #check ConvexOn ℝ s f
-- #check f.toReal

instance RealFun_is_ProperFun {α : Type*} {s : Set α} {f : α → ℝ} :
  ProperFunction s (fun x => f x) where
  uninfinity := fun x _ ↦ EReal.bot_lt_coe (f x)
  existence_of_finite_value := by
    by_cases hs : s.Nonempty
    · right;rcases hs with ⟨x ,hx⟩
      use x , hx
      exact EReal.coe_lt_top (f x)
    left;
    exact Set.not_nonempty_iff_eq_empty.mp hs

noncomputable instance ProperFunction.add {α : Type*} {s : Set α} {f g : α → EReal}
    [hsf : ProperFunction s f] [hsg : ProperFunction s g]
    (h : dom s f ∩ dom s g ≠ ∅) : ProperFunction s (f + g) where
  uninfinity := fun x hx => by
    simp
    exact ⟨hsf.uninfinity x hx , hsg.uninfinity x hx⟩
  existence_of_finite_value := by
    by_cases hs : s = ∅
    · left;exact hs
    right;
    have ⟨x, hxf, hxg⟩ := Set.nonempty_def.mp <| Set.nonempty_iff_ne_empty.mpr h
    use x
    exact ⟨hxf.1, EReal.add_lt_top (LT.lt.ne_top hxf.2) (LT.lt.ne_top hxg.2)⟩

instance ProperFunction.zero {α : Type*} (s : Set α) : ProperFunction s 0 where
  uninfinity := by simp
  existence_of_finite_value := by
    by_cases hs : s = ∅
    · exact Or.symm (Or.inr hs)
    right
    simp
    refine Set.nonempty_def.mp ?_
    exact Set.nonempty_iff_ne_empty.mpr hs

/-
dom ∑ f_i = ∩ dom(f_i)
Statement : the effective domain of the sum of `f_i` equals
the intersection of their effective domains
-/
theorem effective_domain_sum_eq_intersection {α : Type*}
    {s : Set α} {n : ℕ} [NeZero n] {f : Fin n → α → EReal}
    (hsf : ∀ i, ProperFunction s (f i)) : dom s (∑ i, f i) = ⋂ i, dom s (f i) := by
  ext x
  simp
  constructor
  · intro hx i
    constructor
    · exact hx.1
    let gn : Fin n → EReal := fun i => f i x
    have hx2 : ∑ c : Fin n, f c x = ∑ i, gn i := rfl
    rw[hx2] at hx
    suffices gn i < ⊤ by exact this
    refine EReal.lt_top_of_sum_lt_top (fun i => (hsf i).uninfinity x hx.1) hx.2 i
  intro hi
  let zero : Fin n := ⟨0, Nat.pos_of_neZero n⟩
  constructor
  · exact (hi zero).1
  refine EReal.sum_lt_top_of_lt_top ?h.mpr.right.hf
  exact fun i ↦ x_dom_lt_top (hi i)

theorem effective_domain_sum_eq_intersection_univ {α : Type*} {n : ℕ} {f : Fin n → α → EReal}
    (hsf : ∀ i, ProperFunction (Set.univ : Set α) (f i)) :
  (dom (Set.univ : Set α) (∑ i, f i)) = ⋂ i, dom (Set.univ : Set α) (f i) := by
  ext x
  simp
  constructor
  · intro hx i
    let gn : Fin n → EReal := fun i => f i x
    have hx2 : ∑ c : Fin n, f c x = ∑ i, gn i := rfl
    rw[hx2] at hx
    suffices gn i < ⊤ by exact this
    refine EReal.lt_top_of_sum_lt_top (fun i => (hsf i).uninfinity x trivial) hx i
  intro hi
  refine EReal.sum_lt_top_of_lt_top fun i ↦ hi i


noncomputable instance ProperFunction.sum {α : Type*} {s : Set α} {n : ℕ} {f : Fin n → α → EReal}
    (hsf : ∀ i, ProperFunction s (f i)) (h : ⋂ i, dom s (f i) ≠ ∅) :
    ProperFunction s (∑ i, f i) := by
  induction n with
  | zero =>
    simp;
    apply ProperFunction.zero
  | succ n nh =>
    rw[Fin.sum_univ_castSucc]
    have : ∃ x, (x ∈ (⋂ i, dom s (f i))) :=
      Set.nonempty_def.mp <| Set.nonempty_iff_ne_empty.mpr h
    let x := this.choose
    have hxi : x ∈ (⋂ i, dom s (f i)) := this.choose_spec
    have hxis : x ∈ s := by
      simp at hxi
      let zero : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      apply (hxi zero).1
    have hidti : ⋂ i : Fin n, dom s (f i.castSucc) ≠ ∅ := by
      refine Set.nonempty_iff_ne_empty.mp ?h.a
      use x
      apply Set.mem_iInter.mpr
      intro i
      have : ∀ (i : Fin (n + 1)), x ∈ dom s (f i) := by
        intro i
        apply hxi
        exact Set.mem_range_self i
      exact this i.castSucc
    letI : ProperFunction s (∑ i : Fin n, f i.castSucc) :=
      nh (fun i ↦ hsf i.castSucc) hidti
    have : dom s (∑ i : Fin n, f i.castSucc) ∩ dom s (f (Fin.last n)) ≠ ∅ := by
      -- apply nh
      induction n with
    | zero =>
      simp;
      refine Set.nonempty_iff_ne_empty.mp ?zero.a;
      use x
      simp;
      simp at hxi
      exact hxi 0
    | succ n _ =>
      refine Set.nonempty_iff_ne_empty.mp ?_
      use x
      rw[effective_domain_sum_eq_intersection (fun i ↦ hsf i.castSucc)]
      simp only [Set.mem_inter_iff, Set.mem_iInter]
      have := hxi
      simp only [Set.mem_iInter] at this
      exact ⟨fun i ↦ this i.castSucc, this (Fin.last (n + 1))⟩
    refine ProperFunction.add this


-- ConvexOn.sum' -> ProperFunctionConvexOn.sum
lemma ProperFunctionConvexOn.sum [AddCommMonoid α] [SMul ℝ α]
    {n : ℕ} {t : Fin n → α → EReal} {d : Set α}
    [hst : ∀ i, ProperFunction d (t i)]
    (hdti : ⋂ i, dom d (t i) ≠ ∅)
    (h : ∀ i, ConvexOn ℝ d (t i)) (hd : Convex ℝ d) :
    ConvexOn ℝ d (∑ i, t i) := by
  induction n with
  | zero =>
    simp;
    exact ⟨hd, fun x _ y _ a b _ _ _ => by simp⟩
  | succ n nh =>
    rw[Fin.sum_univ_castSucc]
    have ⟨x, hx⟩ : ∃ x , x ∈ ⋂ i, dom d (t i) :=
      Set.nonempty_def.mp <| Set.nonempty_iff_ne_empty.mpr hdti
    have hidti : ⋂ i : Fin n, dom d (t i.castSucc) ≠ ∅ := by
      refine Set.nonempty_iff_ne_empty.mp ?h.a
      use x
      apply Set.mem_iInter.mpr
      intro i
      simp only [Set.mem_iInter] at hx
      exact hx i.castSucc
    letI : ProperFunction d (∑ i : Fin n, t i.castSucc) :=
      ProperFunction.sum (fun i ↦ hst i.castSucc) hidti
    apply ProperFunctionConvexOn.add
    · apply nh hidti (fun i ↦ h i.castSucc)
    exact (h (Fin.last n))

lemma ProperFunctionConvexOn.sum' {α} [AddCommMonoid α] [SMul ℝ α]
    {τ : Finset ℕ} {t : τ → α → EReal} {d : Set α}
    [hst : ∀ i, ProperFunction d (t i)]
    (hdti : ⋂ i, dom d (t i) ≠ ∅)
    (h : ∀ i, ConvexOn ℝ d (t i)) (hd : Convex ℝ d) :
    ConvexOn ℝ d (∑ i, t i) := by
  induction τ using Finset.induction with
  | empty =>
    simp;
    exact ⟨hd, fun x _ y _ a b _ _ _ => by simp⟩
  | insert i s hi hs =>
    let t1 := fun i1 : { x // x ∈ s } ↦ t ⟨i1.1, by simp⟩
    suffices hp : ConvexOn ℝ d (∑ i1 : { x // x ∈ s }, t1 ⟨i1, by simp⟩ + t ⟨i, by simp⟩) by
      convert hp
      simp [hi]
      rw [add_comm]
    have hpro : ∀ (i : { x // x ∈ s }), ProperFunction d (t1 i) := by
      intro j
      simp [t1]; exact hst ⟨j.1, by simp⟩
    have hinter : ⋂ i, dom d (t1 i) ≠ ∅ := by
      refine Set.nonempty_iff_ne_empty.mp ?h.a
      obtain ⟨x1, hx1⟩ := Set.nonempty_def.mp <| Set.nonempty_iff_ne_empty.mpr hdti
      simp only [t1]; use x1
      apply Set.mem_iInter.mpr
      rw [Set.mem_iInter] at hx1
      intro j
      exact hx1 ⟨j, by simp⟩
    obtain hs1 := @hs t1 hpro hinter (fun i ↦ (h ⟨i, by simp⟩))
    haveI : ProperFunction d (∑ i1 : { x // x ∈ s }, t1 ⟨i1, by simp⟩) := by
      classical
      let n := Fintype.card { x // x ∈ s }
      let e : Fin n ≃ { x // x ∈ s } := (Fintype.equivFin _).symm
      let f : Fin n → α → EReal := fun j => t1 (e j)
      have hpro' : ∀ j : Fin n, ProperFunction d (f j) := by
        intro j
        simpa [f] using hpro (e j)
      have hinter' : ⋂ j, dom d (f j) ≠ ∅ := by
        refine Set.nonempty_iff_ne_empty.mp ?_
        obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hinter
        refine ⟨x, ?_⟩
        apply Set.mem_iInter.mpr
        intro j
        have hx' : ∀ i : { x // x ∈ s }, x ∈ dom d (t1 i) := by
          simpa [Set.mem_iInter] using hx
        simpa [f] using hx' (e j)
      haveI : ProperFunction d (∑ j, f j) := ProperFunction.sum hpro' hinter'
      have hfun :
          (∑ j, f j) = (∑ i1 : { x // x ∈ s }, t1 ⟨i1, by simp⟩) := by
        funext x
        have hsum : (∑ j, f j) x = (∑ i1 : { x // x ∈ s }, t1 i1) x := by
          simpa [f] using (Equiv.sum_comp e (fun i : { x // x ∈ s } => t1 i x))
        simpa using hsum
      simpa [hfun] using (show ProperFunction d (∑ j, f j) from inferInstance)
    apply ProperFunctionConvexOn.add hs1 (h ⟨i, by simp⟩)


noncomputable instance ProperFunction.congr {α : Type*} {s : Set α} {f g : α → EReal}
    {hsf : ProperFunction s f} (h : ∀ x ∈ s, f x = g x) : ProperFunction s g where
  uninfinity := by
    intro x hx
    rw[← h x hx]
    exact uninfinity x hx
  existence_of_finite_value := by
    by_cases hs : s = ∅
    · left; exact hs
    right;
    rcases hsf.existence_of_finite_value with hs1 | hs1
    · exact False.elim (hs hs1)
    rcases hs1 with ⟨x , hx, hx1⟩
    use x
    rw[h x hx] at hx1
    exact ⟨hx, hx1⟩

instance ProperFuntion.empty {α : Type*} {f : α → EReal} :
    ProperFunction ∅ f where
  uninfinity := by simp
  existence_of_finite_value := by simp

noncomputable instance {α : Type*} {s : Set α} {f g : α → EReal}
    [hsf : ProperFunction s f] [hsg : ProperFunction s g] :
    ProperFunction (dom s f ∩ dom s g) (f + g) := by
  by_cases h : (dom s f ∩ dom s g) = ∅
  · rw[h];exact ProperFuntion.empty
  refine { uninfinity := ?_, existence_of_finite_value := ?_ }
  · intro x hx
    simp at hx
    have h1 := hsf.uninfinity x hx.1.1
    have h2 := hsg.uninfinity x hx.1.1
    simp
    exact ⟨h1, h2⟩
  right;
  have ⟨x, hx⟩ : ∃ x , x ∈ dom s f ∩ dom s g := by
    refine Set.nonempty_def.mp ?_
    exact Set.nonempty_iff_ne_empty.mpr h
  use x,hx
  simp at hx
  simp
  have h1 := hx.1.2
  have h2 := hx.2.2
  refine EReal.add_lt_top ?right.hx ?right.hy
  · exact LT.lt.ne_top h1
  exact LT.lt.ne_top h2


lemma ProperFunction.real_dom_univ {α : Type*} (s : Set α) (g : α → ℝ) :
    (dom s fun x ↦ (g x)) = s := by
  ext x
  constructor
  · intro hx
    dsimp [dom] at hx
    exact hx.1
  intro hx
  dsimp[dom]
  exact ⟨hx, EReal.coe_lt_top (g x)⟩

noncomputable instance ProperFunction.add_real {α : Type*} {s : Set α} {f : α → EReal}
    (g : α → ℝ) [hsf : ProperFunction s f] :
    ProperFunction s (fun x => f x + g x) := by
  by_cases hs : s = ∅
  · constructor
    · intro x hx
      exfalso
      rw[hs] at hx
      exact hx
    left;
    exact hs
  apply ProperFunction.add
  rw[ProperFunction.real_dom_univ]
  simp[dom]
  rcases hsf.existence_of_finite_value with hs1 | hs1
  · exact fun _ ↦ hs hs1
  have ⟨x ,hx⟩ := hs1
  refine Set.Nonempty.ne_empty ⟨x, Set.mem_inter hx hx.1⟩

noncomputable instance ProperFunction.proper_of_dom {α : Type*} {s : Set α} {f : α → EReal}
    [hsf : ProperFunction s f] :
    ProperFunction (dom s f) f := by
  by_cases hdomsf: (dom s f) = ∅
  · constructor
    · intro x hx
      exfalso
      rw [hdomsf] at hx
      exact hx
    left;
    exact hdomsf
  apply ProperFun_of_subset
  · exact hsf
  simp

instance {f : E → EReal} {s : Set E} (hf : ∀ x ∈ s, ⊥ < f x ∧ f x < ⊤) :
    ProperFunction s f where
  uninfinity := fun x hx => (hf x hx).1
  existence_of_finite_value := by
    by_cases hs : s = ∅
    · left; exact hs
    have ⟨x, hx⟩: ∃ x, x ∈ s := nonempty_def.mp (nonempty_iff_ne_empty.mpr hs)
    right
    use x, hx
    exact (hf x hx).2

lemma neg_proper_of_top (h : ∀ x ∈ s, f x = ⊤) (hs : s ≠ ∅) : ¬ProperFunction s f := by
  rintro ⟨_, hf2 | ⟨x, hx, hfx⟩⟩
  · exact hs hf2
  rw[h x hx] at hfx
  exact (lt_self_iff_false ⊤).mp hfx

/-
If a non-proper function never attains -∞, then it is identically +∞.
-/
lemma top_of_ne_bot_of_ne_proper {s : Set E} {f : E → EReal}
    (hsf : ¬ProperFunction s f) (hf : ∀ x ∈ s, f x ≠ ⊥) (hx : x ∈ s) : f x = ⊤ := by
  contrapose! hsf
  refine (properFunction_iff s f).mpr ?_
  constructor
  · exact fun x a ↦ Ne.bot_lt' fun a_1 ↦ hf x a (id (Eq.symm a_1))
  right
  use x, hx
  exact Ne.lt_top' (id (Ne.symm hsf))

lemma exist_xs_lt_top [hsf : ProperFunction s f] (hs : s ≠ ∅) :
    ∃ x ∈ s , f x < ⊤  := by
  rcases hsf.2 with hss | hss
  · exact False.elim (hs hss)
  exact hss

section Convex
/-
An improper closed convex function takes no finite values.
-/
theorem ProperFuntion.conveximproper_nonfinte [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f : E → EReal}
    (hf : ConvexOn ℝ (dom s f) f) (hfcl : LowerSemicontinuousOn f s) (nhsf : ¬ProperFunction s f) :
    ∀ x ∈ s, ((f x = ⊤) ∨ (f x = ⊥)) := by
  intro x hx
  by_contra! hxor
  have ⟨y, hy⟩ : ∃ y ∈ s, f y = ⊥ := by
    by_contra! hy
    apply nhsf
    refine (properFunction_iff s f).mpr ?_
    constructor
    · exact fun x a ↦ Ne.bot_lt' fun a_1 ↦ hy x a (id (Eq.symm a_1))
    by_cases hs : s = ∅
    · rw[hs];simp
    right;
    use x, hx
    exact Ne.lt_top hxor.1

  rw[lowerSemicontinuousOn_iff_le_liminf] at hfcl

  let xn : ℕ → E := fun n => ((n : ℝ) / n.succ) •  x  + ((1 : ℝ) / n.succ) • y
  have limxn : Tendsto xn atTop (𝓝 x) := by
    rw[← add_zero x]
    simp only [xn]
    refine Tendsto.add ?hf ?hg
    nth_rw 2 [← one_smul ℝ x]
    apply Tendsto.smul
    simp
    apply tendsto_natCast_div_add_atTop 1
    exact tendsto_const_nhds
    rw[← zero_smul ℝ y]
    apply Tendsto.smul
    simp only [Nat.succ_eq_add_one,Nat.cast_add, Nat.cast_one]
    apply tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_const_nhds
  have xnins : ∀ n , xn n ∈ s := by
    intro n
    have : xn n ∈ dom s f := by
      apply hf.1 ⟨hx, Ne.lt_top hxor.1⟩ ⟨hy.1, by simp[hy]⟩
      repeat positivity; simp
      field_simp
    exact this.1
  have : liminf f (𝓝[s] x) ≤ ⊥ := by
    apply liminf_le_of_frequently_le'
    apply frequently_nhdsWithin_iff.mpr
    apply frequently_iff_seq_forall.mpr
    use xn
    constructor
    · exact limxn
    intro n
    constructor
    · simp only [xn]
      calc
       _ ≤ ((n : ℝ) / n.succ) * f x  + ((1 : ℝ) / n.succ) * f y  := by
        apply hf.2 ⟨hx, Ne.lt_top hxor.1⟩ ⟨hy.1, by simp[hy]⟩
        repeat positivity
        field_simp
        simp
       _ ≤ _ := by
        rw [hy.2]
        simp
        right
        refine mul_bot_of_pos <| EReal.coe_pos.mpr (by positivity)
    exact xnins n
  have : f x ≤ ⊥ := Preorder.le_trans (f x) (liminf f (𝓝[s] x)) ⊥ (hfcl x hx) this
  simp at this
  apply hxor.2 this

lemma convex_on_n_inf [NormedAddCommGroup E] [SMul ℝ E] {f : E → EReal}
    (h : (f : E → EReal) = (⊥ : E → EReal)) : ConvexOn ℝ univ f := by
  unfold ConvexOn
  apply And.intro
  intros x _ a _ ha hb _
  · simp
  intros x _ y _ a b _ _ _
  rw [h]; simp

lemma convex_on_n_inf' [NormedAddCommGroup E] [SMul ℝ E] {f : E → EReal}
    (h : ∀ x, f x = ⊥) : ConvexOn ℝ univ f := by
  apply convex_on_n_inf
  ext x; exact h x

lemma convex_on_p_top [NormedAddCommGroup E] [SMul ℝ E] {f : E → EReal}
    (h : f = (⊤ : E → EReal)) : ConvexOn ℝ univ f := by
  unfold ConvexOn
  apply And.intro
  intros x _ a _ ha hb _
  · simp
  intros x _ y _ a b ha hb hab
  rw [h]
  simp
  rcases lt_trichotomy a 0 with (ha_neg | ha_zero | ha_pos)
  -- a < 0
  · have : ¬a < 0 := by linarith [ha]
    contradiction
  -- a = 0
  · rw [ha_zero, EReal.coe_zero, zero_mul, zero_add]
    rw [ha_zero,zero_add] at hab
    rw [hab,EReal.coe_one,one_mul]
  -- a > 0
  rcases lt_trichotomy b 0 with (hb_neg | hb_zero | hb_pos)
  -- b < 0
  · have : ¬b < 0 := by linarith  [hb]
    contradiction
  -- b = 0
  · rw [hb_zero, EReal.coe_zero, zero_mul, add_zero]
    rw [hb_zero,add_zero] at hab
    rw [hab, EReal.coe_one,one_mul]
  -- b > 0
  rw [EReal.coe_mul_top_of_pos ha_pos, EReal.coe_mul_top_of_pos hb_pos]
  exact top_add_top

lemma convex_on_p_top' [NormedAddCommGroup E] [SMul ℝ E] {f : E → EReal}
    (h : ∀ x, f x = ⊤) : ConvexOn ℝ univ f := by
  apply convex_on_p_top
  ext x; exact h x

end Convex
