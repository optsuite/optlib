/-
Copyright (c) 2024 Shengyang Xu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengyang Xu, Chenyi Li
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Optlib.Convex.ClosedCone

/-!
# Farkas

## Main results

This file contains the proof of the Farkas lemma.
$p$ and $q \in \mathbb{N}$ Given sets of vectors $ \{a_i \in \mathbb{R}^n | i = 1, 2, \ldots, p\} $
and $ \{b_i \in \mathbb{R}^n | i = 1, 2, \ldots, q\} $,
and a vector $ c \in \mathbb{R}^n $, the following conditions are equivalent:

1. There does not exist a vector $ d \in \mathbb{R}^n $ such that:
   - $ d^T a_i = 0 $ for all $ i = 1, 2, \ldots, p $
   - $ d^T b_i \geq 0 $ for all $ i = 1, 2, \ldots, q $
   - $ d^T c < 0 $

2. The vector $ c $ can be expressed as a linear combination of the vectors
   $ a_i $ and $ b_i $ with coefficients $ \lambda_i $ and $ \mu_i $, respectively, where:
   - $ \lambda_i $ can be any real number for all $ i = 1, 2, \ldots, p $
   - $ \mu_i \geq 0 $ for all $ i = 1, 2, \ldots, q $
   - $ c = \sum_{i=1}^p \lambda_i a_i + \sum_{i=1}^q \mu_i b_i $

-/

variable {τ σ : Finset ℕ} {n : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin n)}
variable {b : ℕ → EuclideanSpace ℝ (Fin n)} {c : EuclideanSpace ℝ (Fin n)}


open Finset InnerProductSpace BigOperators

lemma polyhedra_iff_cone {σ : Finset ℕ} : ∀ (b : ℕ → EuclideanSpace ℝ (Fin n)),
    {z | ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ mu i • b i)} = cone σ b := by
  intro b
  simp only [cone, quadrant]
  ext z; constructor
  · simp; intro c cpos h
    let c1 : ℕ → ℝ := fun i => if w : i ∈ σ then c {val := i, property := w} else 0
    use c1; constructor
    · intro i; simp [c1];
      by_cases ht : i ∈ σ
      simp [ht]; specialize cpos i ht; exact cpos; simp [ht]
    rw [h]
    let f : ℕ → EuclideanSpace ℝ (Fin n) := fun i ↦ (c1 i) • (b i)
    have htt : ∑ x ∈ σ.attach, f x = Finset.sum (attach σ) fun x => (c1 x • b x) := by simp [f]
    have h1 : ∀ i : σ, c1 i • b i = c i • b i := by intro i; simp [c1]
    have ht : ∑ x ∈ σ.attach, f x = Finset.sum (attach σ) fun x => (c x • b x) := by
      rw [← htt]; apply Finset.sum_congr; simp
      intro i _; simp [f, c1]
    nth_rw 1 [Finset.sum_attach] at htt
    rw [← ht, ← htt]
  simp; intro c cpos h
  let c1 : σ → ℝ := fun i => c i
  use c1; constructor
  · intro i _; exact cpos i
  let f : ℕ → EuclideanSpace ℝ (Fin n) := fun i ↦ (c i) • (b i)
  have : ∑ x ∈ σ.attach, f x = Finset.sum (attach σ) fun x => (c x • b x) := by simp [f]
  rw [← h]; simp [c1]; rw [← this, Finset.sum_attach]

private lemma leq_tendsto_zero {a x : ℝ} (ha : a < 0) (h : ∀ t > 0, t * x > a) : 0 ≤ x := by
  by_contra h'; push_neg at h';
  have : 2 * a / x > 0 := by
    rw [← mul_div]; apply mul_pos; norm_num; apply div_pos_of_neg_of_neg ha h'
  specialize h (2 * a / x) this
  have : 2 * a / x * x = 2 * a := by
    ring_nf; simp; field_simp; rw [← mul_div, div_self (by linarith)]; linarith
  rw [this] at h; linarith

private lemma geq_tendsto_zero {a x : ℝ} (ha : a < 0) (h : ∀ t < 0, t * x > a) : 0 ≥ x := by
  by_contra h'; push_neg at h';
  have : 2 * a / x < 0 := by
    rw [← mul_div]; apply mul_neg_of_pos_of_neg; norm_num; apply div_neg_of_neg_of_pos ha h'
  specialize h (2 * a / x) this
  have : 2 * a / x * x = 2 * a := by ring_nf; simp; field_simp;
  rw [this] at h; linarith

private lemma decompose_pn : ∀ (lam : τ → ℝ), ∃ (lamp lamn : ℕ → ℝ),
    ∀ i : τ, (0 ≤ lamp i) ∧ (0 ≤ lamn i) ∧ (lam i = (lamp i) - (lamn i)) := by
  intro lam
  let lamp : ℕ → ℝ := fun j => if h : (j ∈ τ) then if _ : (0 ≤ lam ⟨j, h⟩) then lam ⟨j, h⟩ else 0 else 0
  let lamn : ℕ → ℝ := fun j => if h : (j ∈ τ) then if _ : (0 ≤ lam ⟨j, h⟩) then 0 else -lam ⟨j, h⟩ else 0
  use lamp; use lamn
  intro i
  by_cases hpos : 0 ≤ lam i
  · simp [lamp, lamn, hpos]
  · simp [lamp, lamn, hpos]; linarith

private lemma shift_sum (τ : Finset ℕ) (m : ℕ) (f : ℕ → EuclideanSpace ℝ (Fin n)) :
    (∑ i : τ, f i) = (∑ i : (Finset.image (fun x => x + m) τ), f (i - m)) := by
  let h : ℕ → ℕ := fun i => i + m
  let g : ℕ → EuclideanSpace ℝ (Fin n) := fun i => f (i - m)
  have eq : f = g ∘ h := by ext i j; simp [g, h]
  have aux : ∀ x ∈ τ, ∀ y ∈ τ, h x = h y → x = y := by
    intro x _ y _; simp [h]
  show (∑ i : τ, f i) = (∑ i : (Finset.image h τ), g i); simp
  rw [Finset.sum_attach, Finset.sum_attach, Finset.sum_image aux, eq]; simp

private lemma shift_not_in (τ : Finset ℕ) (m : ℕ) (hm : ∀ i : τ, i < m): m ∉ τ := by
  contrapose hm; simp; simp at hm; use m

private lemma mem_lt_m {m i : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) : (i ∈ (τ ∪ σ)) → (i < m) := by
  intro iin; rw [hm]; apply Nat.lt_succ_of_le
  apply Finset.le_max' (τ ∪ σ) i iin

private lemma exist_of_mem_shift {x m : ℕ} {τ : Finset ℕ}:
    x ∈ (Finset.image (fun x => x + m) τ) → ∃ a : τ, x = a + m := by
  simp; intro a ain eq; use a; use ain; rw [← eq]

private lemma s_inter_t1_empty {m : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) : σ ∩ (Finset.image (fun x => x + m) τ) = ∅ := by
  by_contra neq; push_neg at neq; rw [← Finset.nonempty_iff_ne_empty] at neq
  rcases neq with ⟨x, xin⟩
  absurd Finset.mem_of_mem_inter_left xin
  apply shift_not_in; intro i
  calc
    i.1 < m := by apply mem_lt_m he hm; simp [i.2]
    m ≤ x := by
      rcases exist_of_mem_shift (Finset.mem_of_mem_inter_right xin) with ⟨a, _, aeq⟩; linarith

private lemma s_inter_t2_empty {m : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) : σ ∩ (Finset.image (fun x => x + 2 * m) τ) = ∅ := by
  by_contra neq; push_neg at neq; rw [← Finset.nonempty_iff_ne_empty] at neq
  rcases neq with ⟨x, xin⟩
  absurd Finset.mem_of_mem_inter_left xin
  apply shift_not_in; intro i
  calc
    i.1 < m := by apply mem_lt_m he hm; simp [i.2]
    m ≤ 2 * m := by linarith
    2 * m ≤ x := by
      rcases exist_of_mem_shift (Finset.mem_of_mem_inter_right xin) with ⟨a, _, aeq⟩; linarith

private lemma t1_inter_t2_empty {m : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) :
    (Finset.image (fun x => x + m) τ) ∩ (Finset.image (fun x => x + 2 * m) τ) = ∅ := by
  by_contra neq; push_neg at neq; rw [← Finset.nonempty_iff_ne_empty] at neq
  rcases neq with ⟨x, xin⟩
  absurd Finset.mem_of_mem_inter_left xin
  apply shift_not_in; intro i
  rcases exist_of_mem_shift (Finset.mem_of_mem_inter_right xin) with ⟨a, aeq⟩
  rcases exist_of_mem_shift i.2 with ⟨b, beq⟩
  calc
    i.1 < 2 * m := by
      rw [beq, two_mul]; apply Nat.add_lt_add_right; apply mem_lt_m he hm; simp
    2 * m ≤ x := by rw [aeq]; simp

lemma general_polyhedra_is_polyhedra_empty (τ σ : Finset ℕ) (he : ¬(τ ∪ σ).Nonempty) :
    ∀ (a : ℕ → EuclideanSpace ℝ (Fin n)), ∀ (b : ℕ → EuclideanSpace ℝ (Fin n)),
    ∃ μ c, {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)} =
    cone μ c := by
  simp at he; rw [← Finset.union_eq_empty] at he
  intro a b; simp
  use ∅; use (fun _ => 0)
  simp [cone, quadrant]; ext x; simp; constructor
  · intro a_1
    simp_all only [union_eq_empty, notMem_empty, IsEmpty.forall_iff, implies_true, true_and]
    obtain ⟨left, right⟩ := he
    obtain ⟨w, h⟩ := a_1
    obtain ⟨w_1, h⟩ := h
    subst h right left
    simp_all only [attach_empty, sum_empty, add_zero, and_true]
    apply Exists.intro
    · intro i
      rfl
  · intro a_1
    simp_all only [union_eq_empty, notMem_empty, IsEmpty.forall_iff, implies_true, true_and]
    obtain ⟨left, right⟩ := he
    obtain ⟨left_1, right_1⟩ := a_1
    obtain ⟨w, h⟩ := left_1
    subst right right_1 left
    simp_all only [attach_empty, sum_empty, add_zero, exists_const]

lemma general_polyhedra_is_polyhedra_ne (τ σ : Finset ℕ) (he : (τ ∪ σ).Nonempty) :
    ∀ (a : ℕ → EuclideanSpace ℝ (Fin n)), ∀ (b : ℕ → EuclideanSpace ℝ (Fin n)),
    ∃ μ c, {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)} =
    cone μ c := by
  intro a b
  let m := (Finset.max' (τ ∪ σ) he).succ
  let τ1 := Finset.image (fun x => x + m) τ
  let τ2 := Finset.image (fun x => x + 2 * m) τ
  let μ := σ ∪ τ1 ∪ τ2
  have mt1emp : σ ∩ τ1 = ∅ := by
    simp only [τ1]; apply s_inter_t1_empty he; simp; rfl
  have mt2emp : σ ∩ τ2 = ∅ := by
    simp only [τ2]; apply s_inter_t2_empty he; simp; rfl
  have t1t2emp : τ1 ∩ τ2 = ∅ := by
    simp only [τ1, τ2]; apply t1_inter_t2_empty he; simp; rfl
  have disj_st : Disjoint σ (τ1 ∪ τ2) := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_union_distrib_left]; simp [mt1emp, mt2emp]
  have disj_tt : Disjoint τ1 τ2 := by
    rw [Finset.disjoint_iff_inter_eq_empty]; simp [t1t2emp]
  let cσ : ℕ → EuclideanSpace ℝ (Fin n) := fun i => if i ∈ σ then b i else 0
  let cτ1 : ℕ → EuclideanSpace ℝ (Fin n) := fun i => if i ∈ τ then a i else 0
  let cτ2 : ℕ → EuclideanSpace ℝ (Fin n) := fun i => if i ∈ τ then -a i else 0
  let c : ℕ → EuclideanSpace ℝ (Fin n) := fun i => if i ∈ σ then cσ i else
      if i ∈ τ1 then cτ1 (i - m) else if i ∈ τ2 then cτ2 (i - 2 * m) else 0
  use μ; use c; simp only [cone, quadrant]; ext x; constructor
  · rintro ⟨lam, mu, munneg, xeq⟩
    obtain ⟨lamp, lamn, lameq⟩ := decompose_pn lam
    have tau_decpn : ∑ x : τ, lam x • a x =
        ∑ x : τ, (fun y => lamp y • cτ1 y) x + ∑ x : τ, (fun y => lamn y • cτ2 y) x := by
      have aux : ∑ x : τ, lam x • a x =
          ∑ x : τ, (lamp x • a x - lamn x • a x) := by
        congr; ext i j
        obtain ⟨_, _, eq⟩ := lameq i; simp; rw [eq, sub_mul]
      rw [aux]; simp [cτ1, cτ2]; rw [sub_eq_add_neg]
    simp
    let w : ℕ → ℝ := fun i => if h : i ∈ σ then mu ⟨i, h⟩ else
      if i ∈ τ1 then lamp (i - m) else if i ∈ τ2 then lamn (i - 2 * m) else 0
    have wnneg : ∀ i : ℕ, 0 ≤ w i := by
      intro i; simp [w]; by_cases hs : i ∈ σ
      · simp [hs]; linarith [munneg ⟨i, hs⟩]
      by_cases ht1 : i ∈ τ1
      · simp [hs, ht1]; simp [τ1] at ht1; rcases ht1 with ⟨a, ain, aeq⟩
        rw [← aeq]; simp; linarith [lameq ⟨a, ain⟩]
      by_cases ht2 : i ∈ τ2
      · simp [hs, ht1, ht2]; simp [τ2] at ht2; rcases ht2 with ⟨a, ain, aeq⟩
        rw [← aeq]; simp; linarith [lameq ⟨a, ain⟩]
      simp [hs, ht1, ht2]
    use w; use wnneg
    rw [xeq, tau_decpn]
    have eq1 : ∑ x : { x // x ∈ σ }, mu x • b x = ∑ x ∈ σ, (fun y => w y • c y) x := by
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j; simp [w, c, cσ]
    have eq2 : ∑ x : τ, (fun y => lamp y • cτ1 y) x = ∑ x ∈ τ1, (fun y => w y • c y) x := by
      rw [shift_sum τ m (fun y => lamp y • cτ1 y)]
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j
      have hns : x.1 ∉ σ := by
        contrapose mt1emp; simp at mt1emp; push_neg; rw [← Finset.nonempty_iff_ne_empty]
        use x; simp [τ1, mt1emp, x.2]
      simp [w, c, hns]
    have eq3 : ∑ x : τ, (fun y => lamn y • cτ2 y) x = ∑ x ∈ τ2, (fun y => w y • c y) x := by
      rw [shift_sum τ (2 * m) (fun y => lamn y • cτ2 y)]
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j
      have hns : x.1 ∉ σ := by
        contrapose mt2emp; simp at mt2emp; push_neg; rw [← Finset.nonempty_iff_ne_empty]
        use x; simp [τ2, mt2emp, x.2]
      have hnt : x.1 ∉ τ1 := by
        contrapose t1t2emp; simp at t1t2emp; push_neg; rw [← Finset.nonempty_iff_ne_empty]
        use x; simp [τ2, t1t2emp, x.2]
      simp [w, c, hns, hnt]
    rw [eq1, eq2, eq3]; simp [μ]
    rw [Finset.sum_union disj_st, Finset.sum_union disj_tt, add_comm]
  · intro cond; simp at cond; rcases cond with ⟨w, wnneg, xeq⟩
    simp [μ] at xeq
    rw [Finset.sum_union disj_st, Finset.sum_union disj_tt] at xeq
    let lamp : ℕ → ℝ := fun i => if i ∈ τ then w (i + m) else 0
    let lamn : ℕ → ℝ := fun i => if i ∈ τ then w (i + 2 * m) else 0
    let lam : τ → ℝ := fun i => lamp i.1 - lamn i.1
    let mu : ℕ → ℝ := fun i => if i ∈ σ then w i else 0
    have eq1 : ∑ x : { x // x ∈ σ }, mu x • b x = ∑ x ∈ σ, (fun y => w y • c y) x := by
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j; simp [mu, c, cσ]
    have eq2 : ∑ x : τ, (fun y => lamp y • cτ1 y) x = ∑ x ∈ τ1, (fun y => w y • c y) x := by
      rw [shift_sum τ m (fun y => lamp y • cτ1 y)]
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j
      have hns : x.1 ∉ σ := by
        contrapose mt1emp; simp at mt1emp; push_neg; rw [← Finset.nonempty_iff_ne_empty]
        use x; simp [τ1, mt1emp, x.2]
      rcases exist_of_mem_shift x.2 with ⟨a, eq⟩
      have hin : x.1 - m ∈ τ := by rw [eq]; simp
      simp [lamp, c, hns, hin]; rw [eq]; simp
    have eq3 : ∑ x : τ, (fun y => lamn y • cτ2 y) x = ∑ x ∈ τ2, (fun y => w y • c y) x := by
      rw [shift_sum τ (2 * m) (fun y => lamn y • cτ2 y)]
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j
      have hns : x.1 ∉ σ := by
        contrapose mt2emp; simp at mt2emp; push_neg; rw [← Finset.nonempty_iff_ne_empty]
        use x; simp [τ2, mt2emp, x.2]
      have hnt : x.1 ∉ τ1 := by
        contrapose t1t2emp; simp at t1t2emp; push_neg; rw [← Finset.nonempty_iff_ne_empty]
        use x; simp [τ2, t1t2emp, x.2]
      rcases exist_of_mem_shift x.2 with ⟨a, eq⟩
      have hin : x.1 - 2 * m ∈ τ := by rw [eq]; simp
      simp [lamn, c, hns, hnt, hin]; rw [eq]; simp
    rw [← eq1, ← eq2, ← eq3] at xeq; simp at xeq
    simp; use lam; use (fun i => mu i); constructor
    · intro a ain; simp [mu, ain]; linarith [wnneg a]
    · simp [lam]
      rw [← xeq, add_comm]; simp [cτ1, cτ2]; rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      congr; ext x j; rw [sub_smul]

lemma general_polyhedra_is_polyhedra (τ σ : Finset ℕ) :
    ∀ (a : ℕ → EuclideanSpace ℝ (Fin n)), ∀ (b : ℕ → EuclideanSpace ℝ (Fin n)),
    ∃ μ c, {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)} =
    cone μ c := by
  by_cases trivial : (τ ∪ σ).Nonempty
  · exact general_polyhedra_is_polyhedra_ne τ σ trivial
  · exact general_polyhedra_is_polyhedra_empty τ σ trivial

lemma general_polyhedra_is_closed : IsClosed {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ),
    (∀ i, 0 ≤ mu i) ∧ z = Finset.sum univ (fun i ↦ lam i • a i) +
    Finset.sum univ (fun i ↦ mu i • b i)} := by
  rcases general_polyhedra_is_polyhedra τ σ a b with ⟨μ, c, h⟩
  rw [h]; exact closed_conic μ c

theorem Farkas :
  (∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ c =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)) ↔
    ¬ (∃ (z : EuclideanSpace ℝ (Fin n)), (∀ i ∈ τ, inner (𝕜 := ℝ) (a i) z = (0 : ℝ))
    ∧ (∀ i ∈ σ, inner (𝕜 := ℝ) (b i) z ≥ (0 : ℝ)) ∧ (inner (𝕜 := ℝ) c z < (0 : ℝ))) := by
  constructor
  intro h; rcases h with ⟨lam, mu, ⟨h1, h2⟩⟩
  by_contra h3
  rcases h3 with ⟨z, ⟨h31, ⟨h32, h33⟩⟩⟩
  have : inner (𝕜 := ℝ) c z ≥ (0 : ℝ) := by
    classical
    have h31' : ∀ i : τ, inner (𝕜 := ℝ) (a i) z = 0 := fun i => h31 i i.2
    have h32' : ∀ i : σ, inner (𝕜 := ℝ) (b i) z ≥ 0 := fun i => h32 i i.2
    calc
      _ = inner (𝕜 := ℝ) (Finset.sum univ (fun i ↦ lam i • a i)) z
          + inner (𝕜 := ℝ) (Finset.sum univ (fun i ↦ mu i • b i)) z := by
        rw [h2]; simp [inner_add_left]
      _ = Finset.sum univ (fun i ↦ inner (𝕜 := ℝ) (lam i • a i) z)
          + Finset.sum univ (fun i ↦ inner (𝕜 := ℝ) (mu i • b i) z) := by
        rw [@sum_inner]; rw [@sum_inner]
      _ = Finset.sum univ (fun i ↦ lam i * inner (𝕜 := ℝ) (a i) z)
          + Finset.sum univ (fun i ↦ mu i * inner (𝕜 := ℝ) (b i) z) := by
        have hsumA :
            Finset.sum univ (fun i ↦ inner (𝕜 := ℝ) (lam i • a i) z)
          = Finset.sum univ (fun i ↦ lam i * inner (𝕜 := ℝ) (a i) z) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [inner_smul_left]
        have hsumB :
            Finset.sum univ (fun i ↦ inner (𝕜 := ℝ) (mu i • b i) z)
          = Finset.sum univ (fun i ↦ mu i * inner (𝕜 := ℝ) (b i) z) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [inner_smul_left]
        rw [hsumA, hsumB]
      _ = Finset.sum univ (fun i ↦ mu i * inner (𝕜 := ℝ) (b i) z) := by
        have hz : ∀ i : τ, lam i * inner (𝕜 := ℝ) (a i) z = 0 := by
          intro i; simp [h31' i]
        simp [hz]
      _ ≥ 0 := by
        apply Finset.sum_nonneg; intro i _
        have h1i := h1 i
        have h2i := h32' i
        positivity
  linarith
  intro h; by_contra h1
  let S := {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)}
  have sc : IsClosed S := by exact general_polyhedra_is_closed
  have scon : Convex ℝ S := by
    apply convex_iff_forall_pos.mpr
    intro x xs y ys a1 b1 anng bnng _
    rcases xs with ⟨sx, ⟨tx, ⟨txcond, eqx⟩⟩⟩
    rcases ys with ⟨sy, ⟨ty, ⟨tycond, eqy⟩⟩⟩
    use (a1 • sx + b1 • sy)
    use (a1 • tx + b1 • ty)
    constructor
    . show 0 ≤ (a1 • tx + b1 • ty)
      apply add_nonneg; apply smul_nonneg
      apply le_of_lt anng; apply txcond
      apply smul_nonneg; apply le_of_lt bnng
      apply tycond
    . rw [eqx, eqy, smul_add, smul_add]
      simp
      rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
      rw [add_assoc]; nth_rw 2 [add_comm]
      rw [← add_assoc, ← add_assoc, add_assoc]
      have aux1 : ((Finset.sum (attach τ) fun x => a1 • sx x • a ↑x) + Finset.sum (attach τ) fun x
        => b1 • sy x • a ↑x) = (Finset.sum (attach τ) fun x => (a1 * sx x + b1 * sy x) • a ↑x) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr
        simp; intro i _
        rw [smul_smul, smul_smul, ← add_smul]
      have aux2 : ((Finset.sum (attach σ) fun x => b1 • ty x • b ↑x) + Finset.sum (attach σ) fun x
        => a1 • tx x • b ↑x) = Finset.sum (attach σ) fun x => (a1 * tx x + b1 * ty x) • b ↑x := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr
        simp; intro i _
        rw [smul_smul, smul_smul, ← add_smul, add_comm]
      rw [aux1, aux2]
  have cn : c ∉ S := by
    by_contra cn; simp only [Set.mem_setOf_eq, S] at cn;
    rcases cn with ⟨lam, mu, ⟨cn1, cn2⟩⟩
    apply h1; use lam; use mu
  obtain sep := geometric_hahn_banach_point_closed scon sc cn
  rcases sep with ⟨f, u, ⟨sep1, sep2⟩⟩
  have feq : ∃ d : EuclideanSpace ℝ (Fin n), ∀ x, f x = inner (𝕜 := ℝ) d x := by
    refine ⟨((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f), ?_⟩
    intro x
    have h := (toDual ℝ (EuclideanSpace ℝ (Fin n))).apply_symm_apply f
    have hx := congrArg (fun g => g x) h
    simp
  rcases feq with ⟨d, feq⟩
  have uleq : u < 0 := by
    have : 0 ∈ S := by simp [S]; use 0; use 0; simp
    specialize sep2 0 this; rw [feq 0, inner_zero_right] at sep2; exact sep2
  have hc : inner (𝕜 := ℝ) c d < (0 : ℝ) := by
    rw [real_inner_comm, ← feq c]
    apply lt_trans sep1 uleq
  have hb : ∀ i : σ, inner (𝕜 := ℝ) (b i) d ≥ (0 : ℝ) := by
    intro i
    have : ∀ t > (0 : ℝ), (t • b i) ∈ S := by
      intro t ht
      simp only [S]; use 0; use (fun j ↦ if j = i then t else 0)
      constructor; intro j; by_cases h : j = i; simp [h]
      linarith; simp [h]; simp
    apply leq_tendsto_zero uleq
    intro t ht
    specialize sep2 (t • b i) (this t ht);
    rw [feq (t • b i), inner_smul_right, real_inner_comm] at sep2; exact sep2
  have ha : ∀ i : τ, inner (𝕜 := ℝ) (a i) d = (0 : ℝ) := by
    intro i
    have : ∀ t : ℝ, (t • a i) ∈ S := by
      intro t
      simp only [S]; use (fun j ↦ if j = i then t else 0); use 0;
      constructor; intro _; simp; simp only [Pi.zero_apply, zero_smul, sum_const_zero,
        ite_smul]; simp
    rw [le_antisymm_iff]; constructor
    · apply geq_tendsto_zero uleq
      intro t _
      specialize sep2 (t • a i) (this t); rw [feq (t • a i), inner_smul_right, real_inner_comm] at sep2
      linarith
    apply leq_tendsto_zero uleq
    intro t _
    specialize sep2 (t • a i) (this t); rw [feq (t • a i), inner_smul_right, real_inner_comm] at sep2
    linarith
  apply absurd h
  push_neg; use d;
  constructor
  · intro i hi; specialize ha {val := i, property := hi}; simp [ha]
  constructor
  intro i hi; specialize hb {val := i, property := hi}; simp at hb; simp; exact hb
  exact hc
