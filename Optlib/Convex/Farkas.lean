/-
Copyright (c) 2024 Shengyang Xu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengyang Xu, Chenyi Li
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Optlib.Differential.Calculation
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
    have htt : Finset.sum σ.attach (fun x => f x) = Finset.sum (attach σ) (fun x => c1 x • b x) := by
      simp [f]
    have h1 : ∀ i : σ, c1 i • b i = c i • b i := by intro i; simp [c1]
    have ht : Finset.sum σ.attach (fun x => f x) = Finset.sum (attach σ) (fun x => c x • b x) := by
      rw [← htt]; apply Finset.sum_congr; simp
      intro i _; simp [f, c1]
    nth_rw 1 [Finset.sum_attach] at htt
    rw [← ht, ← htt]
  simp; intro c cpos h
  let c1 : σ → ℝ := fun i => c i
  use c1; constructor
  · intro i _; exact cpos i
  let f : ℕ → EuclideanSpace ℝ (Fin n) := fun i ↦ (c i) • (b i)
  have : Finset.sum σ.attach (fun x => f x) = Finset.sum (attach σ) (fun x => c x • b x) := by
    simp [f]
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
  intro hmem
  exact Nat.lt_irrefl m (hm ⟨m, hmem⟩)

private lemma mem_lt_m {m i : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) : (i ∈ (τ ∪ σ)) → (i < m) := by
  intro iin; rw [hm]; apply Nat.lt_succ_of_le
  apply Finset.le_max' (τ ∪ σ) i iin

private lemma exist_of_mem_shift {x m : ℕ} {τ : Finset ℕ}:
    x ∈ (Finset.image (fun x => x + m) τ) → ∃ a : τ, x = a + m := by
  simp; intro a ain eq; use a; use ain; rw [← eq]

private lemma s_inter_t1_empty {m : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) : σ ∩ (Finset.image (fun x => x + m) τ) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x xin
  have hx : x ∉ σ := by
    apply shift_not_in; intro i
    calc
      i.1 < m := by apply mem_lt_m he hm; simp [i.2]
      m ≤ x := by
        rcases exist_of_mem_shift (Finset.mem_of_mem_inter_right xin) with ⟨a, _, aeq⟩; linarith
  exact hx (Finset.mem_of_mem_inter_left xin)

private lemma s_inter_t2_empty {m : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) : σ ∩ (Finset.image (fun x => x + 2 * m) τ) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x xin
  have hx : x ∉ σ := by
    apply shift_not_in; intro i
    calc
      i.1 < m := by apply mem_lt_m he hm; simp [i.2]
      m ≤ 2 * m := by linarith
      2 * m ≤ x := by
        rcases exist_of_mem_shift (Finset.mem_of_mem_inter_right xin) with ⟨a, _, aeq⟩; linarith
  exact hx (Finset.mem_of_mem_inter_left xin)

private lemma t1_inter_t2_empty {m : ℕ} {σ τ : Finset ℕ} (he : (τ ∪ σ).Nonempty)
    (hm : m = (Finset.max' (τ ∪ σ) he).succ) :
    (Finset.image (fun x => x + m) τ) ∩ (Finset.image (fun x => x + 2 * m) τ) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x xin
  have hx : x ∉ Finset.image (fun x => x + m) τ := by
    apply shift_not_in; intro i
    rcases exist_of_mem_shift (Finset.mem_of_mem_inter_right xin) with ⟨a, aeq⟩
    rcases exist_of_mem_shift i.2 with ⟨b, beq⟩
    calc
      i.1 < 2 * m := by
        rw [beq, two_mul]; apply Nat.add_lt_add_right; apply mem_lt_m he hm; simp
      2 * m ≤ x := by rw [aeq]; simp
  exact hx (Finset.mem_of_mem_inter_left xin)

lemma general_polyhedra_is_polyhedra_empty (τ σ : Finset ℕ) (he : ¬(τ ∪ σ).Nonempty) :
    ∀ (a : ℕ → EuclideanSpace ℝ (Fin n)), ∀ (b : ℕ → EuclideanSpace ℝ (Fin n)),
    ∃ μ c, {z | ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ z =
    Finset.sum univ (fun i ↦ lam i • a i) + Finset.sum univ (fun i ↦ mu i • b i)} =
    cone μ c := by
  simp at he
  rcases he with ⟨rfl, rfl⟩
  intro a b
  refine ⟨∅, fun _ => 0, ?_⟩
  ext x
  simp [cone, quadrant]
  constructor
  · intro hx; subst hx; refine ⟨⟨fun _ => 0, by simp⟩, rfl⟩
  · intro hx; simpa using hx.2.symm

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
    simpa [τ1, m] using s_inter_t1_empty (σ := σ) (τ := τ) he (m := m) rfl
  have mt2emp : σ ∩ τ2 = ∅ := by
    simpa [τ2, m] using s_inter_t2_empty (σ := σ) (τ := τ) he (m := m) rfl
  have t1t2emp : τ1 ∩ τ2 = ∅ := by
    simpa [τ1, τ2, m] using t1_inter_t2_empty (σ := σ) (τ := τ) he (m := m) rfl
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
    have eq1 : (∑ x : { x // x ∈ σ }, mu x • b x) = Finset.sum σ (fun x => w x • c x) := by
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j; simp [w, c, cσ]
    have eq2 : (∑ x : τ, (fun y => lamp y • cτ1 y) x) = Finset.sum τ1 (fun x => w x • c x) := by
      rw [shift_sum τ m (fun y => lamp y • cτ1 y)]
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j
      have hns : x.1 ∉ σ := by
        intro hs
        have : x.1 ∈ σ ∩ τ1 := by simp [hs]
        simp [mt1emp] at this
      simp [w, c, hns]
    have eq3 : (∑ x : τ, (fun y => lamn y • cτ2 y) x) = Finset.sum τ2 (fun x => w x • c x) := by
      rw [shift_sum τ (2 * m) (fun y => lamn y • cτ2 y)]
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j
      have hns : x.1 ∉ σ := by
        intro hs
        have : x.1 ∈ σ ∩ τ2 := by simp [hs]
        simp [mt2emp] at this
      have hnt : x.1 ∉ τ1 := by
        intro hs
        have : x.1 ∈ τ1 ∩ τ2 := by simp [hs]
        simp [t1t2emp] at this
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
    have eq1 : (∑ x : { x // x ∈ σ }, mu x • b x) = Finset.sum σ (fun x => w x • c x) := by
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j; simp [mu, c, cσ]
    have eq2 : (∑ x : τ, (fun y => lamp y • cτ1 y) x) = Finset.sum τ1 (fun x => w x • c x) := by
      rw [shift_sum τ m (fun y => lamp y • cτ1 y)]
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j
      have hns : x.1 ∉ σ := by
        intro hs
        have : x.1 ∈ σ ∩ τ1 := by simp [hs]
        simp [mt1emp] at this
      rcases exist_of_mem_shift x.2 with ⟨a, eq⟩
      have hin : x.1 - m ∈ τ := by rw [eq]; simp
      simp [lamp, c, hns, hin]; rw [eq]; simp
    have eq3 : (∑ x : τ, (fun y => lamn y • cτ2 y) x) = Finset.sum τ2 (fun x => w x • c x) := by
      rw [shift_sum τ (2 * m) (fun y => lamn y • cτ2 y)]
      nth_rw 2 [← Finset.sum_attach]; simp; congr
      ext x j
      have hns : x.1 ∉ σ := by
        intro hs
        have : x.1 ∈ σ ∩ τ2 := by simp [hs]
        simp [mt2emp] at this
      have hnt : x.1 ∉ τ1 := by
        intro hs
        have : x.1 ∈ τ1 ∩ τ2 := by simp [hs]
        simp [t1t2emp] at this
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
    ¬ (∃ (z : EuclideanSpace ℝ (Fin n)), (∀ i ∈ τ, inner ℝ (a i) z = (0 : ℝ))
    ∧ (∀ i ∈ σ, inner ℝ (b i) z ≥ (0 : ℝ)) ∧ (inner ℝ c z < (0 : ℝ))) := by
  constructor
  intro h; rcases h with ⟨lam, mu, ⟨h1, h2⟩⟩
  by_contra h3
  rcases h3 with ⟨z, ⟨h31, ⟨h32, h33⟩⟩⟩
  have : inner ℝ c z ≥ (0 : ℝ) := by
    calc
      _ = inner ℝ (Finset.sum univ (fun i ↦ lam i • a i)) z
          + inner ℝ (Finset.sum univ (fun i ↦ mu i • b i)) z := by rw [h2]; simp [inner_add_left]
      _ = Finset.sum univ (fun i ↦ inner ℝ (lam i • a i) z)
          + Finset.sum univ (fun i ↦ inner ℝ (mu i • b i) z) := by
        rw [sum_inner, sum_inner]
      _ = Finset.sum univ (fun i ↦ lam i * inner ℝ (a i) z)
          + Finset.sum univ (fun i ↦ mu i * inner ℝ (b i) z) := by
        congr; ext i; rw [inner_smul_left]; simp
        ext i; rw [inner_smul_left]; simp
      _ = Finset.sum univ (fun i ↦ mu i * inner ℝ (b i) z) := by simp [h31]
      _ ≥ 0 := by
        apply Finset.sum_nonneg; intro i _
        obtain h1i := h1 i; obtain h2i := h32 i i.2; positivity
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
    exact h1 ⟨lam, mu, cn1, cn2⟩
  obtain sep := geometric_hahn_banach_point_closed scon sc cn
  rcases sep with ⟨f, u, ⟨sep1, sep2⟩⟩
  have feq : ∃ d : EuclideanSpace ℝ (Fin n), ∀ x, f x = inner ℝ d x := by
    refine ⟨(toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f, ?_⟩
    intro x
    symm
    exact toDual_symm_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) (x := x) (y := f)
  rcases feq with ⟨d, feq⟩
  have uleq : u < 0 := by
    have : 0 ∈ S := by simp [S]; use 0; use 0; simp
    specialize sep2 0 this; rw [feq 0, inner_zero_right] at sep2; exact sep2
  have hc : inner ℝ c d < (0 : ℝ) := by
    rw [real_inner_comm, ← feq c]
    apply lt_trans sep1 uleq
  have hb : ∀ i : σ, inner ℝ (b i) d ≥ (0 : ℝ) := by
    intro i
    have : ∀ t > (0 : ℝ), (t • b i) ∈ S := by
      intro t ht
      simp only [S]; use 0; use (fun j ↦ if j = i then t else 0)
      constructor; intro j; by_cases h : j = i; simp [h]
      linarith; simp [h]; simp
    apply leq_tendsto_zero uleq
    intro t ht
    specialize sep2 (t • b i) (this t ht);
    rw [feq, inner_smul_right, real_inner_comm] at sep2; exact sep2
  have ha : ∀ i : τ, inner ℝ (a i) d = (0 : ℝ) := by
    intro i
    have : ∀ t : ℝ, (t • a i) ∈ S := by
      intro t
      simp only [S]; use (fun j ↦ if j = i then t else 0); use 0;
      constructor; intro _; simp; simp only [Pi.zero_apply, zero_smul, sum_const_zero,
        ite_smul]; simp
    rw [le_antisymm_iff]; constructor
    · apply geq_tendsto_zero uleq
      intro t _
      specialize sep2 (t • a i) (this t); rw [feq, inner_smul_right, real_inner_comm] at sep2
      linarith
    apply leq_tendsto_zero uleq
    intro t _
    specialize sep2 (t • a i) (this t); rw [feq, inner_smul_right, real_inner_comm] at sep2
    linarith
  apply absurd h
  push_neg; use d;
  constructor
  · intro i hi; specialize ha {val := i, property := hi}; simp [ha]
  constructor
  intro i hi; specialize hb {val := i, property := hi}; simp at hb; simp; exact hb
  exact hc
