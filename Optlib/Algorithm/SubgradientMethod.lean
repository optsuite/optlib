/-
Copyright (c) 2024 Hongjia Chen, Chenyi Li, Wanyi He, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hongjia Chen, Chenyi Li, Wanyi He, Zaiwen Wen
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Order
import Optlib.Convex.Subgradient

/-!
# SubgradientMethod

## Main results

  This file mainly concentrates on the subgradient algorithm for
  unconstrained nonsmooth optimization problems.

  We prove the convergence rate with different kinds of step size.

-/

open Filter Topology Set InnerProductSpace Finset

/-! ### Convergence of Subgradient method -/

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {S :Set E} {f : E → ℝ} {g : E} {x : E}

variable {G : NNReal}

theorem bounded_subgradient_to_Lipschitz (hf : ConvexOn ℝ univ f) (hc : ContinuousOn f univ)
    (h : ∀ ⦃x : E⦄ , ∀ ⦃g⦄ , g ∈ SubderivAt f x → ‖g‖ ≤ G) :
    LipschitzWith G f := by
  intro x y
  have hx₂' : Nonempty (SubderivAt f x) := SubderivAt.nonempty hf hc x
  simp at hx₂'
  rcases hx₂' with ⟨gx, hx₁⟩
  have hx₃ : ‖gx‖ ≤ G := by rcases h hx₁ with hx; apply hx
  rcases hx₁ y with hx₂
  have hx₄ : f x - f y ≤ inner ℝ gx (x - y) := by
    rw [add_comm] at hx₂
    have : f x ≤ f y - inner ℝ gx (y - x) := le_sub_left_of_add_le hx₂
    rw [sub_eq_add_neg, ← inner_neg_right, neg_sub] at this
    exact sub_left_le_of_le_add this
  have hy₂' : Nonempty (SubderivAt f y) := SubderivAt.nonempty hf hc y
  simp at hy₂'
  rcases hy₂' with ⟨gy, hy₁⟩
  have hy₃ : ‖gy‖ ≤ G := by rcases h hy₁ with hy; apply hy
  rcases hy₁ x with hy₂
  have hy₄: f x - f y ≥ inner ℝ gy (x - y) := by
    calc
      _ ≥ f y + inner ℝ gy (x - y) - f y := by apply sub_le_sub_right hy₂
      _ = inner ℝ gy (x - y) := by ring
  have hG₁: ↑G = ENNReal.ofReal ↑G := by simp
  rw [edist_dist, edist_dist, hG₁]
  have hG₂ : ENNReal.ofReal (↑G * (dist x y)) = ENNReal.ofReal ↑G * ENNReal.ofReal (dist x y) := by
    apply ENNReal.ofReal_mul; simp
  rw[← hG₂]
  have hG₃ : 0 ≤ ↑G * dist x y := Right.mul_nonneg NNReal.zero_le_coe dist_nonneg
  apply (ENNReal.ofReal_le_ofReal_iff hG₃).mpr
  have h₁ : dist (f x) (f y) = |f x - f y| := rfl
  rw [h₁, dist_eq_norm x y]
  apply abs_le.mpr
  constructor
  · calc
      f x - f y ≥ inner ℝ gy (x - y) := hy₄
      _ ≥ - (‖gy‖ * ‖x - y‖) := by
        apply neg_le_of_neg_le
        rw  [← inner_neg_right, neg_sub, norm_sub_rev]
        apply real_inner_le_norm
      _ ≥ - (↑G * ‖x - y‖) := neg_le_neg (mul_le_mul_of_nonneg_right hy₃ (norm_nonneg _))
  · calc
      f x - f y ≤ inner ℝ gx (x - y) := hx₄
      _ ≤ ‖gx‖ * ‖x - y‖ := real_inner_le_norm _ _
      _ ≤ ↑G * ‖x - y‖ := mul_le_mul_of_nonneg_right hx₃ (norm_nonneg _)

omit [CompleteSpace E] in
theorem Lipschitz_to_bounded_subgradient (h : LipschitzWith G f ) :
    ∀ ⦃x : E⦄ , ∀ ⦃g⦄ , g ∈ SubderivAt f x → ‖g‖ ≤ G := by
  by_contra h₁
  push_neg at h₁
  rcases h₁ with ⟨x, g, h₂, h₃⟩
  let y : E := x + ((1 / ‖g‖) • g)
  have hy : y = x + ((1 / ‖g‖) • g) := by rfl
  rcases h₂ y with hy₂
  rw[LipschitzWith] at h
  have hg₁ : ‖g‖ ≠ 0 := by
    apply ne_of_gt (lt_of_le_of_lt _ h₃)
    simp only [NNReal.zero_le_coe]
  have hl : inner ℝ g (y - x) = ‖g‖ := by
    rw[hy ,add_comm, ← add_sub, sub_self, add_zero, inner_smul_right, inner_self_eq_norm_sq_to_K]
    field_simp
    norm_cast
  rw [hl] at hy₂
  have _ : f y - f x ≥ ‖g‖ := by
    calc
      _ ≥ f x + ‖g‖ - f x := by apply sub_le_sub_right hy₂
      _ = ‖g‖:= by ring
  rcases h x y with h₅
  have hG₁: ↑G = ENNReal.ofReal ↑G := by rw [ENNReal.ofReal_coe_nnreal]
  rw [edist_dist, edist_dist, hG₁] at h₅
  have hG₂ : ENNReal.ofReal (↑G * (dist x y)) = ENNReal.ofReal ↑G * ENNReal.ofReal (dist x y) := by
    apply ENNReal.ofReal_mul; simp
  rw[← hG₂] at h₅
  have hG₃ : 0 ≤ ↑G * dist x y := Right.mul_nonneg NNReal.zero_le_coe dist_nonneg
  have h₃' : dist (f x) (f y) ≤ ↑G * dist x y := (ENNReal.ofReal_le_ofReal_iff hG₃).mp h₅
  have h₁ : dist (f x) (f y) = |f x - f y| := by rfl
  rw[h₁, dist_eq_norm] at h₃'; nth_rw 2 [hy] at h₃'
  rw[sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_smul, abs_sub_comm] at h₃'
  have h₄' : f y - f x < ‖g‖:= by
    calc
      f y - f x ≤ |f y - f x|:= by apply le_abs_self
      _ ≤ ↑G * (‖1 / ‖g‖‖ * ‖g‖) := by apply h₃'
      _ = ↑G := by
        rw [Real.norm_eq_abs, one_div, abs_inv, ← abs_of_nonneg (norm_nonneg g), abs_abs]
        rw [inv_mul_cancel₀ (abs_ne_zero.mpr hg₁), mul_one]
      _ < ‖g‖ := by apply h₃
  linarith

/- Subgradient of `f` is bounded if and only if `f` is Lipschitz -/
theorem bounded_subgradient_iff_Lipschitz (hf : ConvexOn ℝ univ f) (hc : ContinuousOn f univ) :
    (∀ ⦃x : E⦄ , ∀ ⦃g⦄ , g ∈ SubderivAt f x → ‖g‖ ≤ G)  ↔ LipschitzWith G f :=
  ⟨bounded_subgradient_to_Lipschitz hf hc, Lipschitz_to_bounded_subgradient⟩

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {S :Set E} {f : E → ℝ} {g : E} {x : E}

variable (hf : ConvexOn ℝ univ f)

open Finset

class subgradient_method (f : E → ℝ) (x₀ : E) where
  (x g : ℕ → E)
  (a : ℕ → ℝ) (ha : ∀ n, a n > 0)
  (G : NNReal) (lipschitz : LipschitzWith G f)
  (initial : x 0 = x₀)
  (update : ∀ k, (x (k + 1)) = x k - a k • (g k))
  (hg : ∀ n, g n ∈ SubderivAt f (x n))

variable (xm x₀ : E) {alg : subgradient_method f x₀}

/- Convergence of general subgradient method -/
omit [CompleteSpace E] in
theorem subgradient_method_converge:
    ∀ k, 2 * ((Finset.range (k + 1)).sum alg.a) *
    (sInf {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x} - f xm)
    ≤ ‖x₀ - xm‖ ^ 2 + alg.G ^ 2 * (Finset.range (k + 1)).sum (fun i => alg.a i ^ 2) := by
  intro k
  have h' : ∀ ⦃x : E⦄ , ∀ ⦃g⦄ , g ∈ SubderivAt f x → ‖g‖ ≤ alg.G := Lipschitz_to_bounded_subgradient alg.lipschitz
  by_cases k₀ : k = 0
  · simp [k₀]
    rcases (alg.hg 0) xm with hk₀
    rcases h' (alg.hg 0) with h₀'
    rw [← mul_pow]
    apply le_trans _ (two_mul_le_add_sq _ _)
    rw [mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (show (0 : ℝ) ≤ 2 by positivity)
    rw [mul_comm, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (alg.ha 0))
    have : f (alg.x 0) - f xm ≤ - inner ℝ (alg.g 0) (xm - alg.x 0) := by
      simp; rw[add_comm]; apply hk₀
    apply le_trans this _
    rw [← inner_neg_right,neg_sub, alg.initial]
    apply le_trans (real_inner_le_norm _ _) _; rw [mul_comm]
    apply mul_le_mul_of_nonneg_left h₀' (norm_nonneg _)
  · have heq : (Set.range fun (x : Finset.range (k + 1)) => f (alg.x x)) =
        {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x} := by simp [Set.ext_iff]
    have h₁ :  ∀ ⦃i : ℕ⦄, i ≥ 0 ∧ i ≤ k → ‖alg.x (i+1) - xm‖ ^ 2 ≤ ‖alg.x i - xm‖ ^ 2 - 2 * alg.a i
        * (sInf {f (alg.x i) | i ∈ Finset.range (k + 1)} - f xm) + alg.G ^ 2 * alg.a i ^ 2 := by
      intro i ⟨ _ ,hi₂⟩
      rw [alg.update i, sub_right_comm, norm_sub_sq_real, norm_smul, mul_pow, sub_eq_add_neg]
      have : ‖alg.x i - xm‖ ^ 2 - 2 * alg.a i * (sInf {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) =
          x} - f xm) + ↑alg.G ^ 2 * alg.a i ^ 2 = ‖alg.x i - xm‖ ^ 2 + - (2 * alg.a i * (sInf {x | ∃ i ∈
          Finset.range (k + 1), f (alg.x i) = x} - f xm)) + ↑alg.G ^ 2 * alg.a i ^ 2 := by ring
      rw [this]
      have inq₁: ‖alg.a i‖ ^ 2 * ‖alg.g i‖ ^ 2 ≤ ↑alg.G ^ 2 * alg.a i ^ 2 := by
        rw[mul_comm]; simp
        rcases h' (alg.hg i) with hi
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        · nlinarith [hi, norm_nonneg (alg.g i), alg.G.2]
      have inq₂: 2 * alg.a i * (sInf {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x} - f xm)
          ≤ 2 * inner ℝ (alg.x i - xm) (alg.a i • alg.g i) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (show (0 : ℝ) ≤ 2 by positivity)
        rw [inner_smul_right]
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (alg.ha i))
        rcases (alg.hg i) xm with hxm
        calc
          _ = sInf (Set.range fun (x : Finset.range (k + 1)) => f (alg.x x)) - f xm := by rw [← heq]
          _ ≤ f (alg.x i) - f xm := by
            simp
            have : f (alg.x i) ∈ Set.range fun (x : Finset.range (k + 1)) => f (alg.x x) := by
              exact ⟨⟨i, Finset.mem_range.mpr (lt_of_le_of_lt hi₂ (Nat.lt_succ_self k))⟩, rfl⟩
            apply csInf_le _ this; apply Finite.bddBelow_range
          _ ≤ inner ℝ (alg.x i - xm) (alg.g i) := by
            simp; apply le_add_of_sub_left_le
            rw [sub_eq_add_neg, ← inner_neg_left, neg_sub, real_inner_comm]
            apply hxm
      rw [add_assoc, add_assoc]
      have hneg : -(2 * inner ℝ (alg.x i - xm) (alg.a i • alg.g i)) ≤
          -(2 * alg.a i * (sInf {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x} - f xm)) := by
        exact neg_le_neg inq₂
      linarith [hneg, inq₁]
    have h₁' : ∀ ⦃i : ℕ⦄, i ≥ 0 ∧ i ≤ k → alg.a i * (2 * (sInf {f (alg.x i) | i ∈ Finset.range (k +
        1)} - f xm)) ≤ ‖alg.x i - xm‖ ^ 2 - ‖alg.x (i+1) - xm‖ ^ 2 + alg.G ^ 2 * (alg.a i) ^ 2 := by
      intro i ⟨hi₁, hi₂⟩
      rcases h₁ ⟨hi₁, hi₂⟩ with hii
      have : 2 * (alg.a i) * (sInf {f (alg.x i) | i ∈ Finset.range (k + 1)} - f xm) ≤
          ‖alg.x i - xm‖ ^ 2 - ‖alg.x (i+1) - xm‖ ^ 2 + alg.G ^ 2 * (alg.a i) ^ 2:= by
        linarith [hii]
      rw [mul_assoc, mul_comm, mul_assoc, mul_comm _ 2] at this
      apply this
    have h₂ : (Finset.range (k + 1)).sum (fun i => (alg.a i) * (2 * (sInf {f (alg.x i) | i ∈
        Finset.range (k + 1)} - f xm))) ≤ (Finset.range (k + 1)).sum
        (fun i => ‖alg.x i - xm‖ ^ 2 - ‖alg.x (i+1) - xm‖ ^ 2 + alg.G ^ 2 * (alg.a i) ^ 2) := by
      apply Finset.sum_le_sum; intro i hi; apply h₁'
      constructor
      · simp
      · have : i < k + 1 := by
          apply Finset.mem_range.mp; apply hi
        apply (Nat.lt_add_one_iff).mp this
    rw [← sum_mul, ← mul_assoc, mul_comm _ 2, sum_add_distrib] at h₂
    rw [sum_range_sub' _, ← mul_sum, alg.initial] at h₂
    calc
      _ = (2 * Finset.sum (Finset.range (k + 1)) fun x => alg.a x) * (sInf {x | ∃ i ∈
          Finset.range (k + 1), f (alg.x i) = x} - f xm) := by simp
      _ ≤ ‖x₀ - xm‖ ^ 2 - ‖alg.x (k + 1) - xm‖ ^ 2 + ↑alg.G ^ 2 * Finset.sum (Finset.range
          (k + 1)) fun x => alg.a x ^ 2 := by apply h₂
      _ ≤ ‖x₀ - xm‖ ^ 2 + alg.G ^ 2 * Finset.sum (Finset.range (k + 1)) fun x => alg.a x ^ 2 := by simp

omit [CompleteSpace E] in
/-- convergence with fixed step size --/
theorem subgradient_method_fix_step_size {t : ℝ}
    (ha' : ∀ (n : ℕ), alg.a n = t) :
    ∀ (k : ℕ) , sInf {f (alg.x i) | i ∈ Finset.range (k + 1)} - f xm
      ≤ ‖x₀ - xm‖ ^ 2 / (2 * (k + 1) * t) + alg.G ^ 2 * t / 2 := by
  intro k
  have ht : t > 0 := by rw[← ha' 0]; apply alg.ha 0
  have h₁ : ∀ (k : ℕ), 2 * ((Finset.range (k + 1)).sum alg.a) *
      (sInf {f (alg.x i) | i ∈ Finset.range (k + 1)} - (f xm))
      ≤ ‖x₀ - xm‖ ^ 2 + alg.G ^ 2 * (Finset.range (k + 1)).sum (fun i => (alg.a i) ^ 2) := by
    apply subgradient_method_converge
  rcases h₁ k with hk
  simp [ha'] at hk
  have hpos :  2 * ((↑k + 1) * t) > 0 := by
    simp
    apply mul_pos _ ht
    · apply add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_one
  refine le_of_mul_le_mul_left ?_ hpos
  calc
    2 * ((↑k + 1) * t) * (sInf {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x} - f xm)
      = 2 * ((↑k + 1) * t) * (sInf {x | ∃ i < k + 1, f (alg.x i) = x} - f xm) := by simp
    _ ≤ ‖x₀ - xm‖ ^ 2 + ↑alg.G ^ 2 * ((↑k + 1) * t ^ 2) := by
      simpa [Nat.lt_add_one_iff] using hk
    _ = 2 * ((↑k + 1) * t) * (‖x₀ - xm‖ ^ 2 / (2 * (↑k + 1) * t) + ↑alg.G ^ 2 * t / 2) := by
      field_simp

omit [CompleteSpace E] in
/-- convergence with fixed $‖x^{i+1}-x^{i}‖$ --/
theorem subgradient_method_fixed_distance {s : ℝ} (hm : IsMinOn f univ xm)
   (ha' : ∀ (n : ℕ), alg.a n * ‖alg.g n‖ = s) (hs : s > 0):
    ∀ (k : ℕ) ,(sInf {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x}) - (f xm)
      ≤ alg.G * ‖x₀ - xm‖ ^ 2 / (2 * (k + 1) * s) + alg.G * s / 2 := by
  intro k
  have heq : (Set.range fun (x : Finset.range (k + 1)) => f (alg.x x)) =
      {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x} := by simp [Set.ext_iff]
  have hnek : Nonempty (Finset.range (k + 1)) := by
    exact ⟨⟨0, by simp⟩⟩
  obtain h' := Lipschitz_to_bounded_subgradient alg.lipschitz
  have h₁ :  ∀ ⦃i : ℕ⦄ , i ≥ 0 ∧ i ≤ k → ‖alg.x (i+1) - xm‖ ^ 2 ≤ ‖alg.x i - xm‖ ^ 2 - 2 * (alg.a i)
      * (sInf {f (alg.x i) | i ∈ Finset.range (k + 1)} - f xm) + ‖alg.a i‖ ^ 2 * ‖alg.g i‖ ^ 2:= by
    intro i ⟨_, hi₂⟩
    rw [alg.update i, sub_right_comm, norm_sub_sq_real, norm_smul,mul_pow, sub_eq_add_neg]
    have : ‖alg.x i - xm‖ ^ 2 - 2 * alg.a i * (sInf {x | ∃ i ∈ Finset.range (k + 1),
        f (alg.x i) = x} - f xm) + ‖alg.a i‖ ^ 2 * ‖alg.g i‖ ^ 2 = ‖alg.x i - xm‖ ^ 2 +
        -(2 * alg.a i * (sInf {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x} - f xm))
        + ‖alg.a i‖ ^ 2 * ‖alg.g i‖ ^ 2 := by ring
    rw [this]
    have inq₂: 2 * alg.a i * (sInf {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x} - f xm)
        ≤ 2 * inner ℝ (alg.x i - xm) (alg.a i • alg.g i) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (show (0 : ℝ) ≤ 2 by positivity)
      rw[inner_smul_right]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (alg.ha i))
      rcases (alg.hg i) xm with hxm
      calc
        _ = sInf (Set.range fun (x : Finset.range (k + 1)) => f (alg.x x)) - f xm := by rw [← heq]
        _ ≤ f (alg.x i)- f xm := by
          simp
          have : f (alg.x i) ∈ Set.range fun (x : Finset.range (k + 1)) => f (alg.x x) := by
            exact ⟨⟨i, Finset.mem_range.mpr (lt_of_le_of_lt hi₂ (Nat.lt_succ_self k))⟩, rfl⟩
          apply csInf_le _ this; apply Finite.bddBelow_range
        _ ≤ inner ℝ (alg.x i - xm) (alg.g i) := by
          simp; apply le_add_of_sub_left_le
          rw[sub_eq_add_neg, ← inner_neg_left, neg_sub, real_inner_comm]; apply hxm
    rw[add_assoc, add_assoc]
    have hneg : -(2 * inner ℝ (alg.x i - xm) (alg.a i • alg.g i)) ≤
        -(2 * alg.a i * (sInf {x | ∃ i ∈ Finset.range (k + 1), f (alg.x i) = x} - f xm)) := by
      exact neg_le_neg inq₂
    linarith [hneg]
  have h₁' :  ∀ ⦃i : ℕ⦄ , i ≥ 0 ∧ i ≤ k → alg.a i * (2 * (sInf {f (alg.x i) | i ∈ Finset.range (k + 1)}
       - f xm)) ≤ ‖alg.x i - xm‖ ^ 2 - ‖alg.x (i+1) - xm‖ ^ 2 + s ^ 2 := by
    intro i ⟨hi₁, hi₂⟩
    rcases h₁ ⟨hi₁, hi₂⟩ with hii
    calc
      _ ≤ ‖alg.x i - xm‖ ^ 2 - ‖alg.x (i + 1) - xm‖ ^ 2 + ‖alg.a i‖ ^ 2 * ‖alg.g i‖ ^ 2 := by
        linarith [hii]
      _ = ‖alg.x i - xm‖ ^ 2 - ‖alg.x (i + 1) - xm‖ ^ 2 + s ^ 2 := by
        simp; rw[← mul_pow, (ha' i)]
  have h₂ : (Finset.range (k + 1)).sum (fun i => (alg.a i) * (2 * (sInf {f (alg.x i) |
      i ∈ Finset.range (k + 1)} - f xm))) ≤ (Finset.range (k + 1)).sum
      (fun i => ‖alg.x i - xm‖ ^ 2 - ‖alg.x (i+1) - xm‖ ^ 2 + s ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    apply h₁'
    constructor
    · simp
    · have : i < k + 1 := Finset.mem_range.mp hi
      apply (Nat.lt_add_one_iff).mp this
  rw [← Finset.sum_mul, ← mul_assoc, mul_comm _ 2, Finset.sum_add_distrib] at h₂
  rw [Finset.sum_range_sub', alg.initial, Finset.sum_const] at h₂
  simp at h₂
  have hG : (NNReal.toReal alg.G) > 0 := by
      apply lt_of_lt_of_le _ (h' (alg.hg 0))
      have : alg.a 0 * ‖alg.g 0‖ > 0 := by rw[ha' 0]; apply hs
      apply (pos_iff_pos_of_mul_pos this).mp (alg.ha 0)
  have inq₁ : Finset.sum (Finset.range (k + 1)) (fun x => alg.a x) ≥ (k + 1) * (s / ↑alg.G) := by
    have : Finset.sum (range (k + 1)) (fun _ => s / (NNReal.toReal alg.G)) = (k + 1) * (s / ↑alg.G) := by
      rw [Finset.sum_const]; simp
    rw[← this]
    apply Finset.sum_le_sum
    intro i _
    rw [← (ha' i)]
    apply (div_le_iff₀ hG).mpr
    exact mul_le_mul_of_nonneg_left (h' (alg.hg i)) (le_of_lt (alg.ha i))
  have hpos₁ : (↑k + 1) * (s / ↑alg.G) > 0 := by
    apply mul_pos
    · apply add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_one
    · apply div_pos hs hG
  have hpos₁' : 2 * (↑k + 1) * (s / ↑alg.G) > 0 :=by
    rw [mul_assoc]
    apply mul_pos
    · linarith
    · apply hpos₁
  have h₂' : (2 * (k + 1) * (s / ↑alg.G)) * (sInf {x | ∃ i < k + 1, f (alg.x i) = x} - f xm) ≤
      ‖x₀ - xm‖ ^ 2 - ‖alg.x (k + 1) - xm‖ ^ 2 + (↑k + 1) * s ^ 2 := by
    have hnonneg : 0 ≤ sInf {x | ∃ i < k + 1, f (alg.x i) = x} - f xm := by
      apply le_sub_right_of_add_le; simp
      apply le_csInf
      · simp at heq
        rw[← heq]
        apply Set.range_nonempty
      · intro b hb
        simp at hb
        rcases hb with ⟨i , _ , hb₂⟩
        rw[← hb₂]
        simp[isMinOn_univ_iff] at hm
        rcases hm (alg.x i) with hmi
        apply hmi
    have hmul : (2 * (k + 1) * (s / ↑alg.G)) * (sInf {x | ∃ i < k + 1, f (alg.x i) = x} - f xm) ≤
        (2 * ∑ i ∈ Finset.range (k + 1), alg.a i) * (sInf {x | ∃ i < k + 1, f (alg.x i) = x} - f xm) := by
      refine mul_le_mul_of_nonneg_right ?_ hnonneg
      rw[mul_assoc]
      exact mul_le_mul_of_nonneg_left inq₁ (show (0 : ℝ) ≤ 2 by positivity)
    have h₂'' : (2 * ∑ i ∈ Finset.range (k + 1), alg.a i) *
        (sInf {x | ∃ i < k + 1, f (alg.x i) = x} - f xm) ≤
        ‖x₀ - xm‖ ^ 2 - ‖alg.x (k + 1) - xm‖ ^ 2 + (↑k + 1) * s ^ 2 := by
      simpa [Nat.lt_add_one_iff] using h₂
    exact le_trans hmul h₂''
  calc
    _= sInf {x | ∃ i < k + 1, f (alg.x i) = x} - f xm := by simp
    _ ≤ (‖x₀ - xm‖ ^ 2 - ‖alg.x (k + 1) - xm‖ ^ 2 + (k + 1) * s ^ 2) / (2 * (k + 1) * (s / alg.G)) := by
      apply (le_div_iff₀' hpos₁').mpr h₂'
    _ ≤ (‖x₀ - xm‖ ^ 2 + (↑k + 1) * s ^ 2) / (2 * (↑k + 1) * (s / ↑alg.G)) := by
      apply (div_le_div_iff_of_pos_right hpos₁').2
      simp
    _ = alg.G * ‖x₀ - xm‖ ^ 2 / (2 * (k + 1) * s) + alg.G * s / 2 := by
      field_simp


/-
  convergence with diminishing step size
-/

omit [CompleteSpace E] in
lemma subgradient_method_diminishing_step_size (hm : IsMinOn f univ xm)
    (ha' : Tendsto alg.a atTop (𝓝 0))
    (ha'' : Tendsto (fun (k : ℕ) => (Finset.range (k + 1)).sum alg.a) atTop atTop) :
    Tendsto (fun k => sInf {f (alg.x i) | i ∈ Finset.range (k + 1)}) atTop (𝓝 (f xm)) := by
  have h₁ : Tendsto (fun k => sInf {f (alg.x i) | i ∈ Finset.range (k + 1)} - f xm)
      atTop (𝓝 0) := by
    simp [tendsto_def]; simp [tendsto_def] at ha' ha''
    intro s hs
    simp [mem_nhds_iff,Metric.isOpen_iff] at hs ha'
    rcases hs with ⟨t, hs₁, hs₂, hs₀⟩
    rcases hs₂ 0 hs₀ with ⟨ε, εpos, hs₂₀⟩
    have ha₁ : ∃ a₁, ∀ (b : ℕ), a₁ ≤ b → ‖x₀ - xm‖ ^ 2 /
        (2 * (Finset.range (b + 1)).sum alg.a) < ε / 2 := by
      let A := (‖x₀ - xm‖ ^ 2 / ε) + 1
      let s := {x | x > ‖x₀ - xm‖ ^ 2 / ε}
      have : ∀ (b : ℝ), A ≤ b → b ∈ s := by
        intro b hb
        simp [s]; apply lt_of_lt_of_le _ hb; simp [A]
      rcases ha'' s A this with ⟨a_1, hasA⟩
      use a_1
      intro b hb
      rcases hasA b hb with hb'; simp [s] at hb'
      obtain h₂ := (div_lt_iff₀ εpos).mp hb'
      have hpos : 2 * Finset.sum (Finset.range (b + 1)) alg.a > 0 := by
        apply mul_pos
        · simp
        · apply Finset.sum_pos
          · intro i _
            apply (alg.ha i)
          · simp
      apply (div_lt_iff₀' hpos).mpr
      calc
        ‖x₀ - xm‖ ^ 2 < Finset.sum (Finset.range (b + 1)) alg.a * ε := by apply h₂
        _ = 2 * Finset.sum (Finset.range (b + 1)) alg.a * (ε / 2) := by
          field_simp
    have ha₂ : ∃ a₂, ∀ (b : ℕ), a₂ ≤ b → alg.G ^ 2 * (Finset.range (b + 1)).sum
        (fun i => (alg.a i) ^ 2) / (2 * (Finset.range (b + 1)).sum alg.a) < ε / 2 := by
      by_cases hG : ↑alg.G = 0
      · use 0; intro b _ ; rw[hG]; simp
        positivity
      · have hpos': (NNReal.toReal alg.G) ^ 2 > 0 := by
          apply (sq_pos_iff).mpr; simp[hG]
        let s := {x | |x| < ε / (2 * ↑alg.G ^ 2)}
        have c₁ : ∀ x_1 ∈ s, x_1 ∈ s := by simp
        have c₂ : ∀ x_1 ∈ s, ∃ ε, 0 < ε ∧ ∀ (x_2 : ℝ), dist x_2 x_1 < ε → x_2 ∈ s := by
          intro x₁ hx₁; simp [s] at hx₁
          use ((ε / (2 * ↑alg.G ^ 2)) -|x₁|) / 2
          constructor
          · apply div_pos
            · simp[hx₁]
            · simp
          · intro x₂ hx₂; simp [s]
            calc
              |x₂| ≤ |x₁| + dist x₂ x₁ := by
                rw [← Real.dist_0_eq_abs x₁, ← Real.dist_0_eq_abs x₂, dist_comm x₂ x₁]
                rw [dist_comm x₂ 0, dist_comm x₁ 0]
                apply dist_triangle
              _ < |x₁| + (ε / (2 * ↑alg.G ^ 2) - |x₁|) / 2 := by simp [hx₂]
              _ = (ε / (2 * ↑alg.G ^ 2) + |x₁|) / 2 := by
                field_simp; ring
              _ < (ε / (2 * ↑alg.G ^ 2) + ε / (2 * ↑alg.G ^ 2)) / 2 := by
                nlinarith [hx₁]
              _ = ε / (2 * ↑alg.G ^ 2) := by field_simp; ring
        have c₃ : 0 ∈ s := by
          simp [s]
          apply div_pos
          · apply εpos
          · apply mul_pos
            · simp
            · apply hpos'
        rcases ha' s s c₁ c₂ c₃ with ⟨a₂,ha₂⟩
        simp [s] at ha₂
        let A := (2 * alg.G ^ 2 * (Finset.range (a₂ + 1)).sum fun x => (alg.a x) ^ 2) / ε + 1
        let s₁ := {x | x > (2 * alg.G ^ 2 * (Finset.range (a₂ + 1)).sum fun x => (alg.a x) ^ 2) / ε}
        have : ∀ (b : ℝ), A ≤ b → b ∈ s₁ := by
          intro b hb; simp [s₁]; apply lt_of_lt_of_le _ hb; simp [A]
        rcases ha'' s₁ A this with ⟨a₁, hasA⟩
        use max a₁ (a₂ + 1); intro b hb
        have hba₁ : b ≥ a₁ := by
          apply le_trans _ hb; apply le_max_left
        have hba₂' : b ≥ a₂ + 1 := by
          apply le_trans _ hb; apply le_max_right
        have hba₂ : b ≥ a₂ := by
          apply le_trans _ hba₂'; linarith
        have hpos : 2 * Finset.sum (Finset.range (b + 1)) alg.a > 0 := by
          apply mul_pos
          · simp
          · apply Finset.sum_pos
            · intro i _; apply (alg.ha i)
            · simp
        have hpos'' : Finset.sum (Finset.range (b + 1)) alg.a > 0 := by
          apply Finset.sum_pos
          · intro i _; apply (alg.ha i)
          · simp
        have hposG : ↑alg.G ^ 2 * (ε / (2 * ↑alg.G ^ 2)) > 0 := by
          apply mul_pos
          · apply hpos'
          · apply div_pos
            · apply εpos
            · apply mul_pos
              · simp
              · apply hpos'
        calc
          _ = (↑alg.G ^ 2 * Finset.sum (Finset.range (a₂ + 1)) fun x => alg.a x ^ 2) /
                  (2 * Finset.sum (Finset.range (b + 1)) alg.a) + (↑alg.G ^ 2 * Finset.sum
                  (Finset.range (b - a₂)) fun x => alg.a (a₂ + 1 + x) ^ 2) /
                  (2 * Finset.sum (Finset.range (b + 1)) alg.a) := by
                field_simp
                obtain heq := Finset.sum_range_add (fun i => alg.a i ^ 2) (a₂ + 1) (b - a₂)
                have h₃' : (b + 1) = a₂ + 1 + (b - a₂) := by
                  rw[(Nat.add_comm a₂ 1), Nat.add_assoc, (Nat.add_sub_cancel' hba₂), Nat.add_comm]
                rw[h₃']; apply heq
          _ < ε / 4 + ε / 4 := by
            apply add_lt_add
            · rcases hasA b hba₁ with h₃; simp [s₁] at h₃
              obtain h₃₁ := (div_lt_iff₀ εpos).mp h₃
              obtain h₃₂ := (div_lt_iff₀' hpos'').mpr h₃₁
              have h₃₃ : (2 * ↑alg.G ^ 2 * Finset.sum (Finset.range (a₂ + 1)) (fun x => alg.a x ^ 2)) /
                  Finset.sum (Finset.range (b + 1)) alg.a / 4 < ε / 4 := by
                exact (div_lt_div_iff_of_pos_right zero_lt_four).2 h₃₂
              calc
                _ = (2 * ↑alg.G ^ 2 * Finset.sum (Finset.range (a₂ + 1)) fun x => alg.a x ^ 2) /
                      Finset.sum (Finset.range (b + 1)) alg.a / 4 := by field_simp;ring
                _ < ε / 4 := by exact h₃₃
            · apply (div_lt_iff₀ hpos).mpr
              calc
                _ ≤ ↑alg.G ^ 2 * Finset.sum (Finset.range (b - a₂)) (fun x => (ε / (2 * ↑alg.G ^ 2))
                      * alg.a (a₂ + 1 + x)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpos')
                    apply Finset.sum_le_sum; intro i _
                    have hposi : alg.a (a₂ + 1 + i) > 0 := by apply (alg.ha (a₂ + 1 + i))
                    rw [pow_two]
                    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hposi)
                    have : a₂ + 1 + i ≥ a₂ := by
                      rw[Nat.add_assoc]; apply Nat.le_add_right
                    rcases ha₂ (a₂ + 1 + i) this with hai₂
                    apply le_trans _ (le_of_lt hai₂); apply le_abs_self
                _ = ↑alg.G ^ 2 *  (ε / (2 * ↑alg.G ^ 2)) * Finset.sum (Finset.range (b - a₂))
                      fun x => alg.a (a₂ + 1 + x) := by
                    rw[mul_assoc]
                    apply (mul_eq_mul_left_iff).mpr
                    left
                    rw[← Finset.mul_sum]
                _ < ↑alg.G ^ 2 *  (ε / (2 * ↑alg.G ^ 2)) * Finset.sum (Finset.range (b + 1))
                      (fun x => alg.a x) := by
                    refine mul_lt_mul_of_pos_left ?_ hposG
                    obtain heq := Finset.sum_range_add (fun x => alg.a x) (a₂ + 1) (b - a₂)
                    have h₃' : (b + 1) = a₂ + 1 + (b - a₂) := by
                      rw [Nat.add_comm a₂, Nat.add_assoc, (Nat.add_sub_cancel' hba₂), Nat.add_comm]
                    rw [h₃', heq]
                    simp
                    apply Finset.sum_pos
                    · intro i _
                      apply (alg.ha i)
                    · simp
                _ = ε / 4 * (2 * Finset.sum (Finset.range (b + 1)) alg.a) := by
                  field_simp;ring
          _ = ε / 2 := by field_simp; ring
    rcases ha₁ with ⟨a₁,ha₁⟩; rcases ha₂ with ⟨a₂,ha₂⟩
    use max a₁ a₂
    intro b hb
    have hba₁: b ≥ a₁ :=by
      apply le_trans _ hb; apply le_max_left
    have hba₂: b ≥ a₂ :=by
      apply le_trans _ hb; apply le_max_right
    apply hs₁; apply hs₂₀; simp
    have hne: sInf {x | ∃ i < b + 1, f (alg.x i) = x} - f xm ≥ 0 := by
      have heq : (Set.range fun (x : Finset.range (b + 1)) => f (alg.x x)) =
          {x | ∃ i ∈ Finset.range (b + 1), f (alg.x i) = x} := by simp [Set.ext_iff]
      have hneb : Nonempty (Finset.range (b + 1)) := by
        exact ⟨⟨0, by simp⟩⟩
      apply le_sub_right_of_add_le
      simp
      apply le_csInf
      · simp at heq; rw[← heq]; apply Set.range_nonempty
      · intro b hb; simp at hb
        rcases hb with ⟨i , _ , hb₂⟩
        rw[← hb₂]; simp[isMinOn_univ_iff] at hm
        rcases hm (alg.x i) with hmi
        apply hmi
    have hne' : sInf {x | ∃ i ≤ b, f (alg.x i) = x} - f xm ≥ 0 := by
      simpa [Nat.lt_add_one_iff] using hne
    rw[(abs_of_nonneg hne')]
    have h₁ : ∀ (k : ℕ), 2 * ((Finset.range (k + 1)).sum alg.a) * (sInf {f (alg.x i) |
        i ∈ Finset.range (k + 1)} - (f xm)) ≤ ‖x₀ - xm‖ ^ 2 + alg.G ^ 2 *
        (Finset.range (k + 1)).sum (fun i => (alg.a i) ^ 2) := by
      apply subgradient_method_converge
    rcases h₁ b with hb₁
    rcases ha₁ b hba₁ with hba₁'
    rcases ha₂ b hba₂ with hba₂'
    have hpos : 2 * Finset.sum (Finset.range (b + 1)) alg.a > 0 := by
      apply mul_pos
      · simp
      · apply Finset.sum_pos
        · intro i _; apply (alg.ha i)
        · simp
    calc
      _ ≤ (‖x₀ - xm‖ ^ 2 + ↑alg.G ^ 2 * Finset.sum (Finset.range (b + 1)) fun i => alg.a i ^ 2)
            / (2 * Finset.sum (Finset.range (b + 1)) alg.a) := by
          apply (le_div_iff₀' hpos).mpr; simp at hb₁; apply hb₁
      _ = ‖x₀ - xm‖ ^ 2 / (2 * Finset.sum (Finset.range (b + 1)) alg.a) + (↑alg.G ^ 2 *
            Finset.sum (Finset.range (b + 1)) fun i => alg.a i ^ 2) /
            (2 * Finset.sum (Finset.range (b + 1)) alg.a) := by
          simp [add_div]
      _ < ε / 2 + ε / 2 := by
        apply add_lt_add; apply hba₁'; apply hba₂'
      _ = ε := by ring
  obtain h₁' := Filter.Tendsto.add_const (f xm) h₁
  simp at h₁'; simp; apply h₁'

end
