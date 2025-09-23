/-
Copyright (c) 2024 Yuxuan Wu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Wu, Chenyi Li
-/
import Optlib.Function.Proximal

/-!
# NesterovAccelerationFirst

## Main results

  This file mainly concentrates on the first version of Nesterov algorithm for composite optimization problems.

  We prove the O(1 / k ^ 2) rate for this algorithm.

-/

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

section Nesterov_first

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f h : E → ℝ} {f' : E → E} {x0 : E}

open Set Real

class Nesterov_first (f h: E → ℝ) (f' : E → E) (x0 : E) where
  (l : NNReal) (x y : ℕ → E) (t γ : ℕ → ℝ) (hl : l > (0 : ℝ))
  (h₁ : ∀ x : E, HasGradientAt f (f' x) x) (convf : ConvexOn ℝ univ f)
  (h₂ : LipschitzWith l f') (convh : ConvexOn ℝ univ h)
  (oriy : y 0 = x 0) (oriγ : γ 0 = 1) (initial : x 0 = x0)
  (cond : ∀ n : ℕ+, (1 - γ n) * t n / γ n ^ 2 ≤ t (n - 1) / γ (n - 1) ^ 2)
  (tbound : ∀ k : ℕ, 0 < t k ∧ t k ≤ 1 / l) (γbound : ∀ n : ℕ, 0 < γ n ∧ γ n ≤ 1)
  (update1 : ∀ k : ℕ+, y k = x k + (γ k * (1 - γ (k - 1)) / γ (k - 1)) • (x k - x (k - 1)))
  (update2 : ∀ k : ℕ, prox_prop (t k • h) (y k - t k • f' (y k)) (x (k + 1)))

variable {alg : Nesterov_first f h f' x0}
variable {xm : E}

theorem Nesterov_first_converge (minφ : IsMinOn (f + h) univ xm) :
    ∀ k, f (alg.x (k + 1)) + h (alg.x (k + 1)) -
    f xm - h xm ≤ (alg.γ k) ^ 2 / (2 * alg.t k) * ‖x0 - xm‖ ^ 2 := by
  have h1 : ∀ k : ℕ, alg.y k - alg.x (k + 1) - (alg.t k) • (f' (alg.y k))
      ∈ (SubderivAt ((alg.t k) • h) (alg.x (k + 1))) := by
    intro k
    let update2 := alg.update2 k
    rw [prox_iff_subderiv, sub_right_comm] at update2
    exact update2
    apply ConvexOn.smul; linarith [alg.tbound k]; exact alg.convh
  have hieq1 : ∀ z : E, ∀ k : ℕ, (alg.t k) * h (alg.x (k + 1))
      + ⟪alg.y k - alg.x (k + 1) - (alg.t k) • (f' (alg.y k)), z - alg.x (k + 1)⟫
      ≤ alg.t k * h z := by
    intro z k
    specialize h1 k
    rw [← mem_SubderivAt, HasSubgradientAt] at h1
    specialize h1 z; simp at h1; linarith [h1]
  have hieq2 : ∀ z : E, ∀ k : ℕ, h (alg.x (k + 1)) ≤ h z +
      ⟪(f' (alg.y k)) + (1 / alg.t k) • (alg.x (k + 1) - alg.y k), z - alg.x (k + 1)⟫ := by
    intro z k
    calc
      h (alg.x (k + 1)) = (1 / alg.t k) * (alg.t k * h (alg.x (k + 1))
          + ⟪alg.y k - alg.x (k + 1) - (alg.t k) • (f' (alg.y k)), z - alg.x (k + 1)⟫
          - ⟪alg.y k - alg.x (k + 1) - (alg.t k) • (f' (alg.y k)), z - alg.x (k + 1)⟫) := by
        rw [← add_sub, sub_self, add_zero, ← mul_assoc, one_div_mul_cancel]; simp
        linarith [(alg.tbound k).1]
      _ ≤ (1 / alg.t k) * (alg.t k * h z
          - ⟪alg.y k - alg.x (k + 1) - (alg.t k) • (f' (alg.y k)), z - alg.x (k + 1)⟫) := by
        rw [mul_le_mul_iff_right₀]; apply add_le_add_right; exact hieq1 z k
        simp; linarith [(alg.tbound k).1]
      _ = h z +
          ⟪(f' (alg.y k)) + (1 / alg.t k) • (alg.x (k + 1) - alg.y k), z - alg.x (k + 1)⟫ := by
        rw [sub_eq_add_neg, ← inner_neg_left, mul_add, ← mul_assoc, one_div_mul_cancel]
        simp; rw [← real_inner_smul_left, smul_sub, inv_smul_smul₀];
        rw [smul_sub, sub_sub_eq_add_sub, smul_sub, add_sub]
        repeat linarith [(alg.tbound k).1]
  have fieq1 : ∀ k : ℕ, ∀ x y : E,
      f x ≤ f y + ⟪f' y, x - y⟫ + 1 / (2 * alg.t k) * ‖x - y‖ ^ 2 := by
    intro k x y
    calc
      f x ≤ f y + ⟪f' y, x - y⟫
          + alg.l / 2 * ‖x - y‖ ^ 2 := by
        apply lipschitz_continuos_upper_bound' alg.h₁ alg.h₂ y x
      _ ≤ f y + ⟪f' y, x - y⟫ + 1 / (2 * alg.t k) * ‖x - y‖ ^ 2 := by
        apply add_le_add_left; apply mul_le_mul_of_nonneg_right
        rw [← mul_one_div, ← one_div_mul_one_div, mul_comm, mul_le_mul_iff_right₀]
        rw [le_one_div]; exact (alg.tbound k).2; exact alg.hl; exact (alg.tbound k).1
        simp; apply sq_nonneg
  let φ := fun z : E ↦ f z + h z
  have φieq2 : ∀ z : E, ∀ k : ℕ, φ (alg.x (k + 1)) ≤ φ z + (1 / alg.t k)
      * ⟪alg.x (k + 1) - alg.y k, z - alg.x (k + 1)⟫
      + (1 / (2 * alg.t k)) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
    intro z k
    calc
      _ ≤ f (alg.y k) + ⟪f' (alg.y k), alg.x (k + 1) - alg.y k⟫
          + 1 / (2 * alg.t k) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 + h (alg.x (k + 1)) := by
        apply add_le_add_right; exact fieq1 k (alg.x (k + 1)) (alg.y k)
      _ ≤ f (alg.y k) + ⟪f' (alg.y k), alg.x (k + 1) - alg.y k⟫
          + 1 / (2 * alg.t k) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 + h z
          + ⟪(f' (alg.y k)) + (1 / alg.t k) • (alg.x (k + 1) - alg.y k), z - alg.x (k + 1)⟫ := by
        rw [add_assoc _ (h z)]; apply add_le_add_left; exact hieq2 z k
      _ = f (alg.y k) + ⟪f' (alg.y k), z - alg.y k⟫
          + (1 / alg.t k) * ⟪alg.x (k + 1) - alg.y k, z - alg.x (k + 1)⟫
          + 1 / (2 * alg.t k) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 + h z := by
        rw [add_assoc _ _ (h z), add_right_comm, add_assoc _ _ (h z)]
        rw [add_right_cancel_iff, inner_add_left, ← add_assoc, add_assoc (f (alg.y k))]
        rw [← inner_add_right]; simp; rw [real_inner_smul_left]
      _ ≤ φ z + (1 / alg.t k) *
          ⟪alg.x (k + 1) - alg.y k, z - alg.x (k + 1)⟫
          + (1 / (2 * alg.t k)) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
        rw [add_comm _ (h z)]; repeat rw [← add_assoc]; repeat apply add_le_add_right
        simp [φ]; rw [add_comm _ (h z), add_assoc]; apply add_le_add_left
        apply Convex_first_order_condition'
        exact alg.h₁ (alg.y k); exact alg.convf; repeat simp
  have φieq3 (k : ℕ) : φ (alg.x (k + 1)) - φ xm - (1 - alg.γ k) * (φ (alg.x k) - φ xm) ≤
      1 / (alg.t k) * ⟪alg.x (k + 1) - alg.y k,
      (1 - alg.γ k) • (alg.x k) + (alg.γ k) • xm - alg.x (k + 1)⟫ +
      1 / (2 * alg.t k) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
    have ieq1 : φ (alg.x (k + 1)) ≤ φ (alg.x k) + (1 / (alg.t k))
        • ⟪alg.x (k + 1) - alg.y k, (alg.x k) - alg.x (k + 1)⟫
        + (1 / (2 * alg.t k)) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
      exact φieq2 (alg.x k) k
    have ieq2 : φ (alg.x (k + 1)) ≤ φ xm + (1 / (alg.t k))
        • ⟪alg.x (k + 1) - alg.y k, xm - alg.x (k + 1)⟫
        + (1 / (2 * alg.t k)) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
      exact φieq2 xm k
    rw [add_rotate, ← sub_le_iff_le_add] at ieq1; rw [add_rotate, ← sub_le_iff_le_add] at ieq2
    calc
      φ (alg.x (k + 1)) - φ xm - (1 - alg.γ k) * (φ (alg.x k) - φ xm) =
          (alg.γ k) * (φ (alg.x (k + 1)) - φ xm)
          + (1 - alg.γ k) * (φ (alg.x (k + 1)) - φ (alg.x k)) := by
        rw [mul_sub, mul_sub, mul_sub, sub_add_sub_comm, ← add_mul, add_comm (alg.γ k)]
        rw [sub_add_cancel, one_mul, ← sub_add, sub_add_eq_add_sub, sub_add]
        nth_rw 1 [← one_mul (φ xm)]; rw [← sub_mul, sub_sub_cancel, sub_sub]
      _ ≤ (alg.γ k) * ((1 / alg.t k) • ⟪alg.x (k + 1) - alg.y k, xm - alg.x (k + 1)⟫ +
          1 / (2 * alg.t k) * ‖alg.x (k + 1) - alg.y k‖ ^ 2) +
          (1 - alg.γ k) * ((1 / alg.t k) • ⟪alg.x (k + 1) - alg.y k, alg.x k - alg.x (k + 1)⟫ +
          1 / (2 * alg.t k) * ‖alg.x (k + 1) - alg.y k‖ ^ 2) := by
        apply add_le_add
        · rw [mul_le_mul_iff_right₀]; exact ieq2; linarith [(alg.γbound k).1]
        · apply mul_le_mul_of_nonneg_left; exact ieq1; linarith [(alg.γbound k).2]
      _ = (alg.γ k) * (1 / alg.t k) * ⟪alg.x (k + 1) - alg.y k, xm - alg.x (k + 1)⟫ +
          (1 - alg.γ k) * (1 / alg.t k) * ⟪alg.x (k + 1) - alg.y k, alg.x k - alg.x (k + 1)⟫ +
          1 / (2 * alg.t k) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
        rw [mul_add, mul_add, add_add_add_comm, ← add_mul, add_sub_cancel]
        rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, one_mul]
      _ = 1 / (alg.t k) * ⟪alg.x (k + 1) - alg.y k,
          (1 - alg.γ k) • (alg.x k) + (alg.γ k) • xm - alg.x (k + 1)⟫ +
          1 / (2 * alg.t k) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
        rw [add_right_cancel_iff, mul_comm (alg.γ k), mul_comm (1 - alg.γ k)]
        rw [mul_assoc, mul_assoc, ← mul_add, ← inner_smul_right, ← inner_smul_right]
        rw [← inner_add_right]
        rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, add_comm (alg.γ k)]
        rw [sub_add_cancel, one_smul, add_comm (alg.γ k • xm)]
  let v := fun k : ℕ+ ↦ alg.x (k - 1) + (1 / (alg.γ (k - 1))) • (alg.x k - alg.x (k - 1))
  have eq : ∀ k : ℕ+, alg.y k = (1 - alg.γ k) • alg.x k + (alg.γ k) • (v k) := by
    intro k
    simp [v]; rw [alg.update1 k, sub_smul, sub_add_eq_add_sub, ← smul_add, ← add_sub, one_smul]
    rw [add_left_cancel_iff, ← smul_sub, mul_div_assoc, ← smul_eq_mul, smul_assoc]
    have h2 : ((1 - alg.γ (k - 1)) / alg.γ (k - 1)) • (alg.x k - alg.x (k - 1)) =
        alg.x (k - 1) + (alg.γ (k - 1))⁻¹ • (alg.x k - alg.x (k - 1)) - alg.x k := by
      rw [sub_div, div_self, ← sub_add_eq_add_sub, sub_smul, one_smul, ← sub_add]
      rw [sub_add_comm]; simp
      linarith [(alg.γbound (k - 1)).1]
    rw [h2]
  have eq2 (k : ℕ) : 1 / (alg.t k) * ⟪alg.x (k + 1) - alg.y k,
      (1 - alg.γ k) • (alg.x k) + (alg.γ k) • xm - alg.x (k + 1)⟫
      + 1 / (2 * alg.t k) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 = 1 / (2 * alg.t k)
      * (‖alg.y k - (1 - alg.γ k) • (alg.x k) - (alg.γ k) • xm‖ ^ 2
      - ‖alg.x (k + 1) - (1 - alg.γ k) • (alg.x k) - (alg.γ k) • xm‖ ^ 2) := by
    have aux (a b : E) : 1 / (alg.t k) * ⟪a - b, -a⟫ +
        1 / (2 * alg.t k) * ‖a - b‖ ^ 2 = 1 / (2 * alg.t k) * (‖b‖ ^ 2 - ‖a‖ ^ 2) := by
      have h3 : 0 < 2 * alg.t k := by linarith [alg.tbound k]
      have h4 : 2 * alg.t k ≠ 0 := by linarith [alg.tbound k]
      have h5: alg.t k ≠ 0 := by linarith [alg.tbound k]
      rw [← mul_left_cancel_iff_of_pos h3, ← mul_assoc, mul_one_div_cancel h4]
      rw [mul_add, ← mul_assoc, ← mul_assoc, mul_one_div_cancel h4]
      rw [mul_assoc 2, mul_one_div_cancel h5, mul_one]; repeat rw [one_mul]
      rw [← inner_neg_neg]; simp; rw [← inner_smul_right, norm_sub_rev]
      rw [← real_inner_self_eq_norm_sq, ← inner_add_right, add_comm, two_smul, ← add_assoc]
      rw [sub_add_cancel, inner_sub_left, inner_add_right, inner_add_right]
      rw [real_inner_comm a b]; ring_nf; repeat rw [real_inner_self_eq_norm_sq]
    let a := alg.x (k + 1) - (1 - alg.γ k) • (alg.x k) - (alg.γ k) • xm
    let b := alg.y k - (1 - alg.γ k) • (alg.x k) - (alg.γ k) • xm
    have h7 : alg.x (k + 1) - alg.y k = a - b := by simp [a, b]
    have h8 : (1 - alg.γ k) • (alg.x k) + (alg.γ k) • xm - alg.x (k + 1) = -a := by
      simp [a]; rw [← sub_add, sub_add_comm, sub_add_eq_add_sub]
    rw [h7, h8]; exact aux a b
  have φieq4 (k : ℕ+) : φ (alg.x (k + 1)) - φ xm - (1 - alg.γ k) * (φ (alg.x k) - φ xm) ≤
      (alg.γ k) ^ 2 / (2 * alg.t k) * (‖v k - xm‖ ^ 2 - ‖v (k + 1) - xm‖ ^ 2) := by
    specialize φieq3 k; rw [eq2] at φieq3
    calc
      φ (alg.x (k + 1)) - φ xm - (1 - alg.γ k) * (φ (alg.x k) - φ xm) ≤ 1 / (2 * alg.t k) *
          (‖alg.y k - (1 - alg.γ k) • (alg.x k) - (alg.γ k) • xm‖ ^ 2
          - ‖alg.x (k + 1) - (1 - alg.γ k) • (alg.x k) - (alg.γ k) • xm‖ ^ 2) := φieq3
      _ = (alg.γ k) ^ 2 / (2 * alg.t k) * (‖v k - xm‖ ^ 2 - ‖v (k + 1) - xm‖ ^ 2) := by
        rw [eq k, add_sub_cancel_left, ← smul_sub, mul_sub, mul_sub, norm_smul, mul_pow, norm_eq_abs]
        rw [sq_abs, mul_left_comm, ← mul_assoc, mul_one_div]
        have h9 : 1 / (2 * alg.t k) * ‖alg.x (k + 1)
            - (1 - alg.γ k) • alg.x k - alg.γ k • xm‖ ^ 2 =
            alg.γ k ^ 2 / (2 * alg.t k) * ‖v (k + 1) - xm‖ ^ 2 := by
          simp [v]; rw [← mul_one_div, mul_assoc (alg.γ k ^ 2), mul_left_comm, ← sq_abs (alg.γ k)]
          rw [← norm_eq_abs, ← mul_pow, ← norm_smul, smul_sub, smul_add, smul_inv_smul₀]
          rw [← add_comm_sub, sub_smul, one_smul, ← sub_add, sub_add_comm]; simp
          linarith [(alg.γbound k).1]
        linarith [h9]
  let α := fun k : ℕ ↦ (2 * alg.t k) / (alg.γ k) ^ 2
  have αpos : ∀ n : ℕ, 0 < α n := by
    intro n; apply div_pos; linarith [alg.tbound n]
    rw [sq_pos_iff]; linarith [(alg.γbound n).1]
  have cond' : ∀ n : ℕ+, (1 - alg.γ n) * α n ≤ α (n - 1) := by
    intro n
    let cond := alg.cond n
    simp [α]
    rw [mul_div_assoc, mul_div_assoc, ← mul_assoc, mul_comm _ 2, mul_assoc, mul_le_mul_iff_right₀]
    rw [← mul_div_assoc]; exact cond; simp
  have h10 (n : ℕ) : α n * (alg.γ n ^ (2 : ℕ) / (2 * alg.t n)) = 1 := by
    have hγnz : alg.γ n ^ 2 ≠ 0 := by
      have hγpos : 0 < alg.γ n := (alg.γbound n).1
      exact ne_of_gt (pow_pos hγpos 2)
    have htnz : 2 * alg.t n ≠ 0 := by
      have htpos : 0 < alg.t n := (alg.tbound n).1
      exact ne_of_gt (by linarith [htpos])
    simp [α, pow_two, mul_comm, mul_left_comm, mul_div_mul_comm]; aesop
  have decrease (n : ℕ+) : (α n) * (φ (alg.x (n + 1)) - φ xm) + ‖v (n + 1) - xm‖ ^ 2 ≤
      (α (n - 1)) * (φ (alg.x n) - φ xm) + ‖v n - xm‖ ^ 2 := by
    calc
      (α n) * (φ (alg.x (n + 1)) - φ xm) + ‖v (n + 1) - xm‖ ^ 2 =
          (α n) * (φ (alg.x (n + 1)) - φ xm - (1 - alg.γ n) * (φ (alg.x n) - φ xm) +
          (1 - alg.γ n) * (φ (alg.x n) - φ xm)) + ‖v (n + 1) - xm‖ ^ 2 := by
        rw [sub_add_cancel]
      _ ≤ (α n) * ((alg.γ n) ^ 2 / (2 * alg.t n)
          * (‖v n - xm‖ ^ 2 - ‖v (n + 1) - xm‖ ^ 2))
          + (α n) * ((1 - alg.γ n) * (φ (alg.x n) - φ xm)) + ‖v (n + 1) - xm‖ ^ 2 := by
        rw [mul_add]; repeat apply add_le_add_right
        rw [mul_le_mul_iff_right₀]; exact φieq4 n; exact αpos n
      _ = ‖v n - xm‖ ^ 2 - ‖v (n + 1) - xm‖ ^ 2 +
          (α n) * ((1 - alg.γ n) * (φ (alg.x n) - φ xm)) + ‖v (n + 1) - xm‖ ^ 2 := by
        rw [← mul_assoc, h10, one_mul]
      _ ≤ ‖v n - xm‖ ^ 2 - ‖v (n + 1) - xm‖ ^ 2 +
          (α (n - 1)) * (φ (alg.x n) - φ xm) + ‖v (n + 1) - xm‖ ^ 2 := by
        apply add_le_add_right; apply add_le_add_left
        rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right; rw [mul_comm]
        exact cond' n
        simp
        rw [isMinOn_iff] at minφ
        specialize minφ (alg.x n)
        simp at minφ; exact minφ
      _ = (α (n - 1)) * (φ (alg.x n) - φ xm) + ‖v n - xm‖ ^ 2 := by
        rw [add_comm _ (α (↑n - 1) * (φ (alg.x ↑n) - φ xm)), add_assoc, sub_add_cancel]
  let nr := fun n : ℕ ↦ α n * (φ (alg.x (n + 1)) - φ xm)
      + ‖v (Nat.toPNat' (n + 1)) - xm‖ ^ 2
  have nrdiff (n : ℕ+) : nr n - nr (n - 1) ≤ 0 := by
    specialize decrease n; simp [nr]; rw [Nat.sub_add_cancel]; simp
    exact decrease; apply PNat.one_le
  intro k
  have bound : nr k - nr 0 ≤ 0 := by
    rw [← Finset.sum_range_sub]
    apply Finset.sum_nonpos
    intro i _; specialize nrdiff (Nat.toPNat' (i + 1))
    simp at nrdiff; simp; exact nrdiff
  rw [sub_nonpos] at bound
  calc
    f (alg.x (k + 1)) + h (alg.x (k + 1)) - f xm - h xm =
        alg.γ k ^ 2 / (2 * alg.t k) * ((α k) * (φ (alg.x (↑k + 1))- φ xm)) := by
      rw [sub_sub, ← mul_assoc, mul_comm _ (α k), h10 k]; simp; grind
    _ ≤ alg.γ k ^ 2 / (2 * alg.t k) * nr k := by
      rw [mul_le_mul_iff_right₀]; simp [nr]; apply div_pos
      rw [sq_pos_iff]; linarith [(alg.γbound k).1]; linarith [alg.tbound k]
    _ ≤ alg.γ k ^ 2 / (2 * alg.t k) * nr 0 := by
      rw [mul_le_mul_iff_right₀]; exact bound; apply div_pos
      rw [sq_pos_iff]; linarith [(alg.γbound k).1]; linarith [alg.tbound k]
    _ ≤ alg.γ k ^ 2 / (2 * alg.t k) * ‖x0 - xm‖ ^ 2 := by
      rw [mul_le_mul_iff_right₀]; simp [nr, v, α]; rw [alg.oriγ]; simp
      specialize φieq3 0; rw [alg.oriγ] at φieq3; simp at φieq3
      calc
        2 * alg.t 0 * (φ (alg.x 1) - φ xm) + ‖alg.x 1 - xm‖ ^ 2 ≤ 2 * alg.t 0
            * ((alg.t 0)⁻¹ * ⟪alg.x 1 - alg.y 0, xm - alg.x 1⟫
            + (alg.t 0)⁻¹ * 2⁻¹ * ‖alg.x 1 - alg.y 0‖ ^ 2 + φ xm - φ xm)
            + ‖alg.x 1 - xm‖ ^ 2 := by
          apply add_le_add_right; rw [mul_le_mul_iff_right₀]; simp; linarith [φieq3]
          linarith [alg.tbound 0]
        _ = ‖alg.x 0 - xm‖ ^ 2 := by
          rw [← add_sub, sub_self, add_zero, mul_add, ← mul_assoc]; ring_nf
          rw [mul_inv_cancel₀, one_mul, one_mul, alg.oriy, norm_sub_rev (alg.x 1) xm]
          rw [add_comm (⟪alg.x 1 - alg.x 0, xm - alg.x 1⟫ * 2), mul_comm, ← norm_add_sq_real]
          simp; rw [norm_sub_rev]; linarith [alg.tbound 0]
      rw [alg.initial]; apply div_pos; rw [sq_pos_iff]
      linarith [(alg.γbound k).1]; linarith [alg.tbound k]

end Nesterov_first

section Nesterov_first_fix_stepsize

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f h : E → ℝ} {f' : E → E} {x0 : E}

open Set Real PNat

class Nesterov_first_fix_stepsize (f h: E → ℝ) (f' : E → E) (x0 : E) where
  (l : NNReal) (hl : l > (0 : ℝ))
  (h₁ : ∀ x : E, HasGradientAt f (f' x) x) (convf: ConvexOn ℝ univ f)
  (h₂ : LipschitzWith l f') (convh : ConvexOn ℝ univ h)
  (x y : ℕ → E) (t γ : ℕ → ℝ) (oriy : y 0 = x 0) (initial : x 0 = x0)
  (teq : ∀ n : ℕ, t n = 1 / l) (γeq : ∀ n : ℕ, γ n = 2 / (2 + n))
  update1 : ∀ (k : ℕ+), y k = x k + (γ k * (1 - γ (k - 1)) / (γ (k - 1))) • (x k - x (k - 1))
  update2 : ∀ k:ℕ, prox_prop (t k • h) (y k - t k • f' (y k)) (x (k + 1))

instance {f h: E → ℝ} {f' : E → E} {x0 : E} [p : Nesterov_first_fix_stepsize f h f' x0] :
    Nesterov_first f h f' x0 where
  l := p.l
  h₁ := p.h₁
  convf := p.convf
  h₂ := p.h₂
  convh := p.convh
  x := p.x; y := p.y; t := p.t; γ := p.γ;
  oriy := p.oriy
  oriγ := by simp [p.γeq 0]
  initial := p.initial
  cond := by
    intro n; simp [p.teq n, p.teq (n - 1), p.γeq n, p.γeq (n - 1)]; field_simp
    ring_nf
    norm_num
  tbound := by
    intro k; rw [p.teq k]; simp; exact p.hl
  hl := p.hl
  γbound := by
    intro k; rw [p.γeq k]; constructor
    · apply div_pos; repeat linarith
    · rw [div_le_one]; repeat linarith
  update1 := p.update1
  update2 := p.update2

variable {alg : Nesterov_first_fix_stepsize f h f' x0}

variable {xm : E} (minφ : IsMinOn (f + h) univ xm)

theorem Nesterov_first_fix_stepsize_converge (minφ : IsMinOn (f + h) univ xm):
    ∀ (k : ℕ), f (alg.x (k + 1)) + h (alg.x (k + 1)) - f xm - h xm ≤
    2 * alg.l / (k + 2) ^ 2 * ‖x0 - xm‖ ^ 2 := by
  intro k
  calc
    f (alg.x (k + 1)) + h (alg.x (k + 1)) - f xm - h xm ≤
        (alg.γ k) ^ 2 / (2 * alg.t k) * ‖x0 - xm‖ ^ 2 := by
      have h1 :
        f (Nesterov_first_fix_stepsize.x f h f' x0 (k + 1)) +
        h (Nesterov_first_fix_stepsize.x f h f' x0 (k + 1)) -
        f xm - h xm = f (Nesterov_first.x f h f' x0 (k + 1))
        + h (Nesterov_first.x f h f' x0 (k + 1)) - f xm - h xm := rfl
      have h2 :
        Nesterov_first_fix_stepsize.γ f h f' x0 k ^ 2 /
        (2 * Nesterov_first_fix_stepsize.t f h f' x0 k) *
        ‖x0 - xm‖ ^ 2 =
        Nesterov_first.γ f h f' x0 k ^ 2 / (2 * Nesterov_first.t f h f' x0 k) *
        ‖x0 - xm‖ ^ 2 := rfl
      rw [h1, h2]; apply Nesterov_first_converge minφ
    _ ≤ 2 * alg.l / (k + 2) ^ 2 * ‖x0 - xm‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right; rw [alg.γeq k, alg.teq k]; field_simp
      rw [add_comm (2 : ℝ) (↑k)]; apply sq_nonneg

end Nesterov_first_fix_stepsize
