/-
Copyright (c) 2023 Chenyi Li, Ziyu Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Zaiwen Wen
-/
import Optlib.Function.Lsmooth
import Mathlib.Tactic

/-!
# NesterovSmooth

## Main results

  This file mainly concentrates on the Nesterov algorithm for smooth convex optimization problems.

  We prove the O(1 / k ^ 2) rate for this algorithm.

-/
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

open Set
open scoped Set InnerProductSpace RealInnerProductSpace

class Nesterov (f : E → ℝ) (f' : E → E) (γ : ℕ+ → ℝ) (initial_point : E) where
  (x : ℕ → E) (y : ℕ+ → E) (v : ℕ → E) (l : NNReal)
  (diff : ∀ x₁, HasGradientAt f (f' x₁) x₁)
  (update1 : ∀ (k : ℕ+), y k = (1 - γ k) • x (k - 1) + γ k • v (k - 1))
  (update2 : ∀ (k : ℕ+), x k = y k - (1 / l.1) • (f' (y k)))
  (update3 : ∀ (k : ℕ+), v k = x (k - 1) + (1 / (γ k)) • (x k - x (k - 1)))
  (hl : l > 0) (smooth : LipschitzWith l f')
  (initial1 : γ 1 = (1 : ℝ)) (initial2 : v 0 = initial_point)

variable {f : E → ℝ} {f' : E → E} {xm x₀: E} {γ : ℕ+ → ℝ } {alg : Nesterov f f' γ x₀}

lemma one_iter (hfun : ConvexOn ℝ Set.univ f) (hg : ∀ (k : ℕ+), γ k = 2 / (k + 1)) :
    ∀ (k : ℕ+), f (alg.x k) - f xm - (1 - γ k) * (f (alg.x (k - 1)) - f xm) ≤
    alg.l * (γ k) ^ 2 / 2 * (‖alg.v (k - 1) - xm‖ ^ 2 - ‖alg.v k - xm‖ ^ 2)  := by
  have h2 : ∀ (k : ℕ+), ∀ x' : E , f (alg.x k) - f x' ≤ alg.l *
      (⟪alg.x k - alg.y k, x' - alg.x k⟫_ℝ) + alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by
    intro k x'
    rw [sub_le_iff_le_add', ← add_assoc]
    have : (f' (alg.y k)) = alg.l.1 • (alg.y k - alg.x k) := by
      have update2 := alg.update2 k
      have h1 := (eq_sub_iff_add_eq').1 update2
      have h2 : alg.y k - alg.x k = (1 / alg.l.1) • f' (alg.y k) := by
        exact sub_eq_iff_eq_add.mpr (id (Eq.symm h1))
      have hlne : alg.l.1 ≠ 0 := by exact ne_of_gt alg.hl
      have hsmul := congrArg (fun t => alg.l.1 • t) h2
      have : alg.l.1 • (alg.y k - alg.x k) = f' (alg.y k) := by
        simp_all only [NNReal.val_eq_coe, one_div, add_sub_cancel, sub_sub_cancel, ne_eq, NNReal.coe_eq_zero,
          not_false_eq_true, smul_inv_smul₀]
      exact this.symm
    have t1 : f (alg.y k) + ⟪f' (alg.y k), x' - alg.y k⟫_ℝ ≤ f x' := by
      exact Convex_first_order_condition' (alg.diff (alg.y k)) hfun (by trivial) x' (by trivial)
    calc
      _ ≤ f (alg.y k) + ⟪f' (alg.y k), alg.x k - alg.y k⟫_ℝ +
            alg.l.1 / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by
          exact lipschitz_continuos_upper_bound' alg.diff alg.smooth (alg.y k) (alg.x k)
        _ = f (alg.y k) + ⟪f' (alg.y k), x' - alg.y k + (alg.x k - x')⟫_ℝ +
            alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by
          rw [add_comm (x' - alg.y k), add_sub (alg.x k - x'), sub_add, sub_self, sub_zero]; simp
        _ = f (alg.y k) + ⟪f' (alg.y k), x' - alg.y k⟫_ℝ + ⟪f' (alg.y k), alg.x k - x'⟫_ℝ
            + alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by rw [inner_add_right, ← add_assoc]
        _ ≤ f x' + ⟪f' (alg.y k), alg.x k - x'⟫_ℝ + alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by
          rw [add_le_add_iff_right, add_le_add_iff_right]; exact t1
        _ = f x' + ⟪alg.l.1 • (alg.y k - alg.x k), alg.x k - x'⟫_ℝ +
          alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by rw [this]
        _ = f x' + alg.l * (⟪alg.x k - alg.y k, x' - alg.x k⟫_ℝ) +
            alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by
          rw [real_inner_smul_left, ← inner_neg_neg, neg_sub, neg_sub]; simp
  have h3 : ∀ (k : ℕ+), f (alg.x k) - f xm - (1 - γ k) * (f (alg.x (k - 1)) - f xm) ≤
      alg.l * (⟪alg.x k - alg.y k, (1 - γ k) • (alg.x (k - 1)) + ((γ k) • xm) -
      alg.x k⟫_ℝ) + alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by
    intro k
    have : f (alg.x k) - f xm - (1 - γ k) * (f (alg.x (k - 1)) - f xm) = γ k *
        (f (alg.x k) - f xm) + (1 - γ k) * (f (alg.x k) - f (alg.x (k - 1))) := by ring_nf
    rw [this]
    have lzero:  0 < k + (1 : ℝ) := Nat.cast_add_one_pos k
    have hz : γ k ≥ (0 : ℝ) := by
      rw [hg k]
      apply div_nonneg (by norm_num); linarith
    have hl : γ k ≤ (1 : ℝ) := by
      rw [hg k, div_le_iff₀ lzero, one_mul, ← sub_le_iff_le_add]
      ring_nf; simp
      exact Nat.succ_le_of_lt k.2
    have : γ k • (xm - alg.x k) + (1 - γ k) • (alg.x (k - 1) - alg.x k)
        = (1 - γ k) • (alg.x (k - 1)) + ((γ k) • xm)- alg.x k := by
      rw [smul_sub, smul_sub, add_sub, ← add_sub_right_comm, sub_sub, ← add_smul]
      ring_nf; rw [one_smul, add_comm]
    calc
      _ ≤ γ k * (alg.l * (⟪alg.x k - alg.y k, xm - alg.x k⟫_ℝ) + alg.l / 2 *
            ‖alg.x k - alg.y k‖ ^ 2) + (1 - γ k) * (alg.l * (⟪alg.x k - alg.y k,
            alg.x (k - 1) - alg.x k⟫_ℝ) + alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (h2 k xm) hz
          · exact mul_le_mul_of_nonneg_left (h2 k (alg.x (k - 1))) (by linarith)
      _ = alg.l * (γ k * (⟪alg.x k - alg.y k, xm - alg.x k⟫_ℝ)) + alg.l * ((1 - γ k) *
            (⟪alg.x k - alg.y k, alg.x (k - 1) - alg.x k⟫_ℝ)) +
            alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by ring_nf
      _ = alg.l * (⟪alg.x k - alg.y k, γ k • (xm - alg.x k)⟫_ℝ) + alg.l *
            (⟪alg.x k - alg.y k, (1 - γ k) •
            (alg.x (k - 1) - alg.x k)⟫_ℝ) +  alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by
            rw [← inner_smul_right _ _ (γ k), ← inner_smul_right _ _ (1 - γ k)]
      _ = alg.l * (⟪alg.x k - alg.y k, γ k • (xm - alg.x k) + (1 - γ k) •
            (alg.x (k - 1) - alg.x k)⟫_ℝ) + alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by
          rw [← mul_add, ← inner_add_right (alg.x k - alg.y k)]
      _ = alg.l * (⟪alg.x k - alg.y k, (1 - γ k) • (alg.x (k - 1)) +
            ((γ k) • xm)- alg.x k⟫_ℝ) + alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by rw [this]
  intro k
  have hz : γ k ≥ (0 : ℝ) := by
    rw [hg k]
    apply div_nonneg (by norm_num); linarith
  have hzs : γ k > (0 : ℝ) := by
      rw [hg k]
      apply div_pos (by norm_num); linarith
  have this1 : alg.l * (γ k) ^ 2 / 2 * (‖alg.v (k-1) - xm‖ ^ 2 - ‖alg.v k - xm‖ ^ 2) =
      alg.l / 2 * (‖alg.y k - (1 - γ k) • (alg.x (k - 1)) - γ k • xm‖ ^ 2 -
      ‖alg.x k - (1 - γ k) • alg.x (k - 1) - γ k • xm‖ ^ 2) := by
    calc
        _ = alg.l / 2 * ((γ k) ^ 2 * ‖alg.v (k-1) - xm‖ ^ 2 -
              (γ k) ^ 2 * ‖alg.v k - xm‖ ^ 2) := by ring_nf
        _ = alg.l / 2 * ((‖γ k‖ * ‖(alg.v (k-1) - xm)‖) ^ 2 -
              (‖γ k‖ * ‖(alg.v k - xm)‖) ^ 2) := by
            simp; rw [abs_of_nonneg hz]; ring_nf; left; simp
        _ = alg.l / 2 * (‖γ k • (alg.v (k-1) - xm)‖ ^ 2 - ‖γ k • (alg.v k - xm)‖ ^ 2) := by
            rw [norm_smul, norm_smul]
        _ = alg.l / 2 * (‖alg.y k - (1 - γ k) • (alg.x (k - 1)) - γ k • xm‖ ^ 2 -
              ‖γ k • (alg.x (k - 1) + (1 / (γ k)) • (alg.x k - alg.x (k - 1)))
              - γ k • xm‖ ^ 2) := by
            have update1 : ∀ (k : ℕ+), alg.y k = (1 - γ k) •
              alg.x (k - 1) + γ k • alg.v (k - 1) := alg.update1
            specialize update1 k
            rw [← neg_add_eq_iff_eq_add, neg_add_eq_sub] at update1
            rw [smul_sub, smul_sub, update1, alg.update3 k]
        _ = alg.l / 2 * (‖alg.y k - (1 - γ k) • (alg.x (k - 1)) - γ k • xm‖ ^ 2 -
                ‖alg.x k - (1 - γ k) • alg.x (k - 1) - γ k • xm‖ ^ 2) := by
            rw [smul_add, smul_smul]; simp
            left; rw [mul_inv_cancel₀ (by linarith), one_smul, sub_smul, one_smul, add_comm, sub_add]
  have this2 : alg.l / 2 * (‖alg.y k - (1 - γ k) • (alg.x (k - 1)) - γ k • xm‖ ^ 2 -
      ‖alg.x k - (1 - γ k) • alg.x (k - 1) - γ k • xm‖ ^ 2) = alg.l *
      (⟪alg.x k - alg.y k, (1 - γ k) • (alg.x (k - 1)) + ((γ k) • xm)- alg.x k⟫_ℝ)
      + alg.l / 2 * ‖alg.x k - alg.y k‖ ^ 2 := by
    rw [sub_sub, sub_sub, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real]
    calc
      _ = alg.l / 2 * (‖alg.y k‖ ^ 2 - ‖alg.x k‖ ^ 2) + alg.l / 2 * 2 * (⟪alg.x k,
            (1 - γ k) • alg.x (↑k - 1) + γ k • xm⟫_ℝ - ⟪alg.y k,
            (1 - γ k) • alg.x (↑k - 1) + γ k • xm⟫_ℝ) := by ring_nf
      _ = alg.l / 2 * (‖alg.y k‖ ^ 2 - ‖alg.x k‖ ^ 2) + alg.l * (⟪alg.x k - alg.y k,
            (1 - γ k) • alg.x (↑k - 1) + γ k • xm⟫_ℝ)  := by rw [← inner_sub_left]; ring_nf
      _ = alg.l / 2 * (‖alg.y k‖ ^ 2 - ‖alg.x k‖ ^ 2) + alg.l * (⟪alg.x k - alg.y k,
            (1 - γ k) • (alg.x (k - 1)) + ((γ k) • xm) - alg.x k + alg.x k⟫_ℝ) := by
          rw [sub_add, sub_self, sub_zero]
      _ = alg.l / 2 * (‖alg.y k‖ ^ 2 - ‖alg.x k‖ ^ 2) + alg.l * (⟪alg.x k - alg.y k,
            alg.x k⟫_ℝ) + alg.l * (⟪alg.x k - alg.y k, (1 - γ k) • (alg.x (k - 1))
            + ((γ k) • xm) - alg.x k⟫_ℝ) := by
          rw [inner_add_right, mul_add]; ring_nf
      _ = alg.l / 2 * (‖alg.y k‖ ^ 2 - ‖alg.x k‖ ^ 2) + alg.l * ‖alg.x k‖ ^ 2 -
            alg.l * (⟪alg.x k, alg.y k⟫_ℝ) + alg.l * (⟪alg.x k - alg.y k, (1 - γ k)
            • (alg.x (k - 1)) + ((γ k) • xm) - alg.x k⟫_ℝ) := by
          rw [inner_sub_left, mul_sub, mul_sub, real_inner_self_eq_norm_sq]
          rw [real_inner_comm, add_sub];
      _ = alg.l * (⟪alg.x k - alg.y k, (1 - γ k) • (alg.x (k - 1)) + ((γ k) • xm)
            - alg.x k⟫_ℝ) + alg.l / 2 * (‖alg.x k‖ ^ 2 - 2 *
            ⟪alg.x k, alg.y k⟫_ℝ + ‖alg.y k‖ ^ 2) := by ring_nf
  rw [this1, this2]
  exact h3 k

set_option maxHeartbeats 0 in
theorem nesterov_algorithm_smooth (hfun: ConvexOn ℝ Set.univ f)
    (hg : ∀ (k : ℕ+), γ k = 2 / (k + 1)) (min : IsMinOn f Set.univ xm)
    (con : ∀ k : ℕ+ , (1 - γ k) / (γ k) ^ 2 ≤ 1 / (γ (k - 1)) ^ 2):
    ∀ k : ℕ+, f (alg.x k) - f xm ≤  2 * alg.l / ((k + 1) ^ 2) * ‖x₀ - xm‖ ^ 2 := by
  have h4 : ∀ (k : ℕ+), f (alg.x k) - f xm - (1 - γ k) * (f (alg.x (k - 1)) - f xm) ≤
      alg.l.1 * (γ k) ^ 2 / 2 * (‖alg.v (k-1) - xm‖ ^ 2 - ‖alg.v k -xm‖ ^ 2) := by
    exact one_iter hfun hg
  have h5 : ∀ (k : ℕ+), 1 / (γ k) ^ 2 * (f (alg.x k) - f xm) + alg.l.1 / 2 * ‖alg.v k - xm‖ ^ 2
      ≤ 1 / (γ (k - 1)) ^ 2 * (f (alg.x (k - 1)) - f xm) +
        alg.l.1 / 2 * ‖alg.v (k - 1) - xm‖ ^ 2 := by
    intro k
    specialize h4 k
    specialize con k
    have : (γ k) ^ 2 > 0 := by
      rw [hg k]
      simp only [div_pow, gt_iff_lt]
      apply div_pos (by linarith)
      apply sq_pos_of_ne_zero
      exact Nat.cast_add_one_ne_zero ↑k
    have hpos : 0 < (γ k) ^ 2 := by
      rw [hg k]
      simp only [div_pow]
      apply div_pos (by linarith)
      apply sq_pos_of_ne_zero
      exact Nat.cast_add_one_ne_zero ↑k
    rw [← div_le_div_iff_of_pos_right this, sub_div, mul_div_right_comm (1 - γ k)] at h4
    rw [← one_mul (f (alg.x k) - f xm), mul_div_right_comm 1] at h4
    rw [mul_div_right_comm (alg.l).1, mul_assoc, mul_comm (γ k ^ 2)] at h4
    rw [← mul_assoc, mul_div_assoc] at h4
    rw [div_self (by linarith), mul_one, mul_sub (alg.l.1 / 2)] at h4
    rw [tsub_le_iff_left, add_sub, le_sub_iff_add_le] at h4
    apply le_trans h4
    simp only [add_le_add_iff_right]
    have : f xm ≤ f (alg.x (k - 1)):= min (by trivial)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact con
  have h6 : ∀ (k : ℕ+), 1 / (γ k) ^ 2 * (f (alg.x k) - f xm) + alg.l / 2 * ‖alg.v k - xm‖ ^ 2
      ≤ 1 / (γ 1) ^ 2 * (f (alg.x 1) - f xm) + alg.l / 2 * ‖alg.v 1 - xm‖ ^ 2 := by
    intro k
    induction' k using PNat.caseStrongInductionOn with j IH
    · simp
    · specialize IH j (le_refl _)
      specialize h5 (j + 1)
      have y1: ↑(j + 1) - (1 : ℕ) = j := by simp
      have y2: j + 1 - 1 = j := by exact Iff.mp PNat.natPred_inj rfl
      apply le_trans h5 _
      rw [y1, y2]
      exact IH
  have h7 : 1 / (γ 1) ^ 2 * (f (alg.x 1) - f xm) + alg.l / 2 * ‖alg.v 1 - xm‖ ^ 2
      ≤ (1 - γ 1) / ((γ 1) ^ 2 ) * (f (alg.x 0) - f xm)
      + alg.l / 2 * ‖alg.v 0 - xm‖ ^ 2 := by
    specialize h4 1
    rw [alg.initial1, sub_self, zero_mul, sub_zero] at h4
    rw [alg.initial1, sub_self, zero_div, zero_mul, zero_add]
    simp
    simp only [PNat.one_coe, one_pow, mul_one, le_refl, tsub_eq_zero_of_le] at h4
    rw [← le_sub_iff_add_le, ← mul_sub]
    exact h4
  have h8 : ∀ (k : ℕ+), 1 / (γ k) ^ 2 * (f (alg.x k) - f xm) + alg.l / 2
      * ‖alg.v k - xm‖ ^ 2 ≤ alg.l / 2 * ‖x₀ - xm‖ ^ 2 := by
    rw [alg.initial1] at h6
    rw [alg.initial1, sub_self, zero_div, zero_mul, zero_add, alg.initial2] at h7
    intro k
    apply le_trans (h6 k) h7
  intro k
  specialize h8 k
  have h9 : 1 / (γ k) ^ 2 * (f (alg.x k) - f xm) ≤ alg.l / 2 * ‖x₀ - xm‖ ^ 2 := by
    apply le_of_add_le_of_nonneg_left h8 _
    have : alg.l > 0 := alg.hl
    apply mul_nonneg _ _
    · positivity
    · simp only [sq_nonneg]
  have h10 : alg.l / (2 : ℝ) * ‖x₀ - xm‖ ^ 2 / ((1 :ℝ) / (2 / (k + 1)) ^ 2)
      = 2 * alg.l / ((k + 1) ^ 2) * ‖x₀ - xm‖ ^ 2 := by
    simp; field_simp
  rw [hg k] at h9
  rw [← le_div_iff₀'] at h9
  · rw [h10] at h9
    exact h9
  · simp only [div_pow, one_div, inv_div]
    apply div_pos
    · apply sq_pos_of_ne_zero
      exact Nat.cast_add_one_ne_zero ↑k
    · simp only [zero_lt_two, pow_pos]
