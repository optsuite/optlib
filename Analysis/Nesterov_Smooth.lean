/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang
-/
import Analysis.Gradient_Decent
import Analysis.First_Order
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
/-!
  the nesterov method for convex smooth functions
  need to be modiefied to work for nonconvex functions and gradient
-/
noncomputable section
variable {n : Type _}[Fintype n]

section
open InnerProductSpace
variable {f: (EuclideanSpace ℝ n) → ℝ} {f' :((EuclideanSpace ℝ n)) → ((EuclideanSpace ℝ n) →L[ℝ] ℝ)}
{l : ℝ} {xm x₀: EuclideanSpace ℝ n} {x : ℕ → EuclideanSpace ℝ n} {y : ℕ+ → EuclideanSpace ℝ n}
{v : ℕ → EuclideanSpace ℝ n}{γ : ℕ+ → ℝ}

lemma one_iter (h₁ : ∀ x₁ :EuclideanSpace ℝ n, HasFDerivAt f (f' x₁) x₁)
(hfun: ConvexOn ℝ Set.univ f)(h₂: l > 0)(hg : ∀ (k : ℕ+), γ k = 2 / (k + 1))
(h₃ : ∀ x y : EuclideanSpace ℝ n, ‖f' x - f' y‖ ≤ l *‖x - y‖)
(update1 : ∀ (k : ℕ+), y k = (1 - γ k) • x (k - 1) + γ k • v (k - 1))
(update2 : ∀ (k : ℕ+), x k = y k - (1 / l) • grad (f' (y k))) 
(update3 : ∀ (k : ℕ+), v k = x (k - 1) + (1 / (γ k)) • (x k - x (k - 1)))
: ∀ (k : ℕ+), f (x k) - f (xm) - (1 - γ k) * (f (x (k - 1)) - f (xm)) ≤ l * (γ k) ^ 2 / 2 * (‖v (k-1) - xm‖ ^ 2 - ‖v k -xm‖ ^ 2)  := by
    have h2 : ∀ (k : ℕ+), ∀ x' : EuclideanSpace ℝ n , f (x k) - f x' ≤ l * (inner (x k - y k) (x' - x k)) + l / 2 * ‖x k - y k‖ ^ 2 := by
      intro k x'
      rw [sub_le_iff_le_add', ← add_assoc]
      have : grad (f' (y k)) = l • (y k - x k) := by
        specialize update2 k
        rw [eq_sub_iff_add_eq', ← eq_sub_iff_add_eq] at update2
        rw [← update2, smul_smul]
        field_simp [h₂]
        rw [div_self (by linarith), one_smul]
      have t1 : f (y k) + (f' (y k)) (x' - y k) ≤ f x' := by
        exact first_order_condition (h₁ (y k)) hfun (by trivial) x' (by trivial)
      rw [← grad_equiv] at t1
      calc 
        f (x k) ≤ f (y k) + f' (y k) (x k - y k) + l / 2 * ‖x k - y k‖ ^ 2 :=by exact lipschitz_continuos_upper_bound h₁ h₃ (y k) (x k)
              _ = f (y k) + inner (grad (f' (y k))) (x k - y k) + l / 2 * ‖x k - y k‖ ^ 2 := by rw [grad_equiv]
              _ = f (y k) + inner (grad (f' (y k))) (x' - y k + (x k - x')) + l / 2 * ‖x k - y k‖ ^ 2 :=by rw [add_comm (x' - y k), add_sub (x k - x'), sub_add, sub_self, sub_zero]
              _ = f (y k) + inner (grad (f' (y k))) (x' - y k) + inner (grad (f' (y k))) (x k - x') + l / 2 * ‖x k - y k‖ ^ 2 :=by rw [inner_add_right, ← add_assoc]
              _ ≤ f x' + inner (grad (f' (y k))) (x k - x') + l / 2 * ‖x k - y k‖ ^ 2 := by rw [add_le_add_iff_right, add_le_add_iff_right]; exact t1
              _ = f x' + inner (l • (y k - x k)) (x k - x') + l / 2 * ‖x k - y k‖ ^ 2 := by rw [this]
              _ = f x' + l * inner (x k - y k) (x' - x k) + l / 2 * ‖x k - y k‖ ^ 2 := by rw [real_inner_smul_left, ← inner_neg_neg, neg_sub, neg_sub] 
    have h3 : ∀ (k : ℕ+), f (x k) - f (xm) - (1 - γ k) * (f (x (k - 1)) - f (xm)) ≤ l * (inner (x k - y k) ((1 - γ k) • (x (k - 1)) + ((γ k) • xm)- x k)) + l / 2 * ‖x k - y k‖ ^ 2 := by
      intro k
      have : f (x k) - f xm - (1 - γ k) * (f (x (k - 1)) - f xm) = γ k * (f (x k) - f xm) + (1 - γ k) * (f (x k) - f (x (k - 1))) := by ring_nf
      rw [this]
      have lzero:  0 < k + (1 : ℝ) := by exact Nat.cast_add_one_pos k
      have hz : γ k ≥ (0 : ℝ) := by 
        rw [hg k]
        apply div_nonneg (by norm_num)
        linarith
      have hl : γ k ≤ (1 : ℝ) := by 
        rw [hg k]
        rw [div_le_iff lzero, one_mul, ← sub_le_iff_le_add]
        ring_nf
        simp
        exact Nat.succ_le_of_lt k.2
      have : γ k • (xm - x k) + (1 - γ k) • (x (k - 1) - x k) = (1 - γ k) • (x (k - 1)) + ((γ k) • xm)- x k := by 
        rw [smul_sub, smul_sub, add_sub, ← add_sub_right_comm, sub_sub, ← add_smul]
        ring_nf; rw [one_smul, add_comm]
      calc γ k * (f (x k) - f xm) + (1 - γ k) * (f (x k) - f (x (k - 1))) ≤ 
            γ k * (l * (inner (x k - y k) (xm - x k)) + l / 2 * ‖x k - y k‖ ^ 2) + (1 - γ k) * (l * (inner (x k - y k) (x (k - 1) - x k)) + l / 2 * ‖x k - y k‖ ^ 2) := by
                      apply add_le_add
                      · exact mul_le_mul_of_nonneg_left (h2 k xm) hz
                      · exact mul_le_mul_of_nonneg_left (h2 k (x (k - 1))) (by linarith)
          _ = l * (γ k * (inner (x k - y k) (xm - x k))) + l * ((1 - γ k) * (inner (x k - y k) (x (k - 1) - x k))) +  l / 2 * ‖x k - y k‖ ^ 2 := by ring_nf
          _ = l * inner (x k - y k) (γ k • (xm - x k)) + l * (inner (x k - y k) ((1 - γ k) • (x (k - 1) - x k))) +  l / 2 * ‖x k - y k‖ ^ 2 := by rw [← inner_smul_right _ _ (γ k), ← inner_smul_right _ _ (1 - γ k)]
          _ = l * inner (x k - y k) (γ k • (xm - x k) + (1 - γ k) • (x (k - 1) - x k)) + l / 2 * ‖x k - y k‖ ^ 2 := by rw [← mul_add, ← inner_add_right (x k - y k)]
          _ = l * inner (x k - y k) ((1 - γ k) • (x (k - 1)) + ((γ k) • xm)- x k) + l / 2 * ‖x k - y k‖ ^ 2 := by rw [this]
    intro k
    have lzero:  0 < k + (1 : ℝ) := by exact Nat.cast_add_one_pos k
    have hz : γ k ≥ (0 : ℝ) := by 
      rw [hg k]
      apply div_nonneg (by norm_num)
      linarith
    have hzs : γ k > (0 : ℝ) := by
      rw [hg k]
      apply div_pos (by norm_num)
      linarith
    have this1 : l * (γ k) ^ 2 / 2 * (‖v (k-1) - xm‖ ^ 2 - ‖v k - xm‖ ^ 2) = l / 2 * (‖y k - (1 - γ k) • (x (k - 1)) - γ k • xm‖ ^ 2 - ‖x k - (1 - γ k) • x (k - 1) - γ k • xm‖ ^ 2) := by 
      calc l * (γ k) ^ 2 / 2 * (‖v (k-1) - xm‖ ^ 2 - ‖v k - xm‖ ^ 2) = l / 2 * ((γ k) ^ 2 * ‖v (k-1) - xm‖ ^ 2 - (γ k) ^ 2 * ‖v k - xm‖ ^ 2) := by ring_nf
            _ = l / 2 * ((‖γ k‖ * ‖(v (k-1) - xm)‖) ^ 2 - (‖γ k‖ * ‖(v k - xm)‖) ^ 2) := by simp; rw [abs_of_nonneg hz]; ring_nf; left; simp
            _ = l / 2 * (‖γ k • (v (k-1) - xm)‖ ^ 2 - ‖γ k • (v k - xm)‖ ^ 2) := by rw [norm_smul, norm_smul]
            _ = l / 2 * (‖y k - (1 - γ k) • (x (k - 1)) - γ k • xm‖ ^ 2 - ‖γ k • (x (k - 1) + (1 / (γ k)) • (x k - x (k - 1))) - γ k • xm‖ ^ 2) := by 
              specialize update1 k
              rw [← neg_add_eq_iff_eq_add, neg_add_eq_sub] at update1
              rw [smul_sub, smul_sub, update1, update3 k]
            _ = l / 2 * (‖y k - (1 - γ k) • (x (k - 1)) - γ k • xm‖ ^ 2 - ‖x k - (1 - γ k) • x (k - 1) - γ k • xm‖ ^ 2) := by 
              rw [smul_add, smul_smul];simp
              left
              rw [mul_inv_cancel (by linarith), one_smul, sub_smul, one_smul, add_comm, sub_add]
    have this2 : l / 2 * (‖y k - (1 - γ k) • (x (k - 1)) - γ k • xm‖ ^ 2 - ‖x k - (1 - γ k) • x (k - 1) - γ k • xm‖ ^ 2) = l * (inner (x k - y k) ((1 - γ k) • (x (k - 1)) + ((γ k) • xm)- x k)) + l / 2 * ‖x k - y k‖ ^ 2 := by
      simp only [Real.rpow_two]
      rw [sub_sub, sub_sub, norm_sub_sq_real (y k), norm_sub_sq_real (x k), norm_sub_sq_real (x k)]
      rw [← Real.rpow_two, ← Real.rpow_two, ← Real.rpow_two]
      calc l / 2 * (‖y k‖ ^ 2 - 2 * inner (y k) ((1 - γ k) • x (↑k - 1) + γ k • xm) + ‖(1 - γ k) • x (k - 1) + γ k • xm‖ ^ 2 - (‖x k‖ ^ 2 - 2 * inner (x ↑k) ((1 - γ k) • x (↑k - 1) + γ k • xm) + ‖(1 - γ k) • x (k - 1) + γ k • xm‖ ^ 2))
            = l / 2 * (‖y k‖ ^ 2 - ‖x k‖ ^ 2) + l / 2 * 2 * (inner (x k) ((1 - γ k) • x (↑k - 1) + γ k • xm) - inner (y k) ((1 - γ k) • x (↑k - 1) + γ k • xm)) := by ring_nf
            _ = l / 2 * (‖y k‖ ^ 2 - ‖x k‖ ^ 2) + l * inner (x k - y k) ((1 - γ k) • x (↑k - 1) + γ k • xm)  := by rw [← inner_sub_left]; ring_nf
            _ = l / 2 * (‖y k‖ ^ 2 - ‖x k‖ ^ 2) + l * inner (x k - y k) ((1 - γ k) • (x (k - 1)) + ((γ k) • xm) - x k + x k) := by rw [sub_add, sub_self, sub_zero]
            _ = l / 2 * (‖y k‖ ^ 2 - ‖x k‖ ^ 2) + l * inner (x k - y k) (x k) + l * (inner (x k - y k) ((1 - γ k) • (x (k - 1)) + ((γ k) • xm) - x k)) := by rw [inner_add_right, mul_add]; ring_nf
            _ = l / 2 * (‖y k‖ ^ 2 - ‖x k‖ ^ 2) + l * ‖x k‖ ^ 2 - l * inner (x k) (y k) + l * (inner (x k - y k) ((1 - γ k) • (x (k - 1)) + ((γ k) • xm) - x k)) := by rw [inner_sub_left, mul_sub, mul_sub, real_inner_self_eq_norm_sq, real_inner_comm, add_sub]; simp
            _ = l * (inner (x k - y k) ((1 - γ k) • (x (k - 1)) + ((γ k) • xm) - x k)) + l / 2 * (‖x k‖ ^ 2 - 2 * inner (x k) (y k) + ‖y k‖ ^ 2) := by ring_nf
    rw [this1, this2]
    exact (h3 k)

theorem nesterov_algorithm (h₁ : ∀ x₁ :EuclideanSpace ℝ n, HasFDerivAt f (f' x₁) x₁)
(hfun: ConvexOn ℝ Set.univ f)(h₂: l > 0)(hg : ∀ (k : ℕ+), γ k = 2 / (k + 1))
(h₃ : ∀ x y : EuclideanSpace ℝ n, ‖f' x - f' y‖ ≤ l *‖x - y‖)
(min : IsMinOn f Set.univ xm)
(initial1 : γ 1 = (1 : ℝ))(initial2 : v 0 = x₀)
(update1 : ∀ (k : ℕ+), y k = (1 - γ k) • x (k - 1) + γ k • v (k - 1))
(update2 : ∀ (k : ℕ+), x k = y k - (1 / l) • grad (f' (y k))) 
(update3 : ∀ (k : ℕ+), v k = x (k - 1) + (1 / (γ k)) • (x k - x (k - 1)))
(con : ∀ k : ℕ+ , (1 - γ k) / (γ k) ^ 2 ≤ 1 / (γ (k - 1)) ^ 2):
∀ k : ℕ+  , f (x k) - f (xm) ≤  2 * l / ((k + 1) ^ 2) * ‖x₀ - xm‖ ^ 2 := by
  have h4 : ∀ (k : ℕ+), f (x k) - f (xm) - (1 - γ k) * (f (x (k - 1)) - f (xm)) ≤ l * (γ k) ^ 2 / 2 * (‖v (k-1) - xm‖ ^ 2 - ‖v k -xm‖ ^ 2) := by
    exact one_iter h₁ hfun h₂ hg h₃ update1 update2 update3
  have h5 : ∀ (k : ℕ+), 1 / (γ k) ^ 2 * (f (x k) - f xm) + l / 2 * ‖v k - xm‖ ^ 2 ≤ 1 / (γ (k - 1)) ^ 2 * (f (x (k - 1)) - f xm) + l / 2 * ‖v (k - 1) - xm‖ ^ 2 := by 
    intro k
    specialize h4 k
    specialize con k
    have : (γ k) ^ 2 > 0 := by
      rw [hg k]
      simp only [Real.rpow_two, div_pow, gt_iff_lt]
      apply div_pos (by linarith) 
      apply sq_pos_of_ne_zero 
      exact Nat.cast_add_one_ne_zero ↑k
    rw [← div_le_div_right this, sub_div, mul_div_right_comm (1 - γ k)] at h4
    rw [← one_mul (f (x k) - f xm), mul_div_right_comm 1] at h4
    rw [mul_div_right_comm l, mul_assoc, mul_comm (γ k ^ 2), ← mul_assoc, mul_div_assoc] at h4
    rw [div_self (by linarith), mul_one, mul_sub (l / 2)] at h4
    rw [tsub_le_iff_left, add_sub, le_sub_iff_add_le] at h4
    apply le_trans h4 
    simp only [Real.rpow_two, ge_iff_le, add_le_add_iff_right, gt_iff_lt, sub_pos, sub_neg]
    have : f xm ≤ f (x (k - 1)):= min (by trivial)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    simp only [Real.rpow_two] at con
    exact con
  have h6 : ∀ (k : ℕ+), 1 / (γ k) ^ 2 * (f (x k) - f xm) + l / 2 * ‖v k - xm‖ ^ 2 ≤ 1 / (γ 1) ^ 2 * (f (x 1) - f xm) + l / 2 * ‖v 1 - xm‖ ^ 2 := by
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
  have h7 : 1 / (γ 1) ^ 2 * (f (x 1) - f xm) + l / 2 * ‖v 1 - xm‖ ^ 2 ≤ (1 - γ 1) / ((γ 1) ^ 2 ) * (f (x 0) - f xm) + l / 2 * ‖v 0 - xm‖ ^ 2 := by
    specialize h4 1
    rw [initial1, sub_self, zero_mul, sub_zero] at h4
    rw [initial1, sub_self, zero_div, zero_mul, zero_add]
    simp
    simp only [PNat.one_coe, Real.rpow_two, one_pow, mul_one, le_refl, tsub_eq_zero_of_le] at h4 
    rw [← le_sub_iff_add_le, ← mul_sub]
    exact h4
  have h8 : ∀ (k : ℕ+), 1 / (γ k) ^ 2 * (f (x k) - f xm) + l / 2 * ‖v k - xm‖ ^ 2 ≤ l / 2 * ‖x₀ - xm‖ ^ 2 := by
    rw [initial1] at h6
    rw [initial1, sub_self, zero_div, zero_mul, zero_add, initial2] at h7
    intro k
    apply le_trans (h6 k) h7 
  intro k 
  specialize h8 k
  have h9 : 1 / (γ k) ^ 2 * (f (x k) - f xm) ≤ l / 2 * ‖x₀ - xm‖ ^ 2 := by
    apply le_of_add_le_of_nonneg_left h8 _
    apply mul_nonneg (by linarith) _
    simp only [Real.rpow_two, sq_nonneg]
  have h10 : l / (2 : ℝ) * ‖x₀ - xm‖ ^ 2 / ((1 :ℝ) / (2 / (k + 1)) ^ 2) = 2 * l / ((k + 1) ^ 2) * ‖x₀ - xm‖ ^ 2 := by
    simp [Nat.cast_add_one_ne_zero ↑k]
    rw [← div_mul]
    ring_nf
  rw [hg k] at h9
  rw [← le_div_iff'] at h9
  · rw [h10] at h9
    exact h9
  · simp only [Real.rpow_two, div_pow, one_div, inv_div]
    apply div_pos
    · apply sq_pos_of_ne_zero
      exact Nat.cast_add_one_ne_zero ↑k
    · simp only [gt_iff_lt, zero_lt_two, pow_pos]
