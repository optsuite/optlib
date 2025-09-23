/-
Copyright (c) 2024 Yuxuan Wu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Wu, Chenyi Li
-/
import Optlib.Function.Proximal
import Mathlib.Tactic

/-!
# NesterovAccelerationSecond

## Main results

  This file mainly concentrates on the second version of Nesterov algorithm for composite optimization problems.

  We prove the O(1 / k ^ 2) rate for this algorithm.

-/

local notation "⟪" alg.x ", " y "⟫" => @inner ℝ _ _ alg.x y

section Nesterov_acceleration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x0 : E}
variable {f h : E → ℝ} {f' : E → E}

open Set Real

class Nesterov_second (f h : E → ℝ) (f' : E → E) (x0 : E) where
  (l : NNReal) (hl : l > (0 : ℝ)) (x y : ℕ → E) (z : ℕ+ → E) (t γ : ℕ → ℝ)
  (h₁ : ∀ x : E, HasGradientAt f (f' x) x) (convf: ConvexOn ℝ Set.univ f)
  (h₂ : LipschitzWith l f') (convh : ConvexOn ℝ univ h)
  (oriy : y 0 = x 0) (oriγ : γ 1 = 1) (initial : x0 = x 0)
  (cond : ∀ n : ℕ+, (1 - γ (n + 1)) * (t (n + 1)) / (γ (n + 1)) ^ 2 ≤ (t n) / (γ n) ^ 2)
  (tbound : ∀ k, (0 < t k) ∧ t k ≤ 1 / l) (γbound : ∀ n, (0 < γ n) ∧ γ n ≤ 1)
  (update1 : ∀ (k : ℕ+), z k = (1 - γ k) • (x (k - 1)) + γ k • (y (k - 1)))
  (update2 : ∀ (k : ℕ+), prox_prop ((t k / γ k) • h) (y (k - 1) - (t k / γ k) • (f' (z k))) (y k))
  (update3 : ∀ (k : ℕ+), x k = (1 - γ k) • (x (k - 1)) + γ k • y k)

variable {alg : Nesterov_second f h f' x0}

variable {xm : E}

theorem Nesterov_second_convergence (minφ : IsMinOn (f + h) Set.univ xm):
    ∀ (k : ℕ), f (alg.x (k + 1)) + h (alg.x (k + 1)) - f xm - h xm ≤
      (alg.γ (k + 1)) ^ 2 / (2 * alg.t (k + 1)) * ‖x0 - xm‖ ^ 2 := by
  let φ := fun z : E ↦ f z + h z
  have φdef : ∀ z : E, φ z = f z + h z := by aesop
  have h1 : ∀ k : ℕ+, alg.γ k • (alg.y (k - 1) - alg.y k) - alg.t k • (f' (alg.z k))
      ∈ (SubderivAt (alg.t k • h) (alg.y k)) := by
    intro k; obtain h1 := alg.update2 k
    rw [prox_iff_subderiv] at h1
    have upd2 := @SubderivAt.pos_smul _ _ _ ((alg.t k / alg.γ k) • h) (alg.y k) (alg.γ k) (alg.γbound k).1
    rw [← smul_assoc, smul_eq_mul, mul_div, mul_comm, ← mul_div, div_self, mul_one] at upd2
    rw [upd2]
    use (alg.y (↑k - 1) - (alg.t ↑k / alg.γ ↑k) • f' (alg.z k) - alg.y ↑k)
    constructor
    . exact h1
    . simp
      rw [sub_right_comm, smul_sub, ← smul_assoc, smul_eq_mul]
      rw [mul_div, mul_comm, ← mul_div, div_self, mul_one]
      linarith [(alg.γbound k).1]
    linarith [(alg.γbound k).1]
    apply ConvexOn.smul
    apply div_nonneg
    linarith [(alg.tbound k).1]
    linarith [(alg.γbound k).1]
    exact alg.convh
  have hieq1 : ∀ w : E, ∀ k : ℕ+, (alg.t k) * h w ≥ (alg.t k) * h (alg.y k) + ⟪alg.γ k •
      (alg.y (k - 1) - alg.y k) - alg.t k • (f' (alg.z k)), w - (alg.y k)⟫ := by
    intro w k
    specialize h1 k
    rw [← mem_SubderivAt, HasSubgradientAt] at h1
    specialize h1 w; simp at h1; linarith [h1]
  have cvxineq : ∀ k : ℕ+, h (alg.x k) ≤ (1 - alg.γ k) * h (alg.x (k - 1)) + alg.γ k * h (alg.y k) := by
    intro k; obtain convh := alg.convh
    rw [convexOn_iff_forall_pos] at convh;
    rcases convh with ⟨_, fall⟩
    have mem1 : (alg.x (k - 1)) ∈ univ := by simp
    have mem2 : alg.y k ∈ univ := by simp
    by_cases eq1 : alg.γ k = 1
    . simp [eq1]
      obtain update3 := alg.update3 k
      simp [eq1] at update3
      rw [update3]
    . push_neg at eq1
      have pos : 1 - alg.γ k > 0 := by
        apply lt_iff_le_and_ne.mpr
        constructor
        . linarith [(alg.γbound k).2]
        . contrapose eq1
          push_neg at *
          linarith [eq1]
      specialize fall mem1 mem2 pos ((alg.γbound k).1) (by linarith)
      rw [← (alg.update3 k)] at fall
      apply fall
  have bsc1 : ∀ k : ℕ, (alg.t k / alg.γ k) > 0 := by
    intro k
    apply div_pos
    linarith [(alg.tbound k).1]
    linarith [(alg.γbound k).1]
  have hieq2 : ∀ w : E, ∀ k : ℕ+, alg.γ k * h (alg.y k) ≤ alg.γ k * h w - (alg.γ k / alg.t k) *
     ⟪alg.γ k • (alg.y (k - 1) - alg.y k) - alg.t k • (f' (alg.z k)), w - (alg.y k)⟫ := by
    intro w k
    rw [← mul_div_right_comm, ← mul_div, ← mul_sub]
    apply (mul_le_mul_iff_left₀ (bsc1 k)).mp
    rw [mul_comm, ← mul_assoc, div_mul, div_self, div_one]
    rw [mul_assoc]
    nth_rw 3 [mul_comm]
    rw [← mul_assoc, mul_div_left_comm, div_self, mul_one]
    specialize hieq1 w k
    rw [mul_sub, mul_div_left_comm, div_self, mul_one]
    linarith [hieq1]
    linarith [(alg.tbound k).1]
    linarith [(alg.γbound k).1]
    linarith [(alg.γbound k).1]
  have hieq3 : ∀ w : E, ∀ k : ℕ+, h (alg.x k) ≤
      (1 - alg.γ k) * h (alg.x (k - 1)) + alg.γ k * h w - (alg.γ k / alg.t k)
      * ⟪alg.γ k • (alg.y (k - 1) - alg.y k) - alg.t k • (f' (alg.z k)), w - (alg.y k)⟫ := by
    intro w k
    have ax := add_le_add (hieq2 w k) (cvxineq k)
    linarith [ax]
  have hieq4 : ∀ k : ℕ+, f (alg.x k) ≤ f (alg.z k) + ⟪f' (alg.z k), alg.x k - alg.z k⟫ +
      alg.l / 2 * ‖alg.x k - alg.z k‖ ^ 2 := by
    intro k
    apply lipschitz_continuos_upper_bound' alg.h₁ alg.h₂
  have hieq5 : ∀ k : ℕ+, f (alg.x k) ≤ f (alg.z k) + ⟪f' (alg.z k), alg.x k - alg.z k⟫
      + 1 / (2 * alg.t k) * ‖alg.x k - alg.z k‖ ^ 2 := by
    intro k
    apply le_trans (hieq4 k)
    simp only [add_le_add_iff_left]
    by_cases nm0 : ‖alg.x ↑k - alg.z k‖ ^ 2 = 0
    . rw [nm0]
      simp
    . push_neg at nm0
      have ax : ‖alg.x ↑k - alg.z k‖ ^ 2 > 0 := by
        apply lt_of_le_of_ne
        simp
        symm
        apply nm0
      apply (mul_le_mul_iff_left₀ ax).mpr
      have lc2 : alg.l / 2 > (0 : ℝ) := by linarith [alg.hl]
      have tc2 : (2 * alg.t ↑k) > 0 := by linarith [(alg.tbound k).1]
      rw [one_div]
      apply (le_inv_comm₀ lc2 tc2).mpr
      rw [← one_div, ← div_mul, mul_comm]
      linarith [(alg.tbound k).2]
  have hieq6 : ∀ k : ℕ+, f (alg.x k) ≤ f (alg.z k) + ⟪f' (alg.z k), (1 - alg.γ k) • alg.x (k - 1)
      + alg.γ k • alg.y k - alg.z k⟫ + ((alg.γ k) ^ 2 / (2 * alg.t k)) * ‖alg.y k - alg.y (k - 1)‖ ^ 2 := by
    intro k
    have ax1 : alg.x ↑k - alg.z k = alg.γ k • (alg.y k - alg.y (k - 1)) := by
      rw [(alg.update1 k), (alg.update3 k)]
      rw [add_sub_add_left_eq_sub, smul_sub]
    specialize hieq5 k
    nth_rw 2 [ax1] at hieq5
    nth_rw 2 [(alg.update3 k)] at hieq5
    rw [norm_smul, mul_pow, ← mul_assoc, Real.norm_eq_abs] at hieq5
    have ax : ∀ xl : ℝ, |xl| ^ 2 = xl ^ 2 := by
      intro xl
      simp only [sq_abs]
    rw [ax (alg.γ k), div_mul_eq_mul_div, one_mul] at hieq5
    apply hieq5
  have hieq7 : ∀ k : ℕ+, f (alg.x k) ≤ (1 - alg.γ k) * f (alg.x (k - 1))
      + alg.γ k * (f (alg.z k) + ⟪f' (alg.z k), alg.y k - alg.z k⟫)
      + ((alg.γ k) ^ 2 / (2 * alg.t k)) * ‖alg.y k - alg.y (k - 1)‖ ^ 2 := by
    intro k
    calc
      f (alg.x k) ≤ f (alg.z k) + ⟪f' (alg.z k), (1 - alg.γ k) • alg.x (k - 1) + alg.γ k • alg.y k - alg.z k⟫
          + ((alg.γ k) ^ 2 / (2 * alg.t k)) * ‖alg.y k - alg.y (k - 1)‖ ^ 2 := by
        apply hieq6
      _ = (1 - alg.γ k) * (f (alg.z k) + ⟪f' (alg.z k), alg.x (k - 1) - alg.z k⟫) + alg.γ k
          * (f (alg.z k) + ⟪f' (alg.z k), alg.y k - alg.z k⟫)
          + ((alg.γ k) ^ 2 / (2 * alg.t k)) * ‖alg.y k - alg.y (k - 1)‖ ^ 2 := by
        simp only [add_left_inj]
        have ax : (1 - alg.γ ↑k) • alg.x (↑k - 1) + alg.γ ↑k • alg.y ↑k - alg.z k =
            (1 - alg.γ k) • (alg.x (k - 1) - alg.z k) + alg.γ k • (alg.y k - alg.z k) := by
          rw [smul_sub, smul_sub, sub_add_eq_add_sub, ← add_sub_assoc, sub_sub, ← add_smul]
          simp
        rw [ax]
        nth_rw 1 [inner_add_right]
        rw [inner_smul_right, inner_smul_right, mul_add, mul_add]
        ring
      _ ≤ (1 - alg.γ k) * (f (alg.x (k - 1))) + alg.γ k * (f (alg.z k) + ⟪f' (alg.z k), alg.y k - alg.z k⟫)
          + ((alg.γ k) ^ 2 / (2 * alg.t k)) * ‖alg.y k - alg.y (k - 1)‖ ^ 2 := by
        simp only [add_le_add_iff_right]
        by_cases eq1 : alg.γ k = 1
        . simp [eq1]
        . push_neg at eq1
          have pos : 1 - alg.γ k > 0 := by
            apply lt_iff_le_and_ne.mpr
            constructor
            . linarith [(alg.γbound k).2]
            . contrapose eq1
              push_neg at *
              linarith [eq1]
          apply (mul_le_mul_iff_right₀ pos).mpr
          apply Convex_first_order_condition' (alg.h₁ (alg.z k)) alg.convf
          simp
          simp
  specialize hieq3 xm
  have hieqmajor : ∀ k : ℕ+, φ (alg.x k) - φ xm - (1 - alg.γ k) * (φ (alg.x (k - 1)) - φ xm) ≤
    (alg.γ k) ^ 2 / (2 * alg.t k) * (‖alg.y (k - 1) - xm‖ ^ 2 - ‖alg.y k - xm‖ ^ 2) := by
    intro k
    specialize hieq3 k
    specialize hieq7 k
    calc
      _ = φ (alg.x k) - (1 - alg.γ k) * φ (alg.x (k - 1)) - alg.γ k * φ xm := by
        ring
      _ ≤ alg.γ ↑k * h xm - alg.γ ↑k / alg.t ↑k * ⟪alg.γ ↑k • (alg.y (↑k - 1) - alg.y ↑k)
          - alg.t ↑k • f' (alg.z k), xm - alg.y ↑k⟫
          + alg.γ ↑k * (f (alg.z k) + ⟪f' (alg.z k), alg.y ↑k - alg.z k⟫)
          + alg.γ ↑k ^ 2 / (2 * alg.t ↑k) * ‖alg.y ↑k - alg.y (↑k - 1)‖ ^ 2 - alg.γ k * φ xm := by
        have ax := add_le_add hieq3 hieq7
        rw [φdef, φdef, mul_add]
        apply sub_le_sub_right
        apply sub_le_iff_le_add'.mpr
        linarith [ax]
      _ = - alg.γ ↑k * f xm - alg.γ ↑k / alg.t ↑k * ⟪alg.γ ↑k • (alg.y (↑k - 1) - alg.y ↑k)
          - alg.t ↑k • f' (alg.z k), xm - alg.y ↑k⟫
          + alg.γ ↑k * (f (alg.z k) + ⟪f' (alg.z k), alg.y ↑k - alg.z k⟫)
          + alg.γ ↑k ^ 2 / (2 * alg.t ↑k) * ‖alg.y ↑k - alg.y (↑k - 1)‖ ^ 2 := by
        rw [φdef]
        ring
      _ ≤ - alg.γ ↑k * (f (alg.z k) + ⟪f' (alg.z k), xm - alg.z k⟫) - alg.γ ↑k / alg.t ↑k
          * ⟪alg.γ ↑k • (alg.y (↑k - 1) - alg.y ↑k) - alg.t ↑k • f' (alg.z k), xm - alg.y ↑k⟫
          + alg.γ ↑k * (f (alg.z k) + ⟪f' (alg.z k), alg.y ↑k - alg.z k⟫)
          + alg.γ ↑k ^ 2 / (2 * alg.t ↑k) * ‖alg.y ↑k - alg.y (↑k - 1)‖ ^ 2 := by
        simp
        have gpos : alg.γ k > 0 := by exact (alg.γbound k).1
        apply (mul_le_mul_iff_right₀ gpos).mpr
        apply Convex_first_order_condition' (alg.h₁ (alg.z k)) alg.convf
        simp
        simp
      _ = (alg.γ ↑k) ^ 2 / (2 * alg.t k) * (‖alg.y (k - 1) - xm‖ ^ 2 - ‖alg.y k - xm‖ ^ 2) := by
        rw [sub_add_eq_add_sub, neg_mul, ← sub_eq_neg_add, ← mul_sub, ← sub_sub,
            ← sub_add_eq_add_sub, sub_self, zero_add]
        rw [← inner_sub_right, ← sub_add, (sub_add_eq_add_sub _ xm _), sub_add_cancel]
        rw [inner_sub_left, mul_sub, ← sub_add, sub_add_eq_add_sub, inner_smul_left, conj_trivial]
        rw [← mul_assoc, div_mul, div_self, div_one, ← mul_add, ← inner_add_right]
        rw [sub_add_sub_cancel, sub_self, inner_zero_right, mul_zero, zero_sub]
        rw [inner_smul_left, conj_trivial, ← mul_assoc, div_mul_eq_mul_div, ← pow_two]
        have ax : alg.γ ↑k ^ 2 / alg.t ↑k = alg.γ ↑k ^ 2 / (2 * alg.t ↑k) * 2 := by
          rw [div_mul, mul_comm, ← mul_div, div_self, mul_one]
          norm_num
        rw [ax, ← sub_eq_neg_add, mul_assoc, ← mul_sub]
        apply mul_eq_mul_left_iff.mpr
        left
        rw [← real_inner_self_eq_norm_sq, ← inner_smul_right]
        nth_rw 4 [← neg_sub]
        rw [inner_neg_left, sub_neg_eq_add, ← inner_add_right, smul_sub,
            add_comm, add_sub, sub_add]
        nth_rw 2 [two_smul]
        rw [← add_sub, sub_self, add_zero]
        have sqsub : ∀ a b : E, ‖a‖ ^ 2 - ‖b‖ ^ 2 = ⟪- a - b, b - a⟫ := by
          intro a b
          rw [neg_sub_left, ← neg_sub a b, add_comm, inner_neg_left, inner_neg_right, neg_neg]
          rw [inner_add_left, inner_sub_right, inner_sub_right, real_inner_comm a b,
              add_sub, sub_add_cancel]
          rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
        rw [sqsub, real_inner_comm, neg_sub, ← sub_add _ _ xm, add_comm _ xm, add_sub, add_sub]
        rw [sub_sub, add_comm, ← sub_sub, two_smul]
        rw [← sub_add, sub_add_eq_add_sub, sub_add_cancel]
        linarith [(alg.tbound k).1]
  have decrease : ∀ k : ℕ+, alg.t (k + 1) / (alg.γ (k + 1) ^ 2) * (φ (alg.x (k + 1)) - φ xm)
      + 1 / 2 * ‖alg.y (k + 1) - xm‖ ^ 2 ≤
    alg.t k / (alg.γ k ^ 2) * ((φ (alg.x k)) - φ xm) + 1 / 2 * ‖alg.y k - xm‖ ^ 2 := by
    intro k
    apply le_add_neg_iff_add_le.mp
    rw [neg_eq_zero_sub, add_zero_sub]
    nth_rw 2 [add_sub_assoc]
    rw [add_comm (alg.t ↑k / alg.γ ↑k ^ 2 * (φ (alg.x ↑k) - φ xm)) _]
    apply add_neg_le_iff_le_add.mp
    rw [neg_eq_zero_sub, add_zero_sub]
    calc
      _ ≤ alg.t (↑k + 1) / alg.γ (↑k + 1) ^ 2 * (φ (alg.x (↑k + 1)) - φ xm) - (1 - alg.γ (k + 1))
          * (alg.t (k + 1)) / (alg.γ (k + 1)) ^ 2 * (φ (alg.x k) - φ xm) := by
        apply sub_le_sub_left
        apply mul_le_mul
        exact alg.cond k
        apply le_of_eq
        simp
        apply sub_nonneg.mpr
        apply minφ
        simp
        apply div_nonneg
        linarith [(alg.tbound k).1]
        apply pow_two_nonneg
      _ = (alg.t (↑k + 1)) / (alg.γ (↑k + 1)) ^ 2 * (φ (alg.x (↑k + 1)) - φ xm
          - (1 - alg.γ (↑k + 1)) * (φ (alg.x k) - φ xm)) := by
        rw [mul_comm _ (alg.t (↑k + 1)), mul_div_right_comm, mul_assoc, ← mul_sub]
      _ ≤ 1 / 2 * ‖alg.y k - xm‖ ^ 2 - 1 / 2 * ‖alg.y (k + 1) - xm‖ ^ 2 := by
        specialize hieqmajor (k + 1)
        simp only [PNat.add_coe, PNat.one_coe, add_tsub_cancel_right] at hieqmajor
        have ax : alg.t (k + 1) / alg.γ (k + 1) ^ 2 > 0 := by
          apply div_pos
          linarith [(alg.tbound (k + 1)).1]
          rw [pow_two]
          apply mul_pos
          linarith [(alg.γbound (k + 1)).1]
          linarith [(alg.γbound (k + 1)).1]
        have ine := (mul_le_mul_iff_of_pos_right ax).mpr hieqmajor
        rw [mul_comm, mul_right_comm, ← div_div, mul_div, div_mul_cancel₀,
            div_right_comm, div_self, mul_sub (1 / 2) _] at ine
        apply ine
        symm
        apply ne_of_lt
        rw [pow_two]
        apply mul_pos
        linarith [(alg.γbound (k + 1)).1]
        linarith [(alg.γbound (k + 1)).1]
        linarith [(alg.tbound (k + 1)).1]
  have bound (k : ℕ) : alg.t (k + 1) / (alg.γ (k + 1) ^ 2) * (φ (alg.x (k + 1)) - φ xm)
      + 1 / 2 * ‖alg.y (k + 1) - xm‖ ^ 2 ≤
      alg.t 1 / (alg.γ 1 ^ 2) * (φ (alg.x 1) - φ xm) + 1 / 2 * ‖alg.y 1 - xm‖ ^ 2 := by
    induction' k with k ik
    . simp
    have ine := decrease (Nat.toPNat' (k + 1))
    simp only [Nat.toPNat'_coe, add_pos_iff, zero_lt_one, or_true, ↓reduceIte] at ine
    apply le_trans ine
    apply ik
  specialize hieqmajor 1
  intro k
  have ax : ∀ n : ℕ, alg.t (n + 1) / alg.γ (n + 1) ^ 2 > 0 := by
    intro n
    apply div_pos
    linarith [(alg.tbound (n + 1)).1]
    rw [pow_two]
    apply mul_pos
    linarith [(alg.γbound (n + 1)).1]
    linarith [(alg.γbound (n + 1)).1]
  apply (mul_le_mul_iff_of_pos_left (ax (k))).mp
  rw [← mul_assoc, mul_div, div_mul_cancel₀, ← div_div, div_right_comm, div_self]
  simp only [PNat.one_coe, le_refl, tsub_eq_zero_of_le] at hieqmajor
  rw [alg.oriγ, sub_self, zero_mul, sub_zero] at hieqmajor
  calc
    _ = alg.t (k + 1) / alg.γ (k + 1) ^ 2 * (φ (alg.x (k + 1)) - φ xm) := by
      rw [sub_sub, ← φdef, ← φdef]
    _ ≤ alg.t (k + 1) / alg.γ (k + 1) ^ 2 * (φ (alg.x (k + 1)) - φ xm) + 1 / 2 * ‖alg.y (k + 1) - xm‖ ^ 2 := by
      simp
    _ ≤ alg.t 1 / alg.γ 1 ^ 2 * (φ (alg.x 1) - φ xm) + 1 / 2 * ‖alg.y 1 - xm‖ ^ 2 := by
      exact bound k
    _ ≤ 1 / 2 * ‖x0 - xm‖ ^ 2:= by
      specialize ax 0
      rw [zero_add] at ax
      have ieq := (mul_le_mul_iff_of_pos_left ax).mpr hieqmajor
      apply (add_le_add_iff_right (-(1 / 2 * ‖alg.y 1 - xm‖ ^ 2))).mp
      rw [← zero_sub, add_sub, add_sub, add_zero, add_zero, ← add_sub, sub_self, add_zero]
      apply le_trans ieq
      rw [alg.oriγ]
      rw [one_pow, div_one, ← mul_assoc, mul_div, mul_one, ← div_div, div_right_comm, div_self]
      rw [alg.oriy, ← alg.initial, mul_sub]
      linarith [(alg.tbound 1).1]
  linarith [(alg.tbound (k + 1)).1]
  rw [pow_two]
  symm
  apply ne_of_lt
  apply mul_pos
  linarith [(alg.γbound (k + 1)).1]
  linarith [(alg.γbound (k + 1)).1]

end Nesterov_acceleration

section Nesterov_second_fix_stepsize

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f h : E → ℝ} {f' : E → E} {x0 : E}

open Set Real PNat

class Nesterov_second_fix_stepsize (f h: E → ℝ) (f' : E → E) (x0 : E) where
  (l : NNReal) (hl : l > (0 : ℝ)) (x y : ℕ → E) (z : ℕ+ → E) (t γ : ℕ → ℝ)
  (h₁ : ∀ x : E, HasGradientAt f (f' x) x) (convf: ConvexOn ℝ Set.univ f)
  (h₂ : LipschitzWith l f') (convh : ConvexOn ℝ univ h)
  (oriy : y 0 = x 0) (initial : x0 = x 0)
  (teq : ∀ n : ℕ, t n = 1 / l)
  (γeq : ∀ n : ℕ, γ n = if n = 0 then (1 / (2 : ℝ)) else (2 : ℝ) / (1 + n))
  (update1 : ∀ k : ℕ+, z k = (1 - γ k) • (x (k - 1)) + γ k • (y (k - 1)))
  (update2 : ∀ k : ℕ+, prox_prop ((t k / γ k) • h) (y (k - 1) - (t k / γ k) • f' (z k)) (y k))
  (update3 : ∀ k : ℕ+, x k = (1 - γ k) • (x (k - 1)) + γ k • y k)

instance {f h : E → ℝ} {f' : E → E} {x0 : E} [p : Nesterov_second_fix_stepsize f h f' x0] :
    Nesterov_second f h f' x0 where
  l := p.l
  h₁ := p.h₁
  convf := p.convf
  h₂ := p.h₂
  convh := p.convh
  x := p.x; y := p.y; z := p.z; t := p.t; γ := p.γ;
  oriy := p.oriy
  oriγ := by simp [p.γeq 1]; norm_num
  initial := p.initial
  cond := by
    intro n
    have hn0 : (↑n : ℕ) ≠ 0 := by
      have : 1 ≤ (↑n : ℕ) := by simpa using n.2
      exact Nat.pos_iff_ne_zero.mp ((Nat.succ_le_iff).1 (by simpa using this))
    have h1 : 0 < (1 + (↑n : ℕ) : ℝ) := by positivity
    have h2 : 0 < (1 + (↑n : ℕ) + 1 : ℝ) := by positivity
    simp [p.γeq, p.teq, hn0, pow_two]
    have hn1 : (↑n + 1 : ℕ) ≠ 0 := by simp
    simp only [ge_iff_le]
    field_simp [h1, h2]
    ring_nf
    simp_all only [ne_eq, ne_zero, not_false_eq_true, Nat.add_eq_zero, one_ne_zero, and_self, one_div,
      le_add_iff_nonneg_right, inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_right, inv_nonneg, NNReal.zero_le_coe]
  tbound := by
    intro k; rw [p.teq k]; simp; exact p.hl
  hl := p.hl
  γbound := by
    intro k;rw [p.γeq]; constructor
    · by_cases hk : k = 0
      · rw [hk]; simp
      simp [hk]; positivity
    · by_cases hk : k = 0
      rw [hk]; simp; norm_num; push_neg at hk
      simp [hk]; rw [div_le_iff₀ (by positivity)]; simp
      have : (k : ℝ) ≥ 1 := by
        rw [← Nat.pos_iff_ne_zero, Nat.lt_iff_add_one_le, zero_add] at hk; simp [hk]
      linarith
  update1 := p.update1
  update2 := p.update2
  update3 := p.update3

variable {alg : Nesterov_second_fix_stepsize f h f' x0}

variable {xm : E}

theorem Nesterov_second_fix_stepsize_converge (minφ : IsMinOn (f + h) Set.univ xm):
    ∀ (k : ℕ), f (alg.x (k + 1)) + h (alg.x (k + 1)) - f xm - h xm ≤
    2 * alg.l / (k + 2) ^ 2 * ‖x0 - xm‖ ^ 2 := by
  intro k
  calc
    f (alg.x (k + 1)) + h (alg.x (k + 1)) - f xm - h xm ≤
        (alg.γ (k + 1)) ^ 2 / (2 * alg.t (k + 1)) * ‖x0 - xm‖ ^ 2 := by
      have h1 :
        f (Nesterov_second_fix_stepsize.x f h f' x0 (k + 1)) +
        h (Nesterov_second_fix_stepsize.x f h f' x0 (k + 1)) -
        f xm - h xm = f (Nesterov_second.x f h f' x0 (k + 1))
        + h (Nesterov_second.x f h f' x0 (k + 1)) - f xm - h xm := rfl
      have h2 :
        Nesterov_second_fix_stepsize.γ f h f' x0 (k + 1) ^ 2 /
        (2 * Nesterov_second_fix_stepsize.t f h f' x0 (k + 1)) *
        ‖x0 - xm‖ ^ 2 =
        Nesterov_second.γ f h f' x0 (k + 1) ^ 2 / (2 * Nesterov_second.t f h f' x0 (k + 1)) *
        ‖x0 - xm‖ ^ 2 := rfl
      rw [h1, h2]; apply Nesterov_second_convergence minφ
    _ ≤ 2 * alg.l / (k + 2) ^ 2 * ‖x0 - xm‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [alg.γeq (k + 1), alg.teq (k + 1)]; field_simp
      simp only [pow_two]
      have h_nonzero : 1 + k ≠ 0 := by simp
      simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.cast_add, Nat.cast_one,
        ge_iff_le]
      field_simp
      ring_nf
      simp_all only [ne_eq, Nat.add_eq_zero, one_ne_zero, false_and, not_false_eq_true, le_refl]

end Nesterov_second_fix_stepsize
