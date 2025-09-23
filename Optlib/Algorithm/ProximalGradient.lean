/-
Copyright (c) 2024 Shengyang Xu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengyang Xu, Chenyi Li
-/
import Optlib.Function.Proximal

/-!
# ProximalGradient

## Main results

  This file mainly concentrates on the proximal gradient algorithm for
  composite optimization problems.

  We prove the O(1 / k) rate for this algorithm.

-/

section method

open Set
open scoped RealInnerProductSpace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [ProperSpace E]
variable {xm x₀: E} {s : Set E} {f : E → ℝ} {f' : E → E} {h : E → ℝ}
variable {t : ℝ} {x : ℕ → E} {L : NNReal}

class proximal_gradient_method (f h: E → ℝ) (f' : E → E) (x₀ : E) where
  (xm : E) (t : ℝ) (x : ℕ → E) (L : NNReal)
  (fconv : ConvexOn ℝ univ f) (hconv : ConvexOn ℝ univ h)
  (h₁ : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁) (h₂ : LipschitzWith L f')
  (h₃ : ContinuousOn h univ) (minphi : IsMinOn (f + h) Set.univ xm)
  (tpos : 0 < t) (step : t ≤ 1 / L) (ori : x 0 = x₀) (hL : L > (0 : ℝ))
  (update : ∀ (k : ℕ), prox_prop (t • h) (x k - t • f' (x k)) (x (k + 1)))

variable {alg : proximal_gradient_method f h f' x₀}

theorem proximal_gradient_method_converge : ∀ (k : ℕ+),
    (f (alg.x k) + h (alg.x k) - f alg.xm - h alg.xm)
    ≤ 1 / (2 * k * alg.t) * ‖x₀ - alg.xm‖ ^ 2 := by
  intro k
  rw [mul_comm, mul_one_div, le_div_iff₀, mul_comm]
  have th : ContinuousOn (alg.t • h) univ := by
    apply ContinuousOn.const_smul alg.h₃ alg.t
  have th' : ConvexOn ℝ univ (alg.t • h) := by
    apply ConvexOn.smul; linarith [alg.tpos]; apply alg.hconv
  let Gt := fun x ↦ (1 / alg.t) • (x - prox_point_c'  (alg.t • h)  (x - alg.t • f' x) th th')
  let φ := fun x ↦ f x + h x
  have hG : ∀ z : E, Gt z - f' z ∈ (SubderivAt h (z - alg.t • Gt z)) := by
    intro z
    have eq1 : z - alg.t • Gt z = prox_point_c' (alg.t • h) (z - alg.t • f' z) th th' := by
      simp [Gt]; rw [smul_inv_smul₀, ← sub_add]; simp; linarith [alg.tpos]
    have eq2 : prox_prop (alg.t • h) (z - alg.t • f' z) (z - alg.t • Gt z) := by
      rw [prox_point_c'] at eq1; rw [eq1]; apply Classical.choose_spec
    rw [prox_iff_subderiv_smul, sub_sub_sub_comm, sub_sub_eq_add_sub] at eq2;
    rw [sub_self, zero_add, ← smul_sub, smul_smul _ alg.t _] at eq2
    rw [one_div_mul_cancel, one_smul] at eq2; exact eq2
    linarith [alg.tpos]; exact alg.hconv; linarith [alg.tpos]
  have fieq1 : ∀ x : E, f (x - alg.t • Gt x) ≤
      f x - alg.t * ⟪f' x, Gt x⟫_ℝ + alg.t ^ 2 * alg.L / 2 * ‖Gt x‖ ^ 2 := by
    intro x
    let y := x - alg.t • Gt x
    have ieq1 : f y ≤ f x + ⟪f' x, y - x⟫_ℝ + alg.L / 2 * ‖y - x‖ ^ 2 := by
      apply lipschitz_continuos_upper_bound' alg.h₁ alg.h₂
    have eq3 : y - x = - alg.t • Gt x := by simp [Gt, y]
    rw [eq3] at ieq1; rw [inner_smul_right, norm_smul, mul_pow] at ieq1
    rw [← mul_assoc, mul_comm ] at ieq1
    simp at ieq1; rw [← sub_eq_add_neg] at ieq1; simp; linarith [alg.tpos]
  have fieq2 : ∀ x : E,
      f (x - alg.t • Gt x) ≤ f x - alg.t * ⟪f' x, Gt x⟫_ℝ + alg.t / 2 * ‖Gt x‖ ^ 2 := by
    intro x
    calc
      f (x - alg.t • Gt x) ≤
          f x - alg.t * ⟪f' x, Gt x⟫_ℝ + alg.t ^ 2 * alg.L / 2 * ‖Gt x‖ ^ 2 := fieq1 x
      _ ≤ f x - alg.t * ⟪f' x, Gt x⟫_ℝ + alg.t / 2 * ‖Gt x‖ ^ 2 := by
        apply add_le_add_left
        apply mul_le_mul_of_nonneg_right
        apply div_le_div_of_nonneg_right _ (by norm_num)
        calc
          alg.t ^ 2 * alg.L ≤ alg.t * (1 / alg.L) * alg.L := by
            rw [pow_two]; apply mul_le_mul_of_nonneg_right
            rw [mul_le_mul_iff_right₀ alg.tpos]; exact alg.step; simp
          _ = alg.t := by field_simp; rw [← mul_div, div_self (by linarith [alg.hL]), mul_one]
        exact sq_nonneg _
  have fieq3 : ∀ x z : E, f x + ⟪f' x, z - x⟫_ℝ ≤ f z := by
    intro x z
    apply Convex_first_order_condition' (alg.h₁ x) alg.fconv
    simp; simp
  have hieq1 : ∀ x z : E,
      h (x - alg.t • Gt x) + ⟪Gt x - f' x, z - x + alg.t • Gt x⟫_ℝ ≤ h z := by
    intro x z
    specialize hG x
    rw [← mem_SubderivAt, HasSubgradientAt] at hG
    specialize hG z; rw [sub_add]; apply hG
  have hieq2 : ∀ x z : E,
      h (x - alg.t • Gt x) ≤ h z - ⟪Gt x - f' x, z - x + alg.t • Gt x⟫_ℝ := by
    intro x z; linarith [hieq1 x z]
  have univieq : ∀ x z : E,
      φ (x - alg.t • Gt x) ≤ φ z + ⟪Gt x, x - z⟫_ℝ - alg.t / 2 * ‖Gt x‖ ^ 2 := by
    intro x z
    calc
      φ (x - alg.t • Gt x) ≤ (f x - alg.t * ⟪f' x, Gt x⟫_ℝ + alg.t / 2 * ‖Gt x‖ ^ 2)
        + (h z - ⟪Gt x - f' x, z - x + alg.t • Gt x⟫_ℝ) := by
        linarith [fieq2 x, hieq2 x z]
      _ ≤ (f z - ⟪f' x, z - x⟫_ℝ - alg.t * ⟪f' x, Gt x⟫_ℝ + alg.t / 2 * ‖Gt x‖ ^ 2)
        + (h z - ⟪Gt x - f' x, z - x + alg.t • Gt x⟫_ℝ) := by
        linarith [fieq3 x z]
      _ = φ z + ⟪Gt x, x - z⟫_ℝ - alg.t / 2 * ‖Gt x‖ ^ 2 := by
        rw [← inner_smul_right, sub_sub, ← inner_add_right]
        rw [inner_sub_left, ← sub_add, add_rotate, ← add_comm_sub, ← add_sub]
        rw [← add_sub, sub_self, add_zero, add_rotate, inner_add_right, ← neg_sub x z]
        rw [inner_neg_right, ← sub_sub, sub_neg_eq_add, add_comm _ ⟪Gt x, x - z⟫_ℝ]
        rw [add_comm _ ⟪Gt x, x - z⟫_ℝ, ← add_sub _ (φ z), ← add_sub, add_assoc]
        rw [add_assoc, add_left_cancel_iff]
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        rw [add_comm_sub, ← add_sub]
        have (a : ℝ): alg.t / 2 * a - alg.t * a = - alg.t / 2 * a := by ring
        rw [this, sub_eq_add_neg, ← add_assoc, add_comm (h z) (f z)]; field_simp; grind
  have φieq1 : ∀ x : E, φ (x - alg.t • Gt x) - φ alg.xm ≤
      (1 / (2 * alg.t)) * (‖x - alg.xm‖ ^ 2 - ‖x - alg.t • Gt x - alg.xm‖ ^ 2) := by
    intro x
    calc
      φ (x - alg.t • Gt x) - φ alg.xm ≤ ⟪Gt x, x - alg.xm⟫_ℝ - alg.t / 2 * ‖Gt x‖ ^ 2 := by
        linarith [univieq x alg.xm]
      _ = (1 / (2 * alg.t)) * (‖x - alg.xm‖ ^ 2 - ‖x - alg.t • Gt x - alg.xm‖ ^ 2) := by
        have aux (p q : E) : ⟪p, q⟫_ℝ - alg.t / 2 * ‖p‖ ^ 2 =
            1 / (2 * alg.t) * (‖q‖ ^ 2 - ‖q - alg.t • p‖ ^ 2) := by
          rw [norm_sub_sq_real]; field_simp; ring_nf
          rw [inner_smul_right, real_inner_comm];
          nth_rw 2 [mul_comm _ (alg.t)⁻¹]; rw [norm_smul, mul_pow, pow_two ‖alg.t‖]
          simp; rw [mul_comm _ ⟪q, p⟫_ℝ, mul_assoc _ alg.t, mul_inv_cancel₀, ← mul_assoc]
          rw [← mul_assoc, inv_mul_cancel₀]; simp
          repeat linarith [alg.tpos]
        rw [sub_right_comm]; apply aux
  have iter : ∀ i : ℕ, alg.x (i + 1) = alg.x i - alg.t • Gt (alg.x i) := by
    intro i
    apply prox_unique_of_convex
    apply th'; apply alg.update i; simp [Gt]; rw [smul_inv_smul₀, ← sub_add]; simp
    rw [prox_point_c']; apply Classical.choose_spec; linarith [alg.tpos]
  have φdecrease : ∀ i : ℕ, φ (alg.x (i + 1)) ≤ φ (alg.x i) := by
    intro i
    specialize φieq1 (alg.x i)
    rw [iter i]
    calc
      φ ((alg.x i) - alg.t • Gt (alg.x i)) ≤ φ (alg.x i)
        + ⟪Gt (alg.x i), (alg.x i) - (alg.x i)⟫_ℝ
        - alg.t / 2 * ‖Gt (alg.x i)‖ ^ 2 := by
        linarith [univieq (alg.x i) (alg.x i)]
      _ ≤ φ (alg.x i) := by
        simp; apply mul_nonneg; linarith [alg.tpos]; apply sq_nonneg
  have φdecrease' : ∀ i j : ℕ, (i ≤ j) → φ (alg.x j) ≤ φ (alg.x i) := by
    intro i j ilej
    let φx := fun n : ℕ ↦ φ (alg.x (n + i))
    have aux : (Finset.sum (Finset.range (j - i)) fun (n : ℕ) => φx (n + 1) - φx n)
        = φx (j - i) - φx 0 := by apply Finset.sum_range_sub
    let diffφ := fun n : ℕ ↦ φx (n + 1) - φx n
    have diffφle : ∀ n : ℕ, diffφ n ≤ 0 := by
      intro n
      show φ (alg.x (n + 1 + i)) - φ (alg.x (n + i)) ≤ 0
      rw [add_right_comm]; linarith [φdecrease (n + i)]
    have nonpos : φx (j - i) - φx 0 ≤ 0 := by
      rw [← aux]; apply Finset.sum_nonpos
      intro n _; exact diffφle n
    simp [φx] at nonpos; rw [Nat.sub_add_cancel ilej] at nonpos; exact nonpos
  have φieq3 : ∀ i k : ℕ, (i < k) → φ (alg.x k) - φ alg.xm ≤
      (1 / (2 * alg.t)) * ‖(alg.x i) - alg.xm‖ ^ 2
      - (1 / (2 * alg.t)) * ‖(alg.x (i + 1)) - alg.xm‖ ^ 2 := by
    intro i k ilt
    rw [← mul_sub]
    calc
      φ (alg.x k) - φ alg.xm ≤ φ (alg.x (i + 1)) - φ alg.xm := by
        apply sub_le_sub_right
        apply φdecrease' (i + 1) k
        linarith
      _ ≤ (1 / (2 * alg.t)) * (‖(alg.x i) - alg.xm‖ ^ 2
          - ‖(alg.x (i + 1)) - alg.xm‖ ^ 2) := by
        rw [iter i]; apply φieq1 (alg.x i)
  have ieq (k : ℕ) : k • (φ (alg.x k) - φ alg.xm) ≤
      (1 / (2 * alg.t)) * ‖(alg.x 0) - alg.xm‖ ^ 2
      - (1 / (2 * alg.t)) * ‖(alg.x k) - alg.xm‖ ^ 2 := by
    let nr := fun n : ℕ ↦ (1 / (2 * alg.t)) * ‖(alg.x n) - alg.xm‖ ^ 2
    let _ := fun _ : ℕ ↦ φ (alg.x k) - φ alg.xm
    let s := Finset.range k
    have : k = s.card := by simp [s]
    nth_rw 1 [this];
    show s.card • (φ (alg.x k) - φ alg.xm) ≤ nr 0 - nr k
    rw [← Finset.sum_range_sub', ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro i iin; apply φieq3 i; simp [s] at iin; linarith
  calc
    2 * k * alg.t * (f (alg.x k) + h (alg.x k) - f alg.xm - h alg.xm) =
        2 * alg.t * (k * (φ (alg.x k) - φ alg.xm)) := by simp [φ]; ring_nf
    _ ≤ 2 * alg.t *
        ((1 / (2 * alg.t)) * ‖(alg.x 0) - alg.xm‖ ^ 2
        - (1 / (2 * alg.t)) * ‖(alg.x k) - alg.xm‖ ^ 2) := by
      rw [mul_le_mul_iff_right₀]
      let ieq' := ieq k; simp at ieq'
      simp; apply ieq'; linarith [alg.tpos]
    _ = ‖(alg.x 0) - alg.xm‖ ^ 2 - ‖(alg.x k) - alg.xm‖ ^ 2 := by
      rw [← mul_sub, ← mul_assoc, mul_one_div_cancel]; simp; linarith [alg.tpos]
    _ ≤ ‖x₀ - alg.xm‖ ^ 2 := by rw [alg.ori]; simp
  · field_simp
    simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos, PNat.pos];
    exact proximal_gradient_method.tpos

end method
