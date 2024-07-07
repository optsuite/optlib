/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yuxuan Wu, Shengyang Xu
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strong
import Convex.Function.StronglyConvex
import Convex.Algorithm.GradientDescent

/-!
# GradientDescentStronglyConvex

## Main results

  This file mainly concentrates on the Gradient Descent algorithm for
  smooth strongly convex optimization problems.

  We prove the O(ρ^k) rate for this algorithm.

-/

section Strongly_Convex_Gradient_Descent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {m : ℝ} {f' : E → E} {xm x₀ : E} {x : ℕ → E}
variable {a : ℝ} {x y : E} {l : NNReal}

open Set

theorem Strong_convex_Lipschitz_smooth (hsc: StrongConvexOn univ m f) (mp : m > 0)
    (hf : ∀ x, HasGradientAt f (f' x) x) (h₂ : LipschitzWith l f') (hl : l > (0 : ℝ)):
    inner (f' x - f' y) (x - y) ≥ m * l / (m + l) * ‖x - y‖ ^ 2
    + 1 / (m + l) * ‖f' x - f' y‖ ^ 2 := by
  rw [StrongConvexOn, UniformConvexOn] at hsc
  rcases hsc with ⟨cov, hsc⟩
  let phi : E → ℝ := fun x ↦ l / 2 * ‖x‖ ^ 2 - f x
  have convphi : ConvexOn ℝ univ phi := by
    apply lipschitz_to_lnorm_sub_convex
    apply cov; simp; apply hf; rw [← lipschitzOn_univ] at h₂; apply h₂; apply hl
  let g : E → ℝ := fun x ↦ f x - m / 2 * ‖x‖ ^ 2
  let g' : E → E := fun x ↦ f' x - m • x
  let h : E → ℝ := fun x ↦ (l - m) / 2 * ‖x‖ ^ 2 - g x
  have gderiv :
    ∀ (x : E), HasGradientAt g (g' x) x := by
      intro x
      apply sub_normsquare_gradient; show ∀ x ∈ univ, HasGradientAt f (f' x) x
      simp; apply hf; simp
  have convg : ConvexOn ℝ univ g := by
      rw [← strongConvexOn_iff_convex, StrongConvexOn, UniformConvexOn]
      use cov
  have convh : ConvexOn ℝ univ h := by
    have (x : E) : h x = phi x := by
        field_simp [phi, h]; ring_nf
    rw [ConvexOn]; use cov; intro x xin y yin a b apos bpos absum1
    rw [this, this, this]
    rw [ConvexOn] at convphi
    apply convphi.2 xin yin apos bpos absum1
  by_cases coef: 0 < l - m
  · have eq1 : inner (g' x - g' y) (x - y) ≥ 1 / (l - m) * ‖g' x - g' y‖ ^ 2 := by
      apply convex_to_lower gderiv
      show ConvexOn ℝ univ h; apply convh; apply coef; apply convg
    let alpha : E := f' x - f' y
    let beta : E := x - y
    have eq2 : g' x - g' y = alpha - m • beta := by
      simp [g']; rw [smul_sub]; rw [← sub_add, ← sub_add]; simp
      rw [sub_right_comm]
    rw [eq2] at eq1
    have eq3 (u v : E) : inner (u - m • v) v ≥ 1 / (l - m) * ‖u - m • v‖ ^ 2
      → inner u v ≥ m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2 := by
      have : ‖u - m • v‖ ^ 2 = ‖u‖ ^ 2 + m ^ 2 * ‖v‖ ^ 2 - 2 * m * inner u v := by
        rw [norm_sub_sq_real, inner_smul_right]; ring_nf; rw [norm_smul]; simp
        rw [mul_pow, sq_abs]
      rw [this]
      intro h0; rw [inner_sub_left, inner_smul_left] at h0; field_simp at h0
      rw [real_inner_self_eq_norm_sq, div_le_iff] at h0
      field_simp at h0; rw [sub_mul, sub_add_eq_add_sub, le_sub_iff_add_le] at h0
      rw [mul_right_comm, mul_sub] at h0; ring_nf at h0
      rw [mul_right_comm, ← add_mul] at h0
      have mlpos : 0 < m + l := by linarith
      rw [ge_iff_le]
      field_simp; rw [add_comm]
      calc
        _ ≤ ((m + l) * inner u v) / (m + l) := by
          rw [div_le_div_right]; apply h0; apply mlpos
        _ = inner u v := by field_simp
      apply coef
    show inner alpha beta ≥ m * l / (m + l) * ‖beta‖ ^ 2 + 1 / (m + l) * ‖alpha‖ ^ 2
    apply eq3
    show inner (alpha - m • beta) (x - y) ≥ 1 / (l - m) * ‖alpha - m • beta‖ ^ 2
    apply eq1
  · let alpha : E := f' x - f' y
    let beta : E := x - y
    have eq1 : inner alpha beta ≥ m * ‖beta‖ ^ 2 := by
      show inner (f' x - f' y) (x - y) ≥ m * ‖x - y‖ ^ 2
      apply Strong_Convex_lower; rw [StrongConvexOn, UniformConvexOn]
      use cov; simp; apply hf; simp; simp
    have eq2 : inner alpha beta ≥ 1 / l * ‖alpha‖ ^ 2 := by
      show inner (f' x - f' y) (x - y) ≥ 1 / l * ‖f' x - f' y‖ ^ 2
      apply lipschitz_to_lower hf h₂
      apply StrictConvexOn.convexOn; apply StrongConvexOn.strictConvexOn
      rw [StrongConvexOn, UniformConvexOn]; use cov; apply mp; apply hl
    rw [ge_iff_le] at eq1
    rw [ge_iff_le] at eq2
    have mlpos : 0 < m + l := by linarith
    have eq3 (u v : E) (h1 : m * ‖v‖ ^ 2 ≤ inner u v) (h2 : 1 / l * ‖u‖ ^ 2 ≤ inner u v):
      inner u v ≥ m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2 := by
        field_simp; rw [div_le_iff mlpos, mul_comm _ (m + l), add_mul]
        have eq4 : m * l * ‖v‖ ^ 2  ≤ m * inner u v := by
          calc
            _ ≤ m * m * ‖v‖ ^ 2 := by
              rw [mul_comm m l, mul_assoc, mul_assoc]
              have : 0 ≤ ‖v‖ ^ 2 := by simp
              apply mul_le_mul_of_nonneg_right
              simp at coef; apply coef
              rw [mul_nonneg_iff_right_nonneg_of_pos]; simp; apply mp
            _ ≤ m * inner u v := by
              rw [mul_assoc, mul_le_mul_left]; apply h1; apply mp
        have eq5 : ‖u‖ ^ 2 ≤ l * inner u v := by
          field_simp at h2; rw [mul_comm, ← div_le_iff]; apply h2; apply hl
        linarith
    show inner alpha beta ≥ m * l / (m + l) * ‖beta‖ ^ 2 + 1 / (m + l) * ‖alpha‖ ^ 2
    apply eq3; apply eq2; apply eq1

lemma lipschitz_derivxm_eq_zero (h₁ : ∀ x : E, HasGradientAt f (f' x) x)
    (h₂ : LipschitzWith l f') (min: IsMinOn f Set.univ xm) (hl: l > (0 : ℝ)) : f' xm = 0 := by
  have eq1 : ∀ x : E, 1 / (2 * l) * ‖f' x‖ ^ 2 ≤ f x - f xm := by
    apply lipschitz_minima_lower_bound h₁ h₂ min hl
  specialize eq1 xm
  field_simp at eq1
  have _ : (0 : ℝ) < 2 * l := by linarith
  have eq3 : 0 ≤ ‖f' xm‖ ^ 2 / (2 * l) := by
    apply div_nonneg; simp; linarith
  have eq4 : ‖f' xm‖ ^ 2 / (2 * l) = 0 := by linarith
  field_simp at eq4; exact eq4

variable (hsc: StrongConvexOn univ m f) {alg : Gradient_Descent_fix_stepsize f f' x₀}

lemma gradient_method_strong_convex (hm : m > 0) (min : IsMinOn f univ xm)
    (step₂ : alg.a ≤ 2 / (m + alg.l)) : ∀ k : ℕ , ‖alg.x k - xm‖ ^ 2 ≤ (1 - alg.a *
    (2 * m * alg.l / (m + alg.l))) ^ k * ‖x₀ - xm‖ ^ 2 := by
  have : LipschitzWith alg.l f' := alg.smooth
  have : alg.l > (0 : ℝ) := alg.hl
  have reduction : ∀ k : ℕ ,
    ‖alg.x (k + 1) - xm‖ ^ 2 ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l)))
    * ‖alg.x k - xm‖ ^ 2 := by
      intro k
      rw [alg.update k]
      calc
      _ = ‖alg.x k - xm - alg.a • f' (alg.x k)‖ ^ 2 := by
        rw [sub_right_comm]
      _ = ‖alg.x k - xm‖ ^ 2 - 2 * alg.a * inner (alg.x k - xm) (f' (alg.x k))
        + alg.a ^ 2 * ‖f' (alg.x k)‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_smul_right]
        ring_nf; rw [norm_smul]; simp; rw [mul_pow, sq_abs]
      _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) * ‖alg.x k - xm‖ ^ 2
        + alg.a * (alg.a - 2 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2 := by
        have : inner (alg.x k - xm) (f' (alg.x k)) ≥
            m * alg.l / (m + alg.l) * ‖alg.x k - xm‖ ^ 2
            + 1 / (m + alg.l) * ‖f' (alg.x k)‖ ^ 2 := by
          have eq1 : f' (alg.x k) = f' (alg.x k) - f' xm := by
            apply eq_sub_of_add_eq; simp
            apply lipschitz_derivxm_eq_zero alg.diff alg.smooth min this
          rw [eq1, real_inner_comm]
          apply Strong_convex_Lipschitz_smooth; apply hsc; apply hm;
          apply alg.diff; apply alg.smooth; apply alg.hl
        rw [sub_mul, one_mul, mul_sub, sub_mul, ← add_comm_sub, ← pow_two]
        apply add_le_add_right
        rw [sub_eq_add_neg, sub_sub]; rw [sub_eq_add_neg (‖alg.x k - xm‖ ^ 2)]
        apply add_le_add_left; apply neg_le_neg
        calc
          _ =
            2 * alg.a * ((m * alg.l / (m + alg.l)) * ‖alg.x k - xm‖ ^ 2 +
                (1 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2) := by
              field_simp; rw [mul_add, mul_comm alg.a 2, ← mul_assoc, ← mul_assoc, mul_comm alg.a 2]
              ring_nf
          _ ≤ 2 * alg.a * inner (alg.x k - xm) (f' (alg.x k)) := by
            rw [ge_iff_le] at this
            have twoapos : 0 < 2 * alg.a := by linarith [alg.step₁]
            rw [mul_le_mul_left twoapos]; apply this
      _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) * ‖alg.x k - xm‖ ^ 2 := by
        simp
        have eq2 : alg.a * (alg.a - 2 / (m + alg.l)) ≤ 0 := by
          rw [← neg_le_neg_iff, mul_comm, ← neg_mul]; simp; apply mul_nonneg
          linarith; linarith [alg.step₁]
        have eq3 : 0 ≤ ‖f' (alg.x k)‖ ^ 2 := by simp
        apply mul_nonpos_of_nonpos_of_nonneg eq2 eq3
  have eq : 0 ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) := by
    have : 0 < m + alg.l := by linarith
    field_simp; rw [div_nonneg_iff]; left
    constructor
    · simp
      calc
        alg.a * (2 * m * alg.l) ≤ 2 / (m + alg.l) * (2 * m * alg.l) := by
          rw [mul_le_mul_right]; linarith [step₂, alg.step₁];
          apply mul_pos <;> linarith
        _ ≤ (m + alg.l) ^ 2 / (m + alg.l) := by
          field_simp; rw [div_le_div_right this]
          ring_nf
          calc
            _ ≤ m * alg.l * 4 + (m - alg.l) ^ 2 := by
              simp; apply sq_nonneg
            _ = m * alg.l * 2 + m ^ 2 + alg.l ^ 2 := by ring_nf
        _ = (m + alg.l) := by
          rw [pow_two]; simp
    · linarith
  intro k
  induction' k with q IH1
  · simp; rw [alg.initial]
  · calc
    _ = ‖alg.x (q + 1) - xm‖ ^ 2 := by simp
    _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) * ‖alg.x q - xm‖ ^ 2 := by
      apply reduction
    _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) *
      (1 - alg.a * (2 * m * alg.l / (m + alg.l))) ^ q * ‖x₀ - xm‖ ^ 2 := by
        rw [mul_assoc _ _ (‖x₀ - xm‖ ^ 2)]
        apply mul_le_mul_of_nonneg_left; apply IH1; apply eq
    _ = (1 - alg.a * (2 * m * alg.l / (m + alg.l))) ^ (q + 1) * ‖x₀ - xm‖ ^ 2 := by
        simp; left; rw [pow_succ, pow_mul_comm']
    _ = (1 - alg.a * (2 * m * alg.l / (m + alg.l))) ^ Nat.succ q * ‖x₀ - xm‖ ^ 2 := by simp

end Strongly_Convex_Gradient_Descent
