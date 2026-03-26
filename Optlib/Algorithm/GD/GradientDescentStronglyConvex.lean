/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yuxuan Wu, Shengyang Xu
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strong
import Optlib.Convex.StronglyConvex
import Optlib.Algorithm.GD.GradientDescent

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
    inner ℝ (f' x - f' y) (x - y) ≥ m * l / (m + l) * ‖x - y‖ ^ 2
    + 1 / (m + l) * ‖f' x - f' y‖ ^ 2 := by
  rw [StrongConvexOn, UniformConvexOn] at hsc
  rcases hsc with ⟨cov, hsc⟩
  let phi : E → ℝ := fun x ↦ l / 2 * ‖x‖ ^ 2 - f x
  have convphi : ConvexOn ℝ univ phi := by
    apply lipschitz_to_lnorm_sub_convex
    apply cov; simp; apply hf; rw [← lipschitzOnWith_univ] at h₂; apply h₂; apply hl
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
        simp [phi, h, g]
        ring
    rw [ConvexOn]; use cov; intro x xin y yin a b apos bpos absum1
    rw [this, this, this]
    rw [ConvexOn] at convphi
    apply convphi.2 xin yin apos bpos absum1
  by_cases coef: 0 < l - m
  · have eq1 : inner ℝ (g' x - g' y) (x - y) ≥ 1 / (l - m) * ‖g' x - g' y‖ ^ 2 := by
      apply convex_to_lower gderiv
      show ConvexOn ℝ univ h; apply convh; apply coef; apply convg
    let alpha : E := f' x - f' y
    let beta : E := x - y
    have eq2 : g' x - g' y = alpha - m • beta := by
      simp [g']; rw [smul_sub]; rw [← sub_add, ← sub_add]; simp
      rw [sub_right_comm]
    rw [eq2] at eq1
    have eq3 (u v : E) : inner ℝ (u - m • v) v ≥ 1 / (l - m) * ‖u - m • v‖ ^ 2
      → inner ℝ u v ≥ m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2 := by
      have : ‖u - m • v‖ ^ 2 = ‖u‖ ^ 2 + m ^ 2 * ‖v‖ ^ 2 - 2 * m * inner ℝ u v := by
        rw [norm_sub_sq_real, inner_smul_right]; ring_nf; rw [norm_smul]; simp
        rw [mul_pow, sq_abs]
      rw [this]
      intro h0; rw [inner_sub_left, inner_smul_left] at h0; field_simp at h0
      rw [real_inner_self_eq_norm_sq] at h0
      have h0' : ‖u‖ ^ 2 + m ^ 2 * ‖v‖ ^ 2 - 2 * m * inner ℝ u v ≤
          (l - m) * (inner ℝ u v - m * ‖v‖ ^ 2) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h0
      have mlpos : 0 < m + l := by linarith
      rw [ge_iff_le]
      field_simp [mlpos.ne']
      nlinarith [h0']
    show inner ℝ alpha beta ≥ m * l / (m + l) * ‖beta‖ ^ 2 + 1 / (m + l) * ‖alpha‖ ^ 2
    apply eq3
    show inner ℝ (alpha - m • beta) (x - y) ≥ 1 / (l - m) * ‖alpha - m • beta‖ ^ 2
    apply eq1
  · let alpha : E := f' x - f' y
    let beta : E := x - y
    have eq1 : inner ℝ alpha beta ≥ m * ‖beta‖ ^ 2 := by
      show inner ℝ (f' x - f' y) (x - y) ≥ m * ‖x - y‖ ^ 2
      apply Strong_Convex_lower; rw [StrongConvexOn, UniformConvexOn]
      use cov; simp; apply hf; simp; simp
    have eq2 : inner ℝ alpha beta ≥ 1 / l * ‖alpha‖ ^ 2 := by
      show inner ℝ (f' x - f' y) (x - y) ≥ 1 / l * ‖f' x - f' y‖ ^ 2
      apply lipschitz_to_lower hf h₂
      apply StrictConvexOn.convexOn; apply StrongConvexOn.strictConvexOn
      rw [StrongConvexOn, UniformConvexOn]; use cov; apply mp; apply hl
    rw [ge_iff_le] at eq1
    rw [ge_iff_le] at eq2
    have mlpos : 0 < m + l := by linarith
    have eq3 (u v : E) (h1 : m * ‖v‖ ^ 2 ≤ inner ℝ u v) (h2 : 1 / l * ‖u‖ ^ 2 ≤ inner ℝ u v):
      inner ℝ u v ≥ m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2 := by
        rw [ge_iff_le]
        field_simp [mlpos.ne']
        have hmnonneg : 0 ≤ m := by linarith [mp]
        have hlnonneg : 0 ≤ (l : ℝ) := by linarith [hl]
        have hlem : (l : ℝ) ≤ m := by linarith [coef]
        have eq4 : m * l * ‖v‖ ^ 2  ≤ m * inner ℝ u v := by
          calc
            _ ≤ m * m * ‖v‖ ^ 2 := by
              have : l * (m * ‖v‖ ^ 2) ≤ m * (m * ‖v‖ ^ 2) := by
                apply mul_le_mul_of_nonneg_right hlem
                exact mul_nonneg hmnonneg (by positivity)
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
            _ ≤ m * inner ℝ u v := by
              simpa [mul_assoc] using mul_le_mul_of_nonneg_left h1 hmnonneg
        have eq5 : ‖u‖ ^ 2 ≤ l * inner ℝ u v := by
          have hlne : (l : ℝ) ≠ 0 := by linarith [hl]
          have : l * (1 / l * ‖u‖ ^ 2) ≤ l * inner ℝ u v := mul_le_mul_of_nonneg_left h2 hlnonneg
          simpa [mul_assoc, hlne] using this
        nlinarith [eq4, eq5]
    show inner ℝ alpha beta ≥ m * l / (m + l) * ‖beta‖ ^ 2 + 1 / (m + l) * ‖alpha‖ ^ 2
    apply eq3; apply eq2; apply eq1

lemma lipschitz_derivxm_eq_zero (h₁ : ∀ x : E, HasGradientAt f (f' x) x)
    (h₂ : LipschitzWith l f') (min: IsMinOn f Set.univ xm) (hl: l > (0 : ℝ)) : f' xm = 0 := by
  have eq1 : ∀ x : E, 1 / (2 * l) * ‖f' x‖ ^ 2 ≤ f x - f xm := by
    apply lipschitz_minima_lower_bound h₁ h₂ min hl
  specialize eq1 xm
  have hnonneg : 0 ≤ 1 / (2 * l) * ‖f' xm‖ ^ 2 := by positivity
  have hle : 1 / (2 * l) * ‖f' xm‖ ^ 2 ≤ 0 := by simpa using eq1
  have hzero : 1 / (2 * l) * ‖f' xm‖ ^ 2 = 0 := le_antisymm hle hnonneg
  have hcoef : (1 / (2 * l : ℝ)) ≠ 0 := by positivity
  have hsq : ‖f' xm‖ ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left hcoef
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

variable (hsc: StrongConvexOn univ m f) {alg : Gradient_Descent_fix_stepsize f f' x₀}

lemma gradient_method_strong_convex (hm : m > 0) (min : IsMinOn f univ xm)
    (step₂ : alg.a ≤ 2 / (m + alg.l)) (hsc: StrongConvexOn univ m f) :
    ∀ k : ℕ , ‖alg.x k - xm‖ ^ 2 ≤ (1 - alg.a *
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
      _ = ‖alg.x k - xm‖ ^ 2 - 2 * alg.a * inner ℝ (alg.x k - xm) (f' (alg.x k))
        + alg.a ^ 2 * ‖f' (alg.x k)‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_smul_right]
        ring_nf; rw [norm_smul]; simp; rw [mul_pow, sq_abs]
      _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) * ‖alg.x k - xm‖ ^ 2
        + alg.a * (alg.a - 2 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2 := by
        have : inner ℝ (alg.x k - xm) (f' (alg.x k)) ≥
            m * alg.l / (m + alg.l) * ‖alg.x k - xm‖ ^ 2
            + 1 / (m + alg.l) * ‖f' (alg.x k)‖ ^ 2 := by
          have eq1 : f' (alg.x k) = f' (alg.x k) - f' xm := by
            apply eq_sub_of_add_eq; simp
            apply lipschitz_derivxm_eq_zero alg.diff alg.smooth min this
          rw [eq1, real_inner_comm]
          apply Strong_convex_Lipschitz_smooth; apply hsc; apply hm;
          apply alg.diff; apply alg.smooth; apply alg.hl
        rw [sub_mul, one_mul, mul_sub, sub_mul, ← add_comm_sub, ← pow_two]
        have this_le :
            (m * alg.l / (m + alg.l)) * ‖alg.x k - xm‖ ^ 2
              + 1 / (m + alg.l) * ‖f' (alg.x k)‖ ^ 2 ≤
            inner ℝ (alg.x k - xm) (f' (alg.x k)) := by
          simpa [ge_iff_le] using this
        have hmul :
            (2 * alg.a) *
              ((m * alg.l / (m + alg.l)) * ‖alg.x k - xm‖ ^ 2
                + 1 / (m + alg.l) * ‖f' (alg.x k)‖ ^ 2) ≤
            (2 * alg.a) * inner ℝ (alg.x k - xm) (f' (alg.x k)) := by
          apply mul_le_mul_of_nonneg_left this_le
          linarith [alg.step₁]
        have hnegTerm :
            -2 * alg.a * inner ℝ (alg.x k - xm) (f' (alg.x k)) ≤
              -alg.a * (2 * m * alg.l / (m + alg.l)) * ‖alg.x k - xm‖ ^ 2
                - alg.a * (2 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2 := by
          have hnegTerm0 : -(2 * alg.a * inner ℝ (alg.x k - xm) (f' (alg.x k))) ≤
              -(2 * alg.a *
                ((m * alg.l / (m + alg.l)) * ‖alg.x k - xm‖ ^ 2
                  + 1 / (m + alg.l) * ‖f' (alg.x k)‖ ^ 2)) := neg_le_neg hmul
          have hleft : -(2 * alg.a * inner ℝ (alg.x k - xm) (f' (alg.x k))) =
              -2 * alg.a * inner ℝ (alg.x k - xm) (f' (alg.x k)) := by ring
          have hright : -(2 * alg.a *
              ((m * alg.l / (m + alg.l)) * ‖alg.x k - xm‖ ^ 2
                + 1 / (m + alg.l) * ‖f' (alg.x k)‖ ^ 2)) =
              -alg.a * (2 * m * alg.l / (m + alg.l)) * ‖alg.x k - xm‖ ^ 2
                - alg.a * (2 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2 := by ring
          rw [hleft, hright] at hnegTerm0
          exact hnegTerm0
        have hmid0 := add_le_add_left hnegTerm (‖alg.x k - xm‖ ^ 2)
        have hmid1 := add_le_add_right hmid0 (alg.a ^ 2 * ‖f' (alg.x k)‖ ^ 2)
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmid1
      _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) * ‖alg.x k - xm‖ ^ 2 := by
        simp
        have eq2 : alg.a * (alg.a - 2 / (m + alg.l)) ≤ 0 := by
          rw [← neg_le_neg_iff, mul_comm, ← neg_mul]; simp; apply mul_nonneg
          linarith; linarith [alg.step₁]
        have eq3 : 0 ≤ ‖f' (alg.x k)‖ ^ 2 := by simp
        apply mul_nonpos_of_nonpos_of_nonneg eq2 eq3
  have eq : 0 ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) := by
    have hmlpos : 0 < m + alg.l := by linarith
    have hcoef_nonneg : 0 ≤ 2 * m * alg.l / (m + alg.l) := by positivity
    have hbound1 :
        alg.a * (2 * m * alg.l / (m + alg.l)) ≤
          (2 / (m + alg.l)) * (2 * m * alg.l / (m + alg.l)) := by
      exact mul_le_mul_of_nonneg_right step₂ hcoef_nonneg
    have hsq : 4 * m * alg.l ≤ (m + alg.l) ^ 2 := by
      nlinarith [sq_nonneg (m - alg.l)]
    have hbound2 : (2 / (m + alg.l)) * (2 * m * alg.l / (m + alg.l)) ≤ (1 : ℝ) := by
      have hmlnz : (m + alg.l : ℝ) ≠ 0 := by linarith
      field_simp [hmlnz]
      nlinarith [sq_nonneg (m - alg.l)]
    have hbound : alg.a * (2 * m * alg.l / (m + alg.l)) ≤ (1 : ℝ) := le_trans hbound1 hbound2
    linarith
  intro k
  induction k with
  | zero =>
      simp [alg.initial]
  | succ q IH1 =>
      calc
      _ = ‖alg.x (q + 1) - xm‖ ^ 2 := by simp
      _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) * ‖alg.x q - xm‖ ^ 2 := by
        apply reduction
      _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) *
        (1 - alg.a * (2 * m * alg.l / (m + alg.l))) ^ q * ‖x₀ - xm‖ ^ 2 := by
          rw [mul_assoc _ _ (‖x₀ - xm‖ ^ 2)]
          apply mul_le_mul_of_nonneg_left IH1 eq
      _ = (1 - alg.a * (2 * m * alg.l / (m + alg.l))) ^ (q + 1) * ‖x₀ - xm‖ ^ 2 := by
          rw [pow_succ]
          ring

end Strongly_Convex_Gradient_Descent
