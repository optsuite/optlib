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
open scoped InnerProductSpace BigOperators RealInnerProductSpace

theorem Strong_convex_Lipschitz_smooth (hsc: StrongConvexOn univ m f) (mp : m > 0)
    (hf : ∀ x, HasGradientAt f (f' x) x) (h₂ : LipschitzWith l f') (hl : l > (0 : ℝ)):
    ⟪f' x - f' y, x - y⟫_ℝ ≥ m * l / (m + l) * ‖x - y‖ ^ 2
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
        simp [phi, h]; ring_nf; simp; grind
    rw [ConvexOn]; use cov; intro x xin y yin a b apos bpos absum1
    rw [this, this, this]
    rw [ConvexOn] at convphi
    apply convphi.2 xin yin apos bpos absum1
  by_cases coef: 0 < l - m
  · have eq1 : ⟪g' x - g' y, x - y⟫_ℝ ≥ 1 / (l - m) * ‖g' x - g' y‖ ^ 2 := by
      apply convex_to_lower gderiv
      show ConvexOn ℝ univ h; apply convh; apply coef; apply convg
    let alpha : E := f' x - f' y
    let beta : E := x - y
    have eq2 : g' x - g' y = alpha - m • beta := by
      simp [g']; rw [smul_sub]; rw [← sub_add, ← sub_add]; simp
      rw [sub_right_comm]
    rw [eq2] at eq1
    have eq3 (u v : E) : ⟪u - m • v, v⟫_ℝ ≥ 1 / (l - m) * ‖u - m • v‖ ^ 2
      → ⟪u, v⟫_ℝ ≥ m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2 := by
      have : ‖u - m • v‖ ^ 2 = ‖u‖ ^ 2 + m ^ 2 * ‖v‖ ^ 2 - 2 * m * ⟪u, v⟫_ℝ := by
        rw [norm_sub_sq_real, inner_smul_right]; ring_nf; rw [norm_smul]; simp
        rw [mul_pow, sq_abs]
      rw [this]
      intro h0
      rw [inner_sub_left, inner_smul_left] at h0
      simp [real_inner_self_eq_norm_sq] at h0
      rw [inv_mul_eq_div] at h0
      rw [div_le_iff₀ coef] at h0
      rw [sub_mul, add_sub_assoc, le_sub_iff_add_le] at h0
      rw [mul_right_comm, mul_sub] at h0
      ring_nf at h0
      rw [mul_right_comm] at h0
      have mlpos : 0 < m + l := by linarith
      rw [ge_iff_le]
      -- Rearrange h0 to isolate ⟪u, v⟫ on the right, then divide by (m + l) > 0
      have h1 : ‖u‖ ^ 2 + m * l * ‖v‖ ^ 2 ≤ (m + l) * ⟪u, v⟫_ℝ := by
        have h0' := add_le_add_right h0 (2 * m * ⟪u, v⟫_ℝ)
        ring_nf at h0'
        simpa [add_mul] using h0'
      have hdiv :
          (‖u‖ ^ 2 + m * l * ‖v‖ ^ 2) / (m + l) ≤ ⟪u, v⟫_ℝ := by
        have h1' : ‖u‖ ^ 2 + m * l * ‖v‖ ^ 2 ≤ ⟪u, v⟫_ℝ * (m + l) := by
          simpa [mul_comm] using h1
        exact (div_le_iff₀ mlpos).2 h1'
      -- Rewrite the left-hand side as the desired combination
      simpa [div_eq_mul_inv, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdiv
    show ⟪alpha, beta⟫_ℝ ≥ m * l / (m + l) * ‖beta‖ ^ 2 + 1 / (m + l) * ‖alpha‖ ^ 2
    apply eq3
    show ⟪alpha - m • beta, x - y⟫_ℝ ≥ 1 / (l - m) * ‖alpha - m • beta‖ ^ 2
    apply eq1
  · let alpha : E := f' x - f' y
    let beta : E := x - y
    have eq1 : ⟪alpha, beta⟫_ℝ ≥ m * ‖beta‖ ^ 2 := by
      show ⟪f' x - f' y, x - y⟫_ℝ ≥ m * ‖x - y‖ ^ 2
      apply Strong_Convex_lower; rw [StrongConvexOn, UniformConvexOn]
      use cov; simp; apply hf; simp; simp
    have eq2 : ⟪alpha, beta⟫_ℝ ≥ 1 / l * ‖alpha‖ ^ 2 := by
      show ⟪f' x - f' y, x - y⟫_ℝ ≥ 1 / l * ‖f' x - f' y‖ ^ 2
      apply lipschitz_to_lower hf h₂
      apply StrictConvexOn.convexOn; apply StrongConvexOn.strictConvexOn
      rw [StrongConvexOn, UniformConvexOn]; use cov; apply mp; apply hl
    rw [ge_iff_le] at eq1
    rw [ge_iff_le] at eq2
    have mlpos : 0 < m + l := by linarith
    have eq3 (u v : E) (h1 : m * ‖v‖ ^ 2 ≤ ⟪u, v⟫_ℝ) (h2 : 1 / l * ‖u‖ ^ 2 ≤ ⟪u, v⟫_ℝ):
      ⟪u, v⟫_ℝ ≥ m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2 := by
        field_simp; rw [ge_iff_le, div_le_iff₀ mlpos, mul_comm _ (m + l), add_mul]
        have eq4 : m * l * ‖v‖ ^ 2  ≤ m * ⟪u, v⟫_ℝ := by
          calc
            _ ≤ m * m * ‖v‖ ^ 2 := by
              rw [mul_comm m l, mul_assoc, mul_assoc]
              have : 0 ≤ ‖v‖ ^ 2 := by simp
              apply mul_le_mul_of_nonneg_right
              simp at coef; apply coef
              rw [mul_nonneg_iff_right_nonneg_of_pos]; simp; apply mp
            _ ≤ m * ⟪u, v⟫_ℝ := by
              rw [mul_assoc, mul_le_mul_iff_right₀]; apply h1; apply mp
        have eq5 : ‖u‖ ^ 2 ≤ l * ⟪u, v⟫_ℝ := by
          field_simp at h2; rw [mul_comm, ← div_le_iff₀]; apply h2; apply hl
        linarith
    show ⟪alpha, beta⟫_ℝ ≥ m * l / (m + l) * ‖beta‖ ^ 2 + 1 / (m + l) * ‖alpha‖ ^ 2
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
  field_simp at eq4; simp_all

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
      _ = ‖alg.x k - xm‖ ^ 2 - 2 * alg.a * ⟪alg.x k - xm, f' (alg.x k)⟫_ℝ
        + alg.a ^ 2 * ‖f' (alg.x k)‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_smul_right]
        ring_nf; rw [norm_smul]; simp; rw [mul_pow, sq_abs]
      _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) * ‖alg.x k - xm‖ ^ 2
        + alg.a * (alg.a - 2 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2 := by
        have : ⟪alg.x k - xm, f' (alg.x k)⟫_ℝ ≥
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
              field_simp
          _ ≤ 2 * alg.a * ⟪alg.x k - xm, f' (alg.x k)⟫_ℝ := by
            rw [ge_iff_le] at this
            have twoapos : 0 < 2 * alg.a := by linarith [alg.step₁]
            rw [mul_le_mul_iff_right₀ twoapos]; apply this
      _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) * ‖alg.x k - xm‖ ^ 2 := by
        simp
        have eq2 : alg.a * (alg.a - 2 / (m + alg.l)) ≤ 0 := by
          rw [← neg_le_neg_iff, mul_comm, ← neg_mul]; simp; apply mul_nonneg
          linarith; linarith [alg.step₁]
        have eq3 : 0 ≤ ‖f' (alg.x k)‖ ^ 2 := by simp
        apply mul_nonpos_of_nonpos_of_nonneg eq2 eq3
  have eq : 0 ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) := by
    have hpos_ml : 0 < m + alg.l := by linarith
    let t : ℝ := (2 * m * alg.l) / (m + alg.l)
    have t_nonneg : 0 ≤ t := by
      have num_nonneg : 0 ≤ 2 * m * alg.l := by
        have h2 : 0 ≤ (2 : ℝ) := by norm_num
        exact mul_nonneg (mul_nonneg h2 (le_of_lt hm)) (le_of_lt alg.hl)
      exact div_nonneg num_nonneg (le_of_lt hpos_ml)
    have hmono_ge : 1 - alg.a * t ≥ 1 - (2 / (m + alg.l)) * t := by
      have hmul := mul_le_mul_of_nonneg_right step₂ t_nonneg
      have hneg' : -(2 / (m + alg.l)) * t ≤ -(alg.a * t) := by
        simpa [ge_iff_le] using (neg_le_neg hmul)
      simp [sub_eq_add_neg]; grind
    have hfrac_le_one : (2 / (m + alg.l)) * t ≤ 1 := by
      have denom_pos : 0 < (m + alg.l) ^ 2 := by
        simpa [pow_two] using mul_pos hpos_ml hpos_ml
      have hrewrite :
          (2 / (m + alg.l)) * t =
            (4 * m * alg.l) * ((m + alg.l) ^ 2)⁻¹ := by
        unfold t
        simp [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]; grind
      have hsq : 4 * m * alg.l ≤ (m + alg.l) ^ 2 := by
        have hnonneg : 0 ≤ (m - alg.l) ^ 2 := by
          simpa using sq_nonneg (m - alg.l)
        have hbase : 0 ≤ m ^ 2 + alg.l ^ 2 - 2 * m * alg.l := by
          simp [pow_two, sub_eq_add_neg, add_assoc,
            mul_comm, mul_left_comm]; grind
        have : 4 * m * alg.l ≤ m ^ 2 + alg.l ^ 2 + 2 * m * alg.l := by
          linarith
        simp [pow_two, mul_comm, mul_left_comm]; grind
      have : (4 * m * alg.l) * ((m + alg.l) ^ 2)⁻¹ ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (le_of_lt denom_pos))
        have denom_ne_zero : (m + alg.l) ^ 2 ≠ 0 := ne_of_gt denom_pos
        simpa [mul_comm, mul_left_comm, mul_assoc, denom_ne_zero] using h
      simpa [hrewrite] using this
    have hRHS_nonneg : 0 ≤ 1 - (2 / (m + alg.l)) * t := sub_nonneg.mpr hfrac_le_one
    have hmono_le : 1 - (2 / (m + alg.l)) * t ≤ 1 - alg.a * t := by
      simpa [ge_iff_le] using hmono_ge
    exact le_trans hRHS_nonneg hmono_le
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
