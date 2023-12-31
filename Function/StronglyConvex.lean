/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yuxuan Wu, Shengyang Xu
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strong
import Analysis.Calculation
import Function.Lsmooth
import Function.Convex_Function

/-!
  the properties of strongly convex function and gradient descent method
  for strongly convex function
-/
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Strongly_Convex

variable {s : Set E} {f : E → ℝ} {m : ℝ} {xm xm': E} {f' : E → E} {mp : m > 0}

open Set InnerProductSpace

theorem Strongly_Convex_Bound (m : ℝ) (strongly_convex: StrongConvexOn s m f):
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
     ∀ ⦃a⦄, 0 < a → ∀ ⦃b⦄, 0 < b → a + b = 1 → f (a • x + b • y)
       ≤ a * f x + b * f y - m / 2 * a * b * ‖x - y‖ ^ 2 := by
  intro x xs y ys a ap b bp abp
  rcases strongly_convex with ⟨_, sc⟩
  have anneg : a ≥ 0 := by linarith
  have bnneg : b ≥ 0 := by linarith
  rcases sc xs ys anneg bnneg abp with ineq
  simp at ineq
  rw [mul_comm (m / 2), mul_assoc a, mul_comm (m / 2),← mul_assoc, mul_assoc (a * b)]
  apply ineq

theorem stronglyConvexOn_def (hs : Convex ℝ s)
    (hfun : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∀ ⦃a⦄, 0 ≤ a → ∀ ⦃b⦄, 0 ≤ b → a + b = 1 → f (a • x + b • y)
        ≤ a * f x + b * f y - m / 2 * a * b * ‖x - y‖ ^ 2) :
    StrongConvexOn s m f := by
  constructor
  · exact hs
  intro x hx y hy a b ha hb hab
  specialize hfun hx hy ha hb hab
  dsimp
  have : m / 2 * a * b * ‖x - y‖ ^ 2 = a * b * (m / 2 * ‖x - y‖ ^ 2) := by ring_nf
  simp at this;
  rw [← this]; exact hfun

theorem Strongly_Convex_Unique_Minima (hsc: StrongConvexOn s m f)
    (min: IsMinOn f s xm) (min' : IsMinOn f s xm') (hxm : xm ∈ s) (hxm' : xm' ∈ s): xm = xm' := by
  by_contra neq
  push_neg at neq
  have eq : f xm = f xm' := by
    apply le_antisymm
    . apply min hxm'
    . apply min' hxm
  let x := (2 : ℝ)⁻¹ • xm + (2 : ℝ)⁻¹ • xm'
  have xeq : x = (2 : ℝ)⁻¹ • xm + (2 : ℝ)⁻¹ • xm' := by rfl
  rcases hsc with ⟨cr, sc⟩
  have : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have p : (0 : ℝ) < 1 / 2 := by norm_num
  have xs : x ∈ s := by
    rcases convex_iff_forall_pos.mp cr hxm hxm' p p (by norm_num) with cxs
    simp at cxs
    rw [← xeq] at cxs
    apply cxs
  specialize sc hxm hxm' this this (by norm_num)
  simp at sc
  rw [← xeq,← eq] at sc
  rw [← two_mul,← mul_assoc, mul_inv_cancel (by norm_num), one_mul] at sc
  have normp : ‖xm - xm'‖ > 0 := by
    apply norm_sub_pos_iff.mpr
    apply neq
  have nng : m / 2 * ‖xm - xm'‖ ^ 2 > 0 := by
    apply mul_pos
    . linarith
    . apply pow_pos; linarith
  apply absurd (min xs)
  simp [← xeq]
  calc
    f x ≤ f xm - 2⁻¹ * 2⁻¹ * (m / 2 * ‖xm - xm'‖ ^ 2) := by apply sc
    _ < f xm := by apply lt_of_sub_pos; simp; apply nng

lemma sub_normsquare_gradient (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) (m : ℝ):
    ∀ x ∈ s, HasGradientAt (fun x ↦ f x - m / 2 * ‖x‖ ^ 2) (f' x - m • x) x := by
  intro x xs
  apply HasGradientAt.sub
  . apply hf x xs
  . have u := HasGradientAt.const_smul (gradient_norm_sq_eq_two_self x) (m / 2)
    simp at u
    rw [smul_smul, div_mul_cancel] at u
    apply u; norm_num

theorem Strong_Convex_lower (hsc: StrongConvexOn s m f) (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ∀ x ∈ s, ∀ y ∈ s, inner (f' x - f' y) (x - y) ≥ m * ‖x - y‖ ^ 2 := by
  intro x xs y ys
  have cvx := strongConvexOn_iff_convex.mp hsc
  have grd := sub_normsquare_gradient hf m
  have grm := convex_monotone_gradient' cvx grd x xs y ys
  rw [sub_sub, add_sub, add_comm, ← add_sub, ← sub_sub, inner_sub_left, ← smul_sub] at grm
  apply le_of_sub_nonneg at grm
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at grm
  apply grm

theorem Lower_Strong_Convex (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∀ y ∈ s, inner (f' x - f' y) (x - y) ≥ m * ‖x - y‖ ^ 2) :
    StrongConvexOn s m f := by
  apply strongConvexOn_iff_convex.mpr
  have grd := sub_normsquare_gradient hf m
  apply monotone_gradient_convex' hs grd
  intro x xs y ys
  specialize h x xs y ys
  rw [sub_sub, add_sub, add_comm, ← add_sub, ← sub_sub, inner_sub_left, ← smul_sub]
  apply sub_nonneg_of_le
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  apply h

theorem Strong_Convex_second_lower (hsc: StrongConvexOn s m f)
    (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) : ∀ x ∈ s, ∀ y ∈ s,
    f y ≥ f x + inner (f' x) (y - x) + m / 2 * ‖y - x‖ ^ 2 := by
  intro x xs y ys
  have cvx := strongConvexOn_iff_convex.mp hsc
  have grd := sub_normsquare_gradient hf m x xs
  let g := fun x ↦ f' x - m • x
  have : g x = f' x - m • x := by rfl
  rw [← this] at grd
  have foc := first_order_condition' grd cvx xs y ys
  rw [this] at foc
  apply sub_nonneg_of_le at foc
  apply le_of_sub_nonneg
  rw [sub_right_comm, sub_add, ← sub_add, add_sub, add_sub_right_comm] at foc
  rw [inner_sub_left, sub_add, sub_sub (f y), sub_sub, add_sub, add_sub] at foc
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, sub_add, ← mul_sub] at foc
  nth_rw 7 [← zero_add x] at foc
  nth_rw 5 [← sub_zero y] at foc
  nth_rw 1 [← sub_self y] at foc
  rw [← sub_self x] at foc
  rw [sub_add, ← sub_add y x x, add_comm (y - x), inner_sub_right x, inner_add_right y] at foc
  rw [real_inner_comm x y, sub_right_comm (inner x y), ← sub_sub, sub_self, sub_sub 0] at foc
  rw [← inner_add_left, zero_sub, mul_neg, sub_neg_eq_add] at foc
  have : m = m / 2 * 2 := by simp
  nth_rw 1 [this] at foc
  rw [← smul_smul, inner_smul_left, two_smul] at foc
  simp only [map_div₀, IsROrC.conj_to_real, map_ofNat] at foc
  rw [sub_add, ← mul_sub, ← inner_sub_left, ← sub_sub, sub_right_comm, add_sub_cancel] at foc
  have : x - y = - (y - x) := by simp
  rw [this, inner_neg_left, mul_neg, sub_neg_eq_add, real_inner_self_eq_norm_sq] at foc
  apply foc

end Strongly_Convex
