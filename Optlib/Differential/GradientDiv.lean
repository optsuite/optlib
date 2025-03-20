/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Penghao Yu, Zhipeng Cao, Zaiwen Wen
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Gradient.Basic
import Optlib.Convex.ConvexFunction
import Optlib.Differential.Lemmas

/-!
# Gradient.division

## Main results

This file contains the division parts of gradient, which can't be found in `fderiv`.

As the functions discussed in this file are restricted to `E → ℝ `

Two main theorems are formalized in this file
* `HasGradientAt.one_div`, shows the gradient at `x` of `1 / f x` where `f x ≠ 0`.
* `HasGradientAt.div`, shows the gradient at `x` of `f x / g x` where `g x ≠ 0`.
-/

variable (a b c d : ℝ)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {f' : E → E} {x y : E} {s : Set E}
variable {x y grad x': E} {gradient' : E}
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

lemma Vert_abs : ‖|a| - |b|‖ ≤ ‖a - b‖ := by
  simp only [Real.norm_eq_abs]
  exact abs_abs_sub_abs_le_abs_sub a b

lemma Vert_div : ‖a / b‖ = ‖a‖ * ‖1 / b‖ := by
  simp only [norm_div, Real.norm_eq_abs, one_div, norm_inv]
  exact rfl

lemma Simplifying₁ (h₁ : a ≠ 0) (h₂ : b ≠ 0) (h₃ : ‖b‖ / 2 ≤ ‖a‖) :
    ‖1 / (b * b * a)‖ ≤ ‖2 / (b * b * b)‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div]
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h₃
  have l₁ : |1| / |b * b * a| = 1 / |b * b * a| := by norm_num
  have l₂ : |2| / |b * b * b| = 1 / (|b * b * b| / 2) := by norm_num
  rw [l₁, l₂, ← le_one_div]
  simp only [one_div, div_inv_eq_mul, one_mul]
  have l₃ : |b * b * b| / 2 = |b * b| * (|b| / 2) := by rw [mul_div, abs_mul]
  have l₄ : |b * b * a| = |b * b| * |a| := by rw [abs_mul]
  rw [l₃, l₄, mul_le_mul_left]
  apply h₃
  rw [abs_pos]
  simp only [ne_eq, mul_eq_zero, or_self]
  apply h₂
  have : 0 < |b * b * b| := by rw [abs_pos]; simp [h₂]
  have : 0 < |b * b * b| / 2 := half_pos this
  apply this
  have : 0 < |b * b * a| := by rw [abs_pos]; simp [h₁, h₂]
  exact Iff.mpr one_div_pos this

lemma Simplifying₂ (h₁ : a ≠ 0) (h₂ : 0 ≤ c) :
    ‖(2 / (a * a * a))‖ * b * (c + 1) * (d * ‖a‖ * ‖a‖ * ‖a‖ / (4 * (c + 1))) = (d / 2) * b := by
  have l₁: |(2 / (a * a * a))| = |2| / |a * a * a| := norm_div 2 (a * a * a)
  have l₂: d * ‖a‖ * ‖a‖ * ‖a‖ = d * |a * a * a| := by
    repeat rw [Real.norm_eq_abs]; rw [abs_mul, abs_mul, ← mul_assoc, ← mul_assoc]
  have l₃: (c + 1) * (d * |a * a * a| / (4 * (c + 1))) = (d * |a * a * a| / 4) := by
    have : d * |a * a * a| / (4 * (c + 1)) = (d * |a * a * a| / 4) / (c + 1):= by
      exact div_mul_eq_div_div (d * |a * a * a|) _ _
    rw [mul_comm, this]
    apply div_mul_cancel₀
    linarith
  have l₄ : |2| / |a * a * a| * b * |a * a * a| = |2| * b := by
    rw [mul_comm (|2| / |a * a * a|), mul_assoc, div_mul_cancel₀, mul_comm]
    simp only [ne_eq, abs_eq_zero, mul_eq_zero, or_self]
    apply h₁
  rw [Real.norm_eq_abs, l₁, l₂, mul_assoc,l₃, mul_comm d, ← mul_div, ← mul_assoc, l₄]
  norm_num; ring_nf

lemma div_div_mul (h₁ : a / b ≤ c) (h₂ : 0 < a) (h₃ : 0 < b) (h₄ : 0 < c):
    1 / c ≤ b / a := by
  have : a ≤ c * b := Iff.mp (div_le_iff h₃) h₁
  have : a ≤ b * c := by linarith
  apply Iff.mpr (div_le_div_iff h₄ h₂)
  rw [one_mul]
  apply this

theorem HasGradientAt.one_div (hf : HasGradientAt f grad x)(h₁: ¬ f x = (0 : ℝ)):
    HasGradientAt (fun y => (1 : ℝ) / (f y)) (- ((1 : ℝ) / (f x) ^ (2 : ℕ)) • grad) x := by
  have hf' : HasGradientAt f grad x := hf
  rw [HasGradient_iff_Convergence_Point]
  intro ε εpos
  rcases (ContinuousAt_Convergence (ContinuousAt.abs (HasGradientAt.continuousAt hf))) ε εpos with ⟨δ', _ , _⟩
  have ε1pos : 0 < ε * ‖f x‖ * ‖f x‖ / 4 := by
    apply div_pos
    repeat apply mul_pos
    apply εpos
    repeat apply Iff.mpr norm_pos_iff h₁
    norm_num
  have h₀ : ∃ δ₀ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ₀ → ‖f x‖ / 2 ≤ ‖f x'‖ := by
    have absh : ∃ δ₀ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ₀ →
        ‖|f x'| - |f x|‖ ≤ ‖f x‖ / 2 := by
      apply (ContinuousAt_Convergence (ContinuousAt.abs (HasGradientAt.continuousAt hf)))
      apply div_pos
      apply Iff.mpr norm_pos_iff h₁
      norm_num
    have absh' : ∃ δ₀ > (0 : ℝ), ∀ (x' : E),
        ‖x - x'‖ ≤ δ₀ → |f x| - ‖f x‖/2 ≤ ‖f x'‖ := by
      rcases absh with ⟨δ₀, δ₀pos, so⟩
      use δ₀
      constructor
      apply δ₀pos
      intro x' h
      specialize so x' h
      exact sub_le_of_abs_sub_le_left so
    have equal : |f x| - ‖f x‖/2 = ‖f x‖/2 := by
      exact sub_half |f x|
    rw [equal] at absh'
    apply absh'
  rcases h₀ with ⟨δ₀, δ₀pos, hδ₀⟩
  rw [HasGradient_iff_Convergence_Point] at hf
  rcases hf (ε * ‖f x‖ * ‖f x‖ /4) ε1pos with ⟨δ'',δ''pos,hm2⟩
  have h₂ : ∃ δ₂ > (0 : ℝ ), ∀ (x' : E), ‖x - x'‖ ≤ δ₂ →
    ‖f x - f x' + ⟪grad, (x' - x)⟫‖ ≤ ε * ‖f x‖ * ‖f x‖/4 * ‖x - x'‖ := by
    use δ''
    constructor
    apply δ''pos
    intro x' h'
    have sep2 : ∀ (x' : E), ‖x - x'‖ ≤ δ'' →
      ‖f x - f x' + ⟪grad, (x' - x)⟫‖ ≤ ε * ‖f x‖ * ‖f x‖/4 * ‖x - x'‖ := by
        intro x1 hp1
        specialize hm2 x1 hp1
        have hp' : ‖f x - f x1 + ⟪grad, (x1 - x)⟫‖ = ‖f x1 - f x - ⟪grad, (x1 - x)⟫‖ := by
          have h'' : f x - f x1 + ⟪grad, (x1 - x)⟫ = - (f x1 - f x - ⟪grad, (x1 - x)⟫) := by
            linarith
          rw [h'']
          apply norm_neg
        rw [← hp'] at hm2
        apply hm2
    specialize sep2 x' h'
    apply sep2
  rcases h₂ with ⟨δ₂, δ₂pos, hδ₂⟩
  have ε2pos : 0 < ε * ‖f x‖ * ‖f x‖ * ‖f x‖ /(4 * (‖grad‖ + 1 )) := by
    apply div_pos
    repeat apply mul_pos
    apply εpos
    apply Iff.mpr norm_pos_iff h₁
    apply Iff.mpr norm_pos_iff h₁
    norm_num
    apply h₁
    apply mul_pos
    linarith
    have h' : (0 : ℝ)  < 1 := by linarith
    have h'' : 0 ≤ ‖grad‖ := by exact norm_nonneg (grad)
    exact add_pos_of_nonneg_of_pos h'' h'
  have h₃ : ∃ δ₃ > (0 : ℝ), ∀ (x' : E),
      ‖x - x'‖ ≤ δ₃ → ‖f x' - f x‖ ≤ ε * ‖f x‖ * ‖f x‖ * ‖f x‖ /(4 * (‖grad‖ + 1 )) := by
    apply ContinuousAt_Convergence
    · exact HasGradientAt.continuousAt hf'
    · exact ε2pos
  rcases h₃ with ⟨δ₃,δ₃pos,hδ₃⟩
  have h₄ : ∃ δ > (0 : ℝ ), ∀ (x' : E), ‖x - x'‖ ≤ δ →
      ‖(f x' * ⟪grad, (x' - x)⟫ - f x * ⟪grad, (x' - x)⟫)/((f x) * (f x) * (f x'))‖
      ≤ (ε / 2) * ‖x' - x‖ := by
    use min δ₀ δ₃
    constructor
    exact lt_min δ₀pos δ₃pos
    intro x' h'
    have hp₁ : ‖x - x'‖ ≤ δ₀ := by
      have h₂ : min δ₀ δ₃ ≤ δ₀ := by exact min_le_left δ₀ δ₃
      apply le_trans h' h₂
    have hp₂ : ‖x - x'‖ ≤ δ₃ := by
      have h₂ : min δ₀ δ₃ ≤ δ₃ := by exact min_le_right δ₀ δ₃
      apply le_trans h' h₂
    have l0 : 0 < ‖f x'‖ := by
      have h' : ‖f x‖/2 ≤ ‖f x'‖ := hδ₀ x' hp₁
      have h'' : 0 < ‖f x‖/2 := by
        apply div_pos
        apply Iff.mpr norm_pos_iff h₁
        norm_num
      apply lt_of_lt_of_le h'' h'
    have l1 : ‖(f x' - f x) * ⟪grad, (x' - x)⟫/((f x) * (f x) * (f x'))‖  =
        ‖(f x' - f x) * ⟪grad, (x' - x)⟫‖ * ‖1 / ((f x) * (f x) * (f x'))‖  := by
      apply Vert_div
    have l2 : ‖(f x' - f x) * ⟪grad, (x' - x)⟫‖ * ‖1 / ((f x) * (f x) * (f x'))‖ =
        ‖f x' - f x‖ * ‖ ⟪grad, (x' - x)⟫‖  * ‖1 / ((f x) * (f x) * (f x'))‖ := by
      have h' : ‖(f x' - f x) * ⟪grad, (x' - x)⟫‖ = ‖f x' - f x‖ * ‖ ⟪grad, (x' - x)⟫‖ := by
        exact norm_mul (f x' - f x) ⟪grad, (x' - x)⟫
      rw [h']
    have l3 : ‖f x' - f x‖ * ‖⟪grad, (x' - x)⟫‖ ≤ ‖f x' - f x‖ * ‖grad‖ * ‖x' - x‖ := by
      have h' : ‖f x' - f x‖ * ‖grad‖ * ‖x' - x‖ = ‖f x' - f x‖ * (‖grad‖ * ‖x' - x‖) := by
        apply mul_assoc
      rw [h']
      have h'' : 0 ≤ ‖f x' - f x‖ := by apply norm_nonneg (f x' - f x)
      have h''' : ‖⟪grad, (x' - x)⟫‖ ≤ ‖grad‖ * ‖x' - x‖ := by
        exact norm_inner_le_norm grad (x' - x)
      exact mul_le_mul_of_nonneg_left h''' h''
    have l5 :  ‖f x' - f x‖ ≤ ε * ‖f x‖ * ‖f x‖ * ‖f x‖ /(4 * (‖grad‖ + 1 )) := hδ₃ x' hp₂
    calc
      ‖(f x' * ⟪grad, (x' - x)⟫ - f x * ⟪grad, (x' - x)⟫)/(f x * f x * f x')‖ =
          ‖(f x' - f x) * ⟪grad, (x' - x)⟫/((f x) * (f x) * (f x'))‖ := by rw [← sub_mul]
      _ = ‖(f x' - f x) * ⟪grad, (x' - x)⟫‖ * ‖1 / ((f x) * (f x) * (f x'))‖  := l1
      _ = ‖f x' - f x‖ * ‖⟪grad, (x' - x)⟫‖ * ‖1 / ((f x) * (f x) * (f x'))‖ := l2
      _ ≤ ‖f x' - f x‖ * ‖grad‖ * ‖x' - x‖ * ‖1 / ((f x) * (f x) * (f x'))‖  := by
        have h' : 0 ≤ ‖1 / ((f x) * (f x) * (f x'))‖ := by
          apply norm_nonneg (1 / ((f x) * (f x) * (f x')))
        apply mul_le_mul_of_nonneg_right l3 h'
      _ ≤ ‖(f x' - f x)‖ * ‖grad‖ * ‖x' - x‖ * ‖2 / ((f x) * (f x) * (f x))‖ := by
        have h'' : ‖1 / ((f x) * (f x) * (f x'))‖ ≤ ‖2 / ((f x) * (f x) * (f x))‖ := by
          apply Simplifying₁ (f x') (f x)
          apply Iff.mp norm_pos_iff l0
          apply h₁
          apply hδ₀
          apply hp₁
        exact mul_le_mul_of_nonneg_left h'' (mul_nonneg (mul_nonneg
            (norm_nonneg (f x' - f x)) (norm_nonneg grad)) (norm_nonneg (x' - x)))
      _ ≤ ‖(2 / ((f x) * (f x) * (f x)))‖ * ‖f x' - f x‖ * ‖x' - x‖ * ‖grad‖  := by
        linarith
      _ ≤ ‖(2 / ((f x) * (f x) * (f x)))‖ * ‖f x' - f x‖ * ‖x' - x‖ * (‖grad‖ + 1) := by
        have h' : ‖grad‖ ≤ ‖grad‖ + 1 := by
          linarith
        exact mul_le_mul_of_nonneg_left h' (mul_nonneg (mul_nonneg
        (norm_nonneg (2 / (f x * f x * f x))) (norm_nonneg (f x' - f x))) (norm_nonneg (x' - x)))
      _ = ‖(2 / ((f x) * (f x) * (f x)))‖ * ‖x' - x‖ * (‖grad‖ + 1) * ‖f x' - f x‖ := by
        linarith
      _ ≤ ‖(2 / ((f x) * (f x) * (f x)))‖ * ‖x' - x‖ * (‖grad‖ + 1) *
          (ε * ‖f x‖ * ‖f x‖ * ‖f x‖ /(4 * (‖grad‖ + 1 ))) := by
        apply mul_le_mul_of_nonneg_left l5
        apply mul_nonneg
        apply mul_nonneg
        apply norm_nonneg
        apply norm_nonneg
        have h' : 0 ≤ ‖grad‖ := by apply norm_nonneg
        have h'' : ‖grad‖ ≤ ‖grad‖ + 1 := by linarith
        apply le_trans h' h''
      _ = (ε / 2) * ‖x' - x‖ := by
        apply Simplifying₂
        apply h₁
        apply norm_nonneg
  rcases h₄ with ⟨δ₄,δ₄pos,hδ₄⟩
  have h₅ : ∃ δ > (0 : ℝ ), ∀ (x' : E), ‖x - x'‖ ≤ δ →
      ‖f x * (f x -f x' + ⟪grad, (x' - x)⟫)/((f x) * (f x) * (f x'))‖ ≤ (ε / 2) * ‖x' - x‖ := by
    use min δ₀ δ₂
    constructor
    exact lt_min δ₀pos δ₂pos
    intro x' h'
    have hp₁ : ‖x - x'‖ ≤ δ₀ := by
      have h₂ : min δ₀ δ₂ ≤ δ₀ := by exact min_le_left δ₀ δ₂
      apply le_trans h' h₂
    have hp₂ : ‖x - x'‖ ≤ δ₂ := by
      have h₂ : min δ₀ δ₂ ≤ δ₂ := by exact min_le_right δ₀ δ₂
      apply le_trans h' h₂

    have zp1 :‖f x * (f x - f x' + inner grad (x' - x)) / (f x * f x * f x')‖ =
        ‖(f x - f x' + inner grad (x' - x)) / (f x * f x')‖ := by
      rw [mul_comm, mul_assoc (f x) (f x) (f x'),
      div_mul_eq_div_div ((f x - f x' + inner grad (x' - x)) * (f x)) (f x) (f x * f x'), mul_div_cancel_right₀]
      apply h₁

    have zp2 : ‖f x‖ * ‖f x‖/2 ≤ ‖f x * f x'‖ := by
      have h' : ‖f x * f x'‖ = ‖f x‖ * ‖f x'‖ := by
        exact norm_mul (f x) (f x')
      rw [h']
      have h'' : ‖f x‖ * ‖f x‖/2 = ‖f x‖ * ‖f x‖ * (1/2) := by
        linarith
      rw [h'']
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left
      have h''' : ‖f x‖ * (1/2) = ‖f x‖/2 := by linarith
      rw [h''']
      apply hδ₀
      apply hp₁
      apply norm_nonneg
    have zp3 : ‖1/(f x * f x')‖ ≤ 2 / (‖f x‖ * ‖f x‖) := by
      have zp4 : 1 / ‖f x * f x'‖ = ‖1/(f x * f x')‖ := by
        have h₁ : (0 : ℝ) ≤ (1 : ℝ) := by
          exact zero_le_one
        have h' : 1 = ‖(1 : ℝ)‖ := by
          exact Eq.symm (Real.norm_of_nonneg h₁)
        nth_rw 1 [h']
        exact Eq.symm (norm_div 1 (f x * f x'))
      rw [← zp4]
      apply div_div_mul (‖f x‖ * ‖f x‖) 2 ‖f x * f x'‖
      apply zp2
      apply mul_pos
      apply Iff.mpr norm_pos_iff h₁
      apply Iff.mpr norm_pos_iff h₁
      norm_num
      rw [norm_mul]
      apply mul_pos
      apply Iff.mpr norm_pos_iff h₁
      have h' : ‖f x‖/2 ≤ ‖f x'‖ := hδ₀ x' hp₁
      have h'' : 0 < ‖f x‖/2 := by
        apply div_pos
        apply Iff.mpr norm_pos_iff h₁
        norm_num
      apply lt_of_lt_of_le h'' h'
    have zp5 : ((ε * ‖f x‖ * ‖f x‖ / 4) * ‖x - x'‖) * (2 / (‖f x‖ * ‖f x‖)) = (ε / 2) * ‖x' - x‖ := by
      have l : ‖f x‖ ≠ 0 := by
        exact Iff.mpr norm_ne_zero_iff h₁
      calc
        ((ε * ‖f x‖ * ‖f x‖/4) * ‖x - x'‖) * (2 / (‖f x‖ * ‖f x‖)) = (ε / 2) * ‖x - x'‖ *
            ((‖f x‖ * ‖f x‖)/(‖f x‖ * ‖f x‖)) := by
          ring_nf
        _ = (ε / 2) * ‖x' - x‖ := by
          rw [div_self (mul_ne_zero l l), mul_one, norm_sub_rev]
    calc
      ‖f x * (f x - f x' + inner grad (x' - x)) / (f x * f x * f x')‖ =
          ‖(f x - f x' + inner grad (x' - x)) / (f x * f x')‖ := by
        apply zp1
      _ = ‖(f x - f x' + inner grad (x' - x))‖ * ‖1/(f x * f x')‖ := by
        apply Vert_div
      _ ≤ ‖(f x - f x' + inner grad (x' - x))‖ * (2 / (‖f x‖ * ‖f x‖)) := by
        apply mul_le_mul_of_nonneg_left zp3
        apply norm_nonneg
      _ ≤ ((ε * ‖f x‖ * ‖f x‖/4) * ‖x - x'‖) * (2 / (‖f x‖ * ‖f x‖)) := by
        have : ‖(f x - f x' + inner grad (x' - x))‖ ≤ (ε * ‖f x‖ * ‖f x‖/4) * ‖x - x'‖ := by
          apply hδ₂
          apply hp₂
        apply mul_le_mul_of_nonneg_right this
        apply div_nonneg
        norm_num
        apply mul_nonneg
        apply norm_nonneg
        apply norm_nonneg
      _ = (ε / 2) * ‖x' - x‖ := by
        apply zp5
  rcases h₅ with ⟨δ₅,δ₅pos,hδ₅⟩
  use min δ₀ (min δ₄ δ₅)
  constructor
  have :  0 < min δ₄ δ₅ := by
    exact lt_min δ₄pos δ₅pos
  apply lt_min δ₀pos this
  intro x' h'
  have hp₀ : ‖x - x'‖ ≤ δ₀ := by
    have : min δ₀ (min δ₄ δ₅) ≤ δ₀ := by
      exact min_le_left δ₀ (min δ₄ δ₅)
    apply le_trans h' this
  have hp₁ : ‖x - x'‖ ≤ δ₄ := by
    have h₀ : min δ₀ (min δ₄ δ₅) ≤ (min δ₄ δ₅) := by
      exact min_le_right δ₀ (min δ₄ δ₅)
    have h₂ : min δ₄ δ₅ ≤ δ₄ := by exact min_le_left δ₄ δ₅
    have h₃ : ‖x - x'‖ ≤ (min δ₄ δ₅) := by
      apply le_trans h' h₀
    apply le_trans h₃ h₂
  have hp₂ : ‖x - x'‖ ≤ δ₅ := by
    have h₀ : min δ₀ (min δ₄ δ₅) ≤ (min δ₄ δ₅) := by
      exact min_le_right δ₀ (min δ₄ δ₅)
    have h₂ : min δ₄ δ₅ ≤ δ₅ := by exact min_le_right δ₄ δ₅
    have h₃ : ‖x - x'‖ ≤ (min δ₄ δ₅) := by
      apply le_trans h' h₀
    apply le_trans h₃ h₂
  have l0 : 0 < ‖f x'‖ := by
    have h' : ‖f x‖/2 ≤ ‖f x'‖ := hδ₀ x' hp₀
    have h'' : 0 < ‖f x‖/2 := by
      apply div_pos
      apply Iff.mpr norm_pos_iff h₁
      norm_num
    apply lt_of_lt_of_le h'' h'
  have l' : f x' ≠ 0 := by
      apply Iff.mp norm_pos_iff l0
  have k₁ : 1 / f x' - 1 / f x = (f x - f x')/(f x' * f x) := by
    rw [← inv_eq_one_div, ← inv_eq_one_div]
    exact inv_sub_inv l' h₁
  have k₂ : (f x - f x')/(f x' * f x) = (f x - f x') * f x /(f x' * f x * f x) := by
    apply Eq.symm (mul_div_mul_right (f x - f x') (f x' * f x) h₁)
  have k₃ : ⟪ (-(1 / f x ^ 2) • grad),  (x' - x)⟫ = -⟪grad, (x' - x)⟫/((f x) * (f x)) := by
    have h' : 1 / f x ^ 2 = 1 / (f x * f x) := by
      rw [← inv_eq_one_div]
      have : (f x) ^ 2 = (f x) * (f x) := by
        rw [pow_two]
      rw [this, inv_eq_one_div]
    rw [h']
    have l1 : ⟪(-(1 / (f x * f x)) • grad), (x' - x)⟫ =
         -(1 / (f x * f x)) *  ⟪grad, (x' - x)⟫ := by
      rw [inner_smul_left]
      rfl
    rw [l1, neg_mul, mul_comm, mul_one_div, neg_div]
  have k₄ : ‖1 / f x' - 1 / f x - - (⟪grad, (x' - x)⟫)/((f x) * (f x))‖ =
      ‖1 / f x' - 1 / f x + (⟪grad, (x' - x)⟫)/((f x) * (f x))‖ := by
    congr
    ring_nf
  have k₅ : (⟪grad, (x' - x)⟫)/((f x) * (f x)) =
      f x' * (⟪grad, (x' - x)⟫)/((f x') * ((f x) * (f x))) := by
    apply Eq.symm (mul_div_mul_left (⟪grad, (x' - x)⟫) ((f x) * (f x)) l')
  have k₆ : (f x - f x') * f x /(f x' * f x * f x) + f x' * (⟪grad, (x' - x)⟫)/(f x' * f x * f x)
      = ((f x - f x') * f x  + f x' * (⟪grad, (x' - x)⟫))/(f x' * f x * f x) := by
    apply div_add_div_same ((f x - f x') * f x) (f x' * (⟪grad, (x' - x)⟫)) (f x' * f x * f x)
  have k₇ : ((f x - f x') * f x + f x' * inner grad (x' - x)) / (f x' * f x * f x) =
      (f x * (f x - f x' + inner grad (x' - x)) +
      (f x' * inner grad (x' - x) - f x * inner grad (x' - x))) / (f x' * f x * f x) := by
    have h' : (f x - f x') * f x + f x' * inner grad (x' - x) =
        f x * (f x - f x' + inner grad (x' - x)) +
        (f x' * (inner grad (x' - x)) - f x * (inner grad (x' - x)))  := by
      linarith
    rw [h']
  have k₈ : (f x * (f x - f x' + inner grad (x' - x)) +
      (f x' * inner grad (x' - x) - f x * inner grad (x' - x))) /
      (f x * f x * f x') = f x * (f x - f x' + inner grad (x' - x))/
      (f x * f x * f x') + (f x' * inner grad (x' - x) - f x * inner grad (x' - x))/
      (f x * f x * f x') := by
        apply add_div ((f x) * (f x - f x' + inner grad (x' - x)))
          (f x' * inner grad (x' - x) - f x * inner grad (x' - x)) (f x * f x * f x')
  have k₉ : f x' * f x * f x =  f x * f x * f x' := by linarith
  have p₁ : ‖1 / f x' - 1 / f x - (- (⟪grad, (x' - x)⟫))/((f x) * (f x))‖ ≤ ε * ‖x' - x‖ := by
    rw [k₄, k₁, k₂, k₅]
    have : f x' * (f x * f x) = f x' * f x * f x := by
      rw [← mul_assoc]
    rw [this]
    rw [k₆, k₇, k₉]
    calc
      ‖(f x * (f x - f x' + inner grad (x' - x)) +
      (f x' * inner grad (x' - x) - f x * inner grad (x' - x))) /
      (f x * f x * f x')‖ = ‖f x * (f x - f x' + inner grad (x' - x))/
      (f x * f x * f x') + (f x' * inner grad (x' - x) - f x * inner grad (x' - x))/
      (f x * f x * f x')‖ := by
        rw [k₈]
      _ ≤ ‖f x * (f x - f x' + inner grad (x' - x))/
      (f x * f x * f x')‖ + ‖(f x' * inner grad (x' - x) - f x * inner grad (x' - x))/
      (f x * f x * f x')‖ := by
        apply norm_add_le ((f x) * (f x - f x' + inner grad (x' - x))/
      (f x * f x * f x')) ((f x' * inner grad (x' - x) - f x * inner grad (x' - x))/
      (f x * f x * f x'))
      _ ≤ (ε/2) * ‖x' - x‖ + (ε/2) * ‖x' - x‖ := by exact add_le_add (hδ₅ x' hp₂) (hδ₄ x' hp₁)
      _ = ε * ‖x' - x‖ := by linarith
  have j₁ : ‖1 / f x' - 1 / f x - (- (⟪grad, (x' - x)⟫))/((f x) * (f x))‖ = ‖1 / f x' - 1 / f x -
      inner ((-(1 / f x ^ ↑2) • grad)) (x' - x)‖ := by
    congr; rw [k₃]
  rw [j₁] at p₁
  have l1 : ‖x - x'‖ = ‖x' - x‖ := by
    exact norm_sub_rev x x'
  rw [l1]
  apply p₁
