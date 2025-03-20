/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Convex.Quasiconvex
import Optlib.Convex.ConvexFunction

open InnerProductSpace

noncomputable section
/-!
  the first order condition for quasiconvex function
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {f' : E → (E →L[ℝ] ℝ)} {s : Set E}{x: E}

theorem Quasiconvex_first_order_condition_right (h : HasFDerivAt f (f' x) x) (xs : x ∈ s)
    (hf: QuasiconvexOn ℝ s f) : ∀ y ∈ s, f y ≤ f x  → f' x (y - x) ≤ 0 := by
  have h₁: ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ →
      ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
    apply HasFDeriv_Convergence h
  intro y ys fxy
  by_cases h₂: y = x
  · rw [h₂, sub_self, ContinuousLinearMap.map_zero (f' x)]
  have h₃: 0 < ‖x - y‖ := by
    rw[norm_sub_pos_iff, Ne]
    exact Iff.mpr ne_comm h₂
  by_contra H
  push_neg at H
  rw [quasiconvexOn_iff_le_max] at hf
  rcases hf with ⟨_, cxf⟩
  specialize cxf xs ys
  let ε := (f' x) (y - x) / (2 * ‖x-y‖)
  have εpos: 0 < ε := by
    apply div_pos H
    exact Real.mul_pos two_pos h₃
  specialize h₁ ε εpos
  rcases h₁ with ⟨δ, dpos, converge⟩
  let b1:= δ /(‖x - y‖)
  have b1pos: 0 < b1 := div_pos dpos h₃
  let b:= min b1 (1 : ℝ)
  let a:= 1-b
  have sum_a_b: a + b = 1 := sub_add_cancel 1 b
  have b_nonneg: 0 ≤ b:= le_min (LT.lt.le b1pos) zero_le_one
  have a_nonneg : 0 ≤ a:= by
    have h1: 0 + b ≤ a+b:= by
      rw [zero_add, sum_a_b]
      exact min_le_right b1 1
    rw [add_le_add_iff_right b] at h1
    exact h1
  specialize cxf a_nonneg b_nonneg sum_a_b
  let x' := a • x + b • y
  have h10:  x - x' =  b • (x - y) := by
    calc
      x - x' = x - (a • x + b • y):= rfl
      _= x - a • x - b • y:= by
        rw [sub_add_eq_sub_sub x (a • x) (b • y)]
      _= (1 : ℝ) • x - a • x - b • y:= by
        rw [one_smul]
      _= b • (x - y) := by
        rw [← sub_smul 1 a]; simp [a, b, sum_a_b]; rw[smul_sub b x y]
  have h01 : x' - x =  b • (y - x) :=by
    rw [← neg_inj, ← smul_neg, neg_sub, neg_sub]; exact h10
  have h1 : ‖x - x'‖ = ‖b • (x - y)‖ := by
    congr
  have h2 : ‖b • (x - y)‖ = b * ‖x - y‖ := by
    rw [norm_smul, Real.norm_of_nonneg]
    apply b_nonneg
  have x1nbhd: ‖x - x'‖ ≤ δ := by
    rw [h1, h2]
    have h3: b * ‖x - y‖ ≤ b1 * ‖x - y‖:= by
      rw [mul_le_mul_right]
      apply min_le_left
      exact h₃
    have h4: b1 * ‖x - y‖= δ := by
      rw[div_mul_cancel₀]
      apply ne_of_gt h₃
    rw[← h4]
    apply h3
  specialize converge x' x1nbhd
  have H1: f x + (f' x) (x' - x) - ε * ‖x - x'‖ ≤ f x':= by
    have l1: f x + (f' x) (x' - x) - f x'≤ ‖f x' - f x - (f' x) (x' - x)‖:= by
      rw [Real.norm_eq_abs]
      have l11: f x + (f' x) (x' - x) - f x'= -(f x' - f x - (f' x) (x' - x)):= by
        ring
      rw [l11]
      apply neg_le_abs
    have _ : f x + (f' x) (x' - x) - f x' ≤ ε * ‖x - x'‖:= by
      apply le_trans l1 converge
    linarith
  have H2: f x' ≤ f x := by
    have : x' = a • x + b • y :=by
      rfl
    rw [← this] at cxf
    have : max (f x) (f y) = f x :=by
      simp
      apply fxy
    rw [this] at cxf
    apply cxf
  rw [h10,h2,h01] at H1
  have h': (f' x) (b • (y - x)) = b * (f' x) (y - x):=by
    simp
  have h'': ε * (b * ‖x - y‖) = b * ε * ‖x - y‖ :=by
    rw [←mul_assoc,mul_comm ε b]
  rw [h',h''] at H1
  have : ε = (f' x) (y - x) / (2 * ‖x - y‖) :=by
    rfl
  have h''' : (f' x) (y - x) =2 * ε * ‖x - y‖ :=by
    rw [this,mul_assoc,mul_comm,mul_assoc,mul_comm ‖x - y‖ 2,div_mul_cancel₀]
    linarith
  rw [h'''] at H1
  have : b * (2 * ε * ‖x - y‖) - b * ε * ‖x - y‖ = b * ε * ‖x - y‖ :=by
   rw [←mul_assoc,←mul_assoc,mul_comm b 2,mul_assoc 2 b,mul_assoc 2]
   linarith
  rw [←add_sub,this] at H1
  have _ : b * ε * ‖x - y‖ ≤ 0 :=by
    linarith [H1, H2]
  have true: b * ε * ‖x - y‖ > 0 :=by
    positivity
  linarith
