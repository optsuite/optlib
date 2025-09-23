/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Zaiwen Wen
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Positive
import Optlib.Convex.ConvexFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x xm : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open Set InnerProductSpace

/-
  A vector d is considered a descent direction at a point x if the inner product of the gradient at
  x with d is less than zero.
-/
def DescentDirection (d : E) (x : E) (_ : HasGradientAt f (f' x) x) : Prop :=
  ⟪f' x, d⟫_ℝ < (0 : ℝ)

/-
  For any vector d, there does not exist a descent direction for the function f
  at the minimum point xm.
-/
theorem optimal_no_descent_direction (hf : ∀ x : E, HasGradientAt f (f' x) x)
    (min : IsMinOn f univ xm) (hfc : ContinuousOn f' univ) :
    ∀ d : E, ¬ (DescentDirection d xm (hf xm)) := by
  intro d
  by_contra h
  have : ∃ t : ℝ , f (xm + t • d) < f xm := by
    have h₁ : ∃ T : ℝ , T > 0 ∧ (∀ a ∈ Icc (- T) T, ⟪f' (xm + a • d), d⟫_ℝ < (0 : ℝ)) := by
      let g := fun r : ℝ ↦ (⟪f' (xm + r • d), d⟫_ℝ : ℝ)
      have hg0 : g 0 = ⟪f' xm, d⟫_ℝ := by simp [g]
      have hc : ContinuousOn g univ := by
        change ContinuousOn (fun r : ℝ => ⟪f' (xm + r • d), d⟫_ℝ) univ
        apply ContinuousOn.inner
        · apply ContinuousOn.comp hfc
          · apply ContinuousOn.add continuousOn_const
            apply ContinuousOn.smul continuousOn_id continuousOn_const
          · intro _ _; simp
        · exact continuousOn_const
      have hu : ∃ u < (0 : ℝ) , ⟪f' xm, d⟫_ℝ ≤  u := by
        use (⟪f' xm, d⟫_ℝ / 2)
        rw [DescentDirection] at h
        constructor
        · linarith
        · rw [le_div_iff₀ (by norm_num)]; linarith
      rcases hu with ⟨u, ⟨hu1, hu2⟩⟩
      rw [← hg0] at hu2
      have hc' : ∃ T, T > 0 ∧ (∀ a ∈ Icc (- T) T, g a < 0) := by
        have : univ ∈ nhds (0 : ℝ) := by simp
        rcases Metric.continuousAt_iff.mp (ContinuousOn.continuousAt hc this) with h1
        specialize h1 (- u / 2) (by linarith)
        rcases h1 with ⟨T, ⟨hT1, hT2⟩⟩
        use T / 2; constructor
        · linarith
        · intro a ha
          have : ‖a - 0‖ < T := by
            simp; rw [abs_lt]; simp at ha
            rcases ha with ⟨ha1, ha2⟩
            constructor; linarith; linarith
          specialize hT2 this
          have : |g a - g 0| < -u / 2 := hT2
          rw [abs_lt] at this
          rcases this with ⟨_, hs2⟩
          rw [sub_lt_iff_lt_add] at hs2
          apply lt_trans hs2
          · linarith
      rcases hc' with ⟨T, ⟨hT1, hT2⟩⟩
      use T
    rcases h₁ with ⟨T, ⟨hT1,hT2⟩⟩
    have h₂ : ∃ t1 : ℝ, t1 ≥ -T ∧ t1 ≤ T ∧ f (xm + T • d) =
        f xm + ⟪f' (xm + t1 • d), T • d⟫_ℝ := by
      rcases (expansion hf xm (T • d)) with ⟨ts,⟨ts1,⟨ts2,ts3⟩⟩⟩
      use (ts • T)
      constructor
      · simp; apply le_trans
        · show -T ≤ 0
          linarith
        · simp [hT1]; linarith
      · constructor
        · simp [hT1]; linarith
        · rw [smul_assoc]; exact ts3
    rcases h₂ with ⟨t1, ⟨ht1, ⟨ht2, ht3⟩⟩⟩
    use T; rw [ht3]; simp; rw [inner_smul_right]
    simp at ht1
    exact mul_neg_of_pos_of_neg hT1 (hT2 t1 ⟨ht1, ht2⟩)
  rcases this with ⟨t, ht⟩
  have : f (xm + t • d) ≥ f xm := min trivial
  linarith

/-
  Suppose we have a function f defined on a set E, such that for every point x in E,
  f has a gradient f'(x) at x. Let xm be a point in E where f attains its minimum on the entire set.
  Assume that f' is continuous on the entire set, then the gradient of f at xm equals 0.
-/
theorem first_order_unconstrained (hf : ∀ x : E, HasGradientAt f (f' x) x) (min : IsMinOn f univ xm)
    (hfc : ContinuousOn f' univ) : f' xm = 0 := by
  by_contra h
  have h1: DescentDirection (-f' xm) xm (hf xm) := by
    rw [DescentDirection, inner_neg_right, Left.neg_neg_iff]
    rw [real_inner_self_eq_norm_sq]
    simp [h]
  exact (optimal_no_descent_direction hf min hfc (- f' xm)) h1

/-
  If a function f is convex and has a gradient at every point, and if xm is a
  point where the gradient is zero, then xm is a minimum point for f.
-/
theorem first_order_convex (hf : ∀ x : E, HasGradientAt f (f' x) x) (hcon : ConvexOn ℝ univ f)
    (hfm : f' xm = 0) : IsMinOn f univ xm := by
  have : ∀ y , f y ≥ f xm + ⟪f' xm, y - xm⟫_ℝ := by
    intro y
    apply Convex_first_order_condition' (hf xm) hcon (by trivial)
    · trivial
  intro y
  dsimp; specialize this y
  rw [hfm, inner_zero_left, add_zero] at this
  exact fun _ => this

/-
  If f has a gradient at every point and f is convex, and the derivative of f is continuous
  then a point xm is a minimum point of f if and only if the derivative of f at xm is equal to zero.
-/
theorem first_order_convex_iff (hf : ∀ x : E, HasGradientAt f (f' x) x) (hcon : ConvexOn ℝ univ f)
    (hfc : ContinuousOn f' univ) :
    IsMinOn f univ xm ↔ f' xm = 0 := by
  constructor
  · intro hmin
    exact first_order_unconstrained hf hmin hfc
  · intro hgrad
    apply first_order_convex hf hcon hgrad
