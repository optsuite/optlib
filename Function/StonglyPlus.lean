/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strong
import Analysis.Calculation
import Function.Lsmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Strongly_Convex

variable {s : Set E} {f : E → ℝ} {m : ℝ} {xm xm': E} {f' : E → E}

theorem Strongly_Convex_Bound (m : ℝ) (strongly_convex: StrongConvexOn s m f):
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
     ∀ ⦃a⦄, 0 < a → ∀ ⦃b⦄, 0 < b → a + b = 1 → f (a • x + b • y)
       ≤ a * f x + b * f y - m / 2 * a * b * ‖x - y‖ ^ 2 := by
  sorry

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
  simp at this; simp at hfun
  rw [← this]; exact hfun

theorem Strongly_Convex_Unique_Minima (hsc: StrongConvexOn s m f)
    (min: IsMinOn f s xm) (min' : IsMinOn f s xm') (hxm : xm ∈ s) (hxm' : xm' ∈ s): xm = xm' := by
  sorry

theorem Strong_Convex_lower (hsc: StrongConvexOn s m f) (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ∀ x ∈ s, ∀ y ∈ s, inner (f' x - f' y) (x - y) ≥ m * ‖x - y‖ ^ 2 := by
  sorry

theorem Lower_Strong_Convex (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∀ y ∈ s, inner (f' x - f' y) (x - y) ≥ m * ‖x - y‖ ^ 2) :
    StrongConvexOn s m f := by
  sorry

theorem Strong_Convex_second_lower (hsc: StrongConvexOn s m f)
    (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) : ∀ x ∈ s, ∀ y ∈ s,
    f y ≥ f x + inner (f' x) (y - x) + m / 2 * ‖y - x‖ ^ 2 := by
  sorry

end Strongly_Convex

section Strongly_Convex_Gradient_Descent

variable {f : E → ℝ} {l m : ℝ} {f' : E → E} {xm x₀: E} {point : ℕ → E}

open Set

theorem Strong_convex_Lipschitz_smooth (hsc: StrongConvexOn univ m f)
    (hf : ∀ x, HasGradientAt f (f' x) x) (h₂ : LipschitzOn f' l) (hl : l > 0):
    inner (f' x - f' y) (x - y) ≥ m * l / (m + l) * ‖x - y‖ ^ 2
      + 1 / (m + l) * ‖f' x - f' y‖ ^ 2 := by
  sorry

lemma gradient_method_strong_convex (hsc: StrongConvexOn univ m f)
    (hf : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁) (h₃ : LipschitzOn f' l) (hl: l > 0)
    (step₁: a ≤ 2 / (m + l)) (step₂ : a > 0) (initial : point 0 = x₀)
    (update: ∀ (k : ℕ), point (k + 1) = point k - a • (f' (point k))):
    ∀ k : ℕ , ‖point k - xm‖ ^ 2 ≤ (1 - a * (2 * m * l / (m + l))) ^ k * ‖x₀ - xm‖ ^ 2 := by
  sorry

end Strongly_Convex_Gradient_Descent
