/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

variable {E : Type*} {n : Type*}

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype n]

section

open Topology InnerProductSpace Set

variable {f : E → ℝ} {x : E} {f' : E → E} {f'' : E → (E →L[ℝ] E)}

lemma is_star_equiv  (h₁ : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁)
    (h₂ : ∀ x₁ : E, HasFDerivAt f' (f'' x₁) x₁) : ∀ x, IsSelfAdjoint (f'' x) := by
  intro x
  rw [ContinuousLinearMap.isSelfAdjoint_iff']; symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro y z
  let g := fun x ↦ toDual ℝ E (f' x)
  have h₁' : ∀ x₁ : E, HasFDerivAt f (g x₁) x₁ := by
    intro x₁; apply h₁
  let g' := fun t y : E ↦ toDual ℝ E (f'' t y)
  have : (inner (f'' x y) z : ℝ) = inner y (f'' x z) := by sorry
  exact this

theorem convex_second_order (hfun: ConvexOn ℝ univ f) (h₁ : ∀ x : E, HasGradientAt f (f' x) x)
    (h₂ : ∀ x : E, HasFDerivAt f' (f'' x) x) : ∀ x, ContinuousLinearMap.IsPositive (f'' x) := by
  intro x; rw [ContinuousLinearMap.IsPositive]
  constructor
  · exact is_star_equiv h₁ h₂ x
  · intro y; rw [ContinuousLinearMap.reApplyInnerSelf]
    simp only [IsROrC.re_to_real]
    sorry

theorem second_order_convex (h₁ : ∀ x : E, HasGradientAt f (f' x) x)
    (h₂ : ∀ x : E, HasFDerivAt f' (f'' x) x) (hp : ∀ x, ContinuousLinearMap.IsPositive (f'' x)) :
    ConvexOn ℝ univ f := by
  sorry
