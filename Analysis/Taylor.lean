/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li,
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Analysis.Calculation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x p y : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open Set

theorem expansion (h : ∀ x : E, HasGradientAt f (f' x) x) (x p : E) :
    ∃ t, t > 0 ∧ t < 1 ∧ f (x + p) = f x + inner (f' (x + t • p)) p := by
  sorry

theorem continuous (h : ContinuousAt f x) : ∀ ε > 0, ∃ δ > 0, ∀ (y : E), ‖y - x‖ < δ → |f y - f x| < ε := by
  rw [ContinuousAt] at h
  sorry
