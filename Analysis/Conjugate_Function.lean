/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Order.Bounds.Basic
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
  the defition of the conjugate function and the Fenchel inequality
  need to solve the sorry
-/
open LinearMap Set BigOperators Classical Convex Pointwise

noncomputable section

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] 
variable {f : E → ℝ} 

def cg (f : E → ℝ) (y : E) : ℝ :=
  sSup {@inner ℝ _ _ y x - f x | x : E}

--Fenchel 不等式
theorem Fenchel (f : E → ℝ) (y x: E) : f x + cg f y  ≥  @inner ℝ _ _ y x := by
  rw [cg]
  have h1 : sSup {x | ∃ x_1, inner y x_1 - f x_1 = x} ≥ inner y x - f x := by
    sorry
  exact Iff.mp tsub_le_iff_left h1

lemma quadratic {b : E} {c : ℝ} :
    cg (fun x ↦ 1 / 2 * inner x x + inner b x + c) y = 1 / 2 * inner (y - b) (y - b) - c := by
  sorry