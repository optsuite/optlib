/-
Copyright (c) 2025 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix
/-!
# The gradient of matrix variable functions

## References

* Matrix Cookbook
-/

#check InnerProductSpace

noncomputable section Gradient

open Matrix

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup

/-
  The inner product of two matrices is defined as trace (ABᵀ).
  This forms an inner product space.
-/
instance Matrix.Innerproductspace
    {m : Type u_3} {n : Type u_4} [Fintype m] [Fintype n] :
    InnerProductSpace ℝ (Matrix m n ℝ) where
  norm_smul_le := by sorry
  inner := fun A B => trace (A * Bᵀ)
  conj_inner_symm := by sorry
  norm_sq_eq_re_inner := by sorry
  add_left := by sorry
  smul_left := by sorry

/-
  The inner product space is complete
-/
instance Matrix.CompleteSpace
    {m : Type u_3} {n : Type u_4} [Fintype m] [Fintype n] :
    CompleteSpace (Matrix m n ℝ) where
  complete := by sorry

variable {m : Type u_3} {n : Type u_4} [Fintype m] [Fintype n]

end Gradient

noncomputable section Calculation

end Calculation
