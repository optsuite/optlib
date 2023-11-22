/-
Copyright (c) 2023 Mingquan Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingquan Zhang
-/

/-
  Here, we give examples of norm ball and norm cone and prove their convexity.
  We call a set of the form {x | ‖x - x₀‖ ≤ r} a norm ball.
  We call a set of the form {(x, t) | ‖x‖ ≤ t} a norm cone,
  where x is an n-dimensional real vector and t is a nonnegative real number.
-/

import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupPower.Basic


open Set Finset BigOperators Real

variable {n : Type _} [Fintype n]
variable (r : ℝ) (x₀: n -> ℝ)
variable {k : ℕ}

-- 2-norm ball
def Normball (r : ℝ)(x₀: n -> ℝ): Set (n -> ℝ) := {x: (n -> ℝ) | ‖x - x₀‖ ≤ r}

theorem convex_Normball: Convex ℝ (Normball r x₀) := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, smul_eq_mul, mem_setOf] at *
    have k₁ : s • x + t • y - x₀ = s • x + t • y - (s + t) • x₀ := by
        rw[hst, one_smul]
    calc
        ‖s • x + t • y - x₀‖ = ‖s • (x - x₀) + t • (y - x₀)‖ := by
            congr; simp [k₁, add_smul, smul_sub, smul_sub]
            simp only [sub_add_eq_sub_sub, add_sub]; ring
        _ ≤ ‖s • (x - x₀)‖ + ‖ t • (y - x₀)‖ := by
            simp only [norm_add_le]
        _ = s * ‖x - x₀‖ + t * ‖y - x₀‖ := by
            simp only [norm_smul]; dsimp; simp only [abs_of_pos hs, abs_of_pos ht]
        _ ≤ s * r + t * r := by
            apply add_le_add; apply mul_le_mul; simp [norm_nonneg]; apply hx
            simp [norm_nonneg]; linarith
            apply mul_le_mul; linarith; apply hy; simp [norm_nonneg]; linarith
        _ = (s+t)*r := by ring
        _ = r := by rw [hst]; simp


-- 2-norm cone
def Normcone (k: ℕ): Set ((Fin k -> Real) × Real) :=
  {x : (Fin k -> Real) × Real | ‖x.1‖ ≤ x.2}

theorem convex_Normcone: Convex ℝ (Normcone k) := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, smul_eq_mul, mem_setOf] at *
    have hs': 0 ≤ s := by linarith
    have ht': 0 ≤ t := by linarith
    calc
      ‖(s • x + t • y).1‖ = ‖s • x.1 + t • y.1‖ := by simp
      _ ≤ ‖s • x.1‖ + ‖t • y.1‖ := by apply norm_add_le
      _ = ‖s‖ * ‖x.1‖ + ‖t‖ * ‖y.1‖ := by rw [norm_smul, norm_smul]
      _ = s * ‖x.1‖ + t * ‖y.1‖ := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs', abs_of_nonneg ht']
      _ ≤ s * x.2 + t * y.2 := by
        apply add_le_add; apply mul_le_mul_of_nonneg_left
        exact hx; linarith
        apply mul_le_mul_of_nonneg_left; exact hy; linarith