/-
Copyright (c) 2023 Zuokai Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zuokai Wen
-/


/-
  We call the set of points that
  satisfy a set of linear equations and inequalities a polyhedron:
  {x | A x ≤ b,C x = d}
  where A ∈ ℝ^(m×n),C ∈ ℝ^(p×n),x≤y means that each component of the vector x is
  less than or equal to the corresponding component of y.
  And it is a convex set.
-/

import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Convex.Basic

open scoped Matrix

variable {p m n: Type _}[Fintype p][Fintype m] [Fintype n]
  (A:Matrix m n ℝ)(b:m -> ℝ)(C:Matrix p n ℝ)(d:p -> ℝ)

def polyhedron (A:Matrix m n ℝ)(b:m -> ℝ)(C:Matrix p n ℝ)(d:p -> ℝ):
  Set (n -> ℝ):= {x | (∀ i,A i ⬝ᵥ x ≤ b i) ∧ (∀ j,C j ⬝ᵥ x = d j)}

/-
  A polyhedron is the intersection of a finite number of half-spaces and hyperplanes,
  and is therefore a convex set.
-/

theorem convex_halfspace:∀{i:m},Convex ℝ {x|A i ⬝ᵥ x ≤ b i}:= by
  intro i
  apply convex_iff_forall_pos.mpr
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq, Matrix.dotProduct_add, Matrix.dotProduct_smul, smul_eq_mul] at *
  have hs_nonneg:0 ≤ s:=le_of_lt hs
  have ht_nonneg:0 ≤ t:=le_of_lt ht
  have hx':s * A i ⬝ᵥ x ≤ s * b i :=mul_le_mul_of_nonneg_left hx hs_nonneg
  have hy':t * A i ⬝ᵥ y ≤ t * b i :=mul_le_mul_of_nonneg_left hy ht_nonneg
  rw[←one_mul (b i),← hst,add_mul]
  apply add_le_add
  · exact hx'
  exact hy'


theorem convex_hyperspace:∀{j:p},Convex ℝ {x|C j ⬝ᵥ x = d j}:= by
  intro j
  apply convex_iff_forall_pos.mpr
  intro x hx y hy s t _ _ hst
  simp only [Set.mem_setOf_eq, Matrix.dotProduct_add, Matrix.dotProduct_smul, smul_eq_mul] at *
  rw[hx,hy,←add_mul,hst,one_mul]


theorem polyhedron_eq_inter : polyhedron A b C d
  =(⋂ i, { x | A i ⬝ᵥ x ≤ b i}) ∩ (⋂ j,{x|C j ⬝ᵥ x = d j}):= by
  ext w
  simp only [polyhedron,Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]


theorem convex_inter_hyperspace :Convex ℝ (⋂ i, { x | A i ⬝ᵥ x ≤ b i}):=by
  apply convex_iff_forall_pos.mpr
  intro y hy z hz s t hs ht hst
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Matrix.dotProduct_add,
    Matrix.dotProduct_smul, smul_eq_mul] at *
  intro i
  have hyi:A i ⬝ᵥ y ≤ b i:=hy i
  have hzi:A i ⬝ᵥ z ≤ b i:=hz i
  have hs_nonneg:0 ≤ s:=le_of_lt hs
  have ht_nonneg:0 ≤ t:=le_of_lt ht
  rw[←one_mul (b i),← hst,add_mul]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left hyi hs_nonneg
  apply mul_le_mul_of_nonneg_left hzi ht_nonneg

theorem convex_inter_hyperplane :Convex ℝ (⋂ j,{x|C j ⬝ᵥ x = d j}):= by
  apply convex_iff_forall_pos.mpr
  intro y hy z hz s t _ _ hst
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Matrix.dotProduct_add,
    Matrix.dotProduct_smul, smul_eq_mul] at *
  intro j
  have hyj:C j ⬝ᵥ y = d j:=hy j
  have hzj:C j ⬝ᵥ z = d j:=hz j
  rw[hyj,hzj,←add_mul,hst,one_mul]

theorem convex_polyhedron : Convex ℝ (polyhedron A b C d) := by
  rw[polyhedron_eq_inter]
  apply Convex.inter (convex_inter_hyperspace A b) (convex_inter_hyperplane C d)
