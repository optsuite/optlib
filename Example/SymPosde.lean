/-
Copyright (c) 2023 Zuokai Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zuokai Wen
-/

import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-
  This file contains the convex conicity of symmetric matrices,
  semi-positive definite matrices and positive definite matrices.
  The last two are proved under 𝕜 = ℝ(if 𝕜 = ℂ then they haven't convex conicity.)
-/

open Matrix

--The definition of symmetric matrices is contained in "Mathlib.LinearAlgebra.Matrix.Symmetric".
/-
  The definition of semi-positive definite matrices and positive definite matrices is contained
  in "Mathlib.LinearAlgebra.Matrix.PosDef".
-/
/- A convex cone is a subset `s` of a `𝕜`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`.
-/
variable {𝕜 n α: Type _}

section SymmetricMatrix

variable [OrderedSemiring 𝕜][Fintype n][SMul 𝕜 α][Add α]

def Symmat:Set (Matrix n n α):={A | IsSymm A}

theorem smul_mem_Symmat:∀ ⦃c :𝕜⦄, 0 < c → ∀ ⦃A : Matrix n n α⦄, A ∈ Symmat → c • A ∈ Symmat:=by
  intro c _ A hA
  rw[Symmat,Set.mem_setOf_eq] at *
  exact IsSymm.smul hA c

theorem add_mem_Symmat:∀ ⦃A₁ A₂:Matrix n n α⦄ (_ : A₁ ∈ Symmat)
  (_ : A₂ ∈ Symmat), A₁ + A₂ ∈ Symmat:=by
  intro A₁ A₂ hA₁ hA₂
  rw[Symmat,Set.mem_setOf_eq] at *
  exact IsSymm.add hA₁ hA₂

end SymmetricMatrix

section SemipositiveDefiniteMatrix

variable [Fintype n]

def PosSemidefSet:Set (Matrix n n ℝ):={A | PosSemidef A}

theorem smul_mem_PosSemidefSet:
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃A : Matrix n n ℝ⦄, A ∈ PosSemidefSet → c • A ∈ PosSemidefSet:=by
    intro c hc A hA
    rw[PosSemidefSet,Set.mem_setOf_eq] at *
    have Aher:IsHermitian A:=hA.1
    have Aposd:∀ x : n → ℝ, 0 ≤ IsROrC.re (dotProduct (star x) (A.mulVec x)):=hA.2
    constructor
    · rw[IsHermitian] at *
      simp only [conjTranspose_smul, star_trivial]
      rw[Aher]
    · simp only [star_trivial, IsROrC.re_to_real] at *
      intro x
      rw[smul_mulVec_assoc]
      simp only [dotProduct_smul, smul_eq_mul, gt_iff_lt, ge_iff_le]
      exact Iff.mpr (zero_le_mul_left hc) (Aposd x)


theorem add_mem_PosSemidefSet:
  ∀ ⦃x:Matrix n n ℝ⦄ (_ : x ∈ PosSemidefSet) ⦃y:Matrix n n ℝ⦄ (_ : y ∈ PosSemidefSet),
    x + y ∈ PosSemidefSet :=by
    intro A hA B hB
    rw[PosSemidefSet,Set.mem_setOf_eq] at *
    have Aposd:∀ x : n → ℝ, 0 ≤ IsROrC.re (dotProduct (star x) (A.mulVec x)):=hA.2
    have Bposd:∀ x : n → ℝ, 0 ≤ IsROrC.re (dotProduct (star x) (B.mulVec x)):=hB.2
    constructor
    · exact IsHermitian.add hA.1 hB.1
    · simp only [star_trivial, IsROrC.re_to_real] at *
      intro x
      rw[add_mulVec]
      rw[dotProduct_add x]
      exact add_nonneg (Aposd x) (Bposd x)


end SemipositiveDefiniteMatrix


section PositiveDefiniteMatrix

variable [Fintype n]

def PosdefSet:Set (Matrix n n ℝ):={A | PosDef A}

theorem smul_mem_PosdefSet:
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃A : Matrix n n ℝ⦄, A ∈ PosdefSet → c • A ∈ PosdefSet:=by
    intro c hc A hA
    rw[PosdefSet,Set.mem_setOf_eq] at *
    have Aher:IsHermitian A:=hA.1
    have Aposd:∀ x : n → ℝ, x ≠ 0 → 0 < IsROrC.re (dotProduct (star x) (A.mulVec x)):=hA.2
    constructor
    · rw[IsHermitian] at *
      simp only [conjTranspose_smul, star_trivial]
      rw[Aher]
    · simp only [star_trivial, IsROrC.re_to_real] at *
      intro x hx
      rw[smul_mulVec_assoc]
      simp only [dotProduct_smul, smul_eq_mul, gt_iff_lt, ge_iff_le] at *
      exact Real.mul_pos hc (Aposd x hx)


theorem add_mem_PosdefSet:
  ∀ ⦃x:Matrix n n ℝ⦄ (_ : x ∈ PosdefSet) ⦃y:Matrix n n ℝ⦄ (_ : y ∈ PosdefSet),
    x + y ∈ PosdefSet :=by
    intro A hA B hB
    rw[PosdefSet,Set.mem_setOf_eq] at *
    have Aposd:∀ x : n → ℝ, x ≠ 0 → 0 < IsROrC.re (dotProduct (star x) (A.mulVec x)):=hA.2
    have Bposd:∀ x : n → ℝ, x ≠ 0 → 0 < IsROrC.re (dotProduct (star x) (B.mulVec x)):=hB.2
    constructor
    · exact IsHermitian.add hA.1 hB.1
    · simp only [star_trivial, IsROrC.re_to_real] at *
      intro x hx
      rw[add_mulVec]
      rw[dotProduct_add x]
      exact add_pos (Aposd x hx) (Bposd x hx)


end PositiveDefiniteMatrix
