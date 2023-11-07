/-
Copyright (c) 2023 Heying Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Heying Wang.
-/

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
/-
  matrix equalities
-/
open Matrix
open Set

section PosSemidef

variable {𝕜 n α: Type _}

variable [OrderedSemiring 𝕜][Fintype n][SMul 𝕜 α][Add α]

/-
## The following codes are exactly in SymPosde.lean.
-/
def PosSemidefSet [Fintype n] : Set (Matrix n n ℝ):={A | PosSemidef A}

theorem smul_mem_PosSemidefSet:
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃A : Matrix n n ℝ⦄, A ∈ PosSemidefSet → c • A ∈ PosSemidefSet := by sorry

theorem add_mem_PosSemidefSet:
  ∀ ⦃x:Matrix n n ℝ⦄ (_ : x ∈ PosSemidefSet) ⦃y:Matrix n n ℝ⦄ (_ : y ∈ PosSemidefSet),
    x + y ∈ PosSemidefSet := by sorry
/-
The codes above are exactly in SymPosde.lean.
-/

lemma zero_is_possemidef : PosSemidef (0 : Matrix n n ℝ) := by
  unfold PosSemidef
  constructor
  · exact rfl
  · intro x
    dsimp only [IsROrC.re_to_real]
    have : star x ⬝ᵥ mulVec 0 x = 0 := by
      unfold star mulVec
      simp only [Matrix.zero_apply, zero_dotProduct', dotProduct_zero']
    rw [this]

instance toPreorder.PosSemidef : Preorder (Matrix n n ℝ) where
  le x y := y - x ∈ PosSemidefSet
  le_refl x := by
    change x - x ∈ PosSemidefSet
    rw [sub_self x]
    apply zero_is_possemidef
  le_trans x y z xy zy := by
    dsimp; dsimp at xy; dsimp at zy
    have h : z - x = z - y + (y - x) := by
      rw [sub_add_sub_cancel]
    rw [h]
    exact add_mem_PosSemidefSet zy xy
  lt x y := y - x ∈ PosSemidefSet ∧ ¬ x - y ∈ PosSemidefSet
  lt_iff_le_not_le x y : (y - x ∈ PosSemidefSet ∧ ¬ x - y ∈ PosSemidefSet) ↔ (y - x ∈ PosSemidefSet ∧ ¬ x - y ∈ PosSemidefSet) := Iff.rfl

instance toPartialOrder.PosSemidef : PartialOrder (Matrix n n ℝ) :=
  { toPreorder.PosSemidef with
      le_antisymm := by
        intro a b ab ba
        by_contra h₁
        have h₂ : b - a ≠ 0 := fun h₃ => h₁ (eq_of_sub_eq_zero h₃).symm
        have h : ∀ (x : Matrix n n ℝ), x ∈ PosSemidefSet → x ≠ 0 → ¬ -x ∈ PosSemidefSet := by
          dsimp only [ne_eq]
          intro x h₀ h₁
          have h₁ : x ≠ 0 := h₁
          dsimp only at h₀
          unfold PosSemidefSet at h₀; dsimp only [mem_setOf_eq] at h₀
          unfold Matrix.PosSemidef at h₀; dsimp only [IsROrC.re_to_real] at h₀
          have h₀₂ : ∀ (x_1 : n → ℝ), 0 ≤ x_1 ⬝ᵥ mulVec x x_1 := h₀.right
          dsimp only
          unfold PosSemidefSet; dsimp only [mem_setOf_eq]
          unfold Matrix.PosSemidef; dsimp only [IsROrC.re_to_real]
          by_contra h
          have h₂ : ∀ (x_1 : n → ℝ), 0 ≤ - (x_1 ⬝ᵥ mulVec x x_1) := by
            intro x_1
            calc
              0 ≤ x_1 ⬝ᵥ mulVec (-x) x_1 := h.right x_1
              _ ≤ - (x_1 ⬝ᵥ mulVec x x_1) := by
                rw [neg_mulVec, dotProduct_neg]
          have h₃ : ∀ (x_1 : n → ℝ), 0 = x_1 ⬝ᵥ mulVec x x_1 := by
            intro x_1
            apply le_antisymm
            · exact h₀₂ x_1
            · have h₃₁ : 0 ≤ - (x_1 ⬝ᵥ mulVec x x_1) := h₂ x_1
              exact neg_nonneg.mp h₃₁
          sorry
        have H := h (b - a) ab h₂
        rw [neg_sub b a] at H
        exact H ba
  }


section PosDef

open Matrix
open Set

variable {𝕜 n α: Type _}

variable [OrderedSemiring 𝕜][Fintype n][SMul 𝕜 α][Add α]

/-
## The following codes are exactly in SymPosde.lean.
-/
def PosdefSet:Set (Matrix n n ℝ):={A | PosDef A}

theorem smul_mem_PosdefSet:
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃A : Matrix n n ℝ⦄, A ∈ PosdefSet → c • A ∈ PosdefSet:=by sorry

theorem add_mem_PosdefSet:
  ∀ ⦃x:Matrix n n ℝ⦄ (_ : x ∈ PosdefSet) ⦃y:Matrix n n ℝ⦄ (_ : y ∈ PosdefSet),
    x + y ∈ PosdefSet :=by sorry
/-
The codes above are exactly in SymPosde.lean.
-/

instance toPreorder.PosDef : Preorder (Matrix n n ℝ) where
  le x y := y - x ∈ PosdefSet
  le_refl x := by
    change x - x ∈ PosdefSet
    rw [sub_self x]
    sorry
  le_trans x y z xy zy := by
    dsimp; dsimp at xy; dsimp at zy
    have h : z - x = z - y + (y - x) := by
      rw [sub_add_sub_cancel]
    rw [h]
    exact add_mem_PosdefSet zy xy
  lt x y := y - x ∈ PosdefSet ∧ ¬ x - y ∈ PosdefSet
  lt_iff_le_not_le x y : (y - x ∈ PosdefSet ∧ ¬ x - y ∈ PosdefSet) ↔ (y - x ∈ PosdefSet ∧ ¬ x - y ∈ PosdefSet) := Iff.rfl

instance toPartialOrder.PosDef : PartialOrder (Matrix n n ℝ) :=
  { toPreorder.PosDef with
      le_antisymm := by
        intro a b ab ba
        by_contra h₁
        have h₂ : b - a ≠ 0 := fun h₃ => h₁ (eq_of_sub_eq_zero h₃).symm
        have h : ∀ (x : Matrix n n ℝ), x ∈ PosdefSet → x ≠ 0 → ¬ -x ∈ PosdefSet := by
          dsimp only [ne_eq]
          intro x h₀ h₁
          have h₁ : x ≠ 0 := h₁
          dsimp only at h₀
          unfold PosdefSet at h₀; dsimp only [mem_setOf_eq] at h₀
          unfold Matrix.PosDef at h₀; dsimp only [IsROrC.re_to_real] at h₀
          have h₀₂ : ∀ (x_1 : n → ℝ), x_1 ≠ 0 → 0 < x_1 ⬝ᵥ mulVec x x_1 := h₀.right
          dsimp only
          unfold PosdefSet; dsimp only [mem_setOf_eq]
          unfold Matrix.PosDef; dsimp only [IsROrC.re_to_real]
          by_contra h
          have h₂ : ∀ (x_1 : n → ℝ), x_1 ≠ 0 → 0 < - (x_1 ⬝ᵥ mulVec x x_1) := by
            intro x_1 hx₁
            calc
              0 < x_1 ⬝ᵥ mulVec (-x) x_1 := h.right x_1 hx₁
              _ ≤ - (x_1 ⬝ᵥ mulVec x x_1) := by
                rw [neg_mulVec, dotProduct_neg]
          let (x_1 : n → ℝ) := fun _ ↦ 1
          have h₃₀ : x_1 ≠ 0 := by
            by_contra h₃₀'
            sorry
          have h₃₁ : 0 < x_1 ⬝ᵥ mulVec x x_1 := h₀₂ x_1 h₃₀
          have h₃₂ : 0 < - (x_1 ⬝ᵥ mulVec x x_1) := h₂ x_1 h₃₀
          by_cases h₄₁ : x_1 ⬝ᵥ mulVec x x_1 < 0
          · apply lt_asymm h₃₁
            exact h₄₁
          · by_cases h₄₂ : x_1 ⬝ᵥ mulVec x x_1 = 0
            · apply ne_of_gt h₃₁
              exact h₄₂
            · have h₄₃ : x_1 ⬝ᵥ mulVec x x_1 > 0 := h₀₂ x_1 h₃₀
              apply lt_asymm h₃₂
              apply neg_lt.mpr
              rw [neg_zero]
              exact h₃₁
        have H := h (b - a) ab h₂
        rw [neg_sub b a] at H
        exact H ba
  }
