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
-- import GeneralizedInequality

-- universe u u' v

-- open BigOperators

-- def Matrix' (m : Type u) (n : Type u') (α : Type v) [Fintype m] [Fintype n] : Type max u u' v :=
--   m → n → α

-- namespace Matrix'

open Matrix
open Set

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

/-
## The following codes are exactly in GeneralizedInequality.lean.
-/
namespace ConvexCone

variable {𝕜 : Type _} [OrderedSemiring 𝕜]

variable {E : Type _} [AddCommGroup E] [TopologicalSpace E] [SMul 𝕜 E]

def Solid (S : ConvexCone 𝕜 E) : Prop :=
  (interior S.carrier).Nonempty

structure ProperCone' (𝕜 : Type _) (E : Type _) [OrderedSemiring 𝕜] [AddCommGroup E]
    [TopologicalSpace E] [SMul 𝕜 E]
    extends ConvexCone 𝕜 E where
  nonempty' : (carrier : Set E).Nonempty
  is_closed' : IsClosed (carrier : Set E)
  salient' : ∀ (x : E), x ∈ (carrier : Set E) → x ≠ 0 → ¬ -x ∈ (carrier : Set E)
  solid' : (interior carrier).Nonempty

namespace ProperCone'

instance : Coe (ProperCone' 𝕜 E) (ConvexCone 𝕜 E) := ⟨fun K => K.1⟩

theorem ext' : Function.Injective ((↑) : ProperCone' 𝕜 E → ConvexCone 𝕜 E) :=
fun S T h => by
  cases S; cases T; congr

instance : SetLike (ProperCone' 𝕜 E) E where
  coe K := K.carrier
  coe_injective' _ _ h := ProperCone'.ext' (SetLike.coe_injective h)

protected theorem nonempty (K : ProperCone' 𝕜 E) : (K : Set E).Nonempty := K.nonempty'

protected theorem isClosed (K : ProperCone' 𝕜 E) : IsClosed (K : Set E) := K.is_closed'

protected theorem salient (K : ProperCone' 𝕜 E) : (K : ConvexCone 𝕜 E).Salient := K.salient'

protected theorem solid (K : ProperCone' 𝕜 E) : (K : ConvexCone 𝕜 E).Solid := K.solid'
/-
The codes above are exactly in GeneralizedInequality.lean.
-/

noncomputable instance toConvexCone.PosSemidef [Fintype n] : ConvexCone ℝ (Matrix n n ℝ) where
  carrier := PosSemidefSet
  smul_mem' := smul_mem_PosSemidefSet
  add_mem' := add_mem_PosSemidefSet

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

noncomputable instance toProperCone'.PosSemidef : ProperCone' ℝ (Matrix n n ℝ) :=
  { toConvexCone.PosSemidef with
    nonempty' := by
      have : (0 : Matrix n n ℝ) ∈ PosSemidefSet := by
        unfold PosSemidefSet
        dsimp only [mem_setOf_eq]
        apply zero_is_possemidef
      exact nonempty_of_mem this
    is_closed' := sorry
    salient' := by
      dsimp only [ne_eq]
      intro x h₀ h₁
      have h₁ : x ≠ 0 := h₁
      unfold toConvexCone.PosSemidef at h₀; dsimp only at h₀
      unfold PosSemidefSet at h₀; dsimp only [mem_setOf_eq] at h₀
      unfold Matrix.PosSemidef at h₀; dsimp only [IsROrC.re_to_real] at h₀
      have h₀₂ : ∀ (x_1 : n → ℝ), 0 ≤ x_1 ⬝ᵥ mulVec x x_1 := h₀.right
      unfold toConvexCone.PosSemidef; dsimp only
      unfold PosSemidefSet; dsimp only [mem_setOf_eq]
      unfold Matrix.PosSemidef; dsimp only [IsROrC.re_to_real]
      by_contra h
      have h₂ : ∀ (x_1 : n → ℝ), 0 ≤ - (x_1 ⬝ᵥ mulVec x x_1) := by
        intro x_1
        calc
          0 ≤ x_1 ⬝ᵥ mulVec (-x) x_1 := h.right x_1
          _ ≤ - (x_1 ⬝ᵥ mulVec x x_1) := by
            rw [neg_mulVec, dotProduct_neg]
      sorry
    solid' := sorry
  }

namespace ProperCone.PosSemidef

noncomputable instance : Coe (toProperCone'.PosSemidef) (toConvexCone.PosSemidef) := sorry
-- ⟨fun K => K.1⟩

protected theorem salient.PosSemidef (toProperCone'.PosSemidef : ProperCone ℝ (Matrix n n ℝ)) : Salient (toProperCone'.PosSemidef : ConvexCone ℝ (Matrix n n ℝ)) := sorry

instance toPreorder.PosSemidef : Preorder (Matrix n n ℝ) where
  le x y := y - x ∈ toProperCone'.PosSemidef
  le_refl x := by
    change x - x ∈ toProperCone'.PosSemidef
    rw [sub_self x]
    apply zero_is_possemidef
  le_trans x y z xy zy := by
    dsimp; dsimp at xy; dsimp at zy
    have h : z - x = z - y + (y - x) := by
      rw [sub_add_sub_cancel]
    rw [h]
    exact add_mem_PosSemidefSet zy xy
  lt x y := y - x ∈ toProperCone'.PosSemidef ∧ ¬ x - y ∈ toProperCone'.PosSemidef
  lt_iff_le_not_le x y : (y - x ∈ toProperCone'.PosSemidef ∧ ¬ x - y ∈ toProperCone'.PosSemidef) ↔ (y - x ∈ toProperCone'.PosSemidef ∧ ¬ x - y ∈ toProperCone'.PosSemidef) := Iff.rfl

instance toPartialOrder.PosSemidef : PartialOrder (Matrix n n ℝ) :=
  { toPreorder.PosSemidef with
      le_antisymm := by
        intro a b ab ba
        by_contra h₁
        have h₂ : b - a ≠ 0 := fun h₃ => h₁ (eq_of_sub_eq_zero h₃).symm
        have h := toProperCone'.PosSemidef.salient toProperCone'.PosSemidef
        have H := h (b - a) ab h₂
        rw [neg_sub b a] at H
        exact H ba
  }
