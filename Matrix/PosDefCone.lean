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
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
-- import GeneralizedInequality

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

noncomputable instance toConvexCone.PosDef : ConvexCone ℝ (Matrix n n ℝ) where
  carrier := PosdefSet
  smul_mem' := smul_mem_PosdefSet
  add_mem' := add_mem_PosdefSet

lemma id_is_posdef : sorry := by sorry
-- lemma id_is_posdef : PosDef (id : Matrix n n ℝ) := by
--   unfold PosDef
--   constructor
--   · exact rfl
--   · intro x
--     dsimp only [IsROrC.re_to_real]
--     have : star x ⬝ᵥ mulVec 0 x = 0 := by
--       unfold star mulVec
--       simp only [Matrix.zero_apply, zero_dotProduct', dotProduct_zero']
--     rw [this]

noncomputable instance toProperCone'.PosDef : ProperCone' ℝ (Matrix n n ℝ) :=
  { toConvexCone.PosDef with
    nonempty' := by
      have : (0 : Matrix n n ℝ) ∈ PosdefSet := by
        unfold PosdefSet
        dsimp only [mem_setOf_eq]
        apply id_is_posdef
      exact nonempty_of_mem this
    is_closed' := sorry
    salient' := sorry
    solid' := sorry
  }

namespace ProperCone.PosSemidef

noncomputable instance : Coe (toProperCone'.PosDef) (toConvexCone.PosDef) := sorry
-- ⟨fun K => K.1⟩

protected theorem salient.PosDef (toProperCone'.PosDef : ProperCone ℝ (Matrix n n ℝ)) : Salient (toProperCone'.PosSemidef : ConvexCone ℝ (Matrix n n ℝ)) := sorry

instance toPreorder.PosDef : Preorder (Matrix n n ℝ) where
  le x y := y - x ∈ toProperCone'.PosDef
  le_refl x := by
    change x - x ∈ toProperCone'.PosDef
    rw [sub_self x]
    apply id_is_posdef
  le_trans x y z xy zy := by
    dsimp; dsimp at xy; dsimp at zy
    have h : z - x = z - y + (y - x) := by
      rw [sub_add_sub_cancel]
    rw [h]
    exact add_mem_PosdefSet zy xy
  lt x y := y - x ∈ toProperCone'.PosDef ∧ ¬ x - y ∈ toProperCone'.PosDef
  lt_iff_le_not_le x y : (y - x ∈ toProperCone'.PosDef ∧ ¬ x - y ∈ toProperCone'.PosDef) ↔ (y - x ∈ toProperCone'.PosDef ∧ ¬ x - y ∈ toProperCone'.PosDef) := Iff.rfl

instance toPartialOrder.PosDef : PartialOrder (Matrix n n ℝ) :=
  { toPreorder.PosDef with
      le_antisymm := by
        intro a b ab ba
        by_contra h₁
        have h₂ : b - a ≠ 0 := fun h₃ => h₁ (eq_of_sub_eq_zero h₃).symm
        have h := toProperCone'.PosDef.salient toProperCone'.PosDef
        have H := h (b - a) ab h₂
        rw [neg_sub b a] at H
        exact H ba
  }
