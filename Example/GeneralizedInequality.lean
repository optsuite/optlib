/-
Copyright (c) 2023 Heying Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Heying Wang.
-/

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.Cone.Proper

/-
# Proper Cone'

In this file, we defined ProperCone' as nonempty, closed, salient, solid convex cones. Some basic properties are also listed in the first part of this file.

# Partial order

In this part, we define the partial order respected to proper cones we defined above. Moreover, we list some generalized inequalities and give brief proofs.

## References

[Convex Cone](https://en.wikipedia.org/wiki/Convex_cone#:~:text=The%20term%20proper%20(convex)%20cone,salient%2C%20and%20full%2Ddimensional.)

[Convex set](http://faculty.bicmr.pku.edu.cn/~wenzw/optbook/lect/02-convex-set.pdf)
-/

section ProperCone'

open Set

namespace ConvexCone

variable {𝕜 : Type _} [OrderedSemiring 𝕜]

variable {E : Type _} [AddCommGroup E] [TopologicalSpace E] [SMul 𝕜 E]

/-
A proper cone here, named as ProperCone'', is a convex cone `K` that is nonempty, closed, salient and solid. Such a cone is obviously not an empty set, the universe, a half-space or a singleton.
-/

/-
A convex cone is said to be solid if its interior is nonempty.
-/
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
For every real proper cone in an Hilbert space, it is pointed.
-/
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (s t : Set H)

protected theorem pointed (K : ProperCone' ℝ H) : (K : ConvexCone ℝ H).Pointed :=
  (K : ConvexCone ℝ H).pointed_of_nonempty_of_isClosed K.nonempty' K.isClosed


section GeneralizedInequalities

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

instance toPreorder.ProperCone' (S : ProperCone' ℝ E) : Preorder E where
  le x y := y - x ∈ S
  le_refl x := by
    change x - x ∈ S
    rw [sub_self x]
    exact ProperCone'.pointed S
  le_trans x y z xy zy := by
    dsimp; dsimp at xy; dsimp at zy
    have h : z - x = z - y + (y - x) := by
      rw [sub_add_sub_cancel]
    rw [h]
    exact S.add_mem zy xy
/-
For the lt-part of Preorder, we usually define a < b as b - a ∈ S.interior for cones. So we will temporarily ignore this in defining preorder of proper cones.
-/

instance toPartialOrder.ProperCone' (S : ProperCone' ℝ E) : PartialOrder E :=
  { toPreorder.ProperCone' S with
    le_antisymm := by
      intro a b ab ba
      by_contra h₁
      have h₂ : b - a ≠ 0 := fun h₃ => h₁ (eq_of_sub_eq_zero h₃).symm
      have h := ProperCone'.salient S
      have H := h (b - a) ab h₂
      rw [neg_sub b a] at H
      exact H ba
  }

/-
The followings are two basic properties for preorders.
-/
theorem add_le_add.ProperCone' (S : ProperCone' ℝ E) (a b c d : E) (h₁ : (toPartialOrder.ProperCone' S).le a b) (h₂ : (toPartialOrder.ProperCone' S).le c d): (toPartialOrder.ProperCone' S).le (a + c) (b + d) := by
  have h₁' : b - a ∈ S := h₁
  have h₂' : d - c ∈ S := h₂
  have h₃' : b - a + (d - c) ∈ S := S.add_mem h₁' h₂'
  have h₃ : b - a + (d - c) = b + d - (a + c) := sub_add_sub_comm b a d c
  rw [h₃] at h₃'
  exact h₃'

theorem add_le_mul_of_nonneg_const.ProperCone' (S : ProperCone' ℝ E) (a b : E) (c : ℝ) (h₀ : 0 ≤ c) (h₁ : (toPartialOrder.ProperCone' S).le a b) : (toPartialOrder.ProperCone' S).le (c • a) (c • b) := by
  by_cases h₀' : c = 0
  · have hl : c • a = 0 := smul_eq_zero_of_left h₀' a
    have hr : c • b = 0 := smul_eq_zero_of_left h₀' b
    rw [hl, hr]
    have h0 : 0 - 0 ∈ S := by
      simp only [sub_self]
      exact ProperCone'.pointed S
    exact h0
  have h₀'' : 0 < c := Ne.lt_of_le' h₀' h₀
  have h₁' : b - a ∈ S := h₁
  have h₂ : c • (b - a) ∈ S := by
    apply S.smul_mem
    · exact h₀''
    · exact h₁'
  have h₂' : c • (b - a) = c • b - c • a := smul_sub c b a
  rw [h₂'] at h₂
  exact h₂
