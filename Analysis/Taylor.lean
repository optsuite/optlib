/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Analysis.Calculation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x p y : E} {f : E → ℝ} {f' : E → E} {s : Set E}

/-
  The Main Theorem states: if f is differentiable with gradient f',
  then f(x + p) = f (x) + inner (f' (x + t • p)) p for some t ∈ (0, 1).
-/
open Set InnerProductSpace

theorem expansion (hf : ∀ x : E, HasGradientAt f (f' x) x) (x p : E) :
    ∃ t : ℝ, t > 0 ∧ t < 1 ∧ f (x + p) = f x + inner (f' (x + t • p)) p := by
  let g := fun r : ℝ ↦ f (x + r • p)
  let g' := fun r : ℝ ↦ (inner (f' (x + r • p)) p : ℝ)
  have h1 : ∀ r , HasDerivAt g (g' r) r := by
    let h := fun r : ℝ ↦ x + r • p
    have : g = f ∘ h := by rfl
    rw [this]; intro r
    have : inner (f' (x + r • p)) p = toDual ℝ  E (f' (x + r • p)) p := rfl
    simp; rw [this]; apply HasFDerivAt.comp_hasDerivAt
    · apply HasGradientAt.hasFDerivAt
      exact hf (x + r • p)
    · apply HasDerivAt.const_add
      have ht: HasDerivAt (fun x : ℝ ↦ x) 1 r := hasDerivAt_id' r
      have : HasDerivAt (fun r : ℝ ↦ r • p) ((1 : ℝ) • p) r := by
        apply HasDerivAt.smul_const ht p
      rw [one_smul] at this; exact this
  have e1 : f (x + p) = g 1 := by simp [g]
  have e2 : f x = g 0 := by simp [g]
  have e3 : ∀ t, inner (f' (x + t • p)) p = g' t := by simp [g']
  rw [e1, e2]
  have : ∃ c ∈ Set.Ioo 0 1, g' c = (g 1 - g 0) / (1 - 0) := by
    apply exists_hasDerivAt_eq_slope g g' (by norm_num)
    · have : ∀ x ∈ Icc 0 1, HasDerivAt g (g' x) x := by
        intro x _
        exact (h1 x)
      exact HasDerivAt.continuousOn this
    · simp [h1]
  rcases this with ⟨c, ⟨c1, c2⟩, h2⟩
  use c
  constructor; exact c1;
  constructor; exact c2;
  rw [e3 c]; simp [h2]
