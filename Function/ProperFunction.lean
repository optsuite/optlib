/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Semicontinuous

/-!
  the defition of the conjugate function and the Fenchel inequality
  need to solve the sorry
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {x y : ℝ} {s : Set E}

def Proper (f : E → EReal) : Prop :=
  (∀ x, f x > ⊥) ∧ (∃ x, f x < ⊤)

def Effective_Domain (f : E → EReal) : Set E :=
  {x | f x < ⊤}

theorem Proper_Nonempty_Effective_Domain (hp : Proper f) : (Effective_Domain f).Nonempty := by
  rcases hp with ⟨_, h2⟩
  rw [Effective_Domain]
  exact h2
