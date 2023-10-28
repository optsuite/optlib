/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li
-/
import Analysis.Calculation
import Mathlib.Tactic
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.Convex.Basic

/-!
 proximal operator
-/
noncomputable section

open Set

variable {E : Type*} [NormedAddCommGroup E] [SMul ℝ E] [CompleteSpace E]
variable {x y y₁ y₂: E} {s : Set E} {f : E → ℝ}

/-
  a point satisfies the proximal property if it is a minimizer of the function f(u)+1/2‖u-x‖²
-/
def prox_prop (f : E → ℝ) (s : Set E) (x : E) (xm : E) : Prop :=
  IsMinOn (fun u ↦ f u + ‖u - x‖ ^ 2 / 2) s xm

/-
  the set of all points that satisfy the proximal property
-/
def prox_set (f : E → ℝ) (s : Set E) (x : E) : Set E := {u | prox_prop f s x u}

/-
  if the proximal set is nonempty then we can choose the point that satisfies the proximal property
-/
def prox_point (f : E → ℝ) (s : Set E) (x : E) (h : ∃ y, prox_prop f s x y) : E :=
  Classical.choose h

theorem prox_well_define (f : E → ℝ) (hfun : ConvexOn ℝ univ f)
    (hc : LowerSemicontinuousOn f univ) : ∀ x, ∃ y, prox_prop f univ x y :=
  sorry

theorem prox_well_define' (f : E → ℝ) (hfun : ConvexOn ℝ univ f)
    (hc : LowerSemicontinuousOn f univ) (h₁ : prox_prop f univ x y₁)
    (h₂ : prox_prop f univ x y₂) : y₁ = y₂ :=
  sorry

theorem
