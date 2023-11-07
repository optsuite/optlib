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
def prox_prop (f : E → ℝ) (x : E) (xm : E) : Prop :=
  IsMinOn (fun u ↦ f u + ‖u - x‖ ^ 2 / 2) univ xm

/-
  the set of all points that satisfy the proximal property
-/
def prox_set (f : E → ℝ) (x : E) : Set E := {u | prox_prop f x u}

/-
  if the proximal set is nonempty then we can choose the point that satisfies the proximal property
-/
def prox_point (f : E → ℝ) (x : E) (h : ∃ y, prox_set f x y) : E :=
  Classical.choose h

/-
  the definition of the proximal operator for a closed convex function
-/
def prox_point_c (f : E → ℝ) (x : E) (hfun : ConvexOn ℝ univ f)
    (hc : LowerSemicontinuousOn f univ) : E :=
  have h : ∃ y, prox_set f x y := by sorry
  Classical.choose h

theorem prox_well_define (f : E → ℝ) (hfun : ConvexOn ℝ univ f)
    (hc : LowerSemicontinuousOn f univ) : ∀ x, ∃ y, prox_prop f x y :=
  sorry

theorem prox_well_define' (f : E → ℝ) (hfun : ConvexOn ℝ univ f)
    (hc : LowerSemicontinuousOn f univ) (h₁ : prox_prop f x y₁)
    (h₂ : prox_prop f x y₂) : y₁ = y₂ :=
  sorry

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x y y₁ y₂: E} {s : Set E} {f : E → ℝ}

theorem prox_iff_grad (f : E → ℝ) {f' : E → E} (hfun : ConvexOn ℝ univ f)
    (hc : LowerSemicontinuousOn f univ) (hdiff : ∀ x, HasGradientAt f (f' x) x) :
    ∀ u : E, prox_prop f x u ↔ f' u = x - u :=
  sorry

theorem prox_iff_grad_smul (f : E → ℝ) {f' : E → E} (t : ℝ)(hfun : ConvexOn ℝ univ f)
    (hc : LowerSemicontinuousOn f univ) (hdiff : ∀ x, HasGradientAt f (f' x) x) :
    ∀ u : E, prox_prop (t • f) x u ↔ t • f' u = x - u :=
  sorry

theorem prox_iff_grad' (f : E → ℝ) {f' : E → E} (hfun : ConvexOn ℝ univ f)
    (hc : LowerSemicontinuousOn f univ) (hdiff : ∀ x, HasGradientAt f (f' x) x) :
    ∀ u : E, u = prox_point_c f x hfun hc ↔ f' u = x - u :=
  sorry

theorem prox_iff_grad'' (f : E → ℝ) {f' : E → E} (hfun : ConvexOn ℝ univ f)
    (hc : LowerSemicontinuousOn f univ) (hdiff : ∀ x, HasGradientAt f (f' x) x) :
    ∀ u : E, u = prox_point f x (prox_well_define f hfun hc x) ↔ f' u = x - u :=
  sorry
