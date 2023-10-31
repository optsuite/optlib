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

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {x y : E}

/-
  the definition of the conjugate function
-/
def cg (f : E → ℝ) (y : E) : EReal :=
  sSup {(inner y x : ℝ) - f x | x : E}

/-
  the domain of the conjugate function (the set where the infty is not attained)
-/
def cg_dom (f : E → ℝ) : Set E :=
  {x : E | (sSup {(inner x y : ℝ) - f x | y : E} : EReal) ≠ ⊤}

/-
  the strict conjugate function where the image set is ℝ
-/
def strict_cg (f : E → ℝ) (y : E) : ℝ :=
  sSup {inner y x - f x | x : E}

section

/- Fenchel inequality -/
theorem Fenchel (f : E → ℝ) (y x : E) : cg f y ≥ ((inner y x) : ℝ) - f x:= by
  rw [cg]
  apply le_sSup
  use x

theorem convex_cg_dom (f : E → ℝ) : Convex ℝ (cg_dom f) := by
  sorry

theorem convex_cg_fun (f : E → ℝ) (x y : E) (a b: ℝ) (ha : 0 ≤ a) (hb: 0 ≤ b) (hab : a + b = 1):
    strict_cg f (a • x + b • y) ≤ a • strict_cg f x + b • strict_cg f y := by
  sorry

theorem convex_cg (f : E → ℝ) : ConvexOn ℝ (cg_dom f) (fun x => strict_cg f x) := by
  constructor
  · exact convex_cg_dom f
  · intros x hx y hy a b ha hb hab
    calc (fun x => strict_cg f x) (a • x + b • y) = strict_cg f (a • x + b • y) := by rfl
    _ ≤ a • strict_cg f x + b • strict_cg f y := by exact convex_cg_fun f x y a b ha hb hab
    _ = a • (fun x => strict_cg f x) x + b • (fun x => strict_cg f x) y := by rfl

lemma quadratic_cg {b : E} {c : ℝ} :
    strict_cg (fun x ↦ 1 / 2 * inner x x + inner b x + c) y = (inner (y - b) (y - b) / 2 - c) := by
  sorry

lemma norm_cg_dom : cg_dom (fun x ↦ ‖x‖) = {x : E | ‖x‖ ≤ 1} := by
  sorry

lemma norm_cg_value : ∀ (x : E), x ∈ cg_dom (fun x ↦ ‖x‖) → strict_cg (fun t ↦ ‖t‖) x = 0 := by
  sorry

/-
  the definition of the conjugate function for the conjugate function of a function
-/

def cg_double (f : E → ℝ) (y : E) : ℝ :=
  sSup {(inner y x : ℝ) - cg f x | x ∈ cg_dom f}

theorem Fenchel_double (f : E → ℝ) : cg_double f x ≤ f x := by
  sorry

theorem convex_cg_double (f : E → ℝ) (y : E) : ConvexOn ℝ (cg_dom f) (fun x => cg_double f x) := by
  sorry

theorem close_cg_double (f : E → ℝ) (y : E) :
    LowerSemicontinuousOn (fun x => cg_double f x) (cg_dom f) := by
  sorry

theorem convex_close_cg_couble (f : E → ℝ) (hfun : ConvexOn ℝ Set.univ f)
    (hc : LowerSemicontinuousOn f Set.univ) : f x = cg_double f x := by
  sorry
