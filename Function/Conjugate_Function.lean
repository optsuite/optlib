/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Semicontinuous
import Mathlib.Order.CompleteLattice

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
  {x : E | cg f x ≠ ⊤}

/-
  the strict conjugate function where the image set is ℝ
-/
def strict_cg (f : E → ℝ) (y : E) : ℝ :=
  (cg f y).toReal

instance : SMul ℝ EReal :=
{
  smul := fun r x ↦ r * x
}
section


/- Fenchel inequality -/
theorem Fenchel (f : E → ℝ) (y x : E) : cg f y ≥ ((inner y x) : ℝ) - f x := by
  rw [cg]
  apply le_sSup
  use x

lemma up_bottom (f : E → ℝ) (x : E) : cg f x > ⊥ := by
  have h₁ : ((inner x x : ℝ) - f x) ≤ cg f x := by
    apply le_sSup
    use x
  have h₂ : (((inner x x : ℝ) - f x) : EReal) > ⊥ := by
    exact (cmp_eq_lt_iff ⊥ ((inner x x : ℝ) - (f x) : EReal)).mp rfl
  exact LT.lt.trans_le h₂ h₁

theorem equiv_cg_strict_cg (f : E → ℝ) (h : x ∈ cg_dom f) : cg f x = strict_cg f x := by
  have h₁ : cg f x ≠ ⊥ :=ne_bot_of_gt (up_bottom f x)
  rw [cg_dom] at h; dsimp at h; push_neg at h;
  rw [strict_cg]; symm
  exact EReal.coe_toReal h h₁

theorem convex_cg_dom (f : E → ℝ) : Convex ℝ (cg_dom f) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  rw [cg_dom]
  dsimp; push_neg
  have h₁: cg f (a • x + b • y) < a • cg f x + b • cg f y := by
    rw [cg]
    have hh: sSup {x1 | ∃ x2, ((((inner (a • x + b • y) x2) : ℝ) - f x2) : EReal) = x1} =
        sSup {x1 | ∃ x2, (a • (inner x x2 : ℝ) + b • (inner y x2 : ℝ) - f x2 : EReal) = x1} := by
      apply congr_arg
      ext xo
      dsimp only [Set.mem_setOf_eq]
      have : ∀ xk : E, (((inner (a • x) xk) : ℝ) : EReal) + (inner (b • y) xk : ℝ) =
          (((inner (a • x) xk : ℝ) + (inner (b • y) xk : ℝ)) : ℝ) := by
        intro xk; rfl
      constructor
      · intro h
        rcases h with ⟨xk, hxk⟩
        use xk; rw [← inner_smul_real_left, ← inner_smul_real_left]; simp
        rw [inner_add_left, ← this] at hxk; exact hxk
      intro h
      rcases h with ⟨xk, hxk⟩
      use xk; rw [← inner_smul_real_left, ← inner_smul_real_left] at hxk;
      simp at hxk; rw [this xk, ← inner_add_left] at hxk; exact hxk    -- 这两块可以合在一起
    have hl: sSup {x1 | ∃ x2, (a • (inner x x2 : ℝ) + b • (inner y x2 : ℝ) - f x2 : EReal) = x1} <
        sSup {x1 | ∃ x2, (a • (inner x x2 : ℝ) - a • f x2 : EReal) = x1} +
        sSup {x1 | ∃ x2, (b • (inner y x2 : ℝ) - b • f x2 : EReal) = x1} := by
      sorry
    have ha' : sSup {x1 : EReal | ∃ x2, a • (inner x x2 : ℝ) - a • f x2 = x1} =
        a • sSup {x1 : EReal| ∃ x2, (inner x x2 : ℝ) - f x2 = x1} := by
      rw [IsLUB.sSup_eq];sorry
    have hb' : sSup {x1 : EReal| ∃ x2, b • (inner y x2  : ℝ) - b • f x2 = x1} =
        b • sSup {x1 : EReal| ∃ x2, (inner y x2 : ℝ) - f x2 = x1} := by sorry
    rw [cg, cg, ← ha', ← hb']
    rw [hh]; exact hl
  have h₂: cg f (a • x + b • y) < ⊤ := by
    rw [cg_dom] at hx hy
    dsimp at hx hy
    push_neg at hx hy
    have : a * cg f x + b * cg f y < ⊤ := by
      rw [equiv_cg_strict_cg f hx, equiv_cg_strict_cg f hy]
      exact (cmp_eq_lt_iff (a * (strict_cg f x) + b * (strict_cg f y) : EReal) ⊤).mp rfl
    exact gt_trans this h₁
  exact ne_top_of_lt h₂

theorem convex_cg_fun (f : E → ℝ) (x y : E) (a b: ℝ) (ha : 0 ≤ a) (hb: 0 ≤ b) (hab : a + b = 1):
    strict_cg f (a • x + b • y) ≤ a • strict_cg f x + b • strict_cg f y := by
  sorry

theorem convex_cg (f : E → ℝ) : ConvexOn ℝ (cg_dom f) (fun x => strict_cg f x) := by
  constructor
  · exact convex_cg_dom f
  · intros x _ y _ a b ha hb hab
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
