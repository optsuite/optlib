/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li,
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Analysis.Calculation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x p y : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open Set

theorem expansion (h : ∀ x : E, HasGradientAt f (f' x) x) (x p : E) :
    ∃ t, t > 0 ∧ t < 1 ∧ f (x + p) = f x + inner (f' (x + t • p)) p := by
  sorry

-- This theorem should not place here, but let's just first do this for now.
theorem continuous (h : ContinuousAt f x) : ∀ ε > 0, ∃ δ > 0, ∀ (y : E), ‖y - x‖ < δ
    → ‖f y - f x‖ < ε := by
  rw [continuousAt_def] at h
  intro ε epos
  let A := Metric.ball (f x) ε
  specialize h A (Metric.ball_mem_nhds (f x) epos)
  rw [Metric.mem_nhds_iff] at h
  rcases h with ⟨δ, dpos, h⟩
  use (δ / 2); constructor
  exact half_pos dpos
  intro x' x1le
  have H1: x' ∈ Metric.ball x δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub, norm_sub_rev]
    apply lt_trans x1le
    linarith
  exact h H1
