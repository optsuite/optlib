/-
Copyright (c) 2024 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li,
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Analysis.Calculation

/-!
# Constrained_Problem

## Main results

This file contains the following parts of constrained optimization problem.
* the definition of a constrained optimization prblem
* the definition of a local minima, global minima, strict local minima
* the definition of the active set
-/

open InnerProductSpace Set BigOperators

noncomputable section

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {τ σ : Finset ℕ}

/-
  the definition of an unconstrained optimization problem.
  The objective function is a function from a Hilbert space to ℝ.
  The equality constraints are a set of functions from a Hilbert space to ℝ.
  The inequality constraints are a set of functions from a Hilbert space to ℝ.
-/
structure Constrained_OptimizationProblem (E : Type _) (τ σ : Finset ℕ) :=
(domain : Set E)
(equality_constraints : (i : ℕ)  → E → ℝ)
(inequality_constraints : (j : ℕ) → E → ℝ)
(eq_ine_not_intersect : τ ∩ σ = ∅)
(objective : E → ℝ)

namespace Constrained_OptimizationProblem

variable (p : Constrained_OptimizationProblem E τ σ) (x : E)

open Topology InnerProductSpace Set Filter Tendsto

/-
  The feasible point is a point that satisfies all the constraints.
-/
def FeasPoint (point : E) : Prop :=
  point ∈ p.domain ∧ (∀ i ∈ τ, p.equality_constraints i point = 0)
  ∧ (∀ j ∈ σ, p.inequality_constraints j point ≥ 0)

/-
  The feasible set is the set that satisfies all the constraints. Denote the set as Ω
-/
def FeasSet : Set E :=
  {point | p.FeasPoint point}

/-
  A point x₁ ∈ Ω is a global minimizer if f x₁ ≤ f x for all x ∈ Ω.
-/
def Global_Minima (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsMinOn p.objective p.FeasSet point

/-
  A point x₁ ∈ Ω is a local minimizer if there is a neighborhood B of x₁
  such that f x₁ ≤ f x for all x ∈ B ∩ Ω.
-/
def Local_Minima (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsLocalMinOn p.objective p.FeasSet point

/-
  A vector x∗ is a strict local solution (also called a strong local solution) if x∗ ∈ Ω and there
  is a neighborhood B of x∗ such that f (x) > f (x∗) for all x ∈ B ∩ Ω with x ≠ x∗.
-/
def Strict_Local_Minima (point : E) : Prop :=
  (p.FeasPoint point) ∧ (∃ ε > 0, ∀ y, p.FeasPoint y → y ∈ Metric.ball point ε → y ≠ point
  → p.objective point > p.objective y)

/-
  The active set A(x) at any feasible x consists of the equality constraint indices from E
  together with the indices of the inequality constraints i for which c_i(x) = 0;
-/
def active_set (point : E) : Finset ℕ :=
  τ ∪ σ.filter fun i : ℕ ↦ p.inequality_constraints i point = (0 : ℝ)

/-
  Given a feasible point x and the active constraint set A(x) of Definition 12.1, the set of
  linearized feasible directions is defined as
-/
def linearized_feasible_directions (point : E) : Set E :=
  {v | (∀ i ∈ τ, ⟪gradient (p.equality_constraints i) point, v ⟫_ℝ = (0 : ℝ))
    ∧ ∀ j ∈ σ ∩ (p.active_set point), ⟪gradient (p.inequality_constraints j) point, v⟫_ℝ ≥ (0 : ℝ)}

/-
  The set of linearized_feasible_directions is a convex set
-/
theorem linearized_feasible_directions_convex (point : E) :
    Convex ℝ (p.linearized_feasible_directions point) := by
  intro v₁ h₁ v₂ h₂ a b ha hb hab
  rw [linearized_feasible_directions] at h₁ h₂; rw [linearized_feasible_directions]
  dsimp at h₁ h₂; dsimp
  constructor
  · rcases h₁ with ⟨h₁, _⟩
    rcases h₂ with ⟨h₂, _⟩
    intro i itau
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, (h₁ i itau), (h₂ i itau)]
    linarith
  · rcases h₁ with ⟨_, h₁⟩
    rcases h₂ with ⟨_, h₂⟩
    intro j jsigma
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    apply add_nonneg
    . apply mul_nonneg ha (h₁ j jsigma)
    . apply mul_nonneg hb (h₂ j jsigma)

/-
  Given the point x and the active set A(x), we say that the linear
  independence constraint qualification (LICQ) holds if the set of active constraint gradients
  {∇ci(x), i ∈ A(x)} is linearly independent.
-/
def LICQ (point : E) : Prop :=
  LinearIndependent ℝ (fun i : p.active_set point ↦ gradient (p.equality_constraints i) point)

/-
  Lagrangian function for the general problem
-/
def Lagrange_function :=
  fun (x : E) (lambda1 : ℕ → ℝ) (lambda2 : ℕ → ℝ) ↦ (p.objective x)
    - (τ.sum fun i ↦ (lambda1 i) * p.equality_constraints i x)
    - (σ.sum fun j ↦ (lambda2 j) * p.inequality_constraints j x)

end Constrained_OptimizationProblem

end
