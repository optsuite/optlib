/-
Copyright (c) 2025 Chenyi Li, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chenyi Li, Zaiwen Wen
-/
import Optlib.Optimality.Constrained_Problem
import Optlib.Convex.ConvexFunction

section Duality

open Constrained_OptimizationProblem InnerProductSpace Set BigOperators

noncomputable section Definition

namespace Constrained_OptimizationProblem

variable {E : Type _} {τ σ : Finset ℕ}
variable {p : Constrained_OptimizationProblem E τ σ}

def dual_objective : (τ → ℝ) → (σ → ℝ) → EReal :=
  fun (lambda1 : τ → ℝ) (lambda2 : σ → ℝ) ↦
    ⨅ x ∈ p.domain, (p.Lagrange_function x lambda1 lambda2).toEReal

def dual_problem : Constrained_OptimizationProblem ((τ → ℝ) × (σ → ℝ)) ∅ σ where
  domain := {x | p.dual_objective x.1 x.2 ≠ ⊥}
  equality_constraints := fun _ _ ↦ 0
  inequality_constraints := fun i x ↦ if h : i ∈ σ then x.2 ⟨i, h⟩ else 0
  objective := fun x ↦ (p.dual_objective x.1 x.2).toReal
  eq_ine_not_intersect := by simp

def inf_value : EReal := sInf (Real.toEReal '' (p.objective '' (p.FeasSet)))

def sup_value : EReal := sSup (Real.toEReal '' (p.objective '' (p.FeasSet)))

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def KKT_point (self : Constrained_OptimizationProblem E τ σ)
    (x : E) (lambda : τ → ℝ) (mu : σ → ℝ) : Prop :=
  (gradient (fun m ↦ (self.Lagrange_function m lambda mu)) x = 0)
  ∧ (x ∈ self.FeasSet) ∧ (mu ≥ 0)
  ∧ (∀ i : σ, mu i * self.inequality_constraints i x = 0)

end Constrained_OptimizationProblem

end Definition

section WeakDuality

variable {E : Type _} {τ σ : Finset ℕ}
variable {p : Constrained_OptimizationProblem E τ σ} {x : E}

lemma empty_domain_inf_value_top {p : Constrained_OptimizationProblem E τ σ} (hp : (p.domain) = ∅) :
    p.inf_value = ⊤ := by
  unfold inf_value FeasSet FeasPoint
  simp [hp]
  rfl

lemma empty_FeasSet_inf_value_top {p : Constrained_OptimizationProblem E τ σ} (hp : (p.FeasSet) = ∅) :
    p.inf_value = ⊤ := by
  unfold inf_value
  simp [hp]
  rfl

lemma objective_le_sup {p : Constrained_OptimizationProblem E τ σ} (x : E) (hx : x ∈ p.FeasSet) :
    (p.objective x).toEReal ≤ p.sup_value := by
  unfold sup_value
  apply le_sSup
  simp; use x

lemma dual_objective_le_top_nonempty {p : Constrained_OptimizationProblem E τ σ} (hp : (p.domain).Nonempty) :
    ∀ lambda1 lambda2, p.dual_objective lambda1 lambda2 < ⊤ := by
  intro lambda1 lambda2
  unfold dual_objective
  let x := Classical.choose hp
  refine iInf_lt_top.mpr ?_
  refine ⟨x, ?_⟩
  refine iInf_lt_top.mpr ?_
  exact ⟨Classical.choose_spec hp, by
    exact EReal.coe_lt_top (p.Lagrange_function x lambda1 lambda2)⟩

lemma dual_objective_eq_top_empty {p : Constrained_OptimizationProblem E τ σ} (hp : (p.domain) = ∅) :
    ∀ lambda1 lambda2, p.dual_objective lambda1 lambda2 = ⊤ := by
  intro lambda1 lambda2
  unfold dual_objective
  simp [hp]
  rfl

lemma objective_infimum_global_minimum {p : Constrained_OptimizationProblem E τ σ}
    (hp : (p.objective x).toEReal = p.inf_value) (hx : x ∈ p.FeasSet) :
    p.Global_Minimum x := by
  unfold Global_Minimum
  constructor
  · exact hx
  intro x1 hx; simp
  unfold inf_value at hp
  have : (p.objective x).toEReal ≤ (p.objective x1).toEReal := by
    rw [hp]
    apply sInf_le
    simp; use x1
  simpa

lemma global_minimum_objective_infimum {p : Constrained_OptimizationProblem E τ σ}
    (hp : p.Global_Minimum x) :
    (p.objective x).toEReal = p.inf_value := by
  unfold Global_Minimum at hp
  unfold inf_value
  apply Eq.symm (sInf_eq_of_forall_ge_of_forall_gt_exists_lt _ _)
  · intro a ha
    simp at ha
    rcases ha with ⟨x1, hx1, hx2⟩
    rw [← hx2]
    simp; apply hp.2 hx1
  intro w hw
  use (p.objective x).toEReal
  simp; constructor
  · use x; simp
    unfold FeasSet; simp; exact hp.1
  exact hw

lemma objective_maximum_global_maximum {p : Constrained_OptimizationProblem E τ σ}
    (hp : (p.objective x).toEReal = p.sup_value) (hx : x ∈ p.FeasSet) :
    p.Global_Maximum x := by
  unfold Global_Maximum
  constructor
  · exact hx
  intro x1 hx; simp
  unfold sup_value at hp
  have : (p.objective x).toEReal ≥ (p.objective x1).toEReal := by
    rw [hp]
    apply le_sSup
    simp; use x1
  simpa

theorem weak_duality {p : Constrained_OptimizationProblem E τ σ}
    (lambda1 : τ → ℝ) {lambda2 : σ → ℝ} (mpos : lambda2 ≥ 0):
    p.dual_objective lambda1 lambda2 ≤ p.inf_value := by
  unfold inf_value dual_objective
  apply le_sInf; simp
  intro a ha
  let minL := ⨅ x ∈ p.domain, (p.Lagrange_function x lambda1 lambda2).toEReal
  have neq : ∀ x' ∈ p.FeasSet, minL ≤ p.objective x' := by
    intro x hx
    simp [minL]; unfold FeasSet FeasPoint at hx; simp at hx
    apply le_trans (biInf_le _ hx.1.1)
    simp; unfold Lagrange_function
    have : ∑ i : τ, lambda1 i * p.equality_constraints i x = 0:= by
      apply Finset.sum_eq_zero
      intro i _
      rw [hx.1.2 _ i.2, mul_zero]
    have : ∑ j : σ, lambda2 j * p.inequality_constraints j x ≥ 0 := by
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg (mpos j) (hx.2.2 j j.2)
    linarith
  exact neq a ha

theorem weak_duality_aux {p : Constrained_OptimizationProblem E τ σ} (hp : (p.domain).Nonempty) :
    (p.dual_problem).sup_value ≤ p.inf_value := by
  unfold sup_value dual_problem; simp
  intro b lambda1 lambda2 hl hl2
  rw [← hl2]
  have : ((p.dual_objective lambda1 lambda2).toReal).toEReal
      = p.dual_objective lambda1 lambda2 := by
    apply EReal.coe_toReal
    · obtain hlt := dual_objective_le_top_nonempty hp lambda1 lambda2
      exact LT.lt.ne_top hlt
    unfold FeasSet FeasPoint at hl; simp at hl
    exact hl.1
  rw [this]
  apply weak_duality
  unfold FeasSet FeasPoint at hl; simp at hl
  intro j
  obtain hlj := hl.2 j j.2
  simp at hlj; simpa

theorem weak_duality' {p : Constrained_OptimizationProblem E τ σ} :
    (p.dual_problem).sup_value ≤ p.inf_value := by
  by_cases hp : (p.domain).Nonempty
  · exact weak_duality_aux hp
  push_neg at hp
  rw [empty_domain_inf_value_top hp]
  exact le_top

end WeakDuality

section Convex

variable {E : Type _} {τ σ : Finset ℕ}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {p : Constrained_OptimizationProblem E τ σ}

lemma concaveOn_sum {α : Type*} [AddCommMonoid α] [SMul ℝ α]
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {t : s → α → ℝ} {d : Set α}
    (h : ∀ i : s, ConcaveOn ℝ d (t i)) (hd : Convex ℝ d) :
    ConcaveOn ℝ d (fun x => ∑ i : s, t i x) := by
  constructor
  · exact hd
  intro x hx y hy a b ha hb hab
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  simp
  apply Finset.sum_le_sum
  intro i _
  obtain h1 := (h i).2 hx hy ha hb hab
  simpa

theorem convex_problem_convex_Lagrange {p : Constrained_OptimizationProblem E τ σ}
    (h : ConvexOn ℝ univ p.objective) (hτ : τ = ∅) (x : E)
    (hi : ∀ i ∈ σ, ConcaveOn ℝ univ (inequality_constraints p i))
    (lambda1 : τ → ℝ) (lambda2 : σ → ℝ)
    (hKKT : KKT_point p x lambda1 lambda2) :
    ConvexOn ℝ univ (fun m ↦ p.Lagrange_function m lambda1 lambda2) := by
  subst hτ
  unfold Lagrange_function
  apply ConvexOn.sub
  · apply ConvexOn.sub h
    simpa using (concaveOn_const (𝕜 := ℝ) (s := (univ : Set E)) (0 : ℝ) convex_univ)
  apply concaveOn_sum _ convex_univ
  intro i
  apply ConcaveOn.smul
  · unfold KKT_point at hKKT
    exact hKKT.2.2.1 i
  exact hi i i.2

omit [CompleteSpace E] in
theorem diff_problem_diff_Lagrange {p : Constrained_OptimizationProblem E τ σ}
    (hτ : τ = ∅) (x : E)
    (hf : DifferentiableAt ℝ p.objective x)
    (conti : ∀ i ∈ σ, DifferentiableAt ℝ (inequality_constraints p i) x)
    (lambda1 : τ → ℝ) (lambda2 : σ → ℝ) :
    DifferentiableAt ℝ (fun m ↦ p.Lagrange_function m lambda1 lambda2) x := by
  apply DifferentiableAt.sub
  · apply DifferentiableAt.sub
    · exact hf
    simp [hτ]
  convert (DifferentiableAt.sum (u := (Finset.univ : Finset σ))
      (A := fun j m => lambda2 j * p.inequality_constraints (↑j) m)
      (by intro i _; exact DifferentiableAt.const_mul (conti i i.2) (lambda2 i))) using 1
  ext m; simp [Finset.sum_apply]

theorem KKT_multipliers_objective_eq_Lagrangian {p : Constrained_OptimizationProblem E τ σ}
    (x : E) (lambda1 : τ → ℝ) (lambda2 : σ → ℝ)
    (hKKT : KKT_point p x lambda1 lambda2) :
    p.objective x = p.Lagrange_function x lambda1 lambda2 := by
  unfold Lagrange_function
  unfold KKT_point at hKKT
  have h1 : ∑ i : τ, lambda1 i * p.equality_constraints i x = 0 := by
    obtain hx := hKKT.2.1
    unfold FeasSet FeasPoint at hx
    simp at hx
    apply Finset.sum_eq_zero
    intro i _
    rw [hx.1.2 i i.2, mul_zero]
  have h2 : ∑ j : σ, lambda2 j * p.inequality_constraints j x = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hKKT.2.2.2]
  rw [h1, h2, sub_zero, sub_zero]

theorem KKT_multipliers_inf_value_aux {p : Constrained_OptimizationProblem E τ σ}
    (h : ConvexOn ℝ univ p.objective) (hτ : τ = ∅) (x : E)
    (hf : DifferentiableAt ℝ p.objective x)
    (hi : ∀ i ∈ σ, ConcaveOn ℝ univ (inequality_constraints p i))
    (conti : ∀ i ∈ σ, DifferentiableAt ℝ (inequality_constraints p i) x)
    (lambda1 : τ → ℝ) (lambda2 : σ → ℝ) (hg : p.Global_Minimum x)
    (hKKT : KKT_point p x lambda1 lambda2) :
    (⨅ x ∈ p.domain, (p.Lagrange_function x lambda1 lambda2).toEReal)
      = ((p.Lagrange_function x lambda1 lambda2).toEReal) := by
  obtain hg1 := hg.1
  unfold FeasPoint at hg1
  unfold KKT_point at hKKT
  have h1 : ∀ x1 ∈ p.domain, p.Lagrange_function x1 lambda1 lambda2 ≥
      p.Lagrange_function x lambda1 lambda2 := by
    intro x1 _
    have : HasGradientAt (fun m ↦ p.Lagrange_function m lambda1 lambda2)
        (gradient (fun m ↦ p.Lagrange_function m lambda1 lambda2) x) x := by
      apply DifferentiableAt.hasGradientAt
      exact diff_problem_diff_Lagrange hτ x hf conti lambda1 lambda2
    obtain h := Convex_first_order_condition' this
      (convex_problem_convex_Lagrange h hτ x hi lambda1 lambda2 hKKT) (x := x)
    rw [hKKT.1] at h; simp at h
    exact h x1
  refine iInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
  · intro x1; simp; intro hx1
    exact h1 x1 hx1
  intro w hw; use x;
  simp [hg1.1]; exact hw

theorem KKT_multipliers_inf_value {p : Constrained_OptimizationProblem E τ σ}
    (h : ConvexOn ℝ univ p.objective) (hτ : τ = ∅) (x : E)
    (hf : DifferentiableAt ℝ p.objective x)
    (hi : ∀ i ∈ σ, ConcaveOn ℝ univ (inequality_constraints p i))
    (conti : ∀ i ∈ σ, DifferentiableAt ℝ (inequality_constraints p i) x)
    (lambda1 : τ → ℝ) (lambda2 : σ → ℝ) (hg : p.Global_Minimum x)
    (hKKT : KKT_point p x lambda1 lambda2) :
    (p.dual_problem).objective (lambda1, lambda2) = p.inf_value := by
  rw [← global_minimum_objective_infimum hg]
  simp; unfold dual_problem dual_objective; simp
  obtain hg1 := hg.1
  unfold FeasPoint at hg1
  unfold KKT_point at hKKT
  rw [KKT_multipliers_objective_eq_Lagrangian x lambda1 lambda2 hKKT]
  obtain hh := KKT_multipliers_inf_value_aux h hτ x hf hi conti lambda1 lambda2 hg hKKT
  exact congrArg EReal.toReal hh

theorem KKT_multipliers_dual_feasible {p : Constrained_OptimizationProblem E τ σ}
    (h : ConvexOn ℝ univ p.objective) (hτ : τ = ∅) (x : E)
    (hf : DifferentiableAt ℝ p.objective x)
    (hi : ∀ i ∈ σ, ConcaveOn ℝ univ (inequality_constraints p i))
    (conti : ∀ i ∈ σ, DifferentiableAt ℝ (inequality_constraints p i) x)
    (lambda1 : τ → ℝ) (lambda2 : σ → ℝ) (hg : p.Global_Minimum x)
    (hKKT : KKT_point p x lambda1 lambda2) :
    (lambda1, lambda2) ∈ (p.dual_problem).FeasSet := by
  unfold FeasSet FeasPoint
  unfold KKT_point at hKKT
  simp; constructor
  · unfold dual_problem; simp
    unfold dual_objective
    rw [KKT_multipliers_inf_value_aux h hτ x hf hi conti lambda1 lambda2 hg hKKT]; simp
  intro j hj
  unfold dual_problem; simp [hj]
  exact hKKT.2.2.1 ⟨j, hj⟩

theorem optimal_multipliers_solution_dual_problem {p : Constrained_OptimizationProblem E τ σ}
    (h : ConvexOn ℝ univ p.objective) (hτ : τ = ∅) (x : E)
    (hf : DifferentiableAt ℝ p.objective x)
    (hi : ∀ i ∈ σ, ConcaveOn ℝ univ (inequality_constraints p i))
    (conti : ∀ i ∈ σ, DifferentiableAt ℝ (inequality_constraints p i) x)
    (lambda1 : τ → ℝ) (lambda2 : σ → ℝ) (hg : p.Global_Minimum x)
    (hKKT : KKT_point p x lambda1 lambda2) :
    (p.dual_problem).Global_Maximum (lambda1, lambda2) := by
  apply objective_maximum_global_maximum
  · obtain h1 := KKT_multipliers_inf_value h hτ x hf hi conti lambda1 lambda2 hg hKKT
    obtain h2 := weak_duality' (p := p)
    have : (p.dual_problem).objective (lambda1, lambda2) ≤ (p.dual_problem).sup_value := by
      apply objective_le_sup _ (KKT_multipliers_dual_feasible h hτ x hf hi conti lambda1 lambda2 hg hKKT)
    rw [← h1] at h2
    symm; apply antisymm h2 this
  exact KKT_multipliers_dual_feasible h hτ x hf hi conti lambda1 lambda2 hg hKKT


end Convex

end Duality
