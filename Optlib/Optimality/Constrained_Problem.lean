/-
Copyright (c) 2024 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Shengyang Xu, Yuxuan Wu
-/
import Mathlib
import Optlib.Differential.Calculation
import Optlib.Convex.Farkas
import Optlib.Differential.Lemmas

/-!
# Constrained_Problem

## Main results

This file contains the following parts of constrained optimization problem.
* the definition of a constrained optimization prblem
* the definition of a local Minimum, global Minimum, strict local Minimum
* the definition of the active set
* the definition of the linearized feasible directions
* the proof of the creteria of the geometry optimality condition
* the proof of LICQ which states under suitable conditions the positive tangent cone
  equals the linearized feasible directions
* the proof of KKT conditions under LICQ
* the proof of KKT conditions under linear constraint qualification
-/

open InnerProductSpace Set BigOperators
set_option linter.unusedVariables false
set_option maxHeartbeats 500000

noncomputable section

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {τ σ : Finset ℕ}

/-
  the definition of an unconstrained optimization problem.
  The objective function is a function from a Hilbert space to ℝ.
  The equality constraints are a set of functions from a Hilbert space to ℝ.
  The inequality constraints are a set of functions from a Hilbert space to ℝ.
-/
structure Constrained_OptimizationProblem (E : Type _) (τ σ : Finset ℕ) where
  (domain : Set E)
  (equality_constraints : (i : ℕ) → E → ℝ)
  (inequality_constraints : (j : ℕ) → E → ℝ)
  (eq_ine_not_intersect : τ ∩ σ = ∅)
  (objective : E → ℝ)

namespace Constrained_OptimizationProblem

variable {p : Constrained_OptimizationProblem E τ σ} {x : E}

open Topology InnerProductSpace Set Filter

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
def Global_Minimum (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsMinOn p.objective p.FeasSet point

/-
  A point x₁ ∈ Ω is a global maximizer if f x₁ ≥ f x for all x ∈ Ω.
-/
def Global_Maximum (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsMaxOn p.objective p.FeasSet point

/-
  A point x₁ ∈ Ω is a local minimizer if there is a neighborhood B of x₁
  such that f x₁ ≤ f x for all x ∈ B ∩ Ω.
-/
def Local_Minimum (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsLocalMinOn p.objective p.FeasSet point

/-
  A point x₁ ∈ Ω is a local maximizer if there is a neighborhood B of x₁
  such that f x₁ ≥ f x for all x ∈ B ∩ Ω.
-/
def Local_Maximum (point : E) : Prop :=
  (p.FeasPoint point) ∧ IsLocalMaxOn p.objective p.FeasSet point

/-
  A vector x∗ is a strict local solution (also called a strong local solution) if x∗ ∈ Ω and there
  is a neighborhood B of x∗ such that f (x) > f (x∗) for all x ∈ B ∩ Ω with x ≠ x∗.
-/
def Strict_Local_Minimum (point : E) : Prop :=
  (p.FeasPoint point) ∧ (∃ ε > 0, ∀ y, p.FeasPoint y → y ∈ Metric.ball point ε → y ≠ point
  → p.objective point > p.objective y)

/-
  The active set A(x) at any feasible x consists of the equality constraint indices from E
  together with the indices of the inequality constraints i for which c_i(x) = 0;
-/
def active_set (point : E) : Finset ℕ :=
  τ ∪ σ.filter fun i : ℕ ↦ p.inequality_constraints i point = (0 : ℝ)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma equality_constraint_active_set (point : E) : τ ⊆ p.active_set point :=
  fun i itau ↦ Finset.mem_union_left _ itau
/-
  Given a feasible point x and the active constraint set A(x) of Definition 12.1, the set of
  linearized feasible directions is defined as
-/
def linearized_feasible_directions (point : E) : Set E :=
  {v | (∀ i ∈ τ, ⟪gradient (p.equality_constraints i) point, v⟫_ℝ = (0 : ℝ))
    ∧ ∀ j ∈ σ ∩ (p.active_set point), ⟪gradient (p.inequality_constraints j) point, v⟫_ℝ ≥ (0 : ℝ)}

/-
  Given the point x and the active set A(x), we say that the linear
  independence constraint qualification (LICQ) holds if the set of active constraint gradients
  {∇ci(x), i ∈ A(x)} is linearly independent.
-/
def LICQ (point : E) : Prop :=
  LinearIndependent ℝ (fun i : p.active_set point ↦
    if i.1 ∈ τ then gradient (p.equality_constraints i.1) point else gradient (p.inequality_constraints i.1) point)

/-
  Lagrangian function for the general problem
-/
def Lagrange_function :=
  fun (x : E) (lambda1 : τ → ℝ) (lambda2 : σ → ℝ) ↦ (p.objective x)
    - (Finset.sum Finset.univ fun i ↦ (lambda1 i) * p.equality_constraints i x)
    - (Finset.sum Finset.univ fun j ↦ (lambda2 j) * p.inequality_constraints j x)

section linear

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsLinear (f : E → ℝ) : Prop := ∃ a, ∃ b, f = fun x ↦ ⟪x, a⟫_ℝ + b

lemma IsLinear_iff (f : E → ℝ) : IsLinear f ↔ ∃ a b, f = fun x ↦ ⟪x, a⟫_ℝ + b := by rfl

lemma IsLinear_iff' (f : E → ℝ) :
    IsLinear f ↔ ∃ a b, f = fun x ↦ ⟪a, x⟫_ℝ + b := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by
      funext x; simp [real_inner_comm]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by
      funext x; simp [real_inner_comm]⟩

end linear

/-
  Linear Constraint Qualification
-/
def LinearCQ (point : E) : Prop :=
  (∀ i ∈ (p.active_set point ∩ τ), IsLinear (p.equality_constraints i)) ∧
  ∀ i ∈ (p.active_set point ∩ σ), IsLinear (p.inequality_constraints i)

end Constrained_OptimizationProblem

end

section Constrained_OptimizationProblem_property_general

open Constrained_OptimizationProblem Topology InnerProductSpace Set Filter

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {τ σ : Finset ℕ} {p : Constrained_OptimizationProblem E τ σ} {x : E} {n : ℕ}

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

lemma posTangentCone_localmin_inner_pos {f : E → ℝ} {loc : E} (hl : IsLocalMinOn f p.FeasSet loc)
    (hf : DifferentiableAt ℝ f loc) :
    ∀ v ∈ posTangentConeAt p.FeasSet loc, ⟪gradient f loc, v⟫_ℝ ≥ (0 : ℝ) := by
  intro v vt; rw [posTangentConeAt] at vt; simp at vt
  rcases vt with ⟨c, d, ⟨a, ha⟩, ⟨vt1, vt2⟩⟩
  by_contra proneg; push_neg at proneg
  rw [IsLocalMinOn, IsMinFilter, eventually_iff_exists_mem] at hl
  rcases hl with ⟨s, ⟨hs, hs2⟩⟩
  rw [nhdsWithin] at hs
  rcases Metric.mem_nhdsWithin_iff.mp hs with ⟨ε, ⟨εpos, εball⟩⟩
  let s1 := Metric.ball loc ε ∩ p.FeasSet
  have hmin : ∀ y ∈ s1, f loc ≤ f y := fun y yin => hs2 y (εball yin)
  let z := fun n ↦ loc + d n
  have hzd : ∀ n, d n = z n - loc := fun _ => eq_sub_of_add_eq' rfl
  rw [real_inner_comm] at proneg
  have hcp : ∀ᶠ (n : ℕ) in atTop, c n > 0 := by
    rw [Filter.tendsto_atTop] at vt1
    specialize vt1 (1 : ℝ)
    apply Filter.Eventually.mp vt1
    apply Filter.Eventually.of_forall
    intro n hn; linarith
  have hz3 : ∀ᶠ (n : ℕ) in atTop, (1 / c n) > 0 := by
    apply Filter.Eventually.mp hcp
    apply Filter.Eventually.of_forall
    intro n hn; exact one_div_pos.mpr hn
  have hzt : Tendsto z atTop (𝓝 loc) := by
    have : Tendsto d atTop (𝓝 0) := by
      rw [Filter.tendsto_atTop] at vt1
      rw [Filter.tendsto_atTop'] at vt2
      rw [Metric.tendsto_atTop']; intro ε hε
      have : Metric.ball v ε ∈ 𝓝 v := by exact Metric.ball_mem_nhds _ hε
      specialize vt2 (Metric.ball v ε) this
      rcases vt2 with ⟨a, ha⟩
      specialize vt1 (2 * (‖v‖ + ε) / ε); simp at vt1
      rcases vt1 with ⟨a1, ha1⟩
      let n1 := max a a1
      use n1; intro n hn
      specialize ha n (ge_trans (Nat.le_of_lt hn) (a.le_max_left a1))
      specialize ha1 n (ge_trans (Nat.le_of_lt hn) (a.le_max_right a1))
      have : ‖d n‖ < ε := by
        have : ‖c n • d n‖ ≤ ‖v‖ + ε := by
          rw [Metric.mem_ball, dist_eq_norm] at ha;
          have t1 : ‖c n • d n - v‖ ≥ ‖c n • d n‖ - ‖v‖ := norm_sub_norm_le _ v
          linarith
        have cpos : c n > 0 := by
          apply lt_of_le_of_lt'
          · show c n ≥ 2 * (‖v‖ + ε) / ε
            exact ha1
          · positivity
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos cpos] at this;
        calc _ ≤ (‖v‖ + ε) / c n := (le_div_iff₀' cpos).mpr this
             _ ≤ (‖v‖ + ε) / (2 * (‖v‖ + ε) / ε) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) ha1
             _ = ε / 2 := by field_simp [εpos]
             _ < ε := by linarith
      simp; exact this
    have h1 : z = (fun n ↦ d n + loc) := by
      funext n; rw [hzd n, sub_add, sub_self, sub_zero]
    rw [h1]
    convert Filter.Tendsto.add_const loc this
    rw [zero_add]
  have hz : (fun n ↦ f (z n) - f loc - ⟪z n - loc, gradient f loc⟫_ℝ)
      =o[atTop] (fun n ↦ z n - loc) := by
    have : HasGradientAt f (gradient f loc) loc := hf.hasGradientAt
    rw [hasGradientAt_iff_isLittleO] at this
    have heq : (fun n ↦ f (z n) - f loc - ⟪z n - loc, gradient f loc⟫_ℝ) =
        (fun n ↦ f (z n) - f loc - ⟪gradient f loc, z n - loc⟫_ℝ) := by
      ext n; rw [real_inner_comm]
    rw [heq]
    apply Asymptotics.IsLittleO.comp_tendsto this hzt
  have hz1 : (fun n ↦ f (z n) - f loc - (1 / c n) * ⟪v, gradient f loc⟫_ℝ)
      =o[atTop] (fun n ↦ 1 / c n) := by
    have t1: (fun n ↦ z n - loc) =O[atTop] (fun n ↦ 1 / c n) := by
      rw [Asymptotics.isBigO_iff]
      rw [Filter.tendsto_atTop] at vt1
      rw [Filter.tendsto_atTop'] at vt2
      have : Metric.ball v 1 ∈ 𝓝 v := by exact Metric.ball_mem_nhds _ (by norm_num)
      specialize vt2 (Metric.ball v 1) this
      rcases vt2 with ⟨a, ha⟩
      specialize vt1 (2 * (‖v‖ + ε) / ε); simp at vt1
      rcases vt1 with ⟨a1, ha1⟩
      let n1 := max a a1
      use (‖v‖ + 1 : ℝ); simp; use n1; intro n hn
      specialize ha n (ge_trans hn (a.le_max_left a1))
      specialize ha1 n (ge_trans hn (a.le_max_right a1))
      have cpos : c n > 0 := by
          apply lt_of_le_of_lt'
          · show c n ≥ 2 * (‖v‖ + ε) / ε
            exact ha1
          · positivity
      rw [abs_of_pos]
      have : ‖d n‖ ≤ (‖v‖ + 1) * (c n)⁻¹ := by
        have : ‖c n • d n‖ ≤ ‖v‖ + 1 := by
          rw [Metric.mem_ball, dist_eq_norm] at ha;
          have t1 : ‖c n • d n - v‖ ≥ ‖c n • d n‖ - ‖v‖ := norm_sub_norm_le _ v
          linarith
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos cpos] at this;
        field_simp; exact (le_div_iff₀' cpos).mpr this
      rw [← hzd n]; exact this; apply cpos
    have t2 : (fun n ↦ f (z n) - f loc - ⟪z n - loc, gradient f loc⟫_ℝ)
        =o[atTop] (fun n ↦ 1 / c n) := Asymptotics.IsLittleO.trans_isBigO hz t1
    have t3 : (fun n ↦ (⟪z n - loc - (1 / c n) • v, gradient f loc⟫_ℝ : ℝ))
        =o[atTop] (fun n ↦ 1 / c n) := by
      have t5: (fun n ↦ z n - loc - (1 / c n) • v) =o[atTop] (fun n ↦ 1 / c n) := by
        rw [← Asymptotics.isLittleO_norm_norm]
        apply (Asymptotics.isLittleO_iff_tendsto' _).mpr
        · have : (fun x ↦ ‖z x - loc - (1 / c x) • v‖ / ‖1 / c x‖)
              =ᶠ[atTop] (fun x ↦ ‖c x • (z x - loc) - v‖) := by
            simp; rw [Filter.EventuallyEq]
            apply Filter.Eventually.mp hcp
            apply Filter.Eventually.of_forall
            intro n hcn1; rw [mul_comm, ← Real.norm_eq_abs, ← norm_smul]
            congr; field_simp; rw [smul_sub, smul_smul]; field_simp; ring_nf; simp
          rw [Filter.tendsto_congr' this];
          have : Tendsto (fun (n : ℕ) => c n • d n - v) atTop (𝓝 (v - v)) := by
            apply Filter.Tendsto.sub vt2 tendsto_const_nhds
          apply Filter.Tendsto.norm at this
          simp at this; convert this; simp [hzd]
        · apply Filter.Eventually.mp hcp
          apply Filter.Eventually.of_forall
          intro n hcn1 hcn2
          exfalso; simp at hcn2; linarith
      rw [Asymptotics.isLittleO_iff]; intro c1 hc1
      rw [Asymptotics.isLittleO_iff] at t5;
      have pos1 : ‖gradient f loc‖ ≠ (0 : ℝ) := by
        by_contra hhh; simp at hhh
        have : ⟪v, gradient f loc⟫_ℝ = (0 : ℝ) := by rw [hhh, inner_zero_right]
        linarith
      have pos2 : ‖gradient f loc‖ > (0 : ℝ) := by positivity
      have : c1 / ‖gradient f loc‖ > (0 : ℝ) := by positivity
      specialize t5 this
      apply Filter.Eventually.mp t5
      apply Filter.Eventually.of_forall
      intro n hn;
      calc _ ≤ ‖z n - loc - (1 / c n) • v‖ * ‖gradient f loc‖ := norm_inner_le_norm _ _
           _ ≤ c1 / ‖gradient f loc‖ * ‖1 / c n‖ * ‖gradient f loc‖ :=
              (mul_le_mul_iff_left₀ pos2).mpr hn
           _ ≤ c1 * ‖1 / c n‖ := by ring_nf; field_simp [pos1]; simp
    have t4 :  (fun n => f (z n) - f loc - (1 / c n) * ⟪v, gradient f loc⟫_ℝ) =
        (fun n ↦ f (z n) - f loc - ⟪z n - loc, gradient f loc⟫_ℝ) +
        (fun n ↦ (⟪z n - loc - (1 / c n) • v, gradient f loc⟫_ℝ : ℝ)) := by
      ext n; dsimp; simp [inner_sub_left, inner_smul_left]
    rw [t4]; apply Asymptotics.IsLittleO.add t2 t3
  have hz2 : ∀ᶠ (n : ℕ) in atTop, f (z n) ≤ f loc + (1 / 2) *
      (1 / c n) * ⟪v, gradient f loc⟫_ℝ := by
    rw [Asymptotics.isLittleO_iff] at hz1
    have : (- (1 / 2 : ℝ) * ⟪v, gradient f loc⟫_ℝ) > 0 := by
      simp; rw [mul_comm]; apply mul_neg_of_neg_of_pos proneg (by norm_num)
    specialize hz1 this
    apply Filter.Eventually.mp hz1
    apply Filter.Eventually.mp hz3
    apply Filter.Eventually.of_forall
    intro n hn hn1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le, abs_of_pos hn] at hn1
    rcases hn1 with ⟨_, hn1⟩
    rw [sub_le_iff_le_add, sub_le_iff_le_add] at hn1
    have : -(1 / 2) * ⟪v, gradient f loc⟫_ℝ * (1 / c n) + 1 / c n * ⟪v,
        gradient f loc⟫_ℝ + f loc = f loc + 1 / 2 * (1 / c n) * ⟪v, gradient f loc⟫_ℝ := by
      ring_nf
    rw [this] at hn1; exact hn1
  have hz4 : ∀ᶠ (n : ℕ) in atTop, f (z n) < f loc := by
    apply Filter.Eventually.mp hz2
    apply Filter.Eventually.mp hz3
    apply Filter.Eventually.of_forall
    intro n hn1 hn2
    have : 1 / 2 * (1 / c n) * (⟪v, gradient f loc⟫_ℝ) < 0 := by
      apply mul_neg_of_pos_of_neg
      · apply Right.mul_pos; simp; exact hn1
      · exact proneg
    linarith
  have hz5 : ∀ᶠ (n : ℕ) in atTop, z n ∈ s1 := by
    simp only [s1, mem_inter_iff, Metric.mem_ball]
    apply Filter.Eventually.and
    · rw [Filter.tendsto_atTop'] at hzt
      simp;
      have : Metric.ball loc ε ∈ 𝓝 loc := by exact Metric.ball_mem_nhds loc εpos
      rcases hzt (Metric.ball loc ε) this with ⟨a, ha⟩
      use a; intro b hb; specialize ha b (by linarith [hb])
      simp at ha; exact ha
    · simp; use a
  simp at hz5 hz4
  rcases hz5 with ⟨n, hn1⟩; rcases hz4 with ⟨m, hm1⟩
  let M := max n m
  have hh2 : f (z M) < f loc := hm1 M (le_max_right n m)
  have hh1 : z M ∈ s1 := by simp [s1]; apply hn1 M (le_max_left n m)
  have hh3 : f loc ≤ f (z M) := hmin (z M) hh1
  linarith

/-
  Linearized feasible directions contain tagent cone
  Numerical Optimization, Nocedal & Wright, Lemma 12.2
-/
theorem linearized_feasible_directions_contain_tagent_cone (xf : x ∈ p.FeasSet)
    (diffable : ∀ i ∈ τ, DifferentiableAt ℝ (equality_constraints p i) x)
    (diffable₂ : ∀ i ∈ σ, DifferentiableAt ℝ (inequality_constraints p i) x) :
    posTangentConeAt p.FeasSet x ⊆ p.linearized_feasible_directions x := by
  intro v hv
  rw [linearized_feasible_directions]
  simp; constructor
  have imin : ∀ i ∈ τ, IsLocalMinOn (equality_constraints p i) p.FeasSet x := by
    intro i itau
    rw [IsLocalMinOn, IsMinFilter, Filter.eventually_iff_exists_mem]
    use p.FeasSet; constructor
    . use univ; constructor
      simp; use p.FeasSet; constructor
      simp; exact Eq.symm (univ_inter FeasSet)
    . intro y yf
      rw [FeasSet] at yf xf
      rw [(yf.2.1 i itau), (xf.2.1 i itau)]
  have negimin : ∀ i ∈ τ, IsLocalMinOn (-equality_constraints p i) p.FeasSet x := by
    intro i itau
    rw [IsLocalMinOn, IsMinFilter, Filter.eventually_iff_exists_mem]
    use p.FeasSet; constructor
    . use univ; constructor
      simp; use p.FeasSet; constructor
      simp; exact Eq.symm (univ_inter FeasSet)
    . intro y yf; simp
      rw [FeasSet] at yf xf
      rw [(yf.2.1 i itau), (xf.2.1 i itau)]
  . intro i itau
    apply ge_antisymm
    . apply posTangentCone_localmin_inner_pos (imin i itau) (diffable i itau) v hv
    . have a₁ : ∀ i ∈ τ, DifferentiableAt ℝ (-(p.equality_constraints i)) x :=
        fun i itau ↦ DifferentiableAt.neg (diffable i itau)
      have a₂ : - gradient (p.equality_constraints i) x =
          gradient (-(p.equality_constraints i)) x := by
        symm
        apply HasGradientAt.gradient
        apply HasGradientAt.neg
        exact DifferentiableAt.hasGradientAt (diffable i itau)
      have hpos :
          0 ≤ ⟪gradient (-(p.equality_constraints i)) x, v⟫_ℝ :=
        posTangentCone_localmin_inner_pos (negimin i itau) (a₁ i itau) v hv
      have hpos' : 0 ≤ -⟪gradient (p.equality_constraints i) x, v⟫_ℝ := by
        have : 0 ≤ ⟪- gradient (p.equality_constraints i) x, v⟫_ℝ := by
          simpa [a₂] using hpos
        simpa [inner_neg_left] using this
      exact (neg_nonneg).1 hpos'
  . intro j hj jact
    rw [active_set] at jact; simp at jact
    rcases jact with jtau | jsigma
    . have := p.eq_ine_not_intersect
      rw [Finset.ext_iff] at this
      simp at this
      have jns : j ∉ σ := by apply this j jtau
      tauto
    . rcases jsigma with ⟨js, ineq⟩
      have jmin : ∀ i ∈ σ , (inequality_constraints p i x = 0) →
          IsLocalMinOn (inequality_constraints p i) p.FeasSet x := by
        intro i is inezero
        rw [IsLocalMinOn, IsMinFilter, Filter.eventually_iff_exists_mem]
        use p.FeasSet; constructor
        . use univ; constructor
          simp; use p.FeasSet; constructor
          simp; exact Eq.symm (univ_inter FeasSet)
        . intro y yf
          rw [FeasSet] at yf xf
          rw [inezero]
          apply yf.2.2 i is
      apply posTangentCone_localmin_inner_pos (jmin j js ineq) (diffable₂ j js) v hv

/-
  If x∗ is a local solution of the constrained optimization problem,
  then we have ∇ f (x∗) ^ T d ≥ 0, for all d ∈ T_Ω (x∗).
  Numerical Optimization, Nocedal & Wright, Theorem 12.3
-/
theorem local_Minimum_TangentCone (loc : E) (hl : p.Local_Minimum loc)
    (hf : Differentiable ℝ p.objective) :
    ∀ v ∈ posTangentConeAt p.FeasSet loc, ⟪gradient p.objective loc, v⟫_ℝ ≥ (0 : ℝ) :=
  fun v vt ↦ posTangentCone_localmin_inner_pos hl.2 (hf loc) v vt

theorem local_Minimum_TangentCone' (loc : E) (hl : p.Local_Minimum loc)
    (hf : Differentiable ℝ p.objective) :
    posTangentConeAt p.FeasSet loc ∩ {d | ⟪gradient p.objective loc, d⟫_ℝ < (0 : ℝ)} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro d ⟨hd1, hd2⟩
  simp at hd2
  obtain hd1 := local_Minimum_TangentCone loc hl hf d hd1
  linarith

lemma contdiff_equiv {x : E} (c : E → ℝ) (hc : ContDiffAt ℝ (1 : ℕ) c x) :
    ∃ (c' : E → E), (∀ᶠ y in 𝓝 x, HasGradientAt c (c' y) y) ∧ ContinuousAt c' x := by
  have aux := @contDiffAt_succ_iff_hasFDerivAt ℝ _ _ _ _ _ _ _ c x 0
  simp at aux; simp at hc; rw [aux] at hc
  rcases hc with ⟨f', ⟨hf1, hf2⟩⟩
  let g := fun z ↦ (toDual ℝ E).symm (f' z)
  use g; constructor
  · rw [Filter.eventually_iff_exists_mem]; rcases hf1 with ⟨u, ⟨hu1, hu2⟩⟩
    use u; constructor; exact hu1
    intro x hu; specialize hu2 x hu
    simp [g]; exact hasFDerivAt_iff_hasGradientAt.mp hu2
  simp [g];
  have hf2 := ContDiffAt.continuousAt hf2
  apply ContinuousAt.comp
  · exact LinearIsometryEquiv.continuousAt (toDual ℝ E).symm
  assumption

lemma diffable_of_hasgradient_nhds {x : E} {μ : Finset ℕ}
    {c : (i : ℕ) → E → ℝ} (gradci : ∀ i ∈ μ, ContDiffAt ℝ 1 (c i) x) :
    ∀ i ∈ μ, DifferentiableAt ℝ (c i) x := by
  intro i iin; specialize gradci i iin
  rcases (contdiff_equiv (c i) gradci) with ⟨c', ⟨gradci, _⟩⟩
  rw [eventually_iff, Metric.mem_nhds_iff] at gradci
  rcases gradci with ⟨ε, εpos, hasgrad⟩
  have : x ∈ Metric.ball x ε := by simp [εpos]
  obtain hx := Set.mem_of_subset_of_mem hasgrad this; simp at hx
  apply HasGradientAt.differentiableAt hx

lemma LICQ_inactive_nhds (x : E) (xf : x ∈ p.FeasSet)
    (gradci : ∀ i ∈ σ, ContDiffAt ℝ 1 (inequality_constraints p i) x) :
  ∃ ε > 0, ∀ i ∈ σ \ (p.active_set x), ∀ z ∈ Metric.ball x ε, 0 < p.inequality_constraints i z := by
  have diffable : ∀ i ∈ σ, DifferentiableAt ℝ (inequality_constraints p i) x :=
    diffable_of_hasgradient_nhds gradci
  have inactive : ∀ i ∈ σ \ (p.active_set x), 0 < p.inequality_constraints i x := by
    intro i iin; simp at iin
    simp [FeasSet, FeasPoint] at xf
    obtain nneg := xf.2.2 i iin.1
    obtain inin := iin.2; simp [active_set] at inin
    obtain nzero := inin.2; simp [iin] at nzero
    apply lt_of_le_of_ne nneg; symm; simp [nzero]
  have inactive_ε : ∀ i ∈ σ \ (p.active_set x), ∀ᶠ (z : E) in 𝓝 x,
      0 < p.inequality_constraints i z := by
    intro i iin; specialize inactive i iin; simp at iin; specialize diffable i iin.1
    rw [eventually_iff, Metric.mem_nhds_iff]
    obtain hc := ContinuousAt_Convergence (DifferentiableAt.continuousAt diffable)
    let ε := (p.inequality_constraints i x) / 2
    have εpos : 0 < ε := by simp [ε]; linarith [inactive]
    obtain ⟨δ, δpos, hc⟩ := hc ε εpos
    use δ; use δpos
    intro z zin; simp at zin; rw [dist_eq_norm, norm_sub_rev] at zin
    specialize hc z (LT.lt.le zin); simp [ε] at hc
    obtain ieq := sub_le_of_abs_sub_le_left hc
    calc
      0 < p.inequality_constraints i x - p.inequality_constraints i x / 2 := by linarith [inactive]
      _ ≤ p.inequality_constraints i z := ieq
  rw [← Finset.eventually_all, eventually_iff, Metric.mem_nhds_iff] at inactive_ε
  rcases inactive_ε with ⟨ε, εpos, sub⟩
  use ε; use εpos; intro i iin z zin; simp at iin
  obtain hz := Set.mem_of_subset_of_mem sub zin; simp at hz
  specialize hz i; simp [iin] at hz; exact hz

lemma contdiff_hasgradientat (x : E) (c : E → ℝ) (hc : ContDiffAt ℝ 1 c x) :
    ∀ᶠ y in 𝓝 x, HasGradientAt c (gradient c y) y := by
  rcases contdiff_equiv c hc with ⟨c', ⟨hc1, _⟩⟩
  apply Filter.Eventually.mono hc1
  intro x hx; obtain hx := HasGradientAt.differentiableAt hx
  exact hx.hasGradientAt

lemma LICQ_nhds_grad (x : E)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ 1 (equality_constraints p i) x)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ 1 (inequality_constraints p i) x) :
    ∀ᶠ y in 𝓝 x,
    (∀ i ∈ τ, HasGradientAt (equality_constraints p i)
      (gradient (equality_constraints p i) y) y) ∧
    (∀ i ∈ σ, HasGradientAt (inequality_constraints p i)
      (gradient (inequality_constraints p i) y) y) := by
  have conte : ∀ i ∈ τ, ∀ᶠ y in 𝓝 x, HasGradientAt (equality_constraints p i)
      (gradient (equality_constraints p i) y) y :=
    fun i hi ↦ contdiff_hasgradientat x (equality_constraints p i) (conte i hi)
  have conti : ∀ i ∈ σ, ∀ᶠ y in 𝓝 x, HasGradientAt (inequality_constraints p i)
      (gradient (inequality_constraints p i) y) y :=
    fun i hi ↦ contdiff_hasgradientat x (inequality_constraints p i) (conti i hi)
  rw [← Finset.eventually_all] at conte; rw [← Finset.eventually_all] at conti
  rw [Filter.eventually_and]; exact ⟨conte, conti⟩

lemma StrictFderivAt_of_FderivAt_of_ContinuousAt
    {x : E} {c : E → ℝ} (hcd : ContDiffAt ℝ (1 : ℕ) c x) : (fun p_1 : E × E ↦
    c p_1.1 - c p_1.2 - ⟪gradient c x, p_1.1 - p_1.2⟫_ℝ) =o[𝓝 (x, x)] fun p ↦ p.1 - p.2 := by
  rcases (contdiff_equiv c hcd) with ⟨c', ⟨hgrad, hcont⟩⟩
  refine Asymptotics.isLittleO_iff.mpr fun μ hμ => Metric.eventually_nhds_iff_ball.mpr ?_
  rcases Metric.mem_nhds_iff.mp (inter_mem hgrad (hcont <| Metric.ball_mem_nhds _ hμ))
    with ⟨ε, ε0, hε⟩
  refine ⟨ε, ε0, ?_⟩
  rintro ⟨a, b⟩ h
  rw [← ball_prod_same, prodMk_mem_set_prod_eq] at h
  have hf' : ∀ x' ∈ Metric.ball x ε, ‖c' x' - c' x‖ ≤ μ := fun x' H' => by
    rw [← dist_eq_norm]
    exact le_of_lt (hε H').2
  obtain h1 := convex_ball x ε
  have h2 : ∀ y ∈ Metric.ball x ε, HasGradientAt c (c' y) y := fun _ yin ↦ (hε yin).1
  obtain ⟨α, αin, eq⟩ := lagrange h1 h2 b h.2 a h.1
  obtain mem := Convex.add_smul_sub_mem h1 h.2 h.1 (Set.Ioo_subset_Icc_self αin)
  specialize hf' (b + α • (a - b)) mem
  rw [← eq, ← inner_sub_left];
  have : gradient c x = c' x := by
    refine HasGradientAt.gradient ?h; exact h2 x (Metric.mem_ball_self ε0)
  rw [this]
  calc
    _ ≤ ‖c' (b + α • (a - b)) - c' x‖ * ‖(a, b).1 - (a, b).2‖ := by apply norm_inner_le_norm
    _ ≤ μ * ‖(a, b).1 - (a, b).2‖ := by apply mul_le_mul_of_nonneg_right hf' (norm_nonneg (a - b))

omit [CompleteSpace E] in
theorem inactive_constraint_one (x v : E) (hx : x ∈ p.FeasSet)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x)
    (i : ℕ) (hi : i ∈ σ \ (p.active_set x)) : ∃ (t_ : ℝ), t_ > 0 ∧
    (∀ t ∈ Icc 0 t_, 0 < p.inequality_constraints i (x + t • v)) := by
  simp [FeasSet, FeasPoint] at hx; obtain ⟨⟨_, _⟩, ⟨_, h2⟩⟩ := hx
  simp [active_set] at hi
  obtain ⟨h1, ⟨_, h⟩⟩ := hi; specialize h h1; push_neg at h; specialize h2 i h1
  exact continuous_positive_direction (ContDiffAt.continuousAt (conti i h1)) (by positivity) v

lemma exist_forall_forall_exist (P : ℕ → ℝ → Prop) (s : Finset ℕ) (hs : s.Nonempty)
    (h : ∀ i ∈ s, ∃ tm > (0 : ℝ), ∀ t ∈ Icc 0 tm, P i t) :
    ∃ tm > (0 : ℝ), ∀ t ∈ Icc 0 tm, ∀ i ∈ s, P i t := by
  let f := fun i ↦ if hi : i ∈ s then (h i hi).choose else 0
  have fpos : ∀ i ∈ s, ∀ t ∈ Icc 0 (f i), P i t := by
    intro i hi t ht
    simp only [f, hi] at ht
    obtain htt := (h i hi).choose_spec.2
    exact htt t ht
  let s1 := Finset.image f s
  let tm := Finset.min' s1 ((Finset.image_nonempty).mpr hs)
  have po : ∀ y ∈ s1, y > 0 := by
    intro y hy
    simp [s1] at hy; rcases hy with ⟨a, ha1, ha2⟩
    simp only [gt_iff_lt, ha1, ↓reduceDIte, f] at ha2; rw [← ha2]
    exact (h a ha1).choose_spec.1
  have up : ∀ y ∈ s1, tm ≤ y := fun y a ↦ Finset.min'_le s1 y a
  use tm; constructor
  · exact (Finset.lt_min'_iff s1 (Finset.image_nonempty.mpr hs)).mpr po
  intro t ht i hi
  exact (fpos i hi t) ⟨ht.1, Preorder.le_trans t tm _ ht.2 (up _ (Finset.mem_image_of_mem f hi))⟩


omit [CompleteSpace E] in
theorem inactive_constraint (x v : E) (hx : x ∈ p.FeasSet)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x) : ∃ (t_ : ℝ), t_ > 0 ∧
    (∀ t ∈ Icc 0 t_, ∀ i ∈ σ \ (p.active_set x), 0 < p.inequality_constraints i (x + t • v)) := by
  by_cases he1 : σ = ∅
  · use 1; constructor; linarith
    intro _ _ i hi
    exfalso; simp [he1] at hi
  by_cases he2 : σ \ (p.active_set x) = ∅
  · use 1; constructor; linarith
    intro _ _ i hi
    exfalso; simp [he2] at hi
  have : (σ \ (p.active_set x)).Nonempty := Finset.nonempty_iff_ne_empty.mpr he2
  obtain h := inactive_constraint_one x v hx conti
  exact exist_forall_forall_exist _ _ this h

end Constrained_OptimizationProblem_property_general

section Constrained_OptimizationProblem_property_finite_dimensional

open Constrained_OptimizationProblem Topology InnerProductSpace Set Filter Matrix

variable {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
variable {τ σ : Finset ℕ} {p : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin n)) τ σ}
variable {M : Matrix (p.active_set x) (Fin n) ℝ} {v : EuclideanSpace ℝ (Fin n)}

lemma LICQ_mlen (x : EuclideanSpace ℝ (Fin n)) (LIx : p.LICQ x)
    {m : ℕ} (meq : m = (p.active_set x).card) : m ≤ n := by
  let cond := LinearIndependent.fintype_card_le_finrank LIx
  simp at cond; rw [meq]; simp; exact cond

lemma LICQ_Axfullrank (x : EuclideanSpace ℝ (Fin n)) (LIx : p.LICQ x)
    {M : Matrix (p.active_set x) (Fin n) ℝ}
    (eq : M = fun i : (p.active_set x) ↦ if i.1 ∈ τ then gradient (p.equality_constraints i) x
        else gradient (p.inequality_constraints i) x):
    Matrix.rank M = (Fintype.card (p.active_set x)) := by
  apply LE.le.antisymm
  · apply Matrix.rank_le_card_height
  · simp
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card]
    simp; rw [eq]; apply LIx

lemma LICQ_existZ (x : EuclideanSpace ℝ (Fin n)) (LIx : p.LICQ x)
    {m : ℕ} (meq : m = (p.active_set x).card)
    {M : Matrix (p.active_set x) (Fin n) ℝ}
    (eq : M = fun i : (p.active_set x) ↦ if i.1 ∈ τ then gradient (p.equality_constraints i) x
        else gradient (p.inequality_constraints i) x):
    ∃ (Z : Matrix (Fin n) (Fin (n - m)) ℝ), M * Z = 0 ∧ Matrix.rank Z = (n - m) := by
  rw [LICQ] at LIx;
  have mlen : m ≤ n := LICQ_mlen x LIx meq
  have fullrowrank : Matrix.rank M = (Fintype.card (p.active_set x)) := LICQ_Axfullrank x LIx eq
  let map := Matrix.toLin' M
  let eq := LinearMap.finrank_range_add_finrank_ker map
  simp [map] at eq
  have aux : Module.finrank ℝ (LinearMap.range (Matrix.toLin' M)) = m := by
    rw [Matrix.range_toLin', ← Matrix.rank_eq_finrank_span_cols, fullrowrank]; simp [meq]
  rw [aux] at eq
  let kernel := LinearMap.ker (Matrix.toLin' M)
  have dim_ker : Module.finrank ℝ kernel = n - m := by
    simp [kernel]; rw [Nat.sub_eq_of_eq_add]; linarith [eq]
  let base := Module.finBasis ℝ kernel
  rw [dim_ker] at base
  let Z : Matrix (Fin (n - m)) (Fin n) ℝ := fun i ↦ base i
  use Zᵀ
  constructor
  · have colzero : ∀ i : (Fin (n - m)), (Z * Mᵀ) i = 0 := by
      intro i
      rw [Matrix.mul_apply_eq_vecMul, ← Matrix.mulVec_transpose, Matrix.transpose_transpose]
      have zinker : (Z i) ∈ kernel := by simp [Z]
      simp only [kernel] at zinker; rw [LinearMap.mem_ker, Matrix.toLin'] at zinker
      simp at zinker; exact zinker
    rw [← Matrix.transpose_eq_zero]; simp
    ext i j; rw [colzero i]; simp
  · rw [Matrix.rank_transpose]
    apply LE.le.antisymm
    · apply Matrix.rank_le_height
    · simp
      rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card]
      simp; rw [Nat.sub_add_cancel]; apply mlen
      let base_indep := Module.Basis.linearIndependent base
      simp only [Z]
      rw [linearIndependent_iff'']
      intro s g cond sum
      rw [linearIndependent_iff''] at base_indep
      specialize base_indep s g cond; apply base_indep
      let coe := @Subtype.val (Fin n → ℝ) (fun x ↦ x ∈ ↑kernel)
      have coe_zero (x : kernel) : x = 0 ↔ coe x = 0 := by
        constructor
        · intro cond; rw [cond]; simp [coe]
        · intro cond; simp [coe] at cond; exact cond
      rw [coe_zero]; simp only [coe]
      rw [← sum]; simp; rfl

lemma mulVec_eq_toEuclidean {s : Type*} (M : Matrix s (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    M *ᵥ y = (toEuclideanLin M) y := by
  rw [Matrix.toEuclideanLin_apply]; ext j; simp; rfl

lemma inj_iff_full_finrank {s t : Type*} {M : Matrix s t ℝ} [Fintype s] [Fintype t]
    (hn : Fintype.card s = Fintype.card t) :
    M.rank = Fintype.card s ↔ ∀ (v : t → ℝ), M *ᵥ v = 0 → v = 0 := by
  rw [← ker_mulVecLin_eq_bot_iff, LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank,
      range_mulVecLin, rank_eq_finrank_span_cols]
  · constructor
    · intro hM; apply Submodule.eq_top_of_finrank_eq; simp; exact hM
    · intro h; rw [h]; simp
  · simp; rw [hn]

lemma inj_transpose_iff_inj_of_sq {s t : Type*} {M : Matrix s t ℝ} [Fintype s] [Fintype t]
    (hn : Fintype.card s = Fintype.card t) :
    (∀ (v : s → ℝ), Mᵀ *ᵥ v = 0 → v = 0) ↔ (∀ (v : t → ℝ), M *ᵥ v = 0 → v = 0) := by
  rw [← inj_iff_full_finrank hn, ← inj_iff_full_finrank (symm hn), hn]; simp

lemma LICQ_injM (z : EuclideanSpace ℝ (Fin n)) (m : ℕ)
    (Z : Matrix (Fin n) (Fin (n - m)) ℝ) (A : Matrix (p.active_set x) (Fin n) ℝ)
    (meq : m = (p.active_set x).card) (mlen : m ≤ n)
    (Afull : Matrix.rank A = m) (Zfull : Matrix.rank Z = (n - m))
    (AZorth : A * Z = 0) :
    A *ᵥ z = 0 ∧ Zᵀ *ᵥ z = 0 → z = 0 := by
  rintro ⟨eq1, eq2⟩
  let B : Matrix ((p.active_set x) ⊕ (Fin (n - m))) (Fin n) ℝ :=
    Matrix.of (Sum.elim (fun (i : (p.active_set x)) => A i) fun (i : Fin (n - m)) => Zᵀ i)
  let Bt : Matrix (Fin n) ((p.active_set x) ⊕ (Fin (n - m))) ℝ :=
    Matrix.of (fun i => Sum.elim (Aᵀ i) (Z i))
  have Bteq : Bt = Bᵀ := by ext i j; simp [Bt, B]; cases j <;> simp
  have Bzeq0 : B *ᵥ z = Sum.elim (A *ᵥ z) (Zᵀ *ᵥ z) := by
    ext i; cases i <;> simp [B, mulVec, dotProduct]
  rw [eq1, eq2] at Bzeq0; simp at Bzeq0
  have aux : (p.active_set x).card + (n - m) = n := by
    rw [← meq]; rw [add_comm, Nat.sub_add_cancel]; exact mlen
  refine (inj_transpose_iff_inj_of_sq ?_).1 ?_ z Bzeq0
  · simp; rw [aux]
  · intro v Btveq0
    let y := v ∘ Sum.inl
    let z := v ∘ Sum.inr
    have yeq : Bt *ᵥ (Sum.elim y (fun _ ↦ 0)) = Aᵀ *ᵥ y := by ext i; simp [Bt, mulVec, dotProduct]
    have zeq : Bt *ᵥ (Sum.elim (fun _ ↦ 0) z) = Z *ᵥ z := by ext i; simp [Bt, mulVec, dotProduct]
    have veq : v = (Sum.elim y (fun _ ↦ 0)) + (Sum.elim (fun _ ↦ 0) z) := by
      simp [y, z]; ext i; cases i <;> simp
    have eq : Bᵀ *ᵥ v = Aᵀ *ᵥ y + Z *ᵥ z := by rw [veq, ← Bteq, mulVec_add, yeq, zeq]
    rw [eq] at Btveq0
    have yzero : y = 0 := by
      have h : A *ᵥ (Aᵀ *ᵥ y + Z *ᵥ z) = 0 := by rw [Btveq0]; simp
      rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, AZorth] at h; simp at h
      refine (inj_iff_full_finrank ?_).1 ?_ y h
      · simp
      · simp; rw [← meq, Afull]
    have yzero' : (Sum.elim y (fun _ : (Fin (n - m)) ↦ 0)) = 0 := by
      ext i; cases i <;> simp [yzero]
    have zzero : z = 0 := by
      have h : Zᵀ *ᵥ (Aᵀ *ᵥ y + Z *ᵥ z) = 0 := by rw [Btveq0]; simp
      rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, AZorth] at h; simp at h
      refine (inj_iff_full_finrank ?_).1 ?_ z h
      · simp
      · simp; rw [rank_transpose_mul_self, Zfull]
    have zzero' : (Sum.elim (fun _ : (p.active_set x) ↦ 0) z) = 0 := by
      ext i; cases i <;> simp [zzero]
    rw [veq, yzero', zzero']; simp

lemma LICQ_strictfderiv_Ax_elem {x : EuclideanSpace ℝ (Fin n)}
    (c : EuclideanSpace ℝ (Fin n) → ((p.active_set x) → ℝ))
    (ceq : c = fun z ↦ (fun i : (p.active_set x) ↦ if i.1 ∈ τ then (p.equality_constraints i) z
      else (p.inequality_constraints i) z))
    (gradc : EuclideanSpace ℝ (Fin n) → ((p.active_set x) → (EuclideanSpace ℝ (Fin n))))
    (gradceq : gradc = fun z ↦ (fun i : (p.active_set x) ↦ if i.1 ∈ τ then
      gradient (p.equality_constraints i) z else gradient (p.inequality_constraints i) z))
    (A : EuclideanSpace ℝ (Fin n) → Matrix (p.active_set x) (Fin n) ℝ)
    (Aeq : A = fun z ↦ (fun i ↦ gradc z i))
    (Jz : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (p.active_set x))
    (Jzeq : Jz = fun z ↦ (LinearMap.toContinuousLinearMap (toEuclideanLin (A z))))
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p i) x)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x) :
    ∀ (i : { x_1 // x_1 ∈ active_set x }),
    HasStrictFDerivAt (fun x ↦ c x i) ((EuclideanSpace.proj i).comp (Jz x)) x := by
  obtain h := LICQ_nhds_grad x conte conti
  rw [eventually_iff, Metric.mem_nhds_iff] at h; rcases h with ⟨ε, _, _⟩
  intro i; by_cases hi : i.1 ∈ τ
  · rw [ceq, Jzeq, Aeq]; simp [hi]
    rw [hasStrictFDerivAt_iff_isLittleO];
    have eq : (fun p_1 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        p.equality_constraints i.1 p_1.1 - p.equality_constraints i.1 p_1.2 -
        ((EuclideanSpace.proj i).comp (LinearMap.toContinuousLinearMap (toEuclideanLin fun i ↦ gradc x i)))
        (p_1.1 - p_1.2)) = (fun p_1 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        p.equality_constraints i.1 p_1.1 - p.equality_constraints i.1 p_1.2 -
        ⟪gradient (p.equality_constraints ↑i) x, p_1.1 - p_1.2⟫_ℝ ):= by
      ext q; rw [inner_sub_right, gradceq]; simp [toEuclideanLin_apply, mulVec, dotProduct, hi]
      rw [← inner_sub_right]; simp [inner]; grind
    rw [eq]
    specialize conte i hi
    exact StrictFderivAt_of_FderivAt_of_ContinuousAt conte
  · have hi' : i.1 ∈ σ := by
      obtain h := i.2; unfold active_set at h; rw [Finset.mem_union] at h
      rcases h with hi1 | hi2
      · contrapose! hi; exact hi1
      rw [Finset.mem_filter] at hi2
      exact hi2.1
    rw [ceq, Jzeq, Aeq]; simp [hi]
    rw [hasStrictFDerivAt_iff_isLittleO];
    have eq : (fun p_1 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        p.inequality_constraints i.1 p_1.1 - p.inequality_constraints i.1 p_1.2 -
        ((EuclideanSpace.proj i).comp (LinearMap.toContinuousLinearMap (toEuclideanLin fun i ↦ gradc x i)))
        (p_1.1 - p_1.2)) = (fun p_1 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        p.inequality_constraints i.1 p_1.1 - p.inequality_constraints i.1 p_1.2 -
        ⟪gradient (p.inequality_constraints ↑i) x, p_1.1 - p_1.2⟫_ℝ ):= by
      ext q; rw [inner_sub_right, gradceq]; simp [toEuclideanLin_apply, mulVec, dotProduct, hi]
      rw [← inner_sub_right]; simp [inner]; grind
    rw [eq]
    specialize conti i hi'
    exact StrictFderivAt_of_FderivAt_of_ContinuousAt conti

lemma LICQ_implicit_f {x : EuclideanSpace ℝ (Fin n)} {m : ℕ} (v : EuclideanSpace ℝ (Fin n))
    {Mx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    {Rz : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    {Rt : ℝ → EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    (Rteq : Rt = fun t ↦ t • Mx v) (Rxeq0 : Rz x = 0)
    (Rzgrad : HasStrictFDerivAt Rz Mx x) (Mxsurj : LinearMap.range Mx = ⊤) :
    ∃ (N : ℕ) (d : ℕ → EuclideanSpace ℝ (Fin n)), (∀ m ≥ N, Rz (d m) = Rt (1 / m)) ∧
      (Filter.Tendsto d atTop (𝓝 x)) := by
  let g := HasStrictFDerivAt.implicitFunction Rz Mx Rzgrad Mxsurj
  have hfg : ∀ᶠ (p : (EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)) × (LinearMap.ker Mx)) in
      𝓝 (Rz x, (0 : LinearMap.ker Mx)), Rz (g p.1 p.2) = p.1 := by
    simp only [g]; apply HasStrictFDerivAt.map_implicitFunction_eq Rzgrad Mxsurj
  rw [Rxeq0] at hfg
  rw [eventually_iff, Metric.mem_nhds_iff] at hfg
  rcases hfg with ⟨ε, εpos, nhdsin⟩
  have Rtleε : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ‖Rt (m)⁻¹‖ < ε := by
    intro ε εpos
    rw [Rteq]; simp [norm_smul]
    obtain ⟨N, Ngt⟩ := exists_nat_gt (‖Mx v‖ / ε); use N
    intro m mgeN; field_simp
    have mgt : ‖Mx v‖ / ε < m := by apply LT.lt.trans_le Ngt; simp [mgeN]
    have mpos : (0 : ℝ) < m := by
      apply LT.lt.trans_le' mgt; apply div_nonneg; apply norm_nonneg; linarith
    rw [div_lt_comm₀ mpos εpos]; exact mgt
  obtain ⟨N, Rtle⟩ := Rtleε ε εpos
  use N; use fun n ↦ g (Rt (1 / n)) 0; constructor
  · intro m mgeN; specialize Rtle m mgeN
    have Rtmin : (Rt (1 / m), 0) ∈ {x_1 | Rz (g x_1.1 x_1.2) = x_1.1} := by
      apply Set.mem_of_subset_of_mem nhdsin; simp only [one_div, Metric.mem_ball,
        dist_prod_same_right, dist_zero_right]; apply Rtle
    simp at Rtmin; simp [Rtmin]
  · simp only [g]
    apply HasStrictFDerivAt.tendsto_implicitFunction Rzgrad Mxsurj
    · rw [Rxeq0]; rw [NormedAddCommGroup.tendsto_nhds_zero]; simp; apply Rtleε
    · simp

lemma eq_lemma {y z : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (h : ‖(k : ℝ) • y‖ ≠ 0) :
    (1 / ‖y‖) • (y - (1 / (k : ℝ)) • z)
      = (1 / ‖(k : ℝ) • y‖) • ((k : ℝ) • y - z) := by
  rw [norm_smul] at h
  simp at h
  have eq : z = (k : ℝ) • (1 / k : ℝ) • z := by
    rw [smul_smul]; field_simp; rw [div_self, one_smul]; simp [h]
  nth_rw 2 [eq]
  rw [← smul_sub, smul_smul, norm_smul]
  field_simp
  have norm_cast : ‖(k : ℝ)‖ = (k : ℝ) := by simp
  rw [norm_cast]
  field_simp [h.1]

lemma comap1 {x : EuclideanSpace ℝ (Fin n)} {m : ℕ}
    {Mx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    (v : EuclideanSpace ℝ (Fin n)) (vne0 : v ≠ 0)
    (Mxbij : Function.Bijective Mx) : comap (fun z ↦ ‖Mx z‖) (𝓝 0) ≤ 𝓝 0 := by
  rw [ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz] at Mxbij
  obtain ⟨c, antil⟩ := Mxbij.2
  rw [Filter.le_def]; intro s smem
  rw [Metric.mem_nhds_iff] at smem; rcases smem with ⟨a, apos, ha⟩
  rw [antilipschitzWith_iff_le_mul_dist] at antil
  have hc : 0 ≠ c := by
    symm; by_contra hc
    specialize antil 0; simp [hc] at antil; specialize antil v
    absurd antil; simp [vne0]
  have hc' : 0 < c := by refine lt_of_le_of_ne ?_ hc; simp
  use Metric.ball 0 (a / c); constructor
  · apply Metric.ball_mem_nhds
    refine div_pos ?_ hc' ; linarith [apos]
  · intro z zin; simp at zin
    specialize antil 0 z; simp at antil
    have zin' : z ∈ Metric.ball 0 a := by
      simp; calc
        ‖z‖ ≤ c * ‖Mx z‖ := antil
        _ < c * (a / c) := by rw [mul_lt_mul_left]; linarith [zin]; simp [hc']
        _ = a := by field_simp
    exact ha zin'

lemma comap2 (hv : v ≠ 0):
    comap (fun z : EuclideanSpace ℝ (Fin n) ↦ if (‖z‖ = 0) then v else ‖z‖⁻¹ • (z - v))
    (𝓝 0) ≤ 𝓝 v := by
  rw [Filter.le_def]; intro s smem; simp
  rw [Metric.mem_nhds_iff] at smem; rcases smem with ⟨a, apos, ha⟩
  let μ := a / (a + ‖v‖)
  have eq : μ * ‖v‖ = (1 - μ) * a := by
    field_simp [μ]; rw [mul_comm]; rw [@mul_div]
    simp [μ]; ring_nf; field_simp; ring
  have vpos : 0 < ‖v‖ := by
    refine lt_of_le_of_ne (norm_nonneg v) ?_; symm; simp [hv]
  have μle : 0 < 1 - μ := by
    simp [μ]; rw [div_lt_one_iff]
    left
    constructor
    · exact Right.add_pos' apos vpos
    · linarith [apos, vpos]
  have μpos : 0 < μ := by
    simp [μ]; apply div_pos apos; exact add_pos apos (by positivity)
  let r := min μ ‖v‖
  use Metric.ball 0 r; constructor
  · apply Metric.ball_mem_nhds; simp [r]; exact ⟨μpos, hv⟩
  · intro z zin; simp at zin;
    have ze : z ≠ 0 := by
      by_contra hz; simp [hz] at zin; simp [r] at zin
    simp [ze] at zin
    rw [norm_smul] at zin
    have hzpos : 0 < ‖z‖ := by refine lt_of_le_of_ne (norm_nonneg z) ?_; symm; simp [ze]
    have zin' : ‖z‖⁻¹ * ‖z - v‖ < r := by
      simpa [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hzpos)] using zin
    have hmul' : ‖z - v‖ < r * ‖z‖ := by
      have h := mul_lt_mul_of_pos_right zin' hzpos
      have hzne : ‖z‖ ≠ 0 := ne_of_gt hzpos
      simpa [one_div, hzne, mul_comm, mul_left_comm, mul_assoc] using h
    have ieq : ‖z - v‖ < μ * ‖z - v‖ + (1 - μ) * a := by
      calc
        ‖z - v‖ < r * ‖z‖ := hmul'
        _ ≤ μ * ‖z‖ := by
          apply mul_le_mul_of_nonneg_right
          · simp [r]
          · exact norm_nonneg z
        _ ≤ μ * (‖z - v‖ + ‖v‖) := by
          apply mul_le_mul_of_nonneg_left
          rw [add_comm]; apply norm_le_norm_add_norm_sub'
          exact le_of_lt μpos
        _ ≤ μ * ‖z - v‖ + (1 - μ) * a := by
          rw [mul_add]; apply add_le_add_left; rw [eq]
    rw [← sub_lt_iff_lt_add'] at ieq
    nth_rw 1 [← one_mul (‖z - v‖)] at ieq
    rw [← sub_mul, mul_lt_mul_left μle] at ieq
    apply ha; simp; rw [dist_eq_norm]; simp [ieq]

lemma LICQ_tendsto {x : EuclideanSpace ℝ (Fin n)} {m N : ℕ}
    {Mx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    {Rz : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    {Rt : ℝ → EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    {d : ℕ → EuclideanSpace ℝ (Fin n)}
    (v : EuclideanSpace ℝ (Fin n)) (vne0 : v ≠ 0)
    (Rteq : Rt = fun t ↦ t • Mx v) (Rxeq0 : Rz x = 0)
    (hfd : ∀ i ≥ N, Rz (d i) = Rt (1 / (i : ℝ)))
    (dtend : ∀ (ε : ℝ), 0 < ε → ∃ a, ∀ (b : ℕ), a ≤ b → ‖d b - x‖ < ε)
    (Mxbij : Function.Bijective Mx)
    (deriv : Tendsto ((fun x' ↦ ‖x' - x‖⁻¹ * ‖Rz x' - Rz x - Mx (x' - x)‖) ∘ d) atTop (𝓝 0)) :
    Tendsto (fun i : ℕ ↦ (i : ℝ) • (d i - x)) atTop (𝓝 v) := by
  have dne : ∀ i ≥ N.succ, d i ≠ x := by
    contrapose! hfd
    rcases hfd with ⟨i, igeN, dieq⟩
    simp at igeN
    refine ⟨i, ?_, ?_⟩
    · simp; linarith [igeN]
    · rw [dieq, Rxeq0, Rteq]; symm
      rw [smul_ne_zero_iff]; constructor
      · have hi_pos : (0 : ℕ) < i := Nat.zero_lt_of_lt igeN
        have hi0   : (i : ℝ) ≠ 0 := by
          have : (0 : ℝ) < (i : ℝ) := by
            exact_mod_cast hi_pos
          exact ne_of_gt this
        exact one_div_ne_zero hi0
      · contrapose! vne0
        apply Mxbij.1
        rw [vne0]; simp
  have eq1 : ((fun x' ↦ ‖x' - x‖⁻¹ * ‖Rz x' - Rz x - Mx (x' - x)‖) ∘ d) =
      fun i : ℕ ↦ ‖d i - x‖⁻¹ * ‖Rz (d i) - Rz x - Mx (d i - x)‖ := by
    ext i; simp
  have eq2 : (fun i : ℕ ↦ ‖d i - x‖⁻¹ * ‖Rz (d i) - Rz x - Mx (d i - x)‖) =
      fun i : ℕ ↦ ‖d i - x‖⁻¹ * ‖Rz (d i) - Rt (1 / (i : ℝ)) - Rz x - Mx (d i - x - (1 / (i : ℝ)) • v)‖ := by
    ext i
    rw [Rteq]; simp
    left
    rw [sub_right_comm _ _ (Rz x), sub_sub (Rz (d i) - Rz x), add_comm, sub_add_cancel]
  have eq3 : (fun i : ℕ ↦ ‖d i - x‖⁻¹ * ‖Rz (d i) - Rt (1 / (i : ℝ)) - Rz x - Mx (d i - x - (1 / (i : ℝ)) • v)‖)
      =ᶠ[atTop] (fun i : ℕ ↦ ‖d i - x‖⁻¹ * ‖Mx (d i - x - (1 / (i : ℝ)) • v)‖) := by
    rw [EventuallyEq, eventually_atTop]
    refine ⟨N, ?_⟩
    intro i igeN
    specialize hfd i igeN
    rw [hfd, Rxeq0, sub_self, zero_sub, neg_zero, zero_sub, norm_neg]
  rw [eq1, eq2] at deriv
  obtain deriv := Filter.Tendsto.congr' eq3 deriv
  let NMx : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ ‖Mx z‖
  let deriv' : ℕ → EuclideanSpace ℝ (Fin n) := fun i ↦ (‖d i - x‖⁻¹ • (d i - x - (1 / (i : ℝ)) • v))
  have eq4 : (fun i : ℕ ↦ ‖d i - x‖⁻¹ * ‖Mx (d i - x - (1 / (i : ℝ)) • v)‖) =
      NMx ∘ deriv' := by
    ext i; simp [NMx, deriv']; rw [norm_smul]; simp
  rw [eq4] at deriv
  have comap_le : Filter.comap NMx (𝓝 0) ≤ (𝓝 0) := by
    simp only [NMx]
    exact comap1 v vne0 Mxbij
  obtain lim := Tendsto.of_tendsto_comp deriv comap_le
  let φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z ↦ if (‖z‖ = 0) then v else ‖z‖⁻¹ • (z - v)
  have eq5 : deriv' =ᶠ[atTop] φ ∘ (fun i : ℕ ↦ (i : ℝ) • (d i - x)) := by
    rw [EventuallyEq, eventually_atTop]
    have : 0 < ‖v‖ := by
      refine lt_of_le_of_ne (norm_nonneg v) ?_
      symm; simp [vne0]
    rcases dtend ‖v‖ this with ⟨N₁, dtend⟩
    refine ⟨max N₁ N.succ, ?_⟩
    intro i igeN
    simp only [ge_iff_le, max_le_iff] at igeN
    specialize dtend i igeN.1
    have neq : ‖(i : ℝ) • (d i - x)‖ ≠ 0 := by
      rw [norm_smul]
      apply mul_ne_zero
      · have i_pos : 0 < i := lt_of_lt_of_le (Nat.succ_pos N) igeN.2
        have hi_real_ne : (i : ℝ) ≠ 0 := by
          have : (0 : ℝ) < (i : ℝ) := by exact_mod_cast i_pos
          exact ne_of_gt this
        simpa [norm_eq_zero] using hi_real_ne
      · have hdiff_ne : d i - x ≠ 0 := by
          exact sub_ne_zero.mpr (dne i igeN.2)
        simpa [norm_eq_zero] using hdiff_ne
    have i_ne_zero : i ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (Nat.succ_pos N) igeN.2)
    refine (calc
      deriv' i
          = (1 / ‖d i - x‖) • (d i - x - (1 / (i : ℝ)) • v) := by
                simp [deriv', one_div]
      _ = (1 / ‖(i : ℝ) • (d i - x)‖) • ((i : ℝ) • (d i - x) - v) := by
                simpa using eq_lemma (y := d i - x) (z := v) (k := i) neq
      _ = φ ((i : ℝ) • (d i - x)) := by
                simp [φ, one_div]; grind)
  obtain lim' := Filter.Tendsto.congr' eq5 lim
  refine Filter.Tendsto.of_tendsto_comp lim' ?_
  simp only [φ]
  exact comap2 vne0

/-
  Linearized feasible directions equal tagent cone when LICQ holds
  Numerical Optimization, Nocedal & Wright, Lemma 12.2
-/

theorem LICQ_linearized_feasible_directions_sub_posTangentCone
    (x : EuclideanSpace ℝ (Fin n)) (xf : x ∈ p.FeasSet)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p i) x)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x)
    (LIx : p.LICQ x) (hdomain : p.domain = univ):
    p.linearized_feasible_directions x ⊆ posTangentConeAt p.FeasSet x := by
  intro v hv

  by_cases veq0 : v = 0
  · rw [veq0]; rw [posTangentConeAt]; simp
    use fun n ↦ n; use fun _ ↦ 0; simp; constructor
    · use 0; exact fun _ _ ↦ xf
    · exact tendsto_natCast_atTop_atTop

  let gradc : EuclideanSpace ℝ (Fin n) → ((p.active_set x) → (EuclideanSpace ℝ (Fin n))) :=
    fun z ↦ (fun i ↦ if i.1 ∈ τ then gradient (p.equality_constraints i) z
      else gradient (p.inequality_constraints i) z) -- gradient of the constraints
  let Ax : Matrix (p.active_set x) (Fin n) ℝ := fun i ↦ gradc x i -- Jacobi at x
  let m := (p.active_set x).card
  have mlen : m ≤ n := by apply LICQ_mlen x LIx; simp [m]
  have existZ : ∃ (Z : Matrix (Fin n) (Fin (n - m)) ℝ), Ax * Z = 0 ∧ Matrix.rank Z = (n - m) := by
    apply LICQ_existZ x LIx; simp [m]; simp [Ax, gradc]
  rw [LICQ] at LIx;
  rw [posTangentConeAt]; simp only [eventually_atTop, ge_iff_le, mem_setOf_eq]
  rcases existZ with ⟨Z, ⟨eq1, eq2⟩⟩

  let Mx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ) :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Ax)).prod
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Zᵀ)) -- Jacobi of Rz at x
  let c : EuclideanSpace ℝ (Fin n) → ((p.active_set x) → ℝ) :=
    fun z ↦ (fun i ↦ if i.1 ∈ τ then (p.equality_constraints i) z
      else (p.inequality_constraints i) z) -- the constraints
  let Rz : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ) :=
    fun z ↦ (c z, Zᵀ *ᵥ (z - x)) -- z part in R
  let Rt : ℝ → EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ) := fun t ↦ t • Mx v -- t part in R
  let A : EuclideanSpace ℝ (Fin n) → Matrix (p.active_set x) (Fin n) ℝ :=
    fun z ↦ (fun i ↦ gradc z i) -- compose the gradient matrix
  let Jz : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (p.active_set x) :=
    fun z ↦ (LinearMap.toContinuousLinearMap (toEuclideanLin (A z))) -- change the Jacobi into linear transformation
  have cgrad_atx : Jz x = (LinearMap.toContinuousLinearMap (toEuclideanLin Ax)) := by simp [Jz, A, gradc]; rfl -- A x = Ax

  have Rzgrad : HasStrictFDerivAt Rz Mx x := by
    simp only [Rz]
    apply HasStrictFDerivAt.prodMk
    · rw [← cgrad_atx]
      rw [hasStrictFDerivAt_euclidean]
      refine LICQ_strictfderiv_Ax_elem c ?_ gradc ?_ A ?_ Jz ?_ conte conti
      repeat simp only [c, gradc, A, Jz]
    · let N : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin (n - m) → ℝ) :=
        (LinearMap.toContinuousLinearMap (toEuclideanLin Zᵀ))
      show HasStrictFDerivAt (fun y : EuclideanSpace ℝ (Fin n) ↦ Zᵀ *ᵥ (y - x)) N x
      rw [hasStrictFDerivAt_iff_isLittleO]
      have aux :
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
              Zᵀ *ᵥ (p.1 - x) - Zᵀ *ᵥ (p.2 - x) - N (p.1 - p.2)) = 0 := by
        ext y j
        rw [← mulVec_sub, sub_sub, add_sub_cancel, mulVec_eq_toEuclidean]
        simp [N]; grind
      rw [aux]
      simp

  have Rxeq0 : Rz x = 0 := by
    simp [Rz, c]; ext i;
    simp [FeasSet, FeasPoint] at xf
    rcases xf with ⟨⟨_, h12⟩, _, _⟩
    by_cases h1 : i.1 ∈ τ
    · simp [h1]; exact h12 i h1
    · simp [h1]; have hi := i.2; unfold active_set at hi; rw [Finset.mem_union] at hi
      rcases hi with hi1 | hi2
      · contrapose! h1; exact hi1
      rw [Finset.mem_filter] at hi2
      exact hi2.2

  have Mxinj : LinearMap.ker Mx = ⊥ := by
    show LinearMap.ker (Mx : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ
      (p.active_set x) × (Fin (n - m) → ℝ)) = ⊥
    rw [LinearMap.ker_eq_bot']
    intro z Mzeq0; simp [Mx] at Mzeq0
    have heq1 : Ax *ᵥ z = 0 := by rw [mulVec_eq_toEuclidean]; apply Mzeq0.1
    have heq2 : Zᵀ *ᵥ z = 0 := by rw [mulVec_eq_toEuclidean]; apply Mzeq0.2
    refine LICQ_injM z m Z Ax ?_ mlen ?_ eq2 eq1 ⟨heq1, heq2⟩
    simp [m]
    obtain hAx := LICQ_Axfullrank x LIx; simp at hAx
    show Ax.rank = (active_set x).card; apply hAx; simp only [Ax]; rfl
  have Mxsurj : LinearMap.range Mx = ⊤ := by
    show LinearMap.range (Mx : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)) = ⊤
    rw [← LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank]
    · apply Mxinj
    · simp; show n = m + (n - m)
      rw [add_comm, Nat.sub_add_cancel]; apply mlen

  use (fun n ↦ n)

  have implicit_f: ∃ (N : ℕ) (d : ℕ → EuclideanSpace ℝ (Fin n)), (∀ m ≥ N, Rz (d m) = Rt (1 / m)) ∧
      (Filter.Tendsto d atTop (𝓝 x)) := by
    refine LICQ_implicit_f v ?_ Rxeq0 Rzgrad Mxsurj; simp [Rt]

  clear cgrad_atx
  simp only [linearized_feasible_directions] at hv
  rcases hv with ⟨hvh1, hvh2⟩
  rcases implicit_f with ⟨N, d, hfd, dtend⟩
  rw [LinearMapClass.ker_eq_bot] at Mxinj
  rw [LinearMap.range_eq_top] at Mxsurj
  obtain deriv := (hasFDerivAt_iff_tendsto.1 (HasStrictFDerivAt.hasFDerivAt Rzgrad))
  obtain deriv := tendsto_nhds_iff_seq_tendsto.1 deriv d dtend
  rw [tendsto_iff_norm_sub_tendsto_zero, NormedAddCommGroup.tendsto_nhds_zero] at dtend; simp at dtend
  obtain ⟨ε, εpos, inactive⟩ := LICQ_inactive_nhds x xf conti
  obtain ⟨N', dtendx⟩ := dtend ε εpos

  use (fun n ↦ d n - x); constructor
  · use max N N'; intro nn hnn; simp [FeasSet, FeasPoint]
    have hfd_nn := hfd nn (le_of_max_le_left hnn)
    simp [Rz, Rt, Mx] at hfd_nn; rw [← mulVec_eq_toEuclidean] at hfd_nn
    rcases hfd_nn with ⟨hv1, hv2⟩
    have Axeq : (nn : ℝ)⁻¹ • Ax *ᵥ v =
    fun i => (nn : ℝ)⁻¹ * ⟪gradc x i, v⟫_ℝ := by
      ext i
      have hdot : (Ax *ᵥ v) i = ⟪gradc x i, v⟫_ℝ := by
        simp [Ax, Matrix.mulVec, dotProduct, EuclideanSpace.inner_eq_star_dotProduct, mul_comm]
      simp [hdot]
    have Axroweq : ∀ i : (p.active_set x), c (d nn) i = (nn : ℝ)⁻¹ * ⟪gradc x i, v⟫_ℝ := by
      intro i
      have : c (d nn) = (nn : ℝ)⁻¹ • Ax *ᵥ v := hv1
      rw [this, Axeq]
    constructor; constructor
    · rw [hdomain]; simp
    · intro i hi
      obtain h := hvh1 i hi
      obtain eq := Axroweq ⟨i, by simp [active_set, hi]⟩
      simp [c, hi, gradc] at eq
      rw [eq]
      exact mul_eq_zero.mpr (Or.inr h)
    constructor
    · rw [hdomain]; simp
    · intro j hj
      have notin : j ∉ τ := by
        by_contra hh;
        have : j ∈ τ ∩ σ := by simp [hj, hh]
        rw [p.eq_ine_not_intersect] at this; tauto
      by_cases hj1 : j ∈ p.active_set x
      · have jin : j ∈ σ ∩ (p.active_set x) := by simp [hj1, hj]
        obtain h := hvh2 j jin
        obtain eq := Axroweq ⟨j, hj1⟩
        simp [c, notin, gradc] at eq
        rw [eq]
        have inv_nonneg : 0 ≤ (nn : ℝ)⁻¹ := by
          have : 0 ≤ (nn : ℝ) := by exact_mod_cast (Nat.zero_le nn)
          exact inv_nonneg.mpr this
        have : 0 ≤ (nn : ℝ)⁻¹ * ⟪gradient (p.inequality_constraints j) x, v⟫_ℝ :=
          mul_nonneg inv_nonneg h
        simpa [gradc, notin, hj1]
      · specialize inactive j; simp [hj, hj1] at inactive
        specialize inactive (d nn)
        specialize dtendx nn (le_of_max_le_right hnn); rw [← dist_eq_norm] at dtendx
        have hpos : 0 < p.inequality_constraints j (d nn) := inactive dtendx
        exact le_of_lt hpos

  constructor
  · exact tendsto_natCast_atTop_atTop
  · have Mxbij : Function.Bijective Mx := ⟨Mxinj, Mxsurj⟩
    refine LICQ_tendsto v veq0 ?_ Rxeq0 hfd dtend Mxbij deriv; simp [Rt]

theorem LICQ_linearized_feasible_directions_eq_posTangentCone
    (x : EuclideanSpace ℝ (Fin n)) (xf : x ∈ p.FeasSet)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p i) x)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x)
    (LIx : p.LICQ x) (hdomain : p.domain = univ):
    p.linearized_feasible_directions x = posTangentConeAt p.FeasSet x := by
  have diffable : ∀ i ∈ τ, DifferentiableAt ℝ (equality_constraints p i) x :=
    diffable_of_hasgradient_nhds conte
  have diffable₂ : ∀ i ∈ σ, DifferentiableAt ℝ (inequality_constraints p i) x :=
    diffable_of_hasgradient_nhds conti
  apply Set.Subset.antisymm
  · exact LICQ_linearized_feasible_directions_sub_posTangentCone x xf conte conti LIx hdomain
  · exact linearized_feasible_directions_contain_tagent_cone xf diffable diffable₂

theorem local_Minimum_constraint_qualification_descent_direction' (loc : EuclideanSpace ℝ (Fin n))
    (hl : p.Local_Minimum loc) (hf : Differentiable ℝ p.objective)
    (h : p.linearized_feasible_directions loc = posTangentConeAt p.FeasSet loc) :
    ¬ ∃ d : EuclideanSpace ℝ (Fin n), d ∈ p.linearized_feasible_directions loc
      ∧ ⟪gradient p.objective loc, d⟫_ℝ < (0 : ℝ) := by
  simp only [not_exists, not_and, not_lt]
  rw [h]; apply local_Minimum_TangentCone loc hl hf

theorem local_Minimum_constraint_qualification_descent_direction'' (loc : EuclideanSpace ℝ (Fin n))
    (hl : p.Local_Minimum loc) (hf : Differentiable ℝ p.objective)
    (h : p.linearized_feasible_directions loc = posTangentConeAt p.FeasSet loc) :
    ¬ ∃ d : EuclideanSpace ℝ (Fin n), (∀ i ∈ τ, ⟪gradient (p.equality_constraints i) loc, d⟫_ℝ = 0)
      ∧ (∀ j ∈ σ ∩ p.active_set loc, ⟪gradient (p.inequality_constraints j) loc, d⟫_ℝ ≥ 0)
      ∧ (⟪gradient p.objective loc, d⟫_ℝ < (0 : ℝ)) := by
  obtain ht := local_Minimum_constraint_qualification_descent_direction' loc hl hf h
  unfold linearized_feasible_directions at ht
  simp only [mem_setOf_eq] at ht
  by_contra hh; apply absurd ht; push_neg; rcases hh with ⟨d, ⟨hd1, hd2, hd3⟩⟩; use d

lemma subtype_sum (σ τ : Finset ℕ) (f : σ → EuclideanSpace ℝ (Fin n))
    (g : {x // x ∈ σ ∩ τ} → EuclideanSpace ℝ (Fin n))
    (h2 : ∀ i : {x // x ∈ σ ∩ τ}, g i =
      f {val := i.1, property := by have hi := i.2; rw [Finset.mem_inter] at hi; exact hi.1})
    (h3 : ∀ i : σ, i.1 ∉ τ → f i = 0) :
    ∑ i, f i = ∑ i, g i := by
  have : ∑ i, g i = ∑ i : {x // x ∈ σ ∩ τ},
      f {val := i.1, property := by obtain hi := i.2; rw [Finset.mem_inter] at hi; exact hi.1} := by
    congr; ext i; rw [h2]
  rw [this]; simp
  let f₁ : ℕ → EuclideanSpace ℝ (Fin n):= fun i => if h : i ∈ σ then f ⟨i, h⟩ else 0
  have eq1 : ∑ i ∈ σ.attach, f i = ∑ i ∈ σ, f₁ i := by
    simp [f₁]; nth_rw 2 [← Finset.sum_attach]; congr; simp
  have eq2 : ∑ i ∈ (σ ∩ τ).attach,
      f {val := i.1, property := by obtain hi := i.2; rw [Finset.mem_inter] at hi; exact hi.1} =
      ∑ i ∈ (σ ∩ τ), f₁ i := by
    simp [f₁]; nth_rw 2 [← Finset.sum_attach]; congr; ext x j
    have : x.1 ∈ σ := Finset.mem_of_mem_inter_left x.2
    simp [this]
  rw [eq1, eq2]
  obtain eq := Finset.sdiff_union_inter σ τ
  nth_rw 1 [← eq]; rw [Finset.sum_union]; simp
  have feq0 : ∀ x ∈ (σ \ τ), f₁ x = 0 := by
    simp [f₁]; intro x _ xninτ
    intro h; specialize h3 ⟨x, h⟩; apply h3; simp [xninτ]
  apply Finset.sum_eq_zero feq0
  apply Finset.disjoint_sdiff_inter σ τ

open Constrained_OptimizationProblem Topology InnerProductSpace Set Filter

theorem first_order_neccessary_general (p1 : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin n)) τ σ)
    (loc : EuclideanSpace ℝ (Fin n)) (hl : p1.Local_Minimum loc)
    (hf : Differentiable ℝ p1.objective)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p1 i) loc)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p1 i) loc)
    (h : p1.linearized_feasible_directions loc = posTangentConeAt p1.FeasSet loc) :
    p1.FeasPoint loc ∧ (∃ (lambda1 : τ → ℝ) (lambda2 : σ → ℝ),
    (gradient (fun m ↦ (p1.Lagrange_function m lambda1 lambda2)) loc = 0) ∧ (∀ j : σ, lambda2 j ≥ 0) ∧
    (∀ j : σ, (lambda2 j) * (p1.inequality_constraints j loc) = 0)) := by
  constructor
  · exact hl.1
  · obtain h1 := local_Minimum_constraint_qualification_descent_direction'' loc hl hf
    have he1 : ∀ i ∈ τ, DifferentiableAt ℝ (p1.equality_constraints i) loc :=
      diffable_of_hasgradient_nhds conte
    have hc1 : ∀ i ∈ σ, DifferentiableAt ℝ (p1.inequality_constraints i) loc :=
      diffable_of_hasgradient_nhds conti
    obtain h := h1 h
    rw [← Farkas (c := gradient p1.objective loc)] at h
    rcases h with ⟨lam, mu, ⟨h1, h2⟩⟩
    let mu1 : σ → ℝ := fun i ↦ if k : i.1 ∈ p1.active_set loc then
      mu {val := i.1, property := by simp [k]} else 0
    use lam; use mu1; constructor
    · unfold Lagrange_function
      have hDiffEqSum :
        DifferentiableAt ℝ
          (fun m : EuclideanSpace ℝ (Fin n) =>
            ∑ i : {x // x ∈ τ},
              lam i * p1.equality_constraints (↑i) m) loc := by
        change
          DifferentiableAt ℝ
            (fun m : EuclideanSpace ℝ (Fin n) =>
              ∑ i ∈ (Finset.univ : Finset {x // x ∈ τ}),
                lam i * p1.equality_constraints (↑i) m) loc
        refine DifferentiableAt.fun_sum ?_
        intro i _
        exact DifferentiableAt.const_mul (he1 i.1 i.2) (lam i)
      have hDiffObjSubEq :
        DifferentiableAt ℝ
          (fun m : EuclideanSpace ℝ (Fin n) =>
            p1.objective m - ∑ i : {x // x ∈ τ}, lam i * p1.equality_constraints (↑i) m) loc := by
        have := hf loc
        have := this.sub hDiffEqSum
        simpa using this
      have hDiffIneqSum :
        DifferentiableAt ℝ
          (fun m : EuclideanSpace ℝ (Fin n) =>
            ∑ j : {x // x ∈ σ},
              mu1 j * p1.inequality_constraints (↑j) m) loc := by
        change
          DifferentiableAt ℝ
            (fun m : EuclideanSpace ℝ (Fin n) =>
              ∑ j ∈ (Finset.univ : Finset {x // x ∈ σ}),
                mu1 j * p1.inequality_constraints (↑j) m) loc
        refine DifferentiableAt.fun_sum ?_
        intro j _
        exact DifferentiableAt.const_mul (hc1 j.1 j.2) (mu1 j)
      rw [gradient_sub, gradient_sub]
      ·
        have h_grad_sum_eq : gradient (fun m ↦ ∑ i, lam i * p1.equality_constraints (↑i) m) loc =
            ∑ i, gradient (fun m ↦ lam i * p1.equality_constraints (↑i) m) loc := by
          apply gradient_sum
          intro i _; exact DifferentiableAt.const_mul (he1 i.1 i.2) (lam i)
        rw [h_grad_sum_eq]
        have h_grad_sum_ineq : gradient (fun m ↦ ∑ j, mu1 j * p1.inequality_constraints (↑j) m) loc =
            ∑ j, gradient (fun m ↦ mu1 j * p1.inequality_constraints (↑j) m) loc := by
          apply gradient_sum
          intro i _; exact DifferentiableAt.const_mul (hc1 i.1 i.2) (mu1 i)
        rw [h_grad_sum_ineq, h2]
        rw [sub_sub, ← sub_add_sub_comm]
        have : ∑ x, lam x • gradient (p1.equality_constraints x) loc -
            ∑ i, gradient (fun m => lam i * p1.equality_constraints i m) loc = 0 := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_eq_zero
          intro i _; rw [gradient_const_mul']; simp; exact (he1 i.1 i.2)
        rw [this, zero_add, sub_eq_zero]; symm
        have : ∑ i, gradient (fun m => mu1 i * p1.inequality_constraints (↑i) m) loc =
            ∑ i, mu1 i • gradient (p1.inequality_constraints (↑i)) loc := by
          congr; ext i; rw [← gradient_const_mul']; exact (hc1 i i.property)
        rw [this]
        let f := fun i ↦ mu1 i • gradient (p1.inequality_constraints ↑i) loc
        let g := fun i ↦ mu i • gradient (p1.inequality_constraints ↑i) loc
        have : ∑ i, f i = ∑ i, g i := by
          apply subtype_sum σ (p1.active_set loc) f g
          · intro i; simp [f, g, mu1];
            obtain hi := i.2; rw [Finset.mem_inter] at hi; simp [hi.2]
          · intro i hi; simp [f, mu1, hi]
        simp only [f, g] at this; exact this
      · exact hf loc
      · exact hDiffEqSum
      · exact hDiffObjSubEq
      · exact hDiffIneqSum
    constructor
    · intro j; simp [mu1]
      by_cases h : j.1 ∈ p1.active_set loc
      · simp [h]; exact h1 {val := j.1, property := by simp [h]}
      · simp [h]
    · intro j; simp [mu1]
      by_cases h : j.1 ∈ p1.active_set loc
      · simp [h]
        unfold active_set at h
        rw [Finset.mem_union] at h
        cases h with
        | inl h_eq =>
          exfalso
          have : j.1 ∈ τ ∧ j.1 ∈ σ := ⟨h_eq, j.2⟩
          have : j.1 ∈ τ ∩ σ := Finset.mem_inter.mpr this
          rw [p1.eq_ine_not_intersect] at this
          simp at this
        | inr h_ineq =>
          rw [Finset.mem_filter] at h_ineq
          right
          exact h_ineq.2
      · simp [h]

/-
  Karush–Kuhn–Tucker conditions
  Numerical Optimization, Nocedal & Wright, Theorem 12.1
-/
theorem first_order_neccessary_LICQ (p1 : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin n)) τ σ)
    (loc : EuclideanSpace ℝ (Fin n)) (hl : p1.Local_Minimum loc)
    (hf : Differentiable ℝ p1.objective)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p1 i) loc)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p1 i) loc)
    (hLICQ : p1.LICQ loc) (hdomain : p1.domain = univ) :
    p1.FeasPoint loc ∧ (∃ (lambda1 : τ → ℝ) (lambda2 : σ → ℝ),
    (gradient (fun m ↦ (p1.Lagrange_function m lambda1 lambda2)) loc = 0) ∧ (∀ j : σ, lambda2 j ≥ 0) ∧
    (∀ j : σ, (lambda2 j) * (p1.inequality_constraints j loc) = 0)) := by
  apply first_order_neccessary_general p1 loc hl hf conte conti
  apply LICQ_linearized_feasible_directions_eq_posTangentCone
  apply hl.1; use conte; use conti; exact hLICQ; exact hdomain

end Constrained_OptimizationProblem_property_finite_dimensional

section Constrained_OptimizationProblem_property_linear

open Constrained_OptimizationProblem Topology InnerProductSpace Set Filter Matrix

variable {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
variable {τ σ : Finset ℕ} {p : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin n)) τ σ}

theorem LinearCQ_linear_constraint_eq (x : EuclideanSpace ℝ (Fin n)) (Lx : p.LinearCQ x) :
    ∀ i ∈ τ, ∃ a, ∃ b, (equality_constraints p i) = fun y ↦ ⟪a, y⟫_ℝ + b := by
  intro i hi
  simp [LinearCQ] at Lx
  obtain Lx := (Lx).1 i ((equality_constraint_active_set x) hi) hi
  exact (IsLinear_iff' _).mp Lx

theorem LinearCQ_linear_constraint_gradient_eq (x : EuclideanSpace ℝ (Fin n)) (Lx : p.LinearCQ x) :
    ∀ i ∈ τ, ∃ a, ∃ b, ((equality_constraints p i) = fun y ↦ ⟪a, y⟫_ℝ + b) ∧
    gradient (equality_constraints p i) x = a := by
  intro i hi
  obtain ⟨a, b, hab⟩ := LinearCQ_linear_constraint_eq x Lx i hi
  use a; use b; constructor; exact hab
  rw [hab]; rw [gradient_add_const]
  exact (gradient_of_inner_const x a).gradient

theorem LinearCQ_linear_constraint_ineq (x : EuclideanSpace ℝ (Fin n)) (Lx : p.LinearCQ x) :
    ∀ i ∈ p.active_set x ∩ σ, ∃ a, ∃ b, (inequality_constraints p i) = fun y ↦ ⟪a, y⟫_ℝ + b := by
  intro i hi
  simp only [LinearCQ] at Lx
  obtain Lx := (Lx).2 i hi
  exact (IsLinear_iff' _).mp Lx

theorem LinearCQ_linear_constraint_gradient_ineq (x : EuclideanSpace ℝ (Fin n)) (Lx : p.LinearCQ x) :
    ∀ i ∈ p.active_set x ∩ σ, ∃ a, ∃ b, ((inequality_constraints p i) = fun y ↦ ⟪a, y⟫_ℝ + b) ∧
    gradient (inequality_constraints p i) x = a := by
  intro i hi
  obtain ⟨a, b, hab⟩ := LinearCQ_linear_constraint_ineq x Lx i hi
  use a; use b; constructor; exact hab
  rw [hab]; rw [gradient_add_const]
  exact (gradient_of_inner_const x a).gradient

theorem Linear_linearized_feasible_directions_eq_posTangentCone
    (x : EuclideanSpace ℝ (Fin n)) (xf : x ∈ p.FeasSet)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p i) x)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x)
    (Lx : p.LinearCQ x) (hdomain : p.domain = univ):
    p.linearized_feasible_directions x = posTangentConeAt p.FeasSet x := by
  have diffable : ∀ i ∈ τ, DifferentiableAt ℝ (equality_constraints p i) x :=
    diffable_of_hasgradient_nhds conte
  have diffable₂ : ∀ i ∈ σ, DifferentiableAt ℝ (inequality_constraints p i) x :=
    diffable_of_hasgradient_nhds conti
  symm; apply Set.Subset.antisymm
  · exact linearized_feasible_directions_contain_tagent_cone xf diffable diffable₂
  intro v hv
  obtain ⟨t_, ht_, ht⟩ := inactive_constraint x v xf conti
  obtain ⟨hv1, hv2⟩ := hv
  let z := fun (k : ℕ) ↦ (t_ / (k + 1)) • v
  simp [posTangentConeAt]
  let c := fun (k : ℕ) ↦ (k + (1 : ℝ)) / t_
  use c; use z
  constructor
  · use 0; intro n hn
    simp [FeasSet, FeasPoint]; constructor;
    · constructor; rw [hdomain]; trivial
      intro i hi
      obtain ⟨a, c, ⟨hab, hg⟩⟩ := LinearCQ_linear_constraint_gradient_eq x Lx i hi
      simp [FeasSet, FeasPoint] at xf
      obtain ⟨⟨_, h2⟩, ⟨_, _⟩⟩ := xf
      obtain h2 := h2 i hi; rw [← h2]; rw [hab]; simp only
      have : ⟪a, z n⟫_ℝ = 0 := by
        obtain hv1 := hv1 i hi
        rw [hg] at hv1
        simp only [z]; rw [inner_smul_right, hv1, mul_zero]
      rw [inner_add_right, this, add_zero]
    constructor; rw [hdomain]; trivial
    intro j hj
    by_cases hj1 : j ∈ p.active_set x
    · obtain hj' := Finset.mem_inter_of_mem hj1 hj
      obtain ⟨a, c, ⟨hab, hg⟩⟩ := LinearCQ_linear_constraint_gradient_ineq x Lx j hj'
      simp [FeasSet, FeasPoint] at xf
      have : ⟪a, z n⟫_ℝ ≥ 0 := by
        obtain hv2 := hv2 j (Finset.mem_inter_of_mem hj hj1)
        rw [hg] at hv2; simp only [z]; rw [inner_smul_right]
        positivity
      obtain ⟨⟨_, _⟩, ⟨_, h2⟩⟩ := xf
      simp [active_set] at hj1;
      have : j ∉ τ := by
        by_contra hh;
        have : j ∈ τ ∩ σ := by simp [hj, hh]
        rw [p.eq_ine_not_intersect] at this; tauto
      simp [this] at hj1
      rw [← hj1.2, hab]; simp only
      rw [inner_add_right]
      linarith
    simp [z]
    have : (t_ / (↑n + 1)) ∈ Icc 0 t_ := by
      simp; constructor; positivity
      apply div_le_self (by linarith) (by linarith)
    obtain ht := ht _ this j (Finset.mem_sdiff.mpr ⟨hj, hj1⟩)
    linarith
  constructor
  · apply Filter.Tendsto.atTop_div_const ht_
    refine Tendsto.atTop_add_nonneg ?_ ?_
    · exact tendsto_natCast_atTop_atTop
    exact fun x ↦ zero_le_one' ℝ
  apply tendsto_atTop_of_eventually_const (i₀ := 1)
  intro i hi; simp [c, z]
  rw [smul_smul]; field_simp; simp

theorem first_order_neccessary_LinearCQ
    (p1 : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin n)) τ σ)
    (loc : EuclideanSpace ℝ (Fin n)) (hl : p1.Local_Minimum loc)
    (hf : Differentiable ℝ p1.objective)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p1 i) loc)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p1 i) loc)
    (hLinearCQ : p1.LinearCQ loc) (hdomain : p1.domain = univ) :
    p1.FeasPoint loc ∧ (∃ (lambda1 : τ → ℝ) (lambda2 : σ → ℝ),
    (gradient (fun m ↦ (p1.Lagrange_function m lambda1 lambda2)) loc = 0) ∧ (∀ j : σ, lambda2 j ≥ 0) ∧
    (∀ j : σ, (lambda2 j) * (p1.inequality_constraints j loc) = 0)) := by
  apply first_order_neccessary_general p1 loc hl hf conte conti
  apply Linear_linearized_feasible_directions_eq_posTangentCone
  apply hl.1; use conte; use conti; exact hLinearCQ; exact hdomain

end Constrained_OptimizationProblem_property_linear
