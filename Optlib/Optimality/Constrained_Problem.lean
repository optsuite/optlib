/-
Copyright (c) 2024 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Shengyang Xu, Yuxuan Wu
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
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

def IsLinear (f : E → ℝ) : Prop := ∃ a, ∃ b, f = fun x ↦ (⟪x, a⟫_ℝ : ℝ) + b

lemma IsLinear_iff (f : E → ℝ) : IsLinear f ↔ ∃ a b, f = fun x ↦ (⟪x, a⟫_ℝ : ℝ) + b := by rfl

lemma IsLinear_iff' (f : E → ℝ) : IsLinear f ↔ ∃ a b, f = fun x ↦ (⟪a, x⟫_ℝ : ℝ) + b := by
  constructor
  repeat rintro ⟨a, b, rfl⟩; exact ⟨a, b, by ext x; simp; exact real_inner_comm _ _⟩

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

open Constrained_OptimizationProblem Topology InnerProductSpace Set Filter Tendsto

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
  intro v vt
  simpa using hl.hasFDerivWithinAt_nonneg hf.hasGradientAt.hasFDerivAt.hasFDerivWithinAt vt

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
    . rw [← neg_neg (⟪gradient (equality_constraints p i) x, v⟫_ℝ)]
      apply neg_nonpos_of_nonneg
      rw [← inner_neg_left]
      have a₁ : ∀ i ∈ τ, DifferentiableAt ℝ (-equality_constraints p i) x :=
        fun i itau ↦ DifferentiableAt.neg (diffable i itau)
      have a₂ : - gradient (equality_constraints p i) x =
          gradient (-equality_constraints p i) x := by
        symm
        apply HasGradientAt.gradient
        apply HasGradientAt.neg
        exact DifferentiableAt.hasGradientAt (diffable i itau)
      rw [a₂]
      apply posTangentCone_localmin_inner_pos (negimin i itau) (a₁ i itau) v hv
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

open Constrained_OptimizationProblem Topology InnerProductSpace Set Filter Tendsto Matrix

variable {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
variable {τ σ : Finset ℕ} {p : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin n)) τ σ}
variable {M : Matrix (p.active_set x) (Fin n) ℝ} {v : EuclideanSpace ℝ (Fin n)}

axiom LICQ_mlen (x : EuclideanSpace ℝ (Fin n)) (LIx : p.LICQ x)
    {m : ℕ} (meq : m = (p.active_set x).card) : m ≤ n

axiom LICQ_Axfullrank (x : EuclideanSpace ℝ (Fin n)) (LIx : p.LICQ x)
    {M : Matrix (p.active_set x) (Fin n) ℝ}
    (eq : M = fun i : (p.active_set x) ↦ if i.1 ∈ τ then (gradient (p.equality_constraints i) x).ofLp
        else (gradient (p.inequality_constraints i) x).ofLp) :
    Matrix.rank M = (Fintype.card (p.active_set x))

axiom LICQ_existZ (x : EuclideanSpace ℝ (Fin n)) (LIx : p.LICQ x)
    {m : ℕ} (meq : m = (p.active_set x).card)
    {M : Matrix (p.active_set x) (Fin n) ℝ}
    (eq : M = fun i : (p.active_set x) ↦ if i.1 ∈ τ then (gradient (p.equality_constraints i) x).ofLp
        else (gradient (p.inequality_constraints i) x).ofLp) :
    ∃ (Z : Matrix (Fin n) (Fin (n - m)) ℝ), M * Z = 0 ∧ Matrix.rank Z = (n - m)

axiom mulVec_eq_toEuclidean {s : Type*} (M : Matrix s (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    M *ᵥ y = (toEuclideanLin M) y

axiom inj_iff_full_finrank {s t : Type*} {M : Matrix s t ℝ} [Fintype s] [Fintype t]
    (hn : Fintype.card s = Fintype.card t) :
    M.rank = Fintype.card s ↔ ∀ (v : t → ℝ), M *ᵥ v = 0 → v = 0

axiom inj_transpose_iff_inj_of_sq {s t : Type*} {M : Matrix s t ℝ} [Fintype s] [Fintype t]
    (hn : Fintype.card s = Fintype.card t) :
    (∀ (v : s → ℝ), Mᵀ *ᵥ v = 0 → v = 0) ↔ (∀ (v : t → ℝ), M *ᵥ v = 0 → v = 0)

axiom LICQ_injM (z : EuclideanSpace ℝ (Fin n)) (m : ℕ)
    (Z : Matrix (Fin n) (Fin (n - m)) ℝ) (A : Matrix (p.active_set x) (Fin n) ℝ)
    (meq : m = (p.active_set x).card) (mlen : m ≤ n)
    (Afull : Matrix.rank A = m) (Zfull : Matrix.rank Z = (n - m))
    (AZorth : A * Z = 0) :
    A *ᵥ z = 0 ∧ Zᵀ *ᵥ z = 0 → z = 0

axiom LICQ_strictfderiv_Ax_elem {x : EuclideanSpace ℝ (Fin n)}
    (c : EuclideanSpace ℝ (Fin n) → ((p.active_set x) → ℝ))
    (ceq : c = fun z ↦ (fun i : (p.active_set x) ↦ if i.1 ∈ τ then (p.equality_constraints i) z
      else (p.inequality_constraints i) z))
    (gradc : EuclideanSpace ℝ (Fin n) → ((p.active_set x) → (EuclideanSpace ℝ (Fin n))))
    (gradceq : gradc = fun z ↦ (fun i : (p.active_set x) ↦ if i.1 ∈ τ then
      gradient (p.equality_constraints i) z else gradient (p.inequality_constraints i) z))
    (A : EuclideanSpace ℝ (Fin n) → Matrix (p.active_set x) (Fin n) ℝ)
    (Aeq : A = fun z ↦ (fun i ↦ (gradc z i).ofLp))
    (Jz : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (p.active_set x))
    (Jzeq : Jz = fun z ↦ (LinearMap.toContinuousLinearMap (toEuclideanLin (A z))))
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p i) x)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x) :
    ∀ (i : { x_1 // x_1 ∈ active_set x }),
    HasStrictFDerivAt (fun x ↦ c x i) ((EuclideanSpace.proj i).comp (Jz x)) x

axiom LICQ_implicit_f {x : EuclideanSpace ℝ (Fin n)} {m : ℕ} (v : EuclideanSpace ℝ (Fin n))
    {Mx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    {Rz : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    {Rt : ℝ → EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    (Rteq : Rt = fun t ↦ t • Mx v) (Rxeq0 : Rz x = 0)
    (Rzgrad : HasStrictFDerivAt Rz Mx x)
    (Mxsurj : LinearMap.range (Mx : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)) = ⊤) :
    ∃ (N : ℕ) (d : ℕ → EuclideanSpace ℝ (Fin n)), (∀ m ≥ N, Rz (d m) = Rt (1 / m)) ∧
      (Filter.Tendsto d atTop (𝓝 x))

axiom eq_lemma {y z : EuclideanSpace ℝ (Fin n)} {n : ℕ} (h : ‖(n : ℝ) • y‖ ≠ 0) :
    (1 / ‖y‖) • (y - (1 / (n : ℝ)) • z) = (1 / ‖(n : ℝ) • y‖) • ((n : ℝ) • y - z)

axiom comap1 {x : EuclideanSpace ℝ (Fin n)} {m : ℕ}
    {Mx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (p.active_set x) × (Fin (n - m) → ℝ)}
    (v : EuclideanSpace ℝ (Fin n)) (vne0 : v ≠ 0)
    (Mxbij : Function.Bijective Mx) : comap (fun z ↦ ‖Mx z‖) (𝓝 0) ≤ 𝓝 0

axiom comap2 (hv : v ≠ 0) :
    comap (fun z : EuclideanSpace ℝ (Fin n) ↦ if (‖z‖ = 0) then v else ‖z‖⁻¹ • (z - v))
      (𝓝 0) ≤ 𝓝 v

axiom LICQ_tendsto {x : EuclideanSpace ℝ (Fin n)} {m N : ℕ}
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
    Tendsto (fun i : ℕ ↦ (i : ℝ) • (d i - x)) atTop (𝓝 v)

axiom LICQ_linearized_feasible_directions_sub_posTangentCone
    (x : EuclideanSpace ℝ (Fin n)) (xf : x ∈ p.FeasSet)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p i) x)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x)
    (LIx : p.LICQ x) (hdomain : p.domain = univ) :
    p.linearized_feasible_directions x ⊆ posTangentConeAt p.FeasSet x

axiom LICQ_linearized_feasible_directions_eq_posTangentCone
    (x : EuclideanSpace ℝ (Fin n)) (xf : x ∈ p.FeasSet)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p i) x)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x)
    (LIx : p.LICQ x) (hdomain : p.domain = univ) :
    p.linearized_feasible_directions x = posTangentConeAt p.FeasSet x

axiom local_Minimum_constraint_qualification_descent_direction' (loc : EuclideanSpace ℝ (Fin n))
    (hl : p.Local_Minimum loc) (hf : Differentiable ℝ p.objective)
    (h : p.linearized_feasible_directions loc = posTangentConeAt p.FeasSet loc) :
    ¬ ∃ d : EuclideanSpace ℝ (Fin n), d ∈ p.linearized_feasible_directions loc
      ∧ ⟪gradient p.objective loc, d⟫_ℝ < (0 : ℝ)

axiom local_Minimum_constraint_qualification_descent_direction'' (loc : EuclideanSpace ℝ (Fin n))
    (hl : p.Local_Minimum loc) (hf : Differentiable ℝ p.objective)
    (h : p.linearized_feasible_directions loc = posTangentConeAt p.FeasSet loc) :
    ¬ ∃ d : EuclideanSpace ℝ (Fin n), (∀ i ∈ τ, ⟪gradient (p.equality_constraints i) loc, d⟫_ℝ = 0)
      ∧ (∀ j ∈ σ ∩ p.active_set loc, ⟪gradient (p.inequality_constraints j) loc, d⟫_ℝ ≥ 0)
      ∧ (⟪gradient p.objective loc, d⟫_ℝ < (0 : ℝ))

axiom subtype_sum (σ τ : Finset ℕ) (f : σ → EuclideanSpace ℝ (Fin n))
    (g : {x // x ∈ σ ∩ τ} → EuclideanSpace ℝ (Fin n))
    (h2 : ∀ i : {x // x ∈ σ ∩ τ}, g i =
      f {val := i.1, property := by have hi := i.2; rw [Finset.mem_inter] at hi; exact hi.1})
    (h3 : ∀ i : σ, i.1 ∉ τ → f i = 0) :
    ∑ i, f i = ∑ i, g i

axiom first_order_neccessary_general (p1 : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin n)) τ σ)
    (loc : EuclideanSpace ℝ (Fin n)) (hl : p1.Local_Minimum loc)
    (hf : Differentiable ℝ p1.objective)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p1 i) loc)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p1 i) loc)
    (h : p1.linearized_feasible_directions loc = posTangentConeAt p1.FeasSet loc) :
    p1.FeasPoint loc ∧ (∃ (lambda1 : τ → ℝ) (lambda2 : σ → ℝ),
      (gradient (fun m ↦ (p1.Lagrange_function m lambda1 lambda2)) loc = 0) ∧ (∀ j : σ, lambda2 j ≥ 0) ∧
      (∀ j : σ, (lambda2 j) * (p1.inequality_constraints j loc) = 0))

axiom first_order_neccessary_LICQ (p1 : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin n)) τ σ)
    (loc : EuclideanSpace ℝ (Fin n)) (hl : p1.Local_Minimum loc)
    (hf : Differentiable ℝ p1.objective)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p1 i) loc)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p1 i) loc)
    (hLICQ : p1.LICQ loc) (hdomain : p1.domain = univ) :
    p1.FeasPoint loc ∧ (∃ (lambda1 : τ → ℝ) (lambda2 : σ → ℝ),
      (gradient (fun m ↦ (p1.Lagrange_function m lambda1 lambda2)) loc = 0) ∧ (∀ j : σ, lambda2 j ≥ 0) ∧
      (∀ j : σ, (lambda2 j) * (p1.inequality_constraints j loc) = 0))
end Constrained_OptimizationProblem_property_finite_dimensional

section Constrained_OptimizationProblem_property_linear

open Constrained_OptimizationProblem Topology InnerProductSpace Set Filter Tendsto Matrix

variable {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
variable {τ σ : Finset ℕ} {p : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin n)) τ σ}

theorem LinearCQ_linear_constraint_eq (x : EuclideanSpace ℝ (Fin n)) (Lx : p.LinearCQ x) :
    ∀ i ∈ τ, ∃ a, ∃ b, (equality_constraints p i) = fun y ↦ (⟪a, y⟫_ℝ : ℝ) + b := by
  intro i hi
  simp [LinearCQ] at Lx
  obtain Lx := (Lx).1 i ((equality_constraint_active_set x) hi) hi
  exact (IsLinear_iff' _).mp Lx

theorem LinearCQ_linear_constraint_gradient_eq (x : EuclideanSpace ℝ (Fin n)) (Lx : p.LinearCQ x) :
    ∀ i ∈ τ, ∃ a, ∃ b, ((equality_constraints p i) = fun y ↦ (⟪a, y⟫_ℝ : ℝ) + b) ∧
    gradient (equality_constraints p i) x = a := by
  intro i hi
  obtain ⟨a, b, hab⟩ := LinearCQ_linear_constraint_eq x Lx i hi
  use a; use b; constructor; exact hab
  rw [hab]; rw [gradient_add_const]
  exact (gradient_of_inner_const x a).gradient

theorem LinearCQ_linear_constraint_ineq (x : EuclideanSpace ℝ (Fin n)) (Lx : p.LinearCQ x) :
    ∀ i ∈ p.active_set x ∩ σ, ∃ a, ∃ b, (inequality_constraints p i) = fun y ↦ (⟪a, y⟫_ℝ : ℝ) + b := by
  intro i hi
  simp only [LinearCQ] at Lx
  obtain Lx := (Lx).2 i hi
  exact (IsLinear_iff' _).mp Lx

theorem LinearCQ_linear_constraint_gradient_ineq (x : EuclideanSpace ℝ (Fin n)) (Lx : p.LinearCQ x) :
    ∀ i ∈ p.active_set x ∩ σ, ∃ a, ∃ b, ((inequality_constraints p i) = fun y ↦ (⟪a, y⟫_ℝ : ℝ) + b) ∧
    gradient (inequality_constraints p i) x = a := by
  intro i hi
  obtain ⟨a, b, hab⟩ := LinearCQ_linear_constraint_ineq x Lx i hi
  use a; use b; constructor; exact hab
  rw [hab]; rw [gradient_add_const]
  exact (gradient_of_inner_const x a).gradient

axiom Linear_linearized_feasible_directions_eq_posTangentCone
    (x : EuclideanSpace ℝ (Fin n)) (xf : x ∈ p.FeasSet)
    (conte : ∀ i ∈ τ, ContDiffAt ℝ (1 : ℕ) (equality_constraints p i) x)
    (conti : ∀ i ∈ σ, ContDiffAt ℝ (1 : ℕ) (inequality_constraints p i) x)
    (Lx : p.LinearCQ x) (hdomain : p.domain = univ) :
    p.linearized_feasible_directions x = posTangentConeAt p.FeasSet x

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
