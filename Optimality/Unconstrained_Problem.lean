/-
Copyright (c) 2024 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li,
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Positive
import Function.Convex_Function
import Optimality.Optimality_Condition_of_Unconstrained_Problem

/-!
# Unconstrained_Problem

## Main results

This file contains the following parts of unconstrained optimization problem.
* the definition of an unconstrained optimization prblem
* the definition of a local minima, global minima, strict local minima, stationary point
* the first order necessary condition of unconstrained optimization problem
* the second order necessary and sufficient condition of unconstrained optimization problem
* the convexity of a function implies local minima is global minima
-/

section additional_definitions

variable {E : Type _} [NormedAddCommGroup E] [CompleteSpace E] [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

/-
  the definition of a self-adjoint operator which is strict positive.
-/
def ContinuousLinearMap.IsStrictPositive (T : E →L[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x ≠ 0, 0 < T.reApplyInnerSelf x

end additional_definitions

section optimization

variable {E : Type _} [NormedAddCommGroup E] [CompleteSpace E] [InnerProductSpace ℝ E]

open Set

/-
  the definition of an unconstrained optimization problem.
  The objective function is a function from a Hilbert space to ℝ.
-/
structure Unconstrained_OptimizationProblem (E : Type _) :=
(objective : E → ℝ)

namespace Unconstrained_OptimizationProblem

open Unconstrained_OptimizationProblem

variable (p : Unconstrained_OptimizationProblem E)

/-
  A point x₁ is a global minimizer if f x₁ ≤ f x for all x
-/
def Global_Minima (point : E) : Prop :=
  IsMinOn p.objective univ point

/-
  A point x₁ is a local minimizer if there is a neighborhood B of x₁
  such that f x₁ ≤ f x for all x ∈ B .
-/
def Local_Minima (point : E) : Prop :=
  IsLocalMinOn p.objective univ point

/-
  A point x₁ is a strict local minimizer (also called a strong local minimizer) if there is a
  neighborhood B of x∗ such that f x₁ < f x for all x ∈ N with x ≠ x₁.
-/
def Strict_Local_Minima (point : E) : Prop :=
  ∃ ε > 0, ∀ y, y ∈ Metric.ball point ε → y ≠ point → p.objective point > p.objective y

/-
  x is a stationary point if f i differentiable and ∇ f (x) = 0
-/
def Stationary_Point (point : E) : Prop :=
  Differentiable ℝ p.objective ∧ gradient p.objective point = (0 : E)

/-
  A point x₁ is a global maximizer if f x₁ ≥ f x for all x
-/
def Global_Maxima (point : E) : Prop :=
  IsMaxOn p.objective univ point

/-
  A point x₁ is a local maximizer if there is a neighborhood B of x₁
  such that f x₁ ≥ f x for all x ∈ B .
-/
def Local_Maxima (point : E) : Prop :=
  IsLocalMaxOn p.objective univ point

end Unconstrained_OptimizationProblem

section First_Order_Optimality

open Topology InnerProductSpace Set Filter Tendsto

variable (p : Unconstrained_OptimizationProblem E) (loc : E)

/- any global minima must be local minima -/
lemma global_minima_is_local_minima
    (h : p.Global_Minima loc) : p.Local_Minima loc := by
  rw [Unconstrained_OptimizationProblem.Local_Minima]
  rw [Unconstrained_OptimizationProblem.Global_Minima] at h
  exact IsMinOn.localize h

/-
If the function f is first-order continuously differentiable, then
the gradient of f is continuous.
-/
lemma gradient_continuous_of_contdiff {x : E} {ε : ℝ} (f : E → ℝ)
    (he : ε > 0) (hf : ContDiffOn ℝ 1 f (Metric.ball x ε)) :
    ContinuousAt (fun x ↦ gradient f x) x := by
  let s := Metric.ball x ε
  have h : ContDiffAt ℝ 1 f x := by
    apply ContDiffOn.contDiffAt hf
    rw [mem_nhds_iff]; use s
    exact ⟨Eq.subset rfl, ⟨Metric.isOpen_ball, Metric.mem_ball_self he⟩⟩
  rw [contDiffAt_one_iff] at h
  rcases h with ⟨f', ⟨u, ⟨hu1, ⟨hu2, hu3⟩⟩⟩⟩
  have : Set.EqOn (fun y ↦ (LinearIsometryEquiv.symm (toDual ℝ E)) (f' y))
      (fun y ↦ gradient f y) u := by
    intro z hz; dsimp
    specialize hu3 z hz
    rw [hasFDerivAt_iff_hasGradientAt] at hu3
    have : HasGradientAt f (gradient f z) z :=
      DifferentiableAt.hasGradientAt hu3.differentiableAt
    exact HasGradientAt.unique hu3 this
  have hcon1 : ContinuousOn (fun y ↦ (LinearIsometryEquiv.symm (toDual ℝ E)) (f' y)) u :=
    Continuous.comp_continuousOn (LinearIsometryEquiv.continuous _) hu2
  rw [(continuousOn_congr this)] at hcon1
  apply ContinuousOn.continuousAt hcon1 hu1

/-
If x∗ is a local minimizer and f is continuously differentiable in an open neighborhood
of x∗, then ∇ f (x∗) = 0 .
Numerical Optimization, Nocedal & Wright, Theorem 2.2
-/
theorem first_order_unconstrained_necessary
    (h : ∃ ε > 0, ContDiffOn ℝ 1 p.objective (Metric.ball loc ε))
    (hl : p.Local_Minima loc) :
    gradient p.objective loc = (0 : E) := by
  by_contra hn; push_neg at hn
  rw [Unconstrained_OptimizationProblem.Local_Minima] at hl
  rw [IsLocalMinOn, IsMinFilter, eventually_iff_exists_mem] at hl
  rcases hl with ⟨v, ⟨hv, hv2⟩⟩
  rw [nhdsWithin] at hv; simp at hv;
  have hy : ∃ s > 0, (Metric.ball loc s) ⊆ v := by
    exact Metric.mem_nhds_iff.mp hv
  rcases hy with ⟨s, ⟨hs, hy⟩⟩
  rcases h with ⟨ε, ⟨he, hd⟩⟩
  let rad := min s ε
  have pos : 0 < rad := by simp [hs, he]
  have hd : ContDiffOn ℝ 1 p.objective (Metric.ball loc rad) :=
    hd.mono (Metric.ball_subset_ball (min_le_right s ε))
  have hy : Metric.ball loc rad ⊆ v :=
    Set.Subset.trans (Metric.ball_subset_ball (min_le_left s ε)) hy
  let d := (- gradient p.objective loc)
  let g : ℝ → ℝ := fun t ↦ inner d (gradient p.objective (loc + t • d))
  have hg : g 0 < 0 := by
    simp; by_contra hh; push_neg at hh;
    rw [real_inner_self_nonpos] at hh; exact hn hh
  let rad1 := rad / (2 * ‖d‖)
  have t1 : ‖d‖ ≠ 0 := by simp [hn]
  have t2 : d ≠ 0 := by simp [hn]
  have pos1 : 0 < rad1 := by
    apply div_pos pos
    apply mul_pos; simp; exact norm_pos_iff.mpr t2
  have hin : ∀ t ∈ Icc 0 rad1, (loc + t • d) ∈ Metric.ball loc rad := by
    intro t ht; rcases ht with ⟨ht1, ht2⟩
    rw [Metric.mem_ball, dist_eq_norm, ← add_sub_cancel' loc (t • d)]
    rw [add_sub_cancel', add_sub_cancel', norm_smul, t.norm_eq_abs, abs_of_nonneg ht1]
    apply lt_of_lt_of_le'
    · show rad / 2 < rad
      apply half_lt_self
      simp [hs, he]
    · calc _ ≤ rad1 * ‖d‖ := (mul_le_mul_right (norm_pos_iff.mpr t2)).mpr ht2
           _ = rad * (‖d‖ * ‖d‖⁻¹) / 2 := by field_simp; ring_nf
           _ = rad / 2 := by rw [mul_inv_cancel t1, mul_one]
  have hgg : ∃ T ∈ Ioc 0 rad1, ∀ t ∈ Icc 0 T, g t < 0 := by
    have hcon : ContinuousAt g 0 := by
      simp
      apply ContinuousAt.neg
      apply ContinuousAt.inner continuousAt_const
      have : (fun u => gradient p.objective u) ∘ (fun u => loc + - (u • gradient p.objective loc))
          = (fun (t : ℝ) => gradient p.objective (loc + - (t • gradient p.objective loc))) := by
        ext; simp
      have t1 : ContinuousAt (fun u => gradient p.objective u)
          (loc + - ((0 : ℝ) • gradient p.objective loc)) := by
        rw [zero_smul, ← sub_eq_add_neg, sub_zero]
        let g : E → E := fun u => gradient p.objective u
        have : ContinuousAt g loc := by
          exact gradient_continuous_of_contdiff p.objective pos hd
        exact this
      have t2 : ContinuousAt (fun (u : ℝ) => loc + - (u • gradient p.objective loc)) 0 := by
        apply continuousAt_const.add
        apply (ContinuousAt.smul continuous_id'.continuousAt continuousAt_const).neg
      rw [← this]
      exact ContinuousAt.comp t1 t2
    have hcon' : ∀ ε > 0, ∃ δ > 0, ∀ (y : ℝ), ‖y - 0‖ < δ → ‖g y - g 0‖ < ε := continuous hcon
    rcases hcon' (- (g 0) / 2) (by linarith) with ⟨δ, ⟨hδ1, hδ2⟩⟩
    use min (δ / 2) rad1
    constructor
    · constructor
      · rw [lt_min_iff]; constructor <;> linarith
      · apply min_le_right
    · intros t ht
      have th1 : ‖t - 0‖ < δ := by
        rw [Real.norm_eq_abs, sub_zero, abs_lt]
        rcases ht with ⟨ht1, ht2⟩; rw [le_min_iff] at ht2
        exact ⟨by linarith [ht1], by linarith [(ht2).1]⟩
      have th2 : ‖g t - g 0‖ < - (g 0) / 2 := hδ2 t th1
      have : g t - g 0 < - (g 0) / 2 := by
        rw [Real.norm_eq_abs, abs_lt] at th2; exact th2.2
      have : g t < g 0 / 2 := by linarith
      apply lt_trans this (by linarith)
  rcases hgg with ⟨T, ⟨⟨hT1, hT2⟩, hg'⟩⟩
  have hcc : ∃ (a : ℝ), a ∈ Ioc 0 T ∧ loc + a • d ∈ v := by
    use T / 2;
    constructor
    · constructor <;> linarith
    · have : loc + (T / 2) • d ∈ Metric.ball loc rad := by
        apply hin; constructor <;> linarith
      exact hy this
  rcases hcc with ⟨a, ⟨⟨ha1, ha2⟩, hcc⟩⟩
  have : p.objective (loc + a • d) < p.objective loc := by
    let p' := fun t ↦ gradient p.objective t
    have : ∀ y ∈ Metric.closedBall loc ‖a • d‖, HasGradientAt p.objective (p' y) y := by
      intro y hy
      have hh : y ∈ Metric.ball loc rad := by
        rw [Metric.mem_ball];
        rw [Metric.mem_closedBall, norm_smul, a.norm_eq_abs, abs_of_pos ha1] at hy;
        have t3 : ‖gradient p.objective loc‖ ≠ 0 := by simp [hn]
        calc dist y loc ≤ rad1 * ‖d‖ := by
                apply le_trans hy
                rw [mul_le_mul_right (norm_pos_iff.mpr t2)]
                exact le_trans ha2 hT2
             _ = rad / 2 := by field_simp; ring_nf;
             _ < rad := by linarith
      have : DifferentiableAt ℝ p.objective y := by
        apply DifferentiableOn.differentiableAt (hd.differentiableOn (by norm_num))
        rw [mem_nhds_iff]; use Metric.ball loc rad;
        exact ⟨Eq.subset rfl, ⟨Metric.isOpen_ball, hh⟩⟩
      exact this.hasGradientAt
    have hh : ∃ t : ℝ, t > 0 ∧ t < 1 ∧ p.objective (loc + a • d) =
        p.objective loc + inner (p' (loc + t • (a • d))) (a • d) := by
      exact general_expansion _ _ this
    rcases hh with ⟨t, ⟨ht1, ht2, hh⟩⟩
    have hff : inner (p' (loc + t • a • d)) (a • d) < (0 : ℝ) := by
      have : inner (p' (loc + t • a • d)) d = g (t • a) := by
        dsimp [g]; rw [smul_smul, real_inner_comm]
      rw [inner_smul_right, this, mul_comm]
      apply mul_neg_of_neg_of_pos _ ha1
      apply hg' (t • a)
      constructor <;> simp [ha1, ha2, ht1, ht2]
      linarith
      rw [← one_mul T]; apply mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    rw [hh, add_lt_iff_neg_left]; exact hff
  have : p.objective (loc + a • d) ≥ p.objective loc := by exact hv2 (loc + a • d) hcc
  linarith

/-
When f is convex, any local minimizer x∗ is a global minimizer of f.
Numerical Optimization, Nocedal & Wright, Theorem 2.5
-/
theorem convex_local_minima_is_global_minima (h : ConvexOn ℝ univ p.objective)
    (hf : ContDiff ℝ 1 p.objective) (hl : p.Local_Minima loc):
    p.Global_Minima loc := by
  have : gradient p.objective loc = (0 : E) := by
    apply first_order_unconstrained_necessary p loc _ hl
    exact ⟨1, by norm_num, ContDiff.contDiffOn hf⟩
  have hg : HasGradientAt p.objective ((fun t ↦ gradient p.objective t) loc) loc :=
    (hf.differentiable (by norm_num) _).hasGradientAt
  have mini : ∀ y, p.objective loc ≤ p.objective y := by
    intro y
    convert first_order_condition' hg h (by trivial) (by trivial)
    rw [this]; simp
  exact isMinOn_univ_iff.mpr mini

theorem convex_local_minima_is_global_minima' (h : ConvexOn ℝ univ p.objective)
    (hf : ∃ ε > 0, ContDiffOn ℝ 1 p.objective (Metric.ball loc ε)) (hl : p.Local_Minima loc) :
    p.Global_Minima loc := by
  have : gradient p.objective loc = (0 : E) := by
    apply first_order_unconstrained_necessary p loc hf hl
  have hg : HasGradientAt p.objective ((fun t ↦ gradient p.objective t) loc) loc := by
    rcases hf with ⟨e, ⟨he, hdf⟩⟩
    have hdf' : DifferentiableAt ℝ p.objective loc := by
      apply DifferentiableOn.differentiableAt (hdf.differentiableOn (by norm_num))
      exact Metric.ball_mem_nhds loc he
    exact hdf'.hasGradientAt
  have mini : ∀ y, p.objective loc ≤ p.objective y := by
    intro y
    convert first_order_condition' hg h (by trivial) (by trivial)
    rw [this]; simp
  exact isMinOn_univ_iff.mpr mini

/-
When f is convex and differentiable, then any stationary point x∗ is a global minimizer of f.
Numerical Optimization, Nocedal & Wright, Theorem 2.5
-/
theorem convex_stationary_point_is_global_minima
    (h : ConvexOn ℝ univ p.objective) (hs : p.Stationary_Point loc) :
    p.Global_Minima loc := by
  rcases hs with ⟨hdf, hg0⟩
  have mini : ∀ y, p.objective loc ≤ p.objective y := by
    intro y
    convert first_order_condition' (hdf loc).hasGradientAt h (by trivial) (by trivial)
    rw [hg0]; simp
  exact isMinOn_univ_iff.mpr mini

end First_Order_Optimality

end optimization
