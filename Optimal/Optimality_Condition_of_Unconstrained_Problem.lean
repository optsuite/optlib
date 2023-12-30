/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li,
-/
import Analysis.Calculation
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Function.Convex_Function

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x xm : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open Set InnerProductSpace

/-
  A vector d is considered a descent direction at a point x if the inner product of the gradient at
  x with d is less than zero
-/

def DescentDirection (d : E) (x : E) (_ : HasGradientAt f (f' x) x) : Prop :=
  inner (f' x) d < (0 : ℝ)

private lemma continuous (h : ContinuousAt f x) : ∀ ε > 0, ∃ δ > 0, ∀ (y : E), ‖y - x‖ < δ
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

private lemma expansion (hf : ∀ x : E, HasGradientAt f (f' x) x) (x p : E) :
    ∃ t : ℝ, t > 0 ∧ t < 1 ∧ f (x + p) = f x + inner (f' (x + t • p)) p := by
  let g := fun r : ℝ ↦ f (x + r • p)
  let g' := fun r : ℝ ↦ (inner (f' (x + r • p)) p : ℝ)
  have h1 : ∀ r , HasDerivAt g (g' r) r := by
    let h := fun r : ℝ ↦ x + r • p
    have : g = f ∘ h := by rfl
    rw [this]; intro r
    have : inner (f' (x + r • p)) p = toDual ℝ E (f' (x + r • p)) p := rfl
    simp; rw [this]; apply HasFDerivAt.comp_hasDerivAt
    · apply hasGradientAt_iff_hasFDerivAt.mp
      exact hf (x + r • p)
    · apply HasDerivAt.const_add
      have ht: HasDerivAt (fun x : ℝ ↦ x) 1 r := hasDerivAt_id' r
      have : HasDerivAt (fun r : ℝ ↦ r • p) ((1 : ℝ) • p) r := by
        apply HasDerivAt.smul_const ht p
      rw [one_smul] at this; exact this
  have e1 : f (x + p) = g 1 := by simp []
  have e2 : f x = g 0 := by simp []
  have e3 : ∀ t, inner (f' (x + t • p)) p = g' t := by simp []
  rw [e1, e2]
  have : ∃ c ∈ Set.Ioo 0 1, g' c = (g 1 - g 0) / (1 - 0) := by
    apply exists_hasDerivAt_eq_slope g g' (by norm_num)
    · have : ∀ x ∈ Icc 0 1, HasDerivAt g (g' x) x := by
        intro x _
        exact (h1 x)
      exact HasDerivAt.continuousOn this
    · simp [h1]
  rcases this with ⟨c, ⟨c1, c2⟩, h2⟩
  use c
  constructor; exact c1;
  constructor; exact c2;
  rw [e3 c]; simp [h2]

theorem optimal_no_descent_direction (hf : ∀ x : E, HasGradientAt f (f' x) x)
    (min : IsMinOn f univ xm) (hfc : ContinuousOn f' univ) :
    ∀ d : E, ¬ (DescentDirection d xm (hf xm)) := by
  intro d
  by_contra h
  have : ∃ t : ℝ , f (xm + t • d) < f xm := by
    have h₁ : ∃ T : ℝ , T > 0 ∧ (∀ a ∈ Icc (- T) T, inner (f' (xm + a • d)) d < (0 : ℝ)) := by
      let g := fun r : ℝ ↦ (inner (f' (xm + r • d)) d : ℝ)
      have hg0 : g 0 = inner (f' xm) d := by simp
      have hc : ContinuousOn g univ := by
        simp
        apply ContinuousOn.inner
        · apply ContinuousOn.comp hfc
          · apply ContinuousOn.add continuousOn_const
            apply ContinuousOn.smul continuousOn_id continuousOn_const
          · simp only [maps_univ_to, mem_univ, forall_const]
        · exact continuousOn_const
      have hu : ∃ u < (0 : ℝ) , inner (f' xm) d ≤  u := by
        use (inner (f' xm) d / 2)
        rw [DescentDirection] at h
        constructor
        · linarith
        · rw [le_div_iff (by norm_num)]; linarith
      rcases hu with ⟨u, ⟨hu1, hu2⟩⟩
      rw [← hg0] at hu2
      have hc' : ∃ T, T > 0 ∧ (∀ a ∈ Icc (- T) T, g a < 0) := by
        have : univ ∈ nhds (0 : ℝ) := by simp
        rcases continuous (ContinuousOn.continuousAt hc this) with h1
        specialize h1 (- u / 2) (by linarith)
        rcases h1 with ⟨T, ⟨hT1, hT2⟩⟩
        use T / 2; constructor
        · linarith
        · intro a ha
          have : ‖a - 0‖ < T := by
            simp; rw [abs_lt]; simp at ha
            rcases ha with ⟨ha1, ha2⟩
            constructor; linarith; linarith
          specialize hT2 a this
          simp at hT2
          rw [abs_lt] at hT2
          rcases hT2 with ⟨hs1, hs2⟩
          rw [sub_lt_iff_lt_add] at hs2
          apply lt_trans hs2
          · linarith
      rcases hc' with ⟨T, ⟨hT1, hT2⟩⟩
      use T
    rcases h₁ with ⟨T, ⟨hT1,hT2⟩⟩
    have h₂ : ∃ t1 : ℝ, t1 ≥ -T ∧ t1 ≤ T ∧ f (xm + T • d) =
        f xm + inner (f' (xm + t1 • d)) (T • d) := by
      rcases (expansion hf xm (T • d)) with ⟨ts,⟨ts1,⟨ts2,ts3⟩⟩⟩
      use (ts • T)
      constructor
      · simp; apply le_trans
        · show -T ≤ 0
          linarith
        · simp [hT1]; linarith
      · constructor
        · simp [hT1]; linarith
        · rw [smul_assoc]; exact ts3
    rcases h₂ with ⟨t1, ⟨ht1, ⟨ht2, ht3⟩⟩⟩
    use T; rw [ht3]; simp; rw [inner_smul_right]
    simp at ht1
    exact mul_neg_of_pos_of_neg hT1 (hT2 t1 ⟨ht1, ht2⟩)
  rcases this with ⟨t, ht⟩
  have : f (xm + t • d) ≥ f xm := min trivial
  linarith

theorem first_order_unconstrained (hf : ∀ x : E, HasGradientAt f (f' x) x) (min : IsMinOn f univ xm)
    (hfc : ContinuousOn f' univ) : f' xm = 0 := by
  by_contra h
  have h1: DescentDirection (-f' xm) xm (hf xm) := by
    rw [DescentDirection, inner_neg_right, Left.neg_neg_iff]
    rw [real_inner_self_eq_norm_sq]
    simp [h]
  exact (optimal_no_descent_direction hf min hfc (- f' xm)) h1

theorem first_order_convex (hf : ∀ x : E, HasGradientAt f (f' x) x) (hcon : ConvexOn ℝ univ f)
    (hfm : f' xm = 0) : IsMinOn f univ xm := by
  have : ∀ y , f y ≥ f xm + inner (f' xm) (y - xm) := by
    intro y
    apply first_order_condition' (hf xm) hcon (by trivial)
    · trivial
  intro y
  dsimp; specialize this y
  rw [hfm, inner_zero_left, add_zero] at this
  exact fun _ => this

theorem first_order_convex_iff (hf : ∀ x : E, HasGradientAt f (f' x) x) (hcon : ConvexOn ℝ univ f)
    (hfc : ContinuousOn f' univ) :
    IsMinOn f univ xm ↔ f' xm = 0 := by
  constructor
  · intro hmin
    exact first_order_unconstrained hf hmin hfc
  · intro hgrad
    apply first_order_convex hf hcon hgrad
