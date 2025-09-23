/-
Copyright (c) 2023 Chenyi Li, Ziyu Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yuxuan Wu, Junda Ying,
         Hongjia Chen, Shengyang Xu, Zaiwen Wen
-/
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Pow
import Optlib.Optimality.OptimalityConditionOfUnconstrainedProblem
import Optlib.Differential.Lemmas

/-!
# Lsmooth

## Main results

This file mainly concentrates on the properties of the L smooth function.

The main theorem is given as:

* We prove the second order upper bound theorem, i.e.

  Let f be a Lipschitz smooth function defined on a convex set s. f is l-Lipschitz smooth on s.

    `f(y) ≤ f(x) + ∇ f(x)^T (y-x) + 1 / 2 * ‖y - x‖ ^ 2 ∀ x, y ∈ s.`

* We prove the properties of a convex l-Lipschitz smooth function

  Let f be a differentiable convex function defined on ℝ^n, then the following statement is equivalent

    (a) `f` is `l` - Lipschitz smooth on ℝ^n.

    (b)` g(x) = 1 / 2 * ‖x‖ ^ 2 - f(x)`  is convex .

    (c) `(∇ f(x) - ∇ f(y)) ^ T(x- y) ≥ 1 / l * ‖∇ f(x) - ∇ f(y)‖ ^ 2 ∀ x, y ∈ ℝ^n.`

* Some relative lemmas are also contained

-/

-- section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open InnerProductSpace  Set

variable {f : E → ℝ} {a : ℝ} {f' : E → (E →L[ℝ] ℝ)} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {l : NNReal}

theorem lipschitz_continuous_upper_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E → (E →L[ℝ] ℝ)} {l : NNReal}
    (hd : ∀ x : E, HasFDerivAt f (f' x) x)
    (hl : LipschitzWith l f') :
    ∀ (x y : E), f y ≤ f x + (f' x) (y - x)
      + l / 2 * ‖y - x‖ ^ 2 := by
  intro x y; rw [lipschitzWith_iff_norm_sub_le] at hl
  let g := fun t : ℝ ↦ f (x + t • (y - x))
  let g' := fun t : ℝ ↦ (f' (x + t • (y - x)) (y - x))
  let LL := l * ‖y - x‖ ^ 2
  obtain gderiv : ∀ t₀ : ℝ , HasDerivAt g (g' t₀) t₀ :=
    deriv_function_comp_segment x y hd
  have glip : ∀ u v : ℝ, ‖g' u - g' v‖  ≤
      l * ‖y - x‖ ^ 2 * ‖u - v‖ := by
    intro u v
    calc
      _ ≤ ‖f' (x + u • (y - x)) - f' (x + v • (y - x))‖ * ‖y - x‖ :=
          ContinuousLinearMap.le_opNorm _ (y - x)
      _ ≤ l * ‖x + u • (y - x) - (x + v • (y - x))‖ * ‖y - x‖ :=
          mul_le_mul_of_nonneg (hl _ _) (le_refl _) (norm_nonneg _) (norm_nonneg _)
      _ = l * ‖y - x‖ ^ 2 * ‖u - v‖ := by
        rw [← sub_sub, add_sub_right_comm, sub_self, zero_add, ← sub_smul, norm_smul]; ring_nf
  let u := fun t₀ : ℝ ↦ g 0 + t₀ * (g' 0) +  t₀ ^ 2 * (LL / 2)
  let u' := fun t : ℝ ↦ g' 0 + LL * t
  have hderiv : ∀ t, HasDerivAt u (u' t) t := by
    intro t
    apply HasDerivAt.add
    · apply HasDerivAt.const_add
      · apply hasDerivAt_mul_const
    · have : l * ‖y - x‖ ^ 2 * t = (2 * t) * (l * ‖y - x‖ ^ 2 / 2) := by field_simp
      rw [this]; apply HasDerivAt.mul_const
      obtain hd := HasDerivAt.pow (n := 2) (hasDerivAt_id' t)
      simp at hd; exact hd
  suffices g 1 ≤ u 1 by
    simp [u, g, LL, g'] at this
    rw [map_sub]; linarith
  apply image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 2)
  · exact HasDerivAt.continuousOn (fun x _ ↦ gderiv x)
  · exact fun t _ ↦ HasDerivAt.hasDerivWithinAt (gderiv t)
  · simp [u]
  · exact HasDerivAt.continuousOn (fun x _ ↦ hderiv x)
  · exact fun t _ ↦ HasDerivAt.hasDerivWithinAt (hderiv t)
  · intro t ht
    simp [u', LL]; simp at ht
    apply tsub_le_iff_left.mp
    apply le_trans (le_abs_self _)
    convert (glip t 0); simp; rw [abs_of_nonneg ht.1]
  simp

-- end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open InnerProductSpace  Set

variable {f : E → ℝ} {a : ℝ} {f' : E → E} {l : NNReal}

theorem lower_to_lipschitz
    (h₂ : ∀ x y : E, ⟪f' x - f' y, x - y⟫_ℝ ≥ (1 / (l : ℝ)) * ‖f' x - f' y‖ ^ 2)
    (hl : l > 0) : LipschitzWith l f' := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  have H₁ : (1 / l * ‖f' x - f' y‖) * ‖f' x - f' y‖ ≤ (1 / l * ‖f' x - f' y‖) * (l * ‖x - y‖) := by
    calc
    _ = 1 / l * ‖f' x - f' y‖ ^ 2 := by
      simp
      rw [mul_assoc, ← pow_two (‖f' x - f' y‖)]
    _ ≤ ‖f' x - f' y‖ * ‖x - y‖ := by
      apply le_trans (h₂ x y)
      apply real_inner_le_norm
    _ = (1 / l * ‖f' x - f' y‖) * (l * ‖x - y‖) := by
      field_simp
  have H₂ : 1 / l > 0 := by
    apply one_div_pos.mpr hl
  cases lt_or_ge 0 (‖f' x - f' y‖)
  case inl h =>
    apply le_of_mul_le_mul_left H₁
    apply mul_pos _ h
    · simp [hl]
  case inr h =>
    apply le_trans h
    apply mul_nonneg
    · simp
    apply norm_nonneg _

end
section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open InnerProductSpace Set

variable {f : E → ℝ} {a : ℝ} {f' : E → E} {xm : E} {l : NNReal}

theorem lipschitz_continuos_upper_bound'
    (h₁ : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁) (h₂ : LipschitzWith l f') :
    ∀ x y : E, f y ≤ f x + ⟪f' x, y - x⟫_ℝ + l / 2 * ‖y - x‖ ^ 2 := by
  intro x y
  rw [lipschitzWith_iff_norm_sub_le] at h₂
  let g := fun x ↦ (toDual ℝ E) (f' x)
  have h' : ∀ x : E, HasFDerivAt f (g x) x := h₁
  have equiv : ∀ x y : E, ⟪f' x, y - x⟫_ℝ = (g x) (y - x) := by
    intro x y
    rw [InnerProductSpace.toDual_apply]
  have h₂' : LipschitzWith l g := by
    simp only [g]
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    have h1 : ∀ x : E, ‖(toDual ℝ E) x‖ =‖x‖ := by
      simp [LinearIsometryEquiv.norm_map]
    have : ‖(toDual ℝ E) (f' x) - (toDual ℝ E) (f' y)‖ = ‖f' x - f' y‖ := by
      rw [← map_sub (toDual ℝ E) (f' x) (f' y)]
      exact h1 (f' x - f' y)
    rw [this]
    exact h₂ x y
  rw [equiv]
  exact lipschitz_continuous_upper_bound h' h₂' x y

theorem lipschitz_minima_lower_bound (h₁ : ∀ x : E, HasGradientAt f (f' x) x)
    (h₂ : LipschitzWith l f') (min: IsMinOn f Set.univ xm) (hl : l > 0):
    ∀ x : E, 1 / (2 * l) * ‖f' x‖ ^ 2 ≤ f x - f xm := by
  intro x
  rw [IsMinOn, IsMinFilter] at min
  simp at min
  let y : E := x - ((1 : ℝ) / l : ℝ) • (f' x)
  have eq : f xm ≤ f x - 1 / (2 * l) * ‖f' x‖ ^ 2 := by
    calc
      _ ≤ f y := by apply min
      _ ≤ f x + ⟪f' x, y - x⟫_ℝ + l / 2 * ‖y - x‖ ^ 2 := by
        apply lipschitz_continuos_upper_bound' h₁ h₂
      _ = f x - 1 / (2 * l) * ‖f' x‖ ^ 2 := by
        rw [add_assoc]; rw [sub_eq_add_neg (f x), add_left_cancel_iff.2]
        have hyx : y - x = - ((1 : ℝ) / (l : ℝ)) • f' x := by simp [y]
        have hl0 : (l : ℝ) ≠ 0 := by exact ne_of_gt hl
        have hα : 0 ≤ (1 : ℝ) / (l : ℝ) := by exact one_div_nonneg.mpr (le_of_lt hl)
        simp [hyx, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul]
        field_simp [hl0]; ring_nf
  linarith

end

section Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {a : ℝ} {f': E → E} {xm : E}
variable {x y : E} {s v : Set E} {l : NNReal}

open Set

theorem lipschitz_to_lnorm_sub_convex (hs : Convex ℝ s)
    (h₁ : ∀ x ∈ s, HasGradientAt f (f' x) x) (h₂ : LipschitzOnWith l f' s) (_ : l > 0) :
    ConvexOn ℝ s (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) := by
  rw [lipschitzOnWith_iff_norm_sub_le] at h₂
  let g' : E → E := fun x ↦ l.1 • x - f' x
  have H₂ : ∀ x ∈ s, ∀ y ∈ s, ⟪g' x - g' y, x - y⟫_ℝ ≥ (0 : ℝ) := by
    intro x hx y hy
    calc
    _ = l.1 * (⟪x - y, x - y⟫_ℝ) - ⟪f' x - f' y, x - y⟫_ℝ := by
      simp [g']
      rw [← sub_add, sub_right_comm, sub_add, inner_sub_left, ← smul_sub, inner_smul_left]
      simp only [conj_trivial]
    _ = l * ‖x - y‖ ^ 2 - ⟪f' x - f' y, x - y⟫_ℝ := by
      simp; left
      apply real_inner_self_eq_norm_sq
    _ ≥ l * ‖x - y‖ ^ 2 - ‖f' x - f' y‖ * ‖x - y‖ := by
      apply add_le_add; linarith
      simp
      apply real_inner_le_norm
    _ ≥ l * ‖x - y‖ ^ 2 - l * ‖x - y‖ ^ 2 := by
      simp
      rw [pow_two, ← mul_assoc]
      apply mul_le_mul (h₂ hx hy); linarith; apply norm_nonneg
      apply mul_nonneg _ (norm_nonneg _)
      simp
    _ = 0 := by simp
  have H₃ : ∀ x ∈ s, HasGradientAt (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) (g' x) x := by
    intro x hx
    have u₂ := HasGradientAt.const_smul (gradient_norm_sq_eq_two_self x) ((l / (2 : ℝ)) : ℝ)
    have u := u₂.add (HasGradientAt.neg (h₁ x hx))
    have l₁ : (fun x ↦ l / 2 * ‖x‖ ^ 2 + -f x) = (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) := by
      ext; ring
    have l₂ : (l.1 / 2) • (2 : ℝ)  • x + -f' x = g' x := by
      simp [g']; rw [smul_smul, ← sub_eq_add_neg]; ring_nf
    rw [← l₁, ← l₂]
    apply u
  apply monotone_gradient_convex' hs
  apply H₃
  intro x hx y hy
  exact H₂ x hx y hy

theorem convex_to_lower {l : ℝ} (h₁ : ∀ x : E, HasGradientAt f (f' x) x)
    (h₂ : ConvexOn ℝ Set.univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x)) (lp : l > 0)
    (hfun: ConvexOn ℝ Set.univ f) (x : E) (y : E) :
    ⟪f' x - f' y, x - y⟫_ℝ ≥ 1 / l * ‖f' x - f' y‖ ^ 2 := by
  rw [ConvexOn] at hfun
  let fs : E → (E → ℝ) := fun s => (fun x => f x - ⟪f' s, x⟫_ℝ)
  have hfunconvex : ∀ s : E, ConvexOn ℝ Set.univ (fs s) := by
    intro s
    rw [ConvexOn]
    simp
    constructor
    · apply hfun.1
    · intro x₁ y₁ a b ha hb hab
      have : f (a • x₁ + b • y₁) ≤ a * f x₁ + b * f y₁ := by
        apply hfun.2 _ _ ha hb hab
        simp; simp
      simp [fs]
      apply le_trans this
      apply Eq.ge ; ring_nf
      rw[inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
  let fs' : E → (E → E) := fun s => (fun z ↦ f' z - f' s)
  have hfconx₁:  ∀ s x : E, HasGradientAt (fs s) (fs' s x) x := by
    intro s z
    apply HasGradientAt.sub
    · rcases h₁ z with _
      apply h₁
    · apply gradient_of_inner_const z (f' s)
  have hfy₁:  ∀ x : E, HasGradientAt (fs y) (fs' y x) x := hfconx₁ y
  have hfx₁:  ∀ x₁ : E, HasGradientAt (fs x) (fs' x x₁) x₁ := hfconx₁ x
  rw [ConvexOn] at h₂
  let gs : E → (E → ℝ) := fun s ↦ (fun z ↦ l / 2 * ‖z‖ ^ 2 - (fs s) z)
  have hgxconvex : ∀ s : E, ConvexOn ℝ Set.univ (gs s) := by
    intro s; rw [ConvexOn]
    constructor
    · apply hfun.1
    · intro x₁ hhx₁ y₁ hhy₁ a b ha hb hab
      have h₂' : l / 2 * ‖a • x₁ + b • y₁‖ ^ 2 - f (a • x₁ + b • y₁) ≤
          a • (l / 2 * ‖x₁‖ ^ 2 - f x₁) + b • (l / 2 * ‖y₁‖ ^ 2 - f y₁) := by
        apply h₂.2 hhx₁ hhy₁ ha hb hab
      simp only [smul_eq_mul, gs, fs]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      calc
        _ = (l / 2) * ‖a • x₁ + b • y₁‖ ^ 2 - f (a • x₁ + b • y₁) +
            (a * ⟪f' s, x₁⟫_ℝ + b * ⟪f' s, y₁⟫_ℝ) := by ring_nf
        _ ≤ a • (l / 2 * ‖x₁‖ ^ 2 - f x₁) + b • (l / 2 * ‖y₁‖ ^ 2 - f y₁) +
            (a * ⟪f' s, x₁⟫_ℝ + b * ⟪f' s, y₁⟫_ℝ) := by apply add_le_add_right h₂'
        _ = a • (l / 2 * ‖x₁‖ ^ 2 - (f x₁ - ⟪f' s, x₁⟫_ℝ)) + b •
            (l / 2 * ‖y₁‖ ^ 2 - (f y₁ - ⟪f' s, y₁⟫_ℝ)) := by simp; ring_nf
  let gs' := fun s ↦ (fun z ↦ l • z - (fs' s z))
  have hgx₁ :  ∀ s x : E, HasGradientAt (gs s) ((gs' s) x) x := by
    intro s z
    apply HasGradientAt.sub (gradient_of_const_mul_norm l z) (hfconx₁ s z)
  have hgx₂ : ∀ s z₁ z₂ : E, (gs s) z₁ + ⟪gs' s z₁, z₂ - z₁⟫_ℝ ≤ gs s z₂ := by
    intro s z₁ z₂
    apply Convex_first_order_condition' (hgx₁ s z₁) (hgxconvex s)
    · simp only [Set.mem_univ]
    · simp only [Set.mem_univ]
  have hfx₂ : ∀ (s x y₁ : E), (fs s) y₁ ≤ fs s x +
      ⟪fs' s x, y₁ - x⟫_ℝ + l / 2 * ‖y₁ - x‖ ^ 2 := by
    intro s z₁ z₂
    simp only [fs, fs']
    rcases hgx₂ s z₁ z₂ with hgx₂'
    have t₇ : gs s z₁ =  l / 2 * ‖z₁‖ ^ 2 - fs s z₁ := by rfl
    have t₈ : gs s z₂ =  l / 2 * ‖z₂‖ ^ 2 - fs s z₂ := by rfl
    have t₉ : gs' s z₁ = l • z₁ - fs' s z₁ := by rfl
    rw [t₇, t₈, t₉] at hgx₂'
    have t₁₀ : fs s z₂ + (l / 2 * ‖z₁‖ ^ 2 - fs s z₁ + ⟪l • z₁ - fs' s z₁, z₂ - z₁⟫_ℝ)
        ≤ l / 2 * ‖z₂‖ ^ 2 := by
      apply add_le_of_le_sub_left hgx₂'
    have t₁₁ : fs s z₂ ≤ l / 2 * ‖z₂‖ ^ 2 - (l / 2 * ‖z₁‖ ^ 2 - fs s z₁ +
        ⟪l • z₁ - fs' s z₁, z₂ - z₁⟫_ℝ) := by
      rw [add_comm] at t₁₀
      apply le_sub_left_of_add_le t₁₀
    rw [← sub_add (l / 2 * ‖z₁‖ ^ 2) _ _] at t₁₁
    calc
      _ ≤ l / 2 * ‖z₂‖ ^ 2 - (l / 2 * ‖z₁‖ ^ 2 - f z₁ +
          ⟪f' s, z₁⟫_ℝ + ⟪l • z₁ - fs' s z₁, z₂ - z₁⟫_ℝ) := by apply t₁₁
      _ = l / 2 * ‖z₂‖ ^ 2 -(l / 2 * ‖z₁‖ ^ 2 - f z₁ + ⟪f' s, z₁⟫_ℝ +
        (l * (⟪z₁, z₂⟫_ℝ - ‖z₁‖ ^ 2) - ⟪f' z₁ - f' s, z₂ - z₁⟫_ℝ)) := by
        rw [inner_sub_left, inner_smul_left]
        simp; rw [inner_sub_right, real_inner_self_eq_norm_sq]
      _ = f z₁ - ⟪f' s, z₁⟫_ℝ + ⟪f' z₁ - f' s, z₂ - z₁⟫_ℝ +
        l / 2 * (‖z₂‖ ^ 2  - 2 * ⟪z₂, z₁⟫_ℝ + ‖z₁‖ ^ 2) := by
          field_simp; ring_nf; rw [real_inner_comm]
      _ = f z₁ - ⟪f' s, z₁⟫_ℝ + ⟪f' z₁ - f' s, z₂ - z₁⟫_ℝ + l / 2 * ‖z₂ - z₁‖ ^ 2 := by
        rw [← norm_sub_sq_real]
  have hfs₃ : ∀ s : E, IsMinOn (fs s) univ s := by
    intro s
    apply first_order_convex (hfconx₁ s) (hfunconvex s)
    simp_all only [mem_univ, smul_eq_mul, tsub_le_iff_right, forall_const, true_and, gt_iff_lt, sub_self,
      fs, fs', gs, gs']
  have hfy₃ : IsMinOn (fs y) _ y := hfs₃ y
  have hfx₄ : fs x x ≤ fs x y - 1 / (2 * l) * ‖fs' x y‖ ^ 2 := by
    have : fs x x ≤ fs x (y - (1 / l) • fs' x y) := by
      rcases hfs₃ x with hf3'
      rw[isMinOn_iff] at hf3'
      apply hf3'
      simp
    apply le_trans this
    rcases hfx₂ x y (y - (1 / l) • fs' x y) with hfx₂'
    calc
      _ ≤ fs x y + ⟪fs' x y, y - (1 / l) • fs' x y - y⟫_ℝ
          + l / 2 * ‖y - (1 / l) • fs' x y - y‖ ^ 2 := by apply hfx₂'
      _ = fs x y - 1 / (2 * l) * ‖fs' x y‖ ^ 2 := by
        have : y - (1 / l) • fs' x y - y = - (1 / l) • fs' x y := by simp
        rw [this, real_inner_smul_right]
        repeat rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
        rw [real_inner_smul_right, real_inner_smul_left]; field_simp; ring
  have hfy₄ : fs y y ≤ fs y x - 1 / (2 * l) * ‖fs' y x‖ ^ 2 := by
    have : fs y y ≤ fs y (x - (1 / l) • fs' y x) := by
      rw [isMinOn_iff] at hfy₃
      rcases hfy₃ (x - (1 / l) • fs' y x) with hfy₃'
      apply hfy₃'
      simp
    apply le_trans this
    rcases hfx₂ y x (x - (1 / l) • fs' y x) with hfy₂'
    calc
      _ ≤ fs y x + ⟪fs' y x, x - (1 / l) • fs' y x - x⟫_ℝ
          + l / 2 * ‖x - (1 / l) • fs' y x - x‖ ^ 2 := by apply hfy₂'
      _ = fs y x - 1 / (2 * l) * ‖fs' y x‖ ^ 2 := by
        have : x - (1 / l) • fs' y x - x = - (1 / l) • fs' y x := by simp
        rw [this, real_inner_smul_right]
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, real_inner_smul_right]
        rw [real_inner_smul_left]; field_simp; ring
  have hh₁: (1 / (2 * l)) * ‖f' x - f' y‖ ^ 2 ≤ f y - f x - ⟪f' x, y - x⟫_ℝ := by
    calc
      (1 / (2 * l)) * ‖f' x - f' y‖ ^ 2 ≤ fs x y - fs x x := by
        have : f' x - f' y = - fs' x y := by
          have : fs' x y = f' y - f' x := by rfl
          rw [this]; simp
        rw [this]
        have : ‖- fs' x y‖  = ‖fs' x y‖  :=by apply norm_neg
        rw [this]
        linarith [hfx₄]
      _ = f y - f x - ⟪f' x, y - x⟫_ℝ := by
        have t₄: fs x y = f y - ⟪f' x, y⟫_ℝ := by rfl
        have t₅: fs x x = f x - ⟪f' x, x⟫_ℝ := by rfl
        rw [t₄,t₅,inner_sub_right]
        ring
  have hh₂: (1 / (2 * l)) * ‖f' x - f' y‖ ^ 2 ≤ f x - f y - ⟪f' y, x - y⟫_ℝ := by
    calc
      (1 / (2 * l)) * ‖f' x - f' y‖ ^ 2 ≤ fs y x -fs y y := by
        have : f' x - f' y = fs' y x := by aesop
        rw [this]
        linarith [hfy₄]
      _ = f x - f y - ⟪f' y, x - y⟫_ℝ := by
        have t₄' : fs y y = f y - ⟪f' y, y⟫_ℝ := by rfl
        have t₅' : fs y x = f x - ⟪f' y, x⟫_ℝ := by rfl
        rw [t₄', t₅', inner_sub_right]
        ring
  calc
    _ = (1 / (2 * l)) * ‖f' x - f' y‖ ^ 2 + (1 / (2 * l)) * ‖f' x - f' y‖ ^ 2 := by
      field_simp
      rw [← mul_two,mul_comm]
      ring
    _ ≤ (f y - f x - ⟪f' x, y - x⟫_ℝ) + (f x - f y - ⟪f' y, x - y⟫_ℝ) := by
      apply add_le_add hh₁ hh₂
    _ = ⟪f' x - f' y, x - y⟫_ℝ := by
      rw [inner_sub_left]
      have t₆ : (⟪f' x, y - x⟫_ℝ : ℝ) = - (⟪f' x, x - y⟫_ℝ : ℝ) := by
        rw [inner_sub_right, inner_sub_right]; ring
      rw[t₆]; ring

theorem lipschitz_to_lower (h₁ : ∀ x, HasGradientAt f (f' x) x) (h₂ : LipschitzWith l f')
    (hfun : ConvexOn ℝ Set.univ f) (hl : l > 0) :
    ∀ x y, ⟪f' x - f' y, x - y⟫_ℝ ≥ 1 / l * ‖f' x - f' y‖ ^ 2 := by
  obtain convex : ConvexOn ℝ Set.univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) :=
    lipschitz_to_lnorm_sub_convex convex_univ (fun x _ => h₁ x) (lipschitzOnWith_univ.mpr h₂) hl
  exact convex_to_lower h₁ convex hl hfun

theorem lower_iff_lipschitz (h₁ : ∀ x, HasGradientAt f (f' x) x) (hfun: ConvexOn ℝ Set.univ f)
    (hl : l > 0) : LipschitzWith l f' ↔
    ∀ x y, ⟪f' x - f' y, x - y⟫_ℝ ≥ 1 / l * ‖f' x - f' y‖ ^ 2 :=
  ⟨fun h ↦ lipschitz_to_lower h₁ h hfun hl, fun h ↦ lower_to_lipschitz h hl⟩

theorem lipshictz_iff_lnorm_sub_convex (h₁ : ∀ x, HasGradientAt f (f' x) x)
    (hfun: ConvexOn ℝ Set.univ f) (hl : l > 0) : LipschitzWith l f' ↔
    ConvexOn ℝ univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) := by
  constructor
  · intro h
    exact lipschitz_to_lnorm_sub_convex convex_univ (fun x _ ↦ h₁ x) (fun x _ y _ => h x y) hl
  intro h'
  rw [lower_iff_lipschitz h₁ hfun hl]
  exact fun x y => convex_to_lower h₁ h' hl hfun x y

theorem lower_iff_lnorm_sub_convex (h₁ : ∀ x, HasGradientAt f (f' x) x)
    (hfun: ConvexOn ℝ Set.univ f) (hl : l > 0) : ConvexOn ℝ univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x)
    ↔ ∀ x y, ⟪f' x - f' y, x - y⟫_ℝ ≥ 1 / l * ‖f' x - f' y‖ ^ 2  := by
  rw [← lipshictz_iff_lnorm_sub_convex h₁ hfun hl]
  rw [lower_iff_lipschitz h₁ hfun hl]

end Convex
