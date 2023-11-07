/-
Copyright (c) 2023 Ziyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Analysis.Calculation
/-!
  the properties of the L smooth function
-/
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def LipschitzOn (f : E → F) (l : ℝ) : Prop :=
  ∀ x y : E, ‖f x - f y‖ ≤ l * ‖x - y‖

section

open InnerProductSpace

variable {f : E → ℝ} {l a : ℝ} {f': E → (E →L[ℝ] ℝ)}

theorem deriv_function_comp_segment (x y : E) (h₁ : ∀ x₁ : E, HasFDerivAt f (f' x₁) x₁) :
    ∀ t₀ : ℝ , HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x)))
    ((fun t : ℝ ↦ (f' (x + t • (y - x)) (y - x))) t₀) t₀ := by
  let h := fun t : ℝ ↦ x + t • (y - x)
  have h_deriv : ∀ t : ℝ,  HasDerivAt h (y - x) t := by
    intro t
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have :(fun h => (t + h) • (y - x) - t • (y - x) - h • (y - x)) = (fun h => 0) := by
      ext h
      rw [add_smul, add_comm, ← add_sub, sub_self, add_zero, sub_self]
    simp [this]
  have H₂: ∀ t₀ : ℝ , HasDerivAt (f ∘ h) (f' (x + t₀ • (y - x)) (y - x)) t₀ := by
    intro t₀
    apply HasFDerivAt.comp_hasDerivAt
    · apply h₁ (x + t₀ • (y - x))
    · apply h_deriv t₀
  intro t₀
  apply H₂ t₀

theorem lipschitz_continuos_upper_bound
    (h₁ : ∀ x₁ : E, HasFDerivAt f (f' x₁) x₁) (h₂ : LipschitzOn f' l) :
  ∀ (x y : E), f y ≤ f x + (f' x) (y - x) + l / 2 * ‖y - x‖ ^ 2 := by
  intro x y
  let g := fun t : ℝ ↦ f (x + t • (y - x))
  let g' := fun t : ℝ ↦ (f' (x + t • (y - x)) (y - x))
  let LL := l * ‖y - x‖ ^ 2
  have H₁ : ∀ t₀ : ℝ , HasDerivAt g (g' t₀) t₀ := deriv_function_comp_segment x y h₁
  have L₁ : LL = l * ‖y - x‖ ^ 2 := by exact rfl
  have H₂ : ∀ u v : ℝ, ‖g' u - g' v‖  ≤ l * ‖y - x‖ ^ 2 * ‖u - v‖ := by
    intro u v
    specialize h₂ (x + u • (y - x)) (x + v • (y - x))
    have : x + u • (y - x) - (x + v • (y - x)) = (u - v) • (y - x) := by
      rw [← sub_sub, add_sub_right_comm, sub_self, zero_add, ← sub_smul]
    calc ‖g' u - g' v‖ = ‖(f' (x + u • (y - x))) (y - x) - (f' (x + v • (y - x))) (y - x)‖ := by rfl
      _ = ‖(f' (x + u • (y - x)) - f' (x + v • (y - x))) (y - x)‖ := by congr
      _ ≤ ‖f' (x + u • (y - x)) - f' (x + v • (y - x))‖ * ‖y - x‖ :=
         ContinuousLinearMap.le_op_norm (f' (x + u • (y - x)) - f' (x + v • (y - x))) (y - x)
      _ ≤ l * ‖x + u • (y - x) - (x + v • (y - x))‖ * ‖y - x‖ :=
         mul_le_mul_of_le_of_le h₂ (le_refl ‖y - x‖) (norm_nonneg (f' (x + u • (y - x)) - f' (x + v • (y - x)))) (norm_nonneg (y - x))
      _ = l * ‖(u - v) • (y - x)‖ * ‖y - x‖  := by rw [this]
      _ = l * ‖y - x‖ ^ 2 * ‖u - v‖ := by rw [norm_smul]; ring_nf; simp
  let upperf := fun t₀ : ℝ ↦ g 0 + t₀ * (g' 0) +  t₀ ^ 2 * (LL / 2)
  let upperf':= fun t : ℝ ↦ g' 0 + LL * t
  have H₃ : ∀ t ≥ 0 , g' t ≤ upperf' t := by
    intro t ht
    specialize H₂ t 0
    rw [sub_zero] at H₂
    have abs_pos : LL * |t| = LL * t := congrArg (HMul.hMul LL) (abs_of_nonneg (by linarith))
    have HH₆ : g' t - g' 0 ≤ LL * t :=
      calc  (g' t - g' 0) ≤ |g' t - g' 0| := by exact le_abs_self (g' t - g' 0)
            _   ≤ l * ‖y - x‖ ^ 2 * |t| := by exact H₂
            _   = LL * |t| := by simp
            _   = LL * t := abs_pos
    exact tsub_le_iff_left.mp HH₆
  have H1₀ : (upperf 0) = g 0 := by simp only [zero_smul, add_zero, map_sub, Real.rpow_two, zero_mul, ne_eq,
    zero_pow']
  have H₃' : ∀ t : ℝ , HasDerivAt upperf (upperf' t) t  := by
    intro t
    apply HasDerivAt.add
    · apply HasDerivAt.const_add
      · apply hasDerivAt_mul_const
    · show HasDerivAt (fun x_1 => x_1 ^ 2 * (l * ‖y - x‖ ^ 2 / 2)) (l * ‖y - x‖ ^ 2 * t) t
      have h2: deriv (fun x_1 => x_1 ^ 2 * (l * ‖y - x‖ ^ 2 / 2)) t = (l * ‖y - x‖ ^ 2 * t):= by
        simp; ring_nf
      have h3:  DifferentiableAt ℝ (fun x_1 => x_1 ^ 2 * (l * ‖y - x‖ ^ 2 / 2)) t:= by
        simp only [Real.rpow_two, differentiableAt_id', DifferentiableAt.pow, differentiableAt_const,
          DifferentiableAt.mul]
      rw [← h2]
      apply DifferentiableAt.hasDerivAt h3
  have H₄ : ∀ (t:ℝ), t ∈ Set.Icc (0 : ℝ) (2 : ℝ) → g t ≤ upperf t := by
    apply image_le_of_deriv_right_le_deriv_boundary
    · have : ∀ (x : ℝ), x ∈ (Set.Icc (0 : ℝ) (2 : ℝ)) → HasDerivAt g (g' x) x :=
        fun x _ ↦ H₁ x
      exact HasDerivAt.continuousOn this
    · intro t _
      exact HasDerivAt.hasDerivWithinAt (H₁ t)
    · linarith
    · have : ∀ (x : ℝ), x ∈ (Set.Icc (0 : ℝ) (2 : ℝ)) → HasDerivAt upperf (upperf' x) x :=
        fun x _ ↦ H₃' x
      exact HasDerivAt.continuousOn this
    · intro t _
      exact HasDerivAt.hasDerivWithinAt (H₃' t)
    · intro t ht
      have s₁ : t ≥ 0 := by simp only [gt_iff_lt, zero_lt_two, not_true, ge_iff_le, Set.mem_Ico] at ht; linarith
      apply H₃ t s₁
  specialize H₄ (1 : ℝ) (Set.mem_Icc.mpr (by norm_num))
  have H₅ : g 1 = f y := by simp only [one_smul, add_sub_cancel'_right]
  have H₆ : g 0 = f x := by simp only [zero_smul, add_zero]
  have H₇ : upperf 1 = g 0 + g' 0 + LL / 2 := by simp
  have T₁ : g' 0 = f' x (y - x) := by simp only [map_sub, zero_smul, add_zero]
  rw [H₆, T₁] at H₇; rw [H₇, H₅, L₁] at H₄; linarith

end

section

variable {f : E → ℝ} {l a : ℝ} {f': E → E} {xm : E}

theorem lipschitz_continuos_upper_bound'
    (h₁ : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁) (h₂ : LipschitzOn f' l) :
    ∀ (x y : E), f y ≤ f x + inner (f' x) (y - x) + l / 2 * ‖y - x‖ ^ 2 := by
  sorry

theorem lipschitz_minima (h₁ : ∀ x : E, HasGradientAt f (f' x) x) (h₂ : LipschitzOn f' l)
    (min: IsMinOn f Set.univ xm):
    ∀ x : E, 1 / (2 * l) * ‖f' x‖ ^ 2 ≤ f x - f xm := by
  sorry

end

section

variable {f : E → ℝ} {l a : ℝ} {f': E → E} {xm : E} (h₁ : ∀ x : E, HasGradientAt f (f' x) x)
variable (hfun: ConvexOn ℝ Set.univ f)

theorem lipschitz_lower (h₂ : LipschitzOn f' l) :
    inner (f' x - f' y) (x - y) ≥ 1 / l * ‖f' x - f' y‖ ^ 2 := by
  sorry

theorem lipschitz_to_convex (h₂ : LipschitzOn f' l) :
    ConvexOn ℝ Set.univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) := by
  sorry

theorem convex_to_lipschitz (h₂ : ConvexOn ℝ Set.univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) ) :
    LipschitzOn f' l := by
  sorry

theorem convex_to_lower (h₂ : ConvexOn ℝ Set.univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) ) :
    inner (f' x - f' y) (x - y) ≥ 1 / l * ‖f' x - f' y‖ ^ 2 := by
  sorry

end
