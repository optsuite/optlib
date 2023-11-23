/-
Copyright (c) 2023 Ziyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yuxuan Wu, Junda Ying
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Function.Convex_Function
import Mathlib.Analysis.InnerProductSpace.Calculus
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
    calc ‖g' u - g' v‖ = ‖(f' (x + u • (y - x))) (y - x) - (f' (x + v • (y - x))) (y - x)‖ := rfl
      _ = ‖(f' (x + u • (y - x)) - f' (x + v • (y - x))) (y - x)‖ := by congr
      _ ≤ ‖f' (x + u • (y - x)) - f' (x + v • (y - x))‖ * ‖y - x‖ :=
         ContinuousLinearMap.le_op_norm (f' (x + u • (y - x)) - f' (x + v • (y - x))) (y - x)
      _ ≤ l * ‖x + u • (y - x) - (x + v • (y - x))‖ * ‖y - x‖ :=
         mul_le_mul_of_le_of_le h₂ (le_refl ‖y - x‖) (norm_nonneg _) (norm_nonneg _)
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
  have H1₀ : (upperf 0) = g 0 := by
    simp only [zero_smul, add_zero, map_sub, Real.rpow_two, zero_mul, ne_eq, zero_pow']
  have H₃' : ∀ t : ℝ , HasDerivAt upperf (upperf' t) t  := by
    intro t
    apply HasDerivAt.add
    · apply HasDerivAt.const_add
      · apply hasDerivAt_mul_const
    · show HasDerivAt (fun x_1 => x_1 ^ 2 * (l * ‖y - x‖ ^ 2 / 2)) (l * ‖y - x‖ ^ 2 * t) t
      have h2: deriv (fun x_1 => x_1 ^ 2 * (l * ‖y - x‖ ^ 2 / 2)) t = (l * ‖y - x‖ ^ 2 * t) := by
        simp; ring_nf
      have h3:  DifferentiableAt ℝ (fun x_1 => x_1 ^ 2 * (l * ‖y - x‖ ^ 2 / 2)) t:= by
        simp only [Real.rpow_two, differentiableAt_id', DifferentiableAt.pow,
          differentiableAt_const, DifferentiableAt.mul]
      rw [← h2]
      apply DifferentiableAt.hasDerivAt h3
  have H₄ : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) (2 : ℝ) → g t ≤ upperf t := by
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
      have s₁ : t ≥ 0 := by
        simp only [gt_iff_lt, zero_lt_two, not_true, ge_iff_le, Set.mem_Ico] at ht; linarith
      apply H₃ t s₁
  specialize H₄ (1 : ℝ) (Set.mem_Icc.mpr (by norm_num))
  have H₅ : g 1 = f y := by simp only [one_smul, add_sub_cancel'_right]
  have H₆ : g 0 = f x := by simp only [zero_smul, add_zero]
  have H₇ : upperf 1 = g 0 + g' 0 + LL / 2 := by simp
  have T₁ : g' 0 = f' x (y - x) := by simp only [map_sub, zero_smul, add_zero]
  rw [H₆, T₁] at H₇; rw [H₇, H₅, L₁] at H₄; linarith

end

section

open InnerProductSpace

variable {f : E → ℝ} {l a : ℝ} {f' : E → E} {xm : E}

theorem lipschitz_continuos_upper_bound'
    (h₁ : ∀ x₁ : E, HasGradientAt f (f' x₁) x₁) (h₂ : LipschitzOn f' l) :
    ∀ x y : E, f y ≤ f x + inner (f' x) (y - x) + l / 2 * ‖y - x‖ ^ 2 := by
  intro x y
  let g := fun x ↦ (toDual ℝ E) (f' x)
  have h' : ∀ x : E, HasFDerivAt f (g x) x := h₁
  have equiv : ∀ x y : E, inner (f' x) (y - x) = (g x) (y - x) := by
    intro x y
    rw [InnerProductSpace.toDual_apply]
  have h₂' : LipschitzOn g l := by
    simp only [LipschitzOn, equiv]
    rw [LipschitzOn] at h₂
    intro x y
    have h1 : ∀ x : E, ‖(toDual ℝ E) x‖ =‖x‖ := by
      simp [LinearIsometryEquiv.norm_map]
    have : ‖(toDual ℝ E) (f' x) - (toDual ℝ E) (f' y)‖ = ‖f' x - f' y‖ := by
      rw [← map_sub (toDual ℝ E) (f' x) (f' y)]
      exact h1 (f' x - f' y)
    rw [this]
    exact (h₂ x y)
  rw [equiv]
  exact lipschitz_continuos_upper_bound h' h₂' x y

theorem lipschitz_minima (h₁ : ∀ x : E, HasGradientAt f (f' x) x) (h₂ : LipschitzOn f' l)
    (min: IsMinOn f Set.univ xm):
    ∀ x : E, 1 / (2 * l) * ‖f' x‖ ^ 2 ≤ f x - f xm := by
  sorry

end

section Convex

variable {f : E → ℝ} {l a : ℝ} {f': E → E} {xm : E}
variable {x y : E}

lemma gradient_norm_sq_eq_two_self (x : E) :
    HasGradientAt (fun x ↦ ‖x‖ ^ 2) ((2 : ℝ) • x) x := by
  apply Convergence_HasGradient
  simp
  intro e ep
  use e
  constructor
  . linarith
  . intro x' dles
    rw [← norm_neg (x - x'), neg_sub] at dles
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_sub_right]
    rw [real_inner_smul_left, real_inner_smul_left]; ring_nf
    rw [add_sub, add_sub_right_comm, mul_two, ← sub_sub]
    rw [← inner_sub_left, sub_add, ← inner_sub_right]
    rw [real_inner_comm, ← inner_sub_left, real_inner_self_eq_norm_sq]
    rw [abs_of_nonneg, pow_two, ← norm_neg (x - x'), neg_sub]
    apply mul_le_mul_of_nonneg_right dles (norm_nonneg (x' - x))
    apply pow_two_nonneg

theorem lipschitz_to_convex (h₁ : ∀ x : E, HasGradientAt f (f' x) x) (h₂ : LipschitzOn f' l)
    (lp : l > 0) : ConvexOn ℝ Set.univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) := by
  let g' : E → E := fun x ↦ l • x - f' x
  have H₂ : ∀ x y : E, inner (g' x - g' y) (x - y) ≥ (0 : ℝ) := by
    intro x y
    have : l • x - f' x - (l • y - f' y) =  l • (x - y) - (f' x - f' y) := by
      rw [smul_sub, ← sub_add, ← sub_add, sub_right_comm]
    calc
    _ = l * (inner (x - y) (x - y)) - inner (f' x - f' y) (x - y) := by
      simp
      rw [this, inner_sub_left, sub_left_inj, real_inner_smul_left]
    _ = l * ‖x - y‖ ^ 2 - inner (f' x - f' y) (x - y) := by
      simp; left
      apply real_inner_self_eq_norm_sq
    _ ≥ l * ‖x - y‖ ^ 2 - ‖f' x - f' y‖ * ‖x - y‖ := by
      apply add_le_add; linarith
      simp
      apply real_inner_le_norm
    _ ≥ l * ‖x - y‖ ^ 2 - l * ‖x - y‖ ^ 2 := by
      simp
      rw [pow_two, ← mul_assoc]
      apply mul_le_mul (h₂ x y); linarith; apply norm_nonneg
      apply mul_nonneg (le_of_lt lp) (norm_nonneg _)
    _ = 0 := by simp
  have H₃ : ∀ (x : E), HasGradientAt (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) (g' x) x := by
    intro x
    have u₂ := HasGradientAt.const_smul (gradient_norm_sq_eq_two_self x) ((l / (2 : ℝ)) : ℝ)
    have u := u₂.add (HasGradientAt.neg (h₁ x))
    have l₁ : (fun x ↦ l / 2 * ‖x‖ ^ 2 + -f x) = (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) := by
      ext; ring
    have l₂ : (l / 2) • (2 : ℝ)  • x + -f' x = g' x := by
      simp; rw [smul_smul (l / 2) 2, ← sub_eq_add_neg]; ring_nf
    rw [← l₁, ← l₂]
    apply u
  apply monotone_gradient_convex' convex_univ
  apply H₃
  intro x _ y _
  exact H₂ x y

theorem convex_to_lower (h₁ : ∀ x : E, HasGradientAt f (f' x) x)
    (h₂ : ConvexOn ℝ Set.univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x)) (lp : l > 0)
    (hfun: ConvexOn ℝ Set.univ f) (x : E) (y : E) :
    inner (f' x - f' y) (x - y) ≥ 1 / l * ‖f' x - f' y‖ ^ 2 := by
  let fx : E → ℝ := fun z ↦ f z - inner (f' x) z
  let fy : E → ℝ := fun z ↦ f z - inner (f' y) z
  have hfx : ConvexOn ℝ Set.univ fx := by sorry
  have hfy : ConvexOn ℝ Set.univ fy := by sorry
  let gx : E → ℝ := fun z ↦ l / 2 * ‖z‖ ^ 2 - fx z
  let gy : E → ℝ := fun z ↦ l / 2 * ‖z‖ ^ 2 - fy z
  have hgx : ConvexOn ℝ Set.univ gx := by sorry
  have hgx : ConvexOn ℝ Set.univ gy := by sorry
  sorry

theorem lipschitz_to_lower (h₁ : ∀ x : E, HasGradientAt f (f' x) x) (h₂ : LipschitzOn f' l)
    (lp : l > 0) (hfun: ConvexOn ℝ Set.univ f) :
    inner (f' x - f' y) (x - y) ≥ 1 / l * ‖f' x - f' y‖ ^ 2 := by
  have convex : ConvexOn ℝ Set.univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) := lipschitz_to_convex h₁ h₂ lp
  exact convex_to_lower h₁ convex lp hfun x y

theorem lower_to_lipschitz (h₂ : ∀ x y : E, inner (f' x - f' y) (x - y) ≥ 1 / l * ‖f' x - f' y‖ ^ 2)
    (lpos : l > 0) : LipschitzOn f' l := by
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
      ring
  have H₂ : 1 / l > 0 := by
    apply one_div_pos.mpr lpos
  cases lt_or_ge 0 (‖f' x - f' y‖)
  case inl h =>
    apply le_of_mul_le_mul_left H₁
    apply mul_pos H₂ h
  case inr h =>
    apply le_trans h
    apply mul_nonneg (le_of_lt lpos)
    apply norm_nonneg _

theorem convex_to_lipschitz (h₁ : ∀ x : E, HasGradientAt f (f' x) x) (lp : l > 0)
    (hfun: ConvexOn ℝ Set.univ f) (h₂ : ConvexOn ℝ Set.univ (fun x ↦ l / 2 * ‖x‖ ^ 2 - f x) ) :
    LipschitzOn f' l := by
  have : ∀ x y : E, inner (f' x - f' y) (x - y) ≥ 1 / l * ‖f' x - f' y‖ ^ 2 := by
    intro x y
    exact convex_to_lower h₁ h₂ lp hfun x y
  exact lower_to_lipschitz this lp



end Convex
