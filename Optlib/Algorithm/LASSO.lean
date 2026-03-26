/-
Copyright (c) 2024 Yuxuan Wu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Wu, Chenyi Li
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.CStarAlgebra.Matrix
import Optlib.Algorithm.ProximalGradient

set_option linter.unusedVariables false

/-!
# LASSO

## Main results

  This file mainly concentrates on the definition and the proof of the convergence rate
  of the Lasso problem using proximal gradient method.

-/
section property

variable {n m : ℕ+} {t μ : ℝ}
variable {b : (Fin m) → ℝ} {A : Matrix (Fin m) (Fin n) ℝ}
variable {f h : (y : EuclideanSpace ℝ (Fin n)) → ℝ}
variable {f' : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n))}

/- Definition of `‖ ‖₁, ‖ ‖₂`, consistent with the general definition in ℝⁿ -/

local notation "‖" x "‖₂" => @Norm.norm (EuclideanSpace ℝ (Fin m)) (PiLp.instNorm 2 fun _ ↦ ℝ) x
local notation "‖" x "‖₁" => (Finset.sum Finset.univ (fun (i : Fin n) => ‖x i‖))

instance : CoeTC ((Fin m) → ℝ) (EuclideanSpace ℝ (Fin m)) := ⟨WithLp.toLp 2⟩
instance : CoeTC ((Fin n) → ℝ) (EuclideanSpace ℝ (Fin n)) := ⟨WithLp.toLp 2⟩

open Set Real Matrix Finset

/- `u ⬝ Av = Aᵀu ⬝ v` for u v in EuclideanSpace -/

lemma dot_mul_eq_transpose_mul_dot (u : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)) :
      u ⬝ᵥ A *ᵥ v = Aᵀ *ᵥ u ⬝ᵥ v := by
    symm; rw [← vecMul_transpose, transpose_transpose, dotProduct_mulVec]

/- `Au - Av = A(u - v)` for u v in EuclideanSpace -/

lemma mulVec_sub (u v : Fin n → ℝ) : A *ᵥ u - A *ᵥ v = A *ᵥ (u - v) := by
    rw [sub_eq_add_neg u v, mulVec_add, mulVec_neg, sub_eq_add_neg]

/- `‖x‖₂ ^ 2 = x ⬝ x` for x in EuclideanSpace -/

lemma norm2eq_dot (x :  EuclideanSpace ℝ (Fin m)) : ‖x‖₂ ^ 2 = x ⬝ᵥ x := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt, dotProduct]
  rw [Finset.sum_congr]; simp
  intro z _; simp; rw [pow_two]
  apply sum_nonneg; exact fun i _ => sq_nonneg (‖x i‖)

/- `⟪x, y⟫_ℝ = x ⬝ y` for x y in EuclideanSpace -/

lemma real_inner_eq_dot (x y : EuclideanSpace ℝ (Fin m)) : inner ℝ x y = x ⬝ᵥ y := by
  calc
    inner ℝ x y = y.ofLp ⬝ᵥ star x.ofLp := EuclideanSpace.inner_eq_star_dotProduct (x := x) (y := y)
    _ = y.ofLp ⬝ᵥ x.ofLp := by simp
    _ = x.ofLp ⬝ᵥ y.ofLp := by simpa using (dotProduct_comm y.ofLp x.ofLp)

/- gradient of a quadratic in ℝⁿ -/

lemma quadratic_gradient : ∀ x : (EuclideanSpace ℝ (Fin n)),
    HasGradientAt (fun x : (EuclideanSpace ℝ (Fin n)) => ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)))
    ((2 : ℝ) • Aᵀ *ᵥ A *ᵥ x) x := by
  by_cases hA : A = 0
  · intro x
    rw [hA]; simp; apply hasGradientAt_const
  intro x
  rw [HasGradient_iff_Convergence_Point]
  intro ε εpos
  let normA := ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖
  have norm_mul (x : EuclideanSpace ℝ (Fin n)) :  ‖A *ᵥ x‖₂ ≤ normA * ‖x‖ := by
    apply Matrix.l2_opNorm_mulVec A
  have normApos : 0 < normA := by
    contrapose! hA
    have hA' : 0 ≤ normA := by apply norm_nonneg
    have hA'' : normA = 0 := by linarith [hA, hA']
    rw [norm_eq_zero] at hA''; simp at hA''; exact hA''
  use (ε / normA ^ 2)
  constructor
  · apply div_pos εpos; rw [sq_pos_iff]; linarith [normApos]
  intro y ydist;
  rw [inner_smul_left]
  simp; rw [real_inner_eq_dot (m := n)]
  have hsub : A *ᵥ (y - x).ofLp = A *ᵥ (y.ofLp - x.ofLp) := by simp
  rw [← mulVec_mulVec, ← dot_mul_eq_transpose_mul_dot _ (y - x), hsub, Matrix.mulVec_sub,
      dotProduct_sub]
  ring_nf
  have aux2 (u v : Fin m → ℝ) : u ⬝ᵥ u + (v ⬝ᵥ v - v ⬝ᵥ u * 2) = (u - v) ⬝ᵥ (u - v) := by
    rw [dotProduct_sub, sub_dotProduct, sub_dotProduct, ← sub_add, sub_sub, dotProduct_comm u v]
    rw [← mul_two, add_comm_sub]
  rw [aux2, ← norm2eq_dot]
  simp
  have hnormsub : WithLp.toLp 2 (A *ᵥ y.ofLp) - WithLp.toLp 2 (A *ᵥ x.ofLp)
      = WithLp.toLp 2 (A *ᵥ (y - x).ofLp) := by
    ext i
    simp [sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_neg]
  rw [hnormsub]
  calc
    ‖(A *ᵥ (y - x))‖₂ ^ 2 ≤ (normA * ‖x - y‖) ^ 2 := by
      rw [norm_sub_rev]
      apply sq_le_sq' _ (norm_mul (y - x))
      calc
        -(normA * ‖y - x‖) ≤ 0 := by
          simp; apply mul_nonneg; linarith [normApos]; apply norm_nonneg
        _ ≤ ‖A *ᵥ (y - x)‖₂ := by
          apply norm_nonneg
    _ ≤ ε * ‖x - y‖ := by
      rw [pow_two, ← mul_assoc]; apply mul_le_mul_of_nonneg_right
      rw [mul_rotate, mul_assoc, ← pow_two]
      calc
        ‖x - y‖ * normA ^ 2 ≤ ε / normA ^ 2 * normA ^ 2 :=
          mul_le_mul_of_nonneg_right ydist (sq_nonneg normA)
        _ = ε := by
          field_simp
      apply norm_nonneg

/- gradient of a linear map in ℝⁿ -/

private lemma linear_gradient : ∀ x : (EuclideanSpace ℝ (Fin n)),
    HasGradientAt (fun x : (EuclideanSpace ℝ (Fin n)) => (b ⬝ᵥ (A *ᵥ x)))
    (Aᵀ *ᵥ b) x := by
  intro x
  rw [HasGradient_iff_Convergence_Point]
  intro ε εpos
  use ε; use εpos
  intro y _
  rw [dot_mul_eq_transpose_mul_dot, dot_mul_eq_transpose_mul_dot, ← dotProduct_sub]
  rw [real_inner_eq_dot (m := n)]
  simp [dotProduct]
  apply mul_nonneg; linarith [εpos]; apply norm_nonneg

/- gradient of the square of an affine map in ℝⁿ -/

theorem affine_sq_gradient :  ∀ x : (EuclideanSpace ℝ (Fin n)),
    HasGradientAt (fun x : (EuclideanSpace ℝ (Fin n)) => ((1 / 2) * ‖A *ᵥ x - b‖₂ ^ 2))
    (Aᵀ *ᵥ (A *ᵥ x - b)) x := by
  intro x
  let f := fun x : (EuclideanSpace ℝ (Fin n)) => (1 / 2) * (A *ᵥ x) ⬝ᵥ (A *ᵥ x)
  let f' := fun x : (EuclideanSpace ℝ (Fin n)) => Aᵀ *ᵥ A *ᵥ x
  have fgradient : HasGradientAt f (f' x) x := by
    let g := fun x : (EuclideanSpace ℝ (Fin n)) => (1 / (2 : ℝ)) • (2 : ℝ) • Aᵀ *ᵥ A *ᵥ x
    have f'eqg (x : (EuclideanSpace ℝ (Fin n))): f' x = g x := by
      show Aᵀ *ᵥ A *ᵥ x = (1 / (2 : ℝ)) • (2 : ℝ) • Aᵀ *ᵥ A *ᵥ x; simp
    rw [f'eqg]
    apply HasGradientAt.const_mul' (1 / 2) (quadratic_gradient x)
  let h := fun x : (EuclideanSpace ℝ (Fin n)) => (b ⬝ᵥ (A *ᵥ x))
  let h' := fun _ : (EuclideanSpace ℝ (Fin n)) => (Aᵀ *ᵥ b)
  have hgradient : HasGradientAt h (h' x) x := by apply linear_gradient
  let φ := fun x : (EuclideanSpace ℝ (Fin n)) => ((1 / 2) * ‖A *ᵥ x - b‖₂ ^ 2)
  let φ' := fun x : (EuclideanSpace ℝ (Fin n)) => (Aᵀ *ᵥ (A *ᵥ x - b))
  have φeq : φ = fun x : (EuclideanSpace ℝ (Fin n)) => f x - h x + (1 / 2) * b ⬝ᵥ b := by
    ext z; simp [φ]; rw [norm2eq_dot]; simp [f, h]
    rw [← sub_add, dotProduct_comm _ b, sub_sub, ← two_mul, mul_add, mul_sub, ← mul_assoc]
    rw [inv_mul_cancel₀, one_mul]
    simp
  have φ'eq : φ' = fun x : (EuclideanSpace ℝ (Fin n)) => f' x - h' x := by
    ext y z; simp [φ', f', h']
    rw [Matrix.mulVec_sub Aᵀ]; simp
  show HasGradientAt φ (φ' x) x
  rw [φeq, φ'eq]
  apply HasGradientAt.add_const
  apply HasGradientAt.sub fgradient hgradient

/- the square of an affine map is convex on ℝⁿ-/

lemma affine_sq_convex :
    ConvexOn ℝ univ (fun x : (EuclideanSpace ℝ (Fin n)) => ((1 / 2) * ‖A *ᵥ x - b‖₂ ^ 2)) := by
  apply monotone_gradient_convex'
  apply convex_univ
  exact (fun x _ => affine_sq_gradient x)
  intro x _ y _
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, real_inner_eq_dot]
  repeat rw [← dot_mul_eq_transpose_mul_dot]
  let u : Fin m → ℝ := A *ᵥ x.ofLp + -b
  let v : Fin m → ℝ := A *ᵥ y.ofLp + -b
  have hdot : u ⬝ᵥ (A *ᵥ x.ofLp) + (v ⬝ᵥ (A *ᵥ y.ofLp) + (-u ⬝ᵥ (A *ᵥ y.ofLp) + -v ⬝ᵥ (A *ᵥ x.ofLp)))
      = (u - v) ⬝ᵥ ((A *ᵥ x.ofLp) - (A *ᵥ y.ofLp)) := by
    rw [dotProduct_sub, sub_dotProduct, sub_dotProduct]
    simp
    abel_nf
  have hdot' :
      (WithLp.toLp 2 (A *ᵥ x.ofLp + -b)).ofLp ⬝ᵥ A *ᵥ x.ofLp +
        ((WithLp.toLp 2 (A *ᵥ y.ofLp + -b)).ofLp ⬝ᵥ A *ᵥ y.ofLp +
          (-((WithLp.toLp 2 (A *ᵥ x.ofLp + -b)).ofLp ⬝ᵥ A *ᵥ y.ofLp) +
            -((WithLp.toLp 2 (A *ᵥ y.ofLp + -b)).ofLp ⬝ᵥ A *ᵥ x.ofLp))) =
        (u - v) ⬝ᵥ ((A *ᵥ x.ofLp) - (A *ᵥ y.ofLp)) := by
    simpa [u, v] using hdot
  rw [hdot']
  have huv : (u - v) = (A *ᵥ x.ofLp) - (A *ᵥ y.ofLp) := by
    dsimp [u, v]
    abel_nf
  rw [huv]
  have hnonneg : 0 ≤ ‖(WithLp.toLp 2 ((A *ᵥ x.ofLp) - (A *ᵥ y.ofLp)) : EuclideanSpace ℝ (Fin m))‖₂ ^ 2 := by
    exact sq_nonneg ‖(WithLp.toLp 2 ((A *ᵥ x.ofLp) - (A *ᵥ y.ofLp)) : EuclideanSpace ℝ (Fin m))‖₂
  simpa [norm2eq_dot] using hnonneg

/- ‖ ‖₁ is convex on ℝⁿ -/

lemma norm_one_convex : ConvexOn ℝ univ (fun x : (EuclideanSpace ℝ (Fin n)) => ‖x‖₁) := by
  rw [ConvexOn]
  constructor; use convex_univ
  intro x _ y _ a b anneg bnneg _
  rw [smul_eq_mul, smul_eq_mul, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  simp
  calc
    |a * x i + b * y i| ≤ |a * x i| + |b * y i| := by exact abs_add_le _ _
    _ = a * |x i| + b * |y i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg anneg, abs_of_nonneg bnneg]

/- `sgn(x)|x| = x` -/

lemma real_sign_mul_abs (x : ℝ) : Real.sign (x) * |x| = x := by
  by_cases xpos : 0 < x
  · rw [Real.sign_of_pos xpos]; simp; linarith
  · push_neg at xpos
    by_cases xzero : x = 0
    · rw [xzero]; simp
    · push_neg at xzero
      have xneg : x < 0 := by
        contrapose! xzero; linarith
      rw [Real.sign_of_neg xneg]; simp; rw [neg_eq_iff_eq_neg, abs_eq_neg_self]; linarith

/- the proximal of ‖ ‖₁ in ℝⁿ -/

theorem norm_one_proximal
    (lasso : h = fun y => μ • ‖y‖₁)
    (x : EuclideanSpace ℝ (Fin n)) (xm : EuclideanSpace ℝ (Fin n)) (tpos : 0 < t) (μpos : 0 < μ)
    (minpoint : ∀ i : Fin n, xm i = Real.sign (x i) * (max (abs (x i) - t * μ) 0)):
    prox_prop (t • h) x xm := by
  let g := (t * μ) • (fun (x : EuclideanSpace ℝ (Fin n)) => ‖x‖₁)
  have geqth : g = t • h := by
    ext z; rw [Pi.smul_apply]; simp [g]; rw [lasso]; simp; rw [mul_assoc]
  rw [← geqth]
  show prox_prop ((t * μ) • (fun (x : EuclideanSpace ℝ (Fin n)) => ‖x‖₁)) x xm
  have tμpos : 0 < t * μ := by
    apply mul_pos; linarith [tpos]; linarith [μpos]
  rw [prox_iff_subderiv_smul (fun x : (EuclideanSpace ℝ (Fin n)) => ‖x‖₁) norm_one_convex tμpos]
  rw [← mem_SubderivAt, HasSubgradientAt]
  intro y
  simp [real_inner_eq_dot (m := n), dotProduct]
  rw [← Finset.sum_add_distrib]
  apply sum_le_sum
  intro i _
  let abs_subg := SubderivAt_abs (xm i)
  by_cases hxm : xm i = 0
  · rw [hxm]; simp
    specialize minpoint i; rw [hxm] at minpoint; simp at minpoint
    have aux : |x i| ≤ t * μ := by
      by_cases hx : x i = 0
      · rw [hx]; simp; apply mul_nonneg; linarith [tpos]; linarith [μpos]
      · simp [hx] at minpoint; exact minpoint
    calc
      μ⁻¹ * t⁻¹ * x i * y i ≤ μ⁻¹ * t⁻¹ * |x i * y i| := by
        have hcoef : 0 ≤ μ⁻¹ * t⁻¹ := by
          apply mul_nonneg
          · exact inv_nonneg.2 (le_of_lt μpos)
          · exact inv_nonneg.2 (le_of_lt tpos)
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left (le_abs_self (x i * y i)) hcoef)
      _ ≤ |y i| * μ⁻¹ * t⁻¹ * t * μ := by
        rw [abs_mul, ← mul_assoc, mul_comm, ← mul_assoc, ← mul_assoc, mul_assoc _ t]
        apply mul_le_mul_of_nonneg_left
        exact aux; apply mul_nonneg; apply mul_nonneg
        apply abs_nonneg; simp; linarith [μpos]; simp; linarith [tpos]
      _ = |y i| := by
        rw [mul_assoc _ (t⁻¹) t, inv_mul_cancel₀, mul_one]
        rw [mul_assoc _ (μ⁻¹) μ, inv_mul_cancel₀, mul_one]
        linarith [μpos]; linarith [tpos]
  rw [eq_ite_iff, or_iff_right] at abs_subg
  rcases abs_subg with ⟨_, abs_subg⟩
  let sgnxm : ℝ := (xm i).sign
  have aux : sgnxm ∈ SubderivAt abs (xm i) := by
    rw [abs_subg]; simp [sgnxm]
  rw [← mem_SubderivAt, HasSubgradientAt] at aux
  specialize aux (y i)
  have aux2 : inner ℝ sgnxm (y i - xm i) = μ⁻¹ * t⁻¹ * (x i - xm i) * (y i - xm i) := by
    simp [sgnxm]
    rw [minpoint]; simp; rw [minpoint] at hxm; simp at hxm; push_neg at hxm
    rcases hxm with ⟨xiieq0, ieq⟩
    have eq1 : max (|x i| - t * μ) 0 = |x i| - t * μ := by
      apply max_eq_left; linarith
    rw [eq1]; simp; nth_rw 3 [mul_sub]
    nth_rw 2 [mul_comm (sign (x i))]
    by_cases hx : 0 < x i
    · have eq2 : (sign (x i) * (|x i| - t * μ)).sign = 1 := by
        apply Real.sign_of_pos
        apply mul_pos
        · calc
            0 < 1 := by simp
            1 = sign (x i) := by
              symm; exact Real.sign_of_pos hx
        linarith [ieq]
      rw [eq2]
      simp [Real.sign_of_pos hx, abs_of_pos hx]
      field_simp [μpos.ne', tpos.ne']
      have hinner1 : inner ℝ 1 (y i - (x i - t * μ))
          = (y i - (x i - t * μ)) * (starRingEnd ℝ) 1 := by
        exact RCLike.inner_apply 1 (y i - (x i - t * μ))
      rw [hinner1]
      simp
    · have xneg : x i < 0 := by
        contrapose! xiieq0; linarith
      have eq2 : (sign (x i) * (|x i| - t * μ)).sign = -1 := by
        apply Real.sign_of_neg
        apply mul_neg_of_neg_of_pos
        · calc
            sign (x i) = -1 := by
              exact Real.sign_of_neg xneg
            _ < 0 := by linarith
        · linarith [ieq]
      rw [eq2]
      simp [Real.sign_of_neg xneg, abs_of_neg xneg]
      field_simp [μpos.ne', tpos.ne']
      have hinner : inner ℝ 1 (y i - (t * μ + x i))
          = (y i - (t * μ + x i)) * (starRingEnd ℝ) 1 := by
        exact RCLike.inner_apply 1 (y i - (t * μ + x i))
      rw [hinner]
      simp
      abel_nf
  rw [aux2] at aux; linarith [aux]
  push_neg; intro hxm'; contrapose! hxm'; exact hxm

lemma Transpose_mul_self_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} : Aᵀ * A = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
      (congr_fun <| dotProduct_self_eq_zero.1 <| Matrix.ext_iff.2 h j j) i,
    fun h => h ▸ Matrix.mul_zero _⟩

end property

noncomputable section LASSO

variable {n m : ℕ+}

local notation "‖" x "‖₂" => @Norm.norm (EuclideanSpace ℝ (Fin m)) (PiLp.instNorm 2 fun _ ↦ ℝ) x
local notation "‖" x "‖₁" => (Finset.sum Finset.univ (fun (i : Fin n) => ‖x i‖))

instance : CoeTC ((Fin m) → ℝ) (EuclideanSpace ℝ (Fin m)) := ⟨WithLp.toLp 2⟩
instance : CoeTC ((Fin n) → ℝ) (EuclideanSpace ℝ (Fin n)) := ⟨WithLp.toLp 2⟩

open Set Real Matrix Finset NNReal


structure LASSO (A : Matrix (Fin m) (Fin n) ℝ) (b : (Fin m) → ℝ) (μ : ℝ) (μpos : 0 < μ) (Ane0 : A ≠ 0)
    (x₀ : (EuclideanSpace ℝ (Fin n))) where
  (f h : (EuclideanSpace ℝ (Fin n)) → ℝ)
  (f' : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)))
  (L : ℝ≥0) (t : ℝ) (xm : (EuclideanSpace ℝ (Fin n))) (x y : ℕ → (EuclideanSpace ℝ (Fin n)))
  (feq : f = fun x : (EuclideanSpace ℝ (Fin n)) => (1 / 2) * ‖A *ᵥ x - b‖₂ ^ 2)
  (f'eq : f' = fun x : (EuclideanSpace ℝ (Fin n)) => ((Aᵀ *ᵥ (A *ᵥ x - b)) : EuclideanSpace ℝ (Fin n)))
  (heq : h = fun y => μ • ‖y‖₁) (teq : t = 1 / L)
  (Leq : L = ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (Aᵀ * A)‖₊)
  (minphi : IsMinOn (f + h) Set.univ xm)
  (ori : x 0 = x₀)
  (update1 : ∀ (k : ℕ), y k = x k - t • f' (x k))
  (update2 : ∀ (k : ℕ), x (k + 1) =
    fun i : Fin n => (Real.sign (y k i) * (max (abs (y k i) - t * μ) 0)))

instance {A : Matrix (Fin m) (Fin n) ℝ} {b : (Fin m) → ℝ} {μ : ℝ} {μpos : 0 < μ} {Ane0 : A ≠ 0}
    {x₀ : (EuclideanSpace ℝ (Fin n))} (p : LASSO A b μ μpos Ane0 x₀) :
    proximal_gradient_method p.f p.h p.f' x₀ where
  xm := p.xm
  t := p.t
  x := p.x
  L := p.L
  fconv := by
    rw [p.feq]; apply affine_sq_convex
  hconv := by
    rw [p.heq]; apply ConvexOn.smul; linarith [μpos]; apply norm_one_convex
  h₁ : ∀ x₁ : (EuclideanSpace ℝ (Fin n)), HasGradientAt p.f (p.f' x₁) x₁ := by
    rw [p.feq, p.f'eq]
    exact (fun x => affine_sq_gradient x)
  h₂ : LipschitzWith p.L p.f' := by
    rw [lipschitzWith_iff_norm_sub_le]; intro x y
    rw [p.f'eq, p.Leq]
    have hsub :
        Aᵀ *ᵥ (A *ᵥ x.ofLp - b) - Aᵀ *ᵥ (A *ᵥ y.ofLp - b)
          = (Aᵀ * A) *ᵥ (x.ofLp - y.ofLp) := by
      have hinner : A *ᵥ x.ofLp - b - (A *ᵥ y.ofLp - b) = A *ᵥ x.ofLp - A *ᵥ y.ofLp := by
        abel_nf
      calc
        Aᵀ *ᵥ (A *ᵥ x.ofLp - b) - Aᵀ *ᵥ (A *ᵥ y.ofLp - b)
            = Aᵀ *ᵥ (A *ᵥ x.ofLp - b - (A *ᵥ y.ofLp - b)) := by
              symm
              exact Matrix.mulVec_sub Aᵀ (A *ᵥ x.ofLp - b) (A *ᵥ y.ofLp - b)
        _ = Aᵀ *ᵥ (A *ᵥ x.ofLp - A *ᵥ y.ofLp) := by rw [hinner]
        _ = (Aᵀ * A) *ᵥ (x.ofLp - y.ofLp) := by rw [← Matrix.mulVec_sub, mulVec_mulVec]
    have hleft :
        ‖(fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (Aᵀ *ᵥ (A *ᵥ z.ofLp - b))) x
          - (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (Aᵀ *ᵥ (A *ᵥ z.ofLp - b))) y‖
          = ‖WithLp.toLp 2 ((Aᵀ * A) *ᵥ (x.ofLp - y.ofLp))‖ := by
      calc
        ‖(fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (Aᵀ *ᵥ (A *ᵥ z.ofLp - b))) x
            - (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (Aᵀ *ᵥ (A *ᵥ z.ofLp - b))) y‖
            = ‖WithLp.toLp 2 (Aᵀ *ᵥ (A *ᵥ x.ofLp - b) - Aᵀ *ᵥ (A *ᵥ y.ofLp - b))‖ := by
              simp [sub_eq_add_neg]
        _ = ‖WithLp.toLp 2 ((Aᵀ * A) *ᵥ (x.ofLp - y.ofLp))‖ := by simp [hsub]
    rw [hleft]
    have hmul := Matrix.l2_opNorm_mulVec (Aᵀ * A) (x - y)
    rw [Matrix.l2_opNorm_def (A := Aᵀ * A)] at hmul
    simpa [sub_eq_add_neg] using hmul
  h₃ : ContinuousOn p.h univ := by
    rw [ContinuousOn]
    intro x _
    rw [continuousWithinAt_univ, ContinuousAt_iff_Convergence]
    intro ε εpos
    use ε / n / μ; constructor
    have delta_pos : 0 < ε / n / μ := by
      apply div_pos; apply div_pos; linarith; simp; linarith
    use delta_pos
    intro y ydist
    rw [p.heq]; simp; rw [← mul_sub, ← sum_sub_distrib]
    have le (i : Fin n) : |(|y i|) - (|x i|)| ≤ ε / n / μ := by
      rw [EuclideanSpace.norm_eq] at ydist; rw [Real.sqrt_le_iff] at ydist
      have aux : ‖(x - y) i‖ ^ 2 ≤ (ε / n / μ) ^ 2 := by
        calc
          ‖(x - y) i‖ ^ 2 = Finset.sum {i} fun i ↦ ‖(x - y) i‖ ^ 2 := by simp
          _ ≤ Finset.sum Finset.univ fun i ↦ ‖(x - y) i‖ ^ 2 := by
            apply sum_le_sum_of_subset_of_nonneg; simp
            intro j _ _; apply sq_nonneg
          _ ≤ (ε / n / μ) ^ 2 := ydist.2
      calc
        |(|y i|) - (|x i|)| ≤ ‖(x - y) i‖ := by
          simp; rw [abs_sub_comm]; apply abs_abs_sub_abs_le_abs_sub
        _ ≤ (ε / n / μ) := by
          rw [sq_le_sq] at aux
          have : |ε / n / μ| = ε / n / μ := by rw [abs_eq_self]; linarith
          rw [← this]; simp at aux; exact aux
    rw [abs_mul]
    calc
      |μ| * |Finset.sum Finset.univ fun i ↦ (|y i| - |x i|)| ≤
          |μ| * Finset.sum Finset.univ fun i ↦ |(|y i| - |x i|)| := by
        exact mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : Fin n ↦ (|y i| - |x i|)))
          (abs_nonneg _)
      _ ≤ |μ| * (n * (ε / n / μ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc
          (Finset.sum Finset.univ fun i ↦ |(|y i| - |x i|)|) ≤
              (Finset.sum Finset.univ (fun _ ↦ (ε / n / μ))) := by
            apply Finset.sum_le_sum
            exact fun i _ => le i
          _ = (n * (ε / n / μ)) := by simp
      _ = ε := by
        rw [abs_of_pos μpos]
        field_simp [μpos.ne']
  minphi : IsMinOn (p.f + p.h) Set.univ p.xm := p.minphi
  tpos : 0 < p.t := by
    rw [p.teq]; simp
    rw [p.Leq]; simp
    intro h
    have hAtA : Aᵀ * A = 0 := by
      apply (Matrix.toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal))).injective
      simpa [Matrix.toLpLin_mul_same] using h
    exact Ane0 ((Transpose_mul_self_eq_zero).1 hAtA)
  step : p.t ≤ 1 / p.L := by rw [p.teq]
  ori : p.x 0 = x₀ := p.ori
  hL : p.L > (0 : ℝ) := by
    rw [p.Leq]; simp
    intro h
    have hAtA : Aᵀ * A = 0 := by
      apply (Matrix.toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal))).injective
      simpa [Matrix.toLpLin_mul_same] using h
    exact Ane0 ((Transpose_mul_self_eq_zero).1 hAtA)
  update : ∀ (k : ℕ), prox_prop (p.t • p.h) (p.x k - p.t • p.f' (p.x k)) (p.x (k + 1)) := by
    intro k
    apply norm_one_proximal
    · rw [p.heq]
    · rw [p.teq]; simp
      rw [p.Leq]; simp
      intro h
      have hAtA : Aᵀ * A = 0 := by
        apply (Matrix.toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal))).injective
        simpa [Matrix.toLpLin_mul_same] using h
      exact Ane0 ((Transpose_mul_self_eq_zero).1 hAtA)
    · linarith
    · intro i; rw [p.update2 k, p.update1 k]

/- convergence of LASSO -/

variable {A : Matrix (Fin m) (Fin n) ℝ} {b : (Fin m) → ℝ} {μ : ℝ} {μpos : 0 < μ} {Ane0 : A ≠ 0}
variable {x₀ : (EuclideanSpace ℝ (Fin n))}
variable {alg : LASSO A b μ μpos Ane0 x₀}

theorem LASSO_converge : ∀ (k : ℕ+), (alg.f (alg.x k) + alg.h (alg.x k)
    - alg.f alg.xm - alg.h alg.xm) ≤ alg.L / (2 * k) * ‖x₀ - alg.xm‖ ^ 2 := by
  intro k
  have h₁ : alg.f (alg.x k) + alg.h (alg.x k) - alg.f alg.xm - alg.h alg.xm =
      alg.f (proximal_gradient_method.x alg.f alg.h alg.f' x₀ k)
      + alg.h (proximal_gradient_method.x alg.f alg.h alg.f' x₀ k)
      - alg.f (proximal_gradient_method.xm alg.f alg.h alg.f' x₀)
      - alg.h (proximal_gradient_method.xm alg.f alg.h alg.f' x₀) := rfl
  have h₂ : 1 / (2 * k * alg.t) * ‖x₀ - alg.xm‖ ^ 2 =
      1 / (2 * k * proximal_gradient_method.t alg.f alg.h alg.f' x₀)
      * ‖x₀ - proximal_gradient_method.xm alg.f alg.h alg.f' x₀‖ ^ 2 := rfl
  have h₃ : alg.L / (2 * k) = 1 / (2 * k * alg.t) := by
    rw [alg.teq]; field_simp
  rw [h₁, h₃, h₂]
  apply proximal_gradient_method_converge k

end LASSO
