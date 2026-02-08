import Mathlib.Analysis.CStarAlgebra.Matrix
import Reaslib.NumericalAlgebra.Defs
import Mathlib.Logic.Nontrivial.Basic
import Reaslib.NumericalAlgebra.Direct.SVD

namespace Matrix

open scoped Matrix BigOperators

section Norm

variable {α : Type*} [RCLike α]
variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

-- ℓ¹ ℓ² ℓ∞ vector norm
local notation "‖" x "‖₁" => @Norm.norm (EuclideanSpace α _) (PiLp.instNorm 1 fun _ => α) x
local notation "‖" x "‖₂" => @Norm.norm (EuclideanSpace α _) (PiLp.instNorm 2 fun _ => α) x
local notation "‖" x "‖∞" => @Norm.norm (EuclideanSpace α _) (PiLp.instNorm ⊤ fun _ => α) x

/-! ### 2-norm / spectral norm -/

/-- Vector compatibility: ‖A x‖₂ ≤ ‖A‖₂ ‖x‖₂ -/
theorem matrix2Norm_le_vec (A : Matrix m n α) (x : n → α) :
    ‖A.mulVec x‖₂ ≤ ‖A‖₂ * ‖x‖₂ := by
  by_cases hx : x = 0
  · rw [hx]
    simp only [Matrix.mulVec_zero, norm_zero, MulZeroClass.mul_zero, le_refl]
  · have h_norm_x_ne_zero : ‖x‖₂ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hx
    let c := ‖x‖₂
    let y := (c⁻¹) • x
    have h_norm_y : ‖y‖₂ = 1 := by
      rw [norm_smul]
      rw [norm_inv, norm_norm]
      exact inv_mul_cancel₀ h_norm_x_ne_zero
    have mul_vec_smul : A.mulVec x = c • A.mulVec y := by
      calc
        A.mulVec x
        _ = A.mulVec (c • y) := by
          unfold y
          rw [smul_smul]
          sorry
        _ = c • A.mulVec y := by exact mulVec_smul A c y
    have norm_mul : ‖A.mulVec x‖₂ = c * ‖A.mulVec y‖₂ := by
      rw [mul_vec_smul]
      rw [norm_smul, norm_norm]
    have le_sup : ‖A.mulVec y‖₂ ≤ ‖A‖₂ := by
        calc
          ‖A.mulVec y‖₂
          _ ≤ ‖A‖₂ * ‖y‖₂ := by
            sorry
          _ = ‖A‖₂ * 1 := by rw [h_norm_y]
          _ = ‖A‖₂ := by rw [mul_one]
    calc
      ‖A.mulVec x‖₂ = c * ‖A.mulVec y‖₂ := norm_mul
      _ ≤ c * ‖A‖₂ := by gcongr
      _ = ‖A‖₂ * c := by exact CommMonoid.mul_comm c (‖A‖₂)
      _ = ‖A‖₂ * ‖x‖₂ := rfl

/-- Submultiplicativity: ‖A B‖₂ ≤ ‖A‖₂ ‖B‖₂ -/
theorem matrix2Norm_mul_le (A : Matrix m n α) (B : Matrix n k α) :
    ‖A * B‖₂ ≤ ‖A‖₂ * ‖B‖₂ := by
  sorry

omit [DecidableEq n] in
@[simp]
theorem matrix2Norm_nonneg (A : Matrix m n α) : 0 ≤ ‖A‖₂ :=
  ContinuousLinearMap.opNorm_nonneg _

@[simp]
theorem matrix2Norm_eq_zero_iff (A : Matrix m n α) : ‖A‖₂ = 0 ↔ A = 0 := by
  sorry

@[simp]
theorem matrix2Norm_smul (c : α) (A : Matrix m n α) :
    ‖c • A‖₂ = ‖c‖ * ‖A‖₂ := by
  sorry

@[simp]
theorem matrix2Norm_add_le (A B : Matrix m n α) :
    ‖A + B‖₂ ≤ ‖A‖₂ + ‖B‖₂ := by
  sorry

/-! ### 1-norm (maximum column sum) -/

/-- 1-norm vector compatibility: ‖A x‖₁ ≤ ‖A‖₁ ‖x‖₁ -/
theorem matrix1Norm_le_vec (A : Matrix m n α) (x : n → α) :
  ‖A.mulVec x‖₁ ≤ ‖A‖₁ * ‖x‖₁ :=
sorry

/-- 1-norm submultiplicativity: ‖A B‖₁ ≤ ‖A‖₁ ‖B‖₁ -/
theorem matrix1Norm_mul_le (A : Matrix m n α) (B : Matrix n k α) :
  ‖A * B‖₁ ≤ ‖A‖₁ * ‖B‖₁ := by
  sorry

@[simp]
theorem matrix1Norm_nonneg (A : Matrix m n α) : 0 ≤ ‖A‖₁ :=
sorry

@[simp]
theorem matrix1Norm_eq_zero_iff (A : Matrix m n α) : ‖A‖₁ = 0 ↔ A = 0 :=
sorry

@[simp]
theorem matrix1Norm_smul (c : α) (A : Matrix m n α) :
  ‖c • A‖₁ = ‖c‖ * ‖A‖₁ :=
sorry

@[simp]
theorem matrix1Norm_add_le (A B : Matrix m n α) :
  ‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁ :=
sorry

/-! ### ∞-norm (maximum row sum) -/

/-- ∞-norm vector compatibility: ‖A x‖_∞ ≤ ‖A‖_∞ ‖x‖_∞ -/
theorem matrixInfNorm_le_vec (A : Matrix m n α) (x : n → α) :
  ‖A.mulVec x‖∞ ≤ ‖A‖_∞ * ‖x‖∞ :=
sorry

/-- ∞-norm submultiplicativity: ‖A B‖_∞ ≤ ‖A‖_∞ ‖B‖_∞ -/
theorem matrixInfNorm_mul_le (A : Matrix m n α) (B : Matrix n k α) :
  ‖A * B‖_∞ ≤ ‖A‖_∞ * ‖B‖_∞ :=
sorry

@[simp]
theorem matrixInfNorm_nonneg (A : Matrix m n α) : 0 ≤ ‖A‖_∞ :=
sorry

@[simp]
theorem matrixInfNorm_eq_zero_iff (A : Matrix m n α) : ‖A‖_∞ = 0 ↔ A = 0 :=
sorry

@[simp]
theorem matrixInfNorm_smul (c : α) (A : Matrix m n α) :
  ‖c • A‖_∞ = ‖c‖ * ‖A‖_∞ :=
sorry

@[simp]
theorem matrixInfNorm_add_le (A B : Matrix m n α) :
  ‖A + B‖_∞ ≤ ‖A‖_∞ + ‖B‖_∞ :=
sorry

/-! ### Frobenius norm -/

/-- Frobenius norm vector compatibility: ‖A x‖₂ ≤ ‖A‖_F ‖x‖₂
    Note: Frobenius norm is not an induced norm, but this inequality holds as a bound. -/
theorem frobeniusNorm_le_vec (A : Matrix m n α) (x : n → α) :
  ‖A.mulVec x‖ ≤ ‖A‖_F * ‖x‖ :=
sorry

/-- Frobenius norm submultiplicativity: ‖A B‖_F ≤ ‖A‖_F ‖B‖_F -/
theorem frobeniusNorm_mul_le (A : Matrix m n α) (B : Matrix n k α) :
  ‖A * B‖_F ≤ ‖A‖_F * ‖B‖_F :=
sorry

@[simp]
theorem frobeniusNorm_nonneg (A : Matrix m n α) : 0 ≤ ‖A‖_F :=
sorry

@[simp]
theorem frobeniusNorm_eq_zero_iff (A : Matrix m n α) : ‖A‖_F = 0 ↔ A = 0 :=
sorry

@[simp]
theorem frobeniusNorm_smul (c : α) (A : Matrix m n α) :
  ‖c • A‖_F = ‖c‖ * ‖A‖_F :=
sorry

@[simp]
theorem frobeniusNorm_add_le (A B : Matrix m n α) :
  ‖A + B‖_F ≤ ‖A‖_F + ‖B‖_F :=
sorry

/-- The spectral norm of a matrix equals its largest singular value. -/
theorem norm2_eq_largestSingularValue {m n r : ℕ}
    [InnerProductSpace α (Fin m → α)] [InnerProductSpace α (Fin n → α)]
    (A : Matrix (Fin m) (Fin n) α) :
    ‖A‖₂ = A.largestSingularValue := by
  sorry

/-- Frobenius norm and trace relationship.

    The Frobenius norm (a.k.a. Hilbert–Schmidt norm) is defined by
      ‖A‖_F = sqrt (trace (A * A^*)),
    where `A^*` is conjugate-transpose.

    Here we state the equality between the squared Frobenius norm and the trace.
-/
theorem frobenius_sq_eq_trace_mul_conjTranspose (A : Matrix m n α) :
    ‖A‖_F ^ 2 = (trace (A * Aᵀ)) := by
  sorry

omit [DecidableEq m] in
/-- ℓ∞ ≤ ℓ2 -/
theorem norm_inf_le_norm2 (x : EuclideanSpace α m) :
  ‖x‖∞ ≤ ‖x‖₂ := by
  have h1 : ∀ i, ‖x i‖ ≤ ‖x‖₂ := by
    intro i
    rw [EuclideanSpace.norm_eq x]
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (fun j _ => sq_nonneg (‖x j‖)) (Finset.mem_univ i)
  by_cases h : Nonempty m
  · -- Case 1: m is nonempty
    exact ciSup_le h1
  · -- Case 2: m is empty
    have : IsEmpty m := by exact not_nonempty_iff.mp h
    have : ‖x‖∞ = 0 := by
      exact Real.iSup_of_isEmpty fun i ↦ ‖x i‖
    have : ‖x‖₂ = 0 := by
      rw [EuclideanSpace.norm_eq x]
      simp only
      have h_sum_is_zero : (∑ i, ‖x i‖ ^ 2) = 0 := by
        exact Fintype.sum_empty fun x_1 ↦ ‖x x_1‖ ^ 2
      rw [h_sum_is_zero]
      exact Real.sqrt_zero
    rw [this]
    (expose_names; exact le_of_eq this_2)

omit [DecidableEq m] in
/-- ℓ2 ≤ √(dim V) ℓ∞ -/
theorem norm2_le_sqrt_dim_norm_inf (x : EuclideanSpace α m) :
  ‖x‖₂ ≤ Real.sqrt (Fintype.card m) * ‖x‖∞ := by
  rw [EuclideanSpace.norm_eq x]
  have bdd : BddAbove (Set.range (fun i : m => ‖x i‖)) := by
    refine ⟨⨆ i, ‖x i‖, ?_⟩
    intro r hr
    rcases hr with ⟨i, hi⟩
    rw [← hi]
    exact le_ciSup  (f := fun i => ‖x i‖) (by simp) i
  have h_le_inf : ∀ i, ‖x i‖ ≤ ‖x‖∞ := by
    intro i
    exact le_ciSup bdd i
  have h_sum_sq_le_card_sq : ∑ i, ‖x i‖^2 ≤ (Fintype.card m : ℝ) * ‖x‖∞^2 := by
    calc
      ∑ i, ‖x i‖^2 ≤ ∑ i, ‖x‖∞^2 := Finset.sum_le_sum fun i _ => by
        exact pow_le_pow_left₀ (norm_nonneg _) (h_le_inf i) 2
      _ = (Fintype.card m : ℝ) * ‖x‖∞^2 := by
        rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  have h_sqrt_ineq : Real.sqrt (∑ i, ‖x i‖^2) ≤ Real.sqrt ((Fintype.card m : ℝ) * ‖x‖∞^2) := by
    apply Real.sqrt_le_sqrt h_sum_sq_le_card_sq
  rw [Real.sqrt_mul (Nat.cast_nonneg _)] at h_sqrt_ineq
  rw [Real.sqrt_sq_eq_abs] at h_sqrt_ineq
  have h_norm_nonneg : 0 ≤ ‖x‖∞ := by
    have : ∀ i, 0 ≤ ‖x i‖ := fun i => norm_nonneg (x i)
    exact Real.iSup_nonneg this
  rw [abs_of_nonneg h_norm_nonneg] at h_sqrt_ineq
  exact h_sqrt_ineq

/-- ℓ2 ≤ ℓ1 -/
theorem norm2_le_norm1 (x : EuclideanSpace α m) :
  ‖x‖₂ ≤ ‖x‖₁ := by
  have sum_norm_nonneg : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  simp [PiLp.norm_eq_of_L1 x]
  rw [EuclideanSpace.norm_eq x]
  have h4 : ∑ i, ‖x i‖ ^ 2 ≤ (∑ i, ‖x i‖) ^ 2 := by
    calc
      ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖x i‖ * (∑ j, ‖x j‖) :=
        Finset.sum_le_sum fun i _ => by
          have : ‖x i‖ ^ 2 ≤ ‖x i‖ * (∑ j, ‖x j‖) := by
            have h : ‖x i‖ ≤ ∑ j, ‖x j‖ :=
              Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)
            nlinarith [norm_nonneg (x i)]
          exact this
      _ = (∑ i, ‖x i‖) * (∑ j, ‖x j‖) := by
        exact Eq.symm (Finset.sum_mul Finset.univ (fun i ↦ ‖x i‖) (∑ j, ‖x j‖))
      _ = (∑ i, ‖x i‖) ^ 2 := by ring
  calc
    Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt ((∑ i, ‖x i‖) ^ 2) := Real.sqrt_le_sqrt h4
    _ = |∑ i, ‖x i‖| := Real.sqrt_sq_eq_abs _
    _ = ∑ i, ‖x i‖ := abs_of_nonneg sum_norm_nonneg

omit [DecidableEq m] in
/-- ℓ1 ≤ √(dim V) ℓ2 -/
theorem norm1_le_sqrt_dim_norm2 (x : EuclideanSpace α m) :
  ‖x‖₁ ≤ Real.sqrt (Fintype.card m) * ‖x‖₂ := by
  have sum_norm_nonneg : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  simp [PiLp.norm_eq_of_L1 x]
  rw [EuclideanSpace.norm_eq x]
  -- Applying the Cauchy-Schwarz inequality. We regard the vectors a =
  -- (‖x_i‖) and b = (1) as vectors in R^m.
  have h_cs : (∑ i : m, ‖x i‖ * 1) ^ 2 ≤ (∑ i : m, ‖x i‖ ^ 2) * (∑ i : m, 1 ^ 2) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ ‖x i‖) fun i ↦ 1
  have h_card : (∑ i : m, 1 ^ 2) = Fintype.card m := by
    simp [one_pow, Finset.sum_const, Finset.card_univ]
  have h_sum_sq_nonneg : 0 ≤ ∑ i, ‖x i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc
    (∑ i, ‖x i‖)
    _ = Real.sqrt ((∑ i, ‖x i‖) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [← abs_of_nonneg sum_norm_nonneg]
      exact Eq.symm (abs_abs (∑ i, ‖x i‖))
    _ ≤ Real.sqrt ((∑ i, ‖x i‖ ^ 2) * (Fintype.card m)) := by
      refine Real.sqrt_le_sqrt ?_
      calc
        (∑ i, ‖x i‖) ^ 2
        _ = (∑ i, ‖x i‖ * 1) ^ 2 := by simp
        _ ≤ (∑ i, ‖x i‖ ^ 2) * (∑ i, 1 ^ 2) := h_cs
        _ = (∑ i, ‖x i‖ ^ 2) * (Fintype.card m) := by
          simp [one_pow, Finset.sum_const, Finset.card_univ]
    _ = Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (Fintype.card m) := by
      exact Real.sqrt_mul h_sum_sq_nonneg ↑(Fintype.card m)
    _ = Real.sqrt (Fintype.card m) * Real.sqrt (∑ i, ‖x i‖ ^ 2) := by ring

/-- ℓ∞ ≤ ℓ1 -/
theorem norm_inf_le_norm1 (x : EuclideanSpace α m) :
  ‖x‖∞ ≤ ‖x‖₁ := by
  rw [show ‖x‖∞ = ⨆ i, ‖x i‖ by exact rfl]
  simp [PiLp.norm_eq_of_L1 x]
  have h_le_sum : ∀ i, ‖x i‖ ≤ ∑ j, ‖x j‖ := by
    intro i
    exact Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)
  by_cases h : Nonempty m
  · -- Case 1: m is nonempty
    exact ciSup_le h_le_sum
  · -- Case 2: m is empty
    have : IsEmpty m := not_nonempty_iff.mp h
    simp [Real.iSup_of_isEmpty]

omit [DecidableEq m] in
/-- ℓ1 ≤ dim V ℓ∞ -/
theorem norm1_le_dim_norm_inf (x : EuclideanSpace α m) :
  ‖x‖₁ ≤ (Fintype.card m : ℝ) * ‖x‖∞ := by
  have h_le_inf : ∀ i, ‖x i‖ ≤ ‖x‖∞ := by
    intro i
    have bdd : BddAbove (Set.range (fun i : m => ‖x i‖)) := by
      refine ⟨⨆ i, ‖x i‖, ?_⟩
      intro r hr
      rcases hr with ⟨j, hj⟩
      rw [← hj]
      exact le_ciSup (f := fun k => ‖x k‖) (by simp) j
    exact le_ciSup bdd i
  simp [PiLp.norm_eq_of_L1 x]
  calc
    ∑ i, ‖x i‖ ≤ ∑ i, ‖x‖∞ := Finset.sum_le_sum fun i _ => h_le_inf i
    _ = (Fintype.card m : ℝ) * ‖x‖∞ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- Frobenius vs spectral norm: ‖A‖₂ ≤ ‖A‖_F ≤ √(min dim) ‖A‖₂ -/
theorem matrix_norm_two_le_frobenius (A : Matrix m n α) :
  ‖A‖₂ ≤ ‖A‖_F ∧ ‖A‖_F ≤ Real.sqrt (min (Fintype.card m) (Fintype.card n)) * ‖A‖₂ :=
sorry

/-- ∞-norm vs spectral norm -/
theorem matrix_norm_two_vs_inf (A : Matrix m n α) :
  ‖A‖₂ ≤ Real.sqrt (Fintype.card m) * ‖A‖_∞ ∧
  ‖A‖_∞ ≤ Real.sqrt (Fintype.card n) * ‖A‖₂ :=
sorry

/-- 1-norm vs spectral norm -/
theorem matrix_norm_two_vs_one (A : Matrix m n α) :
  ‖A‖₂ ≤ Real.sqrt (Fintype.card n) * ‖A‖₁ ∧
  ‖A‖₁ ≤ Real.sqrt (Fintype.card m) * ‖A‖₂ :=
sorry

/-- The Frobenius norm of a product is bounded by the product of
    the spectral/Frobenius norm of the first matrix and
    the Frobenius/spectral norm of the second matrix:

      ‖A B‖_F ≤ ‖A‖₂ * ‖B‖_F
      ‖A B‖_F ≤ ‖A‖_F * ‖B‖₂

    These are standard inequalities relating operator (2-)norm and Frobenius norm. -/
theorem frobeniusNorm_mul_le_two (A : Matrix m n α) (B : Matrix n k α) :
    ‖A * B‖_F ≤ ‖A‖₂ * ‖B‖_F := by
  sorry

theorem frobeniusNorm_mul_le_two' (A : Matrix m n α) (B : Matrix n k α) :
    ‖A * B‖_F ≤ ‖A‖_F * ‖B‖₂ := by
  sorry

/-- Spectral characterization: there exists a unit eigenvector for Aᵀ * A -/
theorem exists_unit_eigenvector_of_atA (A : Matrix m n α) :
  ∃ (z : EuclideanSpace α n),
    ‖z‖ = 1 ∧
    (Aᴴ * A).mulVec z = (‖A‖₂ ^ 2) • z :=
sorry

/-- Spectral norm bounded by 1-norm and ∞-norm -/
theorem matrix_spectral_norm_le_sqrt_one_inf (A : Matrix m n α) :
  ‖A‖₂ ≤ Real.sqrt (‖A‖₁ * ‖A‖_∞) :=
sorry

end Norm

section Perturbation

variable {α : Type*} [RCLike α]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Neumann series bound in 2-norm -/
theorem neumann_series_matrix_lp (F : Matrix n n α) (hF : ‖F‖₂ < 1) :
  Nonempty (IsUnit (1 - F)) ∧
  ∃ S : Matrix n n α, HasSum (fun k : ℕ => F ^ k) S ∧ ‖S‖₂ ≤ 1 / (1 - ‖F‖₂) :=
sorry

/-- Matrix inverse perturbation bound in 2-norm -/
theorem matrix_inverse_perturbation_bound (A E : Matrix n n α)
  (hA : IsUnit A) (h : ‖A⁻¹ * E‖₂ < 1) :
  Nonempty (IsUnit (A + E)) ∧
  ‖(A + E)⁻¹ - A⁻¹‖₂ ≤ ‖A⁻¹‖₂ ^ 2 * ‖E‖₂ / (1 - ‖A⁻¹ * E‖₂) :=
sorry

end Perturbation

section Invariance

variable {α : Type*} [RCLike α]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Frobenius norm invariant under multiplication by unitary matrices -/
theorem frobenius_norm_unitary
  (A : Matrix m n α) (U : Matrix m m α) (V : Matrix n n α)
  (hU : IsUnit U) (hV : IsUnit V) :
  ‖U * A * V‖_F = ‖A‖_F :=
sorry

/-- Spectral norm invariant under multiplication by unitary matrices -/
theorem spectral_norm_unitary
  (A : Matrix m n α) (U : Matrix m m α) (V : Matrix n n α)
  (hU : IsUnit U) (hV : IsUnit V) :
  ‖U * A * V‖₂ = ‖A‖₂ :=
sorry

end Invariance
end Matrix
