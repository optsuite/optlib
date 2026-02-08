import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

noncomputable section Norm

/-- the `ℝ`-valued Frobenius norm. -/
abbrev FNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.frobeniusSeminormedAddCommGroup).norm X

/-- the `ℝ`-valued `L^∞` operator norm. -/
abbrev LinftyNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.linftyOpSeminormedAddCommGroup).norm X

/-- the `ℝ`-valued `L¹` operator norm. -/
abbrev LoneNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.linftyOpSeminormedAddCommGroup).norm Xᵀ

/-- the `ℝ`-valued `L²` operator norm. -/
abbrev LtwoNorm {α m n} [Fintype m] [Fintype n] [DecidableEq m] [RCLike α] : Matrix m n α → ℝ :=
  fun X => (Matrix.instL2OpNormedAddCommGroup).norm Xᵀ

@[inherit_doc] notation:100 "‖" A "‖_F" => FNorm A
@[inherit_doc] notation:100 "‖" A "‖_∞" => LinftyNorm A
@[inherit_doc] notation:100 "‖" A "‖₁" => LoneNorm A
@[inherit_doc] notation:100 "‖" A "‖₂" => LtwoNorm A

def Norm_ofPosDef {n : Type*} [Fintype n] (A : {X : Matrix n n ℝ // Matrix.PosDef X}) :
    (n → ℝ) → ℝ :=
  fun x ↦ Real.sqrt (x ⬝ᵥ (A *ᵥ x))

instance Norm_ofPosDef.toNorm {n : Type*} [Fintype n] (A : {X : Matrix n n ℝ // Matrix.PosDef X}) :
    Norm (n → ℝ) where
  norm := Norm_ofPosDef A

variable {m n R α} [Fintype m] [Fintype n] [NormedField R] [SeminormedAddCommGroup α]
  [NormedSpace R α] {X : Matrix m n R}

#check ‖X‖_F
#check ‖X‖₁
#check ‖X‖_∞

variable {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n']
  {X : Matrix m' n' ℝ}
#check ‖X‖₂

end Norm

-- noncomputable section Condition_Number

-- def Matrix.conditionNumber {n : Type*} [Fintype n] [DecidableEq n]
--     (A : Matrix n n ℝ) [Invertible A] : ℝ :=
--   ‖A‖₂ * ‖A⁻¹‖₂

-- end Condition_Number

section matrix_structure

def Matrix.lowerPart {n α : Type*} [LE n] [DecidableLE n] (X : Matrix n n α) [Zero α] :
  Matrix n n α := fun i j => if j ≥ i then 0 else X i j

def Matrix.upperPart {n α : Type*} [LE n] [DecidableLE n] (X : Matrix n n α) [Zero α] :
  Matrix n n α := fun i j => if j ≤ i then 0 else X i j

lemma Matrix.transpose_lowerPart_eq_upperPart
    {n α : Type*} [LE n] [DecidableLE n] (X : Matrix n n α) [Zero α] :
    (Matrix.lowerPart X)ᵀ = Matrix.upperPart Xᵀ := by
  ext i j
  simp [lowerPart, upperPart]

abbrev Matrix.diagPart {n α : Type*} [DecidableEq n] (X : Matrix n n α) [Zero α] :=
  Matrix.diagonal (fun i => X i i)

lemma Matrix.part_decompose {n α : Type*} [LinearOrder n] (X : Matrix n n α) [AddZeroClass α] :
    X = Matrix.lowerPart X + Matrix.upperPart X + Matrix.diagPart X := by
  ext i j
  simp only [diagonal, add_apply, lowerPart, ge_iff_le, upperPart, of_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  on_goal 2 => exact absurd (le_antisymm h1 h2) h3
  on_goal 7 => exact absurd (not_le.mp h1).le h5
  all_goals simp_all

theorem Matrix.diagnonzero_diagInvertable
    {n α : Type*} [Fintype n] [DecidableEq n] [Field α] (A : Matrix n n α)
    (hA : ∀ i, A i i ≠ 0) : IsUnit (Matrix.diagPart A) := by
  simpa [Matrix.isUnit_diagonal, Pi.isUnit_iff] using hA

theorem Matrix.diagnonzero_diagInvertable'
    {n α : Type*} [Fintype n] [DecidableEq n] [Field α]
    (A : {X : Matrix n n α // ∀ i, X i i ≠ 0}) : IsUnit (Matrix.diagPart A.1) :=
  (A.1).diagnonzero_diagInvertable A.2

end matrix_structure

section iterative_method

def linearsystem.residual {n : ℕ} {α : Type*} [Field α] (A : Matrix (Fin n) (Fin n) α)
  (b : (Fin n) → α) : (Fin n → α) → (Fin n → α) := fun x ↦ b - (A *ᵥ x)

structure Stationary_iterative {n : ℕ} {α : Type*} [Field α] (x0 : (Fin n) → α) where
  M : Matrix (Fin n) (Fin n) α
  g : (Fin n) → α

def Stationary_iterative.x {n : ℕ} {α : Type*} [Field α] {x0 : (Fin n) → α}
    (self : Stationary_iterative x0) : ℕ → ((Fin n) → α)
  | 0 => x0
  | p + 1 => self.M *ᵥ (self.x p) + self.g

lemma Stationary_iterative.x_zero {n : ℕ} {α : Type*} [Field α] {x0 : (Fin n) → α}
    (self : Stationary_iterative x0) : self.x 0 = x0 := rfl

lemma Stationary_iterative.x_succ {n : ℕ} {α : Type*} [Field α] {x0 : (Fin n) → α}
    (self : Stationary_iterative x0) (p : ℕ) : self.x (p + 1) = self.M *ᵥ (self.x p) + self.g := rfl

noncomputable def Jacobi {n : ℕ} {α : Type*} [Field α] (A : Matrix (Fin n) (Fin n) α)
    (hA : ∀ i, A i i ≠ 0) (b : (Fin n) → α) (x0 : (Fin n) → α) : Stationary_iterative x0 :=
  letI Dinv : Matrix (Fin n) (Fin n) α := (A.diagnonzero_diagInvertable hA).unit.inv
  {
    M := Dinv * (A.diagPart - A)
    g := Dinv *ᵥ b
  }

variable {n : ℕ} {α : Type*} [Field α]

lemma Jacobi.update (b : (Fin n) → α) (x0 : (Fin n) → α)
    (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0) (p : ℕ) :
    (Jacobi A hA b x0).x (p + 1) =
    (Jacobi A hA b x0).M *ᵥ (Jacobi A hA b x0).x p + (Jacobi A hA b x0).g := rfl

end iterative_method

section gauss_iterative_method

open Matrix Finset Filter Topology spectrum

variable {α : Type*} {n : ℕ} [NormedField α]

lemma lemma_le_0_1 (M : Matrix (Fin n) (Fin n) α) (hM : ∀ i, M i i ≠ 0) :
    ∏ i, M i i ≠ 0
    := by
  rw [@prod_ne_zero_iff]
  intro a ha
  exact hM a

lemma lemma_eq_2_1 (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0) :
    ∀ i, IsUnit ((A.diagPart + A.lowerPart) i i) := by
  intro i
  simp [lowerPart]
  exact hA i

lemma lemma_3_1 (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0) :
    IsUnit (A.diagPart + A.lowerPart).det := by
  have h_diag : ∀ i, IsUnit ((A.diagPart + A.lowerPart) i i) := by
    exact lemma_eq_2_1 A hA
  have hd : A.diagPart.BlockTriangular ⇑OrderDual.toDual := by
    simp [diagPart]
    exact blockTriangular_diagonal fun i ↦ A i i
  have hl : A.lowerPart.BlockTriangular ⇑OrderDual.toDual := by
    unfold lowerPart
    unfold BlockTriangular
    simp
    intro i j hij hji
    absurd hij
    simpa using hji.le
  have h : (A.diagPart + A.lowerPart).BlockTriangular ⇑OrderDual.toDual := by
    exact BlockTriangular.add hd hl
  have det_eq : (A.diagPart + A.lowerPart).det = ∏ i : (Fin n), (A.diagPart + A.lowerPart) i i :=
    det_of_lowerTriangular (A.diagPart + A.lowerPart) h
  have det_unit : IsUnit (A.diagPart + A.lowerPart).det := by
    rw [det_eq]
    simp [- add_apply]
    push_neg
    simp [- add_apply] at h_diag
    push_neg at h_diag
    exact lemma_le_0_1 (A.diagPart + A.lowerPart) h_diag
  exact det_unit

theorem Matrix.diagnonzero_diag_minus_lowerPart_Invertable
    (A : Matrix (Fin n) (Fin n) α)
    (hA : ∀ i, A i i ≠ 0) :
    let D := A.diagPart
    let L := -A.lowerPart
    -- let U := -A.upperPart
    IsUnit (D - L) := by
  intro D L
  simp [D, L]
  have det_unit : IsUnit (A.diagPart + A.lowerPart).det := by
    exact lemma_3_1 A hA
  exact (isUnit_iff_isUnit_det (A.diagPart + A.lowerPart)).mpr det_unit

noncomputable def GaussSeidel (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, (A i i) ≠ 0)
    (b : (Fin n) → α) (x0 : (Fin n) → α) : Stationary_iterative x0 :=
  letI D_add_L_inv : Matrix (Fin n) (Fin n) α :=
    (A.diagnonzero_diag_minus_lowerPart_Invertable hA).unit.inv
  {
    M := D_add_L_inv * (-A.upperPart)
    g := D_add_L_inv *ᵥ b
  }

variable {x0 : (Fin n) → α} {A : Matrix (Fin n) (Fin n) α} {hA : ∀ i, (A i i) ≠ 0}
  {b : (Fin n) → α} {x0 : (Fin n) → α}

lemma GaussSeidel.update (alg := GaussSeidel A hA b x0) (p : ℕ) :
    alg.x (p + 1) = alg.M *ᵥ alg.x p + alg.g := rfl

end gauss_iterative_method

section JacobiFolder

open Matrix
open scoped ENNReal

/-- Vector ℓ∞ norm: max_i |x i| -/
noncomputable def vecInftyNorm {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) : ℝ :=
  norm x

open Matrix Finset BigOperators

variable {n : Nat} {i j : Fin n} {x_star : Fin n → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
  {hA : ∀ i, A i i ≠ 0} {b : Fin n → ℝ} {x0 : Fin n → ℝ}

-- def 𝓊 i
noncomputable def Vector_u (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, A i i ≠ 0) (b : Fin n → ℝ)
    (x0 : Fin n → ℝ) (i : Fin n) := ∑ j ∈ {t | t < i}, |(Jacobi A hA b x0).M i j|

-- def ℓ i
noncomputable def Vector_l (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, A i i ≠ 0) (b : Fin n → ℝ)
    (x0 : Fin n → ℝ) (i : Fin n) := ∑ j ∈ {t | t ≥ i}, |(Jacobi A hA b x0).M i j|

-- def μ
noncomputable def mu
  [NeZero n]
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∀ i, A i i ≠ 0)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  ℝ
  :=
  have h : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  Finset.max' (Finset.univ.image (fun i : Fin n =>
    Vector_u A hA b x0 i / (1 - Vector_l A hA b x0 i))) (by simp [h])

-- end def424

-- section def426

open Finset Matrix

-- Diagonal entries > 0 imply nonzero.
lemma diagpos_to_nonzero
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  ∀ i, A i i ≠ 0
  := by
  exact fun i ↦ Ne.symm (ne_of_lt (hdiag i))

-- def D⁻¹
noncomputable def diagonal_inv
  (A : Matrix (Fin n) (Fin n) ℝ)
  -- (hA : ∀ i, A i i ≠ 0)
  : Matrix (Fin n) (Fin n) ℝ
  :=
  fun i j => if i = j then (1 / (A i j)) else 0

--  D ⁻¹ = D⁻¹
-- inv_eq A hA
lemma inv_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∀ i, A i i ≠ 0)
  :
  (diagPart A)⁻¹ = diagonal_inv A
  := by
  ext i j
  rw [Matrix.inv_def]
  unfold diagonal_inv
  by_cases h : i = j
  · split_ifs
    rw [h]
    simp only [det_diagonal, Ring.inverse_eq_inv', adjugate_diagonal, smul_apply,
      diagonal_apply_eq, smul_eq_mul, one_div]
    refine (IsUnit.inv_mul_eq_iff_eq_mul ?_).mpr ?_
    · have h1 : ∏ i, A i i ≠ 0 := by
        exact prod_ne_zero_iff.mpr fun a a_1 ↦ hA a
      exact Ne.isUnit h1
    · refine Eq.symm (CancelDenoms.inv_subst (hA j) ?_)
      refine prod_erase_mul univ (fun «x» ↦ A «x» «x») ?_
      exact mem_univ j
  · split_ifs
    simp only [det_diagonal, Ring.inverse_eq_inv', adjugate_diagonal, smul_apply, smul_eq_mul,
      mul_eq_zero, inv_eq_zero]
    right
    exact diagonal_apply_ne' (fun i ↦ ∏ i ∈ univ.erase i, A i i) fun a ↦ h (id (Eq.symm a))

-- D⁻¹ * D = 1
lemma inv_mul_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (diagonal_inv A) * (diagPart A) = 1
  := by
  refine ext ?_
  intro i j
  have h1 : ((diagonal_inv A) * (diagPart A)) i j =
    ∑ k, ((diagonal_inv A) i k) * ((diagPart A) k j) := rfl
  unfold diagonal_inv diagPart
  by_cases h2 : i = j
  · rw [h2]
    simp only [one_div, mul_diagonal, ↓reduceIte, one_apply_eq]
    refine IsUnit.inv_mul_cancel ?_
    have h3 : A j j ≠ 0 := by
      exact diagpos_to_nonzero A hdiag j
    exact Ne.isUnit h3
  · simp only [one_div, mul_diagonal, ite_mul, zero_mul]
    split_ifs
    exact Eq.symm (one_apply_ne' fun a ↦ h2 (id (Eq.symm a)))

-- def D^1/2
noncomputable def sqrtdiagPart
  (A : Matrix (Fin n) (Fin n) ℝ)
  :
  Matrix (Fin n) (Fin n) ℝ
  :=
  fun i j ↦ if i = j then Real.sqrt (A i j) else 0

-- def D^-1/2
noncomputable def negsqrtdiagPart
  (A : Matrix (Fin n) (Fin n) ℝ)
  :
  Matrix (Fin n) (Fin n) ℝ
  :=
  fun i j ↦ if i = j then 1 / Real.sqrt (A i j) else 0

-- D^-1/2 * D^1/2 = 1
lemma sqrt_eq_one
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (negsqrtdiagPart A) * (sqrtdiagPart A) = 1
  := by
  refine ext ?_
  intro i j
  have h1 : ((negsqrtdiagPart A) * (sqrtdiagPart A)) i j =
    ∑ k, ((negsqrtdiagPart A) i k) * ((sqrtdiagPart A) k j) := rfl
  rw [h1]
  unfold negsqrtdiagPart sqrtdiagPart
  simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  by_cases h2 : i = j
  · split_ifs
    refine (IsUnit.inv_mul_eq_iff_eq_mul ?_).mpr ?_
    · rw [h2]
      have h3 : A j j ≠ 0 := by
        exact diagpos_to_nonzero A hdiag j
      have h4 : Real.sqrt (A j j) ≠ 0 := by
        exact Real.sqrt_ne_zero'.mpr (hdiag j)
      exact Ne.isUnit h4
    · rw [h2]
      simp only [one_apply_eq, mul_one]
  · split_ifs
    exact Eq.symm (one_apply_ne' fun a ↦ h2 (id (Eq.symm a)))

-- D^1/2 * D^-1/2 = 1
lemma sqrt_eq_one'
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (sqrtdiagPart A) * (negsqrtdiagPart A) = 1
  := by
  refine ext ?_
  intro i j
  have h1 : ((sqrtdiagPart A) * (negsqrtdiagPart A)) i j =
    ∑ k, ((sqrtdiagPart A) i k) * ((negsqrtdiagPart A) k j) := rfl
  rw [h1]
  unfold sqrtdiagPart negsqrtdiagPart
  simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  by_cases h2 : i = j
  · split_ifs
    rw [h2]
    refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
    · exact Real.sqrt_ne_zero'.mpr (hdiag j)
    · simp only [one_apply_eq, one_mul]
  · split_ifs
    exact Eq.symm (one_apply_ne' fun a ↦ h2 (id (Eq.symm a)))

--  D^-1/2 * D^-1/2 = D⁻¹
lemma negsqrt_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (negsqrtdiagPart A) * (negsqrtdiagPart A) = diagonal_inv A
  := by
  refine ext ?_
  intro i j
  have h1 : ((negsqrtdiagPart A) * (negsqrtdiagPart A)) i j =
    ∑ k, ((negsqrtdiagPart A) i k) * ((negsqrtdiagPart A) k j) := rfl
  rw [h1]
  unfold diagonal_inv negsqrtdiagPart
  simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  by_cases h2 : i = j
  · split_ifs
    rw [h2]
    rw [← mul_inv, ← pow_two]
    simp only [_root_.inv_inj]
    refine Real.sq_sqrt ?_
    exact le_of_lt (hdiag j)
  · split_ifs
    rfl

-- D^1/2 * D^1/2 = D
lemma sqrtpos_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (sqrtdiagPart A) * (sqrtdiagPart A) = diagPart A
  := by
  refine ext ?_
  intro i j
  have h1 : ((sqrtdiagPart A) * (sqrtdiagPart A)) i j =
    ∑ k, ((sqrtdiagPart A) i k) * ((sqrtdiagPart A) k j) := rfl
  rw [h1]
  unfold sqrtdiagPart diagPart diagonal
  by_cases h2 : i = j
  · simp only [mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, of_apply]
    split_ifs
    rw [h2]
    rw [← pow_two]
    refine Real.sq_sqrt ?_
    exact le_of_lt (hdiag j)
  · simp only [mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, of_apply]
    split_ifs
    rfl

#check mul_adjugate
#check Matrix.inv_subsingleton
#check isDiag_iff_diagonal_diag
#check IsDiag
-- D^-1/2⁻¹ = D^1/2
lemma negsqrt_inv_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (negsqrtdiagPart A)⁻¹ = sqrtdiagPart A
  := by
  refine ext ?_
  intro i j
  unfold negsqrtdiagPart sqrtdiagPart
  simp only [one_div]
  by_cases h1 : i = j
  · split_ifs
    rw [Matrix.inv_def]
    simp only [Ring.inverse_eq_inv', smul_apply, smul_eq_mul]
    let B := fun i j ↦ if i = j then (√(A i j))⁻¹ else 0
    have h11 : B = fun i j ↦ if i = j then (√(A i j))⁻¹ else 0 := rfl
    rw [← h11, h1]
    have h12 : √(A j j) = (B j j)⁻¹ := by
      unfold B
      simp only [↓reduceIte, inv_inv]
    rw [h12]
    sorry
  · split_ifs
    sorry

-- D^-1/2ᵀ = D^-1/2
lemma sqrt_symm
  (A : Matrix (Fin n) (Fin n) ℝ)
  :
  (negsqrtdiagPart A)ᵀ = negsqrtdiagPart A
  := by
  refine ext ?_
  intro i j
  unfold negsqrtdiagPart
  simp only [one_div, transpose_apply]
  by_cases h1 : i = j
  · rw [h1]
  · split_ifs
    · (expose_names; exact False.elim (h1 (id (Eq.symm h))))
    · rfl

-- D^-1/2.det ≠ 0
lemma Bsqrt_det_nonzero
  (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A) (b : Fin n → ℝ) (x0 : Fin n → ℝ) : (negsqrtdiagPart A).det ≠ 0 := by
  sorry

-- Redefine the Jacobi structure: we assume diagonal entries > 0, so `myJacobi` can take this parameter.
noncomputable def myJacobi
  (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i > 0) (b : Fin n → ℝ) (x0 : Fin n → ℝ) :=
  Jacobi A (diagpos_to_nonzero A hdiag) b x0

-- Complexify a real matrix.
def complexify
  (B : Matrix (Fin n) (Fin n) ℝ) :
  Matrix (Fin n) (Fin n) ℂ :=
  Matrix.map B (↑)  -- Embed each real entry into ℂ via coercion.

-- Define that all eigenvalues are real.
def has_all_real_eigenvalues
  (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ t ∈ spectrum ℂ (complexify B), t.im = 0

-- Define similar matrices.
def Matrix.Similar (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :=
  ∃ (P : Matrix (Fin n) (Fin n) ℝ), (IsUnit P.det) ∧ (B = P⁻¹ * A * P)

-- Equivalent definition of matrix eigenvalues.
lemma Matrix.eignevalue
  (B : Matrix (Fin n) (Fin n) ℝ) :
  t ∈ spectrum ℂ (complexify B) ↔ ∃ x : Fin n → ℂ , (complexify B) *ᵥ x = t • x := by
  sorry

end JacobiFolder
