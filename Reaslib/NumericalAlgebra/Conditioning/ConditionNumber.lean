import Mathlib.Analysis.CStarAlgebra.Matrix
import Reaslib.NumericalAlgebra.Defs
import Mathlib.Logic.Nontrivial.Basic
import Reaslib.NumericalAlgebra.Direct.SVD

namespace Matrix

open scoped Matrix BigOperators

section ConditionNumber

variable {α : Type*} [RCLike α]
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ### Condition numbers -/

/-- Condition number of an invertible matrix using 2-norm. -/
noncomputable def conditionNumber₂ (A : Matrix n n α) [Invertible A] : ℝ :=
  ‖A‖₂ * ‖A⁻¹‖₂

/-- Condition number using 1-norm. -/
noncomputable def conditionNumber₁ (A : Matrix n n α) [Invertible A] : ℝ :=
  ‖A‖₁ * ‖A⁻¹‖₁

/-- Condition number using ∞-norm. -/
noncomputable def conditionNumberInf (A : Matrix n n α) [Invertible A] : ℝ :=
  ‖A‖_∞ * ‖A⁻¹‖_∞

/-- Equivalent characterizations of condition number.

    The (2-)condition number `κ₂(A)` is defined as `‖A‖₂ * ‖A⁻¹‖₂` for invertible `A`.
    Prove equivalent formulations such as:
      * `κ₂(A) = σ_max(A) / σ_min(A)` (ratio of largest and smallest singular values),
      * `κ₂(A) ≥ 1`,
      * bounds relating relative forward/backward error with `κ₂(A)`.
-/
theorem cond_eq_ratio_singular_values {n : ℕ} [InnerProductSpace α (Fin n → α)]
  (A : Matrix (Fin n) (Fin n) α) (hA : Invertible A) :
  conditionNumber₂ A = (A.largestSingularValue) / (A.smallestSingularValue) :=
sorry

theorem conditionNumber_ge_one (A : Matrix n n α) (hA : Invertible A) :
    1 ≤ conditionNumber₂ A := by
  sorry

end ConditionNumber
end Matrix
