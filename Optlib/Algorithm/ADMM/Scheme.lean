import Optlib.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib

noncomputable section

open Set InnerProductSpace Topology Filter

variable (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]

-- The basic form of the problem solved by admm
class OptProblem [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ F] where
   f₁ : E₁ → ℝ
   f₂ : E₂ → ℝ
   A₁ : E₁ →L[ℝ] F
   A₂ : E₂ →L[ℝ] F
   b  : F
   lscf₁ : LowerSemicontinuous f₁
   lscf₂ : LowerSemicontinuous f₂
   cf₁ : ConvexOn ℝ univ f₁
   cf₂ : ConvexOn ℝ univ f₂
   nonempty : ∃ x₁ x₂ ,(A₁ x₁) + (A₂ x₂) - b = 0 ∧ IsMinOn (fun (x₁,x₂) ↦ f₁ x₁ + f₂ x₂) univ (x₁,x₂)

-- The subproblem of admm has a unique solution
def Admm_sub_Isunique {E : Type*}(f : E → ℝ)(x : E)(_h : IsMinOn f univ x): Prop :=
   ∃ y , IsMinOn f univ y → x = y

-- Augmented Lagrangian Function
def Augmented_Lagrangian_Function (opt : OptProblem E₁ E₂ F) (ρ : ℝ) : E₁ × E₂ × F → ℝ :=
   fun (x₁ , x₂ , y) => (opt.f₁ x₁) + (opt.f₂ x₂) +
      @inner ℝ F _ y ((opt.A₁ x₁) + (opt.A₂ x₂) - opt.b) + ρ / 2 * ‖(opt.A₁ x₁) + (opt.A₂ x₂) - opt.b‖ ^ 2

-- The basic iteration format of ADMM
class ADMM extends (OptProblem E₁ E₂ F) where
   x₁ : ℕ → E₁
   x₂ : ℕ → E₂
   y  : ℕ → F
   ρ  : ℝ
   τ  : ℝ
   hrho : ρ > 0
   htau  : 0 < τ ∧ τ < ( 1 + √ 5 ) / 2
   itex₁ : ∀ k, IsMinOn (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem ρ) (x₁ , x₂ k , y k)) univ (x₁ ( k + 1 ))
   uitex₁ : ∀ k , Admm_sub_Isunique (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem ρ) (x₁ , x₂ k , y k)) (x₁ ( k + 1 )) (itex₁ k)
   itex₂ : ∀ k, IsMinOn (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem ρ) (x₁ (k+1) , x₂ , y k)) univ (x₂ ( k + 1 ))
   uitex₂ : ∀ k , Admm_sub_Isunique (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem ρ) (x₁ (k+1) , x₂ , y k)) (x₂ ( k + 1 )) (itex₂ k)
   itey : ∀ k, y (k + 1) = y k + (τ * ρ) • ((A₁ $ x₁ (k + 1)) + (A₂ $ x₂ (k + 1)) - b)

-- Convex KKT condition
variable {E₁ E₂ F} in
class Convex_KKT (x₁ : E₁ )(x₂ : E₂)(y : F) (opt : OptProblem E₁ E₂ F) :Prop where
   subgrad₁ : -(ContinuousLinearMap.adjoint opt.A₁) y ∈ SubderivAt opt.f₁ x₁
   subgrad₂ : -(ContinuousLinearMap.adjoint opt.A₂) y ∈ SubderivAt opt.f₂ x₂
   eq       :  (opt.A₁ x₁) + (opt.A₂ x₂) = opt.b
