import Mathlib.Topology.MetricSpace.Sequences
import Optlib.Algorithm.ADMM.Scheme
import Optlib.Algorithm.ADMM.Inv_bounded
import Optlib.Convex.FiniteDimensionalConvexFunctionsLocallyLipschitz
import Optlib.Convex.Subgradient

noncomputable section

open Set InnerProductSpace Topology Filter InnerProduct

open scoped Pointwise

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F ]

variable (admm : ADMM E₁ E₂ F)

structure Existance_of_kkt where
   x₁ : E₁
   x₂ : E₂
   y : F
   h : Convex_KKT x₁ x₂ y admm.toOptProblem

variable (admm_kkt : Existance_of_kkt admm)

namespace ADMM_Converge_Proof

variable {admm admm_kkt}

class Setting (E₁ E₂ F : outParam Type*)
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F ]
    (admm : outParam (ADMM E₁ E₂ F))
    (admm_kkt : outParam (Existance_of_kkt admm)) where

-- variable [Setting E₁ E₂ F admm admm_kkt]

local notation "f₁" => admm.f₁
local notation "f₂" => admm.f₂
local notation "A₁" => admm.A₁
local notation "A₂" => admm.A₂
local notation "b" => admm.b
local notation "x₁" => admm.x₁
local notation "x₂" => admm.x₂
local notation "y" => admm.y
local notation "τ" => admm.τ
local notation "ρ" => admm.ρ

local notation "x₁'" => admm_kkt.x₁
local notation "x₂'" => admm_kkt.x₂
local notation "y'" => admm_kkt.y

local notation "A₁†" => ContinuousLinearMap.adjoint A₁
local notation "A₂†" => ContinuousLinearMap.adjoint A₂
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

lemma Satisfaction_ofthekkt : Convex_KKT x₁' x₂' y' admm.toOptProblem := admm_kkt.h

--误差变量

def e₁ [Setting E₁ E₂ F admm admm_kkt] : ℕ → E₁ := fun n => (x₁ n) - x₁'

def e₂ [Setting E₁ E₂ F admm admm_kkt] : ℕ → E₂ := fun n => (x₂ n) - x₂'

def ey [Setting E₁ E₂ F admm admm_kkt] : ℕ → F :=  fun n => (y  n) - y'

--辅助变量
--这里定义域需要是非0自然数
def u [Setting E₁ E₂ F admm admm_kkt]: ℕ+ → E₁ :=
fun n => - A₁† (y n + (( 1 - τ) * ρ ) • (A₁ (e₁ n) + A₂ (e₂ n)) + ρ • (A₂ (x₂ (n - 1) - x₂ n)))

def v [Setting E₁ E₂ F admm admm_kkt]: ℕ → E₂ :=
fun n => - A₂† (y n + (( 1 - τ) * ρ ) • (A₁ (e₁ n) + A₂ (e₂ n)))

def Ψ [Setting E₁ E₂ F admm admm_kkt]: ℕ → ℝ  := fun n => 1 / ( τ * ρ ) * ‖ey n‖^2 + ρ * ‖A₂ (e₂ n)‖ ^ 2

def Φ [Setting E₁ E₂ F admm admm_kkt]: ℕ → ℝ  := fun n => (Ψ n) + ((max (1 - τ) (1 - 1 / τ)) * ρ ) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^2

def υ [Setting E₁ E₂ F admm admm_kkt] : ℕ → F  :=
   fun n => (y n) + ((1 - τ) * ρ) • (A₁ (x₁ n) + A₂ (x₂ n) - b)

def M [Setting E₁ E₂ F admm admm_kkt] : ℕ+ → ℝ  :=
   fun n => ((1 - τ) * ρ) * (inner (A₂ ((x₂ n) - (x₂ n.natPred))) (A₁ (x₁ n.natPred) + A₂ (x₂ n.natPred) - b))

lemma f₁_continuous [Setting E₁ E₂ F admm admm_kkt]: ContinuousOn f₁ univ :=
   FiniteDimensionalConvexFunctionsContinous convex_univ isOpen_univ OptProblem.cf₁

lemma f₂_continuous [Setting E₁ E₂ F admm admm_kkt]: ContinuousOn f₂ univ :=
   FiniteDimensionalConvexFunctionsContinous convex_univ isOpen_univ OptProblem.cf₂

lemma inner_convex1 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ConvexOn ℝ univ (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) := by
   dsimp [ConvexOn]
   intro n
   constructor
   · apply convex_univ
   intro xx _ yy _ aa bb _ _ abh
   have :=
      calc
         (A₁ (aa • xx + bb • yy)) + (A₂ (x₂ n.natPred)) - b
         = aa • A₁ (xx) + bb • A₁ (yy) + (A₂ (x₂ n.natPred)) - b := by continuity
         _= aa • A₁ (xx) + bb • A₁ (yy) + (aa + bb) • (A₂ (x₂ n.natPred) - b) := by
            rw [abh]
            rw [one_smul]
            rw [add_sub]
         _= aa • A₁ (xx) + bb • A₁ (yy) + aa • (A₂ (x₂ n.natPred) - b) + bb • (A₂ (x₂ n.natPred) - b) := by
            rw [add_smul]
            rw [add_assoc (aa • A₁ (xx) + bb • A₁ (yy))]
         _= aa • (A₁ (xx) + (A₂ (x₂ n.natPred) - b)) + bb • (A₁ (yy) + (A₂ (x₂ n.natPred) - b)) := by
            repeat rw [smul_add]
            rw [← add_assoc, add_assoc (aa • A₁ (xx)), add_comm (bb • A₁ (yy)), ← add_assoc]
   calc
      _= ⟪y n.natPred , aa • (A₁ (xx) + (A₂ (x₂ n.natPred) - b))
          + bb • (A₁ (yy) + (A₂ (x₂ n.natPred) - b))⟫ := by rw [this]
      _= ⟪y n.natPred , aa • (A₁ (xx) + (A₂ (x₂ n.natPred) - b))⟫
          + ⟪y n.natPred , bb • (A₁ (yy) + (A₂ (x₂ n.natPred) - b))⟫ := by rw [inner_add_right]
      _= aa * ⟪y n.natPred , (A₁ (xx) + (A₂ (x₂ n.natPred) - b))⟫
          + bb * ⟪y n.natPred , (A₁ (yy) + (A₂ (x₂ n.natPred) - b))⟫ := by
         rw [inner_smul_right]; rw [inner_smul_right]
      _= aa * ⟪y n.natPred , A₁ (xx) + A₂ (x₂ n.natPred) - b⟫ + bb * ⟪y n.natPred , A₁ (yy) + A₂ (x₂ n.natPred) - b⟫ := by
         rw [add_sub, add_sub]
   rfl

#check LinearMapClass
lemma inner_convex2 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ConvexOn ℝ univ (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) := by
   intro n
   let c := y n.natPred
   let a := (A₁ (x₁ n)) - b
   have : (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) =
         (fun x => ⟪y n.natPred , (A₂ x) + ((A₁ (x₁ n)) - b)⟫) := by
      ext x;rw[add_comm,← add_sub]
   rw[this]
   show ConvexOn ℝ univ (fun x => ⟪c , (A₂ x) + a⟫)
   have h : (fun x => ⟪c , (A₂ x) + a⟫) = (fun x => ⟪c , (A₂ x)⟫ + ⟪c , a⟫):= by
      ext x
      rw[← inner_add_right]
   let p := ⟪c , a⟫
   rw[h]
   show ConvexOn ℝ univ (fun x => ⟪c , (A₂ x)⟫ + p)
   apply ConvexOn.add _
   apply convexOn_const
   apply convex_univ
   let f : E₂ →ₗ[ℝ] ℝ :={
      toFun := (fun x => ⟪c , A₂ x⟫)
      map_add' := by
         intro u v
         simp only [map_add]
         rw[inner_add_right]
      map_smul' := by
         intro u v
         simp only [LinearMapClass.map_smul, RingHom.id_apply, smul_eq_mul]
         apply inner_smul_right
   }
   show ConvexOn ℝ univ f
   apply LinearMap.convexOn
   apply convex_univ

-- ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2
lemma norm_covex1 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ConvexOn ℝ univ (fun x => ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) := by
   intro n
   let c := - ((A₂ (x₂ n.natPred)) - b)
   have h : (fun x => ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) =
         (fun x => ρ  * ‖(A₁ x) - c‖ ^ 2 / 2) := by
      ext x
      simp only [c]
      rw[sub_neg_eq_add, add_sub]
      ring
   rw[h]
   let f := (fun x => ‖(A₁ x) - c‖ ^ 2 / 2)
   show ConvexOn ℝ univ (fun x => ρ • ‖(A₁ x) - c‖ ^ 2 / 2)
   have h1 : (fun x => ρ • ‖(A₁ x) - c‖ ^ 2 / 2) =
         (fun x => ρ • f x) := by
      ext x
      simp only [f,smul_eq_mul]
      ring_nf
   rw[h1]
   apply ConvexOn.smul (le_of_lt admm.hrho)
   let u := fun x => ‖x - c‖ ^ 2 / 2
   let g := A₁
   have h2 : u ∘ g = f := by
      ext x
      simp only [Function.comp_apply]
   rw[← h2]
   have h3 : ⇑g ⁻¹' univ = univ := by
      simp only [preimage_univ]
   rw[← h3]
   have h4 : Convex ℝ (univ (α := F)) := by
      apply convex_univ
   apply ConvexOn.comp_linearMap (convex_of_norm_sq c h4)

lemma norm_covex2 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ConvexOn ℝ univ (fun x => ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) := by
   intro n
   let c := - ((A₁ (x₁ n)) - b)
   have h : (fun x => ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) =
         (fun x => ρ  * ‖(A₂ x) - c‖ ^ 2 / 2) := by
      ext x
      rw[add_comm]
      simp only [c]
      rw[sub_neg_eq_add, add_sub]
      ring
   rw[h]
   let f := (fun x => ‖(A₂ x) - c‖ ^ 2 / 2)
   show ConvexOn ℝ univ (fun x => ρ • ‖(A₂ x) - c‖ ^ 2 / 2)
   have h1 : (fun x => ρ • ‖(A₂ x) - c‖ ^ 2 / 2) =
         (fun x => ρ • f x) := by
      ext x
      simp only [f,smul_eq_mul]
      ring_nf
   rw[h1]
   apply ConvexOn.smul (le_of_lt admm.hrho)
   let u := fun x => ‖x - c‖ ^ 2 / 2
   let g := A₂
   have h2 : u ∘ g = f := by
      ext x
      simp only [Function.comp_apply]
   rw[← h2]
   have h3 : ⇑g ⁻¹' univ = univ := by
      simp only [preimage_univ]
   rw[← h3]
   have h4 : Convex ℝ (univ (α := F)) := by
      apply convex_univ
   apply ConvexOn.comp_linearMap (convex_of_norm_sq c h4)

#check SubderivAt_eq_gradient
lemma ADMM_iter_process₁'_eq3_1' [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+ ,
      HasGradientAt (fun _ => f₂ (x₂ n.natPred)) 0 (x₁ n) := by
   intro n
   apply hasGradientAt_const

lemma ADMM_iter_process₁'_eq3_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun _ => f₂ (x₂ n.natPred)) (x₁ n) = 0 := by
   intro n
   apply SubderivAt_eq_gradient (convexOn_const (f₂ (x₂ n.natPred)) (convex_univ))
   apply ADMM_iter_process₁'_eq3_1'

-- gradient of f (x) = ⟪c , A x⟫
lemma inner_gradient { α β : Type*}
      [NormedAddCommGroup α]  [NormedAddCommGroup β]
      [InnerProductSpace ℝ α] [InnerProductSpace ℝ β]
      [CompleteSpace α]  [CompleteSpace β] (A : α →L[ℝ] β)(c : β) :∀ x,
      HasGradientAt ((fun x => ⟪c , A x⟫)) ((A†) c) x := by
   intro x
   rw[HasGradient_iff_Convergence_Point]
   intro ε εpos
   use ε,εpos
   intro x1 _
   rw[← inner_sub_right,ContinuousLinearMap.adjoint_inner_left,← inner_sub_right]
   simp only [map_sub, sub_self, inner_zero_right, norm_zero]
   have := norm_nonneg (x - x1)
   rwa[mul_nonneg_iff_right_nonneg_of_pos εpos]

#check HasGradient_iff_Convergence_Point
lemma ADMM_iter_process₁'_eq3_2'_1 [Setting E₁ E₂ F admm admm_kkt](c : F) :∀ x,
      HasGradientAt ((fun x => ⟪c , (A₁ x)⟫)) (A₁† c) x := by
   apply inner_gradient

#check HasDerivAt.hasGradientAt'
lemma ADMM_iter_process₁'_eq3_2' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , ∀ x ,
      HasGradientAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (A₁† (y n.natPred)) x := by
   intro n x
   let c := y n.natPred
   let c₁ := ⟪y n.natPred ,(A₂ (x₂ n.natPred)) - b⟫
   have :(fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫)
   = (fun x => ⟪y n.natPred , (A₁ x)⟫) + (fun _ => ⟪y n.natPred ,(A₂ (x₂ n.natPred)) - b⟫) := by
      ext x
      simp only [Pi.add_apply]
      rw[← add_sub (A₁ x) (A₂ (x₂ n.natPred)) b]
      exact inner_add_right (ADMM.y E₁ E₂ n.natPred) ((OptProblem.A₁ E₂) x)
            ((OptProblem.A₂ E₁) (ADMM.x₂ E₁ F n.natPred) - OptProblem.b E₁ E₂)
   rw[this]
   show HasGradientAt ((fun x => ⟪c , (A₁ x)⟫ + c₁)) (A₁† c) x
   rw[hasGradientAt_iff_hasFDerivAt]
   apply HasFDerivAt.add_const _ c₁
   show HasGradientAt ((fun x => ⟪c , (A₁ x)⟫)) (A₁† c) x
   apply ADMM_iter_process₁'_eq3_2'_1

lemma inner_continuous1 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ContinuousOn (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) univ:= by
   intro n
   have :∀ x ∈ univ,HasGradientAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (A₁† (y n.natPred)) x := by
      intro x _
      apply ADMM_iter_process₁'_eq3_2' n
   apply HasGradientAt.continuousOn
   exact this

lemma ADMM_iter_process₁'_eq3_2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (x₁ n) = { A₁† (y n.natPred)} := by
   intro n
   apply SubderivAt_eq_gradient (inner_convex1 n)
   apply ADMM_iter_process₁'_eq3_2'

lemma norm_comm {α β: Type*}
      [NormedAddCommGroup α] [InnerProductSpace ℝ α]
      [NormedAddCommGroup β] [InnerProductSpace ℝ β]
      (A : α →L[ℝ] β) (a₁ a₂ : α): ‖A (a₁ - a₂)‖ =‖A (a₂ - a₁)‖ := by
   rw [map_sub, map_sub , ←neg_sub (A a₂) (A a₁)]; apply norm_neg

#check norm_eq_zero

/-Derivatives of quadratic forms-/
lemma Gradient_of_quadratic_forms { α β : Type*}
      [NormedAddCommGroup α]  [NormedAddCommGroup β]
      [InnerProductSpace ℝ α] [InnerProductSpace ℝ β]
      [CompleteSpace α]  [CompleteSpace β] (A : α →L[ℝ] β):
      ∀ s , HasGradientAt ((fun x => ⟪ A x , A x⟫)) ((2 : ℝ ) • (A†) (A s)) s:= by
   intro s
   rw[HasGradient_iff_Convergence_Point]
   intro ε εpos
   rcases (le_iff_eq_or_lt.1 $ norm_nonneg A) with h | h
   ·  use ε,εpos
      intro x hx
      symm at h
      rw[norm_eq_zero] at h
      simp[h]
      have := norm_nonneg (s - x)
      rwa[mul_nonneg_iff_right_nonneg_of_pos εpos]
   ·  use ε / ‖A‖ ^ 2
      field_simp
      intro x hx
      have hzero : 0 < ‖A‖ ^ 2 := by apply sq_pos_of_pos h
      let t := x - s
      have t1 : s + t = x := by
         show s + (x - s) = x
         simp only [add_sub_cancel]
      have : ⟪A x, A x⟫ - ⟪A s, A s⟫ - ⟪(2 : ℝ) • (A†) (A s), x - s⟫ =
            ⟪A (x - s) , A (x - s)⟫ := by
         rw[← t1]
         simp only [map_add, add_sub_cancel_left]
         show ⟪A s + A t , A s + A t⟫ - ⟪A s, A s⟫ - ⟪(2 : ℝ) • (A†) (A s), t⟫ =
            ⟪A t , A t⟫
         rw[real_inner_add_add_self]
         rw[real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
         ring
      rw[this,real_inner_self_eq_norm_sq]
      simp only [abs_pow, abs_norm, ge_iff_le]
      calc
         _ = ‖A (s - x)‖ ^ 2 := by
            rw[norm_comm]
         _ ≤ (‖A‖ * ‖s - x‖) ^ 2:= by
            rw[sq,sq,← mul_self_le_mul_self_iff]
            apply ContinuousLinearMap.le_opNorm
            apply norm_nonneg
            simp[h , norm_nonneg (s - x)]
         _ = ‖A‖ ^ 2 * ‖s - x‖ ^ 2 := by
            linarith
      rcases (le_iff_eq_or_lt.1 $ norm_nonneg (s - x)) with h1 | _
      ·  rw[← h1]
         simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, le_refl]
      ·  calc
            _ = ‖A‖ ^ 2 * ‖s - x‖ * ‖s - x‖:= by
               nth_rw 2 [sq];
               rw[mul_assoc]
            _ ≤ ‖A‖ ^ 2 * ‖s - x‖ * (ε / ‖A‖ ^ 2) :=by
               have :0 ≤ ‖A‖ ^ 2 * ‖s - x‖ := by
                  simp[hzero,norm_nonneg (s - x)]
               apply mul_le_mul_of_nonneg_left hx this
            _ = _ := by
               field_simp[hzero]
               ring_nf

#check add_sub
lemma ADMM_iter_process₁'_eq3_3' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      HasGradientAt (fun x => ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2)
      (ρ • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))) (x₁ n) := by
   intro n
   let c := (A₂ (x₂ n.natPred)) - b
   have h1: (fun x => ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) =
         (fun x => ρ / 2 * ‖(A₁ x) + ((A₂ (x₂ n.natPred)) - b)‖ ^ 2) := by
      ext x
      rw[← add_sub]
   rw[← add_sub (A₁ (x₁ n))  (A₂ (x₂ n.natPred))  b ,h1]
   show HasGradientAt (fun x => ρ / 2 * ‖(A₁ x) + c‖ ^ 2) (ρ • (A₁† (A₁ (x₁ n) + c))) (x₁ n)
   have h2 : (fun x => ρ / 2 * ‖(A₁ x) + c‖ ^ 2) =
         (fun x => ρ / 2 * (⟪(A₁ x) , (A₁ x)⟫ + 2 * ⟪c , A₁ x⟫ + ⟪c , c⟫)):= by
      ext x
      rw[← real_inner_self_eq_norm_sq ((A₁ x) + c)]
      rw[ real_inner_add_add_self]
      rw[real_inner_comm c (A₁ x)]
   rw[h2]
   have h3 : ρ • (A₁† (A₁ (x₁ n) + c)) = (ρ / 2) • ((2 : ℝ ) • A₁† (A₁ (x₁ n) + c)) := by
      rw [smul_smul]; simp only [map_add, smul_add, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
         not_false_eq_true, IsUnit.div_mul_cancel]
   rw[h3]
   apply HasGradientAt.const_mul' (ρ / 2)
   apply HasGradientAt.add_const
   have h4 : (2 : ℝ ) • A₁† (A₁ (x₁ n) + c) = (2 : ℝ ) • A₁† (A₁ (x₁ n)) + (2 : ℝ ) • A₁† c := by
      calc
         _ = (2 : ℝ ) • (A₁† (A₁ (x₁ n))  + A₁† c) := by
            simp only [map_add, smul_add]
         _ = _ := by
            simp only [smul_add]
   rw[h4]
   apply HasGradientAt.add
   ·  apply Gradient_of_quadratic_forms
   ·  let a := (fun x => ⟪c, A₁ x⟫)
      show HasGradientAt (fun x ↦ 2 * a x) ((2 : ℝ)• (A₁† c)) (x₁ n)
      apply HasGradientAt.const_mul' 2
      apply inner_gradient

-- ⟪a+b,a+b⟫=⟪a,a⟫+2*⟪a,b⟫+⟪b,b⟫

lemma ADMM_iter_process₁'_eq3_3 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x => ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) (x₁ n) = {ρ • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))} := by
   intro n
   apply SubderivAt_eq_gradient (norm_covex1 n)
   apply ADMM_iter_process₁'_eq3_3'

lemma ADMM_iter_process₁'_eq2_1' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      (fun x => (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem ρ) (x , x₂ n.natPred , y n.natPred)) =
      (fun x => (f₁ x) + (f₂ (x₂ n.natPred))+ ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫ + ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) := by
   intro n
   rfl

-- (fun x => f x) + (fun x => g x) = (fun x => f x + g x)
lemma ADMM_iter_process₁'_eq2_1'_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      (fun x => (f₁ x) + (f₂ (x₂ n.natPred))+ ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫ + ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2)
      = f₁ + (fun _ => f₂ (x₂ n.natPred)) + (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) + (fun x => ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2)
      := by
   intro n
   congr

#check SubderivAt.add
#check continuousOn_const
#check convexOn_const
#check convex_univ
#check ConvexOn.add
#check ContinuousOn.add
--(@continuousOn_const E₁ ℝ _ _ univ (f₂ (x₂ n.natPred)) )

lemma ADMM_iter_process₁'_eq2_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem ρ) (x , x₂ n.natPred , y n.natPred)) (x₁ n) =
      SubderivAt f₁ (x₁ n) + SubderivAt (fun _ => f₂ (x₂ n.natPred)) (x₁ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (x₁ n) +
      SubderivAt (fun x => ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) (x₁ n) := by
   intro n
   rw[ADMM_iter_process₁'_eq2_1' n , ADMM_iter_process₁'_eq2_1'_1 n]
   rw[SubderivAt.add admm.cf₁ (convexOn_const (f₂ (x₂ n.natPred)) (convex_univ))
   f₁_continuous (x₁ n)]
   rw[SubderivAt.add (ConvexOn.add admm.cf₁ (convexOn_const (f₂ (x₂ n.natPred)) (convex_univ)))
   (inner_convex1 n) (ContinuousOn.add f₁_continuous (@continuousOn_const E₁ ℝ _ _ univ (f₂ (x₂ n.natPred)))) (x₁ n)]
   rw[SubderivAt.add (ConvexOn.add (ConvexOn.add admm.cf₁ (convexOn_const (f₂ (x₂ n.natPred)) (convex_univ))) (inner_convex1 n))
   (norm_covex1 n) (ContinuousOn.add (ContinuousOn.add f₁_continuous (@continuousOn_const E₁ ℝ _ _ univ (f₂ (x₂ n.natPred)))) (inner_continuous1 n)) (x₁ n)]

lemma ADMM_iter_process₁'_eq2_2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt f₁ (x₁ n) + SubderivAt (fun _ => f₂ (x₂ n.natPred)) (x₁ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (x₁ n) +
      SubderivAt (fun x => ρ / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) (x₁ n) =
      SubderivAt f₁ (x₁ n) + 0 + { A₁† (y n.natPred)} + {ρ • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}:= by
   intro n
   rw[ADMM_iter_process₁'_eq3_1 n,ADMM_iter_process₁'_eq3_2 n,ADMM_iter_process₁'_eq3_3 n]

lemma ADMM_iter_process₁'_eq2_3 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt f₁ (x₁ n) + 0 + { A₁† (y n.natPred)} + {ρ • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}
      = SubderivAt f₁ (x₁ n) + { A₁† (y n.natPred)} + {ρ • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}:= by
   intro n
   rw[add_zero]

lemma ADMM_iter_process₁'_eq1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt f₁ (x₁ n) + { A₁† (y n.natPred)} + {ρ • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}
      = SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem ρ) (x , x₂ n.natPred , y n.natPred)) (x₁ n):=by
   intro n
   rw[← ADMM_iter_process₁'_eq2_3 n,← ADMM_iter_process₁'_eq2_2 n,← ADMM_iter_process₁'_eq2_1 n]


#check first_order_convex_iff_subgradient
lemma ADMM_iter_process₁' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,0 ∈
      SubderivAt f₁ (x₁ n) + { A₁† (y n.natPred)} + {ρ • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}:= by
   intro n
   have := first_order_convex_iff_subgradient (f := (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem ρ) (x , x₂ n.natPred , y n.natPred)) ) (x₁ n)
   have h := admm.itex₁ n.natPred
   have eq : n.natPred + 1 = n := by apply PNat.natPred_add_one
   rw[eq , this , ← ADMM_iter_process₁'_eq1 n] at h
   exact h

-- 0 ∈ s +{a} => -a ∈ s
lemma set_add_assoc {E : Type*}[NormedAddCommGroup E]
(p q r : Set E): p + q + r = p + (q + r) := by
   rw[superset_antisymm_iff]
   constructor
   ·  intro x hx
      rw[Set.mem_add] at hx
      rcases hx with ⟨px,hpx,⟨py,hpy,h1⟩⟩
      rw[Set.mem_add] at hpy
      rcases hpy with ⟨qy,hqy,⟨rz,hrz,h2⟩⟩
      rw[Set.mem_add]
      use px + qy , Set.add_mem_add hpx hqy
      use rz,hrz
      rw[← h1,← h2]
      exact add_assoc px qy rz
   ·  intro x hx
      rw[Set.mem_add] at hx
      rcases hx with ⟨px,hpx,⟨py,hpy,h1⟩⟩
      rw[Set.mem_add] at hpx
      rcases hpx with ⟨qy,hqy,⟨rz,hrz,h2⟩⟩
      rw[Set.mem_add]
      use qy,hqy
      use rz + py , Set.add_mem_add hrz hpy
      rw[← h1,← h2]
      exact Eq.symm (add_assoc qy rz py)

lemma zero_in_add {E : Type*}[NormedAddCommGroup E]{a : E}{s : Set E}
   (h : 0 ∈ s + {a}) : -a ∈ s:= by
   simp only [add_singleton, image_add_right, mem_preimage, zero_add] at h
   exact h;

lemma change_item {α : Type*}[NormedAddCommGroup α]{S : Set α}{p q : α}(h : 0 ∈ S + {p} + {q}):
      - p - q ∈ S := by
   rw[set_add_assoc S {p} {q},Set.singleton_add_singleton] at h
   apply zero_in_add at h
   rwa[← neg_add' p q]


lemma ADMM_iter_process₁ [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      ( - A₁† (y (n - 1)) - ρ • (A₁† (A₁ (x₁ n) + A₂ (x₂ (n - 1)) - b))) ∈ SubderivAt f₁ (x₁ n) := by
   intro n
   let S := SubderivAt f₁ (x₁ n)
   let p := A₁† (y (n - 1))
   let q := ρ • (A₁† (A₁ (x₁ n) + A₂ (x₂ (n - 1)) - b))
   show - p - q ∈ S
   have := ADMM_iter_process₁' n
   change 0 ∈ S + {p} + {q} at this
   apply change_item this

lemma ADMM_iter_process₂'_eq3_1' [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+ ,
      HasGradientAt (fun _ => f₁ (x₁ n)) 0 (x₂ n) := by
   intro n
   apply hasGradientAt_const

lemma ADMM_iter_process₂'_eq3_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun _ => f₁ (x₁ n)) (x₂ n) = 0 := by
   intro n
   apply SubderivAt_eq_gradient (convexOn_const (f₁ (x₁ n)) (convex_univ))
   apply ADMM_iter_process₂'_eq3_1'

#check ADMM_iter_process₁'_eq3_2'
lemma ADMM_iter_process₂'_eq3_2' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , ∀ x ,
      HasGradientAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (A₂† (y n.natPred)) x := by
   intro n x
   let c := y n.natPred
   let c₁ := ⟪c ,(A₁ (x₁ n)) - b⟫
   have :(fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫)
   = (fun x => ⟪y n.natPred , (A₂ x)⟫) + (fun _ => ⟪y n.natPred ,(A₁ (x₁ n)) - b⟫) := by
      ext x
      simp only [Pi.add_apply]
      rw[add_comm]
      rw[← add_sub (A₂ x) (A₁ (x₁ n))  b]
      exact inner_add_right (y n.natPred) (A₂ x) (A₁ (x₁ n) - b)
   rw[this]
   show HasGradientAt (fun x => ⟪c , (A₂ x)⟫ + c₁) (A₂† c) x
   rw[hasGradientAt_iff_hasFDerivAt]
   apply HasFDerivAt.add_const _ c₁
   show HasGradientAt ((fun x => ⟪c , (A₂ x)⟫)) (A₂† c) x
   apply inner_gradient

lemma inner_continuous2 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ContinuousOn (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) univ:= by
   intro n
   have :∀ x ∈ univ,HasGradientAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (A₂† (y n.natPred)) x := by
      intro x _
      apply ADMM_iter_process₂'_eq3_2' n
   apply HasGradientAt.continuousOn
   exact this

lemma ADMM_iter_process₂'_eq3_2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (x₂ n) = { A₂† (y n.natPred)} := by
   intro n
   apply SubderivAt_eq_gradient (inner_convex2 n)
   apply ADMM_iter_process₂'_eq3_2'

#check ADMM_iter_process₁'_eq3_3'
lemma ADMM_iter_process₂'_eq3_3' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      HasGradientAt (fun x => ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2)
      (ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))) (x₂ n) := by
   intro n
   let c := (A₁ (x₁ n)) - b
   have h1: (fun x => ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) =
         (fun x => ρ / 2 * ‖(A₂ x) + ((A₁ (x₁ n)) - b)‖ ^ 2) := by
      ext x
      rw[add_comm,← add_sub]
   rw[h1]
   have h1' : (ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))) =
         (ρ • (A₂† (A₂ (x₂ n) + (A₁ (x₁ n) - b)))):= by
      rw[add_comm,← add_sub]
   rw[h1']
   show HasGradientAt (fun x => ρ / 2 * ‖(A₂ x) + c‖ ^ 2) (ρ • (A₂† (A₂ (x₂ n) + c))) (x₂ n)
   have h2 : (fun x => ρ / 2 * ‖(A₂ x) + c‖ ^ 2) =
         (fun x => ρ / 2 * (⟪(A₂ x) , (A₂ x)⟫ + 2 * ⟪c , A₂ x⟫ + ⟪c , c⟫)):= by
      ext x
      rw[← real_inner_self_eq_norm_sq ((A₂ x) + c)]
      rw[ real_inner_add_add_self]
      rw[real_inner_comm c (A₂ x)]
   rw[h2]
   have h3 : ρ • (A₂† (A₂ (x₂ n) + c)) = (ρ / 2) • ((2 : ℝ ) • A₂† (A₂ (x₂ n) + c)) := by
      rw [smul_smul]; simp only [map_add, smul_add, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
         not_false_eq_true, IsUnit.div_mul_cancel]
   rw[h3]
   apply HasGradientAt.const_mul' (ρ / 2)
   apply HasGradientAt.add_const
   have h4 : (2 : ℝ ) • A₂† (A₂ (x₂ n) + c) = (2 : ℝ ) • A₂† (A₂ (x₂ n)) + (2 : ℝ ) • A₂† c := by
      calc
         _ = (2 : ℝ ) • (A₂† (A₂ (x₂ n))  + A₂† c) := by
            simp only [map_add, smul_add]
         _ = _ := by
            simp only [smul_add]
   rw[h4]
   apply HasGradientAt.add
   ·  apply Gradient_of_quadratic_forms
   ·  let a := (fun x => ⟪c, A₂ x⟫)
      show HasGradientAt (fun x ↦ 2 * a x) ((2 : ℝ)• (A₂† c)) (x₂ n)
      apply HasGradientAt.const_mul' 2
      apply inner_gradient

lemma ADMM_iter_process₂'_eq3_3 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x => ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) (x₂ n) = {ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))} := by
   intro n
   apply SubderivAt_eq_gradient (norm_covex2 n)
   apply ADMM_iter_process₂'_eq3_3'

lemma ADMM_iter_process₂'_eq2_1' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem ρ) (x₁ n , x , y n.natPred))=
      (fun x => f₁ (x₁ n) + (f₂ x)+ ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫ + ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) := by
   intro n
   rfl

lemma ADMM_iter_process₂'_eq2_1'_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      (fun x => f₁ (x₁ n) + (f₂ x)+ ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫ + ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2)
      = (fun _ => f₁ (x₁ n)) + f₂ + (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) + (fun x => ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2):= by
   intro n
   congr

lemma ADMM_iter_process₂'_eq2_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem ρ) (x₁ n , x , y n.natPred)) (x₂ n) =
      SubderivAt (fun _ => f₁ (x₁ n)) (x₂ n) + SubderivAt f₂ (x₂ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (x₂ n) +
      SubderivAt (fun x => ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) (x₂ n):= by
   intro n
   rw[ADMM_iter_process₂'_eq2_1' n , ADMM_iter_process₂'_eq2_1'_1 n]
   rw[SubderivAt.add (convexOn_const (f₁ (x₁ n)) (convex_univ)) admm.cf₂
   (@continuousOn_const E₂ ℝ _ _ univ (f₁ (x₁ n))) (x₂ n)]
   rw[SubderivAt.add (ConvexOn.add (convexOn_const (f₁ (x₁ n)) (convex_univ)) admm.cf₂)
   (inner_convex2 n) (ContinuousOn.add (@continuousOn_const E₂ ℝ _ _ univ (f₁ (x₁ n)))  f₂_continuous) (x₂ n)]
   rw[SubderivAt.add (ConvexOn.add (ConvexOn.add (convexOn_const (f₁ (x₁ n)) (convex_univ)) admm.cf₂) (inner_convex2 n))
   (norm_covex2 n) (ContinuousOn.add (ContinuousOn.add (@continuousOn_const E₂ ℝ _ _ univ (f₁ (x₁ n)))  f₂_continuous) (inner_continuous2 n)) (x₂ n)]

-- #check
lemma ADMM_iter_process₂'_eq2_2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun _ => f₁ (x₁ n)) (x₂ n) + SubderivAt f₂ (x₂ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (x₂ n) +
      SubderivAt (fun x => ρ / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) (x₂ n) =
      0 + SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}:= by
   intro n
   rw[ADMM_iter_process₂'_eq3_1 n,ADMM_iter_process₂'_eq3_2 n,ADMM_iter_process₂'_eq3_3 n]

lemma ADMM_iter_process₂'_eq2_3 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      0 + SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}
      = SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}:= by
   intro n
   rw[zero_add]

lemma ADMM_iter_process₂'_eq1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}
      = SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem ρ) (x₁ n , x , y n.natPred)) (x₂ n):=by
   intro n
   rw[← ADMM_iter_process₂'_eq2_3 n,← ADMM_iter_process₂'_eq2_2 n , ← ADMM_iter_process₂'_eq2_1 n]

lemma ADMM_iter_process₂' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , 0 ∈
      SubderivAt f₂ (x₂ n) + { A₂† (y (n - 1))} + {ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}:= by
   intro n
   have := first_order_convex_iff_subgradient (f := (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem ρ) (x₁ n , x , y n.natPred))) (x₂ n)
   have h := admm.itex₂ n.natPred
   have eq : n.natPred + 1 = n := by apply PNat.natPred_add_one
   rw[eq , this , ← ADMM_iter_process₂'_eq1 n] at h
   exact h

lemma ADMM_iter_process₂ [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      (- A₂† (y (n - 1))- ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) -b))) ∈ SubderivAt f₂ (x₂ n) := by
   intro n
   let S := SubderivAt f₂ (x₂ n)
   let p := A₂† (y (n - 1))
   let q := ρ • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) -b))
   show - p - q ∈ S
   have := ADMM_iter_process₂' n
   change 0 ∈ S + {p} + {q} at this
   apply change_item this

lemma u_inthesubgradient [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , u n ∈ SubderivAt f₁ (x₁ n) := by
  intro n
  have : (↑n : Nat) - 1 + 1 = (↑n : Nat) := PNat.natPred_add_one n
  let un := u n
  have h₁ : un = u n := rfl
  let yn := y n; let yn' := y (n-1)
  have h₂ : yn = y n := rfl; have h₃ : yn' = y (n-1) := rfl
  let x₁n := x₁ n; let x₂n := x₂ n; let x₂n' := x₂ (n-1)
  have h₄ : x₁n = x₁ n := rfl; have h₅ : x₂n = x₂ n := rfl
  have aux : yn' = yn - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b) := by
      rw [h₂, ← this, admm.itey (n - 1), ← h₃, this, ← h₄, ← h₅]
      exact eq_sub_of_add_eq rfl
  have : -A₁†  yn' - ρ • A₁† (A₁ x₁n + A₂ x₂n' - b) = un :=
      calc -A₁† yn' - ρ • A₁† (A₁ x₁n + A₂ x₂n' - b)
         _ = -A₁† (yn' + ρ • (A₁ x₁n + A₂ x₂n' -b)) := by
            rw [← A₁†.map_smul, A₁†.map_add, neg_add']
         _ = -A₁† (yn - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b) + ρ • (A₁ x₁n + A₂ x₂n' -b)) := by rw [aux]
         _ = -A₁† (yn - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b) + ρ • (A₁ x₁n + A₂ x₂n + A₂ x₂n' - A₂ x₂n -b)) := by
            congr
            rw [add_assoc, add_comm (A₂ x₂n), ← add_assoc]
            exact Eq.symm (add_sub_cancel_right (A₁ x₁n + A₂ x₂n') (A₂ x₂n))
         _ = -A₁† (yn - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b) + ρ • (A₁ x₁n + A₂ x₂n - b) + ρ • (A₂ x₂n' - A₂ x₂n)) := by
            have :  ρ • (A₁ x₁n + A₂ x₂n + A₂ x₂n' - A₂ x₂n - b) = ρ • (A₁ x₁n + A₂ x₂n - b) + ρ • (A₂ x₂n' - A₂ x₂n) := by
               rw [←smul_add]
               refine (smul_right_inj ?hc).mpr ?_
               exact Ne.symm (ne_of_lt admm.hrho)
               rw[←add_sub]
               exact add_sub_right_comm (A₁ x₁n + A₂ x₂n) (A₂ x₂n' - A₂ x₂n) b
            rw [this, add_assoc]
         _ = -A₁† (yn - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b) + ρ • (A₁ x₁n + A₂ x₂n -b ) + ρ • A₂ (x₂n' - x₂n)) := by
            have : ρ • (A₂ x₂n' - A₂ x₂n) = ρ • A₂ (x₂n' - x₂n) := by
               refine (smul_right_inj ?hc).mpr ?_
               exact Eq.symm (ContinuousLinearMap.map_sub A₂ x₂n' x₂n)
            rw [this]
         _ = -A₁† (yn + ((1 - τ) * ρ) • (A₁ x₁n + A₂ x₂n - b) + ρ • A₂ (x₂n' - x₂n)) := by
            have : yn - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b) + ρ • (A₁ x₁n + A₂ x₂n - b) = yn +
               ((1 - τ) * ρ) • (A₁ x₁n + A₂ x₂n - b) := by
               refine sub_eq_sub_iff_add_eq_add.mp ?_
               rw[sub_sub,←add_smul];simp
               rw[sub_mul,add_sub];simp
            rw [this]
         _ = -A₁† (yn + ((1 - τ) * ρ) • (A₁ x₁n + A₂ x₂n - (A₁ x₁' + A₂ x₂')) + ρ • A₂ (x₂n' - x₂n)) := by
            rw [(admm_kkt.h).eq]
         _ = -A₁† (yn + ((1 - τ) * ρ) • ((A₁ x₁n - A₁ x₁') + (A₂ x₂n - A₂ x₂')) + ρ • A₂ (x₂n' - x₂n)) := by
            have : A₁ x₁n + A₂ x₂n - (A₁ x₁' + A₂ x₂') = (A₁ x₁n - A₁ x₁') + (A₂ x₂n - A₂ x₂') := by
               exact add_sub_add_comm (A₁ x₁n) (A₂ x₂n) (A₁ x₁') (A₂ x₂')
            rw [this]
         _ = -A₁† (yn + ((1 - τ) * ρ) • ((A₁ (e₁ n)) + A₂ (e₂ n)) + ρ • A₂ (x₂n' - x₂n)) := by
            have h1 : A₁ x₁n - A₁ x₁' = A₁ (e₁ n) := by
               have : e₁ n = x₁ n - x₁' := rfl
               rw [this, ← h₄]
               exact Eq.symm (ContinuousLinearMap.map_sub A₁ x₁n x₁')
            have h2 : A₂ x₂n - A₂ x₂' = A₂ (e₂ n) := by
               have : e₂ n = x₂ n - x₂' := rfl
               rw [this, ← h₅]
               exact Eq.symm (ContinuousLinearMap.map_sub A₂ x₂n x₂')
            rw [← h1, ← h2]
         _ = un := rfl
  rw [← h₁, ← this]
  exact ADMM_iter_process₁ n

lemma v_inthesubgradient [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , v n ∈ SubderivAt f₂ (x₂ n) := by
   intro n
   have : (↑n : Nat) - 1 + 1 = (↑n : Nat) := PNat.natPred_add_one n
   -- notation for v n
   let vn := v n
   have h₁ : vn = v n := rfl
   -- notation for y n, y (n-1)
   let yn := y n; let yn' := y (n-1)
   have h₂ : yn = y n := rfl
   have h₃ : yn' = y (n-1) := rfl
   -- notation for x₁ n, x₂ n, x₂ (n-1)
   let x₁n := x₁ n; let x₂n := x₂ n
   have h₄ : x₁n = admm.x₁ n := rfl
   have h₅ : x₂n = admm.x₂ n := rfl

   -- prove : y_n-1 = y_n - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b)
   have aux : yn' = yn - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b) := by
      rw [h₂, ← this, admm.itey (n - 1), ← h₃, this, ← h₄, ← h₅]
      exact eq_sub_of_add_eq rfl
   -- calculate LHS
   have : -A₂† yn' - ρ • A₂† (A₁ x₁n + A₂ x₂n - b) = vn :=
      calc -A₂† yn' - ρ • A₂† (A₁ x₁n + A₂ x₂n - b)
         _ = -A₂† (yn' + ρ • (A₁ x₁n + A₂ x₂n - b)) := by
           rw [← A₂†.map_smul, A₂†.map_add, neg_add']
         _ = -A₂† (yn - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b) + ρ • (A₁ x₁n + A₂ x₂n - b)) := by rw[aux]
         _ = -A₂† (yn + ((1 - τ) * ρ) • (A₁ x₁n + A₂ x₂n - b)) := by
            have : yn - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b) + ρ • (A₁ x₁n + A₂ x₂n - b) = yn +
              ((1 - τ) * ρ) • (A₁ x₁n + A₂ x₂n - b) := by
               refine sub_eq_sub_iff_add_eq_add.mp ?_
               rw[sub_sub , ←add_smul]
               simp
               rw[sub_mul,add_sub]
               simp
            rw[this]
         -- now substitute for b = (A₁ x₁' + A₂ x₂')
         _ = -A₂† (yn + ((1 - τ) * ρ) • (A₁ x₁n + A₂ x₂n - (A₁ x₁' + A₂ x₂'))) := by
            rw [(admm_kkt.h).eq]
         _ = -A₂† (yn + ((1 - τ) * ρ) • ((A₁ x₁n - A₁ x₁') + (A₂ x₂n  - A₂ x₂'))) := by
            have : A₁ x₁n + A₂ x₂n - (A₁ x₁' + A₂ x₂') = (A₁ x₁n - A₁ x₁') + (A₂ x₂n - A₂ x₂') := by
               exact add_sub_add_comm (A₁ x₁n) (A₂ x₂n) (A₁ x₁') (A₂ x₂')
            rw [this]
         _ = -A₂† (yn + ((1 - τ) * ρ) • ((A₁ (e₁ n)) + A₂ (e₂ n))) := by
            have h1 : A₁ x₁n - A₁ x₁' = A₁ (e₁ n) := by
               have : e₁ n = x₁ n - x₁' := rfl
               rw [this, ← h₄]
               exact Eq.symm (ContinuousLinearMap.map_sub A₁ x₁n x₁')
            have h2 : A₂ x₂n - A₂ x₂' = A₂ (e₂ n) := by
               have : e₂ n = x₂ n - x₂' := rfl
               rw [this, ← h₅]
               exact Eq.symm (ContinuousLinearMap.map_sub A₂ x₂n x₂')
            rw [←h1, ←h2]
         _ = vn := rfl
   rw [← h₁, ← this]
   exact ADMM_iter_process₂ n

lemma Φ_isdescending_eq1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b
      = (1 / (τ * ρ)) • (y (n + 1) - y n):= by
   intro n
   rw [admm.itey n,add_comm (y n)]
   simp only [one_div, mul_inv_rev, add_sub_cancel_right]
   rw [smul_smul, mul_assoc]
   nth_rw 2 [← mul_assoc]
   have htau1 : τ⁻¹ * τ = 1:= by
      refine inv_mul_cancel₀ ?h
      linarith[admm.htau.1];
   have hrho1 : ρ⁻¹ * ρ = 1:= by
      refine inv_mul_cancel₀ ?h
      linarith[admm.hrho];
   rw [htau1 , one_mul, hrho1, one_smul]

lemma Φ_isdescending_eq2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , (1 / (τ * ρ)) • (y (n + 1) - y n)
      = (1 / (τ * ρ)) • (ey (n + 1) - ey n):= by
   intro n
   calc
      _ = (1 / (τ * ρ)) • (y (n + 1) - y' + y' - y n) := by rw [sub_add, sub_self, sub_zero]
      _ = (1 / (τ * ρ)) • (y (n + 1) - y' - (y n - y')) := by simp only [one_div,
        mul_inv_rev, sub_add_cancel, sub_sub_sub_cancel_right]

lemma Φ_isdescending_eq3 [Setting E₁ E₂ F admm admm_kkt] : ∀ n , A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b
      = A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)) := by
   intro n
   calc
      _ = A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - (A₁ x₁' + A₂ x₂') := by rw [Satisfaction_ofthekkt.eq]
      _ = A₁ (x₁ (n + 1)) - A₁ x₁' + (A₂ (x₂ (n + 1)) - A₂ x₂') :=
         add_sub_add_comm (A₁  (x₁ (n + 1))) (A₂ (x₂ (n + 1))) (A₁  x₁') (A₂ x₂')
      _ = A₁ ((x₁ (n + 1)) - x₁') + A₂ ((x₂ (n + 1)) - x₂') := by simp only [map_sub]
      _ = A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)) := by rw [e₁, e₂]

lemma Φ_isdescending_eq3' [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+ , A₁ (x₁ n) + A₂ (x₂ n) - b = A₁ (e₁ n) + A₂ (e₂ n) := by
   intro n
   have := Φ_isdescending_eq3 n.natPred
   have h: n = n.natPred + 1 := by simp only [PNat.natPred_add_one]
   rw[← h] at this
   exact this

lemma subgradientAt_mono_u [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
      (0 : ℝ) ≤ (inner (u (n) + A₁† y') (x₁ (n) - x₁')) := by
   intro n
   calc
      _= inner (u (n) - (- A₁† y')) (x₁ (n) - x₁') := by simp[v]
      _≥ (0 : ℝ) := by
         apply subgradientAt_mono
         apply u_inthesubgradient
         exact admm_kkt.h.subgrad₁

lemma subgradientAt_mono_v [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
      (0 : ℝ) ≤ (inner (v (n) + A₂† y') (x₂ (n) - x₂')) := by
   intro n
   calc
      _= inner (v (n) - (- A₂† y')) (x₂ (n) - x₂') := by simp[v]
      _≥ (0 : ℝ) := by
         apply subgradientAt_mono
         apply v_inthesubgradient
         exact admm_kkt.h.subgrad₂

lemma expended_u_gt_zero [Setting E₁ E₂ F admm admm_kkt]: ∀ n, (0 : ℝ) ≤
      (inner ( -ey (n + 1) - ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
      - (ρ • (A₂ (x₂ (n) - x₂ (n+1))))) (A₁ (e₁ (n + 1)))):= by
   intro n
   let Ae1 := A₁ (e₁ (n + 1))
   let e' := e₁ (n + 1)
   let block := -ey (n + 1) - ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
   - (ρ • (A₂ (x₂ (n) - x₂ (n+1))))
   let u' := - A₁† (y (n + 1) + ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
         + (ρ • (A₂ (x₂ (n) - x₂ (n+1)))))
   let x_diff := x₁ (n + 1) - x₁'
   let succ_n := Nat.toPNat' (n + 1)
   calc
      _= inner (𝕜 := ℝ) block Ae1 := by rfl
      _= inner (A₁† block) (e') := by rw [ContinuousLinearMap.adjoint_inner_left]
      _= inner (u' + A₁† y') (x_diff) := by
         let block₁ := y (n + 1) + ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))) + (ρ • (A₂ (x₂ (n) - x₂ (n+1))))
         have split_block : -block = block₁ - y' := by
            simp[block, block₁]
            have split_ey :  ey (n + 1) = (y (n + 1)) - y' := by rfl
            rw [split_ey]
            simp
            rw [sub_eq_add_neg,neg_sub (y' - y (n + 1)),add_comm,sub_eq_add_neg, neg_sub]
            rw [add_assoc,← smul_add,smul_sub]
            let A := ((1 - τ) * ρ) • ((A₁) (e₁ (n + 1)) + (A₂) (e₂ (n + 1)))
            let C := y (n + 1)
            let D := ρ • ((A₂) (x₂ n))
            let E := ρ • ((A₂) (x₂ (n + 1)))
            change A + (C - y' + (D - E)) = C + A + (D - E) - y'
            rw [← add_assoc,sub_eq_add_neg,← add_assoc,add_comm A C]
            rw [add_assoc,add_comm (-y') (D - E),← add_assoc,← sub_eq_add_neg]
         rw [← neg_neg block,split_block,neg_sub,A₁†.map_sub]
         have u'_eq : - A₁† block₁ = u' := by
            simp[u']
            rw [← A₁†.map_smul, ← A₁†.map_smul,smul_sub,← A₁†.map_smul, ← A₁†.map_smul]
            rw [← A₁†.map_sub,← A₁†.map_neg, ← A₁†.map_neg, ← A₁†.map_neg, ← A₁†.map_neg, ← A₁†.map_neg]
            rw [← A₁†.map_add, ← A₁†.map_add, ← A₁†.map_add]
            simp[block₁]
            rw [← smul_neg, neg_sub,smul_sub]
         have Aty'_eq : A₁† y' = A₁† y' := rfl
         rw [← u'_eq, Aty'_eq, add_comm, sub_eq_add_neg]
         simp[e', x_diff]
         rfl
      _= (inner (u (succ_n) + A₁† y') (x₁ (succ_n) - x₁')) := by rfl
      _≥ 0 := by apply subgradientAt_mono_u

lemma expended_v_gt_zero [Setting E₁ E₂ F admm admm_kkt]: ∀ n,
      (inner ( -ey (n + 1) - ((1 - τ) * ρ) • ((A₁ (e₁ (n + 1))) + (A₂ (e₂ (n + 1)))))
      (A₂ (e₂ (n + 1)))) ≥ (0 : ℝ) := by
   intro n
   let succ_n := Nat.toPNat' (n + 1)
   let ey' := ey (succ_n)
   let e₁' := e₁ (succ_n)
   let e₂' := e₂ (succ_n)
   let y_k_1 := y (succ_n)
   let v_k_1 := v (succ_n)
   let x_diff := x₂ (succ_n) - x₂'
   calc
   _ = inner ( -ey'- ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂')) (A₂ e₂') := by rfl
   _ = inner (A₂† (-ey'- ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂'))) (e₂') := by rw [ContinuousLinearMap.adjoint_inner_left]
   _ = inner (-A₂† (ey'+ ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂'))) (e₂') := by
      rw [sub_eq_add_neg,← neg_add,A₂†.map_neg]
   _ = inner (-A₂† (y_k_1 - y' + ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂'))) (e₂') := by
      have sub : ey' = y_k_1 - y' := by simp [ey', y_k_1] ;rfl
      rw [sub]
   _ = inner (-A₂† (y_k_1 + ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂')) + A₂† y') (e₂') := by
      rw [sub_eq_add_neg, add_comm y_k_1, add_assoc,A₂†.map_add]
      simp
   _ = inner (v_k_1 + A₂† y') x_diff := rfl
   _ ≥ (0 : ℝ) := by apply subgradientAt_mono_v

lemma starRingEnd_eq_R (x : ℝ) : (starRingEnd ℝ) x = x := rfl

lemma expended_u_v_gt_zero [Setting E₁ E₂ F admm admm_kkt]: ∀ n , (inner (ey (n + 1)) (-(A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))))
      - (1 - τ) * ρ * ‖A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2
      + ρ * (inner (-A₂ (x₂ (n) - x₂ (n + 1))) (A₁ (e₁ (n + 1)))) ≥ 0 := by
   intro n
   let A_e_sum := (A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1))
   let A_x_sum := -A₂ (x₂ (n) - x₂ (n + 1))
   let ey' := ey (n + 1)
   let Ae1 := A₁ (e₁ (n + 1))
   let Ae2 := A₂ (e₂ (n + 1))
   calc
   _ = inner ey' (-(A_e_sum)) - (1 - τ) * ρ * (inner A_e_sum A_e_sum)
      + ρ * (inner (A_x_sum) (Ae1)) := by rw [norm_sq_eq_inner (𝕜:=ℝ) (A_e_sum)];rfl
   _ = inner ey' (-(A_e_sum)) + inner (- ((1 - τ) * ρ) • A_e_sum) A_e_sum
      + ρ * (inner A_x_sum Ae1) := by rw [smul_left,starRingEnd_eq_R];ring
   _ = inner (-ey') A_e_sum + inner (- ((1 - τ) * ρ) • A_e_sum) A_e_sum
      + ρ * (inner A_x_sum Ae1) := by
      rw [inner_neg_right (𝕜 := ℝ), inner_neg_left (𝕜 := ℝ), inner_neg_left (𝕜 := ℝ)]
   _ = inner (-ey' - ((1 - τ) * ρ) • A_e_sum) A_e_sum + ρ * (inner A_x_sum Ae1) := by
      rw [← add_left];ring_nf
      have sub: -ey' + (τ * ρ - ρ) • A_e_sum = -ey' - (-(τ * ρ) + ρ) • A_e_sum := by
         rw [← sub_eq_zero,sub_eq_add_neg]
         rw [sub_eq_add_neg (G := F) (-ey') ((-(τ * ρ) + ρ) • A_e_sum)]
         rw [← neg_one_smul (R := ℝ) (-ey' + -((-(τ * ρ) + ρ) • A_e_sum))]
         rw [smul_add (-1)  (-ey') (-((-(τ * ρ) + ρ) • A_e_sum))]
         rw [neg_smul_neg, neg_smul_neg,one_smul, one_smul]
         rw [add_assoc, add_comm, add_assoc,add_comm ey' ((-(τ * ρ) + ρ) • A_e_sum)]
         rw [add_assoc]
         rw [add_neg_cancel, add_zero]
         rw [← add_smul (τ * ρ - ρ) (-(τ * ρ) + ρ) (A_e_sum)]
         rw [add_comm (-(τ * ρ)) ρ, ← add_assoc]
         rw [sub_eq_add_neg, add_assoc (τ * ρ) (-ρ) ρ, add_comm (-ρ) ρ, add_neg_cancel, add_zero, add_neg_cancel, zero_smul]
      rw [sub]
   _ = inner (-ey' - ((1 - τ) * ρ) • A_e_sum) (Ae1 + Ae2) + ρ * (inner A_x_sum Ae1) := by rfl
   _ = inner (-ey' - ((1 - τ) * ρ) • A_e_sum) Ae1 + inner (-ey' - ((1 - τ) * ρ) • A_e_sum) Ae2
      + ρ * (inner A_x_sum Ae1) := by rw [inner_add_right]
   _ = inner (-ey' - ((1 - τ) * ρ) • A_e_sum) Ae2
      + inner (-ey' - ((1 - τ) * ρ) • A_e_sum + ρ • A_x_sum) Ae1 := by
      rw [inner_add_left,add_assoc]
      rw [inner_smul_left A_x_sum Ae1 ρ, starRingEnd_eq_R, add_comm];ring
   _ = (inner ( -ey (n + 1) - ((1 - τ) * ρ) • ((A₁ (e₁ (n + 1))) + (A₂ (e₂ (n + 1)))))
       (A₂ (e₂ (n + 1)))) +
       (inner ( -ey (n + 1) - ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))) - (ρ • (A₂ (x₂ (n) - x₂ (n+1)))))
       (A₁ (e₁ (n + 1)))) := by
         have sub : ρ • (A₂ (x₂ (n + 1)) - A₂ (x₂ (n))) = -1 • ρ • (A₂ (x₂ (n)) - A₂ (x₂ (n + 1))) := by
            rw [smul_comm,neg_one_smul,neg_sub]
         simp[ey', A_e_sum, Ae2, A_x_sum, Ae1]
         nth_rw 5 [sub_eq_add_neg]
         rw [← neg_one_smul (R := ℝ) (ρ • (A₂ (x₂ n) - A₂ (x₂ (n + 1)))),sub]
         simp only [Int.reduceNeg, neg_smul, one_smul]
   _ ≥ 0 := by
      apply add_nonneg
      apply expended_v_gt_zero
      apply expended_u_gt_zero

lemma substitution1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , - ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))) ) = ρ * (inner (A₂ (x₂ n - x₂ (n+1))) (A₂ (e₂ (n+1))) ) := by
   intro n
   rw [neg_mul (ρ) (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))))]
   rw [← mul_neg]
   rw [← inner_neg_left (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1)))]
   rw [← map_neg A₂ (x₂ (n+1) - x₂ n)]
   rw [neg_sub (x₂ (n+1)) (x₂ n)]

lemma substitution2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b - A₂ (e₂ (n+1)) = A₁ (e₁ (n+1)) := by
   intro n
   have h := Φ_isdescending_eq3 n
   simp [h]

lemma Φ_isdescending_inequ1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , 1/(τ * ρ) * (inner (ey (n+1)) ((ey n)-(ey (n+1))))
      - (1-τ)*ρ*‖admm.A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))
      -ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))) ) ≥ 0 := by
   intro n
   let pm1 := 1 / (τ * ρ)
   let pm2 := (1 - τ) * ρ
   have h1:  pm1 * (inner (ey (n+1)) ((ey n)-(ey (n+1))))
      = (inner (ey (n + 1)) (-((A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1))))) := by
      calc  pm1 * (inner (ey (n+1)) ((ey n)-(ey (n+1))))
         _ = (inner (ey (n+1)) ( pm1 • ((ey n)-(ey (n+1))) )) := by
            rw [← real_inner_smul_right (ey (n+1)) ((ey n)-(ey (n+1))) pm1]
         _ = (inner (ey (n+1)) ( pm1 • -((ey (n+1))-(ey n)) )) := by
            rw [← neg_sub (ey (n+1)) (ey n)]
         _ = (inner (ey (n+1)) ( -(pm1 • ((ey (n+1))-(ey n))) )) := by
            rw [smul_neg]
         _ = (inner (ey (n+1)) ( -(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) )) := by
            rw [← Φ_isdescending_eq2, ← Φ_isdescending_eq1]
         _ = (inner (ey (n+1)) (-(A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))))) := by
            rw [Φ_isdescending_eq3]
   have h2:  pm2*‖admm.A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 = pm2*‖admm.A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2 := by
      rw [Φ_isdescending_eq3]
   have h3: ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)) -ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))) )
   =  ρ * (inner (-A₂ (x₂ (n) - x₂ (n + 1))) (A₁ (e₁ (n+1)))) := by
      calc ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))
         -ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))) )
         _ = ρ * (inner (- (A₂ (x₂ (n) - x₂ (n+1)))) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))
         - ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))) ) := by
            rw [← neg_sub (x₂ n) (x₂ (n+1))]
            rw [map_neg A₂ (x₂ (n) - x₂ (n+1))]
         _ = - ρ * (inner (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))
         - ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))) ) := by
            rw [inner_neg_left (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)]
            simp
         _ = - ρ * (inner (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))
         + ρ * (inner (A₂ (x₂ n - x₂ (n+1))) (A₂ (e₂ (n+1))) ) := by
            rw [← substitution1]
            simp only [map_sub, neg_mul];rfl
         _ = ρ * (inner (A₂ (x₂ n - x₂ (n+1))) (A₂ (e₂ (n+1))) )
         - ρ * (inner (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)) := by
            ring
         _ = ρ * (inner (A₂ (x₂ (n) - x₂ (n+1))) (A₂ (e₂ (n+1)) - (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))):= by
            rw [← mul_sub]
            rw [← inner_sub_right (A₂ (x₂ (n) - x₂ (n+1))) (A₂ (e₂ (n+1))) ((A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))]
         _ = - ρ * (inner (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b - A₂ (e₂ (n+1)))) := by
            rw [← neg_sub (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) (A₂ (e₂ (n+1)))]
            rw [inner_neg_right]
            simp only [map_sub, mul_neg, neg_mul]
         _ = - ρ * (inner (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (e₁ (n+1)))) := by
            rw [substitution2]
         _ = ρ * (inner (-A₂ (x₂ (n) - x₂ (n + 1))) (A₁ (e₁ (n+1)))) := by
            rw [neg_mul (ρ) (inner (A₂ (x₂ (n) - x₂ (n + 1))) (A₁ (e₁ (n+1))))]
            rw [← mul_neg]
            rw [← inner_neg_left (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (e₁ (n+1)))]
   rw [h1,h2]
   have h4: (inner (ey (n + 1)) (-((A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1)))))
   - pm2*‖admm.A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2 +
   (ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)) -ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))) )) = (inner (ey (n + 1)) (-((A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1)))))
   - pm2*‖admm.A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2 +
   ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)) -ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))) ) := by ring
   rw [← h4,h3]
   exact expended_u_v_gt_zero n

lemma A'υ_inthesubgradient [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , - (A₂†) (υ n) ∈ SubderivAt f₂ (x₂ n):= by
   intro n
   rw [υ]
   have : v n = - A₂† (y n + (( 1 - τ) * ρ )•(A₁ (e₁ n) + A₂ (e₂ n))):= rfl
   rw[Φ_isdescending_eq3' , ← this]
   apply v_inthesubgradient

lemma Φ_isdescending_inequ2 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      inner ( - ( A₂† ( υ (n+1) - υ n ))) ((x₂ (n+1)) - (x₂ n)) ≥ ( 0 : ℝ ) := by
   intro n
   let A₂T := A₂†
   let A₂υn := - (A₂T ((υ) n))
   let A₂υn1 := - (A₂T ((υ) (n+1)))
   have h1 : A₂υn ∈ SubderivAt f₂ (x₂ n) := by apply A'υ_inthesubgradient
   have h2 : A₂υn1 ∈ SubderivAt f₂ (x₂ (n+1)) := by apply A'υ_inthesubgradient (n+1)
   have mono : inner (A₂υn1 - A₂υn) (x₂ (n+1) - x₂ n) ≥ (0:ℝ):= subgradientAt_mono h2 h1
   have h: -(A₂T ((υ (n+1)) - (υ n))) = A₂υn1 - A₂υn := by
      calc
         -(A₂T ((υ (n+1)) - (υ n))) = - (A₂T (υ (n+1)) - A₂T (υ n)) := by continuity
         _=  (A₂T ((υ) n)) - (A₂T ((υ) (n+1))) := by simp
         _= - (A₂T ((υ) (n+1))) - (-(A₂T ((υ) n))) := by rw [sub_neg_eq_add,add_comm (- (A₂T ((υ) (n+1)))),sub_eq_add_neg]
         _= A₂υn1 - A₂υn := by rfl
   rwa [h]

lemma Φ_isdescending_inequ3 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)) ≤ M (n+1) := by
   intro n
   let A₂_x_diff := A₂ (x₂ (n+1) - x₂ n)
   let r_n := A₁ (x₁ n) + A₂ (x₂ n) - b
   let r_n_1 := A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b
   let υ_diff := υ (n+1) - υ n
   let y_diff := y (n+1) - y n
   let x_diff := x₂ (n+1) - x₂ n
   let A₂T := A₂†
   have h: ρ * (inner A₂_x_diff r_n_1) =
      M (n+1) + inner υ_diff A₂_x_diff := by
         calc
         ρ * (inner A₂_x_diff r_n_1) =
         (1 - τ) * ρ * (inner A₂_x_diff r_n_1) + (τ * ρ) * (inner A₂_x_diff r_n_1) := by
            linarith
         _= (1 - τ) * ρ * (inner A₂_x_diff r_n_1) + (inner A₂_x_diff ((τ * ρ) • r_n_1)) := by
            rw [inner_smul_right]
         _= (1 - τ) * ρ * (inner A₂_x_diff r_n_1) + (inner A₂_x_diff y_diff) := by
            have : (τ * ρ) • r_n_1 = y_diff := by
               simp [r_n_1, y_diff]
               rw [Φ_isdescending_eq1, ← mul_smul, mul_div, mul_one, div_self, one_smul]
               intro H
               rw [mul_eq_zero] at H
               rcases H with _ | _
               · linarith [admm.htau]
               · linarith [admm.hrho]
            rw [this]
         _= (1 - τ) * ρ * (inner A₂_x_diff r_n) - (1 - τ) * ρ * (inner A₂_x_diff r_n)
          + (1 - τ) * ρ * (inner A₂_x_diff r_n_1) + (inner A₂_x_diff y_diff) := by
            rw [sub_self ((1 - τ) * ρ * (inner A₂_x_diff r_n)), zero_add]
         _= M (n+1) - (1 - τ) * ρ * (inner A₂_x_diff r_n)
          + (1 - τ) * ρ * (inner A₂_x_diff r_n_1) + (inner A₂_x_diff y_diff) := by
            rw [M]; rfl
         _= (1 - τ) * ρ * ((inner A₂_x_diff r_n_1) - (inner A₂_x_diff r_n)) +
            M (n+1) + (inner A₂_x_diff y_diff) := by
            ring
         _= (1 - τ) * ρ * (inner A₂_x_diff (r_n_1 - r_n)) +
            M (n+1) + (inner A₂_x_diff y_diff) := by
            rw [← inner_sub_right]
         _= inner A₂_x_diff (((1 - τ) * ρ) • (r_n_1 - r_n)) +
            M (n+1) + (inner A₂_x_diff y_diff) := by
            rw [inner_smul_right]
         _= inner A₂_x_diff (υ_diff - y_diff) +
            M (n+1) + (inner A₂_x_diff y_diff) := by
            have : ((1 - τ) * ρ) • (r_n_1 - r_n) = υ_diff - y_diff := by
               rw [smul_sub]
               have h1: ((1 - τ) * ρ) • r_n_1 = υ (n+1) - y (n+1) := by
                  rw [υ, add_sub_assoc, add_sub_left_comm, sub_self, add_zero]
               have h2: ((1 - τ) * ρ) • r_n = υ n - y n := by
                  rw [υ, add_sub_assoc, add_sub_left_comm, sub_self, add_zero]
               rw [h1, h2, sub_sub_eq_add_sub, sub_add_comm, add_sub_assoc, sub_add_comm, sub_add]
            rw [this]
         _= M (n+1) + (inner A₂_x_diff υ_diff) := by
            rw [inner_sub_right]
            ring
         _= M (n+1) + (inner υ_diff A₂_x_diff) := by
            rw [real_inner_comm]
   have mono: (inner υ_diff A₂_x_diff) ≤ (0:ℝ) := by
      simp [υ_diff, A₂_x_diff]
      rw [← map_sub A₂]
      have : ((inner υ_diff  A₂_x_diff):ℝ) = ((inner (A₂T υ_diff) x_diff):ℝ) := by
         rw [ContinuousLinearMap.adjoint_inner_left]
      rw [this]
      apply neg_nonneg.1
      rw [← inner_neg_left]
      apply Φ_isdescending_inequ2
   linarith

lemma Φ_isdescending_inequ4 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+, 1 / (τ * ρ) * (inner (ey (n + 1)) ((ey n) - (ey (n + 1))))
      - (1 - τ) * ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + M (n + 1)
      - ρ * (inner (A₂ (x₂ (n + 1) - x₂ n)) (A₂ (e₂ (n+1))) ) ≥ 0:= by
   intro n
   let a := 1/(τ*ρ) * (inner (ey (n+1)) ((ey n)-(ey (n+1))))
      - (1-τ)*ρ*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
   let b0 := M (n+1)
   let c := ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))) )
   let d := ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))
   have dleqb: d ≤ b0 := by apply Φ_isdescending_inequ3
   have h : a + d - c ≥ 0 := by apply Φ_isdescending_inequ1
   have : a + b0 - c ≥ 0 := by linarith
   exact this

lemma inner_eq_norm {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      (a₁ a₂ : X) : inner a₁ a₂ = 1/2 * (‖a₁‖^2 + ‖a₂‖^2 - ‖a₁- a₂‖^2) := by
   rw [norm_sub_sq (𝕜 := ℝ) a₁ a₂];ring_nf;
   rfl

lemma Φ_isdescending_eq2' [Setting E₁ E₂ F admm admm_kkt]:
      ∀ n , (τ * ρ) • (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) = ey (n+1) - ey n:=by
   intro n
   rw [Φ_isdescending_eq1, Φ_isdescending_eq2]
   simp only [one_div, mul_inv_rev]
   rw [smul_smul, mul_assoc]
   nth_rw 2 [← mul_assoc]
   rw [mul_inv_cancel₀, one_mul, mul_inv_cancel₀, one_smul]
   rcases admm.htau with ⟨h₁, _⟩
   apply ne_of_gt h₁
   apply ne_of_gt admm.hrho

lemma Φ_isdescending_inequ5' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
      1 / (τ * ρ) * (‖ey n‖^2 - ‖ey (n+1)‖^2) - (2 - τ) * ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * (M (n+1)) - ρ * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 - ρ * ‖A₂ (e₂ (n+1))‖^2 + ρ * ‖A₂ (e₂ n)‖ ^ 2
      = 2 * (1 / (τ * ρ) * (inner (ey (n+1)) ((ey n)-(ey (n+1)))) -
      (1 - τ) * ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + M (n+1) - ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1))))) := by
   intro n
   have h₄'' : ‖A₂ (x₂') - A₂ (x₂ n)‖ = ‖- (A₂ (x₂ n) - A₂ (x₂'))‖ := by simp only [neg_sub]
   have h₄' : ‖A₂ (x₂ (n+1) - x₂ n) - A₂ (e₂ (n+1))‖ = ‖A₂ (e₂ n)‖ := by rw [e₂]; rw[e₂]; simp only [map_sub,sub_sub_sub_cancel_left]; rw [h₄'', norm_neg]
   have h₆ : ‖ey (n+1) - ey n‖ = (τ * ρ) * ‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖
      := by rw [←Φ_isdescending_eq2', norm_smul]; simp only [norm_mul, Real.norm_eq_abs,mul_eq_mul_right_iff, norm_eq_zero]
            left
            have h1: τ ≥ 0 := by rcases admm.htau with ⟨h₁, _⟩; apply le_of_lt h₁
            have h2: ρ ≥ 0 := by apply le_of_lt admm.hrho
            have h3: |τ| = τ := by apply abs_eq_self.mpr h1
            have h4: |ρ| = ρ := by apply abs_eq_self.mpr h2
            rw [h3, h4]
   symm
   calc 2 * (1/(τ*ρ) * (inner (ey (n+1)) ((ey n)-(ey (n+1)))) - (1-τ)*ρ*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + M (n+1) - ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1)))))
      _ = 2 / (τ * ρ) * (inner (ey (n+1)) ((ey n)-(ey (n+1))))
      - 2 * (1-τ) * ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 2 * ρ * (inner (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1)))) := by ring
      _ = 2 / (τ * ρ) * (1 / 2 * (‖ey (n+1)‖^2 + ‖ey n‖^2 - ‖ey (n+1) - ey n‖^2)-‖ey (n+1)‖^2)
      - 2 * (1-τ) * ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 2 * ρ * ( 1 / 2 * (‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (x₂ (n+1) - x₂ n) - A₂ (e₂ (n+1))‖^2))
      := by nth_rw 2 [inner_eq_norm]; rw [inner_sub_right]; rw [inner_eq_norm, real_inner_self_eq_norm_sq]
      _ = 2 / (τ * ρ) * (1 / 2 * (‖ey n‖^2 - ‖ey (n+1) - ey n‖^2-‖ey (n+1)‖^2))
      - 2 * (1-τ) * ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 2 * ρ * ( 1 / 2 * (‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by rw [h₄']; ring_nf
      _ = 1 / (τ * ρ) * ((‖ey n‖^2 - ((τ * ρ) * ‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖)^2-‖ey (n+1)‖^2))
      - 2 * (1-τ) * ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 1 * ρ * ((‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by rw [h₆]; ring_nf
      _ = 1 / (τ * ρ) * ((‖ey n‖^2 -‖ey (n+1)‖^2)) - 1 / (τ * ρ) * (τ * ρ) ^ 2 * (‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖)^2
      - 2 * (1-τ) * ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 1 * ρ * ((‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by ring
      _ = 1 / (τ * ρ) * ((‖ey n‖^2 -‖ey (n+1)‖^2)) - (τ * ρ) * (‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖)^2
      - 2 * (1-τ) * ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 1 * ρ * ((‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by nth_rw 2 [div_eq_mul_inv]; rw [one_mul]; nth_rw 3 [pow_two]; simp [inv_mul_cancel]
            left; rw [mul_assoc]
            nth_rw 2 [← mul_assoc]
            nth_rw 2 [← mul_assoc]
            nth_rw 2 [← mul_assoc]
            rw [inv_mul_cancel₀, one_mul]
            repeat rw [← mul_assoc]
            rw [inv_mul_cancel₀, one_mul]
            apply ne_of_gt admm.hrho
            rcases admm.htau with ⟨h₁, _⟩
            apply ne_of_gt h₁
      _ = 1/(τ*ρ) * (‖ey n‖^2 - ‖ey (n+1)‖^2)
      - (2-τ)*ρ*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2*(M (n+1))
      -ρ * ‖A₂ (x₂ (n+1) - x₂ n)‖^2
      -ρ * ‖A₂ (e₂ (n+1))‖^2
      +ρ * ‖A₂ (e₂ n)‖^2
      := by ring_nf

lemma Φ_isdescending_inequ5 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , 1 / (τ * ρ) * (‖ey n‖ ^ 2 - ‖ey (n+1)‖ ^ 2)
      - (2 - τ) * ρ * ‖A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b‖ ^ 2 + 2 * M (n+1)
      - ρ * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 - ρ * ‖A₂ (e₂ (n+1))‖^2 + ρ * ‖A₂ (e₂ n)‖^2 ≥ 0:= by
   intro n
   rw [Φ_isdescending_inequ5']
   apply mul_nonneg
   · norm_num
   apply Φ_isdescending_inequ4 n

lemma basic_inequ₁' (n : ℕ+) : 2 * inner (A₂ (x₂ (n+1) - x₂ n)) (A₁ (x₁ n) + A₂ (x₂ n) - b)
      ≤ ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2 + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 := by
   have norm_abs:
      ‖A₂ (x₂ n - x₂ (n+1))‖^2 = ‖A₂ (x₂ (n+1) - x₂ (n))‖^2:= by
      rw[← norm_neg]
      have : -(A₂ (x₂ n - x₂ (n+1))) = A₂ (x₂ (n+1) - x₂ (n)) := by continuity
      rw [this]
   rw [←sub_nonneg];
   have : ‖A₂ (x₂ n - x₂ (n+1))‖^2
      + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 - 2 * inner (A₂ (x₂ (n+1) - x₂ (n))) (A₁ (x₁ n) + A₂ (x₂ n) - b)
      = ‖A₂ (x₂ n - x₂ (n+1))‖^2 - 2 * inner (A₂ (x₂ (n+1) - x₂ (n))) (A₁ (x₁ n) + A₂ (x₂ n) - b) + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      := by ring_nf
   rw [this, norm_abs, ← norm_sub_sq_real]
   apply pow_two_nonneg

lemma M_le [Setting E₁ E₂ F admm admm_kkt](n : ℕ+)(htau : 0 < τ ∧ τ ≤ 1 ): 2 * M (n + 1) ≤ (1 - τ) * ρ * ‖A₂ (x₂ n - x₂ (n + 1))‖^2
      + (1 - τ) * ρ * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
   have : (1 - τ) * ρ * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2
         + (1 - τ) * ρ * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
         = (1 - τ) * ρ * (‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2
         + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 ) := by ring
   rw [this]
   have : 2 * M (n + 1) =  (1 - τ) * ρ * ( 2 * inner (A₂ (x₂ (n + 1) - x₂ (n)))
         (A₁ (x₁ n) + A₂ (x₂ n) - b) ) := by
      dsimp [M]
      have : (n + 1).natPred = n := rfl
      simp only [this]
      ring_nf
   rw [this]
   apply mul_le_mul_of_nonneg_left (basic_inequ₁' n)
   have : 0 ≤ 1 - τ := by linarith [htau.1]
   apply mul_nonneg
   · exact this
   linarith [admm.hrho]

lemma Φ_isdescending_inequ6 [Setting E₁ E₂ F admm admm_kkt](htau : 0 < τ ∧ τ ≤ 1 ): ∀ n : ℕ+,
      1 / (τ * ρ) * ‖ey n‖^2 + ρ * ‖A₂ (e₂ n)‖^2 + (1 - τ) * ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2
      - (1 / (τ * ρ) * ‖ey (n+1)‖^2 + ρ * ‖A₂ (e₂ (n+1))‖ ^ 2
      + (1 -τ ) * ρ * ‖A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖ ^ 2)
      ≥ ρ * ‖A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b‖ ^ 2 + τ * ρ * ‖A₂ (x₂ (n + 1) - x₂ n)‖^2 := by
   intro n
   let e_y_n := 1/(τ*ρ) * ‖ey n‖^2
   let e_y_n1 := 1/(τ*ρ) * ‖ey (n+1)‖^2
   let A2_e2_n :=  ρ * ‖A₂ (e₂ n)‖^2
   let A2_e2_n1 := ρ * ‖A₂ (e₂ (n+1))‖^2
   let Ae_Ae_n := (1-τ)*ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖^2
   let Ae_Ae_n1 := (1-τ)*ρ * ‖A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2
   let Ax_Ax_n1 := ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
   let t_Ax_Ax_n1 := (2-τ)*ρ*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
   let tt_Ax_Ax_n := (1-τ)*ρ*‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
   let A_diff_x := τ * ρ * ‖A₂ (x₂ (n+1) - x₂ n)‖^2
   let A_diff_x' := τ * ρ * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
   let t_A_diff_x := ρ*‖A₂ (x₂ n - x₂ (n+1))‖^2
   let t_A_diff_x' := ρ*‖A₂ (x₂ (n+1) - x₂ (n))‖^2
   let tt_A_diff_x' := (1-τ)*ρ*‖A₂ (x₂ n - x₂ (n+1))‖^2
   let ey_diff := 1/(τ*ρ) * (‖ey n‖^2 - ‖ey (n+1)‖^2)
   have cond := by
      calc
         0 ≤ ey_diff - t_Ax_Ax_n1 + 2*(M (n+1)) - t_A_diff_x' - A2_e2_n1 + A2_e2_n := by
            dsimp [ey_diff, t_Ax_Ax_n1, t_A_diff_x', A2_e2_n1, A2_e2_n]
            linarith [Φ_isdescending_inequ5 n]
         _ ≤ ey_diff - t_Ax_Ax_n1 + tt_A_diff_x' + tt_Ax_Ax_n - t_A_diff_x' - A2_e2_n1 + A2_e2_n := by
            dsimp [ey_diff, t_Ax_Ax_n1, tt_A_diff_x', tt_Ax_Ax_n, t_A_diff_x', A2_e2_n1, A2_e2_n]
            linarith [M_le n htau]
         _= e_y_n + A2_e2_n - e_y_n1 - A2_e2_n1 - t_Ax_Ax_n1 + tt_A_diff_x' + tt_Ax_Ax_n - t_A_diff_x' := by ring
         _= e_y_n + A2_e2_n - e_y_n1 - A2_e2_n1 - t_Ax_Ax_n1 + tt_A_diff_x' + Ae_Ae_n - t_A_diff_x' := by
            dsimp [Ae_Ae_n, tt_Ax_Ax_n]; rw [Φ_isdescending_eq3' n]
         _= e_y_n + A2_e2_n - e_y_n1 - A2_e2_n1
         - Ae_Ae_n1 + Ae_Ae_n - Ax_Ax_n1 + t_A_diff_x - A_diff_x' - t_A_diff_x' := by
            dsimp [t_Ax_Ax_n1, Ax_Ax_n1, Ae_Ae_n1]; rw [← Φ_isdescending_eq3 n];ring
   apply ge_iff_le.mpr
   apply le_of_sub_nonneg
   let left_sub_right := e_y_n + A2_e2_n + Ae_Ae_n -
      (e_y_n1 + A2_e2_n1 + Ae_Ae_n1) - (Ax_Ax_n1 + A_diff_x)
   have norm_abs : ‖A₂ (x₂ n - x₂ (n+1))‖^2 = ‖A₂ (x₂ (n+1) - x₂ (n))‖^2:= by
      rw[norm_comm A₂ (x₂ n) (x₂ (n+1))]
   have equation := by
      calc left_sub_right
         _= e_y_n + A2_e2_n + Ae_Ae_n - e_y_n1 - A2_e2_n1 - Ae_Ae_n1 - (Ax_Ax_n1 + A_diff_x) := by ring
         _= e_y_n + A2_e2_n - e_y_n1 - A2_e2_n1 - Ae_Ae_n1 + Ae_Ae_n - Ax_Ax_n1
            + t_A_diff_x - A_diff_x - t_A_diff_x := by ring
         _= e_y_n + A2_e2_n - e_y_n1 - A2_e2_n1 - Ae_Ae_n1 + Ae_Ae_n - Ax_Ax_n1
            + t_A_diff_x - A_diff_x' - t_A_diff_x := by
            dsimp [A_diff_x, A_diff_x']; rw[norm_abs]
         _= e_y_n + A2_e2_n - e_y_n1 - A2_e2_n1
         +(- Ae_Ae_n1 + Ae_Ae_n- Ax_Ax_n1 + t_A_diff_x - A_diff_x' - t_A_diff_x) := by ring
         _= e_y_n + A2_e2_n - e_y_n1 - A2_e2_n1
         - Ae_Ae_n1 + Ae_Ae_n - Ax_Ax_n1 + t_A_diff_x - A_diff_x' - t_A_diff_x' := by
            dsimp [t_A_diff_x, t_A_diff_x']
            rw [norm_abs]
            ring
   have res := by
      calc
         0 ≤ e_y_n + A2_e2_n - e_y_n1 - A2_e2_n1 - Ae_Ae_n1 + Ae_Ae_n - Ax_Ax_n1 + t_A_diff_x - A_diff_x' - t_A_diff_x':= by exact cond
         _= left_sub_right := by rw [equation]
         _= 1/(τ*ρ) * ‖ey n‖^2 + ρ * ‖A₂ (e₂ n)‖^2 + (1-τ)*ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖^2
         -(
            1/(τ*ρ) * ‖ey (n+1)‖^2 + ρ * ‖A₂ (e₂ (n+1))‖^2
            +(1-τ)*ρ * ‖A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2
         )-( ρ * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
         + τ * ρ * ‖A₂ (x₂ (n+1) - x₂ n)‖^2) := by rfl
   exact res

lemma basic_inequ₂ (n : ℕ+) : - 2 * inner (A₂ (x₂ (n+1) - x₂ n)) (A₁ (x₁ n) + A₂ (x₂ n) - b)
      ≤ τ * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 + 1 / τ * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 := by
   rw [← sub_nonneg]
   have h : τ ≥ 0 := by
      rcases admm.htau with ⟨h₁, _⟩
      linarith
   have h₁ : √τ ^2 = τ := by
      apply Real.sq_sqrt
      assumption
   have h₂ : (τ)⁻¹ = (√τ)⁻¹ ^2 := by
      nth_rw 1[←h₁]; rw [inv_pow]
   rw [div_eq_inv_mul, mul_one, h₂]
   nth_rw 1[←h₁]
   let S1 := A₂ (x₂ (n+1) - x₂ n)
   let S2 := A₁ (x₁ n) + A₂ (x₂ n) - b
   let s1 := √τ
   have h1 : s1 ^2 * ‖S1‖^2 = ‖s1 • S1‖ ^2 := by rw [norm_smul, mul_pow]; simp only [Real.norm_eq_abs,sq_abs]
   have h2 : s1⁻¹ ^2 * ‖S2‖^2 = ‖s1⁻¹ • S2‖ ^2 := by rw [norm_smul, mul_pow]; simp only [inv_pow, norm_inv, Real.norm_eq_abs, sq_abs]
   have : s1 ≠ 0 := by
      have h₃ : s1 = √τ := by rfl
      rw [h₃]
      apply Real.sqrt_ne_zero'.mpr
      rcases admm.htau with ⟨h₁, _⟩
      assumption
   have h3 : inner (𝕜 := ℝ) S1 S2 = inner (𝕜 := ℝ) (s1 • S1) (s1⁻¹ • S2) := by rw [inner_smul_left, inner_smul_right]; rw [← mul_assoc]; simp; rw [mul_inv_cancel₀, one_mul]; exact this
   rw [h1, h2, h3]
   have : ‖s1 • S1‖ ^ 2 + ‖s1⁻¹ • S2‖ ^ 2 - -2 * ⟪s1 • S1, s1⁻¹ • S2⟫_ℝ = ‖s1 • S1‖ ^ 2 + 2 * ⟪s1 • S1, s1⁻¹ • S2⟫_ℝ + ‖s1⁻¹ • S2‖ ^ 2 := by ring_nf
   rw [this, ←norm_add_sq_real]
   apply pow_two_nonneg

lemma Φ_isdescending_inequ7 [Setting E₁ E₂ F admm admm_kkt](htau : 1 < τ ): ∀ n : ℕ+, 1 / (τ * ρ) * ‖ey n‖ ^ 2 + ρ * ‖A₂ (e₂ n)‖ ^ 2
      + (1 - 1 / τ) * ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖^2 -
      (1 / (τ * ρ) * ‖ey (n + 1)‖^ 2 + ρ * ‖A₂ (e₂ (n + 1))‖^2
      + (1 - 1 / τ) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖^2)
      ≥ (1 + 1 / τ - τ) * ρ * ‖A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b‖^2
      + (1 + τ - τ ^ 2) * ρ * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 := by
   intro n
   let x_diff := x₂ (n+1) - x₂ n
   let r_n := A₁ (x₁ n) + A₂ (x₂ n) - b; let r_n_1 := A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b
   let e_sum := A₁ (e₁ n) + A₂ (e₂ n); let e_sum_1 := A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))
   let a₁ := (1 / (τ * ρ)) * ‖ey n‖^2; let a₂ := (1 / (τ * ρ)) * ‖ey (n+1)‖^2
   let b₁ := ρ * ‖A₂ (e₂ n)‖^2; let b₂ := ρ * ‖A₂ (e₂ (n+1))‖^2
   let c₁ := (1 - (1 / τ)) * ρ * ‖e_sum‖^2; let c₂ := (1 - (1 / τ)) * ρ * ‖e_sum_1‖^2
   let d₁ := (1 + τ - τ^2) * ρ * ‖A₂ x_diff‖^2; let d₂ := (1 + 1 / τ - τ) * ρ * ‖r_n_1‖^2
   have M_inequ : 2 * (M (n+1)) ≤ (τ^2 - τ) * ρ * ‖A₂ x_diff‖ ^ 2 + (1 - 1 / τ) * ρ * ‖r_n‖ ^ 2 := by
      have h1: 2 * (M (n+1)) = (τ - 1) * ρ * (-2 * (inner (A₂ x_diff) (r_n))) := by
         calc
            _= 2 * (1 - τ) * ρ *  (inner (A₂ x_diff) (r_n)) := by
               dsimp [M,x_diff,r_n]
               have : (n + 1).natPred = n := rfl
               simp only [this]
               ring_nf
            _= (τ - 1) * ρ * (-2 * (inner (A₂ x_diff) (r_n))) := by ring
      rw [h1]
      have h2: (τ - 1) * ρ * (-2 * (inner (A₂ x_diff) (r_n))) ≤ (τ - 1) * ρ * (τ * ‖A₂ x_diff‖^2
         + 1 / τ * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) := by
         have iequ: -2 * (inner (A₂ x_diff) (r_n)) ≤ τ * ‖A₂ x_diff‖^2 + (1/τ) * ‖r_n‖^2 := by
            simp only [x_diff, r_n]; apply basic_inequ₂
         have cpos: (τ - 1) * ρ ≥ 0 := by
            apply mul_nonneg_iff.2
            left; constructor;
            · linarith
            · linarith [admm.hrho]
         apply mul_le_mul_of_nonneg_left iequ cpos
      have h3: (τ - 1) * ρ * (τ * ‖A₂ x_diff‖^2 + 1/τ * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) =
         (τ^2 - τ) * ρ * ‖A₂ x_diff‖ ^ 2 + (1 - 1/τ) * ρ * ‖r_n‖ ^ 2 := by
            rw [mul_add ((τ - 1) * ρ), ← mul_assoc, ← mul_assoc]
            rw [mul_comm (τ-1) ρ, mul_assoc ρ, mul_assoc ρ (τ - 1)]
            rw [sub_mul τ 1 τ, sub_mul τ 1 (1/τ), mul_comm ρ, mul_comm ρ]
            rw [pow_two τ, one_mul, mul_one_div_cancel (by linarith [htau]), one_mul]
      linarith [h1,h2,h3]
   have H: 1 / (τ * ρ) * (‖ey n‖^2 - ‖ey (n+1)‖^2)
      - (2 - τ) * ρ * ‖r_n_1‖^2 + (τ ^ 2 - τ) * ρ * ‖A₂ x_diff‖ ^ 2 + (1 - 1 / τ) * ρ * ‖r_n‖ ^ 2
      - ρ * ‖A₂ x_diff‖^2 - ρ * ‖A₂ (e₂ (n+1))‖^2 + ρ * ‖A₂ (e₂ n)‖^2
      ≥ 0 := by
         calc
         _ ≥ 1 / (τ * ρ) * (‖ey n‖^2 - ‖ey (n+1)‖^2) - (2 - τ) * ρ * ‖r_n_1‖^2
            + 2 * (M (n+1)) - ρ * ‖A₂ x_diff‖^2 - ρ * ‖A₂ (e₂ (n+1))‖^2 + ρ * ‖A₂ (e₂ n)‖^2 := by linarith
         _ ≥ 0 := by apply Φ_isdescending_inequ5
   have rw_rn_1 : r_n_1 = e_sum_1:= by apply Φ_isdescending_eq3
   have rw_rn : r_n = e_sum:= by apply Φ_isdescending_eq3'
   rw [rw_rn_1, rw_rn, mul_sub] at H
   have H_split : (2 - τ) * ρ * ‖e_sum_1‖^2 = (1 - (1 / τ)) * ρ * ‖e_sum_1‖^2 + (1 + (1 / τ) - τ) * ρ * ‖r_n_1‖^2 := by
      calc
         _ = (1 - (1 / τ)) * ρ * ‖e_sum_1‖^2 + (1 + (1 / τ) - τ) * ρ * ‖e_sum_1‖^2 := by ring
         _ = (1 - (1 / τ)) * ρ * ‖e_sum_1‖^2 + (1 + (1 / τ) - τ) * ρ * ‖r_n_1‖^2 := by rw [rw_rn_1]
   rw [H_split] at H
   have H_simp : a₁ - a₂ - (c₂ + d₂) + (τ^2 - τ) * ρ * ‖A₂ x_diff‖^2 + c₁ - ρ * ‖A₂ x_diff‖^2 - b₂ + b₁ ≥ 0 := by apply H
   have H_simp' : a₁ - a₂ - (c₂ + d₂) - (1 + τ - τ^2) * ρ * ‖A₂ x_diff‖^2 + c₁ - b₂ + b₁ ≥ 0 := by linarith [H_simp]
   have H_simp'' : a₁ - a₂ - (c₂ + d₂) - d₁ + c₁ - b₂ + b₁ ≥ 0 := by apply H_simp'
   have rel_simp : a₁ + b₁ + c₁ - (a₂ + b₂ + c₂) ≥ d₂ + d₁ := by linarith [H_simp']
   apply rel_simp

lemma τ_segment [Setting E₁ E₂ F admm admm_kkt] : (0 < τ ∧ τ ≤ 1) ∨ τ > 1 := by
   rcases admm.htau with ⟨h1, _⟩
   by_cases h: τ ≤ 1
   ·  left;exact ⟨h1, h⟩
   ·  right;linarith

lemma τ_min1_1 [Setting E₁ E₂ F admm admm_kkt] (h: 0 < τ ∧ τ ≤ 1) : min τ (1 + τ - τ ^ 2) = τ := by
   rcases h with ⟨h1, h2⟩
   apply min_eq_left
   have h3: τ ^ 2 ≤ 1 := by
      apply pow_le_one;linarith;linarith
   linarith

lemma τ_min1_2 [Setting E₁ E₂ F admm admm_kkt] (h: τ > 1 ) : min τ (1 + τ - τ ^ 2) = 1 + τ - τ ^ 2 := by
   apply min_eq_right
   have : 1 < τ ^ 2 := by
      apply one_lt_pow;exact h;linarith
   linarith

lemma τ_min2_1 [Setting E₁ E₂ F admm admm_kkt] (h: 0 < τ ∧ τ ≤ 1) : min 1 (1 + 1 / τ - τ ) = 1 := by
   rcases h with ⟨h1, h2⟩
   apply min_eq_left
   have h3: τ ≤ 1 / τ :=
   calc
      _ ≤ 1 := h2
      _ ≤ 1 / τ := by
         apply one_le_one_div h1 h2
   linarith

lemma τ_min2_2 [Setting E₁ E₂ F admm admm_kkt] (h: τ > 1 ) : min 1 (1 + 1 / τ - τ ) = 1 + 1 / τ - τ  := by
   apply min_eq_right
   have : τ > 1 / τ :=
   calc
      _ > 1 := h
      _ > 1 / τ := by
         rw [one_div, ← inv_one];apply inv_lt_inv_of_lt;linarith;exact h
   linarith

lemma τ_min3_1 [Setting E₁ E₂ F admm admm_kkt] (h: 0 < τ ∧ τ ≤ 1) : max (1 - τ) (1 - 1 / τ) = 1 - τ := by
   rcases h with ⟨h1, h2⟩
   apply max_eq_left
   have h3: τ ≤ 1 / τ :=
   calc
      _ ≤ 1 := h2
      _ ≤ 1 / τ := by
         apply one_le_one_div h1 h2
   linarith

lemma τ_min3_2 [Setting E₁ E₂ F admm admm_kkt] (h: τ > 1) : max (1 - τ) (1 - 1 / τ) = 1 - 1 / τ  := by
   apply max_eq_right
   have : τ > 1 / τ :=
   calc
      _ > 1 := h
      _ > 1 / τ := by
         rw [one_div, ← inv_one];apply inv_lt_inv_of_lt;linarith;exact h
   linarith

lemma Φ_isdescending [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+, (Φ n ) - (Φ (n + 1) ) ≥ (min τ (1 + τ - τ ^ 2) )* ρ
      * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2 + (min 1 (1 + 1 / τ - τ )) * ρ *
      ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2 :=by
   intro n
   rcases τ_segment with h | h
   ·  rw[τ_min1_1 h,τ_min2_1 h];simp only [Φ,Ψ];rw[τ_min3_1 h];
      have := Φ_isdescending_inequ6 h n
      rw[add_comm (ρ * ‖A₁ (x₁ (↑n + 1)) + A₂ (x₂ (↑n + 1)) - b‖ ^ 2)
      (τ * ρ * ‖A₂ (x₂ (↑n + 1 ) - x₂ ↑n )‖ ^ 2),Φ_isdescending_eq3 n,norm_comm] at this;
      rwa[one_mul]
   ·  rw[τ_min1_2 h,τ_min2_2 h];simp only [Φ,Ψ];rw[τ_min3_2 h];
      have := Φ_isdescending_inequ7 h n
      rw[add_comm ((1 + 1 / τ - τ) * ρ * ‖A₁ (x₁ (↑n + 1)) + A₂ (x₂ (↑n + 1)) - b‖ ^ 2)
      ((1 + τ  - τ  ^ 2) * ρ * ‖A₂ (x₂ (↑n + 1) - x₂ ↑n)‖ ^ 2),Φ_isdescending_eq3 n,norm_comm]
      at this;exact this

end ADMM_Converge_Proof
