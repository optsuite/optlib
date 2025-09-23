/-
Copyright (c) 2024 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Convex.Deriv
import Optlib.Function.KL
import Optlib.Function.Proximal
import Optlib.Differential.Subdifferential
import Mathlib.Topology.EMetricSpace.Lipschitz


/-!
# Block Coordinate Descent

## Main results

This file mainly concentrates on the scheme of the block coordinate descent method.

- We give the definition of gradient on prod space.
- We define the problem type of BCD method and the update scheme of BCD method.
- We prove the Lipschitz continuity of the gradient of the coordinates.

-/

section diff

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {H : WithLp 2 (E × F) → ℝ}

lemma diff_from_l2 (h : Differentiable ℝ H) : @Differentiable ℝ _ (E × F) _ _ _ ℝ _ _ _ H := by
  apply Differentiable.comp h
  apply IsBoundedLinearMap.differentiable
  exact instIsBoundedLinearMapL2equiv

theorem diff_prod₁ (h : Differentiable ℝ H) (y : F) :
    Differentiable ℝ (fun x ↦ H (x, y)) := by
  apply Differentiable.comp (diff_from_l2 h)
  exact Differentiable.prodMk differentiable_fun_id (differentiable_const y)

theorem diff_prod₂ (h : Differentiable ℝ H) (x : E) :
    Differentiable ℝ (fun y ↦ H (x, y)) := by
  apply Differentiable.comp (diff_from_l2 h)
  exact Differentiable.prodMk (differentiable_const x) differentiable_fun_id

end diff

noncomputable section prod_grad

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {H : WithLp 2 (E × F) → ℝ} {x : E} {y : F} {z : WithLp 2 (E × F)} {l : NNReal}

open Set Bornology Filter BigOperators Topology

/- The gradient of the first component -/
def grad_fst (H : WithLp 2 (E × F) → ℝ) (y : F) : E → E := gradient (fun t ↦ H (t, y))

/- The gradient function of the second component -/
def grad_fun_fst (H : WithLp 2 (E × F) → ℝ) := fun (x, y) ↦ (grad_fst H y x)

/- The gradient of the second component -/
def grad_snd (H : WithLp 2 (E × F) → ℝ) (x : E) : F → F := gradient (fun t ↦ H (x, t))

/- The gradient function of the second component -/
def grad_fun_snd (H : WithLp 2 (E × F) → ℝ) := fun (x, y) ↦ (grad_snd H x y)

/- The gradient of the prod domain -/
def grad_comp (H : WithLp 2 (E × F) → ℝ) (z : WithLp 2 (E × F)) : WithLp 2 (E × F) :=
    (WithLp.equiv 2 (E × F)).symm (grad_fst H z.2 z.1, grad_snd H z.1 z.2)

/- The gradient function of the prod domain -/
def grad_fun_comp (H : WithLp 2 (E × F) → ℝ) := fun z ↦ (grad_comp H z)

theorem grad_fst_eq (h : Differentiable ℝ H) (z : WithLp 2 (E × F)) :
    (gradient H z).1 = grad_fst H z.2 z.1 := by
  have h₁ : HasGradientAt (fun x ↦ H (x, z.2)) (grad_fst H z.2 z.1) z.1 := by
    apply DifferentiableAt.hasGradientAt
    apply diff_prod₁ h
  have h₂ : HasGradientAt (fun x ↦ H (x, z.2)) (gradient H z).1 z.1 := by
    have h₃ : HasGradientAt H (gradient H z) z := DifferentiableAt.hasGradientAt (h z)
    rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h₃ ⊢
    intro c hc
    specialize h₃ hc
    obtain h₃' := Filter.Eventually.curry_nhds h₃
    rw [Filter.eventually_iff_exists_mem] at h₃' ⊢
    rcases h₃' with ⟨v, ⟨hv1, hv2⟩⟩
    use v
    constructor
    · exact hv1
    · intro y yv
      specialize hv2 y yv
      obtain hv2' := Filter.Eventually.self_of_nhds hv2
      have : z = (z.1, z.2) := rfl
      rw [this] at hv2'
      rw [Prod.mk_sub_mk y z.1 z.2 z.2] at hv2'
      simp at hv2'
      rw [norm_prod_right_zero] at hv2'
      exact hv2'
  exact HasGradientAt.unique h₂ h₁

theorem grad_snd_eq (h : Differentiable ℝ H) (z : WithLp 2 (E × F)) :
    (gradient H z).2 = grad_snd H z.1 z.2 := by
  have h₁ : HasGradientAt (fun y ↦ H (z.1, y)) (grad_snd H z.1 z.2) z.2 := by
    apply DifferentiableAt.hasGradientAt
    apply diff_prod₂ h
  have h₂ : HasGradientAt (fun y ↦ H (z.1, y)) (gradient H z).2 z.2 := by
    have h₃ : HasGradientAt H (gradient H z) z := DifferentiableAt.hasGradientAt (h z)
    rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h₃ ⊢
    intro c hc
    specialize h₃ hc
    obtain h₃' := Filter.Eventually.curry_nhds h₃
    obtain h₃'' := Filter.Eventually.self_of_nhds h₃'
    rw [Filter.eventually_iff_exists_mem] at h₃'' ⊢
    rcases h₃'' with ⟨v, ⟨hv1, hv2⟩⟩
    use v
    constructor
    · exact hv1
    · intro y yv
      specialize hv2 y yv
      have : z = (z.1, z.2) := rfl
      nth_rw 5 [this] at hv2
      simp at hv2
      nth_rw 6 [this] at hv2
      rw [Prod.mk_sub_mk z.1 z.1 y z.2] at hv2
      simp at hv2
      rw [norm_prod_left_zero] at hv2
      exact hv2
  exact HasGradientAt.unique h₂ h₁

theorem grad_eq_block_grad (h : Differentiable ℝ H) : gradient H = grad_fun_comp H := by
  ext z
  calc
    gradient H z = ((gradient H z).1, (gradient H z).2) := rfl
    _ = (grad_fst H z.2 z.1, grad_snd H z.1 z.2) := by rw [← grad_fst_eq h, ← grad_snd_eq h]
    _ = grad_fun_comp H z := rfl

theorem lip_grad_fst_of_lip (h : Differentiable ℝ H) (hl : LipschitzWith l (gradient H)) :
    LipschitzWith l (fun (z : WithLp 2 (E × F)) ↦ grad_fst H z.2 z.1) := by
  rw [lipschitzWith_iff_norm_sub_le] at *
  intro z z'
  calc
    _ = ‖(gradient H z).1 - (gradient H z').1‖ := by rw [grad_fst_eq h, grad_fst_eq h]
    _ = ‖(gradient H z - gradient H z').1‖ := rfl
    _ ≤ ‖(gradient H z - gradient H z')‖ := fst_norm_le_prod_L2 _
    _ ≤ _ := hl z z'

theorem lip_grad_snd_of_lip (h : Differentiable ℝ H) (hl : LipschitzWith l (gradient H)) :
    LipschitzWith l (fun (z : WithLp 2 (E × F)) ↦ grad_snd H z.1 z.2) := by
  rw [lipschitzWith_iff_norm_sub_le] at *
  intro z z'
  calc
    _ = ‖(gradient H z).2 - (gradient H z').2‖ := by rw [grad_snd_eq h, grad_snd_eq h]
    _ = ‖(gradient H z - gradient H z').2‖ := rfl
    _ ≤ ‖(gradient H z - gradient H z')‖ := snd_norm_le_prod_L2 _
    _ ≤ _ := hl z z'

end prod_grad

noncomputable section algorithm

open Set Bornology Filter BigOperators Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [ProperSpace F]
variable {f : E → ℝ} {g : F → ℝ}
variable {H : (WithLp 2 (E × F)) → ℝ} {x0 : E} {y0 : F} {l : NNReal}

instance Proper_Prod : ProperSpace (WithLp 2 (E × F)) where
  isCompact_closedBall := by
    rintro ⟨x, y⟩ r
    obtain h := IsCompact.prod (isCompact_closedBall x r) (isCompact_closedBall y r)
    have {a b : ℝ} : a ≤ √(a ^ 2 + b ^ 2) := by apply Real.le_sqrt_of_sq_le; linarith [sq_nonneg b]
    have hsub : @Metric.closedBall (WithLp 2 (E × F)) _ ⟨x, y⟩ r
        ⊆ Metric.closedBall x r ×ˢ Metric.closedBall y r := by
      rintro ⟨x', y'⟩ hball
      rw [mem_prod]
      simp only [mem_closedBall_iff_norm, WithLp.prod_norm_eq_of_L2] at *
      constructor
      · exact le_trans this hball
      · exact le_trans this ((add_comm (‖x' - x‖ ^ 2) _) ▸ hball)
    apply IsCompact.of_isClosed_subset h (@Metric.isClosed_closedBall (WithLp 2 (E × F)) _ _ _) hsub

/--
  Assumption: f and g are lower semicontinuous, H is continuously differentiable
  ∇ H is l- Lipschitz continuous, f and g are lower bounded
-/
class ProblemData (f : E → ℝ) (g : F → ℝ) (H : (WithLp 2 (E × F)) → ℝ) (l : NNReal) : Prop where
  lbdf : BddBelow (f '' univ)
  lbdg : BddBelow (g '' univ)
  hf : LowerSemicontinuous f
  hg : LowerSemicontinuous g
  conf : ContDiff ℝ 1 H
  lpos : l > (0 : ℝ)
  lip : LipschitzWith l (gradient H)

/--
  The definition of block coordinate descent
-/
structure BCD (f : E → ℝ) (g : F → ℝ) (H : (WithLp 2 (E × F)) → ℝ) (l : NNReal)
    (x0 : E) (y0 : F) extends ProblemData f g H l where
  x : ℕ → E
  y : ℕ → F
  x0 : x 0 = x0
  y0 : y 0 = y0
  c : ℕ → ℝ
  d : ℕ → ℝ
  s₁ : ∀ k, prox_prop (c k • f) (x k - c k • (grad_fst H (y k) (x k))) (x (k + 1))
  s₂ : ∀ k, prox_prop (d k • g) (y k - d k • (grad_snd H (x (k + 1)) (y k))) (y (k + 1))

open BCD

/- the notation z in BCD -/
def BCD.z {self : BCD f g H l x0 y0} : ℕ → WithLp 2 (E × F) :=
  fun n ↦ (WithLp.equiv 2 (E × F)).symm (self.x n, self.y n)

/- the notation ψ in BCD -/
def BCD.ψ {_ : BCD f g H l x0 y0} := fun z : WithLp 2 (E × F) ↦ f z.1 + g z.2 + H z

variable {alg : BCD f g H l x0 y0}

omit [ProperSpace E] [ProperSpace F] in
lemma BCD.Hdiff {self : BCD f g H l x0 y0} : Differentiable ℝ H :=
    self.conf.differentiable (Preorder.le_refl 1)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
  [InnerProductSpace ℝ F] [CompleteSpace F] [ProperSpace F] in
lemma comp_norm_le (x : E) (y : F) : (‖x‖ ≤ ‖(x,y)‖) ∧ (‖y‖ ≤ ‖(x,y)‖) :=
  ⟨le_max_left ‖x‖ ‖y‖, le_max_right ‖x‖ ‖y‖⟩

omit [ProperSpace E] [ProperSpace F] in
lemma BCD.cpos (γ : ℝ) (hγ : γ > 1) (ck: ∀ k, alg.c k = 1 / (γ * l)): ∀ k, 0 < (alg.c k) := by
  intro k
  specialize ck k; rw [ck]
  apply div_pos; norm_num
  apply mul_pos; linarith[hγ]; apply alg.lpos

omit [ProperSpace E] [ProperSpace F] in
lemma BCD.dpos (γ : ℝ) (hγ : γ > 1) (dk: ∀ k, alg.d k = 1 / (γ * l)): ∀ k, 0 < (alg.d k) := by
  intro k
  specialize dk k; rw [dk]
  apply div_pos; norm_num
  apply mul_pos; linarith[hγ]; apply alg.lpos

omit [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
  [InnerProductSpace ℝ F] [CompleteSpace F] [ProperSpace F] in
private lemma sub_prod (x x1 : E) (y y1 : F) :
  ((x, y) : WithLp 2 (E × F)) - (x1, y1) = (x - x1, y - y1) := rfl

/- Define the A^k_x -/
def BCD.A_kx k := (alg.c k)⁻¹ • (alg.x k - alg.x (k + 1)) - (grad_fst H (alg.y k) (alg.x k))

/- Define the A^k_y -/
def BCD.A_ky k := (alg.d k)⁻¹ • (alg.y k - alg.y (k + 1)) - (grad_snd H (alg.x (k + 1)) (alg.y k))

/- Define the A^k = (A^k_x, A^k_y) -/
def BCD.A_k (k : ℕ) : WithLp 2 (E × F) := (alg.A_kx k, alg.A_ky k)

/- Define the gradient of A^k -/
def BCD.subdiff k := alg.A_k k + gradient H (alg.x (k + 1), alg.y (k + 1))

end algorithm

section Assumption

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → ℝ} {g : F → ℝ}
variable {H : (WithLp 2 (E × F)) → ℝ} {x0 : E} {y0 : F} {l : NNReal}

theorem BCD.lip₁ {self : BCD f g H l x0 y0} : LipschitzWith l (grad_fun_comp H) := by
  obtain lip := self.lip
  rwa [grad_eq_block_grad self.Hdiff] at lip

/- coordinate Lipschitz continuous -/
theorem BCD.coordinate_lip {self : BCD f g H l x0 y0} : (∀ y, LipschitzWith l (grad_fst H y))
    ∧ (∀ x, LipschitzWith l (grad_snd H x)) := by
  have h : LipschitzWith l (grad_fun_comp H) := self.lip₁
  rw [lipschitzWith_iff_norm_sub_le] at h
  constructor
  · intro y
    rw [lipschitzWith_iff_norm_sub_le]
    intro x1 x2
    obtain h := h (x1, y) (x2, y); simp [grad_fun_comp, grad_comp] at h
    apply le_trans (fst_norm_le_prod_L2 _) at h
    simp at h; rwa [sub_prod, sub_self, norm_prod_right_zero] at h;
  intro x
  rw [lipschitzWith_iff_norm_sub_le]
  intro y1 y2; obtain h := h (x, y1) (x, y2)
  simp [grad_fun_comp,grad_comp] at h
  apply le_trans (snd_norm_le_prod_L2 _) at h
  simp at h; rwa [sub_prod, sub_self, norm_prod_left_zero] at h;

end Assumption
