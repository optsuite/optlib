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

lemma diff_from_l2 (h : Differentiable ℝ H) : Differentiable ℝ (fun z : E × F ↦ H z) := by
  apply Differentiable.comp h
  apply IsBoundedLinearMap.differentiable
  exact instIsBoundedLinearMapL2equiv

theorem diff_prod₁ (h : Differentiable ℝ H) (y : F) :
    Differentiable ℝ (fun x : E ↦ H (x, y)) := by
  apply Differentiable.comp (diff_from_l2 h)
  exact Differentiable.prodMk differentiable_id (differentiable_const y)

theorem diff_prod₂ (h : Differentiable ℝ H) (x : E) :
    Differentiable ℝ (fun y : F ↦ H (x, y)) := by
  apply Differentiable.comp (diff_from_l2 h)
  exact Differentiable.prodMk (differentiable_const x) differentiable_id

end diff

noncomputable section prod_grad

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {H : WithLp 2 (E × F) → ℝ} {x : E} {y : F} {z : WithLp 2 (E × F)} {l : NNReal}

open Set Bornology Filter BigOperators Topology

/- The gradient of the first component -/
def grad_fst (H : WithLp 2 (E × F) → ℝ) (y : F) : E → E :=
  fun x : E ↦ (gradient H (WithLp.toLp 2 (x, y))).fst

/- The gradient function of the second component -/
def grad_fun_fst (H : WithLp 2 (E × F) → ℝ) := fun z : WithLp 2 (E × F) ↦ grad_fst H z.snd z.fst

/- The gradient of the second component -/
def grad_snd (H : WithLp 2 (E × F) → ℝ) (x : E) : F → F :=
  fun y : F ↦ (gradient H (WithLp.toLp 2 (x, y))).snd

/- The gradient function of the second component -/
def grad_fun_snd (H : WithLp 2 (E × F) → ℝ) := fun z : WithLp 2 (E × F) ↦ grad_snd H z.fst z.snd

/- The gradient of the prod domain -/
def grad_comp (H : WithLp 2 (E × F) → ℝ) (z : WithLp 2 (E × F)) : WithLp 2 (E × F) :=
    WithLp.toLp 2 (grad_fst H z.snd z.fst, grad_snd H z.fst z.snd)

/- The gradient function of the prod domain -/
def grad_fun_comp (H : WithLp 2 (E × F) → ℝ) := fun z ↦ (grad_comp H z)

theorem grad_fst_eq (_h : Differentiable ℝ H) (z : WithLp 2 (E × F)) :
    (gradient H z).fst = grad_fst H z.snd z.fst := by
  cases z
  simp [grad_fst]

theorem grad_snd_eq (_h : Differentiable ℝ H) (z : WithLp 2 (E × F)) :
    (gradient H z).snd = grad_snd H z.fst z.snd := by
  cases z
  simp [grad_snd]

theorem grad_eq_block_grad (_h : Differentiable ℝ H) : gradient H = grad_fun_comp H := by
  funext z
  cases z with
  | toLp p =>
      dsimp [grad_fun_comp, grad_comp, grad_fst, grad_snd]
      cases h : gradient H (WithLp.toLp 2 p)
      rfl

theorem lip_grad_fst_of_lip (_h : Differentiable ℝ H) (hl : LipschitzWith l (gradient H)) :
    LipschitzWith l (fun (z : WithLp 2 (E × F)) ↦ grad_fst H z.snd z.fst) := by
  rw [lipschitzWith_iff_norm_sub_le] at hl ⊢
  intro z z'
  calc
    ‖grad_fst H z.snd z.fst - grad_fst H z'.snd z'.fst‖ =
      ‖(gradient H z).fst - (gradient H z').fst‖ := by
        cases z
        cases z'
        simp [grad_fst]
    _ = ‖(gradient H z - gradient H z').fst‖ := by simp
    _ ≤ ‖(gradient H z - gradient H z')‖ := fst_norm_le_prod_L2 _
    _ ≤ _ := hl z z'

theorem lip_grad_snd_of_lip (_h : Differentiable ℝ H) (hl : LipschitzWith l (gradient H)) :
    LipschitzWith l (fun (z : WithLp 2 (E × F)) ↦ grad_snd H z.fst z.snd) := by
  rw [lipschitzWith_iff_norm_sub_le] at hl ⊢
  intro z z'
  calc
    ‖grad_snd H z.fst z.snd - grad_snd H z'.fst z'.snd‖ =
      ‖(gradient H z).snd - (gradient H z').snd‖ := by
        cases z
        cases z'
        simp [grad_snd]
    _ = ‖(gradient H z - gradient H z').snd‖ := by simp
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
    intro z r
    let x := z.fst
    let y := z.snd
    have hprod : IsCompact (Metric.closedBall x r ×ˢ Metric.closedBall y r) :=
      (isCompact_closedBall x r).prod (isCompact_closedBall y r)
    have himage : IsCompact (WithLp.toLp 2 '' (Metric.closedBall x r ×ˢ Metric.closedBall y r)) :=
      hprod.image (WithLp.prod_continuous_toLp (p := 2) (α := E) (β := F))
    refine IsCompact.of_isClosed_subset himage Metric.isClosed_closedBall ?_
    intro w hw
    have hnorm : ‖w - z‖ ≤ r := by simpa [dist_eq_norm] using hw
    have hw1 : ‖w.fst - x‖ ≤ r := by
      simpa [x] using (le_trans (fst_norm_le_prod_L2 (w - z)) hnorm)
    have hw2 : ‖w.snd - y‖ ≤ r := by
      simpa [y] using (le_trans (snd_norm_le_prod_L2 (w - z)) hnorm)
    refine ⟨(w.fst, w.snd), ?_, by cases w; rfl⟩
    exact ⟨mem_closedBall_iff_norm.mpr hw1, mem_closedBall_iff_norm.mpr hw2⟩

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
def BCD.ψ {_ : BCD f g H l x0 y0} := fun z : WithLp 2 (E × F) ↦ f z.fst + g z.snd + H z

variable {alg : BCD f g H l x0 y0}

omit [ProperSpace E] [ProperSpace F] in
lemma BCD.Hdiff {self : BCD f g H l x0 y0} : Differentiable ℝ H :=
    self.conf.differentiable (by simp)

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
