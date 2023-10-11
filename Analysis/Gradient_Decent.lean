/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang
-/
import Analysis.Lsmooth
import Analysis.First_Order
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
/-!
  the convergence of the gradient method for the convex function
-/
noncomputable section
variable {n : Type _}[Fintype n]

section
open InnerProductSpace
variable {f: (EuclideanSpace ℝ n) → ℝ} {f' :((EuclideanSpace ℝ n)) → ((EuclideanSpace ℝ n) →L[ℝ] ℝ)}
variable {l a: ℝ} {xm x₀: EuclideanSpace ℝ n} {point : ℕ → EuclideanSpace ℝ n}

lemma convex_function (h₁ : ∀ x₁ :EuclideanSpace ℝ n, HasFDerivAt f (f' x₁) x₁)
(hfun: ConvexOn ℝ Set.univ f): ∀ (x y : EuclideanSpace ℝ n), f x ≤ f y + f' x (x - y) := by
  intro x y
  have : f x + f' x (y - x) ≤ f y := by
    apply first_order_condition (h₁ x) hfun (by trivial) y (by trivial)
  calc  f x = f x + f' x (y - x) - f' x (y - x) := by simp
          _ ≤ f y - f' x (y - x)  := by exact sub_le_sub_right this ((f' x) (y - x))
          _ = f y + f' x (x - y)  := by simp; ring_nf

lemma convex_lipschitz (h₁ : ∀ x₁ : EuclideanSpace ℝ n, HasFDerivAt f (f' x₁) x₁)
(h₂ : l > 0) (step₁: l ≤ (1 / a)) (step₂ : a > 0)
(h₃ : ∀ x y : EuclideanSpace ℝ n, ‖f' x - f' y‖ ≤ l * ‖x - y‖):
∀ x : EuclideanSpace ℝ n, f (x - a • (grad) (f' x)) ≤ f x - a / 2 * ‖ grad (f' x)‖ ^ 2 := by
  intro x
  have t2 : (f' x) (grad (f' x))= ‖(grad) (f' x)‖ ^2 := by
    rw [← grad_equiv x (grad (f' x)), inner_self_eq_norm_sq_to_K (grad (f' x))]; simp
  calc
    f ((x- a • (grad) (f' x)))
      ≤ f x + f' x (x- a • (grad) (f' x)- x) + l / 2 * ‖x- a • (grad) (f' x)- x‖ ^ 2 := by
        exact lipschitz_continuos_upper_bound h₁ h₃ x (x- a • (grad) (f' x))
    _ = f x + ((l/2 * a*a -a)* ‖(grad) (f' x)‖ ^2) := by
      simp;ring_nf;simp;rw [t2,norm_smul _ _];simp;rw [abs_of_pos step₂];ring_nf
    _ ≤ f x + (- a/2* ‖(grad) (f' x)‖ ^2) := by
      simp only [Real.rpow_two, add_le_add_iff_left, gt_iff_lt, norm_pos_iff, ne_eq]
      apply mul_le_mul_of_nonneg_right
      · simp;
        calc l / 2 * a * a = (l * a) * (a / 2) := by ring_nf
              _  ≤ 1 * (a / 2) := by
                apply mul_le_mul_of_le_of_le _ (by linarith) _ (by linarith)
                · exact (le_div_iff step₂).mp step₁
                · linarith [mul_pos h₂ step₂]
              _  = -a / 2 + a := by ring_nf
      · exact sq_nonneg ‖grad (f' x)‖
    _ = f x - a/2* ‖(grad) (f' x)‖ ^2 := by ring_nf

lemma point_descent_for_convex (h₁ : ∀ x₁ :EuclideanSpace ℝ n, HasFDerivAt f (f' x₁) x₁)
(hfun: ConvexOn ℝ Set.univ f)(h₂: l>0)
(h₃ : ∀ x y : EuclideanSpace ℝ n, ‖f' x - f' y‖ ≤ l *‖x - y‖)(step₁: l ≤ (1/a))(step₂ : a >0)
(update: ∀ (k:ℕ), point (k+1) = point (k) -a •(grad) (f' (point (k)))):
∀ k: ℕ , f (point (k+1)) ≤ f (xm)+1/((2:ℝ)*a)*(‖point (k)-xm‖^2-‖point (k+1)-xm‖^2):= by
  intro k
  have descent: ∀ x : EuclideanSpace ℝ n, f ((x- a • (grad) (f' x))) ≤ f (xm)+1/((2:ℝ)*a)*(‖x-xm‖^2-‖x-a • (grad) (f' x)-xm‖^2):= by
    intro x
    have tt : 1/((2:ℝ)*a)*((2:ℝ)*a)=1 := by
        simp;ring_nf;exact mul_inv_cancel (by linarith)
    have t4 :  f' (x) (x-xm) - a/2* ‖(grad) (f' x)‖^2=1/((2:ℝ)*a)*(‖x-xm‖^2-‖x-a • (grad) (f' x)-xm‖^2) := by
      symm
      have t4₁ :‖x-a • (grad) (f' x)-xm‖ ^ 2=‖x-xm‖ ^ 2-((2:ℝ)*a) * inner ((grad) (f' x)) (x-xm)+‖a • (grad) (f' x)‖^2 := by
        rw [sub_right_comm]
        simp [norm_sub_sq_real (x - xm) (a • grad (f' x))]
        ring_nf;rw [Finset.mul_sum];congr;ext;ring_nf
      calc 1/((2:ℝ)*a)*(‖x-xm‖ ^ 2-‖x-a • (grad) (f' x)-xm‖^2) = 1/(2*a)*(‖x-xm‖^2-‖x-xm‖ ^2+(2*a) * inner ((grad) (f' x)) (x-xm)-‖a • (grad) (f' x)‖^2) := by rw [t4₁];ring_nf
                       _ = 1/((2:ℝ)*a)*((2:ℝ)*a)*(f' (x) (x-xm))+1/((2:ℝ)*a)*(-‖a • (grad) (f' x)‖^2) := by rw [sub_self,zero_add,grad_equiv x (x-xm)];ring_nf
                       _ = f' (x) (x-xm)+1/((2:ℝ)*a)*(-‖a • (grad) (f' x)‖^2) := by rw [tt,one_mul]
                       _ = f' (x) (x-xm)-1/((2:ℝ)*a)*(a*a)*( ‖(grad) (f' x)‖^2 ) := by rw [norm_smul _ _,];simp;rw [abs_of_pos step₂];ring_nf;
                       _ = f' (x) (x-xm) - a/(2:ℝ)* ‖(grad) (f' x)‖^2 := by ring_nf;simp;left;rw [pow_two,mul_self_mul_inv a]
    calc f (x- a • (grad) (f' x)) ≤ f (x) - a/2* ‖(grad) (f' x)‖^2 := by exact convex_lipschitz h₁ h₂ step₁ step₂ h₃ x
                         _   ≤ f (xm) + f' (x) (x-xm) - a/2* ‖(grad) (f' x)‖^2:= by linarith [convex_function h₁ hfun x xm]
                         _   = f (xm)+1/((2:ℝ)*a)*(‖x-xm‖^2-‖x-a•(grad) (f' x)-xm‖^2) := by rw [add_sub_assoc  (f (xm))  (f' (x) (x-xm)) (a/2* ‖(grad) (f' x)‖^2),t4]
  specialize descent (point (k))
  rw [update k]
  exact descent

lemma mono_sum_prop_primal (mono : ∀ k: ℕ, f (point (k+1)) ≤ f (point (k))):
∀ n :ℕ , (Finset.range (n+1)).sum (fun (k : ℕ) ↦ f (point (k+1))) ≥ (n+(1:ℝ))*(f (point (n+2))) := by
  intros n
  induction' n with q IH1
  · simp;apply mono 1
  · have jtt : 0 ≤ ↑q+(2:ℝ) := by exact add_nonneg (Nat.cast_nonneg q) zero_le_two
    specialize mono (q+2)
    calc (Finset.range (q.succ+1)).sum (fun (k : ℕ) ↦ f (point (k+1)))= (Finset.range (q+1)).sum (fun (k : ℕ)↦ f (point (k+1)))+f (point (q+2))
            := by rw [Finset.sum_range_succ (fun (k : ℕ) ↦ f (point (k+1))) q.succ]
      _ ≥  (q+(1:ℝ))*(f (point (q+2)))+f (point (q+2)) := by linarith
      _ = (q+2)*(f (point (q+2))) := by ring_nf
      _ ≥ (q+2)*(f (point (q+3))) := by simp;exact mul_le_mul_of_nonneg_left mono jtt
      _ = (↑(q.succ) + 1) * f (point (q.succ+2)) := by simp;left;ring_nf


lemma mono_sum_prop_primal' (mono : ∀ k: ℕ, f (point (k+1)) ≤ f (point (k))):
∀ j : ℕ, (Finset.range (j.succ+1)).sum (fun (k : ℕ)↦ f (point (k+1)))/(j.succ+1) ≥ f (point (j+2)):= by
  intros j
  have jneq : ↑j+(1:ℝ)+(1:ℝ) ≠0 := by
    rw [add_assoc, one_add_one_eq_two]
    apply ne_of_gt
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_two
  have thh :↑j+(1:ℝ)+(1:ℝ)≥ 0 := by
    rw [add_assoc, one_add_one_eq_two]
    exact add_nonneg (Nat.cast_nonneg j) (by norm_num)
  have t5:(↑j + 1) * f (point (j.succ + 1)) / (↑j + 1 + 1) ≤(Finset.range j.succ).sum (fun (k : ℕ)↦ f (point (k + 1))) / (↑j + 1 + 1):= by
    have t6:  (↑j+1) * f (point (j.succ +1))≤ (Finset.range (j.succ )).sum (fun (k : ℕ)↦ f (point (k + 1))) := by exact mono_sum_prop_primal mono (j.succ-1)
    exact div_le_div_of_le thh t6
  calc (Finset.range (j.succ+1)).sum (fun (k : ℕ) ↦ f (point (k+1)))/(j.succ+1) = ((Finset.range (j.succ)).sum (fun (k : ℕ)↦ f (point (k+1)))+f (point (j.succ+1)))/(j.succ+1)
        := by rw [Finset.sum_range_succ (fun (k : ℕ)↦ f (point (k+1))) j.succ]
    _ = ((Finset.range (j.succ)).sum (fun (k : ℕ)↦ f (point (k+1))))/(j.succ+1)+f (point (j.succ+1))/(j.succ+1) := by rw [add_div]
    _ ≥ (j.succ)*f (point (j.succ+1))/(j.succ+1)+f (point (j.succ+1))/(j.succ+1) := by simp;exact t5
    _ = f (point (j+2))*(j.succ+1)/(j.succ+1) := by
      rw [← add_div];simp;rw [Nat.succ_eq_add_one j, add_assoc j 1 1, one_add_one_eq_two]
      field_simp [jneq];ring_nf
    _ = f (point (j+2))*((j.succ+1)/(j.succ+1)) := by ring_nf
    _ = f (point (j+2)) := by simp; rw [div_self jneq]; ring_nf


lemma mono_sum_prop (mono : ∀ k: ℕ, f (point (k+1)) ≤ f (point (k))):
∀ n : ℕ ,  (f (point (n+1))-f (xm)) ≤ (Finset.range (n+1)).sum (fun (k : ℕ)↦ f (point (k+1))-f (xm))/(n+1):= by
  intro n
  induction' n with j _
  · simp
  · simp
    have hs: ↑j+(2:ℝ) ≠ 0:= by
      apply ne_of_gt
      exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_two
    have h11 : f (xm)*(1:ℝ)=f (xm)*((↑j+2)/(↑j+2)) := by
      have n1: (↑j+(2:ℝ))/(↑j+(2:ℝ))=(1:ℝ):= by rw [div_self hs]
      have n2: (1:ℝ)=(↑j+2)/(↑j+2)  ∨ f (xm) = 0 := by simp [n1]
      exact mul_eq_mul_left_iff.mpr n2
    calc f (point (j+2)) ≤ (Finset.range (j.succ+1)).sum (fun (k : ℕ) ↦ f (point (k+1)))/(j.succ+1) := by linarith [mono_sum_prop_primal' mono j]
      _ = (Finset.range (j.succ+1)).sum (fun (k : ℕ) ↦ f (point (k+1)))/(j+2) - f (xm)*1+ f (xm) := by
        rw [Nat.succ_eq_add_one j];simp
        ring_nf;rw [add_assoc,one_add_one_eq_two]
      _ = (Finset.range (j.succ+1)).sum (fun (k : ℕ) ↦ f (point (k+1)))/(j+2) - f (xm)*((↑j+2)/(↑j+2))+ f (xm) := by rw [h11]
      _ = ((Finset.range (j.succ+1)).sum (fun (k : ℕ)↦ f (point (k+1)))-(j+1+1) * f (xm))/(j+1+1)+ f (xm) := by
        simp;rw [← one_add_one_eq_two,← add_assoc,mul_div,mul_comm,← sub_div]


lemma gradient_method (h₁ : ∀ x₁ :EuclideanSpace ℝ n, HasFDerivAt f (f' x₁) x₁)
(hfun: ConvexOn ℝ Set.univ f)(h₂: l>0)
(h₃ : ∀ x y : EuclideanSpace ℝ n, ‖f' x - f' y‖ ≤ l *‖x - y‖)(step₁: l ≤ (1/a))(step₂ : a >0)
(initial : point (0)= x₀)
(update: ∀ (k:ℕ), point (k+1) = point (k) -a •(grad) (f' (point (k)))):
∀ k:ℕ  , f (point (k+1)) - f (xm) ≤ 1/(2*(k+1)*a)*‖x₀ - xm‖^2 := by
  intro k
  have tα : (a / 2) ≥  0:= by linarith
  have tα1 : 1/((2:ℝ)*(k+1)*a) >0 := by
    have t₀ : (2:ℝ)*(k+1)*a >0:= by
      have t₀₁ : (2:ℝ)*(k+1)>0 := by
        simp
        exact Nat.cast_add_one_pos k
      exact mul_pos t₀₁ step₂
    exact one_div_pos.mpr t₀
  have pointdescent : ∀ k: ℕ , f (point (k+1)) ≤ f (xm)+1/((2:ℝ)*a)*(‖point (k)-xm‖^2-‖point (k+1)-xm‖^2):= by
    exact point_descent_for_convex h₁ hfun h₂ h₃ step₁ step₂ update
  have mono : ∀ k: ℕ, f (point (k+1)) ≤ f (point (k)) := by
    intro k
    rw [update k]
    calc f (point k - a •(grad) (f' (point (k)))) ≤ f (point k) - a / 2 * ‖(grad) (f' (point (k)))‖ ^ 2 := by exact convex_lipschitz h₁ h₂ step₁ step₂ h₃ (point (k))
                            _ ≤ f (point k) := by
                              simp
                              apply mul_nonneg tα _
                              · exact sq_nonneg ‖grad (f' (point k))‖
  have sum_prop : ∀ n : ℕ ,  (Finset.range (n+1)).sum (fun (k : ℕ) ↦ f (point (k+1))-f (xm)) ≤ 1/(2*a)*(‖x₀-xm‖^2-‖point (n+1)-xm‖^2):= by
    intro n
    induction' n with j IH
    · specialize pointdescent (0:ℕ)
      simp
      calc f (point 1) ≤f xm + 1 / (2 * a) * (‖point 0 - xm‖ ^ 2 - ‖point (0 + 1) - xm‖ ^ 2) := by exact pointdescent
        _ = a⁻¹ * 2⁻¹ * (‖x₀ - xm‖^ 2 - ‖point 1 - xm‖ ^ 2) + f xm := by rw [initial];simp;ring_nf
      simp
    · specialize pointdescent (j+1)
      calc (Finset.range (j.succ+1)).sum (fun (k : ℕ) ↦ f (point (k+1))-f (xm)) =  (Finset.range (j+1)).sum (fun (k : ℕ) ↦ f (point (k+1))-f (xm)) + f (point (j+2))-f (xm) := by
                  rw [Finset.sum_range_succ (fun (k : ℕ)↦ f (point (k+1))-f (xm)) j.succ];rw [Nat.succ_eq_add_one j];ring_nf;rw [add_sub]
            _ ≤ 1/(2*a)*(‖x₀-xm‖^2-‖point (j+1)-xm‖^2) + f (point (j+2))-f (xm) := by linarith
            _ = 1/(2*a)*(‖x₀-xm‖^2-‖point (j+1)-xm‖^2) -f (xm)+f (point (j+2)) :=  by rw [add_sub_right_comm (1/(2*a)*(‖x₀-xm‖^2-‖point (j+1)-xm‖^2)) (f (point (j+2))) (f (xm))]
            _ ≤ 1/(2*a)*(‖x₀-xm‖^2-‖point (j+1)-xm‖^2) + 1/((2:ℝ)*a)*(‖point (j+1)-xm‖^2-‖point (j+2)-xm‖^2) := by linarith
            _ = 1/(2*a)*(‖x₀-xm‖^2-‖point (j.succ+1)-xm‖^2)  := by ring_nf;simp;left;rw [Nat.succ_eq_add_one j];ring_nf
  have sum_prop_1 : ∀ n : ℕ ,  (f (point (n+1))-f (xm)) ≤ (Finset.range (n+1)).sum (fun (k : ℕ)↦ f (point (k+1))-f (xm))/(n+1) := by
    exact mono_sum_prop mono
  specialize sum_prop_1 k
  specialize sum_prop k
  have t₂: f (point (k+1))-f (xm) ≤ 1/(2*(k+1)*a)*(‖x₀-xm‖^2-‖point (k+1)-xm‖^2) := by
    have tt1 : 0 ≤ ↑k+(1:ℝ) := by exact add_nonneg (Nat.cast_nonneg k) zero_le_one
    calc f (point (k+1))-f (xm) ≤   (Finset.range (k+1)).sum (fun (k : ℕ)↦ f (point (k+1))-f (xm))/(k+1) := by exact sum_prop_1
      _ ≤ 1/(2*a)*(‖x₀-xm‖^2-‖point (k+1)-xm‖^2)/(k+1) := by exact div_le_div_of_le tt1 sum_prop
      _ = 1/(2*(k+1)*a)*(‖x₀-xm‖^2-‖point (k+1)-xm‖^2) := by simp;ring_nf
  have t₃: ‖x₀-xm‖^2-‖point (k+1)-xm‖^2 ≤  ‖x₀-xm‖^2 := by simp
  have t₆: 0 ≤ 1/((2:ℝ)*(k+1)*a) := by linarith
  exact le_mul_of_le_mul_of_nonneg_left t₂ t₃ t₆