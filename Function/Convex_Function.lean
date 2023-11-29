/-
Copyright (c) 2023 Ziyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Penghao Yu, Cao Zhipeng
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Analysis.Calculation
/-!
  the first order condition of the convex functions
  need to be modified to the gradient defition
-/
open InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section FirstOrderCondition

variable {f : E → ℝ} {f' : E → (E →L[ℝ] ℝ)} {x y x': E}

theorem HasFDeriv_Convergence (h: HasFDerivAt f (f' x) x) :
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ
    → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  rw [HasFDerivAt, HasFDerivAtFilter, Asymptotics.isLittleO_iff] at h
  intro ε epos
  specialize h epos
  rw [Filter.Eventually] at h
  let t := {x_1 | ‖f x_1 - f x - (f' x) (x_1 - x)‖ ≤ ε * ‖x_1 - x‖}
  have h₁: ∃ ε1 > (0 : ℝ), Metric.ball x ε1 ⊆ t := Iff.mp Metric.mem_nhds_iff h
  rcases h₁ with ⟨e1, e1pos, h₁⟩
  use (e1 / 2); constructor
  exact (half_pos e1pos)
  intro x' xnhds
  have h₂: x' ∈ Metric.ball x e1:= by
    rw [Metric.mem_ball, dist_comm]
    rw [← dist_eq_norm] at xnhds
    apply lt_of_le_of_lt xnhds (half_lt_self e1pos)
  have h₃: x' ∈ t := h₁ h₂
  rw [Set.mem_setOf] at h₃
  rw [norm_sub_rev x]
  exact h₃

theorem Convergence_HasFDeriv (h : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
    ‖x - x'‖ ≤ δ → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖) :
      HasFDerivAt f (f' x) x := by
  rw [HasFDerivAt, HasFDerivAtFilter, Asymptotics.isLittleO_iff]
  intro ε epos
  rw [Filter.Eventually]
  specialize h ε epos
  rcases h with ⟨δ, dpos, h⟩
  rw [Metric.mem_nhds_iff]
  use δ ; constructor
  apply dpos
  intro x' x1mem
  have h1: ‖x - x'‖ ≤ δ:= by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm] at x1mem
    exact LT.lt.le x1mem
  specialize h x' h1
  rw[Set.mem_setOf, norm_sub_rev x']
  apply h

theorem HasFDeriv_iff_Convergence_Point {f'x : (E →L[ℝ] ℝ)}:
  HasFDerivAt f (f'x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
     ‖x - x'‖ ≤ δ → ‖f x' - f x - (f'x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  apply HasFDeriv_Convergence
  apply Convergence_HasFDeriv

theorem HasFDeriv_iff_Convergence :
  HasFDerivAt f (f' x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
     ‖x - x'‖ ≤ δ → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  apply HasFDeriv_Convergence
  apply Convergence_HasFDeriv

lemma point_proportion {a b: ℝ} (_ : 0 ≤ a) (_ : 0 ≤ b) (sumab: a + b = 1)
  (hpoint : x' = a • x + b • y) :  x - x' =  b • (x - y) := by
    calc
      x - x' = x - (a • x + b • y):= by rw [hpoint]
      _ = x - a • x - b • y:= sub_add_eq_sub_sub x (a • x) (b • y)
      _ = (1 : ℝ) • x - a • x - b • y:= by rw[one_smul]
      _ = (1 - a) • x - b • y:= by rw[sub_smul 1 a]
      _ = b • x - b • y:= by rw [← sumab]; ring_nf
      _ = b • (x - y):= Eq.symm (smul_sub b x y)

theorem first_order_condition {s : Set E}
    (h : HasFDerivAt f (f' x) x) (hf : ConvexOn ℝ s f) (xs : x ∈ s):
    ∀ (y : E), y ∈ s → f x + f' x (y - x) ≤ f y := by
  have h₁ : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ
       → ‖f x' -f x- (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖:= by
    apply HasFDeriv_Convergence h
  intro y ys
  by_cases h₂: y = x
  rw [h₂, sub_self, ContinuousLinearMap.map_zero (f' x), add_zero]
  have h₃: 0 < ‖x - y‖:= by
    rw [norm_sub_pos_iff,Ne]
    exact Iff.mpr ne_comm h₂
  by_contra H
  push_neg at H
  rw [ConvexOn] at hf
  rcases hf with ⟨ _, cxf⟩
  specialize cxf xs ys
  let ε := f x + (f' x) (y - x) - f y
  have epos : 0 < ε := by
    exact Iff.mpr sub_pos H
  have lnmp: ∀ c : ℝ , f' x (c • (y - x)) = c * (f' x (y - x)):= by
    intro c
    rw [map_smul]
    rfl
  let e1:= ε / (2 * ‖x - y‖)
  have npos: 0 < 2 * ‖x - y‖ := mul_pos two_pos h₃
  have e1pos: 0 < e1:= div_pos epos npos
  specialize h₁ e1 e1pos
  rcases h₁ with ⟨δ , dpos, converge⟩
  let b1 := δ / ‖x - y‖
  have b1pos: 0 < b1 := div_pos dpos h₃
  let b := min b1 (1 : ℝ)
  let a := 1 - b
  have sum_a_b : a + b = 1:= sub_add_cancel 1 b
  have b_nonneg: 0 ≤ b := le_min (LT.lt.le b1pos) zero_le_one
  have a_nonneg : 0 ≤ a := by
    have h1: 0 + b ≤ a + b := by
      rw[zero_add, sum_a_b]
      exact min_le_right b1 1
    rw[add_le_add_iff_right b] at h1
    exact h1
  specialize cxf a_nonneg b_nonneg sum_a_b
  let x' := a • x + b • y
  have x'rfl : x' = a • x + b • y := rfl
  have h1 : ‖x - x'‖ = ‖b • (x - y)‖ := by
    congr; apply point_proportion a_nonneg b_nonneg sum_a_b x'rfl
  have h2 : ‖b • (x - y)‖ = b * ‖x - y‖ := by
    rw[norm_smul]
    rw[Real.norm_of_nonneg]
    apply b_nonneg
  have x1nbhd: ‖x - x'‖ ≤ δ := by
    rw[h1, h2]
    have h3: b * ‖x - y‖ ≤ b1 * ‖x - y‖:= by
      rw[mul_le_mul_right]
      apply min_le_left
      exact h₃
    have h4: b1 * ‖x - y‖ = δ := by
      rw[div_mul_cancel]
      apply ne_of_gt h₃
    rw[← h4]
    apply h3
  specialize converge x' x1nbhd
  have H1: f x + (f' x) (x' - x) - e1 * ‖x - x'‖ ≤ f x':= by
    have l1: f x + (f' x) (x' - x) - f x' ≤ ‖f x' - f x - (f' x) (x' - x)‖:= by
      rw[Real.norm_eq_abs]
      have : f x + (f' x) (x' - x) - f x' = -(f x' - f x - (f' x) (x' - x)):= by
        ring
      rw [this]
      apply neg_le_abs_self
    have l2: f x + (f' x) (x' - x) - f x'≤ e1 * ‖x - x'‖:= by
      apply le_trans l1 converge
    linarith
  have H2: f x' ≤ a • f x + b • f y := by apply cxf
  have H3: f y = f x + (f' x) (y - x) - ε := by simp only [map_sub, sub_sub_cancel]
  have l3: a • f x + b • f y= a * (f x) + b * (f y) := by exact rfl
  have l4: e1 * ‖x - x'‖ = ε * b / 2 := by
    rw[h1, h2]
    calc
      e1 * (b * ‖x - y‖) = ε / (2 * ‖x - y‖) * (b * ‖x - y‖):= by rfl
      _ = ((ε / 2) / ‖x - y‖) *(b * ‖x - y‖):= by ring
      _ = ((ε / 2) / ‖x - y‖) * ‖x - y‖ * b := by rw[mul_comm b, mul_assoc]
      _ = (ε / 2) * b := by rw [div_mul_cancel]; apply ne_of_gt h₃
      _ = ε * b / 2 := by ring
  rw [l4] at H1; rw [l3] at H2
  have H4: a * f x + b * f y = f x + b * (f' x) (y - x) - b * ε := by rw [H3]; ring
  have l5: b* (f' x) (y - x) = (f' x) (x' - x):= by
    have h5: (x' - x) = b • (y - x)  := by
      calc
        x' - x = -(x - x'):= Eq.symm (neg_sub x x')
        _ = - (b • (x - y)):= by rw [point_proportion a_nonneg b_nonneg sum_a_b x'rfl]
        _ = -(b • x - b • y):= by rw[smul_sub]
        _ = b • y - b • x:= by simp only[neg_sub]
        _ = b • (y - x):= by rw[smul_sub]
    rw [h5, lnmp b]
  rw [l5] at H4
  rw [H4] at H2
  have H6: f x + (f' x) (x' - x) - ε * b / 2 ≤ f x + (f' x) (x' - x) - b * ε := le_trans H1 H2
  have H7: - ε * b / 2 ≤ - b * ε := by linarith
  have H8: - ε * b / 2 + b * ε ≤ 0 := by linarith
  have H9: ε *b /2 = - ε * b / 2 + b * ε := by ring
  have blt: 0 < b:= by apply lt_min; apply b1pos; apply zero_lt_one
  have H10: ε * b ≤ 0:= by linarith
  have H11: ε ≤ 0:= nonpos_of_mul_nonpos_left H10 blt
  rw [← H9] at H8; linarith

theorem first_order_condition_inverse {f: E → ℝ} {f' : E → (E →L[ℝ] ℝ)}
  {s : Set E} (h : ∀ (x: E), HasFDerivAt f (f' x) x)(h₁: Convex ℝ s)
  (h₂: ∀ (x : E), x ∈ s → ∀ (y : E), y ∈ s → f x + f' x (y - x) ≤ f y): ConvexOn ℝ s f := by
  rw [ConvexOn]; constructor
  apply h₁; intro x xs y ys a b anonneg bnonneg sumab
  let x' := a • x + b • y
  have x'rfl : x' = a • x + b • y := rfl
  have x'rfl_comm : x' = b • y + a • x := by rw [add_comm]
  have sumba : b + a = 1 := by rw [add_comm]; exact sumab
  specialize h x'
  have x1s: x' ∈ s:= by
    rw [convex_iff_segment_subset] at h₁
    specialize h₁ xs ys
    rw [segment_subset_iff] at h₁
    exact h₁ a b anonneg bnonneg sumab
  have H1: f x' + f' x' (x - x') ≤ f x := h₂ x' x1s x xs
  have H2: f x' + f' x' (y - x') ≤ f y := h₂ x' x1s y ys
  have lnmp: ∀ c: ℝ , f' x' (c • (y - x))= c * (f' x' (y - x)) := by
    intro c; rw [map_smul]; rfl
  have H: a • (f x' + (f' x') (x - x')) + b • (f x' + (f' x') (y - x')) = f x' := by
    have l1: a • (f x' + (f' x') (x - x')) + b • (f x' + (f' x') (y - x'))
        = (a + b) • f x' + a • (f' x') (x - x')+ b • (f' x') (y - x'):= by
      rw [smul_add, smul_add, ← add_assoc, add_assoc (a • f x'),
        add_comm (a • (f' x') (x - x')), ← add_assoc, add_smul]
    have l2: b • (f' x') (y - x') = (a * b) * (f' x') (y - x):= by
      rw [point_proportion bnonneg anonneg sumba x'rfl_comm, lnmp a]
      calc
        b • (a * (f' x') (y - x)) = b * (a * (f' x') (y - x)):= by rfl
        _ = b * a * (f' x') (y - x):= by rw [mul_assoc]
        _ = (a * b) * (f' x') (y - x):= by simp[mul_comm]
    have l3_1: x - x' = (- b) • (y - x):= by
      rw [point_proportion anonneg bnonneg sumab x'rfl]
      calc
        b • (x - y) = b • x - b • y:= by rw [smul_sub]
        _ = (-b) • (-x) - b • y:= by simp only [smul_neg, neg_smul, neg_neg]
        _ = (-b) • (-x) + (-b) • y:= by simp only [smul_neg, neg_smul, neg_neg]; rw [sub_eq_add_neg]
        _ = (-b) • (-x + y):= by rw [smul_add]
        _ = (-b) • (y - x):= by rw[neg_add_eq_sub x y]
    have l3: a • (f' x') (x - x') = - (a * b) * (f' x') (y - x):= by
      rw [l3_1, lnmp (- b)]
      calc
        a • ((-b) * (f' x') (y - x))= a * ((-b) * (f' x') (y - x)):= by rfl
        _ = a * (-b) * (f' x') (y - x):= by rw [mul_assoc]
        _ = (-a * b) * (f' x') (y - x):= by simp only [mul_neg, map_sub, neg_mul]
        _ = -(a * b) * (f' x') (y - x):= by simp only [neg_mul, map_sub]
    rw [l1, sumab, one_smul, l2, l3]
    simp only [map_sub, neg_mul, neg_add_cancel_right]
  have h1: a • (f x' + (f' x') (x - x')) ≤ a • f x:= mul_le_mul_of_nonneg_left H1 anonneg
  have h2: b • (f x' + (f' x') (y - x')) ≤ b • f y:= mul_le_mul_of_nonneg_left H2 bnonneg
  have H3: a • (f x' + (f' x') (x - x')) + b • (f x' + (f' x') (y - x')) ≤ a • f x + b • f y:= add_le_add h1 h2
  rw [H] at H3
  apply H3

theorem first_order_condition_iff {s : Set E} (h₁: Convex ℝ s)
  (h : ∀ (x: E), HasFDerivAt f (f' x) x) :
    ConvexOn ℝ s f ↔ ∀ (x: E),
      x ∈ s → ∀ (y: E), y ∈ s → f x + f' x (y - x) ≤ f y:=
        ⟨ fun h₂ x xs ↦ first_order_condition (h x) h₂ xs, first_order_condition_inverse h h₁ ⟩

theorem convex_monotone_gradient {s : Set E} (hfun: ConvexOn ℝ s f)
(h : ∀ (x: E), HasFDerivAt f (f' x) x) :
∀ x ∈ s, ∀ y ∈ s,  (f' x - f' y) (x - y) ≥ 0 := by
  intro x hx y hy
  have h₁ : f x + f' x (y - x) ≤ f y := first_order_condition (h x) hfun hx y hy
  have h₂ : f y + f' y (x - y) ≤ f x := first_order_condition (h y) hfun hy x hx
  have h₃ : f x + f' x (y - x) + (f y + f' y (x - y)) ≤ f y + f x := add_le_add h₁ h₂
  rw [add_assoc, ← le_sub_iff_add_le', ← add_sub, sub_self, add_zero] at h₃
  rw [add_comm, add_assoc, ← le_sub_iff_add_le', sub_self] at h₃
  simp only [map_sub] at h₃
  simp only [map_sub, ContinuousLinearMap.coe_sub', Pi.sub_apply]
  linarith

end FirstOrderCondition

section

open Set InnerProductSpace

variable {f : E → ℝ} {f' : E → E} {s : Set E}

theorem HasGradient_Convergence (h : HasGradientAt f (f' x) x) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E, ‖x - x'‖ ≤ δ
    → ‖f x' - f x - inner (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  rw [HasGradientAt_iff_HasFDerivAt] at h
  show ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ
    → ‖f x' - f x - ((toDual ℝ E) (f' x)) (x' - x)‖ ≤ ε * ‖x - x'‖
  apply HasFDeriv_Convergence
  exact h

theorem Convergence_HasGradient (h : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
      ‖x - x'‖ ≤ δ → ‖f x' - f x - inner (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖) :
      HasGradientAt f (f' x) x := by
  rw [HasGradientAt_iff_HasFDerivAt]
  apply Convergence_HasFDeriv
  exact h

theorem HasGradient_iff_Convergence_Point {f'x : E}:
      HasGradientAt f f'x x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
     ‖x - x'‖ ≤ δ → ‖f x' - f x - inner (f'x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  apply HasGradient_Convergence
  apply Convergence_HasGradient

theorem HasGradient_iff_Convergence :
      HasGradientAt f (f' x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
      ‖x - x'‖ ≤ δ → ‖f x' - f x - inner (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  apply HasGradient_Convergence
  apply Convergence_HasGradient

theorem first_order_condition' (h : HasGradientAt f (f' x) x) (hf : ConvexOn ℝ s f) (xs : x ∈ s):
    ∀ (y : E), y ∈ s → f x + inner (f' x) (y - x) ≤ f y := by
  show ∀ (y : E), y ∈ s → f x + (toDual ℝ E) (f' x) (y - x) ≤ f y
  apply first_order_condition _ hf xs
  apply h

theorem first_order_condition_inverse'  (h : ∀ x : E, HasGradientAt f (f' x) x) (h₁ : Convex ℝ s)
    (h₂ : ∀ x : E, x ∈ s → ∀ y : E, y ∈ s → f x + inner (f' x) (y - x) ≤ f y) : ConvexOn ℝ s f := by
  apply first_order_condition_inverse
  intro x; specialize h x
  rw [HasGradientAt_iff_HasFDerivAt] at h
  apply h
  apply h₁
  apply h₂

theorem first_order_condition_iff' (h₁ : Convex ℝ s) (h : ∀ x : E, HasGradientAt f (f' x) x) :
    ConvexOn ℝ s f ↔ ∀ x : E,
    x ∈ s → ∀ y: E, y ∈ s → f x + inner (f' x) (y - x) ≤ f y :=
  ⟨ fun h₂ x xs ↦ first_order_condition' (h x) h₂ xs, first_order_condition_inverse' h h₁ ⟩

theorem convex_monotone_gradient' (hfun: ConvexOn ℝ s f) (h : ∀ x : E, HasGradientAt f (f' x) x) :
    ∀ x ∈ s, ∀ y ∈ s, inner (f' x - f' y) (x - y) ≥ (0 : ℝ) := by
  let g := fun x ↦ (toDual ℝ E) (f' x)
  have h' : ∀ x : E, HasFDerivAt f (g x) x := h
  have equiv : ∀ x y : E, inner (f' x - f' y) (x - y) = (g x - g y) (x - y) := by
    intro x y
    rw [← InnerProductSpace.toDual_apply]
    simp only [ContinuousLinearMap.strongUniformity_topology_eq, map_sub,
      ContinuousLinearMap.coe_sub', Pi.sub_apply, toDual_apply]
  intro x hx y hy
  rw [equiv]
  exact convex_monotone_gradient hfun h' x hx  y hy

theorem monotone_gradient_convex' (h₁: Convex ℝ s) (hf : ∀ x, HasGradientAt f (f' x) x)
    (mono: ∀ x1 ∈ s, ∀ y1 ∈ s, inner (f' x1 - f' y1) (x1 - y1) ≥ (0 : ℝ)) : ConvexOn ℝ s f := by
  apply first_order_condition_inverse' hf h₁
  intro x xs y ys
  let g := fun t : ℝ ↦ f (x + t • (y - x))
  let g' := fun t : ℝ ↦ (inner (f' (x + t • (y - x))) (y - x) : ℝ)
  have h1 : ∀ r , HasDerivAt g (g' r) r := by
    let h := fun r : ℝ ↦ (x + r • (y - x))
    have : g = f ∘ h := rfl
    rw [this]; intro t
    have : inner (f' (x + t • (y - x))) (y - x) = toDual ℝ  E (f' (x + t • (y - x))) (y - x) := rfl
    simp; rw [this]; apply HasFDerivAt.comp_hasDerivAt
    · apply HasGradientAt.hasFDerivAt
      simp; exact hf (x + t • (y - x))
    · have ht: HasDerivAt (fun r : ℝ ↦ r) 1 t := hasDerivAt_id' t
      have : HasDerivAt (fun r : ℝ ↦ r • (y - x)) ((1 : ℝ) • (y - x)) t := by
        exact HasDerivAt.smul_const ht (y - x)
      rw [one_smul] at this; exact HasDerivAt.const_add x this
  have e1 : f x = g 0 := by simp
  have e2 : f y = g 1 := by simp
  have e3 : inner (f' x) (y - x) = g' 0 := by simp
  rw [e1, e2, e3]
  have mono' : ∀ t ∈ Ioo 0 1, g' t ≥ g' 0 := by
    intro t ht;
    simp; rw [← sub_nonneg, ← inner_sub_left]
    rcases ht with ⟨ht1, ht2⟩
    have hh: inner (f' (x + t • (y - x)) - f' x) (x + t • (y - x) - x) ≥ (0 : ℝ) := by
      apply mono (x + t • (y - x)) _ x xs
      have e4 : x + t • (y - x) = (1 - t) • x + t • y := by
        rw [smul_sub, add_sub, sub_smul, one_smul, add_sub_right_comm]
      rw [e4]
      apply convex_iff_forall_pos.mp h₁ xs ys (by linarith) (by linarith) (by norm_num)
    rw [add_sub_cancel', inner_smul_right] at hh
    exact (zero_le_mul_left ht1).mp hh
  have h2 : ∃ c ∈ Set.Ioo 0 1, g' c = (g 1 - g 0) / (1 - 0) := by
    apply exists_hasDerivAt_eq_slope
    · linarith
    · have : ∀ x ∈ Icc 0 1, HasDerivAt g (g' x) x := by
        intro x _
        exact (h1 x)
      exact HasDerivAt.continuousOn this
    · simp [h1]
  rcases h2 with ⟨c, ⟨⟨hc1,hc2⟩,hc3⟩⟩
  rw [sub_zero, div_one] at hc3; rw [← le_sub_iff_add_le', ← hc3]
  apply mono' c
  simp; constructor; linarith; linarith

theorem monotone_gradient_convex {s : Set E} {f' : E → (E →L[ℝ] ℝ)}(h₁: Convex ℝ s)
    (hf : ∀ (x : E), HasFDerivAt f (f' x) x)
    (mono: ∀ x ∈ s, ∀ y ∈ s,  (f' x - f' y) (x - y) ≥ 0) : ConvexOn ℝ s f := by
  let g := fun x ↦ ((toDual ℝ E).symm (f' x))
  have h' : ∀ x : E, HasGradientAt f (g x) x := by
    intro x'
    exact HasFDerivAt.hasGradientAt (hf x')
  have equiv : ∀ x y : E, inner (g x - g y) (x - y) = (f' x - f' y) (x - y) := by
    intro x y
    rw [← InnerProductSpace.toDual_apply]; simp
  have mono' : ∀ x ∈ s, ∀ y ∈ s, inner (g x - g y) (x - y) ≥ (0 : ℝ) := by
    intro x hx y hy
    specialize mono x hx y hy
    rw [equiv]; exact mono
  exact monotone_gradient_convex' h₁ h' mono'

section strict

variable {f : E → ℝ} {f' : E → E} {s : Set E}

theorem monotone_gradient_strict_convex (hs: Convex ℝ s) (h : ∀ x : E, HasGradientAt f (f' x) x)
    (mono: ∀ x ∈ s, ∀ y ∈ s, inner (f' x - f' y) (x - y) > (0 : ℝ)) : StrictConvexOn ℝ s f := by
  sorry

theorem strict_convex_monotone_gradient (h : ∀ x : E, HasGradientAt f (f' x) x)
    (h₁: StrictConvexOn ℝ s f ) : ∀ x ∈ s, ∀ y ∈ s, inner (f' x - f' y) (x - y) > (0 : ℝ) := by
  sorry

theorem strict_convex_iff_monotone_gradient
    (hs: Convex ℝ s) (h : ∀ x : E, HasGradientAt f (f' x) x) :
    (∀ x ∈ s, ∀ y ∈ s, inner (f' x - f' y) (x - y) > (0 : ℝ)) ↔ StrictConvexOn ℝ s f := by
  constructor
  exact monotone_gradient_strict_convex hs h
  exact strict_convex_monotone_gradient h

end strict
