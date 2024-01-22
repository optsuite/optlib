/-
Copyright (c) 2024 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wanyi He, Chenyi Li
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Function.Convex_Function

/-!
# Subgradient of convex functions

The file defines subgradient for convex functions in E and proves some basic properties.

Let `f : E → ℝ` be a convex function on `s` and `g : E`, where `s` is a set of `E`.
`g` is a subgradient of `f` at `x` if for any `y ∈ s`, we have `f y ≥ f x + inner g (y - x)`.
The insight comes from the first order condition of convex function.

## Main declarations

* `HasSubgradientAt f g x`: The function `f` has subgradient `g` at `x`.
* `HasSubgradientWithinAt f g s x`: The function `f` has subgradient `g` at `x` within `s`.
* `SubderivAt f x`: The subderiv of `f` at `x` is the collection of all possible
  subgradients of `f` at `x`.
* `SubderivWithinAt f s x`: The subderiv of `f` at `x` within `s` is
  the collection of all possible subgradients of `f` at `x` within `s`.

## Main results

* `SubderivWithinAt_eq_gradient`: The subderiv of differentiable convex functions
  is the singleton of its gradient.
* `HasSubgradientAt_zero_iff_isMinOn`: `0` is a subgradient of `f` at `x` if and
  only if `x` is a minimizer of `f`.
-/

open Filter Topology Set InnerProductSpace


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {g : E} {x : E} {s : Set E}

set_option quotPrecheck false

local notation gradient "∇*" => (toDualMap ℝ _) gradient

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Subgradient of functions --/
def HasSubgradientAt (f : E → ℝ) (g x : E) : Prop :=
  ∀ y, f y ≥ f x + ⟪g, y - x⟫

def HasSubgradientWithinAt (f : E → ℝ) (g : E) (s : Set E) (x : E) : Prop :=
  ∀ y ∈ s, f y ≥ f x + ⟪g, y - x⟫

/-- Subderiv of functions --/
def SubderivAt (f : E → ℝ) (x : E) : Set E :=
  {g : E| HasSubgradientAt f g x}

def SubderivWithinAt (f : E → ℝ) (s : Set E) (x : E) : Set E :=
  {g : E| HasSubgradientWithinAt f g s x}

@[simp]
theorem mem_SubderivAt : HasSubgradientAt f g x ↔ g ∈ SubderivAt f x := ⟨id, id⟩

@[simp]
theorem hasSubgradientWithinAt_univ :
    HasSubgradientWithinAt f g univ x ↔ HasSubgradientAt f g x :=
  ⟨fun h y => h y trivial, fun h y _ => h y⟩

theorem HasSubgradientAt.hasSubgradientWithinAt :
    HasSubgradientAt f g x → HasSubgradientWithinAt f g s x := fun h y _ => h y

/-! ### Basic properties about `Subderiv` -/

section Basic_properties

variable (hf : ConvexOn ℝ s f)

open Bornology

/-- The subderiv of `f` at `x` is a closed set. --/
theorem SubderivAt.isClosed : ∀ x, IsClosed (SubderivAt f x) := by
  intro x
  by_cases e : SubderivAt f x = ∅
  · apply Eq.subst (Eq.symm e) isClosed_empty
  rw [← isSeqClosed_iff_isClosed]
  intro g g' hg cg y
  obtain cg' := Tendsto.const_add (f x) (Filter.Tendsto.inner cg tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto' cg' tendsto_const_nhds (fun n => hg n y)

theorem SubderivWithinAt.isClosed : ∀ x, IsClosed (SubderivWithinAt f s x) := by
  intro x
  by_cases e : SubderivWithinAt f s x = ∅
  · apply Eq.subst (Eq.symm e) isClosed_empty
  rw [← isSeqClosed_iff_isClosed]
  intro g g' hg cg y ys
  obtain cg' := Tendsto.const_add (f x) (Filter.Tendsto.inner cg tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto' cg' tendsto_const_nhds (fun n => hg n y ys)

/-- The subderiv of `f` at `x` is a convex set. --/
theorem SubderivAt.convex : ∀ x, Convex ℝ (SubderivAt f x) := by
  intro x
  by_cases e : SubderivAt f x = ∅
  · apply Eq.subst (Eq.symm e) convex_empty
  intro g₁ h1 g₂ h2 a b lea leb abeq y
  have ineq1 : a • f y ≥ a • f x + a • ⟪g₁, y - x⟫ := by
    rw [← smul_add]
    apply smul_le_smul_of_nonneg (h1 y) lea
  have ineq2 : b • f y ≥ b • f x + b • inner g₂ (y - x) := by
    rw [← smul_add]
    apply smul_le_smul_of_nonneg (h2 y) leb
  have eq : (a • f x + a • inner g₁ (y - x)) + (b • f x + b • inner g₂ (y - x))
      = f x + inner (a • g₁ + b • g₂) (y - x) := by
    rw [add_add_add_comm, ← Eq.symm (Convex.combo_self abeq (f x))]
    apply congrArg (HAdd.hAdd (f x))
    rw [inner_add_left, inner_smul_left, inner_smul_left]; rfl
  rw [Eq.symm (Convex.combo_self abeq (f y)), ← eq]
  apply add_le_add ineq1 ineq2

theorem SubderivWithinAt.convex : ∀ x ∈ s, Convex ℝ (SubderivWithinAt f s x) := by
  intro x _
  by_cases e : SubderivWithinAt f s x = ∅
  · apply Eq.subst (Eq.symm e) convex_empty
  intro g₁ h1 g₂ h2 a b lea leb abeq y ys
  have ineq1 : a • f y ≥ a • f x + a • ⟪g₁, y - x⟫ := by
    rw [← smul_add]
    apply smul_le_smul_of_nonneg (h1 y ys) lea
  have ineq2 : b • f y ≥ b • f x + b • inner g₂ (y - x) := by
    rw [← smul_add]
    apply smul_le_smul_of_nonneg (h2 y ys) leb
  have eq : (a • f x + a • inner g₁ (y - x)) + (b • f x + b • inner g₂ (y - x))
      = f x + inner (a • g₁ + b • g₂) (y - x) := by
    rw [add_add_add_comm, ← Eq.symm (Convex.combo_self abeq (f x))]
    apply congrArg (HAdd.hAdd (f x))
    rw [inner_add_left, inner_smul_left, inner_smul_left]; rfl
  rw [Eq.symm (Convex.combo_self abeq (f y)), ← eq]
  apply add_le_add ineq1 ineq2

/-- Monotonicity of subderiv--/
theorem subgradientAt_mono {u v : E} {f : E → ℝ}
    (hu : u ∈ SubderivAt f x) (hv : v ∈ SubderivAt f y) : ⟪u - v, x - y⟫ ≥ (0 : ℝ):= by
  specialize hu y; specialize hv x
  have ineq1 : ⟪u, x - y⟫ ≥ f x - f y := by
    rw [congrArg (inner u) (Eq.symm (neg_sub y x)), inner_neg_right]; linarith
  have ineq2 : inner v (x - y) ≤ f x - f y := Iff.mpr le_sub_iff_add_le' hv
  rw [inner_sub_left]; linarith

end Basic_properties

/-! ### Calculation of `Subderiv` -/

section calculation

open Pointwise

/-- Subderiv of differentiable convex functions --/
theorem SubderivWithinAt_eq_gradient {f' : E → E} (hx : x ∈ interior s)
    (hf : ConvexOn ℝ s f) (h : HasGradientAt f (f' x) x) :
    SubderivWithinAt f s x = {f' x} := by
  obtain h' := hasGradientAt_iff_hasFDerivAt.mp h
  let g := f' x
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  constructor
  · use g; intro y ys
    apply first_order_condition' h hf (interior_subset hx) y ys
  intro g' hg'; by_contra neq
  apply not_le_of_lt (norm_sub_pos_iff.mpr neq)
  let v := g' - g; obtain vneq := sub_ne_zero.mpr neq
  have : Tendsto (fun (t : ℝ) => (f (x + t • v) - f x - ⟪g, t • v⟫) * ‖t • v‖⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]; intro ε εpos
    unfold HasFDerivAt at h'
    rw [hasFDerivAtFilter_iff_tendsto, Metric.tendsto_nhds_nhds] at h'
    obtain ⟨δ, δpos, hδ⟩ := h' ε εpos
    use (δ * ‖v‖⁻¹)
    obtain pos := mul_pos δpos (inv_pos.mpr (norm_pos_iff.mpr vneq))
    constructor
    · exact pos
    intro t _ ht; rw [dist_eq_norm] at ht; rw [dist_eq_norm]
    have : dist (x + t • v) x < δ := by
      rw [dist_eq_norm, add_sub_cancel', norm_smul, ← (sub_zero t)]
      apply lt_of_lt_of_eq ((mul_lt_mul_right (norm_sub_pos_iff.mpr neq)).mpr ht)
      rw [mul_assoc, inv_mul_cancel (norm_ne_zero_iff.mpr vneq), mul_one]
    specialize hδ this; rw [dist_eq_norm] at hδ
    have eq1 : ‖‖x + t • v - x‖⁻¹‖ = ‖t • v‖⁻¹ := by
      rw [add_sub_cancel', norm_inv, norm_norm]
    have eq2 : (g ∇*) (x + t • v - x) = ⟪g, t • v⟫ := by rw [add_sub_cancel']; exact rfl
    have eq3 : ‖(f (x + t • v) - f x - ⟪g, t • v⟫) * ‖t • v‖⁻¹ - 0‖ =
      ‖f (x + t • v) - f x - ⟪g, t • v⟫‖ * ‖t • v‖⁻¹ := by
        rw [sub_zero, norm_mul, norm_inv, norm_norm]
    have eq : ‖‖x + t • v - x‖⁻¹ * ‖f (x + t • v) - f x - (g ∇*) (x + t • v - x)‖ - 0‖ =
      ‖(f (x + t • v) - f x - ⟪g, t • v⟫) * ‖t • v‖⁻¹ - 0‖ := by
        rw [sub_zero, norm_mul, norm_norm, mul_comm, eq1, eq2, ← eq3]
    apply Eq.trans_lt (Eq.symm eq) hδ
  apply ge_of_tendsto this
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff]
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨ε, εpos, ballmem⟩ := hx
  obtain pos := mul_pos εpos (inv_pos.mpr (norm_pos_iff.mpr vneq))
  use (ε * ‖v‖⁻¹); use pos; intro t ht
  have tball := ht.1; have tlt : t > 0 := ht.2
  have tvpos : ‖t • v‖⁻¹ > 0 := by
    apply inv_pos.mpr; rw [norm_smul]
    apply smul_pos (abs_pos_of_pos tlt) (norm_sub_pos_iff.mpr neq)
  have mems : x + t • v ∈ s := by
    apply ballmem
    rw [mem_ball_iff_norm, sub_zero] at tball
    rw [mem_ball_iff_norm, add_sub_cancel', norm_smul]
    have : ‖t‖ * ‖v‖ < ε * ‖v‖⁻¹ * ‖v‖ := by
      apply (mul_lt_mul_right (norm_sub_pos_iff.mpr neq)).mpr tball
    rwa [mul_assoc, inv_mul_cancel (norm_ne_zero_iff.mpr vneq), mul_one] at this
  obtain ineq1 := hg' (x + t • v); rw [add_sub_cancel'] at ineq1
  have eq1 : ‖v‖ = (⟪g', t • v⟫ - ⟪g, t • v⟫) * ‖t • v‖⁻¹ := by
    have eq2 : ‖v‖ = ⟪v, v⟫ * ‖v‖⁻¹ := by
      rw [real_inner_self_eq_norm_sq]
      apply (div_eq_iff _).mp
      · rw [div_inv_eq_mul, pow_two]
      exact inv_ne_zero (norm_ne_zero_iff.mpr vneq)
    have eq3 : ⟪v, v⟫ * ‖v‖⁻¹ = ⟪v, t • v⟫ * ‖t • v‖⁻¹ := by
      have : ⟪v, t • v⟫ = ⟪v, v⟫ * t := by rw [inner_smul_right, mul_comm]
      rw [this, mul_assoc]
      have : ‖v‖⁻¹ = t * ‖t • v‖⁻¹ := by
        have :  t * ‖t • v‖⁻¹ = t / ‖t • v‖ := rfl
        rw [this, inv_eq_one_div]
        have : t = ‖t‖ := by
          have : ‖t‖ = |t| := rfl
          rw [this, abs_of_pos tlt]
        rw [this, norm_smul, norm_norm, div_mul_eq_div_div, div_self]
        rw [norm_ne_zero_iff]
        exact ne_of_gt tlt
      rw [this]
    rw [eq2, eq3, mul_eq_mul_right_iff];
    left; rw [inner_sub_left]
  rw [mem_setOf, eq1, mul_le_mul_right tvpos]
  apply sub_le_sub_right (le_sub_iff_add_le'.mpr (ineq1 mems))

/-- Alternarive version for FDeriv --/
theorem SubderivWithinAt_eq_FDeriv {f' : E → (E →L[ℝ] ℝ)} (hx : x ∈ interior s)
    (hf : ConvexOn ℝ s f) (h : HasFDerivAt f (f' x) x) :
    SubderivWithinAt f s x = {(toDual ℝ E).symm (f' x)} := by
  have h₁ : HasFDerivAt f ((toDual ℝ E) ((LinearIsometryEquiv.symm (toDual ℝ E)) (f' x))) x := by
      simp [h]
  obtain h' := hasGradientAt_iff_hasFDerivAt.mpr h₁
  apply SubderivWithinAt_eq_gradient hx hf
  exact h'

/-- Subderivatives of the sum of two functions is a subset of the sum of the
subderivatives of the two functions --/
theorem SubderivAt.add_subset {f₁ f₂ : E → ℝ} :
    ∀ (x : E), SubderivAt f₁ x + SubderivAt f₂ x ⊆ SubderivAt (f₁ + f₂) x := by
  intro x y hy y'
  obtain ⟨y₁, y₂, hy₁, hy₂, eq⟩ := Set.mem_add.mpr hy
  have eq' : y₁ + y₂ = y := eq
  have : (f₁ + f₂) y' ≥ (f₁ x + ⟪y₁, y' - x⟫) + (f₂ x + ⟪y₂, y' - x⟫) :=
    add_le_add (hy₁ y') (hy₂ y')
  rwa [add_add_add_comm, ← inner_add_left, eq'] at this
  
end calculation

/-! ### Optimality Theory for Unconstrained Nondifferentiable Problems -/

section

theorem HasSubgradientAt_zero_of_isMinOn (h : IsMinOn f univ x) : HasSubgradientAt f 0 x :=
  fun y => le_of_le_of_eq' (h trivial) (by rw [inner_zero_left, add_zero])

theorem isMinOn_of_HasSubgradentAt_zero (h : HasSubgradientAt f 0 x) : IsMinOn f univ x := by
  intro y _; specialize h y
  rwa [inner_zero_left, add_zero] at h

/-- `x'` minimize `f` if and only if `0` is a subgradient of `f` at `x'` --/
theorem HasSubgradientAt_zero_iff_isMinOn :
    HasSubgradientAt f 0 x ↔ IsMinOn f univ x :=
  ⟨isMinOn_of_HasSubgradentAt_zero, HasSubgradientAt_zero_of_isMinOn⟩

theorem HasSubgradientWithinAt_zero_of_isMinOn (h : IsMinOn f s x) :
    HasSubgradientWithinAt f 0 s x :=
  fun y ys => le_of_le_of_eq' (h ys) (by rw [inner_zero_left, add_zero])

theorem isMinOn_of_HasSubgradentWithinAt_zero (h : HasSubgradientWithinAt f 0 s x) :
    IsMinOn f s x := by
  intro y ys; specialize h y ys
  rwa [inner_zero_left, add_zero] at h

theorem HasSubgradientWithinAt_zero_iff_isMinOn :
    HasSubgradientWithinAt f 0 s x ↔ IsMinOn f s x :=
  ⟨isMinOn_of_HasSubgradentWithinAt_zero, HasSubgradientWithinAt_zero_of_isMinOn⟩

end
