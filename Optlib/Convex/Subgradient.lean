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
import Mathlib.Data.Real.Sign
import Optlib.Convex.BanachSubgradient
import Optlib.Convex.ConvexFunction

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

local notation gradient "∇*" => (toDualMap ℝ _) gradient

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {f : E → ℝ} {g : E} {x : E} {s : Set E}

noncomputable section

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

theorem SubderivAt_SubderivWithinAt :
    SubderivAt f x = SubderivWithinAt f univ x := by
  simp only [SubderivAt, SubderivWithinAt, hasSubgradientWithinAt_univ]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {g : E} {x : E} {s : Set E}


theorem HasSubgradientAt_HasBanachSubgradientAt {f : E → ℝ} {g : E} {x : E} :
    HasSubgradientAt f g x ↔ Banach_HasSubgradientAt f (toDual ℝ E g) x := by
  constructor
  · intro h z
    unfold HasSubgradientAt at h
    obtain hz := h z
    simp; linarith
  intro h z
  unfold Banach_HasSubgradientAt at h
  obtain hz := h z; simp at hz
  linarith

theorem HasBanachSubgradientAt_HasSubgradientAt {f : E → ℝ} {g : E →L[ℝ] ℝ} {x : E} :
    Banach_HasSubgradientAt f g x ↔ HasSubgradientAt f ((toDual ℝ E).symm g) x := by
  constructor
  · intro h z
    unfold Banach_HasSubgradientAt at h
    obtain hz := h z
    simp; rw [← ContinuousLinearMap.map_sub]; linarith
  intro h z
  unfold HasSubgradientAt at h
  obtain hz := h z; simp at hz
  rw [ContinuousLinearMap.map_sub]; linarith

theorem HasSubgradientWithinAt_HasBanachSubgradientWithinAt {f : E → ℝ} {g : E} {x : E} :
    HasSubgradientWithinAt f g s x ↔ Banach_HasSubgradientWithinAt f (toDual ℝ E g) s x := by
  constructor
  · intro h z hz
    unfold HasSubgradientAt at h
    obtain hz := h z hz
    simp; linarith
  intro h z hz
  unfold Banach_HasSubgradientAt at h
  obtain hz := h z hz; simp at hz
  linarith

theorem HasBanachSubgradientWithinAt_HasSubgradientWithinAt {f : E → ℝ} {g : E →L[ℝ] ℝ} {x : E} :
    Banach_HasSubgradientWithinAt f g s x ↔ HasSubgradientWithinAt f ((toDual ℝ E).symm g) s x := by
  constructor
  · intro h z hz
    unfold Banach_HasSubgradientAt at h
    obtain hz := h z hz
    simp; rw [← ContinuousLinearMap.map_sub]; linarith
  intro h z hz
  unfold HasSubgradientAt at h
  obtain hz := h z hz; simp at hz
  rw [ContinuousLinearMap.map_sub]; linarith

end

/-! ### Congruence properties of the `Subderiv` -/
section congr

variable {f₁ f₂ : E → ℝ} {t s : Set E}

theorem SubderivAt.congr (h : f₁ = f₂) : SubderivAt f₁ x = SubderivAt f₂ x := by
  ext g; rw [h]

theorem SubderivWithinAt.congr (h : ∀ y ∈ s, f₁ y = f₂ y) (hf : f₁ x = f₂ x):
    SubderivWithinAt f₁ s x = SubderivWithinAt f₂ s x := by
  ext g
  exact ⟨fun hg y ys => by rw [← h y ys, ← hf]; exact hg y ys,
            fun hg y ys => by rw [h y ys, hf]; exact hg y ys⟩

theorem SubderivWithinAt.congr_of_mem (xs : x ∈ s) (h : ∀ y ∈ s, f₁ y = f₂ y) :
    SubderivWithinAt f₁ s x = SubderivWithinAt f₂ s x := congr h (h x xs)

theorem SubderivAt.congr_mono (h : ∀ y ∈ s, f₁ y = f₂ y) (hx : f₁ x = f₂ x) (h₁ : t ⊆ s) :
    SubderivWithinAt f₁ t x = SubderivWithinAt f₂ t x :=
  SubderivWithinAt.congr (fun y a => h y (h₁ a)) hx

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
    apply smul_le_smul_of_nonneg_left (h1 y) lea
  have ineq2 : b • f y ≥ b • f x + b • ⟪g₂, y - x⟫ := by
    rw [← smul_add]
    apply smul_le_smul_of_nonneg_left (h2 y) leb
  have eq : (a • f x + a • ⟪g₁, y - x⟫) + (b • f x + b • ⟪g₂, y - x⟫)
      = f x + ⟪a • g₁ + b • g₂, y - x⟫ := by
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
    apply smul_le_smul_of_nonneg_left (h1 y ys) lea
  have ineq2 : b • f y ≥ b • f x + b • ⟪g₂, y - x⟫ := by
    rw [← smul_add]
    apply smul_le_smul_of_nonneg_left (h2 y ys) leb
  have eq : (a • f x + a • ⟪g₁, y - x⟫) + (b • f x + b • ⟪g₂, y - x⟫)
      = f x + ⟪a • g₁ + b • g₂, y - x⟫ := by
    rw [add_add_add_comm, ← Eq.symm (Convex.combo_self abeq (f x))]
    apply congrArg (HAdd.hAdd (f x))
    rw [inner_add_left, inner_smul_left, inner_smul_left]; rfl
  rw [Eq.symm (Convex.combo_self abeq (f y)), ← eq]
  apply add_le_add ineq1 ineq2

/-- Monotonicity of subderiv--/
theorem subgradientAt_mono {u v : E} {f : E → ℝ}{y : E}
    (hu : u ∈ SubderivAt f x) (hv : v ∈ SubderivAt f y) : ⟪u - v, x - y⟫ ≥ (0 : ℝ):= by
  specialize hu y; specialize hv x
  have ineq1 : ⟪u, x - y⟫ ≥ f x - f y := by
    rw [congrArg (fun z => ⟪u, z⟫) (Eq.symm (neg_sub y x)), inner_neg_right]; linarith
  have _ : ⟪v, x - y⟫ ≤ f x - f y := Iff.mpr le_sub_iff_add_le' hv
  rw [inner_sub_left]; linarith

end congr

/-! ### Basic properties about `Subderiv` -/

section Basic_properties

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {g : E} {x y : E} {s : Set E}

open Bornology

/- The subderiv of `f` at interior point `x` is a nonempty set -/
theorem SubderivWithinAt.Nonempty  (hf : ConvexOn ℝ s f) (hc : ContinuousOn f (interior s)):
    ∀ x ∈ interior s, (SubderivWithinAt f s x).Nonempty := by
  intro x hx
  obtain h := Banach_SubderivWithinAt.Nonempty hf hc hx
  unfold Set.Nonempty at h ⊢
  rcases h with ⟨g, hg⟩; unfold Banach_SubderivWithinAt at hg
  simp at hg
  rw [HasBanachSubgradientWithinAt_HasSubgradientWithinAt] at hg;
  use (toDual ℝ E).symm g; unfold SubderivWithinAt
  simp [hg]

theorem SubderivAt.nonempty (hf : ConvexOn ℝ univ f) (hc : ContinuousOn f univ) :
    ∀ x, Nonempty (SubderivAt f x) := by
  intro x
  rw [SubderivAt_SubderivWithinAt]
  have : x ∈ interior univ := by simp
  rw [← interior_univ] at hc
  obtain h := SubderivWithinAt.Nonempty hf hc x this
  simp
  rcases h with ⟨a, ha⟩
  exact ⟨a, ha⟩

end Basic_properties

/-! ### Calculation of `Subderiv` -/

section equivalence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {g : E} {x y : E} {s : Set E}

open Pointwise

/-- Subderiv of differentiable convex functions --/
theorem SubderivWithinAt_eq_gradient {f'x : E} (hx : x ∈ interior s)
    (hf : ConvexOn ℝ s f) (h : HasGradientAt f (f'x) x) :
    SubderivWithinAt f s x = {f'x} := by
  obtain h' := hasGradientAt_iff_hasFDerivAt.mp h
  let g := f'x
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  constructor
  · use g; intro y ys
    apply Convex_first_order_condition' h hf (interior_subset hx) y ys
  intro g' hg'; by_contra neq
  apply not_le_of_gt (norm_sub_pos_iff.mpr neq)
  let v := g' - g; obtain vneq := sub_ne_zero.mpr neq
  have : Tendsto (fun (t : ℝ) => (f (x + t • v) - f x - ⟪g, t • v⟫) * ‖t • v‖⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]; intro ε εpos
    have h'' := (hasGradientAt_iff_tendsto).mp h
    rw [Metric.tendsto_nhds_nhds] at h''
    obtain ⟨δ, δpos, hδ⟩ := h'' ε εpos
    use (δ * ‖v‖⁻¹)
    obtain pos := mul_pos δpos (inv_pos.mpr (norm_pos_iff.mpr vneq))
    constructor
    · exact pos
    intro t _ ht; rw [dist_eq_norm] at ht; rw [dist_eq_norm]
    have : dist (x + t • v) x < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, ← (sub_zero t)]
      have hmul : ‖t - 0‖ * ‖v‖ < (δ * ‖v‖⁻¹) * ‖v‖ :=
        mul_lt_mul_of_pos_right ht (norm_pos_iff.mpr vneq)
      have hnorm : ‖v‖⁻¹ * ‖v‖ = (1 : ℝ) := inv_mul_cancel₀ (norm_ne_zero_iff.mpr vneq)
      simpa [mul_assoc, hnorm] using hmul
    specialize hδ this; rw [dist_eq_norm] at hδ
    have eq1 : ‖‖x + t • v - x‖⁻¹‖ = ‖t • v‖⁻¹ := by
      rw [add_sub_cancel_left, norm_inv, norm_norm]
    have eq2 : (g ∇*) (x + t • v - x) = ⟪g, t • v⟫ := by rw [add_sub_cancel_left]; exact rfl
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
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul]
    have : ‖t‖ * ‖v‖ < ε * ‖v‖⁻¹ * ‖v‖ := by
      exact mul_lt_mul_of_pos_right tball (norm_pos_iff.mpr vneq)
    rwa [mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr vneq), mul_one] at this
  obtain ineq1 := hg' (x + t • v); rw [add_sub_cancel_left] at ineq1
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
  rw [mem_setOf, eq1]
  exact mul_le_mul_of_nonneg_right
    (sub_le_sub_right (le_sub_iff_add_le'.mpr (ineq1 mems)) _) (le_of_lt tvpos)

/-- Alternarive version for FDeriv --/
theorem SubderivWithinAt_eq_FDeriv {f' : E → (E →L[ℝ] ℝ)} (hx : x ∈ interior s)
    (hf : ConvexOn ℝ s f) (h : HasFDerivAt f (f' x) x) :
    SubderivWithinAt f s x = {(toDual ℝ E).symm (f' x)} := by
  have h₁ : HasFDerivAt f ((toDual ℝ E) ((LinearIsometryEquiv.symm (toDual ℝ E)) (f' x))) x := by
      simp [h]
  obtain h' := hasGradientAt_iff_hasFDerivAt.mpr h₁
  apply SubderivWithinAt_eq_gradient hx hf
  exact h'

theorem SubderivAt_eq_gradient {f'x : E}
    (hf : ConvexOn ℝ univ f) (h : HasGradientAt f (f'x) x) :
    SubderivAt f x = {f'x} := by
  rw [SubderivAt_SubderivWithinAt]
  apply SubderivWithinAt_eq_gradient _ hf h
  · simp only [interior_univ, mem_univ]

end equivalence

/-! ### Optimality Theory for Unconstrained Nondifferentiable Problems -/

section optimality_theory

theorem HasSubgradientAt_zero_of_isMinOn (h : IsMinOn f univ x) : HasSubgradientAt f 0 x :=
  fun y => by simpa [inner_zero_left] using h trivial

theorem isMinOn_of_HasSubgradentAt_zero (h : HasSubgradientAt f 0 x) : IsMinOn f univ x := by
  intro y _; specialize h y
  rwa [inner_zero_left, add_zero] at h

/-- `x'` minimize `f` if and only if `0` is a subgradient of `f` at `x'` --/
theorem HasSubgradientAt_zero_iff_isMinOn :
    HasSubgradientAt f 0 x ↔ IsMinOn f univ x :=
  ⟨isMinOn_of_HasSubgradentAt_zero, HasSubgradientAt_zero_of_isMinOn⟩

theorem HasSubgradientWithinAt_zero_of_isMinOn (h : IsMinOn f s x) :
    HasSubgradientWithinAt f 0 s x :=
  fun y ys => by simpa [inner_zero_left] using h ys

theorem isMinOn_of_HasSubgradentWithinAt_zero (h : HasSubgradientWithinAt f 0 s x) :
    IsMinOn f s x := by
  intro y ys; specialize h y ys
  rwa [inner_zero_left, add_zero] at h

theorem HasSubgradientWithinAt_zero_iff_isMinOn :
    HasSubgradientWithinAt f 0 s x ↔ IsMinOn f s x :=
  ⟨isMinOn_of_HasSubgradentWithinAt_zero, HasSubgradientWithinAt_zero_of_isMinOn⟩

lemma SubderivAt_zero (xm : E) : 0 ∈ SubderivAt f xm ↔ ∀ y, f y ≥ f xm + ⟪0, y - xm⟫:= by rfl

theorem first_order_convex_iff_subgradient (f : E → ℝ) (xm : E) : IsMinOn f univ xm ↔ 0 ∈ SubderivAt f xm := by
  rw [SubderivAt_zero xm ,isMinOn_iff]
  constructor
  · intro h y
    simp only [inner_zero_left, add_zero, ge_iff_le]
    apply h y
    simp only [mem_univ]
  · intro h x _
    have := h x
    simp only [inner_zero_left, add_zero, ge_iff_le] at this
    exact this

end optimality_theory

/-! ### Computing `Subderiv` -/

section computation

open Pointwise

variable {f : E → ℝ} {g : E} {x : E} {s : Set E}

/-- Multiplication by a Positive Scalar--/
theorem HasSubgradientAt.pos_smul {c : ℝ} (h : HasSubgradientAt f g x) (hc : 0 < c) :
    HasSubgradientAt (c • f) (c • g) x := by
  intro y; rw [inner_smul_left]
  have ineq := mul_le_mul_of_nonneg_left (h y) (le_of_lt hc)
  simpa [Pi.smul_apply, mul_add, ge_iff_le] using ineq

theorem SubderivAt.pos_smul {c : ℝ} (hc : 0 < c) :
    SubderivAt (c • f) x = c • (SubderivAt f x) := by
  ext g
  constructor
  · intro hg; use (c⁻¹ • g)
    constructor
    · intro y;
      have neq : c ≠ 0 :=  ne_of_gt hc
      calc
        f y = c⁻¹ * (c * f y) := (eq_inv_mul_iff_mul_eq₀ neq).mpr rfl
        _ ≥ c⁻¹ * (c * f x + ⟪g, y - x⟫) :=
          mul_le_mul_of_nonneg_left (hg y) (inv_nonneg.mpr (le_of_lt hc))
        _ = f x + ⟪c⁻¹ • g, y - x⟫ := by
          rw [mul_add, inner_smul_left, ← ((eq_inv_mul_iff_mul_eq₀ neq).mpr rfl)]
          rfl
    exact smul_inv_smul₀ (ne_of_gt hc) g
  rintro ⟨gg, hgg, eq⟩; intro y
  calc
    c * f y ≥ c * (f x + ⟪gg, y - x⟫) := by
      exact mul_le_mul_of_nonneg_left (hgg y) (le_of_lt hc)
    _ = c * f x + c * ⟪gg, y - x⟫ := mul_add c (f x) ⟪gg, y - x⟫
    _ = c * f x + ⟪c • gg, y - x⟫ := by
      rw [inner_smul_left]; exact rfl
    _ = c * f x + ⟪g, y - x⟫ := by rw [← eq]

/-- Subderivatives of the sum of two functions is a subset of the sum of the
subderivatives of the two functions --/
theorem SubderivAt.add_subset {f₁ f₂ : E → ℝ} :
    ∀ (x : E), SubderivAt f₁ x + SubderivAt f₂ x ⊆ SubderivAt (f₁ + f₂) x := by
  intro x y hy y'
  obtain ⟨y₁, hy₁, y₂, hy₂, eq⟩ := Set.mem_add.mpr hy
  have eq' : y₁ + y₂ = y := eq
  have : (f₁ + f₂) y' ≥ (f₁ x + ⟪y₁, y' - x⟫) + (f₂ x + ⟪y₂, y' - x⟫) :=
    add_le_add (hy₁ y') (hy₂ y')
  rwa [add_add_add_comm, ← inner_add_left, eq'] at this

private lemma leq_tendsto_zero {a : ℝ} (h : ∀ t > 0, 0 < a + t) : 0 ≤ a := by
  by_contra h'; push_neg at h';
  specialize h (- a / 2) (by linarith)
  linarith

end computation

section

variable [CompleteSpace E]

open Pointwise

theorem SubderivAt.add {f₁ f₂ : E → ℝ} (h₁ : ConvexOn ℝ univ f₁) (h₂: ConvexOn ℝ univ f₂)
    (hcon : ContinuousOn f₁ univ) :
    ∀ (x : E), SubderivAt f₁ x + SubderivAt f₂ x = SubderivAt (f₁ + f₂) x := by
  intro x₀
  apply Subset.antisymm (SubderivAt.add_subset x₀)
  rw [SubderivAt, SubderivAt, SubderivAt, Set.subset_def]
  intro g hg
  rw [Set.mem_setOf] at hg; rw [Set.mem_add]
  let S₁ := {(x, y) : E × ℝ | y > f₁ (x + x₀) - f₁ x₀ - ⟪g, x⟫}
  let S₂ := {(x, y) : E × ℝ | y ≤ f₂ x₀ - f₂ (x + x₀)}

  have hs1 : Convex ℝ S₁ := by
    rw [convex_iff_forall_pos]; intro i hi j hj a b ha hb hab
    rw [Set.mem_setOf] at hi hj ⊢; simp at hi hj ⊢
    rw [← mul_lt_mul_iff_of_pos_left ha] at hi
    rw [← mul_lt_mul_iff_of_pos_left hb] at hj
    rw [inner_add_right, inner_smul_right, inner_smul_right, ← sub_sub]
    have : x₀ = (1 : ℝ) • x₀ := by simp only [one_smul]
    have : a • i.1 + b • j.1 + x₀ = a • (i.1 + x₀) + b • (j.1 + x₀) := by
      nth_rw 1 [this]; rw [smul_add, smul_add, ← hab, add_smul];
      rw [← add_assoc, ← add_assoc]; simp; rw [add_assoc, add_comm (b • j.1), ← add_assoc]
    have : f₁ (a • i.1 + b • j.1 + x₀) ≤ a * f₁ (i.1 + x₀) + b * f₁ (j.1 + x₀) := by
      rw [this]
      rw [convexOn_iff_forall_pos] at h₁; rcases h₁ with ⟨_, h₁⟩
      specialize @h₁ (i.1 + x₀) (by trivial) (j.1 + x₀) (by trivial) a b ha hb hab
      simp at h₁; simp; linarith
    apply lt_of_lt_of_le' (b := a * f₁ (i.1 + x₀) + b * f₁ (j.1 + x₀) -
        f₁ x₀ - a * ⟪g, i.1⟫_ℝ - b * ⟪g, j.1⟫_ℝ)
    · have : f₁ x₀ = (1 : ℝ) • (f₁ x₀) := by simp
      rw [this, ← hab, add_smul, ← sub_sub, smul_eq_mul, smul_eq_mul]; linarith
    · simp [this];
  have hs2 : Convex ℝ S₂ := by
    rw [convex_iff_forall_pos]; intro i hi j hj a b ha hb hab
    rw [Set.mem_setOf] at hi hj ⊢; simp at hi hj ⊢
    rw [← mul_le_mul_iff_of_pos_left ha] at hi
    rw [← mul_le_mul_iff_of_pos_left hb] at hj
    have : x₀ = (1 : ℝ) • x₀ := by simp only [one_smul]
    have : a • i.1 + b • j.1 + x₀ = a • (i.1 + x₀) + b • (j.1 + x₀) := by
      nth_rw 1 [this]; rw [smul_add, smul_add, ← hab, add_smul];
      rw [← add_assoc, ← add_assoc]; simp; rw [add_assoc, add_comm (b • j.1), ← add_assoc]
    have ineq : f₂ (a • i.1 + b • j.1 + x₀) ≤ a * f₂ (i.1 + x₀) + b * f₂ (j.1 + x₀) := by
      rw [this]
      rw [convexOn_iff_forall_pos] at h₂; rcases h₂ with ⟨_, h₂⟩
      specialize @h₂ (i.1 + x₀) (by trivial) (j.1 + x₀) (by trivial) a b ha hb hab
      simp at h₂; simp; linarith
    have eq : f₂ x₀ = a * f₂ x₀ + b * f₂ x₀ := by rw [← add_mul, hab, one_mul]
    obtain hh := sub_le_sub_left ineq (a * f₂ x₀ + b * f₂ x₀)
    have eq' : a * (f₂ x₀ - f₂ (i.1 + x₀)) + b * (f₂ x₀ - f₂ (j.1 + x₀)) =
      a * f₂ x₀ + b * f₂ x₀ - (a * f₂ (i.1 + x₀) + b * f₂ (j.1 + x₀)) := by ring
    rw [← eq'] at hh; rw [eq]
    apply le_trans (add_le_add hi hj) hh
  have hint : Disjoint S₁ S₂ := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro ⟨x, y⟩ ⟨hp1, hp2⟩
    rw [Set.mem_setOf] at hp1 hp2
    specialize hg (x + x₀); rw [← add_sub, sub_self, add_zero] at hg
    apply not_le_of_gt ?_ hg
    obtain ineq := add_lt_add_of_le_of_lt hp2 (neg_lt_neg hp1)
    simp at ineq
    have hh : ∀ x : E, (f₁ + f₂) x = f₁ x + f₂ x := fun x => rfl
    apply lt_of_sub_pos
    have eq : f₂ x₀ - f₂ (x + x₀) + (⟪g, x⟫_ℝ - (f₁ (x + x₀) - f₁ x₀)) =
      f₁ x₀ + f₂ x₀ + ⟪g, x⟫_ℝ - (f₁ (x + x₀) + f₂ (x + x₀)) := by ring
    rwa [hh x₀, hh (x + x₀), ← eq]
  have hso : IsOpen S₁ := by
    apply Continuous_epi_open (f₁ := fun x ↦ f₁ (x + x₀) - f₁ x₀ - ⟪g, x⟫)
    apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · apply ContinuousOn.comp (g := f₁) (f := fun x ↦ x + x₀) (t := univ) hcon
        · apply ContinuousOn.add continuousOn_id continuousOn_const
        · simp
      apply continuousOn_const
    apply ContinuousOn.inner continuousOn_const continuousOn_id

  obtain ⟨f, c, ⟨hsl, hsr⟩⟩ := geometric_hahn_banach_open hs1 hso hs2 hint
  have eq : ∃ a : E, ∃ b : ℝ, ∀ (p : E × ℝ), f p = ⟪a, p.1⟫ + b * p.2 := by
    let f1 := ContinuousLinearMap.comp f (ContinuousLinearMap.inl ℝ E ℝ)
    let f2 := ContinuousLinearMap.comp f (ContinuousLinearMap.inr ℝ E ℝ)
    use (toDual ℝ E).symm f1
    use (toDual ℝ ℝ).symm f2
    intro p
    have hf2 : ((toDual ℝ ℝ).symm f2) * p.2 = f2 p.2 := by
      have hinner : ⟪(toDual ℝ ℝ).symm f2, p.2⟫ = f2 p.2 :=
        InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := ℝ) (x := p.2) (y := f2)
      calc
        ((toDual ℝ ℝ).symm f2) * p.2 = p.2 * ((toDual ℝ ℝ).symm f2) := by ring
        _ = ⟪(toDual ℝ ℝ).symm f2, p.2⟫ := by rfl
        _ = f2 p.2 := hinner
    rw [hf2]; simp [f2]
    have : (p.1, (0 : ℝ)) + ((0 : E), p.2) = p := by simp
    nth_rw 1 [← this]; rw [ContinuousLinearMap.map_add]
    simp [f1]
  rcases eq with ⟨a, b, hab⟩

  have hin : (0, 0) ∈ S₂ := by rw [Set.mem_setOf]; simp
  obtain hc0 := hsr (0, 0) hin
  rw [hab (0, 0)] at hc0; simp at hc0
  have hin1 : ∀ t > 0, (0, t) ∈ S₁ := by
    intro t ht; rw [Set.mem_setOf]; simp; linarith
  have htp : ∀ t > 0, b * t < c := by
      intro t ht; obtain hin1 := hin1 t ht
      specialize hsl (0, t) hin1; specialize hab (0, t); simp at hab
      linarith
  have ceq0 : c = 0 := by
    by_contra hc; push_neg at hc; have hc : c < 0 := lt_of_le_of_ne hc0 hc
    by_cases hb : b ≥ 0
    · specialize htp 1 (by linarith); rw [mul_one] at htp
      linarith
    push_neg at hb
    have pos : (c / (2 * b)) > 0 := by
      apply div_pos_of_neg_of_neg hc (by linarith)
    specialize (htp (c / (2 * b)) pos)
    have hb0 : b ≠ 0 := by linarith
    have hhalf : b * (c / (2 * b)) = c / 2 := by
      field_simp [hb0]
    have : c / 2 < c := by linarith [htp, hhalf]
    linarith
  have bleq0 : b < 0 := by
    rw [ceq0] at htp
    specialize htp 1 (by linarith); rw [mul_one] at htp; linarith
  let hata := - (1 / b) • a

  have g1 : g + hata ∈ {g | HasSubgradientAt f₁ g x₀} := by
    rw [Set.mem_setOf]; unfold HasSubgradientAt; intro x
    simp [hata]
    have hin1 : ∀ t > 0, (x - x₀, f₁ x - f₁ x₀ - ⟪g, x - x₀⟫_ℝ + t) ∈ S₁ := by
      intro t ht
      rw [Set.mem_setOf]; simp; exact ht
    have ineq : ∀ t > 0, 0 < b⁻¹ * ⟪a, x - x₀⟫_ℝ + f₁ x - f₁ x₀ - ⟪g, x - x₀⟫_ℝ + t := by
      intro t ht
      specialize hsl (x - x₀, f₁ x - f₁ x₀ - ⟪g, x - x₀⟫_ℝ + t) (hin1 t ht)
      rw [ceq0, hab (x - x₀, f₁ x - f₁ x₀ - ⟪g, x - x₀⟫_ℝ + t)] at hsl; simp at hsl
      obtain ineq := (mul_lt_mul_left_of_neg (inv_lt_zero.mpr bleq0)).mpr hsl
      simp at ineq
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_lt bleq0), one_mul] at ineq
      rw [← add_assoc, add_sub, add_sub] at ineq; exact ineq
    rw [inner_add_left, inner_neg_left, real_inner_smul_left]
    rw [← add_assoc]; simp
    have : b⁻¹ * ⟪a, x - x₀⟫_ℝ + f₁ x - f₁ x₀ - ⟪g, x - x₀⟫_ℝ ≥ 0 := leq_tendsto_zero ineq
    linarith
  have g2 : - hata ∈ {g | HasSubgradientAt f₂ g x₀} := by
    rw [Set.mem_setOf]; unfold HasSubgradientAt; intro x
    simp [hata];
    have hin2 : (x - x₀, f₂ x₀ - f₂ x) ∈ S₂ := by rw [Set.mem_setOf]; simp
    specialize hsr (x - x₀, f₂ x₀ - f₂ x) hin2
    rw [ceq0, hab (x - x₀, f₂ x₀ - f₂ x)] at hsr; simp at hsr
    obtain ineq := (mul_le_mul_left_of_neg (inv_lt_zero.mpr bleq0)).mpr hsr
    rw [mul_add, ← real_inner_smul_left, mul_zero, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_lt bleq0), one_mul] at ineq
    linarith
  use (g + hata); constructor; exact g1
  use (- hata); constructor; exact g2; simp

end

/-! ### Examples of `Subderiv` -/

section

theorem SubderivAt_of_norm_at_zero : SubderivAt (fun (x : E) => ‖x‖) 0 = {g | ‖g‖ ≤ 1} := by
  ext g
  constructor
  · intro hg; by_contra h
    have hg' : ‖g‖ > 1 := not_le.mp h
    specialize hg g
    simp only [sub_zero, norm_zero, zero_add, real_inner_self_eq_norm_mul_norm] at hg
    have : ‖g‖ * ‖g‖ > 1 * ‖g‖ := mul_lt_mul_of_pos_right hg' (by linarith)
    simp only [one_mul] at this
    apply not_lt.mpr hg this
  intro hg y
  calc
    ‖(0 : E)‖ + ⟪g, y - 0⟫ = ⟪g, y⟫ := by simp only [norm_zero, zero_add, sub_zero]
    _ ≤ ‖g‖ * ‖y‖ := real_inner_le_norm g y
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg y)
    _ = ‖y‖ := by simp only [one_mul]

theorem SubderivAt_abs (x : ℝ) :
    SubderivAt abs x = if x = 0 then Icc (-1) 1 else {Real.sign x} := by
  rw [eq_ite_iff]
  by_cases h : x = 0
  · left;
    constructor
    · exact h
    have h2 : Icc (-1 : ℝ) 1 = {g | ‖g‖ ≤ 1} := by
      ext y; simp only [Icc, mem_setOf, norm]
      have : |y| ≤ 1 ↔ -1 ≤ y ∧ y ≤ 1 := by apply abs_le
      exact (Iff.symm this)
    rw [h2, h]
    apply SubderivAt_of_norm_at_zero
  right
  constructor
  · exact h
  ext g
  constructor
  · intro hg
    by_cases hx : x > 0
    · by_contra gne
      by_cases glt : g < 1
      · specialize hg 0
        have ineq : (0 : ℝ) < 0 := by
          calc
            0 ≥ x + g * (-x):= by
              simp only [abs_zero, zero_sub, abs_of_pos hx] at hg
              have hinner : ⟪g, -x⟫ = (-x) * g := by rfl
              rwa [hinner, mul_comm] at hg
            _ = x * (1 - g) := by ring
            _ > 0 := mul_pos hx (by linarith)
        exact LT.lt.false ineq
      specialize hg (x + 1)
      have : x + 1 > 0 := by linarith
      simp only [abs_of_pos hx, abs_of_pos this, add_le_add_iff_left, add_sub_cancel_left] at hg
      apply glt
      have h1: g ≤ 1 := by
        calc
          g = ⟪g, 1⟫ := by
            rw [show ⟪g, 1⟫ = (1 : ℝ) * g by rfl]
            ring
          _ ≤ 1 := hg
      simp only [Real.sign_of_pos hx] at gne
      exact Ne.lt_of_le gne h1
    have hx : x < 0 := Ne.lt_of_le h (not_lt.mp hx)
    rw [Real.sign_of_neg hx]
    by_contra gne
    by_cases glt : g < -1
    · specialize hg (x - 1)
      have : x - 1 < 0 := by linarith
      simp only [abs_of_neg this, abs_of_neg hx] at hg
      have : -g ≤ 1 := by
        calc
          -g = ⟪g, x - 1 - x⟫ := by
            rw [show ⟪g, x - 1 - x⟫ = (x - 1 - x) * g by rfl]
            ring
          _ ≤ 1 := by linarith [hg]
      linarith
    specialize hg 0
    have eq1 : ⟪g, -x⟫ = g * (-x) := by
      rw [show ⟪g, -x⟫ = (-x) * g by rfl]
      ring
    have eq2 : -x + g * -x = -x * (1 + g) := by ring
    simp only [abs_zero, zero_sub, abs_of_neg hx, eq1, eq2] at hg
    have : -x * (1 + g) > 0 := by
      apply mul_pos (by linarith)
      have : g > -1 := Ne.lt_of_le' gne (not_lt.mp glt)
      linarith
    linarith
  intro hg y
  by_cases hx : x > 0
  · simp only [Real.sign_of_pos hx] at hg
    calc
      |x| + ⟪g, y - x⟫ = x + ⟪1, y - x⟫ := by rw [abs_of_pos hx, hg]
      _ = y := by
        rw [show ⟪(1 : ℝ), y - x⟫ = (y - x) * 1 by rfl]
        ring
      _ ≤ |y| := le_abs_self y
  have hx : x < 0 := Ne.lt_of_le h (not_lt.mp hx)
  simp only [Real.sign_of_neg hx] at hg
  calc
    |x| + ⟪g, y - x⟫ = -x + ⟪-1, y - x⟫ := by rw [abs_of_neg hx, hg]
    _ = -y := by
      rw [show ⟪(-1 : ℝ), y - x⟫ = (y - x) * (-1) by rfl]
      ring
    _ ≤ |y| := neg_le_abs y

end
