/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wanyi He
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Convex.Function
import Analysis.Basic
import Mathlib.Topology.MetricSpace.PseudoMetric
import Function.Convex_Function

/-!
# Subgradient of convex functions in EuclideanSpace

The file defines subgradient for convex functions in E and proves some basic properties.

Let `f : E → ℝ` be a convex function on `s` and `g : E`,
where `s` is a set of `E`. Suppose `hf : ConvexOn ℝ s f`.
`g` is a subgradient of `f` at `x` if for any `y ∈ s`, we have `f y ≥ f x + inner g (y - x)`.
The insight comes from the first order condition of convex function.

## Main declarations

* `IsSubgradAt hf g x`: The convex function `f` has subgradient `g` at `x`.
Here `f` is given as an implicit argument
* `SubderivAt hf x`: The collection of all possible subgradients of `f` at `x`.

## Main results

* `subgrad_of_grad` : If `f` has Fderiv `f' x` at `x`, then `SubderivAt hf x = {grad (f' x)}`.
* `zero_mem_iff_isGlobalmin` : Optimality conditions for convex objective functions
-/

open Filter Topology Set InnerProductSpace


noncomputable section

variable {n : Type _} [Fintype n] [DecidableEq n]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {s : Set E}

variable {f : E → ℝ} {g : E} {x : E}

variable {f' : E → (E →L[ℝ] ℝ)}

set_option quotPrecheck false

local notation gradient "∇*" => (toDualMap ℝ _) gradient

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Subgradient of functions --/
def IsSubgradAt (_ : ConvexOn ℝ s f) (g x : E) : Prop :=
  ∀ y ∈ s, f y ≥ f x + inner g (y - x)

/-- Subderiv of functions --/
def SubderivAt (hf : ConvexOn ℝ s f) (x :  E) : Set E :=
  {g : E| IsSubgradAt hf g x}

@[simp]
theorem mem_SubderivAt (hf : ConvexOn ℝ s f) : IsSubgradAt hf g x ↔ g ∈ SubderivAt hf x := ⟨id, id⟩

/-! ### Basic properties about `Subderiv` -/

open EuclideanSpace Set

variable (hf : ConvexOn ℝ s f)

/-- The subderiv of `f` at `x` is a closed set. --/
theorem Subderiv.isClosed : ∀ x ∈ s, IsClosed (SubderivAt hf x) := by
  intro x _
  by_cases e : SubderivAt hf x = ∅
  · apply Eq.subst (Eq.symm e) isClosed_empty
  rw [← isSeqClosed_iff_isClosed]
  intro g g' hg cg y ys
  obtain cg' := Tendsto.const_add (f x) (Filter.Tendsto.inner cg tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto' cg' tendsto_const_nhds (fun n => hg n y ys)

/-- The subderiv of `f` at `x` is a convex set. --/
theorem Subderiv.convex : ∀ x ∈ s, Convex ℝ (SubderivAt hf x) := by
  intro x _
  by_cases e : SubderivAt hf x = ∅
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
theorem subgrad_mono {u v : E} (hf : ConvexOn ℝ s f) (xs : x ∈ s) (ys : y ∈ s)
  (hu : u ∈ SubderivAt hf x) (hv : v ∈ SubderivAt hf y) :
    ⟪u - v, x - y⟫ ≥ (0 : ℝ):= by
      specialize hu y ys; specialize hv x xs
      have ineq1 : ⟪u, x - y⟫ ≥ f x - f y := by
        rw [congrArg (inner u) (Eq.symm (neg_sub y x)), inner_neg_right]; linarith
      have ineq2 := Iff.mpr le_sub_iff_add_le' hv
      rw [inner_sub_left]; linarith


/-! ### Calculation of `Subderiv` -/

open Pointwise

lemma first_order_condition_gradn {f: E → ℝ} {gradf : E}
  {s : Set E} {x: E} (h: HasGradientAt f gradf x) (hf: ConvexOn ℝ s f) (xs: x∈ s) :
  ∀ (y : E), y ∈ s → f x + inner gradf (y - x) ≤ f y:= by
  have H1: ∀ (y : E), y ∈ s → f x + (gradf ∇*) (y - x) ≤ f y:= by
    rw [HasGradientAt] at h
    apply first_order_condition; apply h;
    apply hf; apply xs
  intro y ys
  specialize H1 y ys
  exact H1

/-- Subderiv of differentiable functions --/
theorem subgrad_of_grad' (hx : x ∈ interior s) (hf : ConvexOn ℝ s f) (h : HasGradientAt f g x) :
  SubderivAt hf x = {g} := by
  obtain h' := HasGradientAt_iff_HasFDerivAt.mp h
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  constructor
  · use g; intro y ys
    exact first_order_condition_gradn h hf (interior_subset hx) y ys
  intro g' hg'; by_contra neq
  apply not_le_of_lt (norm_sub_pos_iff.mpr neq)
  let v := g' - g; obtain vneq := sub_ne_zero.mpr neq
  have : Tendsto (fun (t : ℝ) => (f (x + t • v) - f x - ⟪g, t • v⟫) * ‖t • v‖⁻¹) (𝓝[>] 0) (𝓝 0) := by
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
  obtain ineq1 := hg' (x + t • v) mems; rw [add_sub_cancel'] at ineq1
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
  apply sub_le_sub_right (le_sub_iff_add_le'.mpr ineq1)

/-- Alternarive version for FDeriv --/
theorem subgrad_of_grad (hx : x ∈ interior s) (hf : ConvexOn ℝ s f) (h : HasFDerivAt f (f' x) x) :
  SubderivAt hf x = {(toDual ℝ E).symm (f' x)} := by
    have h₁ : HasFDerivAt f ((toDual ℝ E) ((LinearIsometryEquiv.symm (toDual ℝ E)) (f' x))) x := by
      simp [h]
    obtain h' := HasGradientAt_iff_HasFDerivAt.mpr h₁
    exact subgrad_of_grad' hx hf h'

/-- Subderiv of the sum of two functions is a subset of the sum of the subderivs of the two functions --/
theorem subgrad_of_add {s t : Set E} {f₁ f₂ : E → ℝ}
  (hf₁ : ConvexOn ℝ s f₁) (hf₂ : ConvexOn ℝ t f₂) (hadd : ConvexOn ℝ (s ∩ t) (f₁ + f₂)):
    ∀ (x : E), SubderivAt hf₁ x + SubderivAt hf₂ x ⊆ SubderivAt hadd x := by
      intro x y ymem; intro y' hy'
      obtain ⟨y₁, y₂, hy₁, hy₂, eq⟩ := Set.mem_add.mpr ymem
      have eq' : y₁ + y₂ = y := eq
      have : (f₁ + f₂) y' ≥ (f₁ x + ⟪y₁, y' - x⟫) + (f₂ x + ⟪y₂, y' - x⟫ ):= add_le_add (hy₁ y' hy'.1) (hy₂ y' hy'.2)
      rwa [add_add_add_comm, ← inner_add_left, eq'] at this


/-! ### Optimality Theory for Unconstrained Nondifferentiable Problems -/

theorem zero_mem (hf : ConvexOn ℝ s f) (h : x ∈ {x | ∀ y ∈ s, f x ≤ f y}) :
  (0 : E) ∈ SubderivAt hf x :=
    fun y ys => le_of_le_of_eq' (h y ys) (by rw [inner_zero_left, add_zero])

theorem isGlobalmin (hf : ConvexOn ℝ s f) (h : (0 : E) ∈ SubderivAt hf x ) :
  x ∈ {x | ∀ y ∈ s, f x ≤ f y} := by
    intro y ys; specialize h y ys
    rwa [inner_zero_left, add_zero] at h

/-- `x'` minimize `f` if and only if `0` is a subgradient of `f` at `x'` --/
theorem zero_mem_iff_isGlobalmin (hf : ConvexOn ℝ s f) :
  (0 : E) ∈ SubderivAt hf x ↔ x ∈ {x | ∀ y ∈ s, f x ≤ f y} :=
    ⟨fun h => isGlobalmin hf h, fun h => zero_mem hf h⟩



/-! ### Convergence of Subgradient method -/
variable {G : NNReal} (hf : ConvexOn ℝ s f) (lf : LipschitzWith G f)

variable (point : ℕ → E) (g : ℕ → E)
  (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n > 0) (x₀ : E)
  (hg : ∀ (n : ℕ), g n ∈ SubderivAt hf (point n))

variable (update : ∀ (k : ℕ), (point (k + 1)) = point k - a k • (g k))

variable (xm : E) (hm : IsMinOn f s xm)

/- Subgradient of `f` is bounded if and only if `f` is Lipschitz -/
theorem bounded_subgradient_iff_Lipschitz :
    ∀ g ∈ SubderivAt hf x, ‖g‖ ≤ G ↔ LipschitzWith G f := by sorry

theorem subgradient_method :
    ∀ (k : ℕ), 2 * ((Finset.range (k + 1)).sum a) * (sInf {f (point i) | i ∈ Finset.range (k + 1)} - (f xm))
      ≤ ‖x₀ - xm‖ ^ 2 + G ^ 2 * (Finset.range (k + 1)).sum (fun i => (a i) ^ 2) := by sorry

theorem subgradient_method_1 {t : ℝ} (ha' : ∀ (n : ℕ), a n = t) :
    ∀ (k : ℕ), sInf {f (point i) | i ∈ Finset.range (k + 1)} - (f xm)
      ≤ ‖x₀ - xm‖ ^ 2 / (2 * k * t) + G ^ 2 * t / 2 := by sorry

theorem subgradient_method_2 {s : ℝ} (ha' : ∀ (n : ℕ), a n * ‖g n‖ = s) :
    ∀ (k : ℕ), sInf {f (point i) | i ∈ Finset.range (k + 1)} - (f xm)
      ≤ G * ‖x₀ - xm‖ ^ 2 / (2 * k * s) + G * s / 2 := by sorry

theorem subgradient_method_3 (ha' : Tendsto a atTop (𝓝 0))
    (ha'' : Tendsto (fun (k : ℕ) => (Finset.range (k + 1)).sum a) atTop atTop) :
    Tendsto (fun k => sInf {f (point i) | i ∈ Finset.range (k + 1)}) atTop (𝓝 (f xm)) := by sorry

end
