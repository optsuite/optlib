/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wanyi He
-/
import Function.Subgradient

/-!
# Convergence of Subgradient method
-/

open Filter Topology Set InnerProductSpace


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {g : E} {x : E} {s : Set E}


/-! ### Convergence of Subgradient method -/

section

variable {G : NNReal} (hf : ConvexOn ℝ s f) (lf : LipschitzWith G f)

variable (point : ℕ → E) (g : ℕ → E)
  (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n > 0) (x₀ : E)
  (hg : ∀ (n : ℕ), g n ∈ SubderivAt f (point n))

variable (update : ∀ (k : ℕ), (point (k + 1)) = point k - a k • (g k))

variable (xm : E) (hm : IsMinOn f s xm)

/- Subgradient of `f` is bounded if and only if `f` is Lipschitz -/
theorem bounded_subgradient_iff_Lipschitz :
    ∀ g ∈ SubderivAt f x, ‖g‖ ≤ G ↔ LipschitzWith G f := by
  sorry

theorem subgradient_method :
    ∀ (k : ℕ), 2 * ((Finset.range (k + 1)).sum a) * (sInf {f (point i) | i ∈ Finset.range (k + 1)} - (f xm))
      ≤ ‖x₀ - xm‖ ^ 2 + G ^ 2 * (Finset.range (k + 1)).sum (fun i => (a i) ^ 2) := by
  sorry

theorem subgradient_method_1 {t : ℝ} (ha' : ∀ (n : ℕ), a n = t) :
    ∀ (k : ℕ), sInf {f (point i) | i ∈ Finset.range (k + 1)} - (f xm)
      ≤ ‖x₀ - xm‖ ^ 2 / (2 * k * t) + G ^ 2 * t / 2 := by
  sorry

theorem subgradient_method_2 {s : ℝ} (ha' : ∀ (n : ℕ), a n * ‖g n‖ = s) :
    ∀ (k : ℕ), sInf {f (point i) | i ∈ Finset.range (k + 1)} - (f xm)
      ≤ G * ‖x₀ - xm‖ ^ 2 / (2 * k * s) + G * s / 2 := by
  sorry

theorem subgradient_method_3 (ha' : Tendsto a atTop (𝓝 0))
    (ha'' : Tendsto (fun (k : ℕ) => (Finset.range (k + 1)).sum a) atTop atTop) :
    Tendsto (fun k => sInf {f (point i) | i ∈ Finset.range (k + 1)}) atTop (𝓝 (f xm)) := by
  sorry

end
