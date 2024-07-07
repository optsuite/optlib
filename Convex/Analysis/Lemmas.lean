/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Convex.Analysis.Calculation

section continuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {f' : E → (E →L[ℝ] ℝ)} {x y x' : E}

/-!
# Lemmas

## Main results

This file contains the following parts of basic properties of continuous and differentiable lemmas
* the equivalent definition of continuous functions
* the equivalent definition of fderiv and gradient
* the deriv of composed function on a segment
* the gradient of special functions with inner product and norm
* the taylor expansion of a differentiable function locally
* the langrange interpolation of a differentiable function
-/

theorem ContinuousAt_Convergence (h : ContinuousAt f x) : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ (x' : E), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε:= by
  rw [continuousAt_def] at h
  intro ε epos
  let A := Metric.ball (f x) ε
  specialize h A (Metric.ball_mem_nhds (f x) epos)
  rw [Metric.mem_nhds_iff] at h
  rcases h with ⟨δ, dpos, h⟩
  use (δ /2); constructor
  exact half_pos dpos
  intro x' x1le
  have H1: x' ∈ Metric.ball x δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub]
    apply lt_of_le_of_lt x1le
    exact half_lt_self dpos
  exact LT.lt.le (h H1)

theorem Convergence_ContinuousAt (h: ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
    ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε) :
  ContinuousAt f x := by
  rw [continuousAt_def]
  intro A amem
  rw [Metric.mem_nhds_iff] at amem
  rcases amem with ⟨ε, epos, bmem⟩
  specialize h (ε / 2) (half_pos epos)
  rcases h with ⟨δ , dpos, h⟩
  rw [Metric.mem_nhds_iff]
  use δ; constructor
  exact dpos
  rw [Set.subset_def]
  intro x' x1mem
  have : ‖x - x'‖ ≤ δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub] at x1mem
    exact LT.lt.le x1mem
  specialize h x' this
  have H1: f x' ∈  Metric.ball (f x) ε := by
    rw [Metric.ball, Set.mem_setOf, dist_eq_norm_sub]
    apply lt_of_le_of_lt h (half_lt_self epos)
  exact bmem H1

theorem ContinuousAt_iff_Convergence: ContinuousAt f x ↔ ∀ ε > (0 : ℝ),
    ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε:= by
  constructor
  apply ContinuousAt_Convergence
  apply Convergence_ContinuousAt

lemma continuous (h : ContinuousAt f x) : ∀ ε > 0, ∃ δ > 0, ∀ (y : E), ‖y - x‖ < δ
    → ‖f y - f x‖ < ε := by
  rw [ContinuousAt_iff_Convergence] at h
  intro a ha; specialize h (a / 2) (by linarith); rcases h with ⟨δ, ⟨h₁, h₂⟩⟩
  use δ; constructor; assumption
  intro y hy;rw [norm_sub_rev] at hy; specialize h₂ y (by linarith); linarith

end continuous

section derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} {l a : ℝ} {f' : E → (E →L[ℝ] ℝ)} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}

theorem deriv_function_comp_segment (x y : E) (h₁ : ∀ x₁ : E, HasFDerivAt f (f' x₁) x₁) :
    ∀ t₀ : ℝ , HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x)))
    ((fun t : ℝ ↦ (f' (x + t • (y - x)) (y - x))) t₀) t₀ := by
  let h := fun t : ℝ ↦ x + t • (y - x)
  have h_deriv : ∀ t : ℝ,  HasDerivAt h (y - x) t := by
    intro t
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have : (fun z => h (t + z) - h t - z • (y - x)) = (fun z => 0) := by
      ext z; simp [h]
      rw [add_smul, add_comm, ← add_sub, sub_self, add_zero, sub_self]
    simp [this]
  have H₂: ∀ t₀ : ℝ , HasDerivAt (f ∘ h) (f' (x + t₀ • (y - x)) (y - x)) t₀ := by
    intro t₀
    apply HasFDerivAt.comp_hasDerivAt
    · apply h₁ (x + t₀ • (y - x))
    · apply h_deriv t₀
  intro t₀
  apply H₂ t₀

theorem HasFDeriv_Convergence (h: HasFDerivAt f (f' x) x) :
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ
    → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  rw [HasFDerivAt, hasFDerivAtFilter_iff_isLittleO, Asymptotics.isLittleO_iff] at h
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
  rw [HasFDerivAt, hasFDerivAtFilter_iff_isLittleO, Asymptotics.isLittleO_iff]
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
  · intro h
    apply HasFDeriv_Convergence
    exact h
  · apply Convergence_HasFDeriv

theorem HasFDeriv_iff_Convergence :
  HasFDerivAt f (f' x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
     ‖x - x'‖ ≤ δ → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  apply HasFDeriv_Convergence
  apply Convergence_HasFDeriv

end derivative

section gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {x p y : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open Topology InnerProductSpace Set Filter Tendsto

theorem HasGradient_Convergence (h : HasGradientAt f (f' x) x) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E, ‖x - x'‖ ≤ δ
    → ‖f x' - f x - inner (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  rw [hasGradientAt_iff_hasFDerivAt] at h
  show ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ
    → ‖f x' - f x - ((toDual ℝ E) (f' x)) (x' - x)‖ ≤ ε * ‖x - x'‖
  apply HasFDeriv_Convergence
  exact h

theorem Convergence_HasGradient (h : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
    ‖x - x'‖ ≤ δ → ‖f x' - f x - inner (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖) :
    HasGradientAt f (f' x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact HasFDeriv_iff_Convergence_Point.mpr h

theorem HasGradient_iff_Convergence_Point {f'x : E}:
      HasGradientAt f f'x x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
     ‖x - x'‖ ≤ δ → ‖f x' - f x - inner (f'x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  · intro h; apply HasGradient_Convergence
    exact h
  · apply Convergence_HasGradient

theorem HasGradient_iff_Convergence :
      HasGradientAt f (f' x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
      ‖x - x'‖ ≤ δ → ‖f x' - f x - inner (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  apply HasGradient_Convergence
  apply Convergence_HasGradient

lemma gradient_norm_sq_eq_two_self (x : E) :
    HasGradientAt (fun x ↦ ‖x‖ ^ 2) ((2 : ℝ) • x) x := by
  apply Convergence_HasGradient
  simp
  intro e ep
  use e
  constructor
  . linarith
  . intro x' dles
    rw [← norm_neg (x - x'), neg_sub] at dles
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_sub_right]
    rw [real_inner_smul_left, real_inner_smul_left]; ring_nf
    rw [add_sub, add_sub_right_comm, mul_two, ← sub_sub]
    rw [← inner_sub_left, sub_add, ← inner_sub_right]
    rw [real_inner_comm, ← inner_sub_left, real_inner_self_eq_norm_sq]
    rw [abs_of_nonneg, pow_two, ← norm_neg (x - x'), neg_sub]
    apply mul_le_mul_of_nonneg_right dles (norm_nonneg (x' - x))
    apply pow_two_nonneg

lemma gradient_of_inner_const (x : E) (a : E):
    HasGradientAt (fun x ↦ (inner a x : ℝ)) a x := by
  apply HasGradient_iff_Convergence_Point.mpr
  simp only [gt_iff_lt, Real.norm_eq_abs]
  intros ε εpos
  use (1 : ℝ)
  constructor; simp
  · intro x' _
    rw[← inner_sub_right, ← inner_sub_right, sub_self, inner_zero_right]
    simp; positivity

lemma gradient_of_const_mul_norm (l : ℝ) (z : E) :
    HasGradientAt (fun (x : E) => l / 2 * ‖x‖ ^ 2) (l • z) z := by
  let h := fun x : E => ‖x‖ ^ 2
  have e1 : (l • z) = (l / 2) • (2 : ℝ) • z := by rw [smul_smul]; simp
  have : (fun (x : E) => l / 2 * ‖x‖ ^ 2) = (fun (x : E) => (l / 2) • h x) := by
    ext; simp
  have h1 : HasGradientAt h ((2 : ℝ) • z) z := gradient_norm_sq_eq_two_self z
  rw [this, e1]; refine HasGradientAt.const_smul' (l / 2) h1

lemma gradient_of_sq : ∀ u : E, HasGradientAt (fun u ↦ ‖u - x‖ ^ 2 / 2) (u - x) u := by
  intro s
  rw [HasGradient_iff_Convergence_Point]
  simp; intro e ep; use e
  constructor
  · linarith
  · intro x' dles; field_simp; rw [abs_div]; simp
    have eq1 (u v : E) (e : ℝ) (dle : ‖u - v‖ ≤ e) :
      |‖v‖ ^ 2 - ‖u‖ ^ 2 - inner ((2 : ℝ) • u) (v - u)| ≤ e * ‖u - v‖ := by
      rw [← norm_neg (u - v), neg_sub] at dle;
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_sub_right]
      rw [real_inner_smul_left, real_inner_smul_left]; ring_nf
      rw [add_sub, add_sub_right_comm, mul_two, ← sub_sub]
      rw [← inner_sub_left, sub_add, ← inner_sub_right]
      rw [real_inner_comm, ← inner_sub_left, real_inner_self_eq_norm_sq]
      rw [abs_of_nonneg, pow_two, ← norm_neg (u - v), neg_sub]
      apply mul_le_mul_of_nonneg_right dle (norm_nonneg (v - u))
      apply pow_two_nonneg
    let u := s - x
    have hu : u = s - x := rfl
    let v := x' - x
    have hv : v = x' - x := rfl
    rw [← real_inner_smul_left]
    have eq2 : s - x' = u - v := by rw [hu, hv]; simp
    have eq3 : x' - s = v - u := by rw [hu, hv]; simp
    rw [eq2, eq3]
    show |‖v‖ ^ 2 - ‖u‖ ^ 2 - inner ((2 : ℝ) • u) (v - u)| / 2 ≤ e * ‖u - v‖
    calc
      |‖v‖ ^ 2 - ‖u‖ ^ 2 - inner ((2 : ℝ) • u) (v - u)| / 2 ≤ (e * ‖u - v‖) / 2 := by
        rw [div_le_div_right]
        apply eq1; rw [hu, hv]; simp; apply dles; simp
      _ ≤ e * ‖u - v‖ := by
        field_simp

lemma sub_normsquare_gradient (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) (m : ℝ):
    ∀ x ∈ s, HasGradientAt (fun x ↦ f x - m / 2 * ‖x‖ ^ 2) (f' x - m • x) x := by
  intro x xs
  apply HasGradientAt.sub
  . apply hf x xs
  . have u := HasGradientAt.const_smul (gradient_norm_sq_eq_two_self x) (m / 2)
    simp at u
    rw [smul_smul, div_mul_cancel_of_invertible] at u
    apply u

/-
If the function f is first-order continuously differentiable, then
the gradient of f is continuous.
-/
lemma gradient_continuous_of_contdiff {x : E} {ε : ℝ} (f : E → ℝ)
    (he : ε > 0) (hf : ContDiffOn ℝ 1 f (Metric.ball x ε)) :
    ContinuousAt (fun x ↦ gradient f x) x := by
  let s := Metric.ball x ε
  have h : ContDiffAt ℝ 1 f x := by
    apply ContDiffOn.contDiffAt hf
    rw [mem_nhds_iff]; use s
    exact ⟨Eq.subset rfl, ⟨Metric.isOpen_ball, Metric.mem_ball_self he⟩⟩
  rw [contDiffAt_one_iff] at h
  rcases h with ⟨f', ⟨u, ⟨hu1, ⟨hu2, hu3⟩⟩⟩⟩
  have : Set.EqOn (fun y ↦ (LinearIsometryEquiv.symm (toDual ℝ E)) (f' y))
      (fun y ↦ gradient f y) u := by
    intro z hz; dsimp
    specialize hu3 z hz
    rw [hasFDerivAt_iff_hasGradientAt] at hu3
    have : HasGradientAt f (gradient f z) z :=
      DifferentiableAt.hasGradientAt hu3.differentiableAt
    exact HasGradientAt.unique hu3 this
  have hcon1 : ContinuousOn (fun y ↦ (LinearIsometryEquiv.symm (toDual ℝ E)) (f' y)) u :=
    Continuous.comp_continuousOn (LinearIsometryEquiv.continuous _) hu2
  rw [(continuousOn_congr this)] at hcon1
  apply ContinuousOn.continuousAt hcon1 hu1

end gradient

section expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x p y : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open InnerProductSpace Set
/-
  For any function f : E → ℝ, where E is a InnerProduct space, and for any point x in E and vector p in E,
  if f has a gradient at every point in its domain, then there exists a real number t such that t is
  greater than 0 and less than 1, and f(x + p) is equal to f(x) plus the inner product of the gradient of
  f at (x + t * p) with p.
-/

lemma expansion (hf : ∀ x : E, HasGradientAt f (f' x) x) (x p : E) :
    ∃ t : ℝ, t > 0 ∧ t < 1 ∧ f (x + p) = f x + inner (f' (x + t • p)) p := by
  let g := fun r : ℝ ↦ f (x + r • p)
  let g' := fun r : ℝ ↦ (inner (f' (x + r • p)) p : ℝ)
  have h1 : ∀ r , HasDerivAt g (g' r) r := by
    let h := fun r : ℝ ↦ x + r • p
    have : g = f ∘ h := by rfl
    rw [this]; intro r
    have : inner (f' (x + r • p)) p = toDual ℝ E (f' (x + r • p)) p := rfl
    simp [g']; rw [this]; apply HasFDerivAt.comp_hasDerivAt
    · apply hasGradientAt_iff_hasFDerivAt.mp
      exact hf (x + r • p)
    · apply HasDerivAt.const_add
      have ht: HasDerivAt (fun x : ℝ ↦ x) 1 r := hasDerivAt_id' r
      have : HasDerivAt (fun r : ℝ ↦ r • p) ((1 : ℝ) • p) r := by
        apply HasDerivAt.smul_const ht p
      rw [one_smul] at this; exact this
  have e1 : f (x + p) = g 1 := by simp [g]
  have e2 : f x = g 0 := by simp [g]
  have e3 : ∀ t, inner (f' (x + t • p)) p = g' t := by simp []
  rw [e1, e2]
  have : ∃ c ∈ Set.Ioo 0 1, g' c = (g 1 - g 0) / (1 - 0) := by
    apply exists_hasDerivAt_eq_slope g g' (by norm_num)
    · have : ∀ x ∈ Icc 0 1, HasDerivAt g (g' x) x := by
        intro x _
        exact (h1 x)
      exact HasDerivAt.continuousOn this
    · simp [h1]
  rcases this with ⟨c, ⟨c1, c2⟩, h2⟩
  use c
  constructor; exact c1;
  constructor; exact c2;
  rw [e3 c]; simp [h2]

lemma general_expansion (x p : E) (hf : ∀ y ∈ Metric.closedBall x ‖p‖, HasGradientAt f (f' y) y) :
    ∃ t : ℝ, t > 0 ∧ t < 1 ∧ f (x + p) = f x + inner (f' (x + t • p)) p := by
  let g := fun r : ℝ ↦ f (x + r • p)
  let g' := fun r : ℝ ↦ (inner (f' (x + r • p)) p : ℝ)
  have h1 : ∀ r ∈ Icc 0 1, HasDerivAt g (g' r) r := by
    let h := fun r : ℝ ↦ x + r • p
    have : g = f ∘ h := by rfl
    rw [this]; intro r hr
    have : inner (f' (x + r • p)) p = toDual ℝ E (f' (x + r • p)) p := rfl
    simp [g']; rw [this]; apply HasFDerivAt.comp_hasDerivAt
    · apply hasGradientAt_iff_hasFDerivAt.mp
      have : x + r • p ∈ Metric.closedBall x ‖p‖ := by
        simp; simp at hr; rw [norm_smul, r.norm_eq_abs, abs_of_nonneg hr.1];
        rcases hr with ⟨_, hr2⟩
        apply mul_le_of_le_one_left (norm_nonneg p) hr2
      exact hf (x + r • p) this
    · apply HasDerivAt.const_add
      have : HasDerivAt (fun r : ℝ ↦ r • p) ((1 : ℝ) • p) r := by
        apply HasDerivAt.smul_const (hasDerivAt_id' r) p
      rw [one_smul] at this; exact this
  have e1 : f (x + p) = g 1 := by simp [g]
  have e2 : f x = g 0 := by simp [g]
  have e3 : ∀ t, inner (f' (x + t • p)) p = g' t := by simp []
  rw [e1, e2]
  have : ∃ c ∈ Set.Ioo 0 1, g' c = (g 1 - g 0) / (1 - 0) := by
    apply exists_hasDerivAt_eq_slope g g' (by norm_num)
    · exact HasDerivAt.continuousOn h1
    · intro x hx; apply h1 x
      rcases hx with ⟨hx1, hx2⟩; constructor <;> linarith
  rcases this with ⟨c, ⟨c1, c2⟩, h2⟩
  use c
  constructor; exact c1;
  constructor; exact c2;
  rw [e3 c]; simp [h2]

theorem lagrange (hs : Convex ℝ s) (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ∀ x ∈ s, ∀ y ∈ s, ∃ c : ℝ, c ∈ Set.Ioo 0 1 ∧
    inner (f' (x + c • (y - x))) (y - x) = f y - f x := by
  intro x xs y ys
  let g := fun t : ℝ ↦ f (x + t • (y - x))
  let g' := fun t : ℝ ↦ (inner (f' (x + t • (y - x))) (y - x) : ℝ)
  have h1 : ∀ r ∈ Icc 0 1 , HasDerivAt g (g' r) r := by
    let h := fun r : ℝ ↦ (x + r • (y - x))
    have : g = f ∘ h := rfl
    rw [this]; intro t ht
    have : inner (f' (x + t • (y - x))) (y - x) = toDual ℝ  E (f' (x + t • (y - x))) (y - x) := rfl
    simp [g']; rw [this]; apply HasFDerivAt.comp_hasDerivAt
    · apply hasGradientAt_iff_hasFDerivAt.mp
      have : x + t • (y - x) ∈ s := by
        apply Convex.add_smul_sub_mem hs xs ys; simp; simp at ht; rcases ht with ⟨ht1, ht2⟩
        constructor <;> linarith
      exact hf (x + t • (y - x)) this
    · have ht: HasDerivAt (fun r : ℝ ↦ r) 1 t := hasDerivAt_id' t
      have : HasDerivAt (fun r : ℝ ↦ r • (y - x)) ((1 : ℝ) • (y - x)) t := by
        exact HasDerivAt.smul_const ht (y - x)
      rw [one_smul] at this; exact HasDerivAt.const_add x this
  have e1 : f y = g 1 := by simp [g]
  have e2 : f x = g 0 := by simp [g]
  rw [e1, e2]
  have h2 : ∃ c ∈ Set.Ioo 0 1, g' c = (g 1 - g 0) / (1 - 0) := by
    apply exists_hasDerivAt_eq_slope
    · linarith
    · have : ∀ x ∈ Icc 0 1, HasDerivAt g (g' x) x := by
        intro x hx
        exact (h1 x hx)
      exact HasDerivAt.continuousOn this
    · intro x hx
      have : x ∈ Icc 0 1 := by simp at hx; simp; constructor <;> linarith
      exact h1 x this
  simp; simp at h2; apply h2

end expansion
