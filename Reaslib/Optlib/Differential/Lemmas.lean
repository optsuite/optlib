/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.Normed.Lp.ProdLp
import Reaslib.Optlib.Differential.Calculation

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
section continuous

variable {E : Type*} [NormedAddCommGroup E] {f : E → ℝ} {x y x' : E}

open Set InnerProductSpace Topology Filter
set_option linter.unusedVariables false
/-
  The epigraph of under-bounded lowersemicontinuous function is closed
-/
lemma bounded_lowersemicontinuous_to_epi_closed (f : E → ℝ) (hc : LowerSemicontinuousOn f univ)
    (underboundf : ∃ b : ℝ, ∀ x : E, b ≤ f x) :
    IsClosed {p : (E × ℝ) | f p.1 ≤ p.2} := by
  apply IsSeqClosed.isClosed
  intro xn p xnin xntend
  simp
  have xncond : ∀ (n : ℕ), f (xn n).1 ≤ (xn n).2 := by
    intro n; specialize xnin n; simp at xnin
    exact xnin
  rw [Prod.tendsto_iff] at xntend
  rcases xntend with ⟨xtend, ytend⟩
  rw [LowerSemicontinuousOn] at hc
  specialize hc p.1
  simp at hc; rw [LowerSemicontinuousWithinAt, nhdsWithin_univ] at hc
  let linf := liminf (fun n ↦ f (xn n).1) atTop
  have aux : Tendsto (fun n ↦ (xn n).2) atTop (nhds p.2) ↔
        ∀ ε > 0, ∃ N, ∀ n ≥ N, (fun n ↦ (xn n).2) n ∈ Ioo (p.2 - ε) (p.2 + ε) := by
      have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
      rw [this.tendsto_iff (nhds_basis_Ioo_pos p.2)]
      simp
  have ieq1 : f p.1 ≤ linf := by
    by_contra h; push_neg at h
    let t := (linf + f p.1) / 2
    have tin : t < f p.1 := add_div_two_lt_right.2 h
    specialize hc t tin
    have ieq2 : t ≤ linf := by
      apply le_liminf_of_le
      · rw [Filter.IsCoboundedUnder, Filter.IsCobounded]
        rcases underboundf with ⟨bf, condf⟩
        use p.2 + 1; simp; intro a N condb
        rw [aux] at ytend
        specialize ytend 1; simp at ytend
        rcases ytend with ⟨N0, sup⟩
        let M := max N N0
        specialize condb M (le_max_left N N0)
        specialize sup M (le_max_right N N0)
        linarith [condb, xncond M, sup.2]
      · let auxle := fun x : E ↦ (t ≤ f x)
        suffices ∀ᶠ (n : ℕ) in atTop, auxle (xn n).1 by exact this
        apply Tendsto.eventually xtend
        let auxlt := fun x : E ↦ (t < f x)
        have le_of_lt : ∀ x : E, auxlt x → auxle x := by
          simp [auxlt]; intro x cd; exact le_of_lt cd
        apply Eventually.mono hc le_of_lt
    contrapose! ieq2
    apply left_lt_add_div_two.2 h
  have ieq3 : linf ≤ p.2 := by
    have ieq4 : liminf (fun n ↦ (xn n).2) atTop = p.2 := Tendsto.liminf_eq ytend
    rw [← ieq4]
    apply liminf_le_liminf
    simp; use 1
    intro b _; exact xncond b
    rw [Filter.IsBoundedUnder, Filter.IsBounded]
    rcases underboundf with ⟨bf, condf⟩
    use bf; simp; use 0; intro b; simp; exact condf (xn b).1
    rw [Filter.IsCoboundedUnder, Filter.IsCobounded]
    use p.2 + 1; simp; intro a N condb
    rw [aux] at ytend
    specialize ytend 1; simp at ytend
    rcases ytend with ⟨N0, sup⟩
    let M := max N N0
    specialize condb M (le_max_left N N0)
    specialize sup M (le_max_right N N0)
    linarith [condb, sup.2]
  linarith

theorem ContinuousAt_Convergence (h : ContinuousAt f x) : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ (x' : E), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε:= by
  rw [continuousAt_def] at h
  intro ε epos
  let A := Metric.ball (f x) ε
  specialize h A (Metric.ball_mem_nhds (f x) epos)
  rw [Metric.mem_nhds_iff] at h
  rcases h with ⟨δ, dpos, h⟩
  use (δ /2); constructor
  · exact half_pos dpos
  intro x' x1le
  have H1: x' ∈ Metric.ball x δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub]
    apply lt_of_le_of_lt x1le
    exact half_lt_self dpos
  exact LT.lt.le (h H1)

theorem Convergence_ContinuousAt (h : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
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
  · exact dpos
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

theorem ContinuousAt_iff_Convergence : ContinuousAt f x ↔ ∀ ε > (0 : ℝ),
    ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε:= by
  constructor
  · apply ContinuousAt_Convergence
  apply Convergence_ContinuousAt

lemma continuous (h : ContinuousAt f x) : ∀ ε > 0, ∃ δ > 0, ∀ (y : E), ‖y - x‖ < δ
    → ‖f y - f x‖ < ε := by
  rw [ContinuousAt_iff_Convergence] at h
  intro a ha; specialize h (a / 2) (by linarith); rcases h with ⟨δ, ⟨h₁, h₂⟩⟩
  use δ; constructor
  · assumption
  intro y hy;rw [norm_sub_rev] at hy; specialize h₂ y (by linarith); linarith

lemma continuous_positive_neighborhood (h : ContinuousAt f x) (hx : f x > 0) :
    ∃ ε > (0 : ℝ), ∀ (y : E), ‖y - x‖ < ε → f y > 0 := by
  obtain ⟨δ, hδ1, hδ2⟩ := continuous h (f x / 2) (half_pos hx)
  use δ; constructor
  · assumption
  intro y hy; specialize hδ2 y hy
  simp at hδ2;
  obtain hc := neg_lt_of_abs_lt hδ2
  linarith

lemma continuous_positive_direction
    [NormedSpace ℝ E] (h : ContinuousAt f x) (hx : f x > 0) (v : E) :
    ∃ ε > (0 : ℝ), ∀ t ∈ Icc 0 ε, f (x + t • v) > 0 := by
  obtain ⟨δ, hδ1, hδ2⟩ := continuous_positive_neighborhood h hx
  by_cases hv : v = 0
  · rw [hv]; simp; use 1; constructor
    · linarith
    intro t _ _; exact hx
  have : ‖v‖ > 0 := norm_pos_iff.mpr hv
  use δ / (2 * ‖v‖); constructor
  · positivity
  intro y hy
  obtain hδ2 := hδ2 (x + y • v)
  simp at hδ2
  have : ‖y • v‖ < δ := by
    simp at hy; rw [norm_smul]; simp; rw [abs_of_nonneg hy.1]
    calc
      _ ≤ δ / (2 * ‖v‖) * ‖v‖ := (mul_le_mul_iff_of_pos_right this).mpr hy.2
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  exact hδ2 this

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

theorem deriv_function_comp_segment' (s : Set E) (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x) (x y : E) (hx : x ∈ s) (hy : y ∈ s) :
    ∀ t₀, t₀ ∈ Set.Icc 0 1 → HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x)))
      ((fun t : ℝ ↦ (f' (x + t • (y - x)) (y - x))) t₀) t₀ := by
  let h := fun t : ℝ ↦ x + t • (y - x)
  have h_deriv : ∀ t : ℝ,  HasDerivAt h (y - x) t := by
    intro t
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have : (fun z => h (t + z) - h t - z • (y - x)) = (fun z => 0) := by
      ext z; simp [h]
      rw [add_smul, add_comm, ← add_sub, sub_self, add_zero, sub_self]
    simp [this]
  have H₂ : ∀ t₀ : ℝ, t₀ ∈ Set.Icc 0 1 → HasDerivAt (f ∘ h) (f' (x + t₀ • (y - x)) (y - x)) t₀ := by
    intro t₀ ht₀
    have : x + t₀ • (y - x) ∈ s := by
      apply Convex.add_smul_sub_mem hs hx hy; simp; simp at ht₀
      constructor <;> linarith
    apply HasFDerivAt.comp_hasDerivAt
    · apply hf (x + t₀ • (y - x)) this
    · apply h_deriv t₀
  intro t₀ ht₀
  apply H₂ t₀ ht₀

lemma interior_exist_local_fderiv {g : E → ℝ} {f : E → (E →L[ℝ] ℝ)} (s : Set E)
    (hg : ∀ x ∈ s, HasFDerivAt g (f x) x) (y : E) (hy : y ∈ interior s) :
    ∀ᶠ (z : E) in nhds y, HasFDerivAt g (f z) z := by
  apply eventually_nhds_iff.mpr
  rw [mem_interior] at hy
  rcases hy with ⟨t, ht, ht2, ht3⟩
  use t; constructor
  · exact fun k hk ↦ hg k (ht hk)
  constructor <;> assumption

lemma convex_segment_interior (s : Set E) (hs : Convex ℝ s) (x y : E) (hx : x ∈ interior s)
    (hy : y ∈ interior s) (t : ℝ) (ht : t ∈ Set.Icc 0 1) : x + t • (y - x) ∈ interior s := by
  rcases ht with ⟨ht1, ht2⟩
  by_cases ht : t = 0
  · rw [ht]; simpa
  apply Convex.add_smul_mem_interior hs (interior_subset hx) (by simpa)
  constructor
  · exact lt_of_le_of_ne ht1 fun a ↦ ht (id (Eq.symm a))
  linarith


theorem deriv_function_comp_segment_aux'' {g : E → ℝ} {f : E → (E →L[ℝ] ℝ)}
    {f' : E → (E →L[ℝ] E →L[ℝ] ℝ)} (s : Set E) (hs : Convex ℝ s)
    (hg : ∀ x ∈ s, HasFDerivAt g (f x) x) (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (x y : E) (xs : x ∈ interior s) (ys : y ∈ interior s) (hxy : x ≠ y) :
    ∀ t₀, t₀ ∈ Set.Icc 0 1 → HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x)) (y - x))
        (f' (x + t₀ • (y - x)) (y - x) (y - x)) t₀ := by
  let h := fun t : ℝ ↦ x + t • (y - x)
  have hx : x ∈ s := interior_subset xs
  have hy : y ∈ s := interior_subset ys
  have h_deriv : ∀ t : ℝ,  HasDerivAt h (y - x) t := by
    intro t
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have : (fun z => h (t + z) - h t - z • (y - x)) = (fun z => 0) := by
      ext z; simp [h]
      rw [add_smul, add_comm, ← add_sub, sub_self, add_zero, sub_self]
    simp [this]
  intro t₀ ht₀
  let g1 := fun z : E ↦ f z (y - x)
  have hg : HasFDerivAt (fun z ↦ (f z) (y - x))
      ((f' (x + t₀ • (y - x))) (y - x)) (x + t₀ • (y - x)) := by
    have ins : x + t₀ • (y - x) ∈ s := by
      apply Convex.add_smul_sub_mem hs hx hy; simp; simp at ht₀
      constructor <;> linarith
    obtain hf1 := hf (x + t₀ • (y - x)) ins
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at hf1 ⊢
    intro c hc;
    have neq : ‖y - x‖ > 0 := by
      exact norm_sub_pos_iff.mpr (id (Ne.symm hxy))
    have pos : c / ‖y - x‖ > 0 := by positivity
    specialize hf1 pos
    suffices ∀ᶠ (x_1 : E) in nhds 0,
        ‖(f (x + t₀ • (y - x) + x_1)) (y - x) - (f (x + t₀ • (y - x))) (y - x)
        - ((f' (x + t₀ • (y - x))) x_1) (y - x)‖ ≤ c * ‖x_1‖ by
      apply Filter.Eventually.mono this
      intro z hz
      apply le_of_eq_of_le _ hz
      apply congrArg; simp
      have hf' : ∀ᶠ (y : E) in nhds (x + t₀ • (y - x)), HasFDerivAt g (f y) y := by
        apply interior_exist_local_fderiv s hg
        · exact convex_segment_interior s hs x y xs ys t₀ ht₀
      have (p q : E) : f' (x + t₀ • (y - x)) p q = f' (x + t₀ • (y - x)) q p := by
        apply second_derivative_symmetric_of_eventually hf' (hf (x + t₀ • (y - x)) ins) p q
      rw [this z y, this z x]
    suffices ∀ᶠ (x_1 : E) in nhds 0, ‖(f (x + t₀ • (y - x) + x_1)) -
        (f (x + t₀ • (y - x))) - ((f' (x + t₀ • (y - x))) x_1)‖ * ‖(y - x)‖ ≤ c * ‖x_1‖ by
      apply Filter.Eventually.mono this
      intro z hz
      apply le_trans _ hz
      have : (f (x + t₀ • (y - x) + z)) (y - x) - (f (x + t₀ • (y - x))) (y - x)
          - ((f' (x + t₀ • (y - x))) z) (y - x) = (f (x + t₀ • (y - x) + z) -
          f (x + t₀ • (y - x)) - (f' (x + t₀ • (y - x))) z) (y - x) := by simp
      rw [this]; exact ContinuousLinearMap.le_opNorm _ _
    apply Filter.Eventually.mono hf1
    intro z hz; rwa [div_mul_eq_mul_div, le_div_iff₀ neq] at hz
  have : g1 ∘ h = fun t : ℝ ↦ f (x + t • (y - x)) (y - x) := rfl
  rw [← this]
  apply HasFDerivAt.comp_hasDerivAt
  · exact hg
  · exact h_deriv t₀

theorem deriv_function_comp_segment'' {g : E → ℝ} {f : E → (E →L[ℝ] ℝ)}
    {f' : E → (E →L[ℝ] E →L[ℝ] ℝ)} (s : Set E) (hs : Convex ℝ s)
    (hg : ∀ x ∈ s, HasFDerivAt g (f x) x) (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (x y : E) (xs : x ∈ interior s) (ys : y ∈ interior s) :
    ∀ t₀, t₀ ∈ Set.Icc 0 1 → HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x)) (y - x))
        (f' (x + t₀ • (y - x)) (y - x) (y - x)) t₀ := by
  by_cases h : x ≠ y
  · exact deriv_function_comp_segment_aux'' s hs hg hf x y xs ys h
  push_neg at h; rw [h, sub_self]; simp
  intro t _ _; exact hasDerivAt_const t 0

theorem HasFDeriv_Convergence (h : HasFDerivAt f (f' x) x) :
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
  · exact (half_pos e1pos)
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
  · apply dpos
  intro x' x1mem
  have h1: ‖x - x'‖ ≤ δ:= by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm] at x1mem
    exact LT.lt.le x1mem
  specialize h x' h1
  rw[Set.mem_setOf, norm_sub_rev x']
  apply h

theorem HasFDeriv_iff_Convergence_Point {f'x : (E →L[ℝ] ℝ)} :
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
  · apply HasFDeriv_Convergence
  apply Convergence_HasFDeriv

lemma expansion_fderiv (s : Set E) (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x) (x y : E) (hx : x ∈ s) (hy : y ∈ s) :
    ∃ t : ℝ, t > 0 ∧ t < 1 ∧ f y = f x + (f' (x + t • (y - x))) (y - x) := by
  let g := fun r : ℝ ↦ f (x + r • (y - x))
  let g' := fun r : ℝ ↦ ((f' (x + r • (y - x))) (y - x) : ℝ)
  have h1 : ∀ r, r ∈ Set.Icc 0 1 → HasDerivAt g (g' r) r := by
    intro r hr
    apply deriv_function_comp_segment' s hs hf x y hx hy r hr
  have e1 : f (y) = g 1 := by simp [g]
  have e2 : f x = g 0 := by simp [g]
  have e3 : ∀ t, (f' (x + t • (y - x))) (y - x) = g' t := by
    intro t; simp [g']
  rw [e1, e2]
  have : ∃ c ∈ Set.Ioo 0 1, g' c = (g 1 - g 0) / (1 - 0) := by
    -- apply exists_hasDerivAt_eq_slope g g' (by norm_num)
    -- goal : ∃ c ∈ Set.Ioo 0 1, g' c = (g 1 - g 0) / (1 - 0)
    apply exists_hasDerivAt_eq_slope g g' (by norm_num)
    · have : ∀ x ∈ Set.Icc 0 1, HasDerivAt g (g' x) x := by
        intro x hx
        exact (h1 x hx)
      exact HasDerivAt.continuousOn this
    · intro x hx; exact h1 x (by simp at hx; constructor <;> linarith)
  rcases this with ⟨c, ⟨c1, c2⟩, h2⟩
  use c
  constructor
  · exact c1
  constructor
  · exact c2
  rw [e3 c]; simp [h2]

private lemma one_minus_id_deriv (t : ℝ) : HasDerivAt (fun (t : ℝ) ↦ 1 - t) (-1) t := by
  rw [← zero_sub]
  apply HasDerivAt.sub
  · exact hasDerivAt_const t 1
  exact hasDerivAt_id' t

private lemma pow_two_one_minus (t : ℝ) :
    HasDerivAt (fun (t : ℝ) ↦ t ^ 2) (2 * (1 - t)) (1 - t) := by
  obtain h1 := hasDerivAt_pow 2 (1 - t)
  simp at h1; exact h1

lemma one_dimension_expansion {f : ℝ → ℝ} {f' : ℝ → ℝ} {f'' : ℝ → ℝ}
    (hd1 : ∀ t ∈ Set.Icc 0 1, HasDerivAt f (f' t) t)
    (hd2 : ∀ t ∈ Set.Icc 0 1, HasDerivAt f' (f'' t) t) :
    ∃ t : ℝ, t > 0 ∧ t < 1 ∧ (f 1 = f 0 + f' 0 + f'' t / 2) := by
  let F := fun t ↦ f 1 - f t - (1 - t) * f' t
  let G := fun (t : ℝ) ↦ (1 - t) ^ 2
  have eq1 : F 1 - F 0 = - f 1 + f 0 + f' 0 := by simp [F]; ring_nf
  have eq2 : G 1 - G 0 = - 1 := by simp [G]
  let F' := fun t ↦ - (1 - t) * f'' t
  let G' := fun (t : ℝ) ↦ - 2 * (1 - t)
  have h1 : ∀ t ∈ Set.Icc 0 1, HasDerivAt F (F' t) t := by
    intro t ht
    simp [F, F']
    have : ((t - 1) * f'' t) = - f' t - (-1 * (f' t) + (1 - t) * f'' t) := by ring
    rw [this]; apply HasDerivAt.sub
    rw [← zero_sub]; apply HasDerivAt.sub
    exact hasDerivAt_const t (f 1)
    exact hd1 t ht
    apply HasDerivAt.mul
    · exact one_minus_id_deriv t
    exact hd2 t ht
  have h2 : ∀ t ∈ Set.Icc 0 1, HasDerivAt G (G' t) t := by
    intro t _
    simp [G, G']
    have e1 : (fun t ↦ (1 - t) ^ 2) = (fun (t : ℝ) ↦ t ^ 2) ∘ (fun (t : ℝ) ↦ 1 - t) := rfl
    have e2 : -(2 * (1 - t)) = (2 * (1 - t)) * -1 := by ring
    rw [e1, e2]; apply HasDerivAt.comp
    exact pow_two_one_minus _
    exact one_minus_id_deriv _
  have h3 : ContinuousOn F (Set.Icc 0 1) := HasDerivAt.continuousOn h1
  have h4 : ContinuousOn G (Set.Icc 0 1) := HasDerivAt.continuousOn h2
  obtain ⟨c, ⟨hc, eq⟩⟩ := exists_ratio_hasDerivAt_eq_ratio_slope F F' zero_lt_one h3
    (fun a b ↦ h1 a (Set.mem_Icc_of_Ioo b)) G G' h4 (fun a b ↦ h2 a (Set.mem_Icc_of_Ioo b))
  use c; simp at hc; constructor
  · exact hc.1
  constructor
  · exact hc.2
  rw [eq1, eq2] at eq; simp [F', G'] at eq
  have : (c - 1) * (f'' c / 2) = (c - 1) * (f 1 - f 0 - f' 0) := by
    rw [mul_div, eq]; field_simp; ring_nf
  suffices f'' c / 2 = f 1 - f 0 - f' 0 by rw [this]; ring_nf
  apply mul_left_cancel₀ (by linarith) this


variable {f'' : E → (E →L[ℝ] E →L[ℝ] ℝ)}
lemma expansion_fderiv_second (s : Set E) (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x) (h2 : ∀ x ∈ s, HasFDerivAt f' (f'' x) x)
    (x y : E) (hx : x ∈ interior s) (hy : y ∈ interior s) : ∃ (v : ℝ), v ∈ Set.Ioo 0 1 ∧ f y =
    f x + (f' x) (y - x) + f'' (x + v • (y - x)) (y - x) (y - x) / 2 := by
  let g := fun r : ℝ ↦ f (x + r • (y - x))
  let g' := fun r : ℝ ↦ (f' (x + r • (y - x))) (y - x)
  let g'' := fun r : ℝ ↦ (f'' (x + r • (y - x))) (y - x) (y - x)
  have g1 : ∀ t ∈ Set.Icc 0 1, HasDerivAt g (g' t) t := by
    exact fun t a ↦ deriv_function_comp_segment'
      s hs hf x y (interior_subset hx) (interior_subset hy) t a
  have g2 : ∀ t ∈ Set.Icc 0 1, HasDerivAt g' (g'' t) t := by
    exact fun t a ↦ deriv_function_comp_segment'' s hs hf h2 x y hx hy t a
  obtain ⟨t, ht1, ht2, ht3⟩ := one_dimension_expansion g1 g2
  use t; constructor
  · exact ⟨ht1, ht2⟩
  simp [g, g', g''] at ht3
  simpa

end derivative

section gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {x p y : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open Topology InnerProductSpace Set Filter

theorem HasGradient_Convergence (h : HasGradientAt f (f' x) x) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E, ‖x - x'‖ ≤ δ
  → ‖f x' - f x - inner (ℝ) (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  rw [hasGradientAt_iff_hasFDerivAt] at h
  suffices ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ
    → ‖f x' - f x - ((toDual ℝ E) (f' x)) (x' - x)‖ ≤ ε * ‖x - x'‖ by exact this
  apply HasFDeriv_Convergence
  exact h

theorem Convergence_HasGradient (h : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
  ‖x - x'‖ ≤ δ → ‖f x' - f x - inner (ℝ) (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖) :
    HasGradientAt f (f' x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact HasFDeriv_iff_Convergence_Point.mpr h

theorem HasGradient_iff_Convergence_Point {f'x : E} :
      HasGradientAt f f'x x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
  ‖x - x'‖ ≤ δ → ‖f x' - f x - inner (ℝ) (f'x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  · intro h; apply HasGradient_Convergence
    exact h
  · apply Convergence_HasGradient

theorem HasGradient_iff_Convergence :
      HasGradientAt f (f' x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x' : E,
  ‖x - x'‖ ≤ δ → ‖f x' - f x - inner (ℝ) (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  · apply HasGradient_Convergence
  apply Convergence_HasGradient

lemma gradient_norm_sq_eq_two_self (x : E) :
    HasGradientAt (fun x ↦ ‖x‖ ^ 2) ((2 : ℝ) • x) x := by
  apply Convergence_HasGradient
  simp
  intro e ep
  use e
  constructor
  · linarith
  · intro x' dles
    rw [← norm_neg (x - x'), neg_sub] at dles
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_sub_right]
    rw [real_inner_smul_left, real_inner_smul_left]; ring_nf
    rw [add_sub, add_sub_right_comm, mul_two, ← sub_sub]
    rw [← inner_sub_left, sub_add, ← inner_sub_right]
    rw [real_inner_comm, ← inner_sub_left, real_inner_self_eq_norm_sq]
    rw [abs_of_nonneg, pow_two, ← norm_neg (x - x'), neg_sub]
    · apply mul_le_mul_of_nonneg_right dles (norm_nonneg (x' - x))
    apply pow_two_nonneg

lemma gradient_of_inner_const (x : E) (a : E) :
    HasGradientAt (fun x ↦ (inner (ℝ) a x : ℝ)) a x := by
  apply HasGradient_iff_Convergence_Point.mpr
  simp only [gt_iff_lt, Real.norm_eq_abs]
  intros ε εpos
  use (1 : ℝ)
  constructor
  · simp
  · intro x' _
    rw[← inner_sub_right, ← inner_sub_right, sub_self, inner_zero_right]
    simp; positivity

lemma gradient_of_inner_const' (x : E) (a : E) :
    HasGradientAt (fun x ↦ (inner (ℝ) x a : ℝ)) a x := by
  have : (fun x ↦ (inner (ℝ) x a : ℝ)) = fun x ↦ (inner (ℝ) a x : ℝ) := by
    ext y; exact real_inner_comm a y
  rw [this]; apply gradient_of_inner_const

lemma gradient_of_const_mul_norm (l : ℝ) (z : E) :
    HasGradientAt (fun (x : E) => l / 2 * ‖x‖ ^ 2) (l • z) z := by
  let h := fun x : E => ‖x‖ ^ 2
  have e1 : (l • z) = (l / 2) • (2 : ℝ) • z := by rw [smul_smul]; simp
  have : (fun (x : E) => l / 2 * ‖x‖ ^ 2) = (fun (x : E) => (l / 2) • h x) := by
    ext x; simp only [h]; rfl
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
      |‖v‖ ^ 2 - ‖u‖ ^ 2 - inner (ℝ) ((2 : ℝ) • u) (v - u)| ≤ e * ‖u - v‖ := by
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
    suffices |‖v‖ ^ 2 - ‖u‖ ^ 2 - inner (ℝ) ((2 : ℝ) • u) (v - u)| / 2 ≤ e * ‖u - v‖ by exact this
    calc
      |‖v‖ ^ 2 - ‖u‖ ^ 2 - inner (ℝ) ((2 : ℝ) • u) (v - u)| / 2 ≤ (e * ‖u - v‖) / 2 := by
        apply div_le_div_of_nonneg_right
        · apply eq1; rw [hu, hv]; simp; apply dles
        linarith
      _ ≤ e * ‖u - v‖ := by
        rw [half_le_self_iff]
        apply mul_nonneg (by linarith) (norm_nonneg (u - v))

lemma sub_normsquare_gradient (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) (m : ℝ) :
    ∀ x ∈ s, HasGradientAt (fun x ↦ f x - m / 2 * ‖x‖ ^ 2) (f' x - m • x) x := by
  intro x xs
  apply HasGradientAt.sub
  · apply hf x xs
  · have u := HasGradientAt.const_smul (gradient_norm_sq_eq_two_self x) (m / 2)
    simp at u
    rw [smul_smul, div_mul_cancel_of_invertible] at u
    apply u

/-
If the function f is first-order continuously differentiable, then
the gradient of f is continuous.
-/
lemma gradient_continuous_of_contdiffat {x : E} (f : E → ℝ)
    (h : ContDiffAt ℝ 1 f x) : ContinuousAt (fun x ↦ gradient f x) x := by
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

lemma gradient_continuous_of_contdiffon {x : E} {ε : ℝ} (f : E → ℝ)
    (he : ε > 0) (hf : ContDiffOn ℝ 1 f (Metric.ball x ε)) :
    ContinuousAt (fun x ↦ gradient f x) x := by
  let s := Metric.ball x ε
  have h : ContDiffAt ℝ 1 f x := by
    apply ContDiffOn.contDiffAt hf
    rw [mem_nhds_iff]; use s
    exact ⟨Eq.subset rfl, ⟨Metric.isOpen_ball, Metric.mem_ball_self he⟩⟩
  exact gradient_continuous_of_contdiffat f h

end gradient

section expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x p y : E} {f : E → ℝ} {f' : E → E} {s : Set E}

open InnerProductSpace Set
/-
  For any function f : E → ℝ, where E is a InnerProduct space,
  and for any point x in E and vector p in E,
  if f has a gradient at every point in its domain, then there exists a real number t such that t is
  greater than 0 and less than 1, and f(x + p) is equal
  to f(x) plus the inner product of the gradient of
  f at (x + t * p) with p.
-/

lemma expansion (hf : ∀ x : E, HasGradientAt f (f' x) x) (x p : E) :
  ∃ t : ℝ, t > 0 ∧ t < 1 ∧ f (x + p) = f x + inner (ℝ) (f' (x + t • p)) p := by
  let g := fun r : ℝ ↦ f (x + r • p)
  let g' := fun r : ℝ ↦ (inner (ℝ) (f' (x + r • p)) p : ℝ)
  have h1 : ∀ r , HasDerivAt g (g' r) r := by
    let h := fun r : ℝ ↦ x + r • p
    have : g = f ∘ h := by rfl
    rw [this]; intro r
    have : inner (ℝ) (f' (x + r • p)) p = toDual ℝ E (f' (x + r • p)) p := rfl
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
  have e3 : ∀ t, inner (ℝ) (f' (x + t • p)) p = g' t := by intro t; simp only [g']
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
  constructor
  · exact c1
  constructor
  · exact c2
  rw [e3 c]; simp [h2]

lemma general_expansion (x p : E) (hf : ∀ y ∈ Metric.closedBall x ‖p‖, HasGradientAt f (f' y) y) :
  ∃ t : ℝ, t > 0 ∧ t < 1 ∧ f (x + p) = f x + inner (ℝ) (f' (x + t • p)) p := by
  let g := fun r : ℝ ↦ f (x + r • p)
  let g' := fun r : ℝ ↦ (inner (ℝ) (f' (x + r • p)) p : ℝ)
  have h1 : ∀ r ∈ Icc 0 1, HasDerivAt g (g' r) r := by
    let h := fun r : ℝ ↦ x + r • p
    have : g = f ∘ h := by rfl
    rw [this]; intro r hr
    have : inner (ℝ) (f' (x + r • p)) p = toDual ℝ E (f' (x + r • p)) p := rfl
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
  have e3 : ∀ t, inner (ℝ) (f' (x + t • p)) p = g' t := by intro t; simp only [g']
  rw [e1, e2]
  have : ∃ c ∈ Set.Ioo 0 1, g' c = (g 1 - g 0) / (1 - 0) := by
    apply exists_hasDerivAt_eq_slope g g' (by norm_num)
    · exact HasDerivAt.continuousOn h1
    · intro x hx; apply h1 x
      rcases hx with ⟨hx1, hx2⟩; constructor <;> linarith
  rcases this with ⟨c, ⟨c1, c2⟩, h2⟩
  use c
  constructor
  · exact c1
  constructor
  · exact c2
  rw [e3 c]; simp [h2]

theorem lagrange (hs : Convex ℝ s) (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ∀ x ∈ s, ∀ y ∈ s, ∃ c : ℝ, c ∈ Set.Ioo 0 1 ∧
  inner (ℝ) (f' (x + c • (y - x))) (y - x) = f y - f x := by
  intro x xs y ys
  let g := fun t : ℝ ↦ f (x + t • (y - x))
  let g' := fun t : ℝ ↦ (inner (ℝ) (f' (x + t • (y - x))) (y - x) : ℝ)
  have h1 : ∀ r ∈ Icc 0 1 , HasDerivAt g (g' r) r := by
    let h := fun r : ℝ ↦ (x + r • (y - x))
    have : g = f ∘ h := rfl
    rw [this]; intro t ht
    have : inner (ℝ) (f' (x + t • (y - x))) (y - x) =
      toDual ℝ E (f' (x + t • (y - x))) (y - x) := rfl
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

section ProdLp

variable {E F : Type*}
variable [NormedAddCommGroup E]
variable [NormedAddCommGroup F]
variable {x : E} {y : F} {z : WithLp 2 (E × F)}

open Set Bornology Filter BigOperators Topology

lemma fst_norm_le_prod_L2 (z : WithLp 2 (E × F)) : ‖z.1‖ ≤ ‖z‖ := by
  have h : ‖z.1‖ ^ 2 ≤ ‖z‖ ^ 2 := by linarith [WithLp.prod_norm_sq_eq_of_L2 z, sq_nonneg ‖z.2‖]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  rwa [← pow_two, ← pow_two]

lemma snd_norm_le_prod_L2 (z : WithLp 2 (E × F)) : ‖z.2‖ ≤ ‖z‖ := by
  have h : ‖z.2‖ ^ 2 ≤ ‖z‖ ^ 2 := by linarith [WithLp.prod_norm_sq_eq_of_L2 z, sq_nonneg ‖z.1‖]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  rwa [← pow_two, ← pow_two]

lemma prod_norm_le_block_sum_L2 (z : WithLp 2 (E × F)) : ‖z‖ ≤ ‖z.1‖ + ‖z.2‖ := by
  have : ‖z‖ ^ 2 ≤ (‖z.1‖ + ‖z.2‖) ^ 2:= by
    simp [WithLp.prod_norm_sq_eq_of_L2, add_sq]
    positivity
  apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg (norm_nonneg z.1) (norm_nonneg z.2))
  rwa [← pow_two, ← pow_two]

lemma norm_prod_right_zero (x : E) :
    @norm (WithLp 2 (E × F)) _ ((x, (0 : F)) : WithLp 2 (E × F)) = ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L2] ; simp

lemma norm_prod_left_zero (y : F) :
    @norm (WithLp 2 (E × F)) _ ((0 : E), y) = ‖y‖ := by
  rw [WithLp.prod_norm_eq_of_L2] ; simp

end ProdLp

noncomputable section ProdLp_diff

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {x : E} {y : F} {z : WithLp 2 (E × F)}

instance instNormedSpaceProdL2 : NormedSpace ℝ (WithLp 2 (E × F)) where
  norm_smul_le := by
    intro a b
    have : ‖a • b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
      rw [mul_pow, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.smul_fst, WithLp.smul_snd]
      rw [norm_smul, norm_smul, mul_add, mul_pow, mul_pow]
    exact norm_smul_le a b

instance instIsBoundedLinearMapL2equiv :
    @IsBoundedLinearMap ℝ _ (E × F) _ _ (WithLp 2 (E × F)) _ _ id where
  map_add := fun x ↦ congrFun rfl
  map_smul := fun c ↦ congrFun rfl
  bound := by
    use 2
    constructor
    · norm_num
    · intro z
      rw [Prod.norm_def]
      have h := prod_norm_le_block_sum_L2 z
      simp only [id_eq]
      linarith [h, le_max_left ‖z.1‖ ‖z.2‖, le_max_right ‖z.1‖ ‖z.2‖]

end ProdLp_diff
