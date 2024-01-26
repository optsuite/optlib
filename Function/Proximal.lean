/-
Copyright (c) 2024 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Shengyang Xu
-/
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.Convex.Basic
import Analysis.Calculation
import Function.Subgradient
import Mathlib.Data.Set.Pointwise.SMul
import Optimality.Optimality_Condition_of_Unconstrained_Problem
import Function.Lsmooth
import Function.StronglyConvex

/-!
 proximal operator
-/
noncomputable section

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {x y y₁ y₂: E} {s : Set E} {f : E → ℝ}

/-
  a point satisfies the proximal property if it is a minimizer of the function f(u)+1/2‖u-x‖²
-/
def prox_prop (f : E → ℝ) (x : E) (xm : E) : Prop :=
  IsMinOn (fun u ↦ f u + ‖u - x‖ ^ 2 / 2) univ xm

/-
  the set of all points that satisfy the proximal property
-/
def prox_set (f : E → ℝ) (x : E) : Set E := {u | prox_prop f x u}

/-
  if the proximal set is nonempty then we can choose the point that satisfies the proximal property
-/
def prox_point (f : E → ℝ) (x : E) (h : ∃ y, prox_set f x y) : E :=
  Classical.choose h

lemma strongconvex_of_convex_add_sq (f : E → ℝ) (x : E) (hfun : ConvexOn ℝ univ f) :
    StrongConvexOn univ (1 : ℝ) fun u ↦ f u + ‖u - x‖ ^ 2 / 2 := by
  rw [ConvexOn] at hfun
  rcases hfun with ⟨conv, hfun⟩
  rw [StrongConvexOn, UniformConvexOn]
  constructor
  · exact conv
  · intro y yin z zin a b anneg bnneg absum1; simp
    rw [mul_add, add_assoc, add_comm (a * (‖y - x‖ ^ 2 / 2)), ← add_assoc]
    rw [mul_add, ← add_assoc, ← add_sub _ (a * (‖y - x‖ ^ 2 / 2)), add_assoc]
    apply add_le_add
    · rw [← smul_eq_mul, ← smul_eq_mul]
      apply hfun yin zin anneg bnneg absum1
    · field_simp; rw [div_le_div_right, add_sub]
      have eq1 : a • y + b • z - x = a • (y - x) + b • (z - x) := by
        rw [smul_sub, smul_sub, add_comm_sub, sub_sub, ← add_smul, add_comm b a]
        rw [absum1, one_smul, ← add_sub]
      have eq2 (u v : E) : ‖a • u + b • v‖ ^ 2 = b * ‖v‖ ^ 2
        + a * ‖u‖ ^ 2 - a * b * ‖u - v‖ ^ 2 := by
        rw [norm_add_sq_real, norm_sub_sq_real]
        rw [inner_smul_left, inner_smul_right, norm_smul, norm_smul]; field_simp
        rw [add_comm (b * ‖v‖ ^ 2), mul_pow, sq_abs, mul_pow, sq_abs]
        rw [mul_add, ← sub_sub, mul_sub, ← sub_add]
        rw [add_sub_right_comm, add_sub_right_comm, ← sub_mul, ← add_sub, ← sub_mul]
        nth_rw 3 [← mul_one a]; rw [← absum1, mul_add]
        nth_rw 5 [← mul_one b]; rw [← absum1, mul_add, mul_comm b a]
        rw [pow_two, pow_two b]; simp; rw [add_right_comm, add_left_cancel_iff]
        rw [mul_mul_mul_comm, mul_comm a 2, mul_assoc]
      have eq3 : y - z = (y - x) - (z - x) := by simp
      have eq4 (u v : E) : ‖a • u + b • v‖ ^ 2 ≤ b * ‖v‖ ^ 2
        + a * ‖u‖ ^ 2 - a * b * ‖u - v‖ ^ 2 := by rw [eq2]
      let u := y - x
      let v := z - x
      rw [eq1, eq3];
      show ‖a • u + b • v‖ ^ 2 ≤ b * ‖v‖ ^ 2 + a * ‖u‖ ^ 2 - a * b * ‖u - v‖ ^ 2
      apply eq4 u v
      simp

lemma gradient_of_sq : ∀ u : E,
    HasGradientAt (fun u ↦ ‖u - x‖ ^ 2 / 2) (u - x) u := by
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
    let v := x' - x
    rw [← real_inner_smul_left]
    have eq2 : s - x' = u - v := by simp
    have eq3 : x' - s = v - u := by simp
    rw [eq2, eq3]
    show |‖v‖ ^ 2 - ‖u‖ ^ 2 - inner ((2 : ℝ) • u) (v - u)| / 2 ≤ e * ‖u - v‖
    calc
      |‖v‖ ^ 2 - ‖u‖ ^ 2 - inner ((2 : ℝ) • u) (v - u)| / 2 ≤ (e * ‖u - v‖) / 2 := by
        rw [div_le_div_right]
        apply eq1; simp; apply dles; simp
      _ ≤ e * ‖u - v‖ := by
        field_simp

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
  let liminf := Filter.liminf (fun n ↦ f (xn n).1) Filter.atTop
  have aux : Filter.Tendsto (fun n ↦ (xn n).2) Filter.atTop (nhds p.2) ↔
        ∀ ε > 0, ∃ N, ∀ n ≥ N, (fun n ↦ (xn n).2) n ∈ Ioo (p.2 - ε) (p.2 + ε) := by
      have : Filter.atTop.HasBasis (fun _ : ℕ ↦ True) Ici := Filter.atTop_basis
      rw [this.tendsto_iff (nhds_basis_Ioo_pos p.2)]
      simp
  have ieq1 : f p.1 ≤ liminf := by
    by_contra h; push_neg at h
    let t := (liminf + f p.1) / 2
    have tin : t < f p.1 := add_div_two_lt_right.2 h
    specialize hc t tin
    have ieq2 : t ≤ liminf := by
      apply Filter.le_liminf_of_le
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
        show ∀ᶠ (n : ℕ) in Filter.atTop, auxle (xn n).1
        apply Filter.Tendsto.eventually xtend
        let auxlt := fun x : E ↦ (t < f x)
        have le_of_lt : ∀ x : E, auxlt x → auxle x := by
          simp; intro x cd; exact le_of_lt cd
        apply Filter.Eventually.mono hc le_of_lt
    contrapose! ieq2
    apply left_lt_add_div_two.2 h
  have ieq3 : liminf ≤ p.2 := by
    have ieq4 : Filter.liminf (fun n ↦ (xn n).2) Filter.atTop = p.2 := by
      apply Filter.Tendsto.liminf_eq ytend
    rw [← ieq4]
    apply Filter.liminf_le_liminf
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

theorem prox_well_define' (f : E → ℝ) (x : E) (hfun : ConvexOn ℝ univ f)
    (_ : LowerSemicontinuousOn f univ) (h₁ : prox_prop f x y₁)
    (h₂ : prox_prop f x y₂) : y₁ = y₂ := by
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let m := (1 : ℝ)
  have gsconv : StrongConvexOn univ m g := by
    apply strongconvex_of_convex_add_sq
    show ConvexOn ℝ univ f; apply hfun
  rw [prox_prop] at h₁
  rw [prox_prop] at h₂
  apply Strongly_Convex_Unique_Minima gsconv
  apply h₁; apply h₂; simp; simp; norm_num


section properties

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {x y y₁ y₂: E} {s : Set E} {f : E → ℝ} {u : E} {t : ℝ}

open Set InnerProductSpace

lemma convex_of_norm_sq {s : Set E} (x : E) (conv: Convex ℝ s) :
    ConvexOn ℝ s (fun (u : E) ↦ ‖u - x‖ ^ 2 / 2) := by
  rw [ConvexOn]; use conv
  intro y _ z _ a b anneg bnneg absum1
  field_simp
  have eq1 : a • y + b • z - x = a • (y - x) + b • (z - x) := by
    rw [smul_sub, smul_sub, add_comm_sub, sub_sub, ← add_smul, add_comm b a]
    rw [absum1, one_smul, ← add_sub]
  rw [eq1]
  have ieq1 (u v : E) : ‖a • u + b • v‖ ^ 2 / 2 ≤ (a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2) / 2 := by
    rw [div_le_div_right, norm_add_sq_real, add_comm, ← add_assoc]
    rw [norm_smul, norm_smul, mul_pow, mul_pow]; simp
    nth_rw 3 [← mul_one a]; nth_rw 3 [← one_mul b]
    rw [← absum1]; ring_nf; rw [add_right_comm]
    apply add_le_add_right
    rw [add_comm]; apply add_le_add_right
    calc
      inner (a • u) (b • v) * 2 ≤ ‖a • u‖ * ‖b • v‖ * 2 := by
        rw [mul_le_mul_right]
        apply real_inner_le_norm
        simp
      _ = a * b * (2 * ‖u‖ * ‖v‖) := by
        rw [norm_smul, norm_smul]; simp
        rw [abs_of_nonneg anneg, abs_of_nonneg bnneg]; ring
      _ ≤ a * b * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
        by_cases a * b > 0
        · rw [mul_le_mul_left]
          apply two_mul_le_add_pow_two
          linarith
        · have ieq2 : 0 ≤ a * b := by apply mul_nonneg anneg bnneg
          have ieq3 : 0 = a * b := by linarith
          rw [← ieq3]; simp
      _ = b * ‖v‖ ^ 2 * a + b * a * ‖u‖ ^ 2 := by ring
    simp
  apply ieq1

lemma Subderivat_eq_SubderivWithinAt_univ (f : E → ℝ) :
    SubderivWithinAt f univ u = SubderivAt f u := by
    apply subset_antisymm
    · intro p pin
      rw [SubderivWithinAt] at pin
      rw [← mem_SubderivAt, ← hasSubgradientWithinAt_univ]
      apply pin
    · intro p pin
      rw [← mem_SubderivAt, ← hasSubgradientWithinAt_univ] at pin;
      rw [SubderivWithinAt]
      apply pin

end properties

end
