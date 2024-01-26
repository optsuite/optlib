/-
Copyright (c) 2024 Chenyi Li, Shengyang Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Shengyang Xu
-/
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Analysis.Calculation
import Analysis.Subgradient
import Analysis.Optimality_Condition_of_Unconstrained_Problem
import Analysis.Lsmooth
import Analysis.Stongly

/-!
 proximal operator
-/
noncomputable section

open Set InnerProductSpace Bornology Topology Filter TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [ProperSpace E]

variable {x y y₁ y₂: E} {s : Set E} {f : E → ℝ} {nes : Nonempty s}

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

lemma gradient_of_sq : ∀ u : E, HasGradientAt (fun u ↦ ‖u - x‖ ^ 2 / 2) (u - x) u := by
  intro s
  apply Convergence_HasGradient
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
        show ∀ᶠ (n : ℕ) in atTop, auxle (xn n).1
        apply Tendsto.eventually xtend
        let auxlt := fun x : E ↦ (t < f x)
        have le_of_lt : ∀ x : E, auxlt x → auxle x := by
          simp; intro x cd; exact le_of_lt cd
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

theorem prox_well_define (f : E → ℝ) (hc : LowerSemicontinuousOn f univ) :
    ∀ x, ∃ y, prox_prop f x y := by
  intro x
  rcases nes with ⟨z, _⟩
  have : Nonempty (SubderivAt f z) := by
    apply SubderivAt.nonempty
  simp at this
  rcases this with ⟨a, ain⟩
  rw [← mem_SubderivAt, HasSubgradientAt] at ain
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let epi := {p : (E × ℝ) | g p.1 ≤ p.2}
  have second_lower_bound (y : E) : g y ≥ f z + inner a (y - z) + ‖y - x‖ ^ 2 / 2 := by
    simp
    specialize ain y; linarith
  have lower_bound (y : E) : f z + inner a (x - z) - ‖a‖ ^ 2 / 2 ≤ g y := by
    have : y - z = x - z + (y - x) := by simp
    specialize second_lower_bound y
    rw [this, inner_add_right, ← add_assoc, add_assoc] at second_lower_bound
    have : 0 ≤ ‖a‖ ^ 2 / 2 + inner a (y - x) + ‖y - x‖ ^ 2 / 2 := by
      field_simp; rw [mul_comm, ← norm_add_sq_real]
      apply div_nonneg (sq_nonneg ‖a + (y - x)‖)
      norm_num
    calc
      f z + inner a (x - z) - ‖a‖ ^ 2 / 2 ≤ f z + inner a (x - z) - ‖a‖ ^ 2 / 2 +
        (‖a‖ ^ 2 / 2 + inner a (y - x) + ‖y - x‖ ^ 2 / 2) := le_add_of_nonneg_right this
      _ = f z + inner a (x - z) + (inner a (y - x) + ‖y - x‖ ^ 2 / 2) := by ring
      _ ≤ g y := second_lower_bound
  have epi_closed : IsClosed epi := by
    apply bounded_lowersemicontinuous_to_epi_closed
    · apply LowerSemicontinuousOn.add hc
      apply lowerSemicontinuousOn_univ_iff.2
      apply Continuous.lowerSemicontinuous
      apply continuous_iff_continuousOn_univ.2
      apply HasGradientAt.continuousOn
      intro u _
      apply gradient_of_sq u
    use (f z + inner a (x - z) - ‖a‖ ^ 2 / 2)
  let S := {y : E| g y ≤ g z + 1}
  let ImS := {g y | y ∈ S}
  have neImS : Set.Nonempty ImS := by
    use g z; simp; use z; simp
  have S_bddbelow : BddBelow ImS := by
    use (f z + inner a (x - z) - ‖a‖ ^ 2 / 2)
    rw [mem_lowerBounds]
    rintro gy ⟨y0, _, gyeq⟩
    rw [← gyeq]; exact lower_bound y0
  have compacts : IsCompact (closure S) := by
    let B := Metric.closedBall (x - a) (‖z - (x - a)‖ + 2)
    have sinb : S ⊆ B := by
      intro u uin
      simp at uin
      apply mem_closedBall_iff_norm.2
      have norm_bound: ‖u - (x - a)‖ ≤ ‖z - (x - a)‖ + 2 := by
        have ieq : f z + inner a (u - z) + ‖u - x‖ ^ 2 / 2 ≤ f z + ‖z - x‖ ^ 2 / 2 + 1 := by
          calc
          f z + inner a (u - z) + ‖u - x‖ ^ 2 / 2 ≤ g u := second_lower_bound u
          _ ≤ f z + ‖z - x‖ ^ 2 / 2 + 1 := uin
        rw [add_assoc, add_assoc, add_le_add_iff_left] at ieq
        have eq : inner a (u - z) + ‖u - x‖ ^ 2 / 2 =
            (‖u - (x - a)‖ ^ 2 - ‖a‖ ^ 2 + 2 * inner (x - z) a) / 2 := by
            field_simp; rw [← sub_add, norm_add_sq_real]; ring_nf
            rw [add_assoc, ← add_mul, ← inner_add_left, add_comm, real_inner_comm]; simp
        rw [eq] at ieq
        have ieq2 : ‖u - (x - a)‖ ^ 2 ≤ ‖z - (x - a)‖ ^ 2 + 2 := by
          field_simp at ieq; rw [div_le_div_right, sub_add, sub_le_iff_le_add] at ieq
          rw [add_right_comm, add_comm (‖z - x‖ ^ 2), norm_sub_rev z x] at ieq
          rw [real_inner_comm, ← norm_sub_sq_real, ← sub_add a, sub_add_comm] at ieq
          rw [sub_add] at ieq; exact ieq; norm_num
        have : |‖z - (x - a)‖ + 2| = ‖z - (x - a)‖ + 2 := by
          apply abs_of_pos; apply add_pos_of_nonneg_of_pos (norm_nonneg (z - (x - a)))
          simp
        rw [← abs_norm, ← this, ← sq_le_sq, add_sq]
        calc
          ‖u - (x - a)‖ ^ 2 ≤ ‖z - (x - a)‖ ^ 2 + 2 := ieq2
          _ ≤ ‖z - (x - a)‖ ^ 2 + 2 * ‖z - (x - a)‖ * 2 + 2 ^ 2 := by
            rw [add_assoc, add_le_add_iff_left]; apply le_add_of_nonneg_of_le
            simp; norm_num
      exact norm_bound
    have compactb : IsCompact B := isCompact_closedBall (x - a) (‖z - (x - a)‖ + 2)
    apply isCompact_closure_of_subset_compact compactb sinb
  rcases exists_seq_tendsto_sInf neImS S_bddbelow with ⟨fx, _, cfx, fxs⟩
  choose x xsub xeq using fxs
  have xsubs : ∀ (n : ℕ), x n ∈ closure S := by
    intro n; apply subset_closure (xsub n)
  rcases IsCompact.tendsto_subseq compacts xsubs with ⟨x', _, k, mono, cxk⟩
  have cfxk : Filter.Tendsto (g ∘ x ∘ k) Filter.atTop (𝓝 (sInf ImS)) := by
    have xkeq : ∀ (n : ℕ), (g ∘ x ∘ k) n = (fx ∘ k) n := fun n => xeq <| k n
    rw [tendsto_congr xkeq]
    apply Tendsto.comp cfx (StrictMono.tendsto_atTop mono)
  have inepi : (x', sInf ImS) ∈ epi := by
    let p := fun c ↦ (((fun n ↦ x n) ∘ k) c, (g ∘ x ∘ k) c)
    have pnin :  ∀ c : ℕ, p c ∈ epi := by simp
    apply IsClosed.isSeqClosed epi_closed pnin
    show Tendsto (fun c ↦ (((fun n ↦ x n) ∘ k) c, (g ∘ x ∘ k) c)) atTop (𝓝 (x', sInf ImS))
    apply Tendsto.prod_mk_nhds cxk cfxk
  have minima_ieq : g x' ≤ sInf ImS := inepi
  have minima : ∀ w : E, g x' ≤ g w := by
      intro w
      by_cases hw : w ∈ S
      · have gwin : g w ∈ ImS := by use w
        have legw : sInf ImS ≤ g w := by
          rw [Real.sInf_le_iff S_bddbelow neImS]
          intro _ epos; use g w; use gwin; linarith
        linarith
      · have gwnin : g z + 1 < g w := by
          simp at hw; simp; exact hw
        have gzin : g z ∈ ImS := by use z; simp
        have legw : sInf ImS ≤ g w := by
          rw [Real.sInf_le_iff S_bddbelow neImS]
          intro _ epos; use g z; use gzin; linarith
        linarith
  use x'; rw [prox_prop, isMinOn_iff]
  intro v _; exact minima v

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

/-
  the definition of the proximal operator for a closed convex function
-/
def prox_point_c (f : E → ℝ) (x : E) (hc : LowerSemicontinuousOn f univ) : E :=
  have h : ∃ y, prox_set f x y := by
    apply prox_well_define f hc x; use s; exact nes
  Classical.choose h

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

theorem prox_iff_subderiv (f : E → ℝ) (hfun : ConvexOn ℝ univ f) :
    ∀ u : E, prox_prop f x u ↔ x - u ∈ SubderivAt f u := by
  intro u; rw [prox_prop, ← HasSubgradientAt_zero_iff_isMinOn, mem_SubderivAt]
  let g := fun u ↦ ‖u - x‖ ^ 2 / 2
  show 0 ∈ SubderivAt (f + g) u ↔ x - u ∈ SubderivAt f u
  rw [← SubderivAt.add]
  have subg : SubderivAt g u = {u - x} := by
    let g' := fun u ↦ u - x
    have gderiv : ∀ x, HasGradientAt g (g' x) x := gradient_of_sq
    have : SubderivWithinAt g univ u = {g' u} := by
      apply SubderivWithinAt_eq_gradient; simp
      have gconv : ConvexOn ℝ univ g := by
        rcases hfun with ⟨conv, _⟩
        apply convex_of_norm_sq
        apply conv
      apply gconv; apply gderiv
    rw [← Subderivat_eq_SubderivWithinAt_univ, this]
  rw [subg]; simp

theorem prox_iff_grad (f : E → ℝ) {f' : E → E} (hfun : ConvexOn ℝ univ f)
    (hdiff : ∀ x, HasGradientAt f (f' x) x) :
    ∀ u : E, prox_prop f x u ↔ f' u = x - u := by
  intro u
  have iff_subderiv : ∀ u : E, prox_prop f x u ↔ x - u ∈ SubderivAt f u := by
    apply prox_iff_subderiv
    apply hfun
  specialize iff_subderiv u
  rw [iff_subderiv, ← Subderivat_eq_SubderivWithinAt_univ]
  have subderiv_eq_gradient : SubderivWithinAt f univ u = {f' u} := by
    apply SubderivWithinAt_eq_gradient; simp
    apply hfun; apply hdiff
  rw [subderiv_eq_gradient]; simp
  apply eq_comm

theorem prox_iff_grad_smul (f : E → ℝ) {f' : E → E} (t : ℝ) (hfun : ConvexOn ℝ univ f)
    (hdiff : ∀ x, HasGradientAt f (f' x) x) (tnonneg : 0 ≤ t) :
    ∀ u : E, prox_prop (t • f) x u ↔ t • f' u = x - u := by
  intro u
  let g := fun u ↦ (t • f) u
  let g' := fun u ↦ t • f' u
  have gconv : ConvexOn ℝ univ g := by
    apply ConvexOn.smul tnonneg hfun
  have gderiv : ∀ x, HasGradientAt g (g' x) x := by
    intro s
    specialize hdiff s
    rw [HasGradient_iff_Convergence_Point] at hdiff
    apply Convergence_HasGradient
    by_cases h : t > 0
    · simp; intro e ep
      have eq1 : 0 < t⁻¹ * e := by
        field_simp; apply div_pos ep h
      specialize hdiff (t⁻¹ * e) eq1
      rcases hdiff with ⟨delta, dpos, cvg⟩
      use delta; simp at h; use dpos
      intro z zled
      specialize cvg z zled; field_simp at cvg
      rw [inner_smul_left]; simp; rw [sub_sub, ← mul_add, ← mul_sub, abs_mul, abs_of_pos h]
      rw [← le_div_iff' h, ← sub_sub]; exact cvg
    · have h0 : t = (0 : ℝ) := by linarith
      simp; intro e ep; use e; use ep
      intro z _; rw [h0]; simp; apply mul_nonneg
      linarith; apply norm_nonneg
  rw [prox_iff_subderiv]
  have : SubderivWithinAt g univ u = {g' u} := by
      apply SubderivWithinAt_eq_gradient; simp
      apply gconv; apply gderiv
  rw [← Subderivat_eq_SubderivWithinAt_univ, this]; simp
  apply eq_comm
  apply gconv

theorem prox_iff_subderiv_smul (f : E → ℝ) {t : ℝ} (hfun : ConvexOn ℝ univ f) (ht : 0 < t) :
    ∀ u : E, prox_prop (t • f) x u ↔ (1 / t) • (x - u) ∈ (SubderivAt f u) := by
  intro u
  let g := fun u ↦ (t • f) u
  have tnonneg : 0 ≤ t := by linarith
  have gconv : ConvexOn ℝ univ g := by
    apply ConvexOn.smul tnonneg hfun
  rw [prox_iff_subderiv, ← mem_SubderivAt, ← mem_SubderivAt]
  rw [HasSubgradientAt, HasSubgradientAt]
  constructor
  · intro cond y
    specialize cond y; simp at cond
    rw [inner_smul_left]; simp
    rw [← mul_le_mul_left ht]; ring_nf; field_simp
    exact cond
  · intro cond y
    specialize cond y; rw [inner_smul_left] at cond; field_simp at cond
    simp
    have hrect : 0 < t⁻¹ := by
      simp; linarith
    rw [← mul_le_mul_left hrect]; ring_nf; field_simp
    exact cond
  exact gconv

end properties

end
