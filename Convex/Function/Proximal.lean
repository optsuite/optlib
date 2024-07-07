/-
Copyright (c) 2024 Shengyang Xu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengyang Xu, Chenyi Li
-/
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.Convex.Basic
import Convex.Function.Subgradient
import Convex.Function.Lsmooth
import Convex.Function.StronglyConvex
import Convex.Function.MinimaClosedFunction

set_option linter.unusedVariables false

/-!
 proximal operator
-/
noncomputable section

open Set InnerProductSpace Topology Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [ProperSpace E]
variable {x y y₁ y₂ : E} {s : Set E} {f : E → ℝ}

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

/-
  The sum of a convex function and a square of norm is strongly convex
-/
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
        show ∀ᶠ (n : ℕ) in atTop, auxle (xn n).1
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

/-
  The existence of the proximal for proper lower-semi-continuous function
-/
theorem prox_set_compact_of_lowersemi (f : E → ℝ) (hc : LowerSemicontinuous f)
    (lbdf : BddBelow (f '' univ)) :
    ∀ x, Nonempty (prox_set f x) ∧ IsCompact (prox_set f x) := by
  intro x
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let epi := {p : (E × ℝ) | g p.1 ≤ p.2}
  let S := {y : E| g y ≤ g x}
  have eq : S = (g ⁻¹' Set.Iic (g x)) := by constructor
  let ImS := {g y | y ∈ S}
  have neImS : Set.Nonempty ImS := by
    use g x; simp [ImS]; use x; simp [S]
  rcases lbdf with ⟨L, Lbound⟩
  rw [mem_lowerBounds] at Lbound
  have boundg : ∀ (x : E), L ≤ g x := by
    intro z
    calc
      L ≤ f z := by
        specialize Lbound (f z); simp at Lbound; exact Lbound
      _ ≤ f z + ‖z - x‖ ^ 2 / 2 := by
        simp; linarith [sq_nonneg ‖z - x‖]
  have hg : LowerSemicontinuous g := by
    apply LowerSemicontinuous.add hc
    apply Continuous.lowerSemicontinuous
    apply continuous_iff_continuousOn_univ.2
    apply HasGradientAt.continuousOn
    intro u _; apply gradient_of_sq u
  have S_bddbelow : BddBelow ImS := by
    use L; rw [mem_lowerBounds]
    rintro gy ⟨y0, _, gyeq⟩; rw [← gyeq]; exact boundg y0
  have epi_closed : IsClosed epi := by
    apply bounded_lowersemicontinuous_to_epi_closed
    · exact lowerSemicontinuousOn_univ_iff.2 hg
    use L
  have closeds : IsClosed S := by
    rw [eq]
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hg
    exact hg (g x)
  have compacts : IsCompact S := by
    let B := Metric.closedBall x (f x - L + 1)
    have sinb : S ⊆ B := by
      intro u uin; simp [S] at uin
      apply mem_closedBall_iff_norm.2
      have norm_bound: ‖u - x‖ ≤ f x - L + 1 := by
        have ieq : L + ‖u - x‖ ^ 2 / 2 ≤ f x:= by
          calc
          L + ‖u - x‖ ^ 2 / 2 ≤ g u := by
            simp [g]; specialize Lbound (f u); simp at Lbound; exact Lbound
          _ ≤ f x := by simp [g] at uin; exact uin
        rw [← le_sub_iff_add_le'] at ieq
        have aux {a b : ℝ} (h1 : a ^ 2 / 2 ≤ b) (h2 : 0 ≤ a) : a ≤ b + 1 := by
          rw [div_le_iff] at h1; rw [← abs_eq_self] at h2; rw [← h2]
          apply abs_le_of_sq_le_sq; rw [add_sq]; simp
          calc
            a ^ 2 ≤ b * 2 := h1
            _ ≤ b ^ 2 + 2 * b + 1 := by
              rw [add_right_comm, mul_comm]; simp; linarith [sq_nonneg b]
          calc
            0 ≤ a ^ 2 / 2 := by linarith [sq_nonneg a]
            _ ≤ b * 2 / 2 := by rw [div_le_div_right]; exact h1; linarith
            _ ≤ b + 1 := by simp
          linarith
        apply aux ieq
        apply norm_nonneg
      exact norm_bound
    have compactb : IsCompact B := isCompact_closedBall x (f x - L + 1)
    rw [← closure_eq_iff_isClosed] at closeds; rw [← closeds]
    apply IsCompact.closure_of_subset compactb sinb
  rcases exists_seq_tendsto_sInf neImS S_bddbelow with ⟨fx, _, cfx, fxs⟩
  choose xn xsub xeq using fxs
  rcases IsCompact.tendsto_subseq compacts xsub with ⟨x', _, k, mono, cxk⟩
  have cfxk : Filter.Tendsto (g ∘ xn ∘ k) Filter.atTop (𝓝 (sInf ImS)) := by
    have xkeq : ∀ (n : ℕ), (g ∘ xn ∘ k) n = (fx ∘ k) n := fun n => xeq <| k n
    rw [tendsto_congr xkeq]
    apply Tendsto.comp cfx (StrictMono.tendsto_atTop mono)
  have inepi : (x', sInf ImS) ∈ epi := by
    let p := fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)
    have pnin :  ∀ c : ℕ, p c ∈ epi := by simp [epi]
    apply IsClosed.isSeqClosed epi_closed pnin
    show Tendsto (fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)) atTop (𝓝 (x', sInf ImS))
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
    · have gwnin : g x < g w := by
        simp [g, S] at hw; simp [g]; exact hw
      have gxin : g x ∈ ImS := by use x; simp [g, ImS, S]
      have legw : sInf ImS ≤ g w := by
        rw [Real.sInf_le_iff S_bddbelow neImS]
        intro _ epos; use g x; use gxin; linarith
      linarith
  constructor
  · use x'; simp [prox_set]; rw [prox_prop, isMinOn_iff]
    intro v _; exact minima v
  · have aux : prox_set f x = {x | IsMinOn g univ x} := by
      simp [prox_set]; ext y
      constructor
      · intro yin; simp [prox_prop] at yin; simp; exact yin
      · intro yin; simp; rw [prox_prop]
        simp at yin; exact yin
    have nes : Nonempty S := by use x; simp [S]
    rw [eq] at compacts; rw [eq] at nes
    rw [aux] -- apply IsCompact_isMinOn_of_isCompact_preimage hc nes compacts
    have seq : {x | IsMinOn g univ x} = (g ⁻¹' Set.Iic (g x')) := by
      ext y
      constructor
      · exact fun hxx => isMinOn_iff.mp hxx x' trivial
      · intro yin; simp at yin
        exact fun x xuniv => le_trans yin ((fun x _ => minima x) x xuniv)
    simp only [seq]
    apply IsCompact.of_isClosed_subset compacts (LowerSemicontinuous.isClosed_preimage hg (g x'))
    apply Set.preimage_mono
    simp only [Set.Iic_subset_Iic]
    exact minima x

theorem prox_set_compact_of_convex (f : E → ℝ) (hc : ContinuousOn f univ)
    (hconv : ConvexOn ℝ univ f) :
    ∀ x, Nonempty (prox_set f x) ∧ IsCompact (prox_set f x) := by
  intro x
  have subd: ∃ z : E, Nonempty (SubderivAt f z) := by
    use x; apply SubderivAt.nonempty hconv hc
  have hc : LowerSemicontinuous f :=
    Continuous.lowerSemicontinuous (continuous_iff_continuousOn_univ.mpr hc)
  rcases subd with ⟨z, a, ain⟩
  rw [← mem_SubderivAt, HasSubgradientAt] at ain
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let epi := {p : (E × ℝ) | g p.1 ≤ p.2}
  have second_lower_bound (y : E) : g y ≥ f z + inner a (y - z) + ‖y - x‖ ^ 2 / 2 := by
    simp [g]
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
  have hg : LowerSemicontinuous g := by
    apply LowerSemicontinuous.add hc
    apply Continuous.lowerSemicontinuous
    apply continuous_iff_continuousOn_univ.2
    apply HasGradientAt.continuousOn
    intro u _; apply gradient_of_sq u
  have epi_closed : IsClosed epi := by
    apply bounded_lowersemicontinuous_to_epi_closed
    · exact lowerSemicontinuousOn_univ_iff.2 hg
    use (f z + inner a (x - z) - ‖a‖ ^ 2 / 2)
  let S := {y : E| g y ≤ g z}
  have eq : S = (g ⁻¹' Set.Iic (g z)) := by constructor
  let ImS := {g y | y ∈ S}
  have neImS : Set.Nonempty ImS := by
    use g z; simp [ImS, S]; use z
  have S_bddbelow : BddBelow ImS := by
    use (f z + inner a (x - z) - ‖a‖ ^ 2 / 2)
    rw [mem_lowerBounds]
    rintro gy ⟨y0, _, gyeq⟩
    rw [← gyeq]; exact lower_bound y0
  have closeds : IsClosed S := by
    rw [eq]
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hg
    exact hg (g z)
  have compacts : IsCompact S := by
    let B := Metric.closedBall (x - a) (‖z - (x - a)‖ + 2)
    have sinb : S ⊆ B := by
      intro u uin
      simp [S] at uin
      apply mem_closedBall_iff_norm.2
      have norm_bound: ‖u - (x - a)‖ ≤ ‖z - (x - a)‖ + 2 := by
        have ieq : f z + inner a (u - z) + ‖u - x‖ ^ 2 / 2 ≤ f z + ‖z - x‖ ^ 2 / 2 + 1 := by
          calc
            f z + inner a (u - z) + ‖u - x‖ ^ 2 / 2 ≤ g u := second_lower_bound u
            _ ≤ f z + ‖z - x‖ ^ 2 / 2 := uin
            _ ≤ f z + ‖z - x‖ ^ 2 / 2 + 1 := by linarith
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
    rw [← closure_eq_iff_isClosed] at closeds; rw [← closeds]
    apply IsCompact.closure_of_subset compactb sinb
  rcases exists_seq_tendsto_sInf neImS S_bddbelow with ⟨fx, _, cfx, fxs⟩
  choose xn xsub xeq using fxs
  rcases IsCompact.tendsto_subseq compacts xsub with ⟨x', _, k, mono, cxk⟩
  have cfxk : Filter.Tendsto (g ∘ xn ∘ k) Filter.atTop (𝓝 (sInf ImS)) := by
    have xkeq : ∀ (n : ℕ), (g ∘ xn ∘ k) n = (fx ∘ k) n := fun n => xeq <| k n
    rw [tendsto_congr xkeq]
    apply Tendsto.comp cfx (StrictMono.tendsto_atTop mono)
  have inepi : (x', sInf ImS) ∈ epi := by
    let p := fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)
    have pnin :  ∀ c : ℕ, p c ∈ epi := by simp [epi]
    apply IsClosed.isSeqClosed epi_closed pnin
    show Tendsto (fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)) atTop (𝓝 (x', sInf ImS))
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
      · have gwnin : g z < g w := by
          simp [S] at hw; simp [g]; exact hw
        have gzin : g z ∈ ImS := by use z; simp [ImS, S]
        have legw : sInf ImS ≤ g w := by
          rw [Real.sInf_le_iff S_bddbelow neImS]
          intro _ epos; use g z; use gzin; linarith
        linarith
  constructor
  · use x'; simp [prox_set]; rw [prox_prop, isMinOn_iff]
    intro v _; exact minima v
  · have aux : prox_set f x = {x | IsMinOn g univ x} := by
      simp [prox_set]; ext y
      constructor
      · intro yin; simp [prox_prop] at yin; simp; exact yin
      · intro yin; simp; rw [prox_prop]
        simp at yin; exact yin
    have nes : Nonempty S := by use z; simp [S]
    rw [eq] at compacts; rw [eq] at nes
    rw [aux] -- apply IsCompact_isMinOn_of_isCompact_preimage hc nes compacts
    have seq : {x | IsMinOn g univ x} = (g ⁻¹' Set.Iic (g x')) := by
      ext y
      constructor
      · exact fun hxx => isMinOn_iff.mp hxx x' trivial
      · intro yin; simp at yin
        exact fun x xuniv => le_trans yin ((fun x _ => minima x) x xuniv)
    simp only [seq]
    apply IsCompact.of_isClosed_subset compacts (LowerSemicontinuous.isClosed_preimage hg (g x'))
    apply Set.preimage_mono
    simp only [Set.Iic_subset_Iic]
    exact minima z

theorem prox_well_define (f : E → ℝ) (hc : LowerSemicontinuous f) (lbdf : BddBelow (f '' univ)) :
    ∀ x, ∃ y, prox_prop f x y := by
  intro x
  rcases (prox_set_compact_of_lowersemi f hc lbdf x).1 with ⟨y, yprop⟩
  use y; simp [prox_set] at yprop; exact yprop

theorem prox_well_define_convex (f : E → ℝ) (hc : ContinuousOn f univ)
    (hconv : ConvexOn ℝ univ f) :
  ∀ x, ∃ y, prox_prop f x y := by
  intro x
  rcases (prox_set_compact_of_convex f hc hconv x).1 with ⟨y, yprop⟩
  use y; simp [prox_set] at yprop; exact yprop

/-
  The uniqueness of the proximal for proper convex function
-/
theorem prox_unique_of_convex (f : E → ℝ) (x : E) (hfun : ConvexOn ℝ univ f)
    (h₁ : prox_prop f x y₁) (h₂ : prox_prop f x y₂) : y₁ = y₂ := by
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
def prox_point_c (f : E → ℝ) (x : E) (hc : LowerSemicontinuous f)
    (lbdf : BddBelow (f '' univ)) : E :=
  have h : ∃ y, prox_set f x y := by
    apply prox_well_define f hc lbdf x
  Classical.choose h

def prox_point_c' (f : E → ℝ) (x : E) (hc : ContinuousOn f univ)
    (hconv : ConvexOn ℝ univ f) : E :=
  have h : ∃ y, prox_set f x y := by
    apply prox_well_define_convex f hc hconv x
  Classical.choose h

section properties

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {s : Set E} {f : E → ℝ} {u x: E} {t : ℝ}

open Set InnerProductSpace

/-
   The square of norm is convex on a convex set
-/
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

/-
  Sub-derivative at x equal to sub-derivative within univ at x
-/
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

/-
  u minimize the proximal at x iff x - u is subgradient
-/
theorem prox_iff_subderiv (f : E → ℝ) (hfun : ConvexOn ℝ univ f) :
    ∀ u : E, prox_prop f x u ↔ x - u ∈ SubderivAt f u := by
  intro u; rw [prox_prop, ← HasSubgradientAt_zero_iff_isMinOn, mem_SubderivAt]
  let g := fun u ↦ ‖u - x‖ ^ 2 / 2
  have hg : ConvexOn ℝ Set.univ g := by apply convex_of_norm_sq x (convex_univ)
  have hcg : ContinuousOn g univ := by
    simp [g]; apply ContinuousOn.div
    apply ContinuousOn.pow _
    · apply ContinuousOn.norm
      apply ContinuousOn.sub continuousOn_id continuousOn_const
    · apply continuousOn_const
    · simp
  show 0 ∈ SubderivAt (f + g) u ↔ x - u ∈ SubderivAt f u
  have : SubderivAt (f + g) u = SubderivAt (g + f) u := by
    unfold SubderivAt; ext z; rw [Set.mem_setOf, Set.mem_setOf];
    constructor
    repeat
    unfold HasSubgradientAt; intro hy y; specialize hy y; simp at hy ⊢; linarith
  rw [this, ← SubderivAt.add hg hfun hcg]
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

/-
  If f is differentiable and convex on E, then u minimize the proximal at x iff ∇f(u) = x - u
-/
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

/-
  If f is differentiable and convex on E, then u minimize the proximal for t*f at x iff
  t ∇f(u) = x - u
-/
theorem prox_iff_grad_smul (f : E → ℝ) {f' : E → E} (t : ℝ) (hfun : ConvexOn ℝ univ f)
    (hdiff : ∀ x, HasGradientAt f (f' x) x) (tnonneg : 0 ≤ t) :
    ∀ u : E, prox_prop (t • f) x u ↔ t • f' u = x - u := by
  intro u
  let g := fun u ↦ (t • f) u
  let g' := fun u ↦ t • f' u
  have gconv : ConvexOn ℝ univ g := by
    apply ConvexOn.smul tnonneg hfun
  have gderiv : ∀ x, HasGradientAt g (g' x) x := by
    intro x
    simp only [Pi.smul_apply, g, g']
    apply HasGradientAt.const_smul'
    exact hdiff x
  rw [prox_iff_subderiv]
  have : SubderivWithinAt g univ u = {g' u} := by
      apply SubderivWithinAt_eq_gradient; simp
      apply gconv; apply gderiv
  rw [← Subderivat_eq_SubderivWithinAt_univ, this]; simp
  apply eq_comm
  apply gconv

/-
  u minimize the proximal for t*f at x iff (x - u)/t is subgradient
-/
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

/-
  relation of proximal between a function and its shift
-/
theorem proximal_shift (a : E) {t : ℝ} (tnz : t ≠ 0) (f : E → ℝ):
    ∀ z : E, prox_prop (fun x ↦ f (t • x + a)) x z ↔
      prox_prop (t ^ 2 • f) (t • x + a) (t • z + a) := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  simp
  constructor
  · intro cond y
    specialize cond (t⁻¹ • (y - a))
    rw [← smul_assoc, smul_eq_mul, mul_inv_cancel] at cond
    simp at cond
    calc
      t ^ 2 * f (t • z + a) + ‖t • z - t • x‖ ^ 2 / 2 =
          t ^ 2 * (f (t • z + a) + ‖z - x‖ ^ 2 / 2) := by
        rw [← smul_sub, norm_smul, mul_pow, mul_add]; field_simp
      _ ≤ t ^ 2 * (f y + ‖t⁻¹ • (y - a) - x‖ ^ 2 / 2) := by
        rw [mul_le_mul_left]; use cond; rw [sq_pos_iff]; use tnz
      _ = t ^ 2 * f y + ‖t • ((1 / t) • (y - a) - x)‖ ^ 2 / 2 := by
        rw [mul_add, norm_smul, mul_pow]; field_simp
      _ = t ^ 2 * f y + ‖y - (t • x + a)‖ ^ 2 / 2 := by
        rw [smul_sub, ← smul_assoc, smul_eq_mul, ← sub_sub, sub_right_comm]; field_simp
    use tnz
  · intro cond y
    specialize cond (t • y + a)
    rw [← smul_sub, norm_smul, mul_pow] at cond; simp at cond
    rw [← smul_sub, norm_smul, mul_pow] at cond; simp at cond
    rw [mul_div_assoc, ← mul_add, mul_div_assoc, ← mul_add] at cond
    rw [mul_le_mul_left] at cond; use cond; rw [sq_pos_iff]; use tnz

/-
  relation of proximal between a function and its scale
-/
theorem proximal_scale {t : ℝ} (tpos : 0 < t) (f : E → ℝ):
    ∀ z : E, prox_prop (fun x ↦ t • f (t⁻¹ • x)) x z ↔
      prox_prop (t⁻¹ • f) (t⁻¹ • x) (t⁻¹ • z) := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  simp
  constructor
  · intro cond y
    specialize cond (t • y)
    have tsq : 0 < t ^ 2 := by field_simp
    rw [← mul_le_mul_left tsq]
    calc
      t ^ 2 * (t⁻¹ * f (t⁻¹ • z) + ‖t⁻¹ • z - t⁻¹ • x‖ ^ 2 / 2) =
          t * f (t⁻¹ • z) + ‖z - x‖ ^ 2 / 2 := by
        rw [← smul_sub, norm_smul, mul_pow, mul_add, pow_two, ← mul_assoc, mul_assoc _ _ (t⁻¹)]
        rw [mul_inv_cancel, mul_div_assoc, ← mul_assoc]; simp
        rw [← pow_two, mul_inv_cancel]; repeat simp; repeat linarith
      _ ≤ t * f (t⁻¹ • t • y) + ‖t • y - x‖ ^ 2 / 2 := cond
      _ = t ^ 2 * (t⁻¹ * f y) + ‖t • (y - t⁻¹ • x)‖ ^ 2 / 2 := by
        rw [pow_two t, ← mul_assoc, mul_assoc _ _ (t⁻¹), mul_inv_cancel]
        rw [← smul_assoc, smul_eq_mul, inv_mul_cancel]; simp
        rw [smul_sub, ← smul_assoc, smul_eq_mul, mul_inv_cancel]; simp; repeat linarith
      _ = t ^ 2 * (t⁻¹ * f y + ‖y - t⁻¹ • x‖ ^ 2 / 2) := by
        rw [mul_add, norm_smul, mul_pow]; field_simp
  · intro cond y
    specialize cond (t⁻¹ • y)
    have tsq : 0 < t ^ 2 := by field_simp
    rw [← mul_le_mul_left tsq] at cond
    calc
      t * f (t⁻¹ • z) + ‖z - x‖ ^ 2 / 2 =
          t ^ 2 * (t⁻¹ * f (t⁻¹ • z) + ‖t⁻¹ • z - t⁻¹ • x‖ ^ 2 / 2) := by
        rw [← smul_sub, norm_smul, mul_pow, mul_add, pow_two t, ← mul_assoc, mul_assoc _ _ (t⁻¹)]
        rw [mul_inv_cancel, mul_div_assoc, ← mul_assoc]; simp
        rw [← pow_two, mul_inv_cancel]; repeat simp; repeat linarith
      _ ≤ t ^ 2 * (t⁻¹ * f (t⁻¹ • y) + ‖t⁻¹ • y - t⁻¹ • x‖ ^ 2 / 2) := cond
      _ = t ^ 2 * (t⁻¹ * f (t⁻¹ • y)) + ‖t • (t⁻¹ • y - t⁻¹ • x)‖ ^ 2 / 2 := by
        rw [mul_add, norm_smul, mul_pow]; field_simp
      _ = t * f (t⁻¹ • y) + ‖y - x‖ ^ 2 / 2 := by
        rw [pow_two t, ← mul_assoc, mul_assoc _ _ (t⁻¹), mul_inv_cancel]
        rw [smul_sub, ← smul_assoc, smul_eq_mul, mul_inv_cancel]; simp
        rw [← smul_assoc, smul_eq_mul, mul_inv_cancel]; simp; repeat linarith

/-
  change of proximal when added a linear components
-/
theorem proximal_add_linear (a : E) (f : E → ℝ):
    ∀ z : E, prox_prop (fun x ↦ f x + inner a x) x z ↔
      prox_prop f (x - a) z := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  have aux (v : E) : ‖v - (x - a)‖ ^ 2 / 2 =
      ‖v - x‖ ^ 2 / 2 + inner a v + (‖a‖ ^ 2 / 2 - inner a x) := by
    rw [← sub_add, norm_add_sq_real, real_inner_comm, inner_sub_right]; ring_nf
  constructor
  · intro cond y
    specialize cond y
    rw [aux, aux, add_comm _ (inner a z), add_comm _ (inner a y)]
    linarith
  · intro cond y
    specialize cond y
    rw [aux, aux, add_comm _ (inner a z), add_comm _ (inner a y)] at cond
    linarith

/-
  change of proximal when added a square components
-/
theorem proximal_add_sq (a : E) {l : ℝ} (lpos : 0 < l) (f : E → ℝ):
    ∀ z : E, prox_prop (fun x ↦ f x + l / 2 * ‖x - a‖ ^ 2) x z ↔
      prox_prop ((1 / (l + 1)) • f) ((1 / (l + 1)) • (x + l • a)) z := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  have aux (v : E) : ‖v - (1 / (l + 1)) • (x + l • a)‖ ^ 2 / 2 =
      (l + 1)⁻¹ * (l / 2 * ‖v - a‖ ^ 2 + ‖v - x‖ ^ 2 / 2 + (((l + 1)⁻¹ * (‖x + l • a‖ ^ 2)
        - ‖x‖ ^ 2 - l * ‖a‖ ^ 2) / 2)) := by
    rw [div_mul_eq_mul_div, ← add_div, ← add_div, ← mul_div_assoc, div_left_inj']
    rw [norm_sub_sq_real, norm_smul, mul_pow, mul_add, sub_sub, mul_sub, ← mul_assoc, ← pow_two]
    rw [Real.norm_eq_abs, sq_abs, ← inv_eq_one_div, add_sub, add_sub_right_comm]
    rw [add_right_cancel_iff, norm_sub_sq_real, norm_sub_sq_real]
    rw [← mul_sub, mul_add, ← add_assoc, ← sub_sub, inner_smul_right]; simp
    rw [add_sub_right_comm]; simp; rw [mul_sub, ← add_sub_right_comm, ← add_sub_assoc]
    nth_rw 3 [← one_mul (‖v‖ ^ 2)]; rw [← add_mul, ← mul_assoc l, mul_comm l 2, sub_sub]
    rw [mul_assoc, ← mul_add, ← inner_smul_right _ _ l, ← inner_add_right]
    field_simp; rw [mul_comm]; simp
  constructor
  · intro cond y
    specialize cond y
    rw [aux, aux]; simp; rw [← mul_add, ← mul_add, mul_le_mul_left]
    linarith [cond]; simp; linarith
  · intro cond y
    specialize cond y
    rw [aux, aux] at cond; simp at cond; rw [← mul_add, ← mul_add, mul_le_mul_left] at cond
    linarith [cond]; simp; linarith

end properties
