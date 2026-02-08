import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Data.PFun
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Reaslib.ConvexAnalysis.ClosedFunction_Closure_Proper
import Reaslib.ConvexAnalysis.AffineMinorant
import Reaslib.Basic.EReal

open Filter BigOperators Set Topology Inner Function Module EReal
open scoped Pointwise

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

section Thm_12_1

/- See AffineMinorant.lean -/

end Thm_12_1

/-
This section defines the convex conjugate of a function `f : E → EReal` over a set `s ⊆ E`.
The convex conjugate, also known as the Fenchel-Legendre transform, is a function `f* : E → EReal`
defined as:
`f*(y) = sup_{x ∈ s} (⟪x, y⟫ - f(x))`
In the code, this is represented by `convex_conjugate s f`.
-/
noncomputable section convex_conjugate_def

variable (s : Set E) (f : E → EReal)

noncomputable def convex_conjugate : E → EReal :=
  fun y => ⨆ x ∈ s, ⟪x, y⟫ - f x

end convex_conjugate_def

/-
This section provides a collection of fundamental properties and auxiliary lemmas
for the convex conjugate. These include:
- Basic algebraic properties for inequalities involving `EReal`.
- Conditions for the conjugate of a proper function to be well-defined (not `⊥`).
- Behavior of the conjugate for extreme cases, such as when the original function `f`
  is `⊥` or `⊤`.
-/
section aux_lemma

variable {s : Set E} {f : E → EReal}

/-
Lemma. An auxiliary lemma to prove that for a real number `a` and an extended real number `b`,
the inequality `a - b ≤ 0` is equivalent to `a ≤ b`.
Purpose: This is useful for rearranging terms in inequalities involving `EReal`.
-/
lemma E_EReal (a : ℝ) (b : EReal) : a - b ≤ 0 ↔ a ≤ b := by
  by_cases h₁ : b = ⊤
  · rw [h₁]
    exact Iff.symm (le_iff_le_of_cmp_eq_cmp rfl)

  by_cases h₂ : b = ⊥
  · rw [h₂]
    exact Iff.symm (le_iff_le_of_cmp_eq_cmp rfl)

  lift b to ℝ using ⟨h₁, h₂⟩
  rw [← EReal.coe_sub]
  simp only [EReal.coe_le_coe_iff]
  rw [EReal.coe_nonpos]
  exact tsub_nonpos

/-
Lemma. This lemma provides an equivalent condition for the convex conjugate of a function `f`
at a point `x` to be non-positive. It states that `f*(x) ≤ 0` if and only if
for all `y`, the inner product `⟪x, y⟫` is a global underestimator of `f(y)`.
-/
variable (f) in
lemma conjugate_le_zero_iff :
  convex_conjugate univ f x ≤ 0 ↔ ∀ y, ⟪x, y⟫ ≤ f y := by
  simp [convex_conjugate]
  refine forall_congr' ?h
  have h : ∀ (a : E), ⟪x, a⟫ = ⟪a, x⟫ := by
    exact fun a ↦ real_inner_comm a x
  intro a
  rw [h]
  exact E_EReal (inner ℝ a x) (f a)

/-
Theorem. If a function `f` is proper on a nonempty set `s`, its convex conjugate `f*`
is never equal to `⊥` (negative infinity).
-/
variable (f) in
theorem convex_conjugate_ne_bot_s [hsf : ProperFunction s f] (hs : s.Nonempty) :
    ∀ x ∈ univ, (convex_conjugate s f) x > ⊥ := by
  intro x _
  /-
  To show the supremum is greater than `⊥`, we
  find one element in the set that is greater than `⊥`.
  -/
  simp [convex_conjugate]
  -- Since `f` is proper, there exists a `y` in `s` where `f y` is finite.
  obtain exist_y := Or.resolve_left hsf.existence_of_finite_value (Set.nonempty_iff_ne_empty.1 hs)
  choose y ys hfy using exist_y
  -- We use this `y` as a witness.
  use y, ys
  apply sub_lt_bot (by simp) (by simp) (LT.lt.ne_top hfy)

/-
Theorem. This is a direct corollary of `convex_conjugate_ne_bot`, restating `> ⊥` as `≠ ⊥`.
-/
variable (s f) in
theorem convex_conjugate_not_bot [ProperFunction s f] (hs : s.Nonempty) :
    ∀ x ∈ univ, (convex_conjugate s f) x ≠ ⊥ :=
  fun x xs => bot_lt_iff_ne_bot.1 (convex_conjugate_ne_bot_s f hs x xs)

/-
Theorem. A special case of `convex_conjugate_not_bot` for `s = univ`.
The nonemptiness of `univ` is proven by `simp`.
-/
theorem convex_conjugate_not_bot_univ [ProperFunction univ f] :
    ∀ x ∈ univ, (convex_conjugate univ f) x ≠ ⊥ := by
  apply convex_conjugate_not_bot
  simp

/-
Lemma. A helper lemma for rewriting the definition of `convex_conjugate` on `univ`.
-/
lemma cc_univ_eq : ∀ x, ⨆ u, Real.toEReal (inner ℝ u x) - f u
    = convex_conjugate univ f x :=
  fun _ => (by simp [convex_conjugate])

/-
Theorem. If `f` is a proper function on `univ`, its convex conjugate,
expressed as a supremum, is always greater than `⊥`.
The proof uses `convex_conjugate_not_bot_univ` and rewrites the goal using `cc_univ_eq`.
-/
variable (f) in
theorem convex_conjugate_ge_bot_univ [hsf : ProperFunction univ f] :
    ∀ x, ⨆ u, Real.toEReal (inner ℝ u x) - f u > ⊥ := by
  intro x
  have := convex_conjugate_not_bot univ f (by simp) x (by trivial)
  rw [cc_univ_eq]; exact Ne.bot_lt' (id (Ne.symm this))

/-
Theorem. A wrapper for `convex_conjugate_ge_bot_univ` to state the property directly
for `convex_conjugate univ f`.
-/
variable (f) in
theorem convex_conjugate_ge_bot_univ' [hsf : ProperFunction univ f] :
    ∀ x, convex_conjugate univ f x > ⊥ := by
  intro x; rw [← cc_univ_eq x]
  apply convex_conjugate_ge_bot_univ

/-
Lemma. If `f` is a proper function on a nonempty set `s` and `b` is a positive real number,
then `b * f*(y)` is greater than `⊥` for any `y` in `s`.
Purpose: This is useful for dealing with `⊥` (negative infinity).
-/
variable (s f) in
lemma pos_mul_convex_conjugate_not_bot {b : ℝ} [hsf : ProperFunction s f] (hb : b > 0) :
    ∀ y ∈ s, Real.toEReal b * convex_conjugate s f y > ⊥ := by
  by_cases hs : s = ∅
  · simp [hs]
  have hs' := Set.nonempty_iff_ne_empty.2 hs
  intro y _
  -- We handle two cases for the value of the convex conjugate.
  by_cases fytop : convex_conjugate s f y = ⊤
  · rw [fytop, EReal.coe_mul_top_of_pos]
    · simp
    exact hb
  push_neg at fytop
  -- Since `f` is proper, its conjugate is not `⊥` either. So we can lift it to a real number.
  lift convex_conjugate s f y to ℝ with cfy
  · exact ⟨fytop, convex_conjugate_not_bot s f hs' y (by trivial)⟩
  -- The product of two real numbers is a real number, which is always `> ⊥`.
  rw [← EReal.coe_mul]
  apply EReal.bot_lt_coe

/-
Lemma. A technical lemma for multiplying an inequality involving a supremum
by a positive constant `a`.
It states that if an `EReal` value `X` is less than or equal to a supremum `sup Y` (which is the
convex conjugate), then `a * X ≤ a * sup Y` for any positive real number `a`. This is a version
of `EReal.mul_le_mul_of_nonneg` for the specific structure of the convex conjugate, handling
the cases where the supremum might be `⊤` or a finite number.
-/
lemma real_mul_convex_conjugate_inequ {a fu : ℝ} [hsf : ProperFunction univ f] (ha : a > 0)
    (sup_inequ₁ : (Real.toEReal (inner ℝ u x) - fu) ≤ ⨆ u, Real.toEReal (inner ℝ u x) - f u) :
    Real.toEReal a * (Real.toEReal (inner ℝ u x) - fu)
    ≤ Real.toEReal a * ⨆ u, Real.toEReal (inner ℝ u x) - f u := by
  -- The conjugate is proper, so its value is not `⊥`.
  have hcgx2 : ⨆ u, Real.toEReal (inner ℝ u x) - f u > ⊥ := by
    exact convex_conjugate_ge_bot_univ f x
  -- We handle two cases for the value of the convex conjugate.
  by_cases htop : ⨆ u, Real.toEReal (inner ℝ u x) - f u = ⊤
  · rw [htop]
    simp [coe_mul_top_of_pos ha]
  push_neg at htop
  lift ⨆ u, Real.toEReal (inner ℝ u x) - f u to ℝ with sup
  · exact ⟨htop, LT.lt.ne_bot hcgx2⟩
  -- The problem reduces to an inequality over real numbers.
  rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul]
  rw [← EReal.coe_sub] at sup_inequ₁
  apply EReal.coe_le_coe_iff.2
  apply EReal.coe_le_coe_iff.1 at sup_inequ₁
  field_simp
  linarith

/-
Theorem. If a function `f` takes the value `⊥` anywhere in its domain,
its convex conjugate is identically `⊤`.
Purpose: This is useful for dealing with trivial cases in proofs.
-/
theorem conjugate_of_bot_exist {f : E → EReal} (hb : ∃ x ∈ dom univ f, f x = ⊥) :
    convex_conjugate univ f = ⊤ := by
  ext x
  simp [convex_conjugate]
  rcases hb with ⟨y, _, hy2⟩
  -- The term `⟪y, x⟫ - f y` in the supremum becomes `⟪y, x⟫ - ⊥ = ⊤`.
  have : (inner ℝ y x : ℝ) - f y = ⊤ := by rw [hy2]; simp
  -- The supremum of a set containing `⊤` is `⊤`.
  have hx : ⊤ ≤ ⨆ x_1, (inner ℝ x_1 x : ℝ) - f x_1 := by
    rw [← this]
    apply le_iSup (f := fun x_1 ↦ (inner ℝ x_1 x : ℝ) - f x_1) (i := y)
  exact eq_top_iff.mpr hx

/-
Theorem. A simplified version of `conjugate_of_bot_exist`. If `f` takes the value `⊥` anywhere,
its convex conjugate is identically `⊤`.
-/
theorem conjugate_of_bot_exist' {f : E → EReal} (hb : ∃ x, f x = ⊥) :
    convex_conjugate univ f = ⊤ := by
  apply conjugate_of_bot_exist
  rcases hb with ⟨x, hx⟩
  use x; simp [hx]

/-
Theorem. If a function `f` is identically `⊤`, its convex conjugate is identically `⊥`.
-/
theorem conjugate_of_top {f : E → EReal} (hf : f = ⊤) :
    convex_conjugate univ f = ⊥ := by
  ext x
  simp [convex_conjugate]; intro i
  rw [congrFun hf i]; simp

end aux_lemma


/-
This section proves the Fenchel inequality (also known as the Fenchel-Young inequality),
which establishes a fundamental relationship between a function `f`, its convex conjugate `f*`,
and the inner product.
-/
section Fenchel

/-
Theorem. This theorem states that for a proper function `f` on a set `s`,
the following inequality holds:
`⟪x, x_star⟫ ≤ f(x) + f*(x_star)`
for any `x` and `x_star` in `s`.

Proof Idea: The proof starts from the definition of the convex conjugate
`f*(x_star) = sup_{y ∈ s} (⟪y, x_star⟫ - f(y))`.
By definition of the supremum, we have `f*(x_star) ≥ ⟪x, x_star⟫ - f(x)` for any `x ∈ s`.
The main challenge is to rearrange this inequality in `EReal`,
carefully handling potential `⊤` and `⊥` values.
-/
theorem fenchel_inequality (s : Set E) (f : E → EReal) [hf : ProperFunction s f] :
    ∀ x ∈ s, ∀ x_star ∈ s, ⟪x, x_star⟫ ≤ f x + (convex_conjugate s f) x_star := by
  -- Handle the trivial case where `s` is empty.
  by_cases hs: s = ∅
  · rw [hs]
    tauto
  intro x xs x_star _
  simp only [convex_conjugate]
  -- Let `a := ⟪x, x_star⟫`, `b := f*(x_star)`, and `c := f(x)`. The goal is to prove `a ≤ c + b`.
  let a := Real.toEReal (inner ℝ x x_star)
  let b := ⨆ x ∈ s, Real.toEReal (inner ℝ x x_star) - f x
  let c := f x
  change a ≤ c + b
  have ha1 : a ≠ ⊤ := by simp [a]
  have ha2 : a ≠ ⊥ := by simp [a]
  -- Prove that `b` (the conjugate) is not `⊥` because `f` is a proper function on a nonempty set.
  have b_not_bot : b ≠ ⊥ := by
    by_contra hh
    simp [b] at hh
    obtain exist_x := Or.resolve_left (hf.existence_of_finite_value) hs
    choose y ys fy1 using exist_x
    specialize hh y ys
    let a2 := Real.toEReal (inner ℝ y x_star)
    have ha1' : a2 ≠ ⊤ := by simp [a2]
    have ha2' : a2 ≠ ⊥ := by simp [a2]
    obtain ge_bot:= sub_lt_bot ha1' ha2' (LT.lt.ne_top fy1)
    simp [a2, hh] at ge_bot
  -- Prove that `c` (`f(x)`) is not `⊥` because `f` is proper.
  have fx_not_bot : c ≠ ⊥ := bot_lt_iff_ne_bot.1 (hf.uninfinity x xs)
  -- Establish the core inequality `a - c ≤ b`, which follows directly from the definition.
  have EReal.sub_ge_sub_of_ge_add_sub : a - c ≤ b :=
    le_biSup (fun x => Real.toEReal (inner ℝ x x_star) - f x) xs
  /-
  Rerange the inequality. This requires case analysis on whether `b` and `c` are `⊤`,
  ensuring all arithmetic operations are well-defined.
  -/
  by_cases hc : c ≠ ⊤
  · by_cases hb : b = ⊤
    · have : c + ⊤ = ⊤ := EReal.top_of_top_add (Ne.bot_lt fx_not_bot)
      simp [hb, this]
    push_neg at hb
    apply EReal.le_add_of_sub_le EReal.sub_ge_sub_of_ge_add_sub ha1 ha2 hc fx_not_bot hb b_not_bot
  · push_neg at hc
    by_cases hb : b = ⊤
    · simp [hc, hb]
    push_neg at hb
    have : ⊤ + b = ⊤ := by
      rw [add_comm]
      apply EReal.top_of_top_add (Ne.bot_lt b_not_bot)
    simp [hc, this]

/-
Theorem. This theorem provides a more direct form of the Fenchel inequality:
`⟪x, x_star⟫ - f(x) ≤ f*(x_star)`
-/
theorem fenchel_inequality' (s : Set E) (f : E → EReal) :
    ∀ x ∈ s, ∀ x_star ∈ s, ⟪x, x_star⟫ - f x ≤ (convex_conjugate s f) x_star :=
  fun _ xs x_star _ => le_biSup (fun x => Real.toEReal (inner ℝ x x_star) - f x) xs

end Fenchel

/-
This section proves a fundamental property of the convex conjugate: the conjugate `f*` of any
proper function `f` is always a convex function. This holds regardless of whether the original
function `f` is convex.
-/
section convex_conjugate_convex

/-
Theorem. This theorem shows that for any proper function `f`,
its convex conjugate `convex_conjugate univ f` is a convex function on the entire space `E`.

Proof Idea: The convex conjugate `f*(y)` is defined as the supremum of
a family of affine (and thus convex) functions of `y`: `y ↦ ⟪u, y⟫ - f(u)`.
The supremum of any collection of convex functions is
itself convex. This proof formalizes this argument.
-/
theorem convex_conjugate_convex [hsf : ProperFunction univ f] :
    ConvexOn ℝ (univ : Set E) (convex_conjugate univ f) := by
  /-
  Unfold the definition of `ConvexOn`. The goal is to show `f*(a*x + b*y) ≤ a*f*(x) + b*f*(y)`
  for `a, b ≥ 0` with `a + b = 1`.
  -/
  simp [ConvexOn]
  constructor
  · exact convex_univ
  · intro x y a b apos bpos absum
    -- Handle trivial cases where `a` or `b` are zero, or where `f*(x)` is `⊤`.
    by_cases ha : a = 0
    · rw [ha]
      have hb : b = 1 := by linarith
      simp [hb]
    push_neg at ha
    by_cases hb : b = 0
    · have ha' : a = 1 := by linarith
      simp [ha', hb]
    push_neg at hb
    have ha' : a > 0 := lt_of_le_of_ne apos (id (Ne.symm ha))
    have hb' : b > 0 := lt_of_le_of_ne bpos (id (Ne.symm hb))
    by_cases h1 : convex_conjugate univ f x = ⊤
    · rw [h1, EReal.mul_top_of_pos (EReal.coe_pos.mpr ha')]
      have notbot : Real.toEReal b * convex_conjugate univ f y > ⊥ := by
        apply pos_mul_convex_conjugate_not_bot
        apply hb'
        trivial
      simp [add_comm ⊤, top_of_top_add notbot]
    simp [convex_conjugate]
    /-
    The main goal is to show
    `(⨆ u, ⟪u, a*x + b*y⟫ - f u) ≤ a*(⨆ u, ⟪u, x⟫ - f u) + b*(⨆ u, ⟪u, y⟫ - f u)`.
    This is proven by showing that for any fixed `u`,
    the term inside the supremum on the left is less than or equal to the expression on the right.
    -/
    intro u
    /-
    Using the linearity of the inner product and `a+b=1`, we rewrite the term for a fixed `u`:
    `⟪u, a*x + b*y⟫ - f u = a*(⟪u, x⟫ - f u) + b*(⟪u, y⟫ - f u)`.
    -/
    have hfu2 := bot_lt_iff_ne_bot.1 (hsf.uninfinity u (by trivial))
    by_cases hfu1 : f u = ⊤
    · simp [hfu1, EReal.sub_top];
    push_neg at hfu1
    -- By the definition of supremum, we have `⟪u, x⟫ - f u ≤ f*(x)` and `⟪u, y⟫ - f u ≤ f*(y)`.
    have sup₁ : (Real.toEReal (inner ℝ u x) - f u) ≤ ⨆ u, Real.toEReal (inner ℝ u x) - f u := by
      apply le_iSup <| fun u => Real.toEReal (inner ℝ u x) - f u
    have sup₂ : (Real.toEReal (inner ℝ u y) - f u) ≤ ⨆ u, Real.toEReal (inner ℝ u y) - f u := by
      apply le_iSup <| fun u => Real.toEReal (inner ℝ u y) - f u
    have hcgx2 : ⨆ u, Real.toEReal (inner ℝ u x) - f u > ⊥ := by
      exact convex_conjugate_ge_bot_univ f x
    have hcgx2 := LT.lt.ne_bot hcgx2
    have hcgy2 : ⨆ u, Real.toEReal (inner ℝ u y) - f u > ⊥ := by
      exact convex_conjugate_ge_bot_univ f y
    have hcgy2 := LT.lt.ne_bot hcgy2
    have hcgx1 : ⨆ u, Real.toEReal (inner ℝ u x) - f u ≠ ⊤ := by
      simp [convex_conjugate] at h1
      push_neg at h1; exact h1
    lift (f u) to ℝ with fu
    · exact ⟨hfu1, hfu2⟩
    /-
    We multiply these inequalities by `a` and `b` respectively and add them.
    This step requires careful handling of `EReal` arithmetic, especially multiplication with `⊤`,
    which is managed by the helper lemma `real_mul_convex_conjugate_inequ` and case analysis.
    The `calc` block formalizes the algebraic manipulation,
    and the final step uses `linarith` on the lifted real-valued inequalities.
    -/
    rw [← EReal.coe_sub, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [← one_mul (fu), ← absum]
    calc
    _ = ↑(a * inner ℝ u x + b * inner ℝ u y - a * fu - b * fu) := by
      apply EReal.coe_eq_coe_iff.2
      ring
    _ = ↑(a * inner ℝ u x) + ↑(b * inner ℝ u y) - ↑(a * fu) - ↑(b * fu) := by
      rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub]
    _ = ↑a * (Real.toEReal (inner ℝ u x) - fu) + ↑b * (Real.toEReal (inner ℝ u y) - fu) := by
      rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub]
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
      ring
    _ ≤ (↑a * ⨆ u, Real.toEReal (inner ℝ u x) - f u) +
        ↑b * ⨆ u, Real.toEReal (inner ℝ u y) - f u := by
      have supa : Real.toEReal a * (Real.toEReal (inner ℝ u x) - fu)
          ≤ Real.toEReal a * ⨆ u, Real.toEReal (inner ℝ u x) - f u := by
        apply real_mul_convex_conjugate_inequ
        apply ha'
        apply sup₁
      have supb : Real.toEReal b * (Real.toEReal (inner ℝ u y) - fu)
          ≤ Real.toEReal b * ⨆ u, Real.toEReal (inner ℝ u y) - f u := by
        apply real_mul_convex_conjugate_inequ
        apply hb'
        apply sup₂
      by_cases hcgy1 : ⨆ u, Real.toEReal (inner ℝ u y) - f u = ⊤
      · rw [hcgy1, EReal.mul_top_of_pos (EReal.coe_pos.mpr hb')]
        have : ↑a * ⨆ u, Real.toEReal (inner ℝ u x) - f u > ⊥ := by
          lift ⨆ u, Real.toEReal (inner ℝ u x) - f u to ℝ with sup
          · exact ⟨hcgx1, hcgx2⟩
          simp [← EReal.coe_mul]
        simp [EReal.top_of_top_add this]
      push_neg at hcgy1
      lift ⨆ u, Real.toEReal (inner ℝ u x) - f u to ℝ with c
      · exact ⟨hcgx1, hcgx2⟩
      lift ⨆ u, Real.toEReal (inner ℝ u y) - f u to ℝ with d
      · exact ⟨hcgy1, hcgy2⟩
      repeat rw [← EReal.coe_mul]
      repeat rw [← EReal.coe_sub]
      repeat rw [← EReal.coe_add]
      repeat rw [← EReal.coe_mul] at supa
      apply EReal.coe_le_coe_iff.2
      rw [← EReal.coe_sub, ← EReal.coe_mul] at supa supb
      apply EReal.coe_le_coe_iff.1 at supa
      apply EReal.coe_le_coe_iff.1 at supb
      linarith

end convex_conjugate_convex

-- theorem closure_eq_self {s : Set E} {f : E → EReal}
--     (hfcl : LowerSemicontinuousOn f s) (hc : ConvexOn ℝ s f):
--     ∀ x ∈ s, (f.closure s) x = f x := by
--   intro x
--   by_cases hsf : ProperFunction s f
--   · apply closure_eq_self_of_proper; exact hfcl
--   simp [Function.closure, hsf]
--   by_cases h1 : ∀ x ∈ s, f x ≠ ⊥
--   · intro hx
--     have : ¬ (∃ x ∈ s, f x = ⊥) := by push_neg; exact h1
--     simp [this]; exact Eq.symm (top_of_ne_bot_of_ne_proper hsf h1 hx)
--   -- ∃ x ∈ univ, f x = ⊥
--   push_neg at h1
--   have h' : ∀ x ∈ s, f x = ⊥ := by

--     -- exact hc
--     -- --∃ x ∈ univ, f x = ⊥ ⊢ ∃ x, f x = ⊥
--     -- refine mem_range.mp ?hx.a
--     -- exact mem_range_of_mem_image f univ h1
--     sorry
--   intro hx; obtain hx'' := h' x hx
--   have : ∃ x ∈ s, f x = ⊥ := ⟨x, ⟨hx, hx''⟩⟩
--   simp [this]; symm; exact hx''

-- instance convex_conjugate_is_proper (hsf : ProperFunction s f) :
--   ProperFunction univ (convex_conjugate s f) where
--     uninfinity := sorry
--     existence_of_finite_value := sorry

section bi_conjugate

variable {s : Set E} {f : E → EReal}

section aux

variable (s f) in
/-
A technical lemma to rewrite the expression `⟪l, x⟫ - f*(l)` as a supremum.
This is a key step in unfolding the definition of the biconjugate `f**`.-/
lemma inequ_cc_to_const (l : E) :
    ⟪l, x⟫ - convex_conjugate univ f l =
    ⨆ (a : ℝ) (_ : a ≥ convex_conjugate univ f l), (⟪l, x⟫ - a).toEReal := by
    simp
    by_cases hc : convex_conjugate univ f l = ⊤
    · simp [hc]
    push_neg at hc
    by_cases hc2 : convex_conjugate univ f l = ⊥
    · simp [hc2]
      symm
      rw [@iSup_eq_top]
      intro b hb
      by_cases hb2 : b = ⊥
      · simp [hb2]
        use 1
        rw [← EReal.coe_sub]
        exact bot_lt_coe (inner ℝ l x - 1)
      push_neg at hb2
      have hb1 : b ≠ ⊤ := LT.lt.ne_top hb
      lift b to ℝ using ⟨hb1,hb2⟩
      use (inner ℝ l x) - b - 1
      rw [← EReal.coe_sub]
      apply EReal.coe_lt_coe_iff.2
      linarith
    push_neg at hc2
    lift convex_conjugate univ f l to ℝ with fcl
    · exact ⟨hc, hc2⟩
    simp
    refine Eq.symm (ciSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_)
    · intro a; simp; intro ha; repeat rw [← EReal.coe_sub]
      apply EReal.coe_le_coe_iff.mpr; linarith
    · intro w hw; use fcl; simpa
/-
This lemma establishes the fundamental equivalence between the value of the convex conjugate
and the concept of an affine minorant. It states that a real number `a` is an upper bound for
`f*(l)` if and only if the affine function `h(x) = ⟪l, x⟫ - a` is a lower bound for `f(x)`.
This directly connects the dual object (the conjugate) to the geometry of the primal function
(its affine supports).
-/
theorem const_le_cc_iff_affine_minorant {a : ℝ} {l : E} :
  Real.toEReal a ≥ convex_conjugate univ f l ↔ ∀ (x : E), f x ≥ ⟪l, x⟫ - a := by
    simp [convex_conjugate]
    constructor
    · intro hccleq x; specialize hccleq x
      by_cases hfx1 : f x = ⊤
      · simp [hfx1]
      push_neg at hfx1
      have hfx2 : f x ≠ ⊥ := by
        by_contra h
        simp [h] at hccleq
      lift f x to ℝ with fx
      · exact ⟨hfx1, hfx2⟩
      rw [← EReal.coe_sub] at *; rw [EReal.coe_le_coe_iff] at hccleq
      apply EReal.coe_le_coe_iff.mpr; rw [real_inner_comm]; linarith
    · intro hccleq x; specialize hccleq x
      by_cases hfx1 : f x = ⊤
      · simp [hfx1]
      push_neg at hfx1
      have hfx2 : f x ≠ ⊥ := by
        by_contra h
        simp [h] at hccleq
        rw [← EReal.coe_sub] at hccleq
        tauto
      lift f x to ℝ with fx
      · exact ⟨hfx1, hfx2⟩
      rw [← EReal.coe_sub] at *; rw [EReal.coe_le_coe_iff] at hccleq
      apply EReal.coe_le_coe_iff.mpr; rw [real_inner_comm]; linarith

end aux

/-
f** = affine sup
This does not require the function to be convex.
-/
/-
Theorem 12.2.
This theorem provides a geometric interpretation of the biconjugate function `f**`.
It states that the value of `f**(x)` is the supremum of all
affine minorants of `f` evaluated at `x`.
An affine minorant is an affine function `h(y) = ⟪l, y⟫ + w` that is
always less than or equal to `f(y)`.
This holds for any function `f`, not necessarily convex.
-/
omit [NormedAddCommGroup E] in
theorem bi_convex_conjugate_is_sup_of_affine_bound
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ∀ x ∈ univ, convex_conjugate univ (convex_conjugate univ f) x
    = ⨆ (l : E) (w : ℝ) (_ : ∀ x, ⟪l, x⟫ + w ≤ f x),(⟪l, x⟫ + w).toEReal := by
    intro x _; rw [convex_conjugate]; simp
    calc
       -- Step 1: Unfold the definition of the biconjugate `f**`.
      _ = ⨆ (l : E), ⨆ (a : ℝ) (_ : a ≥ convex_conjugate univ f l), (⟪l, x⟫ - a).toEReal := by
        rw [iSup, iSup]; congr; apply funext; intro l; apply inequ_cc_to_const
      _ = ⨆ (l : E) (a : ℝ) (_ : a ≥ convex_conjugate univ f l), (⟪l, x⟫ - a).toEReal := by simp
       -- Step 2: Replace the condition on `a` with the equivalent affine minorant condition.
      _ = ⨆ (l : E) (a : ℝ) (_ : ∀ x, f x ≥ ⟪l, x⟫ - a), (⟪l, x⟫ - a).toEReal := by
        rw [iSup, iSup]; congr; apply funext;
        intro l; rw [iSup, iSup]; congr; apply funext;
        intro a; rw [const_le_cc_iff_affine_minorant]
      -- Step 3: Change of variables from `a` to `w = -a` to
      -- match the standard form of an affine function.
      _ = ⨆ (l : E) (w : ℝ) (_ : ∀ x, f x ≥ ⟪l, x⟫ + w), (⟪l, x⟫ + w).toEReal := by
        rw [iSup, iSup]; congr; apply funext;
        intro l; apply le_antisymm
        · simp; intro a hx; apply le_iSup₂_of_le (-a)
          · rw [← EReal.coe_sub, ← EReal.coe_add]
            apply EReal.coe_le_coe_iff.mpr; linarith
          · intro x; specialize hx x
            rw [← EReal.coe_add, ← sub_eq_add_neg]; simpa
        · simp; intro w hx; apply le_iSup₂_of_le (-w)
          · rw [← EReal.coe_sub, sub_neg_eq_add]; simp
          · intro x; specialize hx x
            rw [← EReal.coe_sub, sub_neg_eq_add]; simpa

/-
1. f closed convex → f = affine sup

2. f is convex but not closed → cl f = affine sup
  cl f is proper
  cl f is convex

3. f** = affine sup

4. f** = cl(f)
-/
-- ConvexOn ℝ s f   → ConvexOn ℝ (dom s f) f
/-
Theorem 12.2.
This is a version of the Fenchel-Moreau theorem. It states that for a convex function `f`,
its biconjugate `f**` is equal to its closure `cl(f)`. This means the biconjugate operation
effectively "closes" the function by filling in any "holes"
in its epigraph, making it lower semicontinuous.
-/
theorem bi_convex_conjugate_eq_closure
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : ConvexOn ℝ (dom univ f) f) :
    convex_conjugate univ (convex_conjugate univ f) = Function.closure f univ := by
  ext x
  calc
    -- Start with the geometric interpretation of the biconjugate.
    _ = ⨆ (l : E) (w : ℝ) (_ : ∀ x ∈ univ, ⟪l, x⟫ + w ≤ f x), (⟪l, x⟫ + w).toEReal := by
      simp
      apply bi_convex_conjugate_is_sup_of_affine_bound
      trivial
      -- Relate the supremum of affine minorants to the closure of the function.
    _ = Function.closure f univ x := by
      sorry
      --rw [closure_of_convex_function_is_sup_of_affine_bound hf x]

-- theorem bi_convex_conjugate_eq_closure
--     [FiniteDimensional ℝ E] {f : E → EReal}
--     (hf : ConvexOn ℝ (dom univ f) f):
--     convex_conjugate univ (convex_conjugate univ f) = Function.closure f univ := by
--   sorry
/-
This is the most common form of the Fenchel-Moreau theorem. It states that for a proper,
lower semicontinuous (closed), convex function `f`,
its biconjugate is the function itself (`f** = f`).
This establishes that the biconjugate operation is the
identity on the space of closed convex functions.
-/
theorem bi_convex_conjugate_eq_self [FiniteDimensional ℝ E] {f : E → EReal}
    (cf : LowerSemicontinuous f) (hf : ConvexOn ℝ univ f) :
    convex_conjugate univ (convex_conjugate univ f) =  f := by
  nth_rw 2 [ccp_closure_is_self hf cf]
  apply bi_convex_conjugate_eq_closure (convexOn_dom_s_f_of_convexOn_s hf)
/-
This theorem shows that the convex conjugate operator is injective on the space of
proper, closed, convex functions. Two such functions are equal if and only if their
convex conjugates are equal. This ensures that no information is lost when taking the conjugate.
-/
theorem convex_conjugate_congr_iff {f g : E → EReal} [FiniteDimensional ℝ E]
    [ProperFunction univ f] [ProperFunction univ g]
    (hf : ConvexOn ℝ univ f) (hg : ConvexOn ℝ univ g)
    (hfl : LowerSemicontinuous f) (hgl : LowerSemicontinuous g) :
    f = g ↔ convex_conjugate univ f = convex_conjugate univ g := by
  constructor
  · intro h; rw [h]
  intro h
  rw [← bi_convex_conjugate_eq_self hfl hf, ← bi_convex_conjugate_eq_self hgl hg, h]

end bi_conjugate

/-
This theorem proves that the closure of a proper function `f` is always lower semicontinuous.
The proof strategy is to show that the epigraph of the closure function is a closed set.
It uses the key fact that the epigraph of the closure of a function is equal to the closure
of the epigraph of the original function (`closure (epi f) = epi (cl f)`). Since the closure
of any set is always closed, the proof is complete.
-/
omit [InnerProductSpace ℝ E] in
theorem univ_convex_closure_semicontinuous_of_proper (f : E → EReal) [hp : ProperFunction univ f] :
    LowerSemicontinuous (Function.closure f univ) := by
    -- The proof strategy is to show that the epigraph of the closure function is a closed set.
  rw [lowerSemicontinuous_iff_isClosed_epigraph]
  have : {p : E × EReal | Function.closure f univ p.1 ≤ p.2}
      = {(x, y) : E × EReal | x ∈ univ ∧ LowerSemicontinuousHull univ f x ≤ y} := by
    ext x; simp [Function.closure, hp]
  -- Use the key identity: epi (cl f) = closure (epi f).
  rw [this, ← closure_epi_eq_epi_closure isClosed_univ]
  -- The closure of any set is closed by definition.
  apply isClosed_closure

-- instance univ_convex_closure_proper' (f : E → EReal) [hp : ProperFunction univ f]
--     (hc : ConvexOn ℝ (dom univ f) f) [FiniteDimensional ℝ E]:
--     ProperFunction univ (Function.closure f univ) where
--   uninfinity := by
--     intro x _
--     -- simp [Function.closure, hp, LowerSemicontinuousHull]
--     rw [← bi_convex_conjugate_eq_closure hc]
--     -- exact convex_conjugate_ne_bot_s univ (convex_conjugate univ f) x trivial
--     sorry
--   existence_of_finite_value := by
--     right; obtain hp1 := hp.2
--     simp at hp1; rcases hp1 with ⟨x, hx⟩
--     use x; constructor; trivial
--     exact lt_of_le_of_lt (closure_le_self univ f x (by trivial)) hx

section Conevx_and_lowersemicontinous_proper

variable (s : Set E) (f : E → EReal)

/-
This lemma proves that the convex conjugate of any function `f` is always a convex function.
The proof considers three cases:
1. `f` is a proper function, where the result follows
from a direct proof (`convex_conjugate_convex`).
2. `f` is identically `⊤`, in which case `f*` is identically `⊥`, which is convex.
3. `f` is not proper and not identically `⊤`, which implies `f` must take the value `⊥` somewhere.
   In this case, `f*` is identically `⊤`, which is also convex.
-/
lemma convex_conjugate_is_convex [FiniteDimensional ℝ E] :
    ConvexOn ℝ univ (convex_conjugate univ f) := by
    by_cases hf : ProperFunction univ f
    · exact convex_conjugate_convex
    by_cases hf_pinf : f = ⊤
    · rw [conjugate_of_top]
      · apply convex_on_n_inf
        simp
      apply hf_pinf
    rw [conjugate_of_bot_exist']
    · apply convex_on_p_top
      simp
    have h_not_proper: ∃ x, f x = ⊥ ∨ f = ⊤ := by
      by_cases h_exists_bot : ∃ x, f x = ⊥
      · obtain ⟨x, hx⟩ := h_exists_bot
        exact ⟨x, Or.inl hx⟩
      · push_neg at h_exists_bot
        have h_bot_univ : ∀ x ∈ univ, f x ≠ ⊥ := fun x _ => h_exists_bot x
        have h_top : ∀ x, f x = ⊤ :=
          fun x ↦ top_of_ne_bot_of_ne_proper hf h_bot_univ  (Set.mem_univ x)
        have h_equality : f = ⊤ := by
          funext x; exact h_top x
        exact ⟨0, Or.inr h_equality⟩
    rcases h_not_proper with ⟨x, hx⟩
    rcases hx with (h_bot | h_top)
    · exact ⟨x, h_bot⟩
    · exact False.elim (hf_pinf h_top)

/-
This lemma proves that the convex conjugate of any function `f` is always lower semicontinuous.
The proof is based on the fact that the convex conjugate is the supremum of a family of
affine functions `y ↦ ⟪x, y⟫ - f x`. Since each of these affine functions is continuous (and thus
lower semicontinuous), their pointwise supremum is also lower semicontinuous.
-/
lemma lowerSemicontinuous_convex_conjugate :
    LowerSemicontinuous (convex_conjugate univ f) := by
  intro x
  let g_x (x : E) : E → EReal := fun y => ⟪x, y⟫ - f x
  have h_continuous : ∀ x, Continuous (g_x x) := by
    intro x
    apply EReal.continuous_inner_sub x
  have h_sup_lower_semicontinuous : LowerSemicontinuous (fun y => ⨆ x, g_x x y) := by
    apply lowerSemicontinuous_iSup (fun i => (h_continuous i).lowerSemicontinuous)
  unfold convex_conjugate
  simp
  exact h_sup_lower_semicontinuous x

/-
A small utility lemma for `EReal` arithmetic, proving `a - (-b) = a + b`.
-/
lemma sub_neg_eq_add_EReal_Real {a : EReal} {b : ℝ} : a - -b = a + b := by
  by_cases h1 : a = ⊤
  · rw [h1] ; rfl
  by_cases h2 : a = ⊥
  · rw [h2] ; rfl
  lift a to ℝ using ⟨h1, h2⟩
  norm_cast
  linarith

/-
rockefeller Coro. 12.1.2
This lemma, a corollary of the geometric Hahn-Banach theorem, states that any proper convex
function `f` is bounded below by at least one affine function. This is a fundamental result
used to prove that the conjugate of a proper convex function is also proper.
-/
lemma CCP_lower_bounded_by_affine [FiniteDimensional ℝ E]
  (hfp : ProperFunction univ f) (hfc : ConvexOn ℝ (dom univ f) f) :
  ∃ (a : E) (b : ℝ), ∀ (x : E), f x ≥ ⟪x, a⟫ - b := by --wyj
    -- First, we prove the result for the closure of f, `cl(f)`.
    sorry
    -- obtain ⟨L⟩ := Nonempty_low_affine
    --     (univ_convex_closure_proper f (convexOn_s_of_convexOn_dom_s_f hfc))
    --     (univ_convex_closure_convex f hfc)
    --     (closure_is_closed f isClosed_univ)
    -- rcases (exist_of_low_affine L) with ⟨l, w, hz, _⟩
    -- use l
    -- use -w
    -- intro x
    -- simp
    -- rw [sub_neg_eq_add_EReal_Real, real_inner_comm]
    -- -- The result for `f` follows from `f ≥ cl(f)` and `cl(f)` being bounded below.
    -- exact le_trans (hz x trivial) (closure_le_self univ f x trivial)

/-
A specialized utility lemma for rearranging `EReal` inequalities involving inner products.
-/
lemma EReal_ge_sub_of_ge_sub_specialcase {a c : E} {b : ℝ} {d : EReal} (hd : d > ⊥)
    (hge : d ≥ ⟪c, a⟫ - b) :
  b ≥ ⟪c, a⟫ - d := by
    by_cases h1 : d = ⊤
    · simp [h1]
    lift d to ℝ using ⟨h1, LT.lt.ne_bot hd⟩
    norm_cast at hge ⊢
    linarith

/-
This instance proves a crucial property: the convex conjugate of a proper convex function
is itself a proper function.
- `uninfinity`: This part is straightforward as the conjugate is always greater than `⊥`.
- `existence_of_finite_value`: This is the main part. It uses the fact that a proper convex
  function is bounded below by an affine function `⟪x, a⟫ - b`. This directly implies that
  the conjugate `f*(a)` is bounded above by `b`, and therefore must be finite.
-/
instance proper_convex_proper_conjugate [FiniteDimensional ℝ E] (hfp : ProperFunction univ f)
    (hfc : ConvexOn ℝ (dom univ f) f) : ProperFunction univ (convex_conjugate univ f) where
  uninfinity := by --wyj
    intro x _
    apply convex_conjugate_ge_bot_univ'
  existence_of_finite_value := by
    right
    -- Find an affine function `⟪x, a⟫ - b` that is a minorant of `f`.
    rcases CCP_lower_bounded_by_affine f hfp hfc with ⟨a, b, hab⟩
    have h₂ : ∀(x : E), b ≥ ⟪x, a⟫ - f x := by
      intro x
      apply EReal_ge_sub_of_ge_sub_specialcase
      apply hfp.uninfinity ; trivial
      exact hab x
    use a
    simp [convex_conjugate]
    -- This implies that `f*(a) = sup_x (⟪x, a⟫ - f x) ≤ b`, so `f*(a)` is finite.
    apply lt_of_le_of_lt
    · simp
      exact fun i ↦ h₂ i
    exact coe_lt_top b

/-
This instance proves that the closure of a proper convex function is also a proper function.
- `uninfinity`: Proved by using `cl(f) = f**` and showing that `f**` is nowhere `⊥`.
- `existence_of_finite_value`: Proved by noting that `cl(f) ≤ f`, so if `f` is finite
  at some point `x`, `cl(f)` cannot be `⊤` everywhere.
-/
instance univ_convex_closure_proper' (f : E → EReal) [hp : ProperFunction univ f]
    (hc : ConvexOn ℝ (dom univ f) f) [FiniteDimensional ℝ E] :
    ProperFunction univ (Function.closure f univ) where
  uninfinity := by
    intro x _
    rw [← bi_convex_conjugate_eq_closure hc]
    have : ProperFunction univ (convex_conjugate univ f) := by
      exact proper_convex_proper_conjugate f hp hc
    apply convex_conjugate_ne_bot_s _ (by simp) _ (by trivial)
  existence_of_finite_value := by
    right; obtain hp1 := hp.2
    simp at hp1; rcases hp1 with ⟨x, hx⟩
    use x; constructor
    · trivial
    exact lt_of_le_of_lt (closure_le_self univ f x (by trivial)) hx


end Conevx_and_lowersemicontinous_proper

section closure_conjugate
/-
This theorem proves a key result from Rockafellar's "Convex Analysis" (Theorem 12.2):
the convex conjugate of a function's closure is the same as the convex conjugate of the
original function, i.e., `(cl f)* = f*`.

The proof is elegant:
1. Use `cl(f) = f**` (Fenchel-Moreau).
2. The expression becomes `(f**)*`.
3. The conjugate of a biconjugate is the original conjugate, `(f**)* = f*`. This relies on
   the fact that `f*` is already a closed convex function, so `(f*)* = f*`.
-/
theorem convex_conjugate_closure_eq_convex_conjugate [FiniteDimensional ℝ E] {f : E → EReal}
    [hp : ProperFunction univ f] (hf : ConvexOn ℝ univ f) :
    convex_conjugate univ (f.closure univ) = convex_conjugate univ f := by
  -- Step 1: Replace `cl(f)` with its biconjugate `f**`.
  rw [← bi_convex_conjugate_eq_closure (convexOn_dom_s_f_of_convexOn_s hf)]
  have :  ProperFunction univ (convex_conjugate univ f) := by
    apply proper_convex_proper_conjugate f hp
    exact convexOn_dom_s_f_of_convexOn_s hf
  -- Step 2: The conjugate of a biconjugate is the original conjugate.
  -- This is because `f*` is already closed and convex, so `(f*)** = f*`.
  -- The expression is `(f**)*`, which is the conjugate of `(f*)*`.
  rw [bi_convex_conjugate_eq_self]
  · exact lowerSemicontinuous_convex_conjugate f
  exact convex_conjugate_is_convex f

end closure_conjugate

section equiv

def ProperClosedConvexFunction (E) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  {f: E → EReal | ProperFunction univ f ∧ LowerSemicontinuous f ∧ ConvexOn ℝ (dom univ f) f}

/-
Corollary 12.2.1
This lemma proves that the convex conjugate operation defines a bijection on the space of proper,
closed, and convex functions. Specifically, the conjugate map
`f ↦ f*` where `f*(y) = sup_x (⟪x, y⟫ - f(x))`
is a permutation of `ProperClosedConvexFunction E`, with inverse given by taking
the conjugate again: `(f*)* = f`.

Proof Idea:
1. `toFun`: We must show that `f*` is proper, closed, and convex.
  - Properness: Follows from `proper_convex_proper_conjugate`, which uses the fact
    that any proper convex function is bounded below by an affine function.
  - Closure (lower semicontinuity): Follows from `lowerSemicontinuous_convex_conjugate`,
    which uses that `f*` is the supremum of continuous (affine) functions.
  - Convexity: Follows from `convex_conjugate_is_convex`, proven by noting `f*`
    is the supremum of affine (hence convex) functions.

2. `invFun`: The inverse map is also the conjugate operation `f ↦ f*`,
  and the same argument as above shows it maps proper closed convex functions to
  proper closed convex functions.

3. `left_inv`: We must show `(f*)* = f` for any proper closed convex function `f`.
  This is the content of the Fenchel-Moreau theorem (`bi_convex_conjugate_eq_self`)

4. `right_inv`: We must show `(f*)* = f` when starting from `f = g*` for some
  proper closed convex function `g`. The proof is identical to `left_inv` because
  `f = g*` is itself a proper closed convex function (by the argument in `toFun`).
-/
noncomputable def convex_conjugate_equiv
    (E) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    Equiv.Perm (ProperClosedConvexFunction E) where
  toFun := fun f ↦ Subtype.mk ((convex_conjugate univ) f.val) (by
    simp [ProperClosedConvexFunction]
    let h := f.property
    simp [ProperClosedConvexFunction] at h
    constructor
    -- Prove that `f*` is proper.
    · have : ConvexOn ℝ (dom univ f.val) f.val := by
        simp [dom]
        exact h.2.2
      exact proper_convex_proper_conjugate f.val h.1 this
    · constructor
      -- Prove that `f*` is closed.
      · exact lowerSemicontinuous_convex_conjugate f.val
      -- Prove that `f*` is convex.
      -- First prove convexity on all of `univ`.
      · have : ConvexOn ℝ (dom univ (convex_conjugate univ f.val))
            (convex_conjugate univ f.val) := by
          -- The restrict to the effective domain `dom`.
          apply convexOn_dom_s_f_of_convexOn_s
          exact convex_conjugate_is_convex f.val
        simp [dom] at this
        exact this
  )
  -- The inverse function is also the conjugate operation.
  invFun := fun f ↦ Subtype.mk ((convex_conjugate univ) f.val) (by
    simp [ProperClosedConvexFunction]
    let h := f.property
    simp [ProperClosedConvexFunction] at h
    constructor
    · have : ConvexOn ℝ (dom univ f.val) f.val := by
        simp [dom]
        exact h.2.2
      exact proper_convex_proper_conjugate f.val h.1 this
    · constructor
      · exact lowerSemicontinuous_convex_conjugate f.val
      · have : ConvexOn ℝ (dom univ (convex_conjugate univ f.val))
            (convex_conjugate univ f.val) := by
          apply convexOn_dom_s_f_of_convexOn_s
          exact convex_conjugate_is_convex f.val
        simp [dom] at this
        exact this
  )
  left_inv := by
    unfold LeftInverse
    simp
    intro f hf
    simp [ProperClosedConvexFunction] at hf
    haveI : ProperFunction univ f := hf.1
    have : ConvexOn ℝ (dom univ f) f := by
      simp [dom]
      exact hf.2.2
    -- Apply the Fenchel-Moreau theorem for proper, convex, closed function.
    exact bi_convex_conjugate_eq_self hf.2.1 (convexOn_s_of_convexOn_dom_s_f this)
  -- The proof is identical to `left_inv` because `f` is also a proper closed convex function.
  right_inv := by
    unfold RightInverse LeftInverse
    simp
    intro f hf
    simp [ProperClosedConvexFunction] at hf
    haveI : ProperFunction univ f := hf.1
    have : ConvexOn ℝ (dom univ f) f := by
      simp [dom]
      exact hf.2.2
    exact bi_convex_conjugate_eq_self hf.2.1 (convexOn_s_of_convexOn_dom_s_f this)

end equiv

section convex_conjugate_mono

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-
This theorem establishes a fundamental property of the convex conjugate operation,
known as order-reversing. if `f₁ ≤ f₂` pointwise on a set `s₂`,
and `s₂ ⊆ s₁`, then their convex conjugates satisfy the reversed inequality:
`f₂* ≤ f₁*`.

Proof Idea:
The proof is direct and constructive. We need to show that for any `y ∈ E`,
`f₂*(y) ≤ f₁*(y)`, which by definition means:
`sup_{x ∈ s₂} (⟪x, y⟫ - f₂(x)) ≤ sup_{x ∈ s₁} (⟪x, y⟫ - f₁(x))`
which can be proved by showing that for any `x ∈ s₂`,
`⟪x, y⟫ - f₂(x) ≤ sup_{x ∈ s₁} (⟪x, y⟫ - f₁(x))`.
To show that, we have: for any `x ∈ s₂`,
`⟪x, y⟫ - f₂(x) ≤ ⟪x, y⟫ - f₁(x) ≤ sup_{x ∈ s₁} (⟪x, y⟫ - f₁(x))`.
-/
theorem convex_conjugate_mono (s₁ s₂ : Set E) (f₁ f₂ : E → EReal)
    (hle : ∀ x ∈ s₂, f₁ x ≤ f₂ x) (hs : s₂ ⊆ s₁) :
    convex_conjugate s₂ f₂ ≤  convex_conjugate s₁ f₁ := by
  intro x
  simp [convex_conjugate]
  intro i is2
  -- Since `s₂ ⊆ s₁`, we have `i ∈ s₁`.
  have is1 : i ∈ s₁ := by exact hs is2
  calc
    -- Since `f₁(i) ≤ f₂(i)`, subtracting `f₂(i)` gives a smaller value than subtracting `f₁(i)`.
    -- The inner product term remains the same.
    _ ≤ ↑(inner ℝ i x) - f₁ i :=
      EReal.sub_le_sub (EReal.coe_le_coe (le_refl (inner ℝ i x))) (hle i is2)
    -- The term `⟪i, x⟫ - f₁(i)` is one of the terms in the supremum defining `f₁*(x)`.
    _ ≤ ⨆ x_1 ∈ s₁, ↑(inner ℝ x_1 x) - f₁ x_1 :=
      le_biSup (fun x_1 ↦ ↑(inner ℝ x_1 x) - f₁ x_1) is1

end convex_conjugate_mono

section convex_conjugate_in_intrinsic_interior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Corollary 12.2.2
-/

theorem convex_conjugate_in_ri (s : Set E) (f : E → EReal) (hc : ConvexOn ℝ (dom s f) f) :
    convex_conjugate s f = fun y ↦ ⨆ x ∈ intrinsicInterior ℝ (dom s f), ⟪x, y⟫ - f x := sorry


end convex_conjugate_in_intrinsic_interior

section linearMap_convex_conjugate

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def ContinuousLinearEquiv.adjoint (A : E ≃L[ℝ] F) : F ≃L[ℝ] E where
  toFun := A.toContinuousLinearMap.adjoint
  map_add' := A.toContinuousLinearMap.adjoint.map_add'
  map_smul' := A.toContinuousLinearMap.adjoint.map_smul'
  continuous_toFun := A.toContinuousLinearMap.adjoint.cont
  invFun := A.symm.toContinuousLinearMap.adjoint
  left_inv := fun x ↦
    by rw [←ContinuousLinearMap.comp_apply, ←ContinuousLinearMap.adjoint_comp]; simp
  right_inv := fun x ↦
    by rw [←ContinuousLinearMap.comp_apply, ←ContinuousLinearMap.adjoint_comp]; simp
  continuous_invFun := A.symm.toContinuousLinearMap.adjoint.cont

/-
Theorem 12.3
-/

theorem linearMap_convex_conjugate {a a' : E} {α : EReal} (g : E → EReal)
    (hg : ConvexOn ℝ (dom univ g) g) (A : E ≃L[ℝ] E) :
    convex_conjugate univ (fun x ↦ g (A (x - a)) + ⟪x, a'⟫ + α) =
    fun y ↦ (convex_conjugate univ g) (A.adjoint.symm (y - a')) + ⟪y, a⟫ - α - ⟪a, a'⟫ := sorry

end linearMap_convex_conjugate
