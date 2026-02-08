/-
Copyright (c) 2025 Zichen Wang, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
/-!
# EReal Lemmas
This file contains various lemmas related to the calculation via `EReal` numbers.

-/

open Filter BigOperators Set EReal
open scoped Pointwise Topology

@[simp]
/-
Instance. Scalar multiplication on extended reals agrees with real multiplication: z • x = z * x.
-/
noncomputable instance real_smul_ereal : SMul ℝ EReal := ⟨fun a x => a * x⟩

/-
Lemma. Scalar multiplication on extended reals agrees with real multiplication: z • x = z * x.
-/
@[simp]
lemma EReal.smul_eq_mul (z : ℝ) (v : EReal) : z • v = z * v := by rfl

section aux

/-
Lemma. For any positive real a, multiplying by a preserves finiteness: a * b < +∞ ↔ b < +∞.
-/
lemma mul_lt_top_iff_lt_top {a : ℝ} (ha : a > 0) {b : EReal} :
    a * b < ⊤ ↔ b < ⊤ := by
  constructor
  · intro h; by_contra ht; push_neg at ht; simp at ht
    rw [ht, coe_mul_top_of_pos ha] at h; simp at h
  intro h
  by_cases hb : b = ⊥
  · rw [hb, EReal.coe_mul_bot_of_pos ha]; simp
  lift b to ℝ using ⟨LT.lt.ne_top h, hb⟩
  rw [← coe_mul]; exact coe_lt_top (a * b)

/-
Lemma. A nonnegative real times a finite extended real is finite:
  if a ≥ 0 and b < +∞, then a * b < +∞.
-/
lemma mul_pos_lt_top {a : ℝ} (ha : a ≥ 0) {b : EReal} (hb : b < ⊤) :
    a * b < ⊤ := by
  by_cases ha1 : a = 0
  · rw [ha1]; simp
  rwa [mul_lt_top_iff_lt_top (by positivity)]

/-
Lemma. A nonnegative real times an extended real above −∞ stays above −∞:
  if 0 ≤ b and ⊥ < c, then ⊥ < b * c.
-/
lemma mul_pos_gt_bot {b : ℝ} {c : EReal} (hb : 0 ≤ b) (hc : ⊥ < c) : ⊥ < b * c := by
  by_cases hb1 : b = 0
  · rw [hb1]; simp
  have : b > 0 := by positivity
  by_cases hc1 : c = ⊤
  · rw [hc1, EReal.coe_mul_top_of_pos this]; simp
  lift c to ℝ using ⟨hc1, LT.lt.ne_bot hc⟩
  rw [← coe_mul]; exact bot_lt_coe (b * c)

/-
Lemma. Distributivity of scalar action: (a + b) • x = a • x + b • x (for finite x).
-/
lemma EReal.add_smul (a b : ℝ) {x : EReal} (hx : x > ⊥) (hx1 : x < ⊤) :
    (a + b) • x = a • x + b • x := by
  have h1 : (a + b) • x = (a + b) * x := rfl
  rw [h1]
  lift x to ℝ using ⟨LT.lt.ne_top hx1, LT.lt.ne_bot hx⟩
  calc
    _ = ((a + b) * x).toEReal := EReal.coe_eq_coe_iff.mpr rfl
    _ = (a * x + b * x).toEReal := by rw [add_mul]

/-
Lemma. Distributivity over subtraction: (a − b) • x = a • x − b • x (for finite x).
-/
lemma EReal.sub_smul (a b : ℝ) {x : EReal} (hx : x > ⊥) (hx1 : x < ⊤) :
    (a - b) • x = a • x - b • x := by
  rw [sub_eq_add_neg, EReal.add_smul, sub_eq_add_neg]
  · simp only [real_smul_ereal, smul_eq_mul, coe_neg, neg_mul]
  · exact hx
  exact hx1

/-
Lemma. Dividing a finite extended real by a positive
  real remains finite: if a < +∞ and b > 0, then a / b < +∞.
-/
lemma EReal.div_lttop_of_lttop {a : EReal} {b : ℝ} (ha : a < ⊤) (hb : b > 0) : a / b < ⊤ := by
  induction a with
  | top => contradiction
  | bot => rw [EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr hb) (coe_ne_top b)]; exact ha
  | coe a => rw [← EReal.coe_div]; exact coe_lt_top (a / b)

/-
Lemma. Subtracting a finite extended real from a
  finite one remains finite: if a < +∞ and ⊥ < b < +∞, then a − b < +∞.
-/
lemma EReal.sub_lttop_of_lttop {a b : EReal}
    (ha : a < ⊤) (hb₁ : b > ⊥) (hb₂ : b < ⊤) : a - b < ⊤ := by
  lift b to ℝ using ⟨LT.lt.ne_top hb₂, LT.lt.ne_bot hb₁⟩
  induction a with
  | top => contradiction
  | bot => simp
  | coe a => rw [← EReal.coe_sub]; exact coe_lt_top (a - b)

/-
Lemma. A convex combination with weights a,b ≥ 0 and a + b = 1 reproduces x: a • x + b • x = x.
-/
lemma EReal.combo_self (a b : ℝ) (x : EReal) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • x = x := by
  have h : a • x + b • x = (a + b) * x := by
    refine Eq.symm (EReal.right_distrib_of_nonneg ?ha ?hb)
    repeat simpa
  have : a.toEReal + b.toEReal = (a + b).toEReal := by simp
  rw [h, this, hab]
  simp only [EReal.coe_one, one_mul]

/-
Lemma. Self-subtraction is nonpositive in extended reals: x − x ≤ 0.
-/
lemma EReal.le_zero_of_self_sub_self (x : EReal) : x - x ≤ 0 := by
  by_cases hx :  x = ⊤
  · rw [hx]; simp
  by_cases hx' :  x = ⊥
  · rw [hx']; simp
  lift x to ℝ using ⟨hx, hx'⟩
  apply EReal.coe_nonpos.mpr (by simp)

/-
Lemma. From a + b ≤ c (with finiteness assumptions) one gets 0 ≤ c − a − b.
-/
lemma EReal.le_zero_of_add_le {a c : EReal} {b : ℝ} (h : a + b ≤ c)
    (ha1 : a ≠ ⊥) (ha2 : a ≠ ⊤) (hc1 : c ≠ ⊥) :
    0 ≤ c - a - b := by
  lift a to ℝ using ⟨ha2, ha1⟩
  by_cases hc2 : c = ⊤
  · rw [hc2]; simp
  lift c to ℝ using ⟨hc2, hc1⟩
  suffices 0 ≤ (c - a - b).toEReal by exact this
  have : a + b ≤ c := by exact EReal.coe_le_coe_iff.mp h
  refine EReal.coe_nonneg.mpr ?intro.intro.a
  linarith

/-
Lemma. Subtracting b then adding b returns a (for finite b): a − b + b = a.
-/
lemma EReal.sub_add {a b : EReal} (hb1 : b ≠ ⊥) (hb2 : b ≠ ⊤) : a - b + b = a := by
  lift b to ℝ using ⟨hb2, hb1⟩
  by_cases ha : a = ⊥
  · rw [ha]
    simp
  by_cases ha' : a = ⊤
  · rw [ha']
    simp
  lift a to ℝ using ⟨ha', ha⟩
  suffices (a - b + b).toEReal = a by exact this
  simp

/-
Lemma. Adding +∞ yields +∞ (when the other term is above −∞): a + ⊤ = ⊤.
-/
lemma EReal.top_of_top_add {a : EReal} (h : a > ⊥) : a + ⊤ = ⊤ :=
  add_top_iff_ne_bot.mpr <| LT.lt.ne_bot h

/-
Lemma. Nonnegative scaling of +∞ cannot produce −∞: for a ≥ 0, a • ⊤ ≠ ⊥.
-/
lemma EReal.smul_top_ne_bot {a : ℝ} (ha : a ≥ 0) : a • ⊤ ≠ (⊥ : EReal) := by
  by_cases ha1 : a = 0
  · rw [ha1];simp
  refine bot_lt_iff_ne_bot.mp ?_
  simp
  have : a * (⊤ : EReal) = ⊤ := by
    refine coe_mul_top_of_pos ?h
    exact lt_of_le_of_ne ha fun a_1 ↦ ha1 (id (Eq.symm a_1))
  rw [this]
  exact bot_lt_top

/-
Lemma. The product of two finite, non-bottom extended reals is above −∞: a * b > ⊥.
-/
lemma EReal.mul_gt_bot {a b : EReal}
    (ha1 : a > ⊥) (ha2 : a < ⊤) (hb1 : b > ⊥) (hb2 : b < ⊤) :
    a * b > ⊥ := by
  lift a to ℝ using ⟨LT.lt.ne_top ha2, LT.lt.ne_bot ha1⟩
  lift b to ℝ using ⟨LT.lt.ne_top hb2, LT.lt.ne_bot hb1⟩
  exact Batteries.compareOfLessAndEq_eq_lt.mp rfl

#check le_mul_of_one_le_right

/-
Lemma. Nonnegative scalar preserves being above −∞: if a ≥ 0 and ⊥ < b then ⊥ < a • b.
-/
lemma EReal.smul_gt_bot_of_ge_zero {a : ℝ} {b : EReal}
    (ha : a ≥ 0) (hb : b > ⊥) :
    a • b > ⊥ := by
  by_cases hb2 : b = ⊤
  · rw [hb2]
    by_cases ha0 : a = 0
    · simp [ha0]
    push_neg at ha0
    have hapos : a > 0 := lt_of_le_of_ne ha (id (Ne.symm ha0))
    have : (⊤:EReal) > a := coe_lt_top a
    by_cases ha1 : a > 0
    · simp [coe_mul_top_of_pos hapos]
    have : a = 0 := by linarith
    rw [this]; simp
  apply EReal.mul_gt_bot
  · simp
  · simp
  · exact hb
  exact Ne.lt_top' fun a ↦ hb2 (id (Eq.symm a))

/-
Lemma. Nonnegative scalar preserves finiteness
  (under finiteness of the other factor): if ⊥ < b < +∞, then a • b < +∞.
-/
lemma EReal.smul_lt_top_of_ge_zero {a : ℝ} {b : EReal}
    (hb1 : b < ⊤) (hb2 : b > ⊥) :
    a • b < ⊤ := by
  simp;
  lift b to ℝ using ⟨LT.lt.ne_top hb1, LT.lt.ne_bot hb2⟩
  rw [← EReal.coe_mul];
  exact coe_lt_top (a * b)

/-
Lemma. Scalar multiplication distributes over addition on
  extended reals (under the stated finiteness/positivity hypotheses).
-/
lemma EReal.smul_add_pre (a : ℝ) {x y : EReal} (hx : x > ⊥) (hx1 : x < ⊤) (hy : y > ⊥) :
    a • (x + y) = a • x + a • y := by
  have h1 : a • (x + y) = a * (x + y) := rfl
  have h2 (z : EReal) : a • z = a * z := rfl
  rw [h1, h2 x, h2 y]
  lift x to ℝ using ⟨LT.lt.ne_top hx1, LT.lt.ne_bot hx⟩
  by_cases hy1 : y < ⊤
  · lift y to ℝ using ⟨LT.lt.ne_top hy1, LT.lt.ne_bot hy⟩
    calc _
      _ = (a * x + a * y).toEReal := EReal.coe_eq_coe_iff.mpr (left_distrib a x y)
      _ = _ := by rfl
  rw [not_lt_top_iff.mp hy1, EReal.add_top_iff_ne_bot.mpr (LT.lt.ne_bot hx)]
  have ha : a > 0 ∨ a = 0 ∨ a < 0 := trichotomous a 0
  rcases ha with ha | ha | ha
  · rw [EReal.coe_mul_top_of_pos ha]
    rw [EReal.add_top_iff_ne_bot.mpr
    (LT.lt.ne_bot <| mul_gt_bot (EReal.bot_lt_coe a) (EReal.coe_lt_top a) hx hx1)]
  · rw [ha]
    simp
  rw [EReal.coe_mul_top_of_neg ha]
  exact Eq.symm (EReal.add_bot (↑a * x))

/-
Lemma. Scalar multiplication distributes over addition on
  extended reals (under the stated finiteness/positivity hypotheses).
-/
lemma EReal.smul_add (a : ℝ) {x y : EReal} (hx : x > ⊥) (hy : y > ⊥) :
    a • (x + y) = a • x + a • y := by
  by_cases hx1 : x < ⊤
  · exact smul_add_pre a hx hx1 hy
  by_cases hy1 : y < ⊤
  · rw [add_comm]
    nth_rw 2 [add_comm]
    exact smul_add_pre a hy hy1 hx
  have xtop : x = ⊤ := not_lt_top_iff.mp hx1
  have ytop : y = ⊤ := not_lt_top_iff.mp hy1
  have htop : (⊤ : EReal) + ⊤ = ⊤ := rfl
  have amul : a • (⊤ : EReal) = a * (⊤ : EReal) := rfl
  rw [xtop, ytop, htop, amul]
  have ha : a > 0 ∨ a = 0 ∨ a < 0 := trichotomous a 0
  rcases ha with ha | ha | ha
  · rw [EReal.coe_mul_top_of_pos ha]; rfl
  · rw [ha]; simp
  rw [EReal.coe_mul_top_of_neg ha]; rfl

/-
Lemma. Real multiplication distributes over
  addition: a * (x + y) = a * x + a * y (under the stated hypotheses).
-/
lemma EReal.smul_add' (a : ℝ) {x y : EReal} (hx : x > ⊥) (hy : y > ⊥) :
    a * (x + y) = a * x + a * y := by
  simpa using (EReal.smul_add a hx hy)

/-
Lemma. Scalar multiplication distributes over addition
  on extended reals (under the stated finiteness/positivity hypotheses).
-/
lemma EReal.pos_smul_add (a : ℝ) {x y : EReal} (ha : a > 0) :
    a • (x + y) = a • x + a • y := by
  by_cases hx : x = ⊥
  · rw [hx]; simp; rw [EReal.coe_mul_bot_of_pos ha]; simp
  by_cases hy : y = ⊥
  · rw [hy]; simp; rw [EReal.coe_mul_bot_of_pos ha]; simp
  apply EReal.smul_add
  · exact Ne.bot_lt' fun a ↦ hx (id (Eq.symm a))
  · exact Ne.bot_lt' fun a ↦ hy (id (Eq.symm a))

/-
Lemma. Real multiplication distributes over
  addition: a * (x + y) = a * x + a * y (under the stated hypotheses).
-/
lemma EReal.pos_smul_add' {a : ℝ} {x y : EReal} (ha : a > 0) :
    a * (x + y) = a * x + a * y := by
  simpa using (EReal.pos_smul_add a ha)

/-
Lemma. Rearrangement inequality in extended reals:
  from a ≥ b + c − d (with finiteness), deduce d − b ≥ c − a.
-/
lemma EReal.sub_ge_sub_of_ge_add_sub {a b c d : EReal} (h : a ≥ b + c - d)
  (ha1 : a ≠ ⊤) (ha2 : a ≠ ⊥)
  (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥)
  (hc1 : c ≠ ⊤) (hc2 : c ≠ ⊥)
  (hd1 : d ≠ ⊤) (hd2 : d ≠ ⊥) : d - b ≥ c - a := by
  lift a to ℝ using ⟨ha1, ha2⟩
  lift b to ℝ using ⟨hb1, hb2⟩
  lift c to ℝ using ⟨hc1, hc2⟩
  lift d to ℝ using ⟨hd1, hd2⟩
  rw [← EReal.coe_sub, ← EReal.coe_sub]
  rw [← EReal.coe_add, ← EReal.coe_sub] at h
  obtain := EReal.coe_le_coe_iff.1 h
  apply EReal.coe_le_coe_iff.2
  linarith

/-
Lemma. If a + b ≤ d and all terms are finite, then a is finite: a < +∞.
-/
lemma EReal.lt_top_of_add_le {a b d : EReal}
  (h : a + b ≤ d) (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥)
  (hd1 : d ≠ ⊤) (hd2 : d ≠ ⊥) : a < ⊤ := by
  lift b to ℝ using ⟨hb1, hb2⟩
  lift d to ℝ using ⟨hd1, hd2⟩
  have : Real.toEReal d < ⊤ := by simp
  by_contra ha
  push_neg at ha
  simp at ha
  simp [ha] at h

/-
Lemma. Basic inequality rearrangements with subtraction under finiteness hypotheses.
-/
lemma EReal.ge_add_sub {a b : EReal}
  (ha1 : a ≠ ⊤) (ha2 : a ≠ ⊥)
  (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥) : a ≥ a + (b - b) := by
  lift a to ℝ using ⟨ha1, ha2⟩
  lift b to ℝ using ⟨hb1, hb2⟩
  rw [← EReal.coe_sub, sub_eq_zero_of_eq rfl, ← EReal.coe_add, add_zero]

/-
Lemma. Basic inequality rearrangements with subtraction under finiteness hypotheses.
-/
lemma EReal.ge_add_sub_of_ge_add_sub
  {a b c d : EReal} (h : a ≥ b + c - d) (ha1 : a ≠ ⊤) (ha2 : a ≠ ⊥)
  (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥) (hc1 : c ≠ ⊤) (hc2 : c ≠ ⊥) (hd1 : d ≠ ⊤) (hd2 : d ≠ ⊥) :
  d ≥ b + c - a := by
  lift a to ℝ using ⟨ha1, ha2⟩
  lift b to ℝ using ⟨hb1, hb2⟩
  lift c to ℝ using ⟨hc1, hc2⟩
  lift d to ℝ using ⟨hd1, hd2⟩
  rw [← EReal.coe_add, ← EReal.coe_sub] at *
  apply EReal.coe_le_coe_iff.2
  obtain h' := EReal.coe_le_coe_iff.1 h
  linarith

/-
Lemma. Basic inequality rearrangements with subtraction under finiteness hypotheses.
-/
lemma EReal.ge_add_sub_of_ge_add {a b c d : EReal}
  (h₁ : a ≥ b + c) (h₂ : c ≥ d - e) (ha1 : a ≠ ⊤) (ha2 : a ≠ ⊥)
  (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥) (hc1 : c ≠ ⊤) (hc2 : c ≠ ⊥) (hd1 : d ≠ ⊤) (hd2 : d ≠ ⊥)
  (he1 : e ≠ ⊤) (he2 : e ≠ ⊥) : a ≥ b + d - e := by
  lift a to ℝ using ⟨ha1, ha2⟩
  lift b to ℝ using ⟨hb1, hb2⟩
  lift c to ℝ using ⟨hc1, hc2⟩
  lift d to ℝ using ⟨hd1, hd2⟩
  lift e to ℝ using ⟨he1, he2⟩
  rw [← EReal.coe_add, ← EReal.coe_sub] at *
  apply EReal.coe_le_coe_iff.2
  obtain h₁':= EReal.coe_le_coe_iff.1 h₁
  obtain h₂':= EReal.coe_le_coe_iff.1 h₂
  linarith

/-
Lemma. Subtracting a finite extended real yields a value strictly above −∞.
-/
lemma EReal.sub_lt_bot {a b : EReal}
    (ha1 : a ≠ ⊤) (ha2 : a ≠ ⊥) (hb1 : b ≠ ⊤) : a - b > ⊥ := by
  lift a to ℝ using ⟨ha1, ha2⟩
  by_cases hb2 : b = ⊥
  · rw [hb2, EReal.coe_sub_bot a]
    simp
  · push_neg at hb2
    lift b to ℝ using ⟨hb1, hb2⟩
    rw [← EReal.coe_sub]
    apply Ne.bot_lt
    apply EReal.coe_ne_bot

/-
Lemma. From a − b ≤ c (with finiteness) deduce a ≤ b + c.
-/
lemma EReal.le_add_of_sub_le {a b c : EReal} (h : a - b ≤ c) (ha1 : a ≠ ⊤) (ha2 : a ≠ ⊥)
  (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥) (hc1 : c ≠ ⊤) (hc2 : c ≠ ⊥) : a ≤ b + c := by
    lift a to ℝ using ⟨ha1, ha2⟩
    lift b to ℝ using ⟨hb1, hb2⟩
    lift c to ℝ using ⟨hc1, hc2⟩
    rw [← EReal.coe_sub] at h
    rw [← EReal.coe_add]
    obtain := EReal.coe_le_coe_iff.1 h
    apply EReal.coe_le_coe_iff.2
    linarith

/-
Lemma. An if-and-only-if relating the two side conditions
  (preserving the stated property in extended reals).
-/
lemma EReal.add_le_iff_sub_le (a b : ℝ) (c : EReal) :
    a + b ≤ c ↔ a - c ≤ -b := by
  rw [← EReal.coe_add, ← EReal.coe_neg]
  by_cases hc : c = ⊤
  · rw [hc]
    simp only [coe_add, le_top, sub_top, coe_neg, bot_le]
  by_cases hc' : c = ⊥
  · rw [hc']
    simp only [coe_add, le_bot_iff, add_eq_bot_iff, coe_ne_bot, or_self, coe_sub_bot, coe_neg,
      top_le_iff, neg_eq_top_iff]
  lift c to ℝ using ⟨hc, hc'⟩
  rw [EReal.coe_le_coe_iff]
  symm
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
  simp only [tsub_le_iff_right, le_neg_add_iff_add_le]
  ring_nf

/-
Lemma. A relationship involving subtraction in extended reals.
-/
lemma EReal.sub_eq_neg_add (a b : EReal) : a - b  = -b + a := by
  calc
    _ = a+(-b) := by rfl
    _ = _ := by exact AddCommMonoid.add_comm a (-b)

/-
Lemma. For any extended real number a which is not bottom, a + ⊤ = ⊤.
-/
lemma EReal.add_top_eq_top {a : EReal} (p : a > ⊥) : a + ⊤ = ⊤ := by
  by_cases h: a = ⊤
  · rw [h]; simp
  have : a ≠ ⊥ := by exact LT.lt.ne_bot p
  lift a to ℝ using ⟨h, this⟩
  exact rfl

/-
Lemma. For any extended real number a which is not top, ⊥ + a = ⊥.
-/
lemma EReal.bot_add_eq_bot {a : EReal} (p : a < ⊤) : ⊥ + a = ⊥ := by
  by_cases h: a = ⊥
  · rw [h]; simp
  have : a ≠ ⊤ := by exact LT.lt.ne_top p
  lift a to ℝ using ⟨this,h⟩
  exact rfl

/-
Lemma. A relationship involving subtraction in extended reals.
-/
lemma EReal.sub_add_eq_sub_sub {a b c : EReal} (hb : b ≠ ⊥) (hc : c ≠ ⊥) :
    a - (b + c) = a - b - c := by
  by_cases h: b = ⊤
  · by_cases h': c = ⊤
    · rw [h, h']; simp
    · lift c to ℝ using ⟨h', hc⟩
      rw [h]; simp
  · lift b to ℝ using ⟨h, hb⟩
    by_cases h': c = ⊤
    · rw [h']; simp
    · lift c to ℝ using ⟨h', hc⟩
      by_cases h'': a = ⊤
      · rw [h'']; simp; rfl
      by_cases h''c: a = ⊥
      · rw [h''c]; simp
      lift a to ℝ using ⟨h'', h''c⟩
      rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub]
      apply EReal.coe_eq_coe_iff.mpr
      linarith

/-
Lemma. For any extended real numbers a and b with a ≤ b, and real number c, then c * a ≤ c * b.
-/
lemma EReal.mul_pos_real_le {a b : EReal} {c : ℝ} (hab : a ≤ b) (hc : c > 0) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left hab (EReal.coe_nonneg.mpr (le_of_lt hc))

/-
Lemma. Positive real factors pull out of finite sums in extended reals: a * (∑ f i) = ∑ a * f i.
-/
lemma EReal.finset_mul_sum [DecidableEq ι] :
    (τ : Finset ι) → (f : ι → EReal) → (a : ℝ) → (hpos : a > 0) →
    a * ∑ i ∈ τ, f i = ∑ i ∈ τ, a * f i := by
  apply Finset.induction
  · simp_all
  intro a τ ha hf f a1 ha1
  simp [ha]
  specialize hf f a1 ha1
  rw [EReal.pos_smul_add' ha1]
  rw [hf]

namespace EReal

/-
Lemma. Multiplication by a positive real is
  order-preserving on extended reals: a ≤ b → γ * a ≤ γ * b.
-/
lemma mul_lt_mul_left' {γ : ℝ} (hpos : γ > 0) : ∀ a b : EReal, a ≤ b → γ * a ≤ γ * b :=
  fun _ _ a => mul_pos_real_le a hpos

/-
Lemma. Multiplication by a positive real reflects and preserves order: γ * a ≤ γ * b ↔ a ≤ b.
-/
lemma mul_le_mul_left {γ : ℝ} (hpos : γ > 0) : ∀ a b : EReal, γ * a ≤ γ * b ↔ a ≤ b := by
  intro a b
  have hone : (γ⁻¹).toEReal * γ = 1 := by
    apply EReal.coe_eq_coe_iff.mpr
    field_simp
  constructor
  · by_cases hb : b = ⊤
    · rw [hb]
      simp only [le_top, implies_true]
    intro h
    have h' : (γ⁻¹).toEReal * (γ * a) ≤ (γ⁻¹).toEReal * (γ * b) := by
        apply mul_lt_mul_left'
        · simp only [gt_iff_lt, inv_pos]
          exact hpos
        exact h
    rw [← mul_assoc, ← mul_assoc, hone] at h'
    simp only [one_mul] at h'
    exact h'
  apply mul_lt_mul_left' hpos

/-
Lemma. Adding a fixed real on the left preserves and reflects order on extended reals.
-/
lemma add_le_add_left (γ : ℝ) : ∀ a b : EReal, γ + a ≤ γ + b ↔ a ≤ b := by
  intro a b
  constructor
  · intro h
    have h' : - γ + γ + a ≤ - γ + γ + b := by
      rw [add_assoc, add_assoc]
      exact _root_.add_le_add_left h (-↑γ)
    have hzero : -γ.toEReal + γ = 0 := by
      rw [← EReal.coe_neg, ← EReal.coe_add]
      simp only [neg_add_cancel, coe_zero]
    rw [hzero] at h'
    simp only [zero_add] at h'
    exact h'
  intro h
  exact _root_.add_le_add_left h γ

/-
Lemma. Adding a fixed real on the right preserves and reflects order on extended reals.
-/
lemma add_le_add_right (γ : ℝ) : ∀ a b : EReal, a + γ ≤ b + γ ↔ a ≤ b := by
  intro a b
  rw [add_comm a γ, add_comm b γ]
  exact add_le_add_left γ a b

/-
Lemma. Cancelling a positive real in a product/division: γ * x / γ = x.
-/
@[simp]
lemma mul_div_self {γ : ℝ} (hpos : γ > 0) (x : EReal) : γ * x / γ = x := by
  rw [mul_comm, ← EReal.mul_div, EReal.div_self]
  repeat simp
  linarith

/-
Lemma. −a + a = 0 in extended reals.
-/
lemma neg_add_zero (a : ℝ) : -a + a = (0 : EReal) := by
  rw [← EReal.coe_neg, ← EReal.coe_add]
  simp

/-
Lemma. a + (−a) = 0 in extended reals.
-/
lemma add_neg_zero (a : ℝ) : a + -a = (0 : EReal) := by
  rw [← EReal.coe_neg, ← EReal.coe_add]
  simp

/-
Lemma. Left distributivity of multiplication over subtraction: a * (b − c) = a * b − a * c.
-/
lemma mul_sub_mul_sub_mul (a b : ℝ) (c : EReal) : a * (b - c) = a * b - a * c := by
  by_cases ha : a = 0
  · simp_all
  by_cases ha' : a < 0
  · have h1 : a.toEReal * ⊥ = ⊤ := coe_mul_bot_of_neg ha'
    have h2 : a.toEReal * ⊤ = ⊥ := coe_mul_top_of_neg ha'
    by_cases hc : c = ⊤
    · rw [hc]
      simp only [sub_top]
      rw [h1, h2]
      rfl
    by_cases hc' : c = ⊥
    · rw [hc']
      simp only [coe_sub_bot]
      rw [h1, h2]
      rfl
    lift c to ℝ using ⟨hc, hc'⟩
    apply EReal.coe_eq_coe_iff.mpr
    ring
  have ha : a > 0 := by
    simp at ha'
    exact lt_of_le_of_ne ha' fun a_1 ↦ ha <| id (Eq.symm a_1)
  have h1 : a.toEReal * ⊥ = ⊥ := coe_mul_bot_of_pos ha
  have h2 : a.toEReal * ⊤ = ⊤ := coe_mul_top_of_pos ha
  by_cases hc : c = ⊤
  · simp_all
  by_cases hc' : c = ⊥
  · rw [hc']
    simp only [coe_sub_bot]
    rw [h1, h2]
    rfl
  lift c to ℝ using ⟨hc, hc'⟩
  apply EReal.coe_eq_coe_iff.mpr
  ring

/-
Lemma. From a − b ≤ c (with finiteness) deduce a ≤ b + c.
-/
lemma le_add_of_ne_top_ne_bot_sub_le {a b c : EReal} (h : a - b ≤ c)
    (ha1 : a ≠ ⊤) (ha2 : a ≠ ⊥)
    (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥) (hc1 : c ≠ ⊤) (hc2 : c ≠ ⊥) : a ≤ b + c := by
  lift a to ℝ using ⟨ha1, ha2⟩
  lift b to ℝ using ⟨hb1, hb2⟩
  lift c to ℝ using ⟨hc1, hc2⟩
  rw [← EReal.coe_sub] at h
  rw [← EReal.coe_add]
  obtain := EReal.coe_le_coe_iff.1 h
  apply EReal.coe_le_coe_iff.2
  linarith

/-
Lemma. Subtracting a finite extended real yields a value strictly above −∞.
-/
lemma real_sub_not_bot {a b : EReal} (ha1 : a ≠ ⊤) (ha2 : a ≠ ⊥)
    (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥) : a - b > ⊥ := by
  lift a to ℝ using ⟨ha1, ha2⟩
  lift b to ℝ using ⟨hb1, hb2⟩
  rw [← EReal.coe_sub]
  apply bot_lt_iff_ne_bot.2
  let c := a - b
  suffices Real.toEReal c ≠ ⊥ by exact this
  simp

/-
Lemma. Adding a nonnegative real cannot decrease an extended real: if p ≥ 0, then a ≤ a + p.
-/
lemma sub_le_of_ge_zero (a : EReal) {p : ℝ} (hp : p ≥ 0) : a ≤ a + p := by
  induction a
  · simp
  · simpa [← EReal.coe_add, EReal.coe_le_coe_iff]
  simp

end EReal

end aux

/-
Lemma. An order isomorphism maps bounded indexed sups to sups: f (⨆ i∈s, x i) = ⨆ i∈s, f (x i).
-/
theorem OrderIso.map_biSup {α β ι} [CompleteLattice α] [CompleteLattice β]
    (s : Set ι) (f : α ≃o β) (x : ι → α) :
    f (⨆ i ∈ s , x i) = ⨆ i ∈ s, f (x i) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

/-
Lemma. An order isomorphism maps bounded indexed infs to infs: f (⨅ i∈s, x i) = ⨅ i∈s, f (x i).
-/
theorem OrderIso.map_biInf {α β ι} [CompleteLattice α] [CompleteLattice β]
    (s : Set ι) (f : α ≃o β) (x : ι → α) :
    f (⨅ i ∈ s , x i) = ⨅ i ∈ s, f (x i) := map_iInf₂ f fun i _ ↦ x i

section Sup_inf

namespace EReal

/-
Lemma. Bounding each term bounds the bounded
  indexed supremum: if ∀ i ∈ u, f i ≤ a, then ⨆ i ∈ u, f i ≤ a.
-/
lemma biSup_le {α} {u : Set α} {f : α → EReal} {a : EReal}
    (p : ∀ i ∈ u, f i ≤ a) : ⨆ t ∈ u, f t ≤ a := by
  simp; exact p

/-
Lemma. Each term lies below the bounded indexed supremum: f a ≤ ⨆ i ∈ u, f i.
-/
lemma le_biSup {α : Type u} {u : Set α} {f : α → EReal}
    {a : α} (p : a ∈ u) : f a ≤ ⨆ t ∈ u, f t := by
  exact _root_.le_biSup f p

/-
Lemma. If some term is above −∞, then the bounded indexed supremum is above −∞.
-/
lemma bot_lt_biSup {α : Type u} {u : Set α} {f : α → EReal}
    (p : ∃ t ∈ u, f t > ⊥) : ⊥ < ⨆ t ∈ u, f t := by
  rcases p with ⟨t, th⟩
  calc
    ⊥ < f t := by exact th.right
    _ ≤ ⨆ t ∈ u, f t := by apply EReal.le_biSup th.left

/-
Lemma. If some term equals +∞, the bounded indexed supremum equals +∞.
-/
lemma biSup_eq_top {α : Type u} {u : Set α} {f : α → EReal}
    (p : ∃ t ∈ u, f t = ⊤) : ⨆ t ∈ u, f t = ⊤ := by
  have: ⊤ ≤ ⨆ t ∈ u, f t := by
    rcases p with ⟨t, th⟩
    rw [← th.right]
    apply EReal.le_biSup th.left
  exact eq_top_iff.mpr this

/-
Lemma. If all terms equal −∞, the bounded indexed supremum equals −∞.
-/
lemma biSup_eq_bot {α : Type u} {u : Set α} {f : α → EReal}
    (p : ∀ t ∈ u, f t = ⊥) : ⨆ t ∈ u, f t = ⊥ := by
  calc
    ⨆ t ∈ u, f t =  ⨆ t ∈ u, ⊥ := by congr; ext t; congr; ext th; exact p t th;
    _ = ⊥ := by simp

/-
Lemma. The infimum of a negated set equals the negation of the supremum: sInf (−s) = − sSup s.
-/
lemma sInf_neg (s : Set EReal) : sInf (-s) = -sSup s := by
  apply le_antisymm_iff.mpr
  constructor
  · have : ∀ a ∈ -s,  sInf (-s) ≤ a := by
      exact CompleteSemilatticeInf.sInf_le (-s)
    have : ∀ a ∈ s, -sInf (-s) ≥ a := by
      intro a ah
      simp at ah
      apply EReal.le_neg_of_le_neg
      have nah : -a ∈ -s := by simp; exact ah
      exact this (-a) nah
    have := sSup_le this
    exact EReal.le_neg_of_le_neg this
  · have :∀ a ∈ s,  a ≤ sSup s := by
      apply le_sSup
    have : ∀ a ∈ -s, -sSup s ≤ a := by
      intro a ah
      simp at ah
      exact EReal.neg_le.mp (this (-a) ah)
    apply le_sInf this

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma iSup_mul {α} (f : α → EReal) {γ : ℝ} (hpos : γ > 0) :
    γ * ⨆ x, f x = ⨆ x, γ * (f x) := by
  let g' : EReal ≃ EReal := ⟨fun x => γ * x, fun y => y / γ,
    by rw [Function.leftInverse_iff_comp]; ext x; simp; exact mul_div_self hpos x,
    by rw [Function.rightInverse_iff_comp]; ext x; simp; rw [mul_div]; exact mul_div_self hpos x⟩
  let g : EReal ≃o EReal := ⟨g',@mul_le_mul_left _ hpos⟩
  apply OrderIso.map_iSup g f

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma biSup_mul {α} (f : α → EReal) {γ : ℝ} (s : Set α) (hpos : γ > 0) :
    γ * ⨆ x ∈ s, f x = ⨆ x ∈ s, γ * (f x) := by
  let g' : EReal ≃ EReal := ⟨fun x => γ * x, fun y => y / γ,
    by rw [Function.leftInverse_iff_comp]; ext x; simp; exact mul_div_self hpos x,
    by rw [Function.rightInverse_iff_comp]; ext x; simp; rw [mul_div]; exact mul_div_self hpos x⟩
  let g : EReal ≃o EReal := ⟨g',@mul_le_mul_left _ hpos⟩
  exact OrderIso.map_biSup s g f

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma biSup_mul' {α} (f : α → EReal) {γ : EReal} (s : Set α) (hpos : γ > 0 ∧ γ < ⊤) :
    γ * ⨆ x ∈ s, f x = ⨆ x ∈ s, γ * (f x) := by
  lift γ to ℝ using ⟨LT.lt.ne_top hpos.2, LT.lt.ne_bot hpos.1⟩ with g
  apply biSup_mul
  simp at hpos; exact hpos

/-
Lemma. A property of (bounded) indexed infima in extended reals.
-/
lemma iInf_mul {α} (f : α → EReal) {γ : ℝ} (hpos : γ > 0) :
    γ * ⨅ x, f x = ⨅ x, γ * (f x) := by
  let g' : EReal ≃ EReal := ⟨fun x => γ * x, fun y => y / γ,
    by rw [Function.leftInverse_iff_comp]; ext x; simp; exact mul_div_self hpos x,
    by rw [Function.rightInverse_iff_comp]; ext x; simp; rw [mul_div]; exact mul_div_self hpos x⟩
  let g : EReal ≃o EReal := ⟨g',@mul_le_mul_left _ hpos⟩
  apply OrderIso.map_iInf g f

/-
Lemma. A property of (bounded) indexed infima in extended reals.
-/
lemma biInf_mul {α} (f : α → EReal) {γ : ℝ} (s : Set α) (hpos : γ > 0) :
    γ * ⨅ x ∈ s, f x = ⨅ x ∈ s, γ * (f x) := by
  let g' : EReal ≃ EReal := ⟨fun x => γ * x, fun y => y / γ,
    by rw [Function.leftInverse_iff_comp]; ext x; simp; exact mul_div_self hpos x,
    by rw [Function.rightInverse_iff_comp]; ext x; simp; rw [mul_div]; exact mul_div_self hpos x⟩
  let g : EReal ≃o EReal := ⟨g',@mul_le_mul_left _ hpos⟩
  exact OrderIso.map_biInf s g f

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma sSup_const_add {α} (a : ℝ) (f : α → EReal) :
    a + sSup (range f) = sSup (range fun x ↦ a + f x) := by
  let g' : EReal ≃ EReal := ⟨fun x => a + x, fun y => - a + y,
    by rw [Function.leftInverse_iff_comp]; ext x; simp; rw [← add_assoc, EReal.neg_add_zero]; simp,
    by rw [Function.rightInverse_iff_comp]; ext x; simp; rw [← add_assoc, EReal.add_neg_zero]; simp⟩
  let g : EReal ≃o EReal := ⟨g', by simp [g'];apply add_le_add_left a⟩
  exact OrderIso.map_iSup g f

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma biSup_coe_const_add {α} (a : ℝ) (f : α → EReal) (s : Set α) :
    a + (⨆ m ∈ s, f m) =  (⨆ m ∈ s, a + f m) := by
  let g' : EReal ≃ EReal := ⟨fun x => a + x, fun y => - a + y,
    by rw [Function.leftInverse_iff_comp]; ext x; simp; rw [← add_assoc, EReal.neg_add_zero]; simp,
    by rw [Function.rightInverse_iff_comp]; ext x; simp; rw [← add_assoc, EReal.add_neg_zero]; simp⟩
  let g : EReal ≃o EReal := ⟨g', by simp [g'];apply add_le_add_left a⟩
  exact OrderIso.map_biSup s g f

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma biSup_add_coe_const {α} {a : ℝ} {f : α → EReal} {s : Set α} : (⨆ m ∈ s, f m) + a =
    (⨆ m ∈ s, f m + a) := by
  let g' : EReal ≃ EReal := ⟨fun x => x + a, fun y => y + -a,
    by rw [Function.leftInverse_iff_comp]; ext x; simp; rw [add_assoc, EReal.add_neg_zero]; simp,
    by rw [Function.rightInverse_iff_comp]; ext x; simp; rw [add_assoc, EReal.neg_add_zero]; simp⟩
  let g : EReal ≃o EReal := ⟨g', by simp [g'];apply add_le_add_right a⟩
  exact OrderIso.map_biSup s g f

/-
Lemma. A property stated for extended reals.
-/
lemma Range.eq_if {α : Type u} {i : Sort u_1} {f g : i → α} (eq : ∀ x, f x = g x) :
    range f = range g := by
  ext x; have : f = g := by ext x; exact eq x
  constructor;
  · intro h
    rw [← this]; exact h
  intro h;
  rw [this]; exact h

/-
Lemma. A property stated for extended reals.
-/
lemma Range.eq_if' {α : Type u} {i : Sort u_1} {f g : i → α} (eq : f = g) :
    range f = range g := by rw [eq]

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma biSup_coe_const_add' {a : EReal} {f : α → EReal} {s : Set α} (p : a < ⊤) (q : a > ⊥) :
    a + (⨆ m ∈ s, f m) =  (⨆ m ∈ s, a + f m) := by
  lift a to ℝ using ⟨LT.lt.ne_top p, LT.lt.ne_bot q⟩
  dsimp [iSup]
  rw [EReal.sSup_const_add]
  congr; ext; rw [EReal.sSup_const_add]

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma biSup_add_coe_const' {α} {a : EReal} (f : α → EReal) (s : Set α)
    (p : a < ⊤) (q : a > ⊥) : (⨆ m ∈ s, f m) + a =  (⨆ m ∈ s, f m + a) := by
  calc
    (⨆ m ∈ s, f m)+a = a + (⨆ m ∈ s, f m) := by
      exact AddCommMagma.add_comm (⨆ m ∈ s, f m) a
    _ = (⨆ m ∈ s, a + f m) := by
      rw [EReal.biSup_coe_const_add' p q]
    _= (⨆ m ∈ s, f m + a) := by
      congr; ext x; congr; ext
      exact AddCommMagma.add_comm a (f x)

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma biSup_const_add {a : EReal} {f : α → EReal} {s : Set α}
    (pf : ∀ m ∈ s, f m > ⊥) (pa : a ≠ ⊥) :
    a + (⨆ m ∈ s, f m) =  (⨆ m ∈ s, a + f m) := by
  by_cases em: s = ∅
  · rw [em]; simp
  by_cases h : a = ⊤
  · rw [h];
    have : ⊥ < ⨆ m ∈ s, f m := by
      by_contra nh
      simp at nh
      push_neg at em
      rcases em with ⟨e, ee⟩
      have n2 := nh e ee
      have n1 := bot_lt_iff_ne_bot.mp ( pf e ee)
      contradiction
    rw [top_add_iff_ne_bot.mpr]
    · have : ⨆ m ∈ s, ⊤ + f m = ⊤ := by
        calc
          ⨆ m ∈ s, ⊤ + f m = ⨆ m ∈ s, ⊤ := by
            congr; ext x; congr; ext xh;
            rw [top_add_iff_ne_bot.mpr]
            exact bot_lt_iff_ne_bot.mp ( pf x xh)
          _ = ⊤ := by
            apply biSup_const
            exact nonempty_iff_ne_empty.mpr em
      rw [this]
    exact LT.lt.ne_bot this
  lift a to ℝ using ⟨h, pa⟩
  dsimp [iSup]
  rw [EReal.sSup_const_add]
  congr; ext
  rw [EReal.sSup_const_add]

/-
Lemma. A property of (bounded) indexed suprema in extended reals.
-/
lemma biSup_add_const {α} {a : EReal} {f : α → EReal} {s : Set α}
    (pf : ∀ m ∈ s, f m > ⊥) (pa : a ≠ ⊥) : (⨆ m ∈ s, f m) + a =  (⨆ m ∈ s, f m + a) := by
  calc
    (⨆ m ∈ s, f m) + a = a + (⨆ m ∈ s, f m) := by
      exact AddCommMagma.add_comm (⨆ m ∈ s, f m) a
    _ = (⨆ m ∈ s, a + f m) := by
      rw [EReal.biSup_const_add pf pa]
    _ = (⨆ m ∈ s, f m + a) := by
      congr; ext x; congr; ext
      exact AddCommMagma.add_comm a (f x)

/-
Theorem. A property of (bounded) indexed suprema in extended reals.
-/
theorem add_le_biSup {ι : Type*} {s : Set ι} (f g : ι → EReal) :
    ⨆ i ∈ s, f i + g i ≤ (⨆ i ∈ s, f i) + ⨆ i ∈ s, g i := by
  refine EReal.biSup_le ?p
  intro i hi
  apply add_le_add (le_biSup hi) (le_biSup hi)

end EReal

end Sup_inf

section continuous

/-
Lemma. The map x ↦ x − c is continuous on extended reals.
-/
theorem EReal.continuous_sub (c : ℝ) : Continuous fun x : EReal => x - c := by
  rw [continuous_iff_continuousAt]
  intro p
  let g : EReal → EReal × EReal:= fun x => (x, -c)
  let f := fun p : EReal × EReal => p.1 + p.2
  suffices ContinuousAt (f ∘ g) p by exact this
  refine ContinuousAt.comp ?_ ?_
  refine continuousAt_add ?_ ?_
  <;>
  · right; simp [g]
  refine ContinuousAt.prodMk (fun ⦃U⦄ a ↦ a) ?_
  exact continuousAt_const

/-
Lemma. For fixed x, the map y ↦ ⟪x, y⟫ − c is continuous (inner product over ℝ).
-/
lemma EReal.continuous_inner_sub {E} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) (c : EReal) :
    Continuous (fun y ↦ (inner ℝ x y : ℝ) - c) := by
  by_cases h1 : c = ⊤
  · rw [h1]; simp; exact continuous_const
  by_cases h2 : c = ⊥
  · rw [h2]; simp; exact continuous_const
  lift c to ℝ using ⟨h1, h2⟩
  apply Continuous.comp (EReal.continuous_sub c)
  suffices (Continuous fun y ↦ (inner ℝ x y : ℝ)) by
    exact EReal.continuous_coe_iff.mpr this
  have : Differentiable ℝ (fun y ↦ (inner ℝ x y : ℝ)) := by
    apply Differentiable.inner
    · exact differentiable_const x
    exact differentiable_fun_id
  exact Differentiable.continuous this

end continuous

section tendsto

/-
Lemma. liminf commutes with adding a finite constant: liminf (f + c) = liminf f + c (with c finite).
-/
lemma EReal.liminf_add_const {α} {F : Filter α} [F.NeBot] {f : α → EReal} {c : EReal}
    (hc1 : c ≠ ⊥) (hc2 : c ≠ ⊤) :
    liminf (fun (i : α) => f i + c) F = liminf f F + c:= by
  let g := fun x => x + c
  suffices liminf (g ∘ f)  F = g (liminf f F) by exact this
  refine (Monotone.map_liminf_of_continuousAt ?f_incr f ?f_cont ?cobdd ?bdd_below).symm
  · exact Monotone.add_const (fun ⦃a b⦄ a ↦ a) c
  · refine Continuous.continuousAt ?f_cont.h
    apply Monotone.continuous_of_surjective <| Monotone.add_const (fun ⦃a b⦄ a ↦ a) c
    intro z
    use z - c
    simp
    exact sub_add hc1 hc2
  repeat isBoundedDefault

/-
Lemma. If the ℝ-embedding of f tends to −∞ in EReal, then f eventually stays below any real bound.
-/
theorem EReal.tendsto_coe_nhds_top {f : α → EReal} {l : Filter α} :
    Tendsto (fun x => (f x : EReal)) l (𝓝 ⊥) →
    ∀ c : ℝ , ∀ᶠ (a : α) in l, (f a) ≤ c.toEReal := by
  rw [tendsto_nhds_bot_iff_real]
  intro hb z
  apply Filter.Eventually.mp (hb z)
  apply Filter.Eventually.of_forall
  intro t ht
  exact le_of_lt ht

/-
Lemma. Along atTop, once (m n) tends to y in EReal,
  eventually the coerced toReal/coe agree pointwise.
-/
theorem EReal.eventually_coe_of_Real {m : ℕ → EReal} {y : ℝ} :
    Tendsto m atTop (𝓝 y.toEReal) → ∀ᶠ x in atTop, (fun a ↦ ↑(m a).toReal) x = m x := by
  intro hm
  rw [@tendsto_iff_seq_tendsto] at hm
  simp
  by_contra! hab
  let x : ℕ → ℕ := fun n => (hab n).choose
  have xs := fun n => (hab n).choose_spec
  have xlim :  Tendsto x atTop atTop := by
    simp [tendsto_atTop_atTop, x]
    intro t
    exact ⟨t, fun a hab => Nat.le_trans hab (xs a).1⟩
  have mx : ∀ n, (m ∘ x) n = ⊤ ∨  (m ∘ x) n = ⊥ := by
    intro n
    simp [x]
    by_contra!
    apply (xs n).2
    refine coe_toReal this.1 this.2
  have := hm _ xlim
  rw [@tendsto_atTop'] at this
  have innbhd : {(⊥ : EReal), ⊤}ᶜ ∈ 𝓝 ↑y := by
    refine (IsOpen.mem_nhds_iff ?hs).mpr ?_
    simp
    rw [← @Finset.coe_pair]; simp
  have ⟨a, ha⟩:= this {⊥, ⊤}ᶜ innbhd
  exact (ha a (by simp)) (id (Or.symm (mx a)))

/-
Lemma. If (m n) → y in EReal, then (m n).toReal → y in ℝ.
-/
theorem EReal.tendsto_coe_of_Real {m : ℕ → EReal} {y : ℝ} :
    Tendsto m atTop (𝓝 y.toEReal) →
    Tendsto (fun n ↦ (m n).toReal) atTop (𝓝 y) := by
  intro hm
  rw [← tendsto_coe]
  have :  ∀ᶠ x in atTop, (fun a ↦ ↑(m a).toReal) x = m x :=
    eventually_coe_of_Real hm
  exact (tendsto_congr' this).mpr hm

end tendsto

section Convex

/-
Lemma. A convex function f : E → EReal that attains −∞ at some point is identically −∞ on all of E.
-/
lemma bot_of_exist_bot_of_convex_of_univ {E} [AddCommGroup E] [Module ℝ E] {f : E → EReal}
    (hf : ConvexOn ℝ univ f) (hx : ∃ x, f x = ⊥) :
    ∀ x, f x = ⊥ := by
  rcases hx with ⟨x, hfx⟩
  intro y
  let a : ℝ := 1 / 2
  let b : ℝ := 2
  rw [eq_bot_iff]
  calc _
    _ = f (a • x + a • (b • y - x)) := by
      congr
      simp [smul_sub, a, b]
    _ ≤ a * (f x) + a * f (b • y - x) := by
      apply hf.2 trivial trivial (by simp [a]) (by simp [a]) (by norm_num)
    _ ≤ _ := by
      simp [hfx]
      left
      refine coe_mul_bot_of_pos  one_half_pos

/-
Lemma. Jensen-type inequality: for a convex f and
  barycentric weights on points in s, f(∑ wᵢ • pᵢ) ≤ ∑ wᵢ • f(pᵢ).
-/
theorem ConvexOn.map_sum_le' {E s} {ι : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq ι]
    {f : E → EReal} {p : ι → E} (hf : ConvexOn ℝ s f) :
    (t : Finset ι) → (w : ι → ℝ) → (∀ i ∈ t, 0 ≤ w i) → (∑ i ∈ t, w i = 1) →
    (∀ i ∈ t, p i ∈ s) → f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) := by
  apply Finset.induction
  · intro _ _ _
    simp_all
  intro a t hat hc w h₀ h₁ hmem
  have hw : ∀ i ∈ t, w i ≥ 0 := fun i hi ↦ h₀ i (Finset.mem_insert_of_mem hi)
  by_cases ha : w a = 1
  · simp [hat] at h₁ ⊢
    rw [ha] at h₁; simp at h₁
    have hw : ∀ i ∈ t, w i = 0 := by
      intro i hi
      by_contra h1; push_neg at h1
      obtain h2 := hw i hi
      linarith [Finset.sum_pos' hw ⟨i, hi, by positivity⟩]
    have p1 : ∑ i ∈ t, w i • p i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hw i hi]; simp
    have p2 : ∑ x ∈ t, ↑(w x) * f (p x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hw i hi]; simp
    rw [p1, p2, ha]; simp
  have hab0 : w a ≥ 0 := h₀ a (Finset.mem_insert_self a t)
  have hab1 : 1 - w a > 0 := by
    simp [hat] at h₁
    by_contra h2; push_neg at h2 ha
    have : w a > 1 := lt_of_le_of_ne (by linarith) (id (Ne.symm ha))
    have : ∑ i ∈ t, w i ≥ 0 := by
      apply Finset.sum_nonneg hw
    linarith
  have : 1 - w a ≤ 1 := by linarith
  let w' : ι → ℝ := fun i => w i / (1 - w a)
  have h₀' : ∀ i ∈ t, 0 ≤ w' i := by
    intro i hi
    simp [w']
    specialize hw i hi
    positivity
  have h₁' : ∑ i ∈ t, w' i = 1 := by
    simp [w']; rw [← Finset.sum_div]
    simp [hat] at h₁
    rw [Eq.symm (sub_eq_of_eq_add' (id (Eq.symm h₁)))]
    field_simp
  have hmem' : ∀ i ∈ t, p i ∈ s := fun i hi ↦ hmem i (Finset.mem_insert_of_mem hi)
  obtain hc := hc w' h₀' h₁' hmem'
  simp [hat]
  have htt : ∑ i ∈ t, w i • p i = (1 - w a) • (∑ i ∈ t, w' i • p i) := by
    rw [Finset.smul_sum]
    congr; ext i
    simp [w']; rw [smul_smul]
    field_simp
  rw [htt]
  have ht2 : f (w a • p a + (1 - w a) • ∑ i ∈ t, w' i • p i) ≤
      (w a) * f (p a) + (1 - w a) * f (∑ i ∈ t, w' i • (p i)) := by
    have hp2 : ∑ i ∈ t, w' i • (p i) ∈ s := by
      exact Convex.sum_mem hf.1 h₀' h₁' hmem'
    have hp3 : 1 - w a ≥ 0 := by linarith
    obtain hcf := hf.2 (hmem a (Finset.mem_insert_self a t)) hp2 hab0 hp3 (by simp)
    simp at hcf
    exact hcf
  have ht3 : ((1 : ℝ) - w a) * f (∑ i ∈ t, w' i • (p i)) ≤
      ((1 : ℝ) - w a) * (∑ i ∈ t, w' i • f (p i)) := by
    apply EReal.mul_pos_real_le hc hab1
  have ht4 : ((1 : ℝ) - w a) * ∑ i ∈ t, w' i • f (p i) =  ∑ i ∈ t, w i * f (p i) := by
    simp only [w']
    have : ((1 : ℝ) - w a) * ∑ i ∈ t, w' i • f (p i) =
        ∑ i ∈ t, ((1 : ℝ) - w a) * (w' i • f (p i)) := by
      apply EReal.finset_mul_sum
      simp; linarith
    rw [this]
    congr; ext i
    simp [w']; rw [← mul_assoc]
    have : (1 - (w a).toEReal) * (w i / (1 - w a) : ℝ) = w i := by
      calc
        _ = ((1 : ℝ) - (w a).toEReal) * (w i / (1 - w a) : ℝ) := by simp
        _ = w i := by
          rw [← EReal.coe_sub, ← EReal.coe_mul]
          apply EReal.coe_eq_coe_iff.mpr
          field_simp
    rw [this]
  rw [ht4] at ht3
  exact le_add_of_le_add_left ht2 ht3

end Convex

section liminf

/-
Lemma. For c ≥ 0 and c ≠ +∞, liminf (c * f) = c * liminf f.
-/
lemma EReal.liminf_negconst_mul {α} {F : Filter α} [F.NeBot] {f : α → EReal} {c : EReal}
    (hc1 : c ≥ 0) (hc2 : c ≠ ⊤) : liminf (fun (i : α) => c * f i) F = c * (liminf f F) := by
  by_cases hc : c = 0
  · rw [hc]
    simp
  let g : EReal → EReal:= fun z => c * z
  suffices liminf (g ∘ f)  F = g (liminf f F) by exact this
  refine (Monotone.map_liminf_of_continuousAt ?f_incr f ?f_cont ?cobdd ?bdd_below).symm
  · exact monotone_mul_left_of_nonneg hc1
  · refine Continuous.continuousAt ?f_cont.h
    apply Monotone.continuous_of_surjective <| monotone_mul_left_of_nonneg hc1
    intro z
    use z / c
    simp
    rw [EReal.mul_div_cancel]
    · simp
      refine bot_lt_iff_ne_bot.mp ?h.h₁.a
      refine lt_iff_exists_rat_btwn.mpr ?h.h₁.a.a
      use -1
      simp
      constructor
      · exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
      refine lt_of_lt_of_le ?h.right.hab hc1
      simp
    · exact hc2
    simpa
  repeat isBoundedDefault

end liminf
section lowersemicontinuous

variable {E : Type*} [NormedAddCommGroup E]

/-
Theorem. Lower semicontinuity is preserved under nonnegative scaling.
-/
theorem smul_lowerSemicontinuous_of_nonneg {f : E → EReal}
    {m : ℝ} (hm : m ≥ 0) (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (m • f) := by
  refine lowerSemicontinuous_iff_le_liminf.mpr ?_
  intro x;simp
  rw [lowerSemicontinuous_iff_le_liminf] at hf
  calc
    _ ≤ m * liminf f (𝓝 x) :=
      mul_le_mul_of_nonneg_left (hf x) (EReal.coe_nonneg.mpr hm)
    _ = liminf (fun x => m * f x) (𝓝 x) := by
      symm
      apply EReal.liminf_negconst_mul (by simpa) (by simp)
    _ ≤ _ := by apply Preorder.le_refl

end lowersemicontinuous

section sum

/-
Lemma. If each term f i is above −∞, the finite sum is above −∞.
-/
lemma EReal.sum_lt_top_of_forall_lt_top {n : ℕ} {f : Fin n → EReal}
    (hf : ∀ i, f i > ⊥) : ∑ i, f i > ⊥ := by
  induction n with
  | zero => simp
  | succ n nh =>
    rw [Fin.sum_univ_castSucc]
    refine bot_lt_add_iff.mpr ⟨nh fun i ↦ hf i.castSucc, hf (Fin.last n)⟩

/-
Lemma. If a finite sum is finite (< +∞) and every term is above −∞, then each term is finite.
-/
lemma EReal.lt_top_of_sum_lt_top {n : ℕ} {f : Fin n → EReal}
    (hf : ∀ i, f i > ⊥)
    (hfi : ∑ i, f i < ⊤) : ∀ i , f i < ⊤ := by
  intro j
  induction n with
  | zero => exact (StrictAnti.lt_iff_gt fun _ _ _ ↦ (Fin.size_positive j)).mp (Fin.size_positive j)
  | succ n _ =>
    by_contra! hfj
    simp at hfj
    rw [Fin.sum_univ_succAbove f j, hfj] at hfi
    have : ∑ i : Fin n, f (j.succAbove i) ≠ ⊥ :=
      bot_lt_iff_ne_bot.mp <| sum_lt_top_of_forall_lt_top fun i ↦ hf (j.succAbove i)
    have : ⊤ + ∑ i : Fin n, f (j.succAbove i) = ⊤ := by
      exact top_add_of_ne_bot this
    rw [this] at hfi
    simp at hfi

/-
Lemma. A finite sum of finite extended reals is finite.
-/
lemma EReal.sum_lt_top_of_lt_top {n : ℕ} {f : Fin n → EReal}
    (hf : ∀ i, f i < ⊤) : ∑ i, f i < ⊤ := by
  induction n with
  | zero => simp
  | succ n nh =>
    rw [Fin.sum_univ_castSucc]
    refine add_lt_top ?succ.hx ?succ.hy
    · exact LT.lt.ne_top (nh fun i ↦ hf i.castSucc)
    exact LT.lt.ne_top (hf (Fin.last n))

/-
Lemma. If all terms in a finite family are not −∞, then the tail sum is not −∞.
-/
lemma sum_neq_bot {n : ℕ} (f : Fin (n + 1) → EReal) (p : ∀ i : Fin (n + 1), f i ≠ ⊥) :
    ∑ i : Fin n, f i.succ ≠ ⊥:= by
  induction n with
  | zero => simp
  | succ n nh =>
    rw [Fin.sum_univ_succ]
    have : ∀ (i : Fin (n + 1)), f i.succ ≠ ⊥ := fun i ↦ p i.succ
    have := nh (fun i ↦ f i.succ) this
    simp at this
    by_contra h
    have cc := EReal.add_eq_bot_iff.mp h
    have le := p (Fin.succ 0);
    have := not_or_intro le this
    contradiction

/-
Lemma. A finite sum of finite extended reals is finite.
-/
lemma EReal.sum_lt_top {c : ℕ} {f : Fin (c) → EReal} (p : ∀ i : Fin (c), f i < ⊤) :
    ∑ i : Fin c, f i < ⊤:= by
  induction c with
  | zero => simp
  | succ n nh =>
    rw [Fin.sum_univ_castSucc]
    have : ∀ (i : Fin (n)), f i.castSucc < ⊤ := fun i ↦ p i.castSucc
    have := @nh (fun i ↦ f i.castSucc) this
    apply EReal.add_lt_top
    · exact LT.lt.ne_top this
    · exact LT.lt.ne_top (p (Fin.last n))


/-
Lemma. If every term is above −∞, then the finite sum is above −∞.
-/
lemma EReal.bot_lt_sum {c : ℕ} {f : Fin (c) → EReal} (p : ∀ i : Fin (c), ⊥ < f i) :
    ⊥ < ∑ i : Fin c, f i :=
  sum_lt_top_of_forall_lt_top p


/-
Lemma. Sum–difference distributes when subtracting an
  EReal-sum from a real sum: (∑ f) − (∑ g) = ∑ (f i − g i).
-/
lemma coe_sum_sub_distrib {c : ℕ} {f : Fin c → ℝ} {g : Fin c → EReal} (p : ∀ i : Fin c, g i ≠ ⊥) :
    (∑ i : Fin c, f i) - (∑ i : Fin c, g i) = ∑ i : Fin c, (f i - g i) := by
  induction c with
  | zero => simp
  | succ n nh =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    rw [EReal.sub_add_eq_sub_sub (p 0) (sum_neq_bot g p)]
    rw [EReal.coe_add, add_sub_assoc, EReal.sub_eq_neg_add _ (g 0)]
    rw [← add_assoc, add_sub_assoc]
    rw [@nh (fun (i: Fin n) ↦ f i.succ) (fun (i: Fin n) ↦ g i.succ) (fun i ↦ p i.succ)]
    rfl

end sum
