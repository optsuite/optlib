/-
Copyright (c) 2023 Zuokai Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Zuokai Wen,Mingquan Zhang
-/

/-
  This file contains proofs of convexity preservation of perspective transformations
  and linear fractional transformation.
  Perspective transformation: f: ℝ ^ (n+1) → ℝ:P(x, t) = x/t,
  domf = {(x, t)| t > 0}.
  Linear fractional transformation: g : ℝⁿ → ℝᵐ， g(x)= (Ax+b)/(cᵀx+d),
  domg = {x | cᵀx+d > 0}.
-/

import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Image

open Set Finset BigOperators Real InnerProductSpace DivisionSemiring Matrix

noncomputable section

variable {n : Type _ }[Fintype n]

def perspective: (n -> ℝ) × ℝ → (n -> ℝ) := fun x ↦ (1 / x.2) • x.1

def dom : Set ((n -> ℝ) × ℝ) := {x | x.2 > 0}

lemma neq_0 {x y a b: ℝ} (hx: x > 0) (hy: y > 0) (ha : 0 ≤ a) (hb: 0 ≤ b)
    (hab: a + b = 1) : a * y + b * x ≠ 0 := by
  have hay: 0 ≤ a * y := by exact Iff.mpr (zero_le_mul_right hy) ha
  have hbx: 0 ≤ b * x := by exact Iff.mpr (zero_le_mul_right hx) hb
  by_contra h
  have hay': 0 = a * y := by
    by_contra h1
    have h2 : 0 < a * y := by
      exact Ne.lt_of_le h1 hay
    have h3 : a * y + b * x > 0 := by exact add_pos_of_pos_of_nonneg h2 hbx
    have h4 : a * y + b * x ≠ 0 := by exact ne_of_gt h3
    contradiction
  have ha1 : a = 0 := by
    by_contra h5
    have h6 : 0 < a := by exact Ne.lt_of_le' h5 ha
    have h7 : 0 ≠ a * y :=by exact LT.lt.ne (Real.mul_pos h6 hy)
    contradiction
  have hbx' : 0 = b * x := by
    rw[h.symm, hay'.symm, zero_add]
  have hb1 : b = 0 := by
    by_contra h8
    have h9 : 0 < b := by exact Ne.lt_of_le' h8 hb
    have h10 : 0 ≠ b * x := by exact LT.lt.ne (Real.mul_pos h9 hx)
    contradiction
  rw[ha1,hb1, zero_add] at hab
  linarith

theorem convex_perspective_image{s : Set ((n -> ℝ) × ℝ)} (h1: Convex ℝ s)
    (h2: ∀ x ∈ s, x.2 > 0): Convex ℝ (perspective '' s) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy
  have hx'2 : x'.2 > 0 := h2 x' hx'
  have hy'2 : y'.2 > 0 := h2 y' hy'
  rw[perspective] at * ;rw[perspective]
  let u := a * y'.2 / (a * y'.2 + b * x'.2)
  let v := b * x'.2 / (a * y'.2 + b * x'.2)
  have hu: 0 ≤ u := by positivity
  have hv: 0 ≤ v := by positivity
  have hasbx: a * y'.2 + b * x'.2 ≠ 0 := by
    apply neq_0 hx'2 hy'2 ha hb hab
  have huv:u+v=1:=by
    field_simp
  refine' ⟨u•x'+v•y',h1 hx' hy' hu hv huv,_⟩
  rw[perspective,Prod.snd_add,Prod.fst_add,
    Prod.smul_snd,Prod.smul_snd,Prod.smul_fst,Prod.smul_fst]
  have h3:u•x'.2+v•y'.2=(x'.2*y'.2)/(a*y'.2+b*x'.2):=by
    simp only [smul_eq_mul]
    rw[div_mul_eq_mul_div,div_mul_eq_mul_div,div_add_div_same]
    rw[mul_right_comm a y'.snd x'.snd]
    have h4:a*x'.2*y'.2+b*x'.2*y'.2=x'.2*y'.2:=by
      rw[mul_assoc,mul_assoc,←add_mul,hab,one_mul]
    rw[h4]
  rw[h3,smul_add]
  have h5:(1/(x'.2*y'.2/(a*y'.2+b*x'.2)))•u=(1/(x'.2*y'.2))*a*y'.2:=by
    rw[smul_eq_mul,←div_mul]
    simp only [one_div,Matrix.mul_inv_rev]
    rw[mul_div_left_comm,←mul_div,div_self,mul_one]
    linarith
    exact hasbx
  have h6:(1/(x'.2*y'.2))*a*y'.2=a•(1/x'.2):=by
    rw[smul_eq_mul,←mul_div_right_comm,div_mul,←mul_div,
      ←mul_div,div_self,mul_div,mul_div,one_mul,mul_one,mul_one]
    exact ne_of_gt (h2 y' hy')
  have h7:(1/(x'.2*y'.2/(a*y'.2+b*x'.2)))•v=(1/(x'.2*y'.2))*b*x'.2:=by
    rw[smul_eq_mul,←div_mul]
    simp only [one_div,Matrix.mul_inv_rev]
    rw[mul_div_left_comm,←mul_div,div_self,mul_one]
    linarith
    exact hasbx
  have h8:(1/(x'.2*y'.2))*b*x'.2=b•(1/y'.2):=by
    rw[smul_eq_mul,←mul_div_right_comm,div_mul,←mul_div,
      mul_comm x'.2 y'.2,←mul_div,div_self,mul_div,mul_div,one_mul,mul_one,mul_one]
    exact ne_of_gt (h2 x' hx')
  have h9:(1/(x'.2*y'.2/(a*y'.2+b*x'.2)))•u•x'.1=a•(1/x'.2)•x'.1:=by
    rw[←smul_assoc,h5,h6,smul_assoc]
  have h10:(1/(x'.2*y'.2/(a*y'.2+b*x'.2)))•v•y'.1=b•(1/y'.2)•y'.1:=by
    rw[←smul_assoc,h7,h8,smul_assoc]
  rw[h9,h10]

theorem convex_perspective_preimage' {s : Set (n -> ℝ)}
  (h1 : Convex ℝ s) : Convex ℝ ((perspective ⁻¹' s) ∩ dom):= by
  intro x hx y hy a b ha hb hab
  rw[inter_def]; simp only [mem_setOf]
  have hx₂ : x.2 > 0 := by apply hx.2
  have hy₂ : y.2 > 0 := by apply hy.2
  have neq0: a * x.2 + b * y.2 ≠ 0 := by
    apply neq_0 hy₂ hx₂ ha hb hab
  constructor
  rw[Set.mem_preimage]
  rw[inter_def] at hx hy; simp only [mem_setOf] at hx hy
  rw [Set.mem_preimage] at hx hy; rw[perspective] at *
  let u := a * x.2 / (a * x.2 + b * y.2); let v := b * y.2 / (a * x.2 + b * y.2)
  have hu: 0 ≤ u := by positivity
  have hv: 0 ≤ v := by positivity
  have huv: u + v = 1 := by rw[div_add_div_same, div_self neq0]
  have h_comm(a t: ℝ)(h: t > 0): (1 / t) * a * t = a := by
    rw [mul_assoc, mul_comm, mul_one_div,mul_div_assoc, div_self, mul_one]
    exact ne_of_gt h
  have h₂: (1 / (a • x + b • y).2) • (a • x + b • y).1 =
    u • ((1 / x.2) • x.1) + v • ((1 / y.2) • y.1) := by
    rw[Prod.snd_add, Prod.fst_add, Prod.smul_snd,Prod.smul_snd,
    Prod.smul_fst,Prod.smul_fst]
    field_simp; apply Eq.symm
    rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul]
    calc
      (a * x.2 / (a * x.2 + b * y.2) * (1 / x.2)) • x.1 +
      (b * y.2 / (a * x.2 + b * y.2) * (1 / y.2)) • y.1 =
      (a * x.2 * (1 / (a * x.2 + b * y.2)) * (1 / x.2)) • x.1 +
      (b * y.2 * (1 / (a * x.2 + b * y.2)) * (1 / y.2)) • y.1 := by field_simp
      _ = (a * (1 / (a * x.2 + b * y.2))) • x.1 +
        (b * (1 / (a * x.2 + b * y.2))) • y.1 := by
          rw[mul_comm, ← mul_assoc, ← mul_assoc, mul_comm, h_comm,
           add_comm, mul_comm, ← mul_assoc, ← mul_assoc,
           mul_comm, h_comm, add_comm]; field_simp
          apply hy₂; exact hx₂
      _ = (1 / (a * x.2 + b * y.2)) • a • x.1 +
        (1 / (a * x.2 + b * y.2)) • b • y.1 := by
          rw[mul_comm, add_comm, mul_comm, add_comm, smul_smul, smul_smul]
  rw[h₂]; exact h1 hx.1 hy.1 hu hv huv
  have dom_eq_set: dom = {x: ((n -> ℝ) × ℝ) | x.2 > 0} := by rfl
  rw[dom_eq_set]; simp only [mem_setOf]
  apply Ne.lt_of_le' neq0
  positivity


variable {A b c d m s:Type _}[Fintype m]

variable(A:Matrix m n ℝ)(b:m -> ℝ)(c:n -> ℝ)(d:ℝ)

def LinearFraction:(n -> ℝ) -> (m -> ℝ):=fun x ↦ (1 / (c ⬝ᵥ x + d)) • (Matrix.mulVec A x + b)

def dom': Set (n -> ℝ) := {x | c ⬝ᵥ x + d > 0}

variable{s:Set (n -> ℝ)}

def g:(n -> ℝ) -> (m -> ℝ) × ℝ:=fun x ↦ (Matrix.mulVec A x + b , c ⬝ᵥ x + d)

theorem gImage{s1:Set (n -> ℝ)}(h1:Convex ℝ s1):Convex ℝ (g A b c d '' s1):=by
  intro x hx y hy a1 b1 ha1 hb1 hab1
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy
  refine' ⟨a1 • x' + b1 • y',⟨h1 hx' hy' ha1 hb1 hab1, _⟩⟩
  rw[g,g,g]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul,Prod.smul_mk, smul_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor
  · rw[mulVec_add,mulVec_smul,mulVec_smul]
    calc
      a1 • mulVec A x' + b1 • mulVec A y' + b =
       a1 • mulVec A x' + b1 • mulVec A y' + (a1+b1)•b :=by
        congr
        rw[hab1,one_smul]
      _=a1 • mulVec A x' + b1 • mulVec A y' + a1 • b + b1 • b :=by
        rw[add_smul]
        exact Mathlib.Tactic.RingNF.add_assoc_rev (a1 • mulVec A x' + b1 • mulVec A y') (a1 • b) (b1 • b)
      _=a1 • mulVec A x' + a1 • b + (b1 • mulVec A y' + b1 • b):=by
        rw[add_right_comm _ _ (a1•b)]
        exact add_assoc (a1 • mulVec A x' + a1 • b) _ _
  · rw[mul_add,mul_add]
    calc
      a1 * c ⬝ᵥ x' + b1 * c ⬝ᵥ y' + d
        = a1 * c ⬝ᵥ x' + b1 * c ⬝ᵥ y' + (a1+b1)•d:=by rw[hab1,one_smul]
       _=a1 * c ⬝ᵥ x' + b1 * c ⬝ᵥ y' +a1•d+b1•d:=by
        rw[add_smul]
        exact Mathlib.Tactic.RingNF.add_assoc_rev (a1 * c ⬝ᵥ x' + b1 * c ⬝ᵥ y') (a1 • d) (b1 • d)
       _=a1 * c ⬝ᵥ x' + a1 * d + (b1 * c ⬝ᵥ y' + b1 * d):=by
        rw[smul_eq_mul,smul_eq_mul]
        rw[add_right_comm _ _ (a1*d)]
        exact add_assoc (a1 *c ⬝ᵥ x'+a1*d) _ _

theorem gPreimage{s1:Set ((m -> ℝ) × ℝ)}(h1:Convex ℝ s1):Convex ℝ (g A b c d ⁻¹' s1):=by
  intro x hx y hy a1 b1 ha1 hb1 hab1
  rw[Set.mem_preimage] at *
  rw[g] at *
  rw[mulVec_add,mulVec_smul,mulVec_smul,dotProduct_add]
  have hw:(a1 • mulVec A x + b1 • mulVec A y + b, c ⬝ᵥ a1 • x + c ⬝ᵥ b1 • y + d)
    =a1 • (mulVec A x + b, c ⬝ᵥ x + d) + b1 • (mulVec A y + b, c ⬝ᵥ y + d):=by
    simp only [dotProduct_smul, smul_eq_mul, Prod.smul_mk,
      smul_add, Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · calc
      a1 • mulVec A x + b1 • mulVec A y + b =
       a1 • mulVec A x + b1 • mulVec A y + (a1+b1)•b :=by
        congr
        rw[hab1,one_smul]
      _=a1 • mulVec A x + b1 • mulVec A y + a1 • b + b1 • b :=by
        rw[add_smul]
        exact Mathlib.Tactic.RingNF.add_assoc_rev (a1 • mulVec A x + b1 • mulVec A y) (a1 • b) (b1 • b)
      _=a1 • mulVec A x + a1 • b + (b1 • mulVec A y + b1 • b):=by
        rw[add_right_comm _ _ (a1•b)]
        exact add_assoc (a1 • mulVec A x + a1 • b) _ _
    · rw[mul_add,mul_add]
      calc
      a1 * c ⬝ᵥ x + b1 * c ⬝ᵥ y + d
        = a1 * c ⬝ᵥ x + b1 * c ⬝ᵥ y + (a1+b1)•d:=by rw[hab1,one_smul]
       _=a1 * c ⬝ᵥ x + b1 * c ⬝ᵥ y +a1•d+b1•d:=by
        rw[add_smul]
        exact Mathlib.Tactic.RingNF.add_assoc_rev (a1 * c ⬝ᵥ x + b1 * c ⬝ᵥ y) (a1 • d) (b1 • d)
       _=a1 * c ⬝ᵥ x + a1 * d + (b1 * c ⬝ᵥ y + b1 * d):=by
        rw[smul_eq_mul,smul_eq_mul]
        rw[add_right_comm _ _ (a1*d)]
        exact add_assoc (a1 *c ⬝ᵥ x+a1*d) _ _
  rw[hw]
  exact h1 hx hy ha1 hb1 hab1

theorem LinearFractionImage(h1:Convex ℝ s)(h2:∀ x ∈ s,c ⬝ᵥ x + d > 0)
  :Convex ℝ (LinearFraction A b c d '' s):=by
    have gImageConvex:Convex ℝ (g A b c d '' s):=by exact gImage A b c d h1
    have h2':∀ (x : (m → ℝ) × ℝ), x ∈ g A b c d '' s → x.snd > 0:=by
      intro x hx
      obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx
      simp only [gt_iff_lt]
      exact h2 x' hx'
    have SameGoal:LinearFraction A b c d '' s=perspective '' (g A b c d '' s):=by
      ext x
      constructor
      · intro hx
        obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx
        simp only [Set.mem_image, exists_exists_and_eq_and]
        refine' ⟨x',hx',rfl⟩
      · intro hx
        obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx
        obtain ⟨x'', hx'', rfl⟩ := mem_image_iff_bex.1 hx'
        simp only [Set.mem_image]
        exact ⟨x'',hx'',rfl⟩
    rw[SameGoal]
    exact convex_perspective_image gImageConvex h2'

theorem LinearFractionPreimage{s : Set (m -> ℝ)}(h1:Convex ℝ s):
  Convex ℝ ((LinearFraction A b c d ⁻¹' s) ∩ dom' c d):= by
    have Samegoal:g A b c d ⁻¹' (perspective ⁻¹' s)=LinearFraction A b c d ⁻¹' s:=by
      ext x
      constructor
      · intro hx
        exact hx
      · intro hx
        exact hx
    rw[←Samegoal]
    have perpreimageConvex:Convex ℝ ((perspective ⁻¹' s) ∩ dom):=by
      exact convex_perspective_preimage' h1
    exact gPreimage A b c d perpreimageConvex
