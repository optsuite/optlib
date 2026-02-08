/-
Copyright (c) 2025  Yifan Bai, Yunxi Duan, Zichen Wang, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yifan Bai, Yunxi Duan, Zichen Wang, Chenyi Li
-/
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.EReal.Basic
import Reaslib.ConvexAnalysis.IntrinsicInterior
import Reaslib.ConvexAnalysis.Epigraph

/-!
# Intrinsic interior of a function's epigraph

## References

* Chapter 7 of [R. T. Rockafellar, *Convex Analysis*][rockafellar1970].
-/

open Set Function EReal

variable {E F : Type*}

section aux_lemma
lemma intrinsic_le {t : EReal} : intrinsicInterior ℝ {z:ℝ | t ≤ ↑z} = {z:ℝ | t < ↑z} := by
  by_cases ht1 : t = ⊤
  · simp [ht1]
  push_neg at ht1
  by_cases ht2 : t = ⊥
  · simp [ht2]
  push_neg at ht2
  lift t to ℝ using ⟨ht1,ht2⟩
  have hs1: {z | Real.toEReal t ≤ Real.toEReal z} = {z | t ≤ z} := by simp
  have hs2: {z | Real.toEReal t < Real.toEReal z} = {z | t < z} := by simp
  rw [hs1,hs2]
  have ho: IsOpen {z:ℝ | t < ↑z} := isOpen_lt continuous_const continuous_id'
  have hc: closure {z:ℝ | t < z} = {z:ℝ | t ≤ z} := by
    change closure (Ioi t) = (Ici t)
    exact closure_Ioi t
  rw [← hc, intrinsicInterior_closure]
  · rw [intrinsicInterior_open ho]
  change Convex ℝ (Ioi t)
  exact convex_Ioi t

def Cy_dom (f : E → EReal) : E → Set ℝ  := fun y => {z | (y, z) ∈ (f.Epi (dom univ f))}

lemma intrinsicInterior_of_ge_eq_le {z1 : ℝ} (f : E → EReal) (y : E) :
  z1 ∈ intrinsicInterior ℝ (Cy_dom f y) ↔ z1 > f y := by
  constructor
  · intro h
    simp only [Cy_dom, Epi] at h
    have : {z | (y, z) ∈ {p | p.1 ∈ dom univ f ∧ f p.1 ≤ Real.toEReal p.2}}
     = {z | f y ≤ Real.toEReal z} := by
      ext z; simp; intro h
      by_contra! hfy
      simp at hfy
      simp [hfy] at h
    simp only [this, intrinsic_le] at h
    exact h
  · intro h
    simp only [Cy_dom, Epi]
    apply interior_subset_intrinsicInterior
    simp
    refine mem_interior.mpr ?mpr.a.a
    use {x:ℝ| (2:ℝ).toEReal * x > z1 + f y}
    have hfy: f y < ⊤ := lt_top_of_lt h
    constructor
    · simp
      intro x hx
      have fyx: f y ≤ x := by
        by_cases hfy2 : f y = ⊥
        simp [hfy2]
        push_neg at hfy2
        lift (f y) to ℝ using ⟨(LT.lt.ne_top h), hfy2⟩ with fy
        simp at *
        rw [← coe_add, ← coe_mul, EReal.coe_lt_coe_iff] at hx
        linarith
      exact ⟨hfy, fyx⟩
    · constructor
      · by_cases hfy2 : f y = ⊥
        · simp [hfy2]
          have : {x:ℝ | ⊥ < (2:ℝ).toEReal * x.toEReal} = univ := by
            ext x; constructor
            intro hx
            simp at hx; simp
            intro hx
            simp; rw [← coe_mul]
            exact bot_lt_coe (2 * x)
          simp [this]
        push_neg at hfy2
        lift (f y) to ℝ using ⟨(LT.lt.ne_top h), hfy2⟩ with fy
        have : {x:ℝ | (2:ℝ).toEReal * x.toEReal > z1.toEReal + fy.toEReal} =
          {x:ℝ | 2 * x > z1 + fy} := by
          ext x; simp [← coe_add, ← coe_mul, EReal.coe_lt_coe_iff]
        rw [this]
        refine isOpen_lt continuous_const <| continuous_mul_left 2
      · simp
        by_cases hfy2 : f y = ⊥
        · simp [hfy2]
          rw [← coe_mul]
          exact bot_lt_coe (2 * z1)
        push_neg at hfy2
        lift (f y) to ℝ using ⟨(LT.lt.ne_top h), hfy2⟩ with fy
        rw [← coe_add, ← coe_mul, EReal.coe_lt_coe_iff]
        linarith [EReal.coe_lt_coe_iff.mp h]

end aux_lemma

section intrinsicinterior_epigraph
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-!
Theorem 7.3
-/
theorem mem_intrinsicInterior_epi_iff {y z} [FiniteDimensional ℝ E]
  (f : E → EReal) (hf : ConvexOn ℝ (dom univ f) f) :
  (y,z) ∈ intrinsicInterior ℝ (f.Epi (dom univ f)) ↔
  (y ∈ intrinsicInterior ℝ (dom univ f)) ∧ (z > f y) := by
  have Epi_convex: Convex ℝ (f.Epi (dom univ f)) := convex_epigraph hf
  have hCy : ∀ (y : E), Cy_dom f y = {z | (y, z) ∈ (f.Epi (dom univ f))} := fun _ => rfl
  have hD : dom univ f = {y | (Cy_dom f y).Nonempty} := by
    simp [Cy_dom]; ext x
    constructor
    · intro hx; apply Set.nonempty_def.2; use ((f x).toReal + 1); simp [Epi]; use hx
      by_cases hfx : f x = ⊥; simp [hfx]; push_neg at hfx
      have hfx2 : f x ≠ ⊤ := LT.lt.ne_top hx
      lift (f x) to ℝ using ⟨hfx2 , hfx⟩ with fx
      simp [← coe_one, ← coe_add, @EReal.coe_le_coe_iff]
    · intro hx;
      simp [Epi] at hx
      obtain ⟨x,hxx⟩ := Set.nonempty_def.1 hx
      exact hxx.1
  constructor
  · intro h
    obtain ⟨hyz1, hyz2⟩ := (mem_intrinsicInterior_prod_iff Epi_convex (Cy_dom f) hCy hD y z).1 h
    exact ⟨hyz1, (intrinsicInterior_of_ge_eq_le f y).mp hyz2⟩
  · intro h
    apply (mem_intrinsicInterior_prod_iff Epi_convex (Cy_dom f) hCy hD y z).2
    exact ⟨h.1, (intrinsicInterior_of_ge_eq_le f y).2 h.2⟩


theorem intrinsicInterior_epi_eq [FiniteDimensional ℝ E]
  (f : E → EReal) (hf : ConvexOn ℝ (dom univ f) f) :
  intrinsicInterior ℝ (f.Epi (dom univ f)) =
  {(y,z) | (y ∈ intrinsicInterior ℝ (dom univ f)) ∧ (z > f y)}
  := by
  ext yz
  constructor
  · intro h
    change (yz.1 ∈ intrinsicInterior ℝ (dom univ f)) ∧ (yz.2 > f yz.1)
    exact (mem_intrinsicInterior_epi_iff f hf).mp h
  intro h
  -- apply?
  sorry

/-
Corollary 7.3.1
-/
theorem lt_real_in_ridom_nonempty (f : E → EReal) (hf : ConvexOn ℝ (dom univ f) f) (α : ℝ)
  (hflt : ∃ x, f x < α) : ∃ x ∈ intrinsicInterior ℝ (dom univ f) , f x < α := by
  sorry

end intrinsicinterior_epigraph
