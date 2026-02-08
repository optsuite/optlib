/-
Copyright (c) 2025  Yifan Bai, Yunxi Duan, Zichen Wang, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yifan Bai, Yunxi Duan, Zichen Wang, Chenyi Li
-/
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Reaslib.ConvexAnalysis.IntrinsicInterior
import Reaslib.ConvexAnalysis.ClosedFunction_Closure

/-!
# Affine minorant of a function
This file explores the affine minorant of a function `f`, which is defined by the affine functions
below `f`. A convex and lower semi-continuous function is the supreme of its affine minorants,
which is an important theorem in convex analysis.

## References

* Chapter 12 of [R. T. Rockafellar, *Convex Analysis*][rockafellar1970].
-/

open Set Module EReal Inner

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

section closed_convex_affinesup

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → EReal}

section aux_structure

/-
Affine maps below an extended real-value function on a set `s`.
Purpose: to give a more precise geometric understanding of closed functions.
-/
structure affine_minorant (s : Set E) (f : E → EReal) where
  h : E →ᵃ[ℝ] ℝ
  hlw : ∀ x ∈ s, h x ≤ f x

/-!
Instance. If the domain is empty, then the affine minorant is nonempty.
Purpose: nonemptiness of affine minorants in the special case where `s = ∅`.
-/
instance Nonempempty_of_empty (hs : s = ∅) : Nonempty (affine_minorant s f) := by
  use 0; simp [hs]

/-
φ is the inverse of the canonical linear equivalence between `E^* × ℝ^*` and `(E × ℝ)^*`.
Specifically, for any `l ∈ (E × ℝ)^*, (φ l).1 ∈ E^*, (φ l).2 ∈ ℝ^*`.
Note that `φ(l) = ((φ l).1, (φ l).2)`.
-/
private noncomputable def φ := (dualProdDualEquivDual ℝ E ℝ).symm

/-!
Lemma. For any `l ∈ (E × ℝ)^*`, `l(x.1, x.2) = (φ l).1 x.1 + (φ l).2 x.2`.
Purpose: decompose the representation of `l x`.
-/
lemma phi_add :  ∀ l : Dual ℝ (E × ℝ), ∀ x, l x = (φ l).1 x.1 + (φ l).2 x.2 := by
  intro l x
  rw [← Module.dualProdDualEquivDual_apply_apply ℝ E ℝ _ _]
  apply LinearMap.congr_fun
    ((LinearEquiv.symm_apply_eq (Module.dualProdDualEquivDual ℝ E ℝ)).1 (by rfl)) _

/-!
Lemma. Riesz representation theorem in dimension 1.
Since `ℝ ≅ ℝ^*`, so `(φ l).2` is nothing but the scalar `(φ l).2 1` times the identity map on ℝ.
Purpose: represent `(φ l).2` with a simpler formulation.
-/
lemma riesz_one : ∀ l: Dual ℝ (E × ℝ), ∃ u, ∀ x, (φ l).2 x = u * x := by
  intro l
  use (φ l).2 1
  intro x
  simp

/-
Choose and fix the scalar in the Riesz representation of `(φ l).2`.
-/
private noncomputable def u : Dual ℝ (E × ℝ) → ℝ := fun l => (riesz_one l).choose

/-!
Lemma. Replacing `u` in `riesz_one` with the chosen `u` above.
Purpose: eliminate the existence in riesz_one.
-/
lemma u_spec : ∀ l : Dual ℝ (E × ℝ), ∀ x, (φ l).2 x = (u l) * x :=
  fun l => (riesz_one l).choose_spec

/-!
Corollary 12.1.2.
Instance. Let `f` be a proper, convex, closed function on a convex set `s`.
Then there exists an affine minorant of `f` over `s`.
Purpose: existence of affine minorants.
-/
instance Nonempty_affine_minorant (hsf : ProperFunction s f) (hf : ConvexOn ℝ s f)
    (hfcl : f.IsClosed s) :
    Nonempty (affine_minorant s f) := by
  by_cases hs : s = ∅
  · exact Nonempempty_of_empty hs
  let x := (exist_xs_lt_top (hsf := hsf) hs).choose
  have hx : x ∈ s := (exist_xs_lt_top (hsf := hsf) hs).choose_spec.1
  have htop : f x < ⊤ := (exist_xs_lt_top (hsf := hsf) hs).choose_spec.2
  have ⟨l, t, hl1, hl2⟩:= geometric_hahn_banach_point_closed (EReal.convex_epigraph hf)
    hfcl (disj htop hx)
  have : ∀ x, l x  = l.toLinearMap x := fun x ↦ rfl
  rw [this, phi_add] at hl1
  have hl3 := lt_trans hl1 (hl2 _ (xfxinepif htop hx))
  rw [this, phi_add] at hl3
  simp [u_spec, mul_sub] at hl3
  let il := LinearMap.mk (σ := RingHom.id ℝ)
    ⟨fun x => (- (@φ E _ _ l).1 x) / @u E _ _ l, by intro x y; simp; field_simp; ring⟩
    (by intro x y; simp; field_simp;)
  let i1 := AffineMap.mk' (fun x => (- (@φ E _ _ l).1 x + t) / @u E _ _ l) il 0
    (by intro x;field_simp;simp [il];field_simp;)
  use i1
  intro x hx
  simp [i1]
  by_cases hfx : f x = ⊤
  · rw[hfx];simp
  rw[← EReal.coe_toReal (x := f x) hfx (LT.lt.ne_bot (hsf.uninfinity x hx))]
  rw[EReal.coe_le_coe_iff, div_le_iff₀' hl3, neg_add_le_iff_le_add]
  have hl4 := hl2 _ (xfxinepif (Ne.lt_top' fun a ↦ hfx (id (Eq.symm a))) hx)
  rw [this, phi_add, u_spec] at hl4
  simp at hl4
  exact le_of_lt hl4


/-!
Lemma. Epigraph of `f` on a set `s` is contained in the intersection
of the epigraphs of all affine minorants of `f`.
Purpose: one of the directions of `closed_convex_function_is_sup_of_affine_bound_of_proper`.
-/
lemma epi_sub_inter_epi :
    f.Epi s ⊆ ⋂ i : affine_minorant s f, (fun x ↦ (i.1 x).toEReal).Epi s := by
  intro x hx
  simp [Function.Epi]
  exact fun fh ↦ ⟨hx.1, EReal.coe_le_coe_iff.1 <| le_trans (fh.hlw x.1 hx.1) (hx.2)⟩

/-
If there exists a point `x ∈ s` such that `f x = ⊥`, then `f` does not have
affine minorant on `s`.
Purpose: avoid the case that `f` has a `⊥` point.
-/
instance empty_affine_minorant (hfex : ∃ x ∈ s, f x = ⊥) :
    IsEmpty (affine_minorant s f) := by
  refine isEmpty_iff.mpr ?_
  intro l
  obtain ⟨x, hs, hfx⟩ := hfex
  have := l.2 x hs
  rw[hfx] at this
  simp at this

end aux_structure

section Thm_12_1

/-
Let `f` be a proper, convex, closed function on a convex set `s`.
`h₂` is one of the affine minorants of `f`.
Purpose: choose and fix an affine minorant of `f`.
-/
noncomputable def h₂ [hsf : ProperFunction s f] (hf : ConvexOn ℝ s f)
    (hfcl : f.IsClosed s) : affine_minorant s f :=
  @Classical.ofNonempty _ (Nonempty_affine_minorant hsf hf hfcl)

/-!
Lemma. Let `f` be a proper, convex, closed function on a convex set `s`.
Suppose `x` is in the intersection of the epigraph of the affine minorants of `f` on `s`,
then `x.1 ∈ s`.
Purpose: part of the proof of `inter_epi_sub_epi`.
-/
lemma x_in_domain_of_inter [hsf : ProperFunction s f]
    (hf : ConvexOn ℝ s f) (hfcl : f.IsClosed s)
    (hx : x ∈ ⋂ i : affine_minorant s f, (fun x ↦ (i.1 x).toEReal).Epi s) :
    x.1 ∈ s := by
  simp at *
  have := hx (h₂ hf hfcl)
  simp [Function.Epi] at this
  apply this.1

/-!
Lemma. Let `f` be a proper, convex, closed function on a set `s` and `h` be a
linear functional such that `h(a) < u` for all `a` in the epigraph of `f`.
If `h` decomposes as `h(x) = φ.1 x.1 + w * x.2`, then the scalar `w` must be non-positive.
Purpose: part of proof of `inter_epi_sub_epi`.
-/
lemma le_zero_of_phi_add {φ : Dual ℝ E × Dual ℝ ℝ} {f : E → EReal} [hsf : ProperFunction s f]
  {y : E} {h : E × ℝ →L[ℝ] ℝ} {w u : ℝ} (hua : ∀ a ∈ Function.Epi f s, h a < u)
  (phi_add : ∀ (x : E × ℝ), h x = φ.1 x.1 + w * x.2)
  (hys : y ∈ s) (hy : f y < ⊤) : w ≤ 0 := by
  let wh := max (f y).toReal ((u - φ.1 y) / w)
  have inepi : h (y, wh) < u := by
    apply hua
    simp [Function.Epi]
    constructor
    · exact hys
    rw[← EReal.coe_toReal (x := f y) (LT.lt.ne_top hy) (LT.lt.ne_bot (hsf.1 y hys))]
    simp [wh]
  simp [wh, phi_add] at inepi
  contrapose! inepi
  calc _
    _ = φ.1 y + w * ((u - φ.1 y) / w) := by field_simp; ring
    _ ≤  _  := by
      rw[add_le_add_iff_left, mul_le_mul_iff_of_pos_left inepi]
      apply le_max_right

/-!
Lemma. Let `f` be a proper, convex, closed function on a set `s` and `h` be a
linear functional such that `h(a) < u` for all `a` in the epigraph of `f`.
If `h` decomposes as `h(x) = φ.1 x.1 + 0 * x.2`, then for any finite point `t ∈ s`, `φ.1 t ≤ u`.
Purpose: part of proof of `exist_of_ne_zero_of_phi_add`.
-/
lemma le_of_ne_top_zero {φ : Dual ℝ E × Dual ℝ ℝ} {f : E → EReal}
  [hsf : ProperFunction s f] {h : E × ℝ →L[ℝ] ℝ} {w u : ℝ}
  (hua : ∀ a ∈ Function.Epi f s, h a < u)
  (phi_add : ∀ (x : E × ℝ), h x = φ.1 x.1 + w * x.2)
  (hw : w = 0) {t : E} (ht : t ∈ s)
  (hfttop : ¬f t = ⊤) : φ.1 t ≤ u := by
  have : (t , (f t).toReal) ∈ Function.Epi f s := by
    refine xfxinepif ?htop ht
    exact Ne.lt_top' fun a ↦ hfttop (id (Eq.symm a))
  have := hua _ this
  simp [phi_add, hw] at this
  exact le_of_lt this

/-!
Lemma. Let `f` be a proper, convex, closed function on a set `s` and `h` be a
linear functional such that `h(a) < u` for all `a` in the epigraph of `f`.
If `h` decomposes as `h(x) = φ.1 x.1 + 0 * x.2` and `h(x) > u`, then there exists
an affine minorant `i` of `f` such that `x.2 < i.h x.1`.
Purpose: part of proof of `inter_epi_sub_epi`.
-/
lemma exist_of_ne_zero_of_phi_add {φ : Dual ℝ E × Dual ℝ ℝ} {f : E → EReal}
    [hsf : ProperFunction s f] {h : E × ℝ →L[ℝ] ℝ} {w u : ℝ}
    (hf : ConvexOn ℝ s f) (hfcl : f.IsClosed s)
    (hua : ∀ a ∈ Function.Epi f s, h a < u) (hux : u < h x)
    (phi_add : ∀ (x : E × ℝ), h x = φ.1 x.1 + w * x.2) (hw : w = 0) :
    ∃ i : affine_minorant s f, x.2 < i.h x.1 := by
  let h₁ : affine_minorant s f := h₂ hf hfcl
  let la := max (1 + (x.2 - h₁.h x.1) / (φ.1 x.1 - u)) 0
  let hal := LinearMap.mk (σ := RingHom.id ℝ)
    ⟨fun x => φ.1 x, by intro x y;simp;⟩ (by intro x y;simp;)
  let ha := AffineMap.mk' (fun x => φ.1 x - u) hal 0
    (by intro x;simp;exact rfl)
  let i : affine_minorant s f := ⟨la • ha + h₁.1,
    by
      intro t ht
      simp
      by_cases hfttop : f t = ⊤
      · rw[hfttop];simp
      calc _
        _ ≤ (h₁.h t).toEReal := by
          rw[← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
          simp
          apply mul_nonpos_of_nonneg_of_nonpos
          exact le_max_right _ 0
          simp [ha]
          apply le_of_ne_top_zero (hsf := hsf) hua phi_add hw ht hfttop
        _ ≤ _ := h₁.2 t ht⟩
  use i; simp [i, la, ha]
  have : φ.1 x.1 - u > 0:= by
    simp
    calc _
      _ < h x := hux
      _ = _ := by simp [phi_add, hw]
  calc _
    _ ≤ ((x.2 - h₁.h x.1) / (φ.1 x.1 - u)) * (φ.1 x.1 - u) + h₁.h x.1 := by field_simp; simp
    _ < (1 + (x.2 - h₁.h x.1) / (φ.1 x.1 - u)) * (φ.1 x.1 - u) + h₁.h x.1 := by
      field_simp; ring_nf; linarith
    _ ≤  _ := by
      rw[add_le_add_iff_right, propext (mul_le_mul_iff_left₀ this)]; simp

/-!
Lemma. Let `f` be a proper, convex, closed function on a set `s` and `h` be a
linear functional such that `h(a) < u` for all `a` in the epigraph of `f`.
If `h` decomposes as `h(x) = φ.1 x.1 + w * x.2` with `w < 0` and `h(x) > u`, then there exists
an affine minorant `i` of `f` such that `x.2 < i.h x.1`.
Purpose: part of proof of `inter_epi_sub_epi`.
-/
lemma exist_of_lt_zero_of_phi_add {φ : Dual ℝ E × Dual ℝ ℝ} {f : E → EReal}
    [hsf : ProperFunction s f] {h : E × ℝ →L[ℝ] ℝ} {w u : ℝ}
    (hua : ∀ a ∈ Function.Epi f s, h a < u) (hux : u < h x)
    (phi_add : ∀ (x : E × ℝ), h x = φ.1 x.1 + w * x.2) (hw : w < 0) :
    ∃ i : affine_minorant s f, x.2 < i.h x.1 := by
  let il := LinearMap.mk (σ := RingHom.id ℝ)
    ⟨fun x => (- φ.1 x) / w, by intro x y; simp; field_simp;ring⟩
    (by intro x y; simp; field_simp;)
  let i1 := AffineMap.mk' (fun x => (- φ.1 x + u) / w) il 0
    (by intro x;field_simp;simp [il];field_simp;)
  let i : affine_minorant s f := affine_minorant.mk i1
    (by
      intro z hz
      simp [i1]
      by_cases hfx : f z = ⊤
      · rw[hfx];simp
      rw[← EReal.coe_toReal (x := f z) hfx (LT.lt.ne_bot (hsf.uninfinity z hz))]
      rw[EReal.coe_le_coe_iff, div_le_iff_of_neg hw]
      have : (z , (f z).toReal) ∈ Function.Epi f s := by
        refine xfxinepif ?htop hz
        exact Ne.lt_top' fun a ↦ hfx (id (Eq.symm a))
      have := hua _ this
      simp [phi_add] at this
      apply le_of_lt
      linarith
    )
  use i
  simpa [i, i1, lt_div_iff_of_neg hw, mul_comm, ← phi_add]

/-!
Lemma. Let `f` be a proper, convex, closed function on a nonempty convex set `s`.
Suppose `x` is in the intersection of the epigraph of the affine minorants of `f`,
then `x` is in the epigraph of `f`.
Purpose: provides a geometric description of
`closed_convex_function_is_sup_of_affine_bound_of_proper`.
-/
lemma inter_epi_sub_epi [hsf : ProperFunction s f] (hs : s ≠ ∅)
    (hf : ConvexOn ℝ s f) (hfcl : f.IsClosed s)
    (hx : x ∈ ⋂ i : affine_minorant s f, (fun x ↦ (i.1 x).toEReal).Epi s) :
    x ∈ f.Epi s := by
  have hx1s : x.1 ∈ s := x_in_domain_of_inter hf hfcl hx
  by_cases hfx : f x.1 ≤ x.2
  · exact ⟨hx1s, hfx⟩
  by_contra! hfxs
  have hs₁ : Convex ℝ (Function.Epi f s) := convex_epigraph hf
  have ⟨h, u, hua, hux⟩:= geometric_hahn_banach_closed_point hs₁ hfcl hfxs
  let φ := (dualProdDualEquivDual ℝ E ℝ).symm h
  have ⟨w, hw⟩ : ∃ w, ∀ x, φ.2 x = w * x := ⟨φ.2 1, fun x ↦ by simp⟩
  have phi_add : ∀ x, h x = φ.1 x.1 + w * x.2 := by
    intro  x
    rw [← hw, ← Module.dualProdDualEquivDual_apply_apply ℝ E ℝ _ _]
    apply LinearMap.congr_fun
    exact (LinearEquiv.apply_symm_apply _ _).symm
  have ⟨y, hys, hy⟩ := exist_xs_lt_top (f := f) hs
  have ⟨i, hi⟩ : ∃ i : affine_minorant s f, x.2 < i.h x.1 := by
    rcases (lt_or_eq_of_le (le_zero_of_phi_add hua phi_add hys hy)) with hw0 | hw0
    exact exist_of_lt_zero_of_phi_add hua hux phi_add hw0
    exact exist_of_ne_zero_of_phi_add hf hfcl hua hux phi_add hw0
  simp [Function.Epi] at hx
  linarith [(hx i).2]


/-!
Theorem 12.1 (affine minorant).
Let `f` be a proper, convex, closed function on a convex set `s`.
Then for any `x ∈ s`, `f(x)` equals to the supremum of its all affine minorants at `x`.
Purpose: provides a description of a closed function using its affine minorants.
-/
theorem closed_convex_function_is_sup_of_affine_bound_of_proper
    [hsf : ProperFunction s f]
    (hf : ConvexOn ℝ s f) (hfcl : f.IsClosed s) :
    ∀ x ∈ s, f x = ⨆ h : affine_minorant s f, (h.1 x).toEReal := by
  by_cases hs : s = ∅
  · simp [hs]
  apply point_sup_of_epi_inter
  rw[Set.Subset.antisymm_iff]
  refine ⟨epi_sub_inter_epi, ?_⟩
  intro x hx
  exact inter_epi_sub_epi hs hf hfcl hx

/-!
Theorem 12.1 (lower semicontinuous function).
For a lower semicontinuous and convex function `f`, `f` is the supreme
of its affine minorants.
Purpose: provides a description of a lower-semicontinuous function using its affine minorants.
-/
theorem closed_convex_function_is_sup_of_affine_bound_univ
    (hf : ConvexOn ℝ univ f) (hfcl : LowerSemicontinuous f) :
    ∀ x, f x = ⨆ h : affine_minorant univ f, (h.1 x).toEReal := by
  intro x
  by_cases hsf : ProperFunction univ f
  · exact closed_convex_function_is_sup_of_affine_bound_of_proper hf
      (by
        refine (epiclosed f univ).mpr ?_
        refine epi_is_closed_of_lowersemicontinuous isClosed_univ
            (lowerSemicontinuousOn_univ_iff.mpr hfcl)
        ) x trivial
  have := ProperFuntion.conveximproper_nonfinte (convexOn_dom_s_f_of_convexOn_s hf)
    (lowerSemicontinuousOn_univ_iff.mpr hfcl) hsf
  by_cases hfex : ∃ x, f x = ⊥
  · rcases hfex with ⟨u, hfu⟩
    letI iem : IsEmpty (affine_minorant univ f) := empty_affine_minorant ⟨u, trivial, hfu⟩
    rw[iSup_of_empty]
    apply bot_of_exist_bot_of_convex_of_univ hf ⟨u, hfu⟩
  push_neg at hfex
  have htop : ∀ x, f x = ⊤ := by
    intro x
    rcases this x trivial with hfx | hfx
    · exact hfx
    exfalso;exact hfex x hfx
  rw[htop x]
  symm;rw[iSup_eq_top]
  intro b hb
  use ⟨AffineMap.const ℝ E (b.toReal + 1),
    fun y _ => by rw[htop y];simp⟩
  simp only [AffineMap.const_apply, coe_add]
  by_cases hb' : b = ⊥
  · rw[hb'];simp;exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  nth_rw 1 [← EReal.coe_toReal (x := b) (LT.lt.ne_top hb) hb']
  rw[← EReal.coe_add, EReal.coe_lt_coe_iff]
  exact lt_add_one b.toReal

/-!
Lemma. Affine minorants of a function `f` can be written in the form of `⟪l, x⟫ + w`.
Purpose: provides the general mathematical formulation of affine map.
-/
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma exist_of_affine_minorant [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] (i : affine_minorant s f) :
  ∃ (l : E) (w : ℝ) (_hz : ∀ x ∈ s, ⟪l, x⟫ + w ≤ f x),
    ∀ x ∈ s , i.h x =  ⟪l, x⟫ + w := by
  let g := LinearMap.toContinuousLinearMap i.h.linear
  let l := (InnerProductSpace.toDual ℝ E).symm g
  let w := i.h 0
  use l, w
  simp
  constructor
  · intro x hx
    simpa [w, l, g, AffineMap.decomp', ← EReal.coe_sub, ← EReal.coe_add] using i.hlw x hx
  intro x _hx
  simp [w, l, g, AffineMap.decomp']

/-!
Theorem 12.1 (finite dimensional).
For a lower semicontinuous and convex function `f`, `f` is the
supreme of its affine minorants.
Purpose: replace the affine map in `closed_convex_function_is_sup_of_affine_bound_univ`
with its mathematical formulation `⟪l, x⟫ + w`.
-/
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem closed_convex_function_is_sup_of_affine_bound_univ'
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  (hf : ConvexOn ℝ univ f) (hfcl : LowerSemicontinuous f) :
  ∀ x, f x = ⨆ (l : E) (w : ℝ) (_ : ∀ x ∈ univ, ⟪l, x⟫ + w ≤ f x),(⟪l, x⟫ + w).toEReal := by
  intro x
  rw[le_antisymm_iff]
  constructor
  · simp [closed_convex_function_is_sup_of_affine_bound_univ hf hfcl x]
    intro i
    obtain ⟨l, w, hlw, hi⟩ :=  exist_of_affine_minorant i
    simp [hi x]
    apply le_triSup (fun l w => ⟪l, x⟫.toEReal + w.toEReal) l w
      (fun l w => ∀ x, ⟪l, x⟫ + w.toEReal ≤ f x) (fun x ↦ hlw x trivial)
  simp
  intro l w hlw
  exact hlw x

end Thm_12_1

end closed_convex_affinesup
