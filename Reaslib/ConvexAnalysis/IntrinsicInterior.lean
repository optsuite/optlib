/-
Copyright (c) 2025 Pengfei Hao, Yuhao Jiang, Zichen Wang, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Join

set_option linter.style.commandStart true


/-!
# Intrinsic Interior, Closure, and Related Properties of Convex Sets
This file explores the intrinsic interior, intrinsic closure,
and related properties of convex sets in a normed vector space,
focusing on their interactions with affine spans, closures, and intersections.
These concepts are essential in convex analysis and finite-dimensional spaces.
The intrinsic interior and closure of a convex set are defined based on its affine span,
while the intrinsic interior is generally larger than the topological interior,
and the intrinsic closure coincides with the topological closure under certain conditions.

## References

* Chapter 6 of [R. T. Rockafellar, *Convex Analysis*][rockafellar1970].
-/

open AffineSubspace Set

open scoped Pointwise

variable {𝕜 V P : Type*}

noncomputable section

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

/-
Given a nonempty set s, it defines an isomorphism
between the affine span and its direction
-/
@[simp]
def affSpanEquiv {s : Set P} (hs : s.Nonempty) :
    affineSpan 𝕜 s ≃ (affineSpan 𝕜 s).direction where
  toFun := fun x => ⟨x.1 -ᵥ hs.choose,
    AffineSubspace.vsub_mem_direction (SetLike.coe_mem x) (mem_affineSpan _ hs.choose_spec)⟩
  invFun := fun x => ⟨x +ᵥ hs.choose,
    AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.coe_mem x) (mem_affineSpan _ hs.choose_spec)⟩
  left_inv := by
    simp [Function.LeftInverse]
    intro a _
    exact ((eq_vadd_iff_vsub_eq a _ _).mpr rfl).symm
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    intro a _
    exact AddTorsor.vadd_vsub' _ _

/-!
Lemma. Intrinsic interior of `s` is included in the intrinsic interior of `intrinsicClosure s`.
Key idea: rewrite via affine span preimage and use interior monotonicity.
-/
theorem intrinsicInterior_sub_intrinsicClosure_intrinsicInterior [TopologicalSpace V]
    {s : Set V} :
    intrinsicInterior 𝕜 s ⊆ intrinsicInterior 𝕜 (intrinsicClosure 𝕜 s) := by
  simp [intrinsicInterior]
  rw [affineSpan_intrinsicClosure s, Function.Injective.preimage_image Subtype.val_injective]
  apply interior_mono (preimage_mono subset_intrinsicClosure)

end

noncomputable section

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [ContinuousSub V] [ContinuousAdd V]

/-
This defines an affine span equivalence between a set s in the vector space V and its direction.
-/
@[simp]
def affSpanDirEquiv
    {s : Set V} (hs : s.Nonempty) :
  affineSpan 𝕜 s ≃ₜ (affineSpan 𝕜 s).direction :=
    ⟨affSpanEquiv 𝕜 hs, by
      simpa only [affSpanEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
      using .subtype_mk (.comp (continuous_sub_right _) continuous_subtype_val) _, by
      simpa only [affSpanEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
      using .subtype_mk (.comp (continuous_add_right _) continuous_subtype_val) _⟩

/-
It is a function that maps affine space elements to the vector space V.
This is prepared for defining **affSpanCoerce**
-/
@[simp]
def affSpanCoerce_pre' {s : Set V} (hs : s.Nonempty) :=
  ((↑) : (affineSpan 𝕜 s) → V) ∘ (affSpanDirEquiv 𝕜 hs).symm

/-!
Lemma. Every point of `s` lies in the range of `affSpanCoerce_pre'`.
Purpose: ensures later image–preimage formulas cover `s`.
-/
lemma sub_range {s : Set V} (hs : s.Nonempty) :
    s ⊆ range (affSpanCoerce_pre' 𝕜 hs) := by
  intro x hx
  simp only [affSpanCoerce_pre', affSpanDirEquiv, affSpanEquiv, vsub_eq_sub,
    Homeomorph.homeomorph_mk_coe_symm, Equiv.coe_fn_symm_mk, mem_range, Function.comp_apply,
    Subtype.exists]
  have b : x -ᵥ Exists.choose hs ∈ (affineSpan 𝕜 s).direction := by
    refine vsub_mem_direction ?hp1 ?hp2
    exact mem_affineSpan 𝕜 hx
    refine mem_affineSpan 𝕜 hs.choose_spec
  use x -ᵥ Exists.choose hs, b
  symm
  exact (eq_vadd_iff_vsub_eq x _ _).mpr rfl

/-!
Lemma. If `x` is in the range of `affSpanCoerce_pre'`,
then `invFun` followed by the map returns `x`.
Purpose: provides a partial inverse on the range.
-/
lemma inv_eq_self {x} {s : Set V} (hs : s.Nonempty) (hx : x ∈ range (affSpanCoerce_pre' 𝕜 hs)) :
   (affSpanCoerce_pre' 𝕜 hs) (Function.invFun (affSpanCoerce_pre' 𝕜 hs) x) = x := by
  let g := (affSpanCoerce_pre' 𝕜 hs)
  change g (Function.invFun g x) = x
  simp only [Function.invFun]
  have : ∃ x_1, g x_1 = x := ⟨hx.choose, hx.choose_spec⟩
  simpa [this] using this.choose_spec

/-!
Lemma. `s` equals the image of its preimage under `affSpanCoerce_pre'`.
Purpose: expresses `s` via an image–preimage factorization.
-/
lemma eq_image_preimage {s : Set V} (hs : s.Nonempty) :
    s = (affSpanCoerce_pre' 𝕜 hs) '' ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s) := by
  refine Eq.symm (image_preimage_eq_of_subset ?hs)
  exact sub_range 𝕜 hs

/-
This defines a linear map from the direction of the affine span of s back to the vector space V.
-/
def affSpanCoerce_pre {s : Set V} (hs : s.Nonempty) :
    (affineSpan 𝕜 s).direction →ᵃ[𝕜] V where
  toFun := affSpanCoerce_pre' 𝕜 hs
  linear := (affineSpan 𝕜 s).direction.subtype
  map_vadd' := by
    simp [affSpanCoerce_pre']
    intro x _ y _
    exact add_assoc y x _

/-!
Lemma. Same image–preimage factorization for `affSpanCoerce_pre`.
Purpose: prepares intrinsic interior/closure formulas.
-/
lemma pre_eq_image_preimage {s : Set V} (hs : s.Nonempty) :
    s = (affSpanCoerce_pre 𝕜 hs) '' ((affSpanCoerce_pre 𝕜 hs) ⁻¹' s) := by
  refine Eq.symm (image_preimage_eq_of_subset ?hs)
  exact sub_range 𝕜 hs

/-!
Lemma. `affSpanCoerce_pre` is injective.
Purpose: enables using `invFun` as a left inverse on the image.
-/
lemma affSpanCoerce_pre_Injective {s : Set V} (hs : s.Nonempty) :
    Function.Injective (affSpanCoerce_pre 𝕜 hs) :=
  (AffineMap.linear_injective_iff _).mp <|
    (injective_codRestrict Subtype.property).mp fun _ _ a ↦ a

/-!
Lemma. For any set `u`, `invFun` on the image of `affSpanCoerce_pre` returns `u`.
Purpose: establishes the left-inverse property on images.
-/
lemma pre_inv_self_eq_id {s : Set V} (hs : s.Nonempty) (u) :
  (Function.invFun (affSpanCoerce_pre 𝕜 hs)) '' ((affSpanCoerce_pre 𝕜 hs) '' u) = u :=
  Function.LeftInverse.image_image
    (Function.leftInverse_invFun (affSpanCoerce_pre_Injective 𝕜 hs)) u

/-!
Theorem. Intrinsic interior of `s` equals the image under `affSpanCoerce_pre`
of the topological interior of the preimage.
Purpose: reduces intrinsic interior to standard interior in the direction space.
-/
theorem intrinsicInterior_equiv_pre {s : Set V} (hs : s.Nonempty) :
    intrinsicInterior 𝕜 s =
    (affSpanCoerce_pre 𝕜 hs) '' (interior ((affSpanCoerce_pre 𝕜 hs) ⁻¹' s)) := by
  change intrinsicInterior 𝕜 s =
    (affSpanCoerce_pre' 𝕜 hs) '' (interior ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s))
  rw [affSpanCoerce_pre', preimage_comp, image_comp]
  rw [((affSpanDirEquiv 𝕜 hs).symm).image_interior, ((affSpanDirEquiv 𝕜 hs).symm).image_preimage]
  rfl

/-!
Theorem. Intrinsic closure of `s` equals the image under `affSpanCoerce_pre`
of the topological closure of the preimage.
Purpose: reduces intrinsic closure to standard closure in the direction space.
-/
theorem intrinsicClosure_equiv_pre {s : Set V} (hs : s.Nonempty) :
    intrinsicClosure 𝕜 s =
      (affSpanCoerce_pre 𝕜 hs) '' (closure ((affSpanCoerce_pre 𝕜 hs) ⁻¹' s)) := by
  change intrinsicClosure 𝕜 s =
    (affSpanCoerce_pre' 𝕜 hs) '' (closure ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s))
  rw [affSpanCoerce_pre', preimage_comp, image_comp]
  rw [((affSpanDirEquiv 𝕜 hs).symm).image_closure, ((affSpanDirEquiv 𝕜 hs).symm).image_preimage]
  rfl

end

noncomputable section

variable (𝕜) [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-
This defines an affine map (affineMap)
from the direction of the affine span of s to the vector space V.
-/
def affSpanCoerce {s : Set V} (hs : s.Nonempty) :
    (affineSpan 𝕜 s).direction →ᵃⁱ[𝕜] V :=
      .mk (affSpanCoerce_pre 𝕜 hs) (by simp [affSpanCoerce_pre])

/-!
Lemma. For any set `u`, `invFun` on the image of `affSpanCoerce` returns `u`.
Purpose: same left-inverse property in the isometric affine setting.
-/
lemma inv_self_eq_id {s : Set V} (hs : s.Nonempty) (u) :
  (Function.invFun (affSpanCoerce 𝕜 hs)) '' ((affSpanCoerce 𝕜 hs) '' u) = u :=
  Function.LeftInverse.image_image (Function.leftInverse_invFun (affSpanCoerce 𝕜 hs).injective) u

/-!
Theorem. Intrinsic interior of `s` equals the image under `affSpanCoerce`
of the topological interior of the preimage.
Purpose: intrinsic interior in a normed setting via the direction space.
-/
theorem intrinsicInterior_equiv {s : Set V} (hs : s.Nonempty) :
    intrinsicInterior 𝕜 s = (affSpanCoerce 𝕜 hs) '' (interior ((affSpanCoerce 𝕜 hs) ⁻¹' s)) := by
  change intrinsicInterior 𝕜 s =
    (affSpanCoerce_pre' 𝕜 hs) '' (interior ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s))
  rw [affSpanCoerce_pre', preimage_comp, image_comp]
  rw [((affSpanDirEquiv 𝕜 hs).symm).image_interior, ((affSpanDirEquiv 𝕜 hs).symm).image_preimage]
  rfl

/-!
Theorem. Intrinsic closure of `s` equals the image under `affSpanCoerce`
of the topological closure of the preimage.
Purpose: intrinsic closure in a normed setting via the direction space.
-/
theorem intrinsicClosure_equiv {s : Set V} (hs : s.Nonempty) :
    intrinsicClosure 𝕜 s = (affSpanCoerce 𝕜 hs) '' (closure ((affSpanCoerce 𝕜 hs) ⁻¹' s)) := by
  change intrinsicClosure 𝕜 s =
    (affSpanCoerce_pre' 𝕜 hs) '' (closure ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s))
  rw [affSpanCoerce_pre', preimage_comp, image_comp]
  rw [((affSpanDirEquiv 𝕜 hs).symm).image_closure, ((affSpanDirEquiv 𝕜 hs).symm).image_preimage]
  rfl

end

section

/-
Theorem. If a point `(m, n)` lies in the vector span of the product set `M × N`,
then `m` lies in the vector span of `M` and `n` lies in the vector span of `N`.
-/
theorem mem_vectorSpan_part_of_mem_prod [Field R] [AddCommGroup α] [Module R α] [AddCommGroup β]
    [Module R β] {M : Set α} {N : Set β} {m : α} {n : β} (h : (m, n) ∈ vectorSpan R (M ×ˢ N)) :
    m ∈ vectorSpan R M ∧ n ∈ vectorSpan R N := by
  have h1 : M ×ˢ N -ᵥ M ×ˢ N ⊆ Submodule.comap (LinearMap.fst R α β) (vectorSpan R M) := by
    rintro p ⟨c, hc, d, hd, rfl⟩
    apply vsub_mem_vectorSpan _ hc.1 hd.1
  have h2 : M ×ˢ N -ᵥ M ×ˢ N ⊆ Submodule.comap (LinearMap.snd R α β) (vectorSpan R N) := by
    rintro p ⟨c, hc, d, hd, rfl⟩
    apply vsub_mem_vectorSpan _ hc.2 hd.2
  rw [←Submodule.span_le] at h1 h2
  replace h1 := h1 h
  replace h2 := h2 h
  simp at h1 h2
  exact ⟨h1, h2⟩

/-
Theorem. If `m` lies in the vector span of `M` and `n` lies in the vector span of `N`,
then the point `(m, n)` lies in the vector span of the product set `M × N`.
-/
theorem mem_vectorSpan_prod_of_mem_part [Field R] [AddCommGroup α] [Module R α] [AddCommGroup β]
    [Module R β] {M : Set α} {N : Set β} {m : α} {n : β}
    (hm : m ∈ vectorSpan R M) (hn : n ∈ vectorSpan R N)
    (hM : M.Nonempty) (hN : N.Nonempty) :
    (m, n) ∈ vectorSpan R (M ×ˢ N) := by
  let v := vectorSpan R (M ×ˢ N)
  rcases hN with ⟨n0, hn0⟩
  rcases hM with ⟨m0, hm0⟩
  have h1 : M -ᵥ M ⊆ Submodule.comap (LinearMap.inl R α β) v := by
    rintro p ⟨c, hc, d, hd, rfl⟩
    exact Submodule.subset_span ⟨⟨c, n0⟩, ⟨hc, hn0⟩, ⟨d, n0⟩, ⟨hd, hn0⟩, by simp⟩
  have h2 : N -ᵥ N ⊆ Submodule.comap (LinearMap.inr R α β) v := by
    rintro v ⟨c, hc, d, hd, rfl⟩
    exact Submodule.subset_span ⟨⟨m0, c⟩, ⟨hm0, hc⟩, ⟨m0, d⟩, ⟨hm0, hd⟩, by simp⟩
  rw [←Submodule.span_le] at h1 h2
  replace h1 := h1 hm
  replace h2 := h2 hn
  simp at h1 h2
  simpa using Submodule.add_mem _ h1 h2

/-
Theorem. The affine span of the product set `M × N` equals the product of the affine spans of
`M` and `N`.
-/
theorem affineSpan_of_product_space [NontriviallyNormedField R] [NormedAddCommGroup α]
    [NormedSpace R α] [Module R α] [NormedAddCommGroup β] [NormedSpace R β] [Module R β]
    (M : Set α) (N : Set β) : (affineSpan R (M ×ˢ N) :
    Set (α × β)) = (affineSpan R M : Set α) ×ˢ (affineSpan R N : Set β) := by
  ext x; simp [spanPoints]
  constructor
  · intro ⟨a, b, ⟨ha, hb⟩, ⟨m, n, hmn, hx⟩⟩
    rw [Prod.eq_iff_fst_eq_snd_eq] at hx
    exact ⟨⟨a, ha, m, mem_vectorSpan_part_of_mem_prod hmn |>.1, hx.1⟩,
           ⟨b, hb, n, mem_vectorSpan_part_of_mem_prod hmn |>.2, hx.2⟩⟩
  · intro ⟨⟨a, ha, m, hm, hx⟩, ⟨b, hb, n, hn, hy⟩⟩
    exact ⟨a, b, ⟨ha, hb⟩,
      ⟨m, n, mem_vectorSpan_prod_of_mem_part hm hn ⟨a, ha⟩ ⟨b, hb⟩,
      Prod.eq_iff_fst_eq_snd_eq.2 ⟨hx, hy⟩⟩⟩

def Homeomorph.subtypeProd {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {p : X → Prop} {q : Y → Prop} :
    { c : X × Y // p c.1 ∧ q c.2 } ≃ₜ { a // p a } × { b // q b } where
  continuous_toFun := Continuous.prodMk
    (Continuous.subtype_mk
      (Continuous.comp' continuous_fst continuous_subtype_val) fun x ↦ x.property.left)
    (Continuous.subtype_mk
      (Continuous.comp' continuous_snd continuous_subtype_val) fun x ↦ x.property.right)

  continuous_invFun := by apply Continuous.subtype_mk; continuity
  __ := Equiv.subtypeProdEquivProd

theorem intrinsicInterior_prod_eq_prod_intrinsicInterior [NontriviallyNormedField R]
    [NormedAddCommGroup α] [NormedSpace R α] [NormedAddCommGroup β] [NormedSpace R β]
    (M : Set α) (N : Set β) :
    intrinsicInterior R (M ×ˢ N) = (intrinsicInterior R M) ×ˢ (intrinsicInterior R N) := by

  by_cases neM : ¬M.Nonempty
  · rw [not_nonempty_iff_eq_empty.mp neM]; simp
  push_neg at neM
  by_cases neN : ¬N.Nonempty
  · rw [not_nonempty_iff_eq_empty.mp neN]; simp
  push_neg at neN

  /- Subtype Homeomorph -/

  let phiM' : (affineSpan R M) → α := (↑)
  let phiN' : (affineSpan R N) → β := (↑)
  let phi' : (affineSpan R (M ×ˢ N)) → α × β := (↑)

  let subtype := { x // x ∈ affineSpan R (M ×ˢ N)}
  let subtypeM := { x : α // x ∈ affineSpan R M }
  let subtypeN := { y : β // y ∈ affineSpan R N }

  have affSpan_iff (x) : (fun x ↦ x ∈ affineSpan R (M ×ˢ N)) x ↔
      (fun x ↦ (x.1 ∈ affineSpan R M) ∧ (x.2 ∈ affineSpan R N)) (Homeomorph.refl (α × β) x) := by
    simp; repeat rw [← AffineSubspace.mem_coe]
    rw [affineSpan_of_product_space, Set.mem_prod]

  let eqv1 := Homeomorph.subtype (p := (fun x ↦ x ∈ affineSpan R (M ×ˢ N)))
    (q := (fun x ↦ (x.1 ∈ affineSpan R M) ∧ (x.2 ∈ affineSpan R N))) (X := α × β) (Y := α × β)
    (Homeomorph.refl (α × β)) affSpan_iff
  let eqv2 : { x : α × β // x.1 ∈ affineSpan R M ∧ x.2 ∈ affineSpan R N } ≃ₜ
    { x : α // x ∈ affineSpan R M } × { y : β // y ∈ affineSpan R N } := Homeomorph.subtypeProd
  let eqv : subtype ≃ₜ subtypeM × subtypeN := eqv1.trans eqv2

  /- Homeomorph Equation -/

  have eqv1_eq (x) : eqv1.invFun x = ⟨(Homeomorph.refl (α × β)).toEquiv.symm x,
      by simp; apply (affSpan_iff x).mpr; simp; exact And.intro x.property.1 x.property.2⟩ := by
    apply Subtype.coe_eq_of_eq_mk
    simp; unfold eqv1
    apply Homeomorph.subtype_symm_apply_coe
  have eqv2_eq (x) : eqv2.invFun x = ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩ := rfl

  /- Calculation -/

  have preimage_phi'_eq: phi' ⁻¹' (M ×ˢ N) = eqv.symm '' {a : subtypeM | a.val ∈ M} ×ˢ
      {b : subtypeN | b.val ∈ N} := by
    calc
      _ = {x : subtype | x.val ∈ (M ×ˢ N)} := rfl
      _ = eqv.symm '' {a : subtypeM | ↑a ∈ M} ×ˢ {b : subtypeN | ↑b ∈ N} := by
        apply Eq.symm
        apply Set.BijOn.image_eq
        apply Equiv.bijOn
        intro x
        change eqv1.invFun (eqv2.invFun x) ∈ {x : subtype | ↑x ∈ M ×ˢ N} ↔
          x ∈ {a : subtypeM | ↑a ∈ M} ×ˢ {b : subtypeN| ↑b ∈ N}
        rw [eqv2_eq x, eqv1_eq]
        simp
        rfl


  change phi' '' interior (phi' ⁻¹' (M ×ˢ N)) = (phiM' '' interior (phiM' ⁻¹' M)) ×ˢ
    (phiN' '' interior (phiN' ⁻¹' N))

  rw [preimage_phi'_eq, ← Homeomorph.image_interior, interior_prod_eq]

  change _ = (phiM' '' interior {x : subtypeM | x.val ∈ M})
    ×ˢ (phiN' '' interior {x : subtypeN | x.val ∈ N})

  rw [prod_image_image_eq, image_image]
  apply image_congr
  intro x _
  change phi' (eqv1.invFun (eqv2.invFun x)) = _
  rw [eqv1_eq, eqv2_eq]; simp; rfl

end

section Thm_6_1

variable (𝕜) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul 𝕜 V] [ContinuousSub V] [ContinuousAdd V]

/-!
Instance. Constant scalar multiplication on the direction space is continuous.
Purpose: equips `(affineSpan s).direction` with `ContinuousConstSMul`.
-/
instance continuous_smul_affinespan_direction {s : Set V} :
  ContinuousConstSMul 𝕜 (affineSpan 𝕜 s).direction where
  continuous_const_smul := by
    intro c
    let f := fun x : ↥(affineSpan 𝕜 s).direction ↦ c • x.1
    have : Continuous f :=
      Continuous.comp' (continuous_const_smul c) continuous_subtype_val
    exact continuous_induced_rng.mpr this

/-
Theorem 6.1.
Let C be a convex set in ℝⁿ. Let x ∈ ri C and y ∈ cl C.
Then (1 - λ)x + λy ∈ ri C (and hence in particular ∈ C) for 0 ≤ λ < 1.
Purpose: stability of the relative interior under convex interpolation with a boundary point.
-/
theorem openSegment_sub_intrinsicInterior {s : Set V} (hsc : Convex 𝕜 s) {x y : V}
    (hx : x ∈ intrinsicInterior 𝕜 s) (hy : y ∈ intrinsicClosure 𝕜 s) :
    openSegment 𝕜 x y ⊆ intrinsicInterior 𝕜 s := by
  -- handle the empty-set case explicitly
  by_cases hs : s.Nonempty
  · rw [intrinsicInterior_equiv_pre 𝕜 hs] at *
    rw [intrinsicClosure_equiv_pre 𝕜 hs] at hy
    let h := affSpanCoerce_pre 𝕜  hs
    let g := Function.invFun h
    -- left inverse on images
    have hgu (u) : g '' (h '' u) = u := pre_inv_self_eq_id 𝕜 hs u
    -- pull back membership to the direction space
    have hx' : g x ∈ interior (h ⁻¹' s) := by
      rw [← hgu (interior (h ⁻¹' s))]
      exact mem_image_of_mem g hx
    have hy' : g y ∈ closure (h ⁻¹' s) := by
      rw [← hgu (closure (h ⁻¹' s))]
      exact mem_image_of_mem g hy
    -- push forward endpoints
    have hgx : h (g x) = x :=
      inv_eq_self 𝕜 hs (mem_range_of_mem_image _ _ hx)
    have hgy : h (g y) = y :=
      inv_eq_self 𝕜 hs (mem_range_of_mem_image _ _ hy)
    change openSegment 𝕜 x y ⊆ h '' interior (h ⁻¹' s)
    -- map open segment through `h`
    have hop : h '' (openSegment 𝕜 (g x) (g y)) = openSegment 𝕜 (h (g x)) (h (g y)) := by
      apply image_openSegment 𝕜 _ (g x) (g y)
    rw [← hgx, ← hgy, ← hop]
    apply image_mono
    -- apply convex result in the preimage space
    exact Convex.openSegment_interior_closure_subset_interior (Convex.affine_preimage _ hsc) hx' hy'
  -- if `s = ∅`, the goal is trivial
  simp [not_nonempty_iff_eq_empty.mp hs] at *

end Thm_6_1

section Thm_6_2_pre

variable (𝕜) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul 𝕜 V] [ContinuousSub V] [ContinuousAdd V] {s : Set V}

/-
Theorem 6.2 (first part).
If s is convex, then its intrinsic interior is also convex.
Purpose: convexity is preserved when passing to the relative interior.
-/
theorem convex_intrinsicInterior (hsc : Convex 𝕜 s) :
    Convex 𝕜 (intrinsicInterior 𝕜 s) := by
  by_cases hs : s.Nonempty
  · rw [intrinsicInterior_equiv_pre 𝕜 hs]
    apply Convex.affine_image _ <| Convex.interior (Convex.affine_preimage _ hsc)
  have hs : s = ∅ := not_nonempty_iff_eq_empty.mp hs
  simpa [hs] using convex_empty

/-
Theorem 6.2 (first part).
If s is convex, then its intrinsic closure is also convex.
Purpose: convexity is preserved when taking the relative closure.
-/
omit [IsStrictOrderedRing 𝕜] in
theorem convex_intrinsicClosure (hsc : Convex 𝕜 s) :
    Convex 𝕜 (intrinsicClosure 𝕜 s) := by
  by_cases hs : s.Nonempty
  · rw [intrinsicClosure_equiv_pre 𝕜 hs]
    apply Convex.affine_image _ <| Convex.closure (Convex.affine_preimage _ hsc)
  have hs : s = ∅ := not_nonempty_iff_eq_empty.mp hs
  simpa [hs] using convex_empty

end Thm_6_2_pre

section Thm_6_2

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set V}

/-
Immediate specialization: convexity of intrinsic interior in ℝ-vector spaces.
Purpose: rephrases convex_intrinsicInterior for real normed spaces.
-/
theorem convex_intrinsicInterior' (hsc : Convex ℝ s) :
    Convex ℝ (intrinsicInterior ℝ s) :=
  convex_intrinsicInterior ℝ hsc

/-
Auxiliary lemma.
In finite-dimensional ℝ-spaces, the affine span of s is contained
in the affine span of the intrinsic interior of s.
Purpose: shows intrinsic interior is large enough to generate the same affine hull.
-/
lemma affineSpan_le_intrinsicInterior [FiniteDimensional ℝ V] (hsc : Convex ℝ s) :
    affineSpan ℝ s ≤ (affineSpan ℝ (intrinsicInterior ℝ s)) := by
  by_cases hs : s.Nonempty
  · rw [intrinsicInterior_equiv_pre ℝ hs]
    let h := affSpanCoerce_pre ℝ hs
    change affineSpan ℝ s ≤ affineSpan ℝ (h '' interior (h ⁻¹' s))
    rw [← AffineSubspace.map_span]
    have : (interior (⇑h ⁻¹' s)).Nonempty :=
      image_nonempty.mp (intrinsicInterior_equiv_pre ℝ hs ▸
        Set.Nonempty.intrinsicInterior hsc hs)
    have : (affineSpan ℝ (interior (⇑h ⁻¹' s))) = ⊤ :=
      IsOpen.affineSpan_eq_top isOpen_interior this
    simp [this]
    refine affineSpan_le.mpr ?_
    simp only [coe_map, top_coe, image_univ]
    apply sub_range
  simp [not_nonempty_iff_eq_empty.mp hs]

/-
Theorem.
The intrinsic interior of a set s is always contained in its affine span.
Purpose: the relative interior cannot leave the affine hull of the original set.
-/
theorem intrinsicInterior_subset_affineSpan {𝕜 : Type*} {V : Type*} {P : Type*} [Ring 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P] {s : Set P} :
    intrinsicInterior 𝕜 s ⊆ affineSpan 𝕜 s :=
  affineSpan_le.mp <| affineSpan_mono 𝕜 intrinsicInterior_subset

/-
Theorem 6.2 (second part).
In finite-dimensional ℝ-spaces, the affine span of the intrinsic interior
of a convex set s equals the affine span of s.
Purpose: intrinsic interior and closure share the same affine hull and hence dimension as s.
-/
theorem affineSpan_intrinsicInterior [FiniteDimensional ℝ V] (hsc : Convex ℝ s) :
    affineSpan ℝ (intrinsicInterior ℝ s) = affineSpan ℝ s :=
  (affineSpan_le.2 intrinsicInterior_subset_affineSpan).antisymm <|
  affineSpan_le_intrinsicInterior hsc

/-
Theorem 6.2 (second part).
In finite-dimensional ℝ-spaces, the affine span of the closure
of a set s equals the affine span of s.
Purpose: intrinsic interior and closure share the same affine hull and hence dimension as s.
-/
#check affineSpan_intrinsicClosure

theorem affineSpan_Closure [FiniteDimensional ℝ V] :
    affineSpan ℝ (closure s) = affineSpan ℝ s :=
  intrinsicClosure_eq_closure ℝ s ▸ affineSpan_intrinsicClosure s

/-
Theorem.
In finite-dimensional ℝ-spaces, the intrinsic interior of the intrinsic interior
of a convex set s is equal to the intrinsic interior itself.
Purpose: relative interior is idempotent under iteration.
-/
theorem intrinsicInterior_intrinsicInterior [FiniteDimensional ℝ V] (hsc : Convex ℝ s) :
    intrinsicInterior ℝ (intrinsicInterior ℝ s) = intrinsicInterior ℝ s := by
  apply intrinsicInterior_subset.antisymm
  nth_rw 1 [intrinsicInterior]
  rw [intrinsicInterior, image_subset_iff]
  rw [affineSpan_intrinsicInterior hsc]
  rw [Function.Injective.preimage_image Subtype.val_injective]
  simp [intrinsicInterior]

/-
Theorem.
In finite-dimensional ℝ-spaces, the closure of closure of a set s is equal to the closure itself.
Purpose: closure is idempotent under iteration.
-/
#check closure_closure

end Thm_6_2

section Thm_6_4
/-
Let s be a non-empty convex subset. Then z ∈ ri s (intrinsic interior of C)
if and only if for every x ∈ s, there exists μ > 1 such that (1 - μ) • x + μ • z ∈ s.
-/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set V}

/-
Theorem:
If x lies in the interior of s,
then moving from x in any direction with small radius remains inside s.
-/
theorem prolongation_of_interior (h : x ∈ interior s) :
    ∀ d , ∃ r > (0 : ℝ), (x + r • d) ∈ s := by
  intro d
  by_cases hd : d = 0
  · use 1; simp [hd]
    exact interior_subset h
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff] at h
  rcases h with ⟨t, ht, hts1, hts2⟩
  rw [Metric.isOpen_iff] at hts1
  obtain ⟨ε, hε, hε1⟩ := hts1 x hts2
  have dnorm : ‖d‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hd
  use ε / (2 * ‖d‖); constructor
  · positivity
  have : x + (ε / (2 * ‖d‖)) • d ∈  Metric.ball x ε := by
    refine add_mem_ball_iff_norm.mpr ?_
    rw [norm_smul]; simp; rw [abs_of_nonneg (a := ε) (by linarith)]
    rw [div_mul, ←mul_div, div_self dnorm]
    linarith
  exact ht (hε1 this)

/-
Theorem:
If z ∈ interior s,
then for each x ∈ s there exists μ > 1 such that (1 - μ) • x + μ • z ∈ s.
-/
theorem prolongation_of_interior' (h : z ∈ interior s) :
    ∀ x, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ s := by
  intro x
  have ⟨r, hr⟩:= prolongation_of_interior h (z - x)
  use r + 1
  simp
  constructor
  · exact hr.1
  have : -(r • x) + (r + 1) • z = z + r • (z - x) := by
    rw [add_smul, smul_sub, add_sub, neg_add_eq_iff_eq_add,
      add_sub_cancel, add_comm, one_smul]
  simpa [this] using hr.2

/-
Theorem 6.4 (forward direction):
If z ∈ ri(s), then for every x ∈ s there exists μ > 1
such that (1 - μ) • x + μ • z ∈ s.
-/
lemma intrinsicInterior_forall_exist_of_intrinsicInterior {z : V}
    (hs : s.Nonempty) (hz : z ∈ intrinsicInterior ℝ s) :
    ∀ x ∈ s, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ s := by
  intro x hx
  rw [intrinsicInterior_equiv_pre ℝ hs] at hz
  let h := affSpanCoerce_pre ℝ hs
  let g := Function.invFun h

  have hgu (u) : g '' (h '' u) = u :=  Function.LeftInverse.image_image
    (Function.leftInverse_invFun <| affSpanCoerce_pre_Injective ℝ hs) u

  have hx' : g z ∈ interior (h ⁻¹' s) := by
    rw [← hgu (interior (h ⁻¹' s))]
    exact mem_image_of_mem g hz

  have hgx : h (g x) = x := inv_eq_self ℝ hs <| sub_range ℝ hs hx

  have hgz : h (g z) = z := inv_eq_self ℝ hs <| mem_range_of_mem_image _ _ hz

  have ⟨μ ,hu1, hu⟩:= prolongation_of_interior' hx' (g x)
  use μ ,hu1
  have : h ((1 - μ) • g x + μ • g z) ∈ h '' (⇑h ⁻¹' s) := mem_image_of_mem _ hu
  rwa [Convex.combo_affine_apply (by simp), hgx, hgz, ← pre_eq_image_preimage] at this

lemma intrinsicInterior_of_intrinsicClosure_of_intrinsicInterior
    (hsc : Convex ℝ s) (hx : x ∈ intrinsicInterior ℝ s) {μ : ℝ} (hμ1 : μ > 1)
    (hu : (1 - μ) • x + μ • z ∈ intrinsicClosure ℝ s) :
    z ∈ intrinsicInterior ℝ s := by
  let y := (1 - μ) • x + μ • z

  let t := 1 / μ
  have hz : z = (1 - t) • x + t • y := by
    simp [y, t, ← add_assoc, sub_smul, sub_smul, smul_sub, smul_smul]
    rw [inv_mul_cancel₀ (by linarith)]; simp
  apply openSegment_sub_intrinsicInterior ℝ hsc hx hu
  rw [openSegment_eq_image]
  nth_rw 2 [hz]
  apply mem_image_of_mem _ (mem_Ioo.mpr ?_)
  simpa [t] using ⟨by linarith, inv_lt_one_of_one_lt₀ hμ1⟩

lemma in_intrinsicInterior_of_intrinsicInterior
    (hsc : Convex ℝ s) (hx : x ∈ intrinsicInterior ℝ s) {μ : ℝ} (hμ1 : μ > 1)
    (hu : (1 - μ) • x + μ • z ∈ s) :
    z ∈ intrinsicInterior ℝ s := by
  apply intrinsicInterior_of_intrinsicClosure_of_intrinsicInterior hsc hx hμ1
  apply subset_intrinsicClosure hu

/-
Theorem 6.4 (converse direction):
If for every x ∈ s there exists μ > 1 with (1 - μ) • x + μ • z ∈ s,
then z belongs to ri(s).
-/
lemma intrinsicInterior_of_forall_exist
    {z : V} (hsc : Convex ℝ s) (hn : (intrinsicInterior ℝ s).Nonempty)
    (h : ∀ x ∈ s, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ s) :
    z ∈ intrinsicInterior ℝ s := by
  have ⟨x, hx⟩ : ∃ x, x ∈ intrinsicInterior ℝ s := hn
  have ⟨μ , hμ1, hu⟩:= h x (intrinsicInterior_subset hx)
  exact in_intrinsicInterior_of_intrinsicInterior hsc hx hμ1 hu

/-
Theorem 6.4 (equivalence form).
A point z lies in ri(s) if and only if for every x ∈ s
there exists μ > 1 such that (1 - μ) • x + μ • z ∈ s.
Purpose: this provides an equivalence condition for the intrinsic interior of a convex set s.
-/
theorem intrinsicInterior_iff
    {z : V} (hs : Convex ℝ s) (hn : (intrinsicInterior ℝ s).Nonempty) :
    z ∈ intrinsicInterior ℝ s ↔ ∀ x ∈ s, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ s := by
  constructor
  · exact fun a x a_1 ↦ intrinsicInterior_forall_exist_of_intrinsicInterior
      (nonempty_of_mem a_1) a x a_1
  exact fun a ↦ intrinsicInterior_of_forall_exist hs hn a

/-
Match the definition of intrinsic interior in books.
-/
theorem intrinsicInterior_iff' {x : V} : x ∈ intrinsicInterior ℝ s ↔
    x ∈ affineSpan ℝ s ∧ ∃ ε > 0, ∀ y ∈ affineSpan ℝ s, dist y x < ε → y ∈ s := by
  simp_rw [mem_intrinsicInterior, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  simp; constructor
  · intro ⟨hx, ε, hε, h⟩
    exact ⟨hx, ε, hε, fun y hy hxy => @h ⟨y, hy⟩ (Metric.mem_ball.1 hxy)⟩
  · intro ⟨hx, ε, hε, h⟩
    exact ⟨hx, ε, hε, fun y hy => h y y.2 (Metric.mem_ball.1 hy)⟩

/-
If the affine span of s is the whole space,
then the intrinsic interior of s equals the topological interior of s.
-/
theorem interior_eq_intrinsicInterior_of_affineSpan_eq_top
    (h : affineSpan ℝ s = ⊤) : interior s = intrinsicInterior ℝ s := by
  ext x
  rw [intrinsicInterior_iff', h, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  simp
  congr!

/-
If the affine span of s is not the whole space,
then the interior of s is empty.
-/
theorem interior_eq_bot_of_affineSpan_ne_top
    (htop : affineSpan ℝ s ≠ ⊤) : interior s = ⊥ := by
  contrapose! htop
  rw [bot_eq_empty, ←nonempty_iff_ne_empty] at htop
  rcases htop with ⟨x, hx⟩
  ext y; simp
  rw [←vsub_vadd y x]
  apply AffineSubspace.vadd_mem_of_mem_direction _ (mem_affineSpan ℝ (interior_subset hx))
  rw [direction_affineSpan]
  let v := y -ᵥ x
  obtain ⟨r, hr, hxr⟩ := prolongation_of_interior hx v
  have hdiff : (x + r • v) -ᵥ x ∈ vectorSpan ℝ s := by
    have hxA : x ∈ affineSpan ℝ s := mem_affineSpan ℝ (interior_subset hx)
    have hxrA : x + r • v ∈ affineSpan ℝ s := mem_affineSpan ℝ hxr
    simpa [vsub_eq_sub] using
      vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hxrA hxA
  simp at hdiff
  have := (vectorSpan ℝ s).smul_mem r⁻¹ hdiff
  rwa [inv_smul_smul₀ (ne_of_gt hr)] at this


/-
Corollary 6.4.1 part 1:
Let s be a non-empty convex subset of V. If the affine span of s is the whole space V,
then z ∈ int s ↔ ∀ y, ∃ ε > 0, z + ε • y ∈ s.
-/
theorem mem_interior_iff_forall_exists_pos_add_smul_mem_of_affineSpan_eq_top {z : V}
    (hs : Convex ℝ s) (htop : affineSpan ℝ s = ⊤)
    (hn : (intrinsicInterior ℝ s).Nonempty) :
    z ∈ interior s ↔ ∀ y, ∃ ε > (0 : ℝ), z + ε • y ∈ s := by
  constructor
  · intro h y
    apply prolongation_of_interior h
  · intro h
    rw [interior_eq_intrinsicInterior_of_affineSpan_eq_top htop]
    apply intrinsicInterior_of_forall_exist hs hn
    intro x hx
    rcases h (z -ᵥ x) with ⟨ε, hε, hh⟩
    use 1 + ε, by simp [hε]
    convert hh using 1
    simp
    rw [add_smul, one_smul, smul_sub, add_comm]
    rw [← @SubNegMonoid.sub_eq_add_neg, add_sub]

/-
Corollary 6.4.1 part 2:
Let s be a convex subset of V. If the affine span of s is not the whole space V,
then z ∈ int s ↔ ∀ y, ∃ ε > 0, z + ε • y ∈ s.
-/
theorem mem_interior_iff_forall_exists_pos_add_smul_mem_of_affineSpan_ne_top {z : V}
    (htop : affineSpan ℝ s ≠ ⊤) : z ∈ interior s ↔ ∀ y, ∃ ε > (0 : ℝ), z + ε • y ∈ s := by
  rw [interior_eq_bot_of_affineSpan_ne_top htop]
  simp
  by_cases hsz : z ∈ affineSpan ℝ s
  · have : ∃ x, x ∉ affineSpan ℝ s := by
      have : (affineSpan ℝ s : Set V) ≠ Set.univ := by
        contrapose! htop
        simp [affineSpan] at htop
        rw [←htop]
        congr!
      apply (ne_univ_iff_exists_notMem _).1 this
    rcases this with ⟨x, hx⟩
    have hy : x -ᵥ z ∉ vectorSpan ℝ s := by
      contrapose! hx with hy
      rw [←direction_affineSpan] at hy
      simpa using AffineSubspace.vadd_mem_of_mem_direction hy hsz
    use x -ᵥ z
    intro ε hε
    contrapose! hy
    have := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan (mem_affineSpan ℝ hy) hsz
    simp at this
    have := (vectorSpan ℝ s).smul_mem ε⁻¹ this
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hε), one_smul] at this
  · use 0
    intro ε hε
    simp
    contrapose! hsz
    exact mem_affineSpan ℝ hsz

/-
Corollary 6.4.1 (full version):
Let s be a non-empty convex subset of V. Then z ∈ int s ↔ ∀ y, ∃ ε > 0, z + ε • y ∈ s.
-/
theorem mem_interior_iff_forall_exists_pos_add_smul_mem {z : V}
    (hs : Convex ℝ s) (hn : (intrinsicInterior ℝ s).Nonempty) :
    z ∈ interior s ↔ ∀ y, ∃ ε > (0 : ℝ), z + ε • y ∈ s := by
  by_cases htop : affineSpan ℝ s = ⊤
  · exact mem_interior_iff_forall_exists_pos_add_smul_mem_of_affineSpan_eq_top hs htop hn
  · exact mem_interior_iff_forall_exists_pos_add_smul_mem_of_affineSpan_ne_top htop

end Thm_6_4

section Thm_6_3_pre

variable (𝕜) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [ContinuousSub V] [ContinuousAdd V] {s : Set V}

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [ContinuousSub V] [ContinuousAdd V] in
lemma in_affineSpan_openSegment {x y : V} (h : x ≠ y) :
    x ∈ affineSpan 𝕜 (openSegment 𝕜 x y) := by
  refine (mem_coe ..).mp ?_
  simp [affineSpan, spanPoints]
  simp [vectorSpan]

  let u := midpoint 𝕜 x y

  have hu : u ∈ openSegment 𝕜 x y :=
    mem_openSegment_of_ne_left_right (by simpa [u]) (by simpa [u])
      (midpoint_mem_segment x y)

  let z := midpoint 𝕜 x u

  have seg : segment 𝕜 x u ⊆ segment 𝕜 x y := by
    simpa [u] using  Convex.segment_subset  (convex_segment x y)
      (left_mem_segment 𝕜 x y) (midpoint_mem_segment x y)

  have hz : z ∈ openSegment 𝕜 x y := by
    refine mem_openSegment_of_ne_left_right (by simpa [z, u]) ?_ (seg <| midpoint_mem_segment x u)
    simp [z, u, midpoint_eq_smul_add]
    rw [smul_smul, smul_smul, ← add_assoc, ← add_smul, ← add_neg_eq_iff_eq_add, ← sub_eq_add_neg]
    nth_rw 1 [← one_smul 𝕜 y]
    rw [← sub_smul]
    norm_num
    rw [smul_right_inj (by norm_num)]
    exact h.symm

  let v := z -ᵥ u
  have hv : v ∈ Submodule.span 𝕜 (openSegment 𝕜 x y -ᵥ openSegment 𝕜 x y) :=
    Submodule.subset_span (vsub_mem_vsub hz hu)
  have huz : u + (x - z) ∈ openSegment 𝕜 x y := by
    simp [u, z, midpoint_eq_smul_add]
    rw [smul_smul, smul_smul, ← add_assoc, ← add_smul, ← sub_sub]
    nth_rw 3 [← one_smul 𝕜 x]
    rw [← sub_smul, sub_eq_add_neg, add_add_add_comm, ← add_smul, ← neg_smul, ← add_smul]
    norm_num
    refine mem_openSegment_iff_div.mpr ?_
    use (3 : 𝕜), (1 : 𝕜)
    norm_num

  use u + (x - z), huz, v, hv
  simp [v]
  rw [add_sub, add_sub, ← add_assoc, sub_add]
  simp

lemma intrinsicClosure_openSegment {x y : V} (hn : x ≠ y) :
    y ∈ intrinsicClosure 𝕜 (openSegment 𝕜 x y) := by
  have hs : (openSegment 𝕜 x y).Nonempty := by
    use midpoint 𝕜 x y
    simp [openSegment, midpoint_eq_smul_add]
    use 2⁻¹, ?_, 2⁻¹,?_, ?_
    repeat norm_num
  rw [intrinsicClosure_equiv_pre 𝕜 hs]
  let h := affSpanCoerce_pre 𝕜 hs
  let g := Function.invFun h
  have hgx : h (g x) = x:= by
    apply inv_eq_self 𝕜 hs
    simp
    have b : x -ᵥ Exists.choose hs ∈ (affineSpan 𝕜 (openSegment 𝕜 x y)).direction := by
      refine (vsub_right_mem_direction_iff_mem ?hp x).mpr ?_
      refine mem_affineSpan 𝕜  hs.choose_spec
      exact in_affineSpan_openSegment 𝕜 hn
    use x - Exists.choose hs, b
    symm
    exact (eq_vadd_iff_vsub_eq x _ _).mpr rfl

  have hgy : h (g y) = y := by
    apply inv_eq_self 𝕜 hs
    simp
    have b : y -ᵥ Exists.choose hs ∈ (affineSpan 𝕜 (openSegment 𝕜 x y)).direction := by
      refine (vsub_right_mem_direction_iff_mem ?hp y).mpr ?_
      rw [openSegment_symm]
      exact in_affineSpan_openSegment 𝕜 hn.symm
    use y - Exists.choose hs, b
    symm
    exact (eq_vadd_iff_vsub_eq y _ _).mpr rfl

  have : openSegment 𝕜 x y = h '' (openSegment 𝕜 (g x) (g y)) := by
    simp_rw [image_openSegment 𝕜 _ (g x) (g y), hgx, hgy]

  have : h ⁻¹' openSegment 𝕜 x y = openSegment 𝕜 (g x) (g y) := by
    simp_rw [this]
    apply preimage_image_eq _
    exact affSpanCoerce_pre_Injective 𝕜 hs

  change y ∈ h '' (closure (h ⁻¹' _))

  simp_rw [this]

  apply (image_mono segment_subset_closure_openSegment)
  use (g y), right_mem_segment 𝕜 (g x) (g y), hgy

theorem segment_subset_intrinsicClosure_openSegment {x y : V} :
    segment 𝕜 x y ⊆ intrinsicClosure 𝕜 (openSegment 𝕜 x y) := by
  by_cases hn : x = y
  · simp [hn]
  apply Convex.segment_subset
  · apply convex_intrinsicClosure 𝕜 <| convex_openSegment x y
  · rw [openSegment_symm]
    exact intrinsicClosure_openSegment 𝕜 fun a ↦ hn a.symm
  exact intrinsicClosure_openSegment 𝕜 hn

/-
The intrinsic closure of the interior of a convex set s equals the intrinsic closure of s.
Purpose: shows relative closure and relative interior operations commute for convex sets.
-/
theorem intrinsicClosure_intrinsicInterior (h : Convex 𝕜 s)
      (hc : (intrinsicInterior 𝕜 s).Nonempty) :
    intrinsicClosure 𝕜 (intrinsicInterior 𝕜 s) = intrinsicClosure 𝕜 s := by
  apply Set.Subset.antisymm (intrinsicClosure_mono intrinsicInterior_subset)
  by_cases hs : Set.Nonempty s
  · intro x h2
    apply intrinsicClosure_mono (openSegment_sub_intrinsicInterior 𝕜 h hc.choose_spec h2)
    apply segment_subset_intrinsicClosure_openSegment
    exact right_mem_segment 𝕜 (Exists.choose hc) x
  simp [not_nonempty_iff_eq_empty.1 hs]

end Thm_6_3_pre

section Thm_6_3

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set V}

theorem intrinsicInterior_intrinsicClosure_sub_intrinsicInterior (h : Convex ℝ s)
    (hn : (intrinsicInterior ℝ s).Nonempty) :
    intrinsicInterior ℝ (intrinsicClosure ℝ s) ⊆  intrinsicInterior ℝ s := by
  intro z hz
  rw [intrinsicInterior_iff (convex_intrinsicClosure ℝ h) (nonempty_of_mem hz)] at hz
  have ⟨x, hx⟩ : ∃ x, x ∈ intrinsicInterior ℝ s := hn
  have ⟨μ , hμ1, hu⟩ := hz x (subset_intrinsicClosure <| intrinsicInterior_subset hx)
  exact intrinsicInterior_of_intrinsicClosure_of_intrinsicInterior h hx hμ1 hu

/-
If s is a convex set and the intrinsic interior of s is non-empty,
then the intrinsic interior of the intrinsic closure of s
is exactly equal to the intrinsic interior of s.
-/
theorem intrinsicInterior_intrinsicClosure
    (h : Convex ℝ s) (hc : (intrinsicInterior ℝ s).Nonempty) :
    intrinsicInterior ℝ (intrinsicClosure ℝ s) = intrinsicInterior ℝ s := by
  apply Set.Subset.antisymm
  · exact intrinsicInterior_intrinsicClosure_sub_intrinsicInterior h hc
  exact intrinsicInterior_sub_intrinsicClosure_intrinsicInterior ℝ


/-
Theorem 6.3 (first part).
For convex set s in finite-dimensional ℝ-vector space,
the relative interior of the closure equals the relative interior of s:
  cl(ri(s)) = cl(s).
Purpose: shows closure and relative interior operations commute for convex sets.
-/
theorem closure_intrinsicInterior [FiniteDimensional ℝ V] (h : Convex ℝ s) :
    closure (intrinsicInterior ℝ s) = closure s := by
  by_cases hs : Set.Nonempty s
  · rw [← intrinsicClosure_eq_closure ℝ s, ← intrinsicClosure_eq_closure ℝ _]
    exact intrinsicClosure_intrinsicInterior ℝ h <|
      (intrinsicInterior_nonempty h).mpr hs
  simp [not_nonempty_iff_eq_empty.1 hs]


/-
Theorem 6.3 (second part).
For convex set s in finite-dimensional ℝ-vector space,
the relative interior of the closure equals the relative interior of s:
  ri(cl(s)) = ri(s).
-/
theorem intrinsicInterior_closure [FiniteDimensional ℝ V] (h : Convex ℝ s) :
    intrinsicInterior ℝ (closure s) = intrinsicInterior ℝ s := by
  by_cases hs : s.Nonempty
  · rw [← intrinsicClosure_eq_closure ℝ s]
    exact intrinsicInterior_intrinsicClosure h <|
      (intrinsicInterior_nonempty h).mpr hs
  simp [not_nonempty_iff_eq_empty.mp hs]

/-
Corollary 6.3.1 (TFAE).
For convex sets s and t in finite-dimensional space, the following are equivalent:
1. closure s = closure t
2. ri(s) = ri(t)
3. ri(s) ⊆ t ⊆ cl(s)
-/
theorem intrinsicInterior_tfae [FiniteDimensional ℝ V] (hs : Convex ℝ s) (ht : Convex ℝ t) :
    [closure s = closure t, intrinsicInterior ℝ s = intrinsicInterior ℝ t,
    intrinsicInterior ℝ s ⊆ t ∧ t ⊆ closure s].TFAE :=  by
  tfae_have  1 → 2 := by
    intro x
    rw[← intrinsicInterior_closure hs,x,intrinsicInterior_closure ht]
  tfae_have  2 → 1 := by
    intro x
    rw[← closure_intrinsicInterior ht,←x,closure_intrinsicInterior hs]
  tfae_have  3 → 1 := by
    rintro ⟨a, b⟩
    apply Subset.antisymm ((closure_intrinsicInterior hs) ▸ closure_mono a)
    nth_rw 2 [← closure_closure]
    exact closure_mono b
  tfae_have  2 → 3 := by
    intro x
    constructor
    rw [x]
    exact intrinsicInterior_subset
    have re := tfae_2_to_1
    apply re at x
    simpa [x] using subset_closure
  tfae_finish

/-
Corollary 6.3.2.
For convex set s and open set t in finite-dimensional space,
if t ∩ cl(s) ≠ ∅, then t ∩ ri(s) ≠ ∅.
-/
theorem IsOpen.inter_intrinsicInterior_of_inter_closure [FiniteDimensional ℝ V]
    (hs : Convex ℝ s) (ht : IsOpen t) (hn : (t ∩ closure s).Nonempty) :
    (t ∩ intrinsicInterior ℝ s).Nonempty := by
  rw [←closure_intrinsicInterior hs] at hn
  rcases hn with ⟨x, hx1, hx2⟩
  rw [mem_closure_iff_nhds] at hx2
  exact hx2 t (ht.mem_nhds hx1)


end Thm_6_3

noncomputable section

variable {E} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Intrinsic interior of the whole space is the whole space.
-/
@[simp]
lemma intrinsicInterior_univ : intrinsicInterior ℝ univ = (univ : Set E) := by
  simp [intrinsicInterior]

/-
Instrinsic interior of an affine subspace is itself.
-/
lemma intrinsicInterior_affineSubspace_eq_self (M : AffineSubspace ℝ E) :
    intrinsicInterior ℝ M = (M : Set E) :=  by
  have : interior ((fun x ↦ (x : E) : ↥M → E) ⁻¹' (M : Set E)) = univ := by simp
  rw [intrinsicInterior, affineSpan_coe]; simp [this]

/-
Instrinsic interior of a submodule is itself.
-/
lemma intrinsicInterior_submodule_eq_self (M : Submodule ℝ E) :
    intrinsicInterior ℝ M = (M : Set E) :=
    intrinsicInterior_affineSubspace_eq_self M.toAffineSubspace

/-
Closure of a finite dimensional affine subspace is itself.
-/
lemma closure_affineSubspace_eq_self [FiniteDimensional ℝ E] (M : AffineSubspace ℝ E) :
    closure M = (M : Set E) := (closed_of_finiteDimensional M).closure_eq

/-
Closure of a finite dimensional submodule is itself.
-/
lemma closure_submodule_eq_self [FiniteDimensional ℝ E] (M : Submodule ℝ E) :
    closure M = (M : Set E) := closure_affineSubspace_eq_self M.toAffineSubspace

end

section Thm_6_5

/-
If {C_i}_I is convex sets，and ⋂ i, (intrinsicInterior ℝ (C_i)) ≠ ∅
1. cl(⋂ C_i) = ⋂ cl(C_i)
2. If I is finite，then ri(⋂ C_i) = ⋂ ri(C_i)
-/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Sort*} {s : ι → Set V}

/-
Lemma.
For a family of convex sets {s i}, if their intrinsic interiors have a common point,
then ⋂ cl(s i) ⊆ cl(⋂ s i).
-/
lemma iIntersection_closure_sub_closure_iIntersection
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ∃ x, ∀ i, x ∈ intrinsicInterior ℝ (s i)) :
    ⋂ i, closure (s i) ⊆  closure (⋂ i, s i) := by
  obtain ⟨x, hx⟩ := hinter
  have h₀ : closure (⋂ i, intrinsicInterior ℝ (s i)) ⊆ closure (⋂ i, s i) :=
    closure_mono (iInter_mono'' (fun i => intrinsicInterior_subset))
  have h₁ : ⋂ i, closure (s i) ⊆  closure ( ⋂ i, intrinsicInterior ℝ (s i) ) := by
    rintro y hy; rw[Set.mem_iInter] at hy
    have h₂ : openSegment ℝ x y ⊆ ⋂ i, intrinsicInterior ℝ (s i) := by
      simp
      intro i
      apply openSegment_sub_intrinsicInterior ℝ (h i) (hx i) --(hy i)
      rw [intrinsicClosure_eq_closure ℝ _]
      exact hy i
    apply closure_mono h₂
    apply segment_subset_closure_openSegment
    exact right_mem_segment ℝ x y
  exact fun _ a_1 => h₀ (h₁ a_1)

omit [FiniteDimensional ℝ V] in
lemma iIntersection_closure_sub_closure_iIntersection''
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ∃ x, ∀ i, x ∈ intrinsicInterior ℝ (s i)) :
    ⋂ i, intrinsicClosure ℝ (s i) ⊆  intrinsicClosure ℝ (⋂ i, s i) := by
  obtain ⟨x, hx⟩ := hinter
  have h₀ : intrinsicClosure ℝ (⋂ i, intrinsicInterior ℝ (s i)) ⊆ intrinsicClosure ℝ (⋂ i, s i) :=
    intrinsicClosure_mono (iInter_mono'' (fun i => intrinsicInterior_subset))
  have h₁ : ⋂ i, intrinsicClosure ℝ (s i) ⊆
      intrinsicClosure ℝ (⋂ i, intrinsicInterior ℝ (s i)) := by
    rintro y hy; rw[Set.mem_iInter] at hy
    have h₂ : openSegment ℝ x y ⊆ ⋂ i, intrinsicInterior ℝ (s i) := by
      simp
      intro i
      apply openSegment_sub_intrinsicInterior ℝ (h i) (hx i) --(hy i)
      exact hy i
    apply intrinsicClosure_mono h₂
    by_cases h: x = y
    · rw [h]; simp
    refine intrinsicClosure_openSegment ℝ h
  exact fun _ a_1 => h₀ (h₁ a_1)

/-
Lemma.
For any family of sets {s i}, closure(⋂ s i) ⊆ ⋂ closure(s i).
This is the standard closure monotonicity result.
-/
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
lemma closure_iIntersection_sub_iIntersection_closure :
  closure (⋂ i, s i) ⊆ ⋂ i, closure (s i) := by
  apply closure_minimal
  · intro x hx
    rw [mem_iInter] at hx
    exact mem_iInter.mpr <| fun i => subset_closure (hx i)
  exact isClosed_iInter <| fun i ↦ isClosed_closure

omit [FiniteDimensional ℝ V] in
lemma closure_iIntersection_sub_iIntersection_closure' :
  intrinsicClosure ℝ (⋂ i, s i) ⊆ ⋂ i, intrinsicClosure ℝ (s i) := by
  intro x hx
  rw [@mem_iInter]; intro i
  have : ⋂ i, s i ⊆ s i := iInter_subset_of_subset i fun ⦃a⦄ a ↦ a
  apply intrinsicClosure_mono this
  exact hx

/-
Theorem 6.5 (first part).
If {s i} are convex and their intrinsic interiors intersect,
then ⋂ cl(s i) = cl(⋂ s i).
Equivalently, closure and intersection commute under this condition.
-/
theorem iInter_closure_eq_closure_iInter
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ∃ x, ∀ i, x ∈ intrinsicInterior ℝ (s i)) :
    ⋂ i, closure (s i) = closure (⋂ i, s i) := by
  apply Subset.antisymm
  · exact iIntersection_closure_sub_closure_iIntersection h hinter
  exact closure_iIntersection_sub_iIntersection_closure

/-
Theorem 6.5 (first part) for intrinsicClosure.
If {s i} are convex and their intrinsic interiors intersect,
then ⋂ cl(s i) = cl(⋂ s i).
Equivalently, closure and intersection commute under this condition.
-/
omit [FiniteDimensional ℝ V] in
theorem iInter_intrinsicClosure_eq_intrinsicClosure_iInter
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ∃ x, ∀ i, x ∈ intrinsicInterior ℝ (s i)) :
    ⋂ i, intrinsicClosure ℝ (s i) = intrinsicClosure ℝ (⋂ i, s i) := by
  apply Subset.antisymm
  · exact iIntersection_closure_sub_closure_iIntersection'' h hinter
  exact closure_iIntersection_sub_iIntersection_closure'

/-
Lemma.
For two sets a, b encoded as a function (Fin 2) → Set V,
their intersection equals a ∩ b. (Technical lemma for reduction.)
-/
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
lemma Fin_two_inter {a b : Set V} {s : (Fin 2) → Set V}
    (hs0 : s 0 = a) (hs1 : s 1 = b) :
    (⋂ i, s i) = a ∩ b := by
  ext x
  constructor
  · intro hx
    simp at hx
    have h1 : x ∈ a := Eq.mp (congrArg (fun _a ↦ x ∈ _a) hs0) (hx 0)
    have h2 : x ∈ b := Eq.mp (congrArg (fun _a ↦ x ∈ _a) hs1) (hx 1)
    exact mem_inter h1 h2
  intro hx
  simp; intro i
  by_cases h : i = 0
  · rw [h, hs0]; exact hx.1
  rw [Fin.eq_one_of_ne_zero i h, hs1]; exact hx.2

/-
Special case for Theorem 6.5 (first part).
For two convex sets a, b with intersecting intrinsic interiors,
closure(a) ∩ closure(b) = closure(a ∩ b).
This is the two-set case of the general intersection-closure result.
-/
theorem iIntersection_closure_eq_intrinsicInterior_closure' {a b : Set V}
    (ha : Convex ℝ a) (hb : Convex ℝ b)
    (hinter : ∃ x, x ∈ (intrinsicInterior ℝ a) ∩ (intrinsicInterior ℝ b)) :
    closure a ∩ closure b = closure (a ∩ b) := by
  let s : (Fin 2) → Set V := fun i ↦ if i = 0 then a else b
  suffices ⋂ i, closure (s i) = closure (⋂ i, s i) by
    have hs1 : (⋂ i, s i) = a ∩ b := by
      apply Fin_two_inter (by simp [s]) (by simp [s])
    have hs2 :  ⋂ i, closure (s i) = closure a ∩ closure b := by
      apply Fin_two_inter (by simp [s]) (by simp [s])
    rwa [hs1, hs2] at this
  apply iInter_closure_eq_closure_iInter
  · intro i
    by_cases h : i = 0
    · rw [h]; simp [s]; exact ha
    rw [Fin.eq_one_of_ne_zero i h]; simp [s]; exact hb
  rcases hinter with ⟨x, hx⟩; use x
  intro i
  by_cases h : i = 0
  · rw [h]; simp only [s]; exact mem_of_mem_inter_left hx
  rw [Fin.eq_one_of_ne_zero i h]; simp only [s]; exact mem_of_mem_inter_right hx

/-
Lemma.
For convex sets s, t, closure(s) = closure(t) ↔ ri(s) ⊆ t ⊆ cl(s).
Gives a characterization of equality of closures in terms of relative interiors.
-/
lemma intrinsicInterior_tfae13 {s t : Set V} (hs : Convex ℝ s) (ht : Convex ℝ t) :
    closure s = closure t ↔ intrinsicInterior ℝ s ⊆ t ∧ t ⊆ closure s := by
   apply (intrinsicInterior_tfae hs ht) <;> simp

/-
Lemma.
If two convex sets have equal closures,
then the intrinsic interior of the first is contained in the second.
-/
lemma from_closure_to_interior_subset {s t : Set V} (hs : Convex ℝ s) (ht : Convex ℝ t)
  (h_closure_eq : closure s = closure t) : intrinsicInterior ℝ s ⊆ t :=
    ((intrinsicInterior_tfae13 hs ht).1 h_closure_eq).1

/-
Lemma.
If ⋂ s i ≠ ∅, then there exists a point belonging to all s i.
This extracts a witness from the nonemptiness of the intersection.
-/
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
lemma exist_of_inter_ne_empty (hinter : ⋂ i, (s i) ≠ ∅) :
    ∃ x, ∀ (i : ι), x ∈ s i :=
  nonempty_iInter.mp <| nonempty_iff_ne_empty.mpr hinter

/-
Lemma.
If convex sets {s i} have nonempty intersection of intrinsic interiors,
then ri(⋂ s i) ⊆ ⋂ ri(s i).
This gives one inclusion for relative interiors.
-/
lemma intrinsicInterior_iIntersection_sub_iIntersection_intrinsicInterior
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ⋂ i, (intrinsicInterior ℝ (s i)) ≠ ∅) :
  intrinsicInterior ℝ (⋂ i, s i) ⊆ ⋂ i, intrinsicInterior ℝ (s i):= by
  have  hr : ∀ (i : ι), Convex ℝ (intrinsicInterior ℝ (s i)) :=
    fun i => convex_intrinsicInterior ℝ (h i)
  have ri_inter :  ⋂ i, intrinsicInterior ℝ (intrinsicInterior ℝ (s i)) ≠ ∅ := by
    rw [iInter_congr fun i ↦ intrinsicInterior_intrinsicInterior (h i)]; exact hinter
  have ht  :⋂ i, closure (s i) = closure (⋂ i, s i):=
    iInter_closure_eq_closure_iInter h  (exist_of_inter_ne_empty hinter)
  have hrt : ⋂ i, closure (intrinsicInterior ℝ (s i) )= closure (⋂ i,intrinsicInterior ℝ (s i)) :=
    iInter_closure_eq_closure_iInter hr (exist_of_inter_ne_empty ri_inter)
  apply from_closure_to_interior_subset (convex_iInter h) (convex_iInter hr)
  rw [ht.symm , hrt.symm]
  rw [iInter_congr fun i ↦ closure_intrinsicInterior (h i)]

/-
Lemma.
For a finite index set I, ⋂ ri(s i) ⊆ ri(⋂ s i).
This is the reverse inclusion in the finite case.
-/
omit [FiniteDimensional ℝ V] in
lemma iIntersection_intrinsicInterior_sub_intrinsicInterior_iIntersection
    [Finite ι] :
    ⋂ i, intrinsicInterior ℝ (s i) ⊆ intrinsicInterior ℝ (⋂ i, s i) := by
  intro x hx
  have xinaff : x ∈ affineSpan ℝ (⋂ i, s i) :=
    mem_affineSpan ℝ <| mem_iInter.2 <| fun i ↦ intrinsicInterior_subset ((mem_iInter.1 hx) i)
  simp only [mem_intrinsicInterior, Subtype.exists, exists_and_right, exists_eq_right]
  let f : (affineSpan ℝ (⋂ i, s i)) → V := Subtype.val
  have inter_sub : ⋂ i, f ⁻¹' (s i) ⊆  (f ⁻¹' ⋂ i, s i) := by
    rw[Set.preimage_iInter]
  simp at hx
  use xinaff
  apply interior_mono
  · apply inter_sub
  rw [interior_iInter_of_finite]
  simp only [mem_iInter]
  intro i
  let g : (affineSpan ℝ (s i)) → V := Subtype.val
  let u : (affineSpan ℝ (⋂ i, s i)) → (affineSpan ℝ (s i)) :=
    fun x => ⟨x, (affineSpan_mono _  <| iInter_subset_of_subset i fun _ a ↦ a) x.2⟩
  let g_u : (affineSpan ℝ (⋂ i, s i)) → V := g ∘ u
  have hug' : f = g_u := by
    simp [g_u, u, g, f]
    exact rfl
  change _ ∈ interior (f ⁻¹' s i)
  rw [hug', preimage_comp]
  apply preimage_interior_subset_interior_preimage
  · apply (Continuous.subtype_mk (Continuous.subtype_val continuous_id'))
  simpa [u] using (hx i).2

/-
Theorem 6.5 (second part).
For a finite family of convex sets with nonempty intersection of relative interiors,
we have ri(⋂ s i) = ⋂ ri(s i).
This establishes equality of relative interiors in the finite case.
-/
theorem iInter_intrinsicInterior_eq_intrinsicInterior_iInter [Finite ι]
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ⋂ i, (intrinsicInterior ℝ (s i)) ≠ ∅) :
    ⋂ i, intrinsicInterior ℝ (s i) = intrinsicInterior ℝ (⋂ i, s i) := by
  apply Subset.antisymm
  · exact iIntersection_intrinsicInterior_sub_intrinsicInterior_iIntersection
  exact intrinsicInterior_iIntersection_sub_iIntersection_intrinsicInterior h hinter

/-
Special case for Theorem 6.5 (second part).
For two convex sets a, b with nonempty intersection of relative interiors,
we have ri (a ∩ b) = (ri a) ∩ (ri b).
This establishes equality of relative interiors in the finite case.
-/
lemma iInter_intrinsicInterior_eq_intrinsicInterior_iInter' {a b : Set V}
    (ha : Convex ℝ a) (hb : Convex ℝ b)
    (hC : (intrinsicInterior ℝ a) ∩ (intrinsicInterior ℝ b) ≠ ∅) :
    (intrinsicInterior ℝ a) ∩ (intrinsicInterior ℝ b) = intrinsicInterior ℝ (a ∩ b) := by
  let Ci : Fin 2 → Set V := fun i ↦ if i = 0 then a else b
  have hCi : ∀ i, Convex ℝ (Ci i) := fun i ↦ by
    by_cases h : i = 0 <;> simp [h, Ci, ha, hb]
  have := iInter_intrinsicInterior_eq_intrinsicInterior_iInter hCi
    (by simp [Fin_two_inter, Ci, hC])
  simpa [Fin_two_inter, Ci] using this

/-
Corollary 6.5.1 (part 1).
For convex sets C and affine set M, if ri(C) ∩ M ≠ ∅,
then ri(C ∩ M) = M ∩ ri(C).
-/
lemma intersection_affineSubspace_intrinsicInterior_eq
    {C : Set V} (hC : Convex ℝ C) {M : AffineSubspace ℝ V}
    (hn : (M : Set V) ∩ intrinsicInterior ℝ C ≠ ∅) :
    intrinsicInterior ℝ (M ∩ C) = (M : Set V) ∩ intrinsicInterior ℝ C := by
  rw [←intrinsicInterior_affineSubspace_eq_self] at hn
  rw [←iInter_intrinsicInterior_eq_intrinsicInterior_iInter' M.convex hC hn]
  rw [intrinsicInterior_affineSubspace_eq_self]

/-
Corollary 6.5.1 (part 2).
For convex sets C and affine set M, if ri(C) ∩ M ≠ ∅,
then cl(C ∩ M) = M ∩ cl(C).
-/
lemma closure_affineSubspace_intrinsicInterior_eq
    {C : Set V} (hC : Convex ℝ C) {M : AffineSubspace ℝ V}
    (hn : (M : Set V) ∩ intrinsicInterior ℝ C ≠ ∅) :
    closure (M ∩ C) = (M : Set V) ∩ closure C := by
  rw [←intrinsicInterior_affineSubspace_eq_self, ←nonempty_iff_ne_empty] at hn
  rw [←iIntersection_closure_eq_intrinsicInterior_closure' M.convex hC hn]
  rw [closure_affineSubspace_eq_self]

/-
Corollary 6.5.2.
For convex sets C1 and C2, if C2 ⊆ cl(C1) and C2 contains a point of ri(C1),
then ri(C2) ⊆ ri(C1).
-/
theorem intrinsicInterior_subset_intrinsicInterior_of_partly_subset_intrinsicFrontier
    {C1 : Set V} (hC1 : Convex ℝ C1) {C2 : Set V} (hC2 : Convex ℝ C2)
    (h1 : C2 ⊆ closure C1) (h2 : ∃ x ∈ C2, x ∈ intrinsicInterior ℝ C1) :
    intrinsicInterior ℝ C2 ⊆ intrinsicInterior ℝ C1 := by
  apply inter_eq_right.1
  have hn : intrinsicInterior ℝ (closure C1) ∩ intrinsicInterior ℝ C2 ≠ ∅ := by
    rw [intrinsicInterior_closure hC1]
    by_contra h
    have : intrinsicInterior ℝ C2 ⊆ intrinsicFrontier ℝ C1 := by
      intro y hy
      rw [←intrinsicClosure_diff_intrinsicInterior, intrinsicClosure_eq_closure]
      use h1 (intrinsicInterior_subset hy)
      intro hy2; apply h ▸ mem_inter hy2 hy
    have : closure C2 ⊆ intrinsicFrontier ℝ C1 := by
      rw [←closure_intrinsicInterior hC2]
      rwa [IsClosed.closure_subset_iff]
      apply isClosed_intrinsicFrontier (closed_of_finiteDimensional _)
    rcases h2 with ⟨x, hx1, hx2⟩
    have h' := this (subset_closure hx1)
    rw [←intrinsicClosure_diff_intrinsicInterior, intrinsicClosure_eq_closure] at h'
    exact h'.2 hx2
  rw [←intrinsicInterior_closure hC1]
  rw [iInter_intrinsicInterior_eq_intrinsicInterior_iInter' (hC1.closure) hC2 hn]
  rw [inter_eq_self_of_subset_right h1]

end Thm_6_5

section Thm_6_6

variable {E F} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-
Theorem 6.6 (first part).
Let C be a convex set in a finite-dimensional real normed space E,
and let A : E → F be a linear map into another finite-dimensional normed space.
Then the relative interior of A(C) equals the image of the relative interior of C.
Purpose: linear maps commute with the relative interior.
-/
theorem linearMap_intrinsicInterior (C : Set E) (A : E →L[ℝ] F) (hC : Convex ℝ C) :
    (intrinsicInterior ℝ (A '' C)) = A '' (intrinsicInterior ℝ C) := by
  by_cases C_nonempty : C.Nonempty
  · apply Subset.antisymm
    · apply from_closure_to_interior_subset
      · exact hC.is_linear_image A.toLinearMap.isLinear
      · exact Convex.is_linear_image
          (convex_intrinsicInterior' hC) (LinearMap.isLinear A.toLinearMap)
      apply Set.Subset.antisymm
      · calc
          _ ⊆ closure (A '' (closure C)) := by gcongr; exact subset_closure
          _ = closure (A '' (closure (intrinsicInterior ℝ C))) := by
            rw [closure_intrinsicInterior hC]
          _ ⊆ closure (closure (A '' (intrinsicInterior ℝ C))) := by
            gcongr; exact image_closure_subset_closure_image A.continuous
          _ = closure (A '' (intrinsicInterior ℝ C)) := closure_closure
      gcongr; exact from_closure_to_interior_subset hC hC rfl
    intro z hz; apply (intrinsicInterior_iff _ _).mpr;
    · intro x hx
      rcases hz with ⟨t, t_mem, t_eq⟩; rcases hx with ⟨s, s_mem, s_eq⟩
      rw [intrinsicInterior_iff hC ⟨t, t_mem⟩] at t_mem
      rcases (t_mem s s_mem) with ⟨μ, hμ1, hμ2⟩
      use μ; constructor
      · exact hμ1
      exact mem_of_eq_of_mem
        (by simp only [map_add, map_smul]; rw [s_eq, t_eq]) (mem_image_of_mem A hμ2)
    · apply Convex.is_linear_image hC  (LinearMap.isLinear A.toLinearMap)
    apply Nonempty.intrinsicInterior (Convex.is_linear_image hC (LinearMap.isLinear A.toLinearMap))
    apply image_nonempty.mpr
    exact C_nonempty
  rw [image_eq_empty.mpr (not_nonempty_iff_eq_empty.mp C_nonempty), intrinsicInterior_empty]
  rw [not_nonempty_iff_eq_empty.mp C_nonempty, intrinsicInterior_empty, @image_empty]


/-
Theorem 6.6 (second part).
Let C be a convex set in a finite-dimensional real normed space E,
and let A : E → F be a linear map into another finite-dimensional normed space.
Then the closure of A(C) contains the image of the closure of C.
Purpose: linear maps preserve closure inclusions.
-/
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem linearMap_closure (C : Set E) (A : E →L[ℝ] F) :
    A '' (closure C) ⊆ closure (A '' C) := image_closure_subset_closure_image A.continuous

/-
Corollary 6.6.1.
-/
theorem intrinsicInterior_of_left_smul_constant {C : Set E} (hC : Convex ℝ C) (a : ℝ) :
    (intrinsicInterior ℝ (a • C)) = a • (intrinsicInterior ℝ C) := by
  let A : E →L[ℝ] E := {
    toFun := fun x ↦ a • x,
    map_add' := by simp [smul_add],
    map_smul' := fun m x ↦ smul_comm a m x,
    cont := continuous_const_smul a
  }
  apply linearMap_intrinsicInterior C A hC

/-
Like intrinsicInterior_iff, but in Finitedimensional real normed spaces,
just assuming C is nonempty.
-/
-- theorem intrinsicInterior_iff' {C : Set E} (hC : Convex ℝ C) (hn : C.Nonempty) :
--     z ∈ intrinsicInterior ℝ C ↔ ∀ x ∈ C, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ C :=
--   intrinsicInterior_iff hC <| (intrinsicInterior_nonempty hC).2 hn

/-
Intrinsic interior of direct sum of convex sets is the direct sum of intrinsic interiors.
-/
#check intrinsicInterior_prod_eq_prod_intrinsicInterior
-- theorem intrinsicInterior_prod_eq {C1 : Set E} {C2 : Set F}
--     (hC1 : Convex ℝ C1) (hC2 : Convex ℝ C2) : intrinsicInterior ℝ (C1 ×ˢ C2) =
--     (intrinsicInterior ℝ C1) ×ˢ (intrinsicInterior ℝ C2) := by
--   by_cases hn : C1.Nonempty ∧ C2.Nonempty
--   · ext ⟨x1, x2⟩
--     rw [mem_prod, intrinsicInterior_iff' hC1 hn.1, intrinsicInterior_iff' hC2 hn.2]
--     rw [intrinsicInterior_iff' (hC1.prod hC2) (hn.1.prod hn.2)]
--     rcases hn with ⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩
--     refine ⟨fun h ↦ ⟨
--       fun x hx ↦ (h ⟨x, y2⟩ (mem_prod.2 ⟨hx, hy2⟩)).imp fun μ hμ ↦ ⟨hμ.1, (mem_prod.2 hμ.2).1⟩,
--       fun x hx ↦ (h ⟨y1, x⟩ (mem_prod.2 ⟨hy1, hx⟩)).imp fun μ hμ ↦ ⟨hμ.1, (mem_prod.2 hμ.2).2⟩⟩,
--       fun h ⟨z1, z2⟩ ⟨hz1, hz2⟩ => ?_⟩
--     rcases h.1 z1 hz1 with ⟨μ1, hμ1, h1⟩
--     rcases h.2 z2 hz2 with ⟨μ2, hμ2, h2⟩
--     let μ := min μ1 μ2
--     have hμ : μ > 1 := lt_min hμ1 hμ2
--     refine ⟨μ, hμ, ⟨?_, ?_⟩⟩
--     · have hμ1' := lt_trans zero_lt_one hμ1
--       have ha1 : 0 ≤ 1 - μ / μ1 := sub_nonneg.2 <| (div_le_one hμ1').2 (min_le_left _ _)
--       have hb1 : 0 ≤ μ / μ1 := div_nonneg (by linarith) (le_of_lt hμ1')
--       apply mem_of_eq_of_mem _ (convex_iff_add_mem.2 hC1 hz1 h1 ha1 hb1 (by ring))
--       simp; rw [←smul_assoc, ←add_assoc, ←add_smul, smul_sub, ←smul_assoc]
--       simp; rw [div_mul_cancel₀ μ (ne_of_gt hμ1')]
--     · have hμ2' := lt_trans zero_lt_one hμ2
--       have ha2 : 0 ≤ 1 - μ / μ2 := sub_nonneg.2 <| (div_le_one hμ2').2 (min_le_right _ _)
--       have hb2 : 0 ≤ μ / μ2 := div_nonneg (by linarith) (le_of_lt hμ2')
--       apply mem_of_eq_of_mem _ (convex_iff_add_mem.2 hC2 hz2 h2 ha2 hb2 (by ring))
--       simp; rw [←smul_assoc, ←add_assoc, ←add_smul, smul_sub, ←smul_assoc]
--       simp; rw [div_mul_cancel₀ μ (ne_of_gt hμ2')]
--   · rw [not_and_or, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty] at hn
--     rcases hn with h | h <;> simp[h]

/-
Closure of direct sum of convex sets is the direct sum of closures.
-/
#check closure_prod_eq

/-
For next corollary.
-/
private def A : E × E →L[ℝ] E := {
  toFun := fun x ↦ x.1 + x.2,
  map_add' := fun x y ↦ by simp [add_add_add_comm],
  map_smul' := by simp,
  cont := by continuity
}

/-
Corollary 6.6.2 (first part).
The intrinsic interior of the sum of two convex sets is the sum of their intrinsic interiors.
-/
theorem intrinsicInterior_sum_eq
    {C1 C2 : Set E} (hC1 : Convex ℝ C1) (hC2 : Convex ℝ C2) :
    intrinsicInterior ℝ (C1 + C2) = (intrinsicInterior ℝ C1) + (intrinsicInterior ℝ C2):= by
  have := linearMap_intrinsicInterior (C1 ×ˢ C2) A (hC1.prod hC2)
  rw [intrinsicInterior_prod_eq_prod_intrinsicInterior] at this; simpa [A]

/-
Corollary 6.6.2 (second part).
The closure of the sum of two sets contains the sum of their closures.
-/
omit [FiniteDimensional ℝ E] in
theorem closure_sum_subset_sum_closure {C1 C2 : Set E} :
    (closure C1) + (closure C2) ⊆ closure (C1 + C2) := by
  simpa [A, closure_prod_eq] using linearMap_closure (C1 ×ˢ C2) A

end Thm_6_6

section Thm_6_7

variable {E F} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-
The projection map from E × F to E.
-/
private def Proj : E × F →L[ℝ] E := {
  toFun := fun z ↦ z.1,
  map_add' := Prod.fst_add,
  map_smul' := Prod.smul_fst,
  cont := continuous_fst
}

/-
Theorem 6.7 (first part).
Let A be a linear map between finite-dimensional real normed spaces E and F,
and let C be a convex set in F. If the preimage of the intrinsic interior of C under A is nonempty,
then the intrinsic interior of the preimage of C equals the preimage of the intrinsic interior of C.
Purpose: linear maps commute with intrinsic interior under preimage.
-/
theorem linearMap_inv_intrinsicInterior {C : Set F} (A : E →L[ℝ] F) (hC : Convex ℝ C)
    (hn : (A ⁻¹' (intrinsicInterior ℝ C)).Nonempty) :
    intrinsicInterior ℝ (A ⁻¹' C) = A ⁻¹' (intrinsicInterior ℝ C) := by
  let D := (univ : Set E) ×ˢ C
  let M := A.graph
  have hAP : A ⁻¹' C = Proj '' (M ∩ D) := by
    ext x; simp [M, D, Proj]
  rw [hAP, linearMap_intrinsicInterior (M ∩ D) Proj (M.convex.inter (convex_univ.prod hC))]
  have hinter : (intrinsicInterior ℝ M) ∩ (intrinsicInterior ℝ D) ≠ ∅ := by
    rcases hn with ⟨x, hx⟩
    rw [←nonempty_iff_ne_empty]
    refine ⟨⟨x, A x⟩, ?_, ?_⟩
    · rw [intrinsicInterior_submodule_eq_self]; simp [M]
    · rw [intrinsicInterior_prod_eq_prod_intrinsicInterior]; exact mk_mem_prod (by simp) hx
  rw [←iInter_intrinsicInterior_eq_intrinsicInterior_iInter' M.convex (convex_univ.prod hC) hinter]
  rw [intrinsicInterior_submodule_eq_self]
  rw [intrinsicInterior_prod_eq_prod_intrinsicInterior]
  ext x; simp [M, Proj]

/-
Theorem 6.7 (second part).
Let A be a linear map between finite-dimensional real normed spaces E and F,
and let C be a convex set in F. If the preimage of the intrinsic interior of C under A is nonempty,
then the intrinsic closure of the preimage of C equals the preimage of the intrinsic closure of C.
Purpose: linear maps commute with intrinsic closure under preimage.
-/
theorem linearMap_inv_intrinsicClosure {C : Set F} (A : E →L[ℝ] F) (hC : Convex ℝ C)
    (hn : (A ⁻¹' (intrinsicInterior ℝ C)).Nonempty) :
    intrinsicClosure ℝ (A ⁻¹' C) = A ⁻¹' (intrinsicClosure ℝ C) := by
  simp only [intrinsicClosure_eq_closure]
  apply Subset.antisymm (A.continuous.closure_preimage_subset _)
  let D := (univ : Set E) ×ˢ C
  let M := A.graph
  have hAP : A ⁻¹' C = Proj '' (M ∩ D) := by
    ext x; simp [M, D, Proj]
  rw [hAP]; apply subset_of_eq_of_subset _ (linearMap_closure (M ∩ D) Proj)
  have hinter :  ∃ x, x ∈ intrinsicInterior ℝ ↑M ∩ intrinsicInterior ℝ D := by
    rcases hn with ⟨x, hx⟩
    refine ⟨⟨x, A x⟩, ?_, ?_⟩
    · rw [intrinsicInterior_submodule_eq_self]; simp [M]
    · rw [intrinsicInterior_prod_eq_prod_intrinsicInterior]; exact mk_mem_prod (by simp) hx
  rw [←iIntersection_closure_eq_intrinsicInterior_closure' M.convex (convex_univ.prod hC) hinter]
  rw [closure_submodule_eq_self, closure_prod_eq]
  ext x; simp [M, Proj]

end Thm_6_7

section Thm_6_8

def LinearMap.fst_WithLp2 (M N : Type*) [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] : WithLp 2 (M × N) →ₗ[ℝ] M where
  toFun := Prod.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def ContinuousLinearMap.fst_WithLp2 (M N : Type*)
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] :
    WithLp 2 (M × N) →L[ℝ] M where
  cont := continuous_fst
  toLinearMap := LinearMap.fst_WithLp2 M N

/-
Theorem 6.8.
-/

def Cy {E F} (C : Set (E × F)) (x : E) := SetRel.image C {x}
def M {E F} (x : E) : Set (E × F) := {x} ×ˢ univ
def D (C : Set (E × F)) : Set E := Prod.fst '' C

lemma D_eq_projection {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (C : Set (E × F)) :
    D C = ContinuousLinearMap.fst_WithLp2 E F '' C := rfl

lemma Set.prod_decomp (S : Set (E × F)) : S = ⋃ i ∈ D S, (M i ∩ S) := by
  ext x; simp
  exact ⟨fun hx ↦ ⟨x.1, by apply mem_prod.mpr; simp, mem_image_of_mem Prod.fst hx, hx⟩,
  fun ⟨_, _, _, hx⟩ ↦ hx⟩

-- theorem mem_intrinsicInterior_prod_iff {E F : Type*}
--     [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
--     [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
--     (C : Set (E × F)) (hc : Convex ℝ C) (x : E) (y : F) : (x, y) ∈ intrinsicInterior ℝ C
--     ↔ x ∈ intrinsicInterior ℝ (D C) ∧ y ∈ intrinsicInterior ℝ (Cy C x) := by
--   have proj : D (intrinsicInterior ℝ C) = intrinsicInterior ℝ (D C) := by
--     repeat rw [D_eq_projection]
--     symm
--     apply linearMap_intrinsicInterior C _ hc

--   have mem (S : Set (E × F)) : (x, y) ∈ ⋃ i ∈ D S, M i ∩ S ↔ x ∈ D S ∧ (x, y) ∈ M x ∩ S := by
--     have iff (a i : E) (b : F) : (a, b) ∈ M i ↔ a = i := by simp [M]
--     simp;
--     constructor
--     · rintro ⟨i, ha, hb, hc⟩
--       have hd := (iff x i y).mp ha
--       exact ⟨hd ▸ hb, hd ▸ ha, hc⟩
--     rintro ⟨ha, hb, hc⟩
--     use x

--   have mem_inter : (x, y) ∈ M x ∩ intrinsicInterior ℝ C ↔ y ∈ intrinsicInterior ℝ (Cy C x) := by
--     have eq1 : M x ∩ intrinsicInterior ℝ C = intrinsicInterior ℝ (M x ∩ C) := sorry
--     have eq2 : M x ∩ C = {x} ×ˢ (Cy C x) := by
--       unfold M Cy; ext s; simp
--       intro h; rw [←h]
--     rw [eq1, eq2, @intrinsicInterior_prod_eq_prod_intrinsicInterior]
--     simp

-- rw [Set.prod_decomp (intrinsicInterior ℝ C), mem, proj, mem_inter]

-- lemma D_epi_f_eq_dom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
-- (f : E → EReal): D (f.Epi (dom univ f)) = (dom univ f) := by
--   ext x
--   constructor
--   · intro hx; simp [D, Cy, Epi] at hx; simp [dom]
--     obtain ⟨x,hxx⟩ := Set.nonempty_def.1 hx
--     exact hxx.1
--   · intro hx; simp [D, Cy]
--     apply Set.nonempty_def.2
--     use ((f x).toReal + 1)
--     simp [Epi]; simp [dom] at hx; use hx
--     by_cases hfx : f x = ⊥
--     simp [hfx]
--     push_neg at hfx
--     have hfx2 : f x ≠ ⊤ := LT.lt.ne_top hx
--     lift (f x) to ℝ using ⟨hfx2 , hfx⟩ with fx
--     simp [← coe_one, ← coe_add, @EReal.coe_le_coe_iff]

-- theorem inter_nonempty  {E F : Type*} [NormedAddCommGroup E]
-- [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
--  [FiniteDimensional ℝ F]  (C : Set (WithLp 2 (E × F))) (hc : Convex ℝ C) :
--     ∀ y ∈ intrinsicInterior ℝ (D C), {(y, z) | z : F} ∩ intrinsicInterior ℝ C ≠ ∅ := by

--   rw [D_eq_projection, linear_ri C (ContinuousLinearMap.fst_WithLp2 E F) hc,
-- ← D_eq_projection (ri C)]
--   rintro y ⟨z, zh⟩
--   rw [← nonempty_iff_ne_empty]
--   exact ⟨(y, z), ⟨by simp, zh⟩⟩

-- omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
-- lemma Epi_eq (f : E → EReal): f.Epi univ = f.Epi (dom univ f) := by
--   ext x; unfold Epi; simp
--   exact fun h ↦ lt_of_le_of_lt h (EReal.coe_lt_top x.2)


@[simp]
lemma affineSubspace_eq_carrier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : AffineSubspace ℝ E) : M = M.carrier := by rfl

variable {E F} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma convex_section {C : Set (E × F)} (hC : Convex ℝ C) (y : E) :
  Convex ℝ {z | (y, z) ∈ C} := fun a ha b hb k1 k2 hk1 hk2 hk12 => by
  simpa [←add_smul, hk12] using @hC ⟨y, a⟩ ha ⟨y, b⟩ hb k1 k2 hk1 hk2 hk12

lemma convex_prod_singleton {C : Set F} (hC : Convex ℝ C) (y : E) :
  Convex ℝ {(y, z) | z ∈ C} := fun ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb k1 k2 hk1 hk2 hk12 => by
  simp at ha hb ⊢; rw [←ha.2, ←hb.2, ←add_smul, hk12]; simp
  simpa using hC ha.1 hb.1 hk1 hk2 hk12

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]


/-
Theorem 6.8.
Let C ⊆ E × F be convex. For each y ∈ E, define Cy = { z ∈ F | (y, z) ∈ C }.
Let D = { y ∈ E | Cy ≠ ∅ }.
Then (y₀, z₀) ∈ ri C  ⇔  (y₀ ∈ ri D) ∧ (z₀ ∈ ri Cy₀).
Purpose: characterizes the relative interior of a convex set in a product space
via the relative interiors of its slices.
-/
theorem mem_intrinsicInterior_prod_iff {C D}
    (hC : Convex ℝ C) (Cy : E → Set F) (hCy : ∀ y, Cy y = {z | (y, z) ∈ C})
    (hD : D = {y | (Cy y).Nonempty}) (y₀ : E) (z₀ : F) :
    (y₀, z₀) ∈ intrinsicInterior ℝ C ↔
    y₀ ∈ intrinsicInterior ℝ D ∧ z₀ ∈ intrinsicInterior ℝ (Cy y₀) := by
  have hProj_C_eq_D : Proj '' C = D := by
    ext t; simp [hD, hCy, Proj, Set.Nonempty]
  have hProj_riC_eq_riD : Proj '' (intrinsicInterior ℝ C) = intrinsicInterior ℝ D := by
    rw [←linearMap_intrinsicInterior C Proj hC, hProj_C_eq_D]
  let M : AffineSubspace ℝ (E × F) := {
    carrier := {(y₀, z) | z : F},
    smul_vsub_vadd_mem := by simp
  }
  have hp : y₀ ∈ intrinsicInterior ℝ D → Proj ⁻¹' {y₀} ∩ intrinsicInterior ℝ C =
      {(y₀, z) | z ∈ intrinsicInterior ℝ (Cy y₀)} := fun hy₀ => by calc
    _ = (M : Set (E × F)) ∩ intrinsicInterior ℝ C := by
      simp [Set.ext_iff, Proj, M, eq_comm] at *
    _ = {(y₀, z) | z ∈ intrinsicInterior ℝ (Cy y₀)} := by
      have hinter : (M : Set (E × F)) ∩ intrinsicInterior ℝ C ≠ ∅ := by
        rw [←nonempty_iff_ne_empty]; rw [←hProj_riC_eq_riD] at hy₀
        rcases (mem_image _ _ _).1 hy₀ with ⟨⟨y, z⟩, hyz⟩
        use (y₀, z); simpa [Proj, M, hyz.2.symm] using hyz.1
      rw [←intersection_affineSubspace_intrinsicInterior_eq hC hinter]
      have heq : (M : Set (E × F)) ∩ C = {y₀} ×ˢ {z | z ∈ Cy y₀} := by
        ext ⟨y, z⟩; simp [M, hCy y₀]
        exact ⟨fun h => ⟨h.1.symm, h.1 ▸ h.2⟩, fun h => ⟨h.1.symm, h.1 ▸ h.2⟩⟩
      rw [heq, intrinsicInterior_prod_eq_prod_intrinsicInterior]
      ext ⟨y, z⟩; simp; exact ⟨fun h => by simp [h], fun h => by simpa [h.2] using h.1⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hy₀ : y₀ ∈ intrinsicInterior ℝ D := by
      rw [←hProj_riC_eq_riD]; exact mem_image_of_mem Proj h
    have hy₀z₀ := (Set.ext_iff.1 (hp hy₀) (y₀, z₀)).1 ⟨rfl, h⟩
    exact ⟨hy₀, by simpa using hy₀z₀⟩
  · apply (Set.ext_iff.1 (hp h.1) (y₀, z₀)).2 (by use z₀; simp [h.2]) |>.2

/-
Lemma: If s ⊆ E is open, then its relative interior equals itself.
Formally: ri(s) = s when s is open.
Purpose: simplifies handling of intrinsicInterior for open sets.
-/
omit [FiniteDimensional ℝ E] in
theorem intrinsicInterior_open {s : Set E} (hs : IsOpen s) : intrinsicInterior ℝ s = s := by
  apply Subset.antisymm (intrinsicInterior_subset)
  by_cases hs' : s.Nonempty
  · intro x hx; rw [mem_intrinsicInterior, hs.affineSpan_eq_top hs']
    rw [interior_eq_iff_isOpen.2 (isOpen_induced hs)]; simp [hx]
  · push_neg at hs'; simp [hs']


/-
Corollary 6.8.1.
Let C ⊆ E be a nonempty convex set, and define the cone
K = cone{ (1, x) | x ∈ C } in ℝ × E.
Then ri K = { (λ, x) | λ > 0 and x ∈ λ • ri C }.
Purpose: describes the relative interior of the conic hull
generated from a convex set in terms of positive scalings of its ri.
-/
theorem mem_intrinsicInterior_prod_convexCone_iff {C : Set E}
    (hC : Convex ℝ C) (hn : C.Nonempty) {K : ConvexCone ℝ (ℝ × E)}
    (hK : K = (convex_prod_singleton hC 1).toCone {(1, z) | z ∈ C}) :
    (intrinsicInterior ℝ K : Set (ℝ × E)) = {(k, x) | (k > 0) ∧ x ∈ k • intrinsicInterior ℝ C} := by
  let Cy : ℝ → Set E := fun y ↦ {z | (y, z) ∈ K}
  have hCy : ∀ y, Cy y = {z | (y, z) ∈ K} := fun y => by simp [Cy]
  have hCyt : ∀ t > 0, Cy t = t • C := fun t ht => by
    ext z; simp [Cy, hK, Convex.mem_toCone]
    exact ⟨fun ⟨c, hc, ⟨w, hw⟩⟩ => ⟨w, hw.1, hw.2.1 ▸ hw.2.2⟩,
           fun ⟨w, hw⟩ => ⟨t, ht, w, hw.1, rfl, hw.2⟩⟩
  have hD : Set.Ioi 0 = {y | (Cy y).Nonempty} := by
    ext t; simp [Cy]; constructor
    · intro h; simp [Cy] at hCyt; exact hCyt t h ▸ hn.smul_set
    · intro h; simp [hK, Convex.mem_toCone'] at h
      rcases h with ⟨_, c, ⟨hc, _, _⟩⟩
      exact (mul_pos_iff_of_pos_left hc).1 (by linarith)
  ext ⟨k, z⟩;
  rw [mem_intrinsicInterior_prod_iff K.convex Cy hCy hD k z, intrinsicInterior_open isOpen_Ioi]
  exact ⟨fun h => ⟨h.1, intrinsicInterior_of_left_smul_constant hC _ ▸ hCyt k h.1 ▸ h.2⟩,
         fun h => ⟨h.1, hCyt k h.1 ▸ intrinsicInterior_of_left_smul_constant hC _ ▸ h.2⟩⟩

def ConvexCone.addPoint {R : Type u_2} {M : Type u_4} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] [AddCommMonoid M] [Module R M] (C : ConvexCone R M) : PointedCone R M where
  carrier := C.carrier ∪ {0}
  add_mem' := by
    simp; intro a b ha hb; rcases ha with ha | ha
    · rw [ha]; simpa
    rcases hb with hb | hb
    · rw [hb]; simp [ha]
    simp [C.add_mem' ha hb]
  zero_mem':= by simp
  smul_mem' := by
    simp; intro a ha x hx
    rcases le_iff_eq_or_lt.mp ha with ha | ha
    · simp [← ha]
    simp [C.smul_mem' ha hx]

theorem ConvexCone.mem_toCone_addPoint {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] {s : Set M} (hs : Convex 𝕜 s) (hne : s.Nonempty) {x : M} :
  x ∈ (Convex.toCone s hs).addPoint ↔ ∃ c : 𝕜, 0 ≤ c ∧ ∃ y ∈ s, c • y = x := by
    constructor
    · rintro hx
      simp [ConvexCone.addPoint] at hx
      rcases hx with hx | hx
      · use 0
        rw [hx]; simpa [hne]
      rcases (Convex.mem_toCone hs).mp hx with ⟨c, hc, hy⟩
      exact ⟨c, ⟨le_of_lt hc, hy⟩⟩
    rintro ⟨c, hc, y, hy, hcy⟩
    simp [ConvexCone.addPoint]
    rcases le_iff_eq_or_lt.mp hc with hc | hc
    · simp [← hc] at hcy
      simp [hcy]
    exact Or.inr ((Convex.mem_toCone hs).mpr ⟨c, hc, y, hy, hcy⟩)

def Convex.toCone_Point {𝕜 : Type u_1} {M : Type u_4} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]
    (s : Set M) (hs : Convex 𝕜 s) : ConvexCone 𝕜 M where
  carrier := hs.toCone s ∪ {0}
  add_mem' := by
    intro a ha b hb; simp at *; rcases ha with ha | ha
    · rw [ha]; simpa
    rcases hb with hb | hb
    · rw [hb]; simp [ha]
    exact Or.inr (ConvexCone.add_mem' (toCone s hs) ha hb)
  smul_mem' := by
    intro a ha x hx; simp at *
    rcases hx with hx | hx
    · simp [hx]
    exact Or.inr (ConvexCone.smul_mem' (toCone s hs) ha hx)

theorem Convex.toCone_Point_pointed {𝕜 : Type u_1} {M : Type u_4}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (s : Set M) (hs : Convex 𝕜 s) : (hs.toCone_Point s).Pointed := by
  unfold Convex.toCone_Point ConvexCone.Pointed; simp

theorem Convex.toCone_Point_nonempty {𝕜 : Type u_1} {M : Type u_4}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (s : Set M) (hs : Convex 𝕜 s) :
    (hs.toCone_Point s : Set M).Nonempty :=
  ⟨0, Convex.toCone_Point_pointed s hs⟩

theorem Convex.mem_toCone_Point {𝕜 : Type u_1} {M : Type u_4}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] {s : Set M} (hs : Convex 𝕜 s) (hne : s.Nonempty) {x : M} :
    x ∈ Convex.toCone_Point s hs ↔ ∃ c, (0:𝕜) ≤ c ∧ ∃ y ∈ s, c • y = x := by
  unfold Convex.toCone_Point
  simp; constructor
  · rintro hx; rcases hx with hx | hx
    · use 0; rw [hx]; simp; exact hne
    rcases (Convex.mem_toCone hs).mp hx with ⟨c, hc, hcy⟩
    exact ⟨c, ⟨le_of_lt hc, hcy⟩⟩
  rintro hx; rcases hx with ⟨c, hc, y, hy, hcy⟩
  rcases le_iff_eq_or_lt.mp hc with hc | hc
  · rw [← hcy, ← hc]; simp
  exact Or.inr ((Convex.mem_toCone hs).mpr ⟨c, hc, y, hy, hcy⟩)

theorem ConvexCone.smul_mem_pointed {R M} [Semiring R] [PartialOrder R] [AddCommMonoid M]
    [Module R M] (C : ConvexCone R M) (hp : C.Pointed) {c : R} {x : M} (hc : 0 ≤ c) (hx : x ∈ C) :
    c • x ∈ C := by
  rcases le_iff_lt_or_eq.mp hc with h | h
  · exact ConvexCone.smul_mem C h hx
  rw [← h, zero_smul]; exact hp

-- theorem Convex.mem_toCone_Point' {𝕜 : Type u_1} {M : Type u_4} [Field 𝕜] [LinearOrder 𝕜]
--   [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]
--   {s : Set M} (hs : Convex 𝕜 s) (hne: s.Nonempty) {x : M} :
--   x ∈ Convex.toCone_Point s hs ↔ ∃ c, 0 ≤ c ∧ c • x ∈ s := by
--   refine (mem_toCone_Point hs hne).trans ⟨?_, ?_⟩
--   · rintro ⟨c, hc, y, hy, rfl⟩
--     exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
--   · rintro ⟨c, hc, hcx⟩
--     exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
--   sorry

lemma one_prod_eq {E} (C : Set E) : {(1, z) | z ∈ C} = {(1:ℝ)} ×ˢ C := by
    ext x; simp; constructor
    · rintro ⟨z, hz, hx⟩
      exact ⟨(Prod.mk_inj.mp (Eq.symm hx)).1, (Prod.mk_inj.mp (Eq.symm hx)).2 ▸ hz⟩
    exact fun ⟨hx, hc⟩ ↦ ⟨x.2, ⟨hc, Prod.mk_inj.mpr ⟨Eq.symm hx, rfl⟩⟩⟩

/-
Corollary 6.8.1 for pointed cone.
Let C ⊆ E be a nonempty convex set, and define the cone
K = cone{ (1, x) | x ∈ C } in ℝ × E.
Then ri K = { (λ, x) | λ > 0 and x ∈ λ • ri C }.
Purpose: describes the relative interior of the conic hull
generated from a convex set in terms of positive scalings of its ri.
-/
theorem mem_intrinsicInterior_prod_convexCone_iff' {C : Set E}
    (hC : Convex ℝ C) (hn : C.Nonempty) {K : ConvexCone ℝ (ℝ × E)}
    (hK : K = (convex_prod_singleton hC 1).toCone_Point {(1, z) | z ∈ C}) :
    (intrinsicInterior ℝ K : Set (ℝ × E)) = {(k, x) | (k > 0) ∧ x ∈ k • intrinsicInterior ℝ C} := by
  let Cy : ℝ → Set E := fun y ↦ {z | (y, z) ∈ K}
  have hne := (one_prod_eq C) ▸ (prod_nonempty_iff).mpr ⟨singleton_nonempty (1:ℝ),hn⟩
  have hCy : ∀ y, Cy y = {z | (y, z) ∈ K} := fun y => by simp [Cy]
  have hCyt : ∀ t ≥ 0, Cy t = t • C := fun t ht => by
    ext z; simp [Cy, hK]; rw [Convex.mem_toCone_Point]; simp
    exact ⟨fun ⟨c, hc, ⟨w, hw⟩⟩ => ⟨w, hw.1, hw.2.1 ▸ hw.2.2⟩,
           fun ⟨w, hw⟩ => ⟨t, ht, w, hw.1, rfl, hw.2⟩⟩
    apply hne
  have hD : Set.Ici 0 = {y | (Cy y).Nonempty} := by
    ext t; simp [Cy]; constructor
    · intro h; simp [Cy] at hCyt; exact hCyt t h ▸ hn.smul_set
    · rw [hK, Set.nonempty_def];
      simp; intro x; rw [Convex.mem_toCone_Point _ hne]; simp;
      intro s hs _ _ hst _; simp_rw [← hst, hs]
  ext ⟨k, z⟩;
  rw [mem_intrinsicInterior_prod_iff K.convex Cy hCy hD k z]
  have : Ici (0:ℝ) = closure (Ioi 0) := by
    exact Eq.symm (closure_Ioi 0)
  rw [this, intrinsicInterior_closure, intrinsicInterior_open isOpen_Ioi]
  · exact
    ⟨fun h => ⟨h.1, intrinsicInterior_of_left_smul_constant hC _ ▸ hCyt k (le_of_lt h.1) ▸ h.2⟩,
     fun h => ⟨h.1, hCyt k (le_of_lt h.1) ▸ intrinsicInterior_of_left_smul_constant hC _ ▸ h.2⟩⟩
  exact convex_Ioi 0

end Thm_6_8

section Thm_6_9

lemma Convex.convexCone_union {𝕜 M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (a b : ConvexCone 𝕜 M)
    (ha : a.Pointed) (hb : b.Pointed) (hnea : (a : Set M).Nonempty) (hneb : (b : Set M).Nonempty) :
    a + b = convexHull 𝕜 (a ∪ b : Set M) := by
  ext x; change x ∈ (a + b) ↔ _
  rw [@ConvexCone.mem_add, convexHull_union hnea hneb, mem_convexJoin,
      convexHull_eq_self.mpr a.convex, convexHull_eq_self.mpr b.convex]
  simp [mem_segment_iff_div];
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    use (2:𝕜) • y, ConvexCone.smul_mem a (by norm_num) hy,
        (2:𝕜) • z, ConvexCone.smul_mem b (by norm_num) hz,
        1, by norm_num, 1, by norm_num
    field_simp [← mul_smul]; simp [smul_smul]; ring_nf; simp [hyz]
  · rintro ⟨y, hy, z, hz, ⟨m, hm, n, hn, hmn, hyz⟩⟩
    use (m/(m+n)) • y, ConvexCone.smul_mem_pointed a ha (div_nonneg hm (le_of_lt hmn)) hy,
        (n/(m+n)) • z, ConvexCone.smul_mem_pointed b hb (div_nonneg hn (le_of_lt hmn)) hz


lemma toCone_subset_convex {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (s : ConvexCone 𝕜 M) (t : Set M) (ht : Convex 𝕜 t)
    (h : t ⊆ s) : (ht.toCone : Set M) ⊆ s := by
  rw [ht.toCone_eq_sInf]; norm_cast
  apply sInf_le (mem_setOf_eq ▸ h)

lemma toCone_Pointed_subset_convex {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (s : ConvexCone 𝕜 M) (hs : s.Pointed) (t : Set M)
    (ht : Convex 𝕜 t) (h : t ⊆ s) : (ht.toCone_Point : Set M) ⊆ s := by
  intro x hx
  simp [Convex.toCone_Point] at hx
  by_cases hx0 : x = 0
  · exact hx0 ▸ hs
  · exact toCone_subset_convex s t ht h (mem_of_mem_insert_of_ne hx hx0)

lemma Convex.subset_toCone_Point {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] {s : Set M} (hs : Convex 𝕜 s) :
    s ⊆ (hs.toCone_Point s : Set M) := fun x hx => by
  simp [Convex.toCone_Point]
  exact or_iff_not_imp_left.2 (fun _ => hs.subset_toCone hx)

@[simp]
lemma mem_of_convexHull {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (s : Set M) {x} (hx : x ∈ s) :
    x ∈ convexHull 𝕜 s := mem_convexHull_iff.mpr fun _ a _ ↦ a hx

def Convex.smul_mem_mk_ConvexCone {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (s : Set M) (hs : Convex 𝕜 s)
    (h₁ : ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : M⦄, x ∈ s → c • x ∈ s) : ConvexCone 𝕜 M :=
    ConvexCone.mk s h₁ (fun y hy z hz => by
      rw [convex_iff_add_mem] at hs
      have := hs (h₁ zero_lt_two hy) (h₁ zero_lt_two hz) (a := (2 : 𝕜)⁻¹) (b := (2 : 𝕜)⁻¹)
          (by linarith) (by linarith) (by ring)
      simpa using this
    )

lemma smul_convexCone_eq {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M]
    [Module 𝕜 M] (s : ConvexCone 𝕜 M) {a : 𝕜} (ha : a > 0) : a • (s : Set M) = s :=
  Set.ext fun x => ⟨fun hx => by
  rcases mem_smul_set.2 hx with ⟨y, hy, rfl⟩
  exact s.smul_mem ha hy,
  fun hx => mem_smul_set.2
    ⟨a⁻¹ • x, s.smul_mem (inv_pos.2 ha) hx, (smul_inv_smul₀ (by linarith) x)⟩⟩

lemma Convex.toCone_Point_isLeast {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] {s : Set M} (hs : Convex 𝕜 s) :
    IsLeast { t : ConvexCone 𝕜 M | t.Pointed ∧ s ⊆ t } (hs.toCone_Point s) := by
  refine ⟨⟨hs.toCone_Point_pointed, hs.subset_toCone_Point⟩, fun t ht x hx => ?_⟩
  by_cases hs' : s.Nonempty
  · rcases (hs.mem_toCone_Point hs').1 hx  with ⟨c, hc, y, hy, rfl⟩
    by_cases hc0 : c > 0
    · apply t.smul_mem hc0 (ht.2 hy)
    · push_neg at hc0; rw [le_antisymm hc0 hc]; simp; exact ht.1
  · push_neg at hs'; simp [hs', toCone_Point, toCone] at hx; exact hx.symm ▸ ht.1

theorem Convex.toCone_Point_eq_sInf {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] {s : Set M} (hs : Convex 𝕜 s) :
    hs.toCone_Point s = sInf { t : ConvexCone 𝕜 M | t.Pointed ∧ s ⊆ t } :=
  hs.toCone_Point_isLeast.isGLB.sInf_eq.symm

lemma Convex.toCone_Pointed_convexHull {𝕜} {M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (s t : Set M) (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    convexHull 𝕜 ((hs.toCone_Point s) ∪ (ht.toCone_Point t)) =
    (toCone_Point (convexHull 𝕜 (s ∪ t)) (convex_convexHull 𝕜 (s ∪ t)) : Set M) := by
  let conv_cone_s_cone_t := convexHull 𝕜 ((hs.toCone_Point s) ∪ (ht.toCone_Point t) : Set M)
  let cone_conv_s_t := toCone_Point _ (convex_convexHull 𝕜 (s ∪ t))
  apply Subset.antisymm
  · have hs1 : s ⊆ cone_conv_s_t := subset_trans
          (subset_trans subset_union_left (subset_convexHull _ _))
          (subset_toCone_Point (convex_convexHull 𝕜 (s ∪ t)))
    have ht1 : t ⊆ cone_conv_s_t := subset_trans
          (subset_trans subset_union_right (subset_convexHull _ _))
          (subset_toCone_Point (convex_convexHull 𝕜 (s ∪ t)))
    have h1 := toCone_Pointed_subset_convex cone_conv_s_t (toCone_Point_pointed _ _) s hs hs1
    have h2 := toCone_Pointed_subset_convex cone_conv_s_t (toCone_Point_pointed _ _) t ht ht1
    apply convexHull_min (union_subset h1 h2) cone_conv_s_t.convex
  · rw [toCone_Point_eq_sInf]
    intro x hx
    simp at hx
    let conv_cone_s_cone_t_is_cone : ConvexCone 𝕜 M := by
      apply Convex.smul_mem_mk_ConvexCone conv_cone_s_cone_t (convex_convexHull 𝕜 _)
      intro c hc y hy
      have := smul_mem_smul_set (a := c) hy
      rw [←convexHull_smul, smul_set_union] at this
      rw [smul_convexCone_eq _ hc, smul_convexCone_eq _ hc] at this
      exact this
    change x ∈ conv_cone_s_cone_t_is_cone
    have h0in : 0 ∈ conv_cone_s_cone_t := mem_of_convexHull _ (by simp [Convex.toCone_Point])
    have hst : s ∪ t ⊆ conv_cone_s_cone_t := by
      have hl := (subset_union_of_subset_left (subset_toCone_Point hs) ht.toCone_Point)
      have hr := (subset_union_of_subset_right (subset_toCone_Point ht) hs.toCone_Point)
      apply union_subset (subset_trans hl (subset_convexHull _ _))
                         (subset_trans hr (subset_convexHull _ _))
    have conv_s_t_ss := convexHull_min hst (convex_convexHull 𝕜 _)
    apply hx _ (by exact h0in) conv_s_t_ss

variable {E F} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem intrinsicInterior_convexHull_iUnion_eq' (a b : Set E)
    (ha : Convex ℝ a) (hb : Convex ℝ b) (hnea : a.Nonempty) (hneb : b.Nonempty) :
    intrinsicInterior ℝ (convexHull ℝ (a ∪ b)) =
    ⋃ s ∈ {(m, n) | (m > 0) ∧ (n > 0) ∧ m + n = (1:ℝ)},
    (s.1 • intrinsicInterior ℝ a + s.2 • intrinsicInterior ℝ b) := by

  let ab := convexHull ℝ (a ∪ b)
  have convex_ab := (convex_convexHull ℝ (a ∪ b))
  have ne_ab : ab.Nonempty := Nonempty.convexHull (Nonempty.inr hneb)

  let Ca := {((1:ℝ), z) | z ∈ a}
  let Cb := {((1:ℝ), z) | z ∈ b}
  let Cab := {((1:ℝ), z) | z ∈ ab}
  have convex_Ca : Convex ℝ Ca:= (convex_prod_singleton ha 1)
  have convex_Cb : Convex ℝ Cb:= (convex_prod_singleton hb 1)

  let Ka: ConvexCone ℝ (ℝ × E) := (convex_Ca.toCone_Point Ca)
  let Kb: ConvexCone ℝ (ℝ × E) := (convex_Cb.toCone_Point Cb)
  let Kab := ((convex_prod_singleton convex_ab 1).toCone_Point Cab)

  have K_sum := by calc
    Kab = convexHull ℝ (Ka ∪ Kb : Set (ℝ × E)) := by
      unfold Kab; rw [Convex.toCone_Pointed_convexHull]; simp; congr; unfold Cab Ca Cb ab;
      rw [one_prod_eq, one_prod_eq a, one_prod_eq b, Eq.symm prod_union, convexHull_prod]; simp
    _ = Ka + Kb := by rw [Convex.convexCone_union _ _
      (Convex.toCone_Point_pointed Ca convex_Ca) ((Convex.toCone_Point_pointed Cb convex_Cb))
      (Convex.toCone_Point_nonempty Ca convex_Ca) (Convex.toCone_Point_nonempty Cb convex_Cb)]

  change intrinsicInterior ℝ ab = _; ext x; calc
    _ ↔ (1, x) ∈ intrinsicInterior ℝ (Kab:Set (ℝ × E)) := by
      rw [mem_intrinsicInterior_prod_convexCone_iff' convex_ab ne_ab (K := Kab) rfl,
        ← (Eq.symm rfl : ab = convexHull ℝ (a ∪ b))]; simp
    _ ↔ (1, x) ∈ intrinsicInterior ℝ (Ka:Set (ℝ × E)) + intrinsicInterior ℝ (Kb:Set (ℝ × E)) := by
      rw [K_sum, ← intrinsicInterior_sum_eq (ConvexCone.convex Ka) (ConvexCone.convex Kb)]
  rw [@mem_add, mem_intrinsicInterior_prod_convexCone_iff' ha hnea (K := Ka) rfl,
      mem_intrinsicInterior_prod_convexCone_iff' hb hneb (K := Kb) rfl]

  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩; simp
    refine ⟨p.1, q.1, ⟨hp.1, hq.1, (Prod.eq_iff_fst_eq_snd_eq.mp hpq).1⟩, ?_⟩
    use p.2, hp.2, q.2, hq.2, (Prod.eq_iff_fst_eq_snd_eq.mp hpq).2
  rw [Set.mem_iUnion₂]
  rintro ⟨i, hi, p, hp, q, hq, hpq⟩
  use ⟨i.1, p⟩, ⟨hi.1, hp⟩, ⟨i.2, q⟩, ⟨hi.2.1, hq⟩
  simp [hi.2.2, hpq]


open Finset in
theorem intrinsicInterior_convexHull_iUnion_eq {ι : Type} [Fintype ι] (C : ι → Set E)
    (hC : (i : ι) → Convex ℝ (C i)) (hne : (i : ι) → (C i).Nonempty) :
    intrinsicInterior ℝ (convexHull ℝ (⋃ i, C i)) =
    ⋃ s ∈ {t : ι → ℝ | (∀ i, t i > 0) ∧ ∑ i, t i = 1},
    ∑ i, (s i) • (intrinsicInterior ℝ (C i)) := by
  induction hι : Fintype.card ι generalizing ι with
  | zero => rw [Fintype.card_eq_zero_iff] at hι; simp
  | succ n ih =>
    rcases n with - | n
    · rw [zero_add] at hι
      rcases Fintype.card_eq_one_iff.1 hι with ⟨i₀, hi₀⟩
      calc
      _ = intrinsicInterior ℝ ((convexHull ℝ) (C i₀)) := by
        congr; apply Subset.antisymm
          (fun x hx => by rcases mem_iUnion.1 hx with ⟨j, hj⟩; exact hi₀ j ▸ hj)
          (subset_iUnion_of_subset i₀ (fun _ h => h))
      _ = intrinsicInterior ℝ (C i₀) := by rw [(convexHull_eq_self).2 (hC i₀)]
      _ = ⋃ s ∈ ({fun i => 1} : Set (ι → ℝ)), ∑ i, s i • intrinsicInterior ℝ (C i) := by
        simp; rw [Fintype.sum_eq_single i₀ (fun x a ↦ False.elim (a (hi₀ x)))]
      _ = _ := by
        congr!; refine Set.ext fun l => ⟨fun h => by simp at h; simpa [h], fun ⟨_, h⟩ => ?_⟩
        rw [Fintype.sum_eq_single i₀ (fun x a ↦ False.elim (a (hi₀ x)))] at h
        ext i; apply hi₀ i ▸ h
    · obtain ⟨i₀⟩ := Fintype.card_pos_iff.1 (Nat.lt_of_sub_eq_succ hι)
      let ι' := {i // i ≠ i₀}
      haveI : Fintype ι' := Fintype.ofFinite ι'
      have hι' : Nonempty ι' := by
        have : Fintype.card ι' = n + 1 := by simpa [ι']
        obtain ⟨i⟩ := Fintype.card_pos_iff.1 (Nat.lt_of_sub_eq_succ this)
        use i, i.2
      rcases hι' with ⟨j, hj⟩
      have h1 := ih (fun i : ι' ↦ C i.1) (fun i ↦ hC i.1) (fun i ↦ hne i.1) (by simp [ι', hι])
      let a := convexHull ℝ (⋃ i : ι', C i)
      have hna : a.Nonempty := by
        rcases hne j with ⟨x, hx⟩
        exact Nonempty.convexHull ⟨x, mem_iUnion.2 ⟨⟨j, hj⟩, hx⟩⟩
      have h2 := intrinsicInterior_convexHull_iUnion_eq' a (C i₀)
          ((convex_convexHull _ _)) (hC i₀) hna (hne i₀)
      calc
      _ = _ := by
        suffices (convexHull ℝ) (⋃ i, C i) = (convexHull ℝ) (a ∪ C i₀) by simp [this]
        rw [convexHull_convexHull_union_left]; congr
        ext x; simp; constructor
        · rintro ⟨i, hi⟩; rcases eq_or_ne i i₀ with rfl | hne
          · right; exact hi
          · left; exact ⟨⟨i, hne⟩, hi⟩
        · rintro (⟨i, hi⟩ | hi)
          · exact ⟨i, hi⟩
          · exact ⟨i₀, hi⟩
      _ = _ := h2
      _ = _ := by
        classical
        rw [h1]; ext x; simp; constructor
        · rintro ⟨m, n, ⟨hm, hn, hmn⟩, y, ⟨y₀, hy₀, hyy₀⟩, hxy⟩
          simp at hy₀ hyy₀ hxy
          rcases hy₀ with ⟨l, ⟨hl1, hl2⟩, hy₀'⟩
          refine ⟨fun i => if h : i = i₀ then n else m * (l ⟨i, h⟩), ⟨?_, ?_⟩, ?_⟩
          · exact fun i => dite_pos (fun _ => hn) (fun h => mul_pos hm (hl1 ⟨i, h⟩))
          · rw [sum_dite, add_comm, ←hmn]; congr
            · rw [←mul_sum]; convert mul_one m; rw [←hl2]; congr
              any_goals simp [ι']
              · congr!; simp
              · congr! <;> simp
            · simp [natCast_card_filter, one_mul]
          · rcases hxy with ⟨z, ⟨z₀, hz₀1, hz₀2⟩, hxyz⟩
            simp at hz₀2
            have := add_mem_add (smul_mem_smul_set (a := m) hy₀')
                                (smul_mem_smul_set (a := n) hz₀1)
            rw [smul_sum, hyy₀, hz₀2, hxyz] at this
            convert this; simp [ι']; rw [sum_dite, add_comm]
            rw [Fintype.sum_congr (fun i => m • l i • intrinsicInterior ℝ (C i))
                  (fun i => (m • l i) • intrinsicInterior ℝ (C i)) (fun i => by simp [smul_smul])]
            congr; any_goals simp [ι', sum_attach_eq_sum_dite]
            · congr!; simp
            · congr! <;> simp
        · rintro ⟨l, ⟨hl1, hl2⟩, hx⟩
          have hl0_pos : 0 < 1 - l i₀ := by
            rw [sub_pos, ←hl2]; apply single_lt_sum hj (by simp) (by simp) (hl1 j)
            exact fun k _ _ => by linarith[hl1 k]
          have hl0_ne0 : (1 - l i₀) ≠ 0 := ne_of_gt hl0_pos
          refine ⟨1 - l i₀, l i₀, ⟨hl0_pos, hl1 i₀, by ring⟩, ?_⟩
          have hx' : x ∈ ∑ i : ι', l i • intrinsicInterior ℝ (C i) +
                         l i₀ • intrinsicInterior ℝ (C i₀) := by
            rw [←Fintype.sum_subtype_add_sum_subtype (· ≠ i₀)] at hx
            convert hx; rw [Fintype.sum_eq_single ⟨i₀, by simp⟩]
            exact fun ⟨j, hj⟩ hj' => False.elim (hj (by simpa using hj'))
          apply Set.mem_of_subset_of_mem _ hx'
          apply Set.add_subset_add_right
          rw [subset_smul_set_iff₀ hl0_ne0]
          intro y hy
          rw [smul_sum] at hy
          apply mem_iUnion.2
          use fun i : ι' => (l i) / (1 - l i₀)
          simp; refine ⟨⟨fun i => div_pos (hl1 i.1) hl0_pos, ?_⟩, ?_⟩
          · rw [←Fintype.sum_subtype_add_sum_subtype (· ≠ i₀)] at hl2
            rw [←sum_div, div_eq_of_eq_mul hl0_ne0]
            simp [ι'] at ⊢ hl2
            convert Eq.symm <| sub_eq_iff_eq_add.2 hl2.symm
            rw [Fintype.sum_eq_single ⟨i₀, by simp⟩]
            exact fun ⟨j, hj⟩ hj' => False.elim (hj (by simpa using hj'))
          · rw [Fintype.sum_congr (fun i : ι' => (1 - l i₀)⁻¹ • l i • intrinsicInterior ℝ (C i))
                (fun i : ι' => ((1 - l i₀)⁻¹ • l i) • intrinsicInterior ℝ (C i))
                (fun i => by simp [smul_smul])] at hy
            convert hy using 2; congr; rw [div_eq_inv_mul, smul_eq_mul]

end Thm_6_9
