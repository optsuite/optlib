import Mathlib.Topology.Algebra.AffineSubspace
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Basis.Defs

/-
* Chapter 1 of [R. T. Rockafellar, *Convex Analysis*] [rockafellar1970].
-/

open Set Topology Inner Function Module AffineSubspace
open scoped Pointwise

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E F : Type*}

section Thm_1_1

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Module ℝ E]

/- The empty set is an affine set. -/
lemma empty_is_affine : ∃ p : AffineSubspace ℝ E, (p : Set E) = ∅ := ⟨⊥, rfl⟩


/- The whole space is an affine set. -/
lemma space_itself_is_affine : ∃ p : AffineSubspace ℝ E, p = (univ : Set E) := ⟨⊤, rfl⟩


/- A singleton is an affine set. -/
lemma singleton_is_affine {s : Set E} (hss : s = {x}) : ∃ p : AffineSubspace ℝ E, p = s := by
  use affineSpan ℝ {x}; ext y
  rw [AffineSubspace.mem_coe, mem_affineSpan_singleton]
  exact Iff.symm (Eq.to_iff (congrFun hss y))



/- Lemma 1: subspaces of Rⁿ are affine sets. -/
lemma subspace_is_affinesubspace (s : Submodule ℝ E) :
  ∃ p : AffineSubspace ℝ E, s = (p : Set E) := by
  use ⟨s, fun c _ _ _ h1 h2 h3 => s.add_mem (s.smul_mem c (s.sub_mem h1 h2)) h3⟩; rfl


/- Lemma 2: affine sets containing 0 are subspaces of Rⁿ. -/
lemma affine_of_subspace (p : AffineSubspace ℝ E) (h0 : (0 : E) ∈ p) :
  ∃ s : Submodule ℝ E, (p: Set E) = s := by
  use p.direction
  ext x; constructor <;> intro hx
  · simpa only [SetLike.mem_coe, vsub_eq_sub, sub_zero] using p.vsub_mem_direction hx h0
  simpa only [SetLike.mem_coe, vadd_eq_add, add_zero] using p.vadd_mem_of_mem_direction hx h0


/- Theorem 1.1
  Subspaces of ℝⁿ containing the origin are affine sets.
  Main statement: a subspace of Rⁿ is equivalent to an affine set containing 0. -/
theorem affinespace_iff_subspace (s : Set E) :
  (∃ (V : Submodule ℝ E), s = V) ↔ ((∃ (p : AffineSubspace ℝ E), s = p) ∧ (0 : E) ∈ s) := by
  constructor
  · rintro ⟨V, rfl⟩
    exact ⟨subspace_is_affinesubspace V, V.zero_mem⟩
  rintro ⟨⟨p, hp⟩, h0⟩
  have h0p : (0 : E) ∈ (p : Set E) := hp ▸ h0
  rcases affine_of_subspace p (h0p) with ⟨V, hV⟩
  use V; rw [hp, hV]


end Thm_1_1

section Thm_1_2

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Module ℝ E]

/- Translations of affine sets are affine. -/
lemma affine_translation (s : AffineSubspace ℝ E) (a : E) :
  ∃ (t : AffineSubspace ℝ E), (· + a) '' s = t := by
  use a +ᵥ s; ext z
  constructor <;> intro h
  · rcases h with ⟨x, hx, heq⟩
    change x + a = z at heq
    simp only [coe_pointwise_vadd]
    rw [← heq, add_comm,Set.mem_vadd_set]
    exact ⟨x, ⟨hx, rfl⟩⟩
  · rcases h with ⟨x, hx, heq⟩
    use x
    exact ⟨hx, (by simp only [add_comm]; exact heq)⟩



/- Theorem 1.2
Every nonempty affine set M is parallel to a unique subspace L, and L = M - M. -/
theorem unique_parallel_subspace (s : AffineSubspace ℝ E) (hs : s ≠ (∅ : Set E)) :
  ∃ (L : Submodule ℝ E) , ∃ (a : E), (· + a) '' s = L ∧ (L : Set E) = s - s := by
  use s.direction
  have h_nonempty : s.1.Nonempty := by
    rwa [Set.nonempty_iff_ne_empty]
  rcases h_nonempty with ⟨y, hy⟩
  use - y; constructor
  · ext z; constructor <;> intro h
    · rcases h with ⟨x, hx, heq⟩
      dsimp at heq
      rw [← sub_eq_add_neg] at heq
      rw [← heq]
      exact vsub_mem_direction hx hy
    · change z ∈ s.direction at h
      use z + y
      exact ⟨vadd_mem_of_mem_direction h hy, by simp only [add_neg_cancel_right]⟩
  exact coe_direction_eq_vsub_set (nonempty_of_mem hy)


end Thm_1_2

section Thm_1_3
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Module ℝ F]

/- Theorem 1.3
Given β ∈ ℝ and nonzero b ∈ R, the set H = {x | ⟪x, b⟫ = β}
is a hyperplane in Rⁿ. Moreover, every hyperplane can be represented this way,
and b is unique up to a common nonzero scalar multiple. -/
theorem solution_space_of_linear_system_is_affine [Module ℝ E] (b : F) (A : E →ₗ[ℝ] F) :
∃ (H : AffineSubspace ℝ E), H = { x | A x = b} := by
  let H : AffineSubspace ℝ E :=
    { carrier := {x | A x = b}
      smul_vsub_vadd_mem := by
        simp only [mem_setOf_eq]
        intro _ _ _ _  hp1 hp2 hp3
        rw [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub,
        hp1, hp2, hp3, sub_self, smul_zero, zero_add]}
  use H ; rfl


/- A hyperplane is an affine set. -/
theorem hyperplane_affinesubspace [Module ℝ E] (g : E →ₗ[ℝ] ℝ) (c : ℝ) :
  ∃ (H : AffineSubspace ℝ E), H = {x | g x = c} := solution_space_of_linear_system_is_affine c g



variable [InnerProductSpace ℝ E]

/- The hyperplane defined by an inner product is an affine set. -/
theorem innerProduct_is_affinesubspace (β : E) (b : ℝ) :
  ∃ (H : AffineSubspace ℝ E), H = {x | ⟪x, β⟫ = b} := by
  refine ⟨{
    carrier := {x | ⟪x, β⟫ = b}
    smul_vsub_vadd_mem := by
      intro c p₁ p₂ p₃ h₁ h₂ h₃
      change ⟪c • (p₁ -ᵥ p₂) +ᵥ p₃, β⟫ = b
      simp [vsub_eq_sub, vadd_eq_add, smul_sub]
      rw [inner_add_left, inner_sub_left]
      simp_rw [real_inner_smul_left]
      rw [h₁, h₂, h₃]
      ring
  }, rfl⟩


end Thm_1_3


section Thm_1_4

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Module ℝ E] [Module ℝ F]

/- Thm 1.4, Part 1: the solution set of A x = b is an affine set. -/
#check solution_space_of_linear_system_is_affine


/- Thm 1.4 (matrix version), Part 1: the solution set of A x = b is an affine set. -/
theorem solution_space_of_linear_system_is_affine' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ) : ∃ (p : AffineSubspace ℝ (Fin n → ℝ)),
  (p : Set (Fin n → ℝ)) = {x | A.mulVec x = b} := by
  rw [show {x | A.mulVec x = b} = {x | (Matrix.toLin' A) x = b} by rfl]
  exact solution_space_of_linear_system_is_affine b (Matrix.toLin' A)


/- Thm 1.4 (matrix version), Part 2: any affine set can be written as {x | A x = b}. -/

lemma exists_matrix_representing_submodule_as_kernel (n : ℕ)
  (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
    (L : Set (EuclideanSpace ℝ (Fin n))) = {x | A.mulVec x = 0} := by
  let L_orth := L.orthogonal
  let m := finrank ℝ L_orth
  let B := finBasis ℝ L_orth
  let A : Matrix (Fin m) (Fin n) ℝ := fun i j => (B i).val j
  use m, A
  ext x
  simp only [SetLike.mem_coe]
  calc
    _ ↔ x ∈ L_orth.orthogonal := by rw [Submodule.orthogonal_orthogonal L]
    _ ↔ ∀ i, ⟪x, (B i).val⟫ = 0 := by
      constructor <;> intro h
      · exact fun i ↦ inner_eq_zero_symm.mp (h (↑(B i)) (Submodule.coe_mem (B i)))
      · rw [Submodule.mem_orthogonal]
        intro y hy
        rw [inner_eq_zero_symm, ← Subtype.coe_mk y hy, ← Basis.sum_repr B ⟨y, hy⟩]
        simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
        simp_rw [inner_sum, inner_smul_right, h,mul_zero, Finset.sum_const_zero]
    _ ↔ x ∈ {x | A.mulVec x = 0} := by
      change (∀ (i : Fin (finrank ℝ ↥L_orth)), ⟪x, ↑(B i)⟫ = 0) ↔ A.mulVec x = 0
      rw [funext_iff]
      apply forall_congr'
      simp only [Pi.zero_apply]
      exact fun i ↦ Iff.symm (AddSemiconjBy.eq_zero_iff ⟪x, ↑(B i)⟫ rfl)


theorem affine_representation_of_linear_system' (n : ℕ)
  (H : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) :∃ (m : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
  {x: (EuclideanSpace ℝ (Fin n)) | A.mulVec x = b} = H := by
  by_cases h_empty: (H : Set (EuclideanSpace ℝ (Fin n)) ) = ∅
  · use 1, 0, fun _ => 1
    rw [h_empty]
    simp only [Matrix.zero_mulVec, funext_iff, Pi.zero_apply, zero_ne_one,forall_const, setOf_false]
  by_cases h_univ : (H: Set (EuclideanSpace ℝ (Fin n))) = univ
  · use 0, default, default
    rw [h_univ]
    simp only [Matrix.empty_mulVec, Pi.default_def, funext_iff, IsEmpty.forall_iff, setOf_true]
  let L := H.direction
  rcases exists_matrix_representing_submodule_as_kernel n L with ⟨m, A, h_L_eq_ker_A⟩
  have h_nonempty : (H : Set (EuclideanSpace ℝ (Fin n))).Nonempty := by
    rwa [Set.nonempty_iff_ne_empty]
  rcases h_nonempty with ⟨a, a_mem_H⟩
  let b := A.mulVec a; use m, A, b; ext x
  calc
    A.mulVec x = b ↔ A.mulVec x = A.mulVec a := by simp only [b]
    _ ↔ A.mulVec (x - a) = 0 := by rw [Matrix.mulVec_sub, sub_eq_zero]
    _ ↔ x - a ∈ L := by
      rw [← SetLike.mem_coe, h_L_eq_ker_A]
      exact Eq.to_iff rfl
    _ ↔ x ∈ H := by
      constructor
      · intro h_vsub_in_L
        exact (vsub_right_mem_direction_iff_mem a_mem_H x).mp h_vsub_in_L
      · intro h_x_in_H
        exact H.vsub_mem_direction h_x_in_H a_mem_H

/- Thm 1.4, Part 2: any affine set can be written as {x | A x = b}. -/
variable [FiniteDimensional ℝ E] in
theorem affine_representation_of_linear_system : ∀ (H : AffineSubspace ℝ E),
  ∃ (F : Type) (_ : AddCommGroup F) (_ : Module ℝ F) (_ : FiniteDimensional ℝ F)
    (A : E →ₗ[ℝ] F) (b : F), {x | A x = b} = H := by
  intro H
  let n := finrank ℝ E
  let e := LinearEquiv.ofFinrankEq E (EuclideanSpace ℝ (Fin n))
    (by exact Eq.symm finrank_euclideanSpace_fin)
  let H' : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)) := H.comap (e.toAffineEquiv.symm.toAffineMap)
  rcases affine_representation_of_linear_system' n H' with ⟨m, A', b', h_eq⟩
  let A : E →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := (Matrix.toLin' A').comp e.toLinearMap
  refine ⟨EuclideanSpace ℝ (Fin m), inferInstance, inferInstance, inferInstance, A, b', ?_⟩
  ext x
  simp only [mem_setOf_eq, SetLike.mem_coe]
  calc
    A x = b' ↔ (Matrix.toLin' A') (e x) = b' := by
      simp only [A]; rfl
    _ ↔ A'.mulVec (e x) = b' := by
      rw [Matrix.toLin'_apply]
    _ ↔ e x ∈ H' := by
      rw [← mem_coe, ← h_eq, Set.mem_setOf_eq]
    _ ↔ x ∈ H := by
      simp only [H', AffineSubspace.mem_comap, AffineEquiv.coe_toAffineMap]
      rw [← LinearEquiv.coe_toAffineEquiv e, AffineEquiv.symm_apply_apply]


#check Matrix

/- Cor 1.4.1: an affine set can be represented as an intersection of hyperplanes. -/
theorem affine_is_iInter_of_hyperplane (p : AffineSubspace ℝ E) :
  ∃ (ι : Type*) (g : ι → E →L[ℝ] ℝ)
  (c : ι → ℝ) , ⋂ (i : ι), {x | (g i) x = (c i)} = p := by sorry



/- Cor 1.4.1: (possibly requiring finite dimension) every affine subset is an intersection
of finitely many hyperplanes. -/
variable [FiniteDimensional ℝ E] in
theorem affine_is_iInter_of_finite_hyperplane (p : AffineSubspace ℝ E) :
  ∃ (n : ℕ ) (g : Fin n → E →L[ℝ] ℝ) (c : Fin n → ℝ),
  ⋂ (i : Fin n), {x | (g i) x = (c i)} = p := by
  by_cases h : p = ⊥
  · refine ⟨1, fun _ => 0, fun _ => 1, ?_⟩
    ext x
    simp only [ContinuousLinearMap.zero_apply, zero_ne_one, setOf_false, mem_iInter,
      mem_empty_iff_false, forall_const, h, bot_coe]
  · sorry




/- Cor 1.4.1 (matrix version): every affine subset is an intersection of finitely many hyperplanes. -/
theorem affine_as_intersection_of_hyperplanes {n : ℕ} (p : AffineSubspace ℝ (Fin n → ℝ)) :
    ∃ (k : ℕ) (A : Matrix (Fin k) (Fin n) ℝ) (b : Fin k → ℝ),
      (p : Set (Fin n → ℝ)) = ⋂ (i : Fin k), {x | (A.mulVec x) i = b i} := by
  let p' : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)) := p
  rcases affine_representation_of_linear_system' n p' with ⟨k, A, b, h⟩
  use k, A, b
  have : (p : Set (Fin n → ℝ)) = (p' : Set (EuclideanSpace ℝ (Fin n))) := rfl
  rw [this, h.symm]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  exact ⟨fun h i => congr_fun h i, fun h => funext h⟩



/- Arbitrary intersections of affine sets are affine. -/
theorem iInter_affineSubspace {ι : Type*} {s : ι → AffineSubspace ℝ E} :
  ∃ (p : AffineSubspace ℝ E), (p : Set E) = ⋂ (i : ι), s i := by
  let p : AffineSubspace ℝ E := sInf (Set.range s)
  refine ⟨p, ?_⟩
  rw [AffineSubspace.coe_sInf, Set.biInter_range]



/- The minimal affine set containing s is called the affine hull of s. -/
#check affineSpan_eq_sInf

/- The affine hull of s equals the set of all affine combinations of s, by mutual inclusion. -/
/- Affine hull ⊆ set of affine combinations. -/
#check eq_affineCombination_of_mem_affineSpan


/- Set of affine combinations ⊆ affine hull. -/
#check affineCombination_mem_affineSpan

end Thm_1_4

section Thm_1_5
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Module ℝ E] [Module ℝ F]

#check AffineMap

/- From the library definition of AffineMap, Tx = Ax + a, one can derive the book's definition:
T ((1 - r) • x + r • y) = (1 - r) • T x + r • T y. -/
theorem affine_map_representation (T : AffineMap ℝ E F) :-- (T : E →ᵃ[ℝ] F) :
   ∀ (x y : E) (r : ℝ),T ((1 - r) • x + r • y) = (1 - r) • T x + r • T y := by
  intro x y r
  rw [show (1 - r) • x + r • y = x +ᵥ r • (y -ᵥ x) by
    simp [smul_sub, sub_smul, one_smul]; abel]
  rw [T.map_vadd]
  simp
  have h : ∀ (z : E), T z = T.linear z + T 0 := by
    intro z
    calc
      T z = T (z +ᵥ (0 : E)) := by simp only [vadd_eq_add, add_zero]
      _ = T.linear z + T 0 := by rw [T.map_vadd, vadd_eq_add]
  rw [h (r • (y - x)), T.linear.map_smul r (y - x), ← vsub_eq_sub, T.linearMap_vsub y x]
  simp[← add_assoc, add_comm, h x, vsub_eq_sub, smul_sub, sub_smul]
  abel

/- From the book's definition of AffineMap,
T ((1 - r) • x + r • y) = (1 - r) • T x + r • T y,
one can derive the library definition Tx = Ax + a. -/
theorem affine_map_representation_inv (T : E → F)
    (h : ∀ (x y : E) (r : ℝ), T ((1 - r) • x + r • y) = (1 - r) • T x + r • T y) :
    ∃ (A : AffineMap ℝ E F), A = T := by
  let o : E := Classical.arbitrary E
  refine ⟨
    { toFun := T
      linear := {
        toFun := fun v => T (v +ᵥ o) -ᵥ T o
        map_add' := by
          intro x y
          have h1 := h (x +ᵥ o) (y +ᵥ o) (1/2)
          have left_eq : (1 - (1/2 : ℝ)) • (x +ᵥ o) + (1/2 : ℝ) •
              (y +ᵥ o) = ((1/2 : ℝ) • (x + y)) +ᵥ o := by
            calc
              (1 - (1/2 : ℝ)) • (x +ᵥ o) + (1/2 : ℝ) • (y +ᵥ o) =
                (1/2 : ℝ) • ((x +ᵥ o) + (y +ᵥ o)) := by ring_nf; rw [smul_add]
              _ = (1/2 : ℝ) • (x + y + (2 : ℝ) • o) := by
                  rw [show (x +ᵥ o) + (y +ᵥ o) = x + y + (o + o) by
                          rw [vadd_eq_add, vadd_eq_add]
                          abel]
                  rw [show o + o = (2 : ℝ) • o by rw [two_smul]]
              _ = (1/2 : ℝ) • (x + y) + (1 : ℝ) • o := by rw [smul_add, ← mul_smul]; norm_num
              _ = ((1/2 : ℝ) • (x + y)) +ᵥ o := by rw [one_smul]; rfl
          rw [left_eq] at h1
          simp at h1 ⊢
          have h2 := h (((1/2 : ℝ) • (x + y)) +ᵥ o) o (2 : ℝ)
          simp at h2
          rw [h1] at h2
          simp at h2 ⊢
          sorry
        map_smul' := by
          intro r x
          have h1 := h o (x +ᵥ o) r
          have left_eq : (1 - r) • o + r • (x +ᵥ o) = (r • x) +ᵥ o := by
            calc
            (1 - r) • o + r • (x +ᵥ o) = (1 - r) • o + (r • x + r • o) := by
               rw [vadd_eq_add, smul_add]
            _ = ((1 - r) + r) • o + r • x := by rw [add_smul]; abel
            _ = (1 : ℝ) • o + r • x := by ring_nf
            _ = o + r • x := by rw [one_smul]
            _ = (r • x) +ᵥ o := by rw [vadd_eq_add,add_comm]
          rw [left_eq] at h1
          simp at h1 ⊢
          rw [h1]
          calc
            ((1 - r) • T o + r • T (x +ᵥ o)) -ᵥ T o
                = ((1 - r) • T o + r • T (x +ᵥ o)) - T o := by rw [vsub_eq_sub]
            _ = -r • T o + r • T (x +ᵥ o) := by
                simp [vadd_eq_add, sub_smul, one_smul]
                abel
            _ = r • (T (x +ᵥ o) - T o) := by
                simp [neg_smul, smul_sub]
                abel
            _ = r • (T (x +ᵥ o) -ᵥ T o) := by rw [vsub_eq_sub]
      }
      map_vadd' := by
        intro p v
        have h1 := h p (v +ᵥ p) 1
        simp only [sub_self, zero_smul, vadd_eq_add, smul_add, one_smul, zero_add, vsub_eq_sub,
          LinearMap.coe_mk, AddHom.coe_mk] at h1 ⊢
        have :T (v + o) = T v + T o := by
          sorry
        calc
        _ =  T (v + o - o ) + T p := by
          simp only [add_sub_cancel_right]
          sorry
        _ = T v + T p := by sorry
        _ = _ := by sorry
    },
    rfl⟩

/- Theorem 1.5
Every affine map from Rⁿ to Rᵐ has the form Tx = Ax + a, where A is linear and a ∈ Rᵐ. -/
theorem affinemap_eq_def (T : E → F) :
    ∃ (A : AffineMap ℝ E F), A = T  ↔ ∀ (x y : E) (r : ℝ),
    T ((1 - r) • x + r • y) = (1 - r) • T x + r • T y := by
  by_cases h : ∀ (x y : E) (r : ℝ), T ((1 - r) • x + r • y) = (1 - r) • T x + r • T y
  · rcases affine_map_representation_inv T h with ⟨A, hA⟩
    refine ⟨A, ?_⟩
    constructor
    · intro hEq x y r
      rw [← hEq]
      exact affine_map_representation A x y r
    · exact fun a ↦ hA
  · let A : AffineMap ℝ E F := {
      toFun := fun _ => 0
      linear := 0
      map_vadd' := by simp only [LinearMap.zero_apply, vadd_eq_add, add_zero, implies_true]}
    refine ⟨A, ?_⟩
    constructor
    · intro hEq
      exfalso
      apply h
      intro x y r
      rw [← hEq]
      exact affine_map_representation A x y r
    · exact fun a ↦ False.elim (h a)




#check AffineEquiv
/- If an affine map is invertible, its inverse is affine. -/
theorem affine_map_inverse_is_affine (T : E →ᵃ[ℝ] F) (h_bij : Function.Bijective T) :
  ∃ (S : F →ᵃ[ℝ] E), S ∘ T = id ∧ T ∘ S = id := by
  let inv_fun : F → E := Function.invFun T
  have left_inv : LeftInverse inv_fun T := Function.leftInverse_invFun h_bij.injective
  have right_inv : RightInverse inv_fun T := Function.rightInverse_invFun h_bij.surjective
  have h : ∀ (x y : F) (r : ℝ), inv_fun ((1 - r) • x + r • y)
      = (1 - r) • inv_fun x + r • inv_fun y := by
    intro x y r
    calc
      _ = inv_fun ((1 - r) • T (inv_fun x) + r • T (inv_fun y)) := by rw [right_inv x, right_inv y]
      _ = inv_fun (T ((1 - r) • inv_fun x + r • inv_fun y)) := by
        rw [affine_map_representation T (inv_fun x) (inv_fun y) r]
      _ = _ := left_inv _

  rcases affinemap_eq_def inv_fun with ⟨S, hS_def⟩
  have hS_eq : S = inv_fun := (hS_def.mpr h)
  exact ⟨S, by ext x; simp [hS_eq, left_inv x], by ext y; simp [hS_eq, right_inv y]⟩


/- If T : Rⁿ → Rᵐ is affine, then for any affine set M ⊆ Rⁿ,
the image T M = {T x | x ∈ M} is affine in Rᵐ. -/
theorem affinesubspace_img_affinesubspace (T : E →ᵃ[ℝ] F) (M : AffineSubspace ℝ E) :
∃ (H : AffineSubspace ℝ F), H = T ''M := ⟨AffineSubspace.map T M, rfl⟩


#check affineSpan
/- In particular, affine maps preserve affine hulls: aff(TS) = T(aff S). -/
theorem affineSpan_conser (s : Set E) (T : E →ᵃ[ℝ] F) :
affineSpan ℝ  (T ''s)  = T ''(affineSpan ℝ s) := by
  apply Set.Subset.antisymm
  · intro x hx
    have : affineSpan ℝ (T '' s) ≤ (affineSpan ℝ s).map T :=
      affineSpan_le.mpr fun x' ⟨y, hy, h⟩ => h ▸ ⟨y, subset_affineSpan ℝ s hy, rfl⟩
    exact this hx
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have : (affineSpan ℝ s).map T ≤ affineSpan ℝ (T '' s) := by
      apply AffineSubspace.map_le_iff_le_comap.mpr ?_
      apply affineSpan_le.mpr
      intro y hy
      change y ∈ (affineSpan ℝ (T '' s)).comap T
      rw [AffineSubspace.mem_comap]
      apply subset_affineSpan ℝ (T '' s)
      exact ⟨y, hy, rfl⟩
    exact this (AffineSubspace.mem_map.mpr ⟨y, hy, rfl⟩)

end Thm_1_5

section Thm_1_6

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Module ℝ E]
#check LinearIndependent
#check AffineIndependent
#check Bijective

/- If {b₀,...,bₘ} and {b₀',...,bₘ'} are affinely independent in ℝⁿ, then there exists
an affine bijection T of ℝⁿ such that Tbᵢ = bᵢ' for i = 0,...,m. -/
theorem affine_map_between_affineindependent_set
  (m : ℕ) (a b : Fin (m + 1) → E)
  (ha : AffineIndependent ℝ a) (hb : AffineIndependent ℝ b) :
  ∃ (T : E →ᵃ[ℝ] E), ∀ i, T (a i) = T (b i) ∧ Bijective T := by
  sorry

#check finrank

/- If m = n, then T is unique. -/
theorem affine_map_between_affineindependent_set_only
  (n : ℕ) (a b : Fin (n + 1) → E) (hr : finrank ℝ E = n)
  (ha : AffineIndependent ℝ a) (hb : AffineIndependent ℝ b) :
  ∃! (T : E →ᵃ[ℝ] E), ∀ i, T (a i) = T (b i) ∧ Bijective T := by
  sorry

/- Corollary 1.6.1 -/
/- If M₁ and M₂ are affine sets in ℝⁿ of the same dimension, then there exists
an affine bijection T of ℝⁿ such that T M₁ = M₂. -/
theorem affine_nap_between_same_rank_affine_sets
  (M₁ M₂ : AffineSubspace ℝ E) (hr : finrank ℝ M₁.direction = finrank ℝ M₂.direction) :
  ∃ (T : E →ᵃ[ℝ] E), (AffineSubspace.map T M₁ = M₂) ∧ Bijective T := by
  sorry


end Thm_1_6

section TuckerRepresentation

variable {n m : ℕ} (E : Type*) [AddCommGroup E] [Module ℝ E]

lemma tucker_representation_of_subspace_is_homogeneous
    (B : Basis (Fin (n + m)) ℝ E)
    (S : Submodule ℝ E)
    (c : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hS : ∀ (v : E), v ∈ S ↔
          let ξ_dep := fun (i : Fin m) => (B.repr v) (Fin.natAdd n i)
          let ξ_indep := fun (j : Fin n) => (B.repr v) (Fin.castAdd m j)
          ξ_dep = c + A.mulVec ξ_indep) :
    c = 0 := by
    have h_zero_mem : (0 : E) ∈ S := S.zero_mem
    have h_zero_eq := (hS 0).mp h_zero_mem
    have h_repr_zero : B.repr 0 = 0 := LinearEquiv.map_zero B.repr
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at h_zero_eq
    change 0 = c + A.mulVec 0 at h_zero_eq
    simp only [Matrix.mulVec_zero, add_zero] at h_zero_eq
    exact h_zero_eq.symm
end TuckerRepresentation

/-
variable {P: Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

open Matrix Submodule

lemma tucker_representation_of_orthogonal_with_basis
    (B : OrthonormalBasis (Fin (n + m)) ℝ P)
    (L : Submodule ℝ P)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hL : ∀ (v : P), v ∈ L ↔
          (let ξ_dep := fun (i : Fin m)  => (B.repr v) (Fin.natAdd n i)
           let ξ_indep := fun (j : Fin n) => (B.repr v) (Fin.castAdd m j)
           ξ_dep = A.mulVec ξ_indep)) :
    ∀ (u : P), u ∈ L.orthogonal ↔
      let ξ_star_dep := fun (i : Fin m)  => (B.repr u) (Fin.natAdd n i)
      let ξ_star_indep := fun (j : Fin n) => (B.repr u) (Fin.castAdd m j)
      A.transpose.mulVec ξ_star_dep = -ξ_star_indep := by
      intro u
      let ξ_star_dep := fun i ↦ B.repr u (Fin.natAdd n i)
      let ξ_star_indep := fun j ↦ B.repr u (Fin.castAdd m j)
      constructor
      intro h_orth
      rw [Submodule.mem_orthogonal] at h_orth
      funext j
      simp only [Pi.neg_apply]
      apply eq_neg_of_add_eq_zero_right
      let ξ_indep_test : Fin n → ℝ := Pi.single j 1
      let ξ_dep_test := A.mulVec ξ_indep_test
      let v := B.repr.symm (Fin.addCases ξ_indep_test ξ_dep_test)
      have hv_in_L : v ∈ L := by
        rw [hL]
        simp


        --simp [Fin.addCases_castAdd, Fin.addCases_natAdd, ξ_dep_test]
        sorry



      sorry


      sorry


#check Fin.castAdd_cast
#check Fin.addCases-/













/-
-- (h_partition : Disjoint I D ∧ I ∪ D = Finset.univ) -- this partition assumption is necessary
theorem tucker_representation_of_subspace_is_linear1
    (L : Submodule ℝ E) (e : E ≃ₗ[ℝ] (Fin n → ℝ))
    (I D : Finset (Fin n)) (f : (I → ℝ) →ᵃ[ℝ] (D → ℝ))
    (h_graph : ∀ (x : E),
    x ∈ L ↔ (fun (i : D) => (e x) i) = f (fun (i : I) => (e x) i)) :
    f 0 = 0 := by
    have h_graph_at_zero := h_graph 0
    simp only [zero_mem, map_zero, Pi.zero_apply, true_iff] at h_graph_at_zero
    funext i
    exact congrFun (id (Eq.symm h_graph_at_zero)) i


variable {K : Type*} [Field K]
/--
Theorem 1: the affine representation of a linear subspace is linear.
If a linear subspace L (Submodule) is the image of an affine map f,
then f must be linear (i.e., f(0) = 0).
-/
--    (h_partition : Disjoint I D ∧ I ∪ D = Finset.univ)
theorem tucker_representation_of_subspace_is_linear2
    (L : Submodule K (EuclideanSpace K (Fin n)))
    (I D : Finset (Fin n))
    (f : (I → K) →ᵃ[K] (D → K))
    (h_graph : ∀ (x : EuclideanSpace K (Fin n)),
      x ∈ L ↔ (fun (i : D) => x i) = f (fun (i : I) => x i)) :
    f 0 = 0 := by
  have h_graph_at_zero := h_graph 0
  simp only [zero_mem, true_iff] at h_graph_at_zero
  funext i
  exact congrFun (id (Eq.symm h_graph_at_zero)) i

/--
Theorem 2 (coordinate version): representation of the orthogonal complement.
If a linear subspace L (in EuclideanSpace) is the image of a linear map A (on coordinates),
then its orthogonal complement L.orthogonal is the image of the negative adjoint (-A.adjoint),
and the indices of independent/dependent variables are swapped.
[InnerProductSpace ℝ ((i : I) → ℝ)]
    [InnerProductSpace ℝ  ((i : D) → ℝ)]noncomputable(- (LinearMap.adjoint A))
-/
theorem tucker_representation_of_orthogonal_complement
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (I D : Finset (Fin n))
    (h_partition : Disjoint I D ∧ I ∪ D = Finset.univ)
    (A : (EuclideanSpace ℝ I) →ᵃ[ℝ] (EuclideanSpace ℝ D))
    (h_graph : ∀ (x : EuclideanSpace ℝ (Fin n)),
      x ∈ L ↔ (fun (i : D) => x i) = A (fun (i : I) => x i)) :
    (∀ (y : EuclideanSpace ℝ (Fin n)),
    y ∈ L.orthogonal ↔ (fun (i : D) => y i) =
      (- (LinearMap.adjoint A)) (fun (i : I) => y i)) := by
      sorry
-/





/-
section TuckerRepresentation

variable {n : ℕ}
variable {K : Type*} [Field K]

/- Tucker representation -/
structure TuckerRepresentation (M : AffineSubspace K (EuclideanSpace K (Fin n)))
     where
  independent_indices : Finset (Fin n)
  dependent_indices   : Finset (Fin n)
  is_partition : Disjoint independent_indices dependent_indices ∧
                 independent_indices ∪ dependent_indices = Finset.univ
  f : (independent_indices → K) →ᵃ[K] (dependent_indices → K)
  M_eq_graph : ∀ (x : EuclideanSpace K (Fin n)),
    x ∈ M ↔ (fun (i : dependent_indices) => x i) = f (fun (i : independent_indices) => x i)




section ExampleVerification

def P_carrier : Set (EuclideanSpace ℝ (Fin 3)) :=
  { p | p 0 + p 1 + p 2 = 1 }

def P_example : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  { carrier := P_carrier
    smul_vsub_vadd_mem := by
      intro c p1 p2 p3 hp1 hp2 hp3
      simp only [vsub_eq_sub, vadd_eq_add]
      unfold P_carrier at *
      simp only [Fin.isValue, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
        smul_eq_mul]
      calc
      _ = c * ((p1 0 + p1 1 + p1 2) - ( p2 0 + p2 1 +  p2 2))
        + (p3 0 + p3 1 + p3 2)  := by linarith!
      _ = c * (1 - 1) + 1 := by rw [hp1, hp2, hp3]
      _ = 1 := by ring
 }

def P_independent_indices : Finset (Fin 3) := {1, 2}
def P_dependent_indices : Finset (Fin 3) := {0}

/-theorem P_indices_are_partition :
    Disjoint P_independent_indices P_dependent_indices ∧
    P_independent_indices ∪ P_dependent_indices = Finset.univ := by
  native_decide-/

noncomputable def P_f_linear_part :
    ({x // x ∈ P_independent_indices} → ℝ) →ₗ[ℝ] ({x // x ∈ P_dependent_indices} → ℝ) :=
  -- Use `LinearMap.pi` to build the output vector.
  -- Since the output vector has only one component (at index 0),
  -- we only need to define how to compute that component.
  -- The underscore `_` in `fun _ => ...` means "any output component" (only 0 here).
  LinearMap.pi fun _ =>
    -- This component is given by -p₁ - p₂.
    -- We use the component extractor `proj` to build this expression.
    - (LinearMap.proj ⟨1, by simp [P_independent_indices]⟩)
      - (LinearMap.proj ⟨2, by simp [P_independent_indices]⟩)


-- Constant/translation part: a vector on {0} with value 1.
def P_f_const_part : {x // x ∈ P_dependent_indices} → ℝ :=
  fun _ => 1

-- Combine the linear and constant parts into a full affine map f.
noncomputable def P_f : ({x // x ∈ P_independent_indices} → ℝ)
   →ᵃ[ℝ] ({x // x ∈ P_dependent_indices} → ℝ) := {
  linear := P_f_linear_part,
  toFun := fun v => P_f_linear_part v + P_f_const_part,
  map_vadd' := by
    intro p v
    simp only [vadd_eq_add, map_add]
    exact add_assoc (P_f_linear_part v) (P_f_linear_part p) P_f_const_part }


noncomputable def P_tucker_representation : TuckerRepresentation P_example := {
  independent_indices := P_independent_indices,
  dependent_indices   := P_dependent_indices,
  is_partition        := by native_decide,
  f                   := P_f,
  M_eq_graph          := by
    intro x
    simp only [P_example, P_carrier]
    constructor <;> intro h
    simp only [Fin.isValue] at h
    have : x 0 + x 1 + x 2 = 1 := h
    unfold P_f
    simp only [AffineMap.coe_mk]
    funext i
    simp only [P_f_linear_part, P_f_const_part, LinearMap.pi_apply, Pi.add_apply]
    simp only [Fin.isValue, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.coe_proj, eval]
    fin_cases i
    simp only [Finset.mem_val, Fin.isValue]
    linarith
    change x 0 + x 1 + x 2 = 1
    simp [P_f, P_f_linear_part] at h
    have h_algebraic := congr_fun h ⟨0, by simp [P_dependent_indices]⟩
    simp only [P_f_const_part, Pi.add_apply, LinearMap.pi_apply] at h_algebraic
    simp only [Fin.isValue, LinearMap.sub_apply,
      LinearMap.neg_apply, LinearMap.coe_proj, eval] at h_algebraic
    linarith
}

end ExampleVerification


#check Matrix

--(h_nontrivial : M ≠ ⊥ ∧ M ≠ ⊤)
theorem exists_tucker_representation (M : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) :
Nonempty (TuckerRepresentation M) := by
  sorry

theorem exists_tucker_representation'
    (M : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
    (h_dim_pos : 0 < finrank ℝ M.direction)
    (h_dim_lt_top : finrank ℝ M.direction < n) :
    Nonempty (TuckerRepresentation M) := by
  sorry

/--
For a fixed variable partition (i.e., fixed independent/dependent index sets),
the affine map `f` in the Tucker representation of an affine set M is unique.
Note: since the type of f depends on the index set, we use the heterogeneous equality `HEq`.
-/
theorem tucker_representation_map_is_unique
    (M : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
    (T₁ T₂ : TuckerRepresentation M)
    (h_partition_eq : T₁.independent_indices = T₂.independent_indices) :
    HEq T₁.f T₂.f := by
  sorry


/--
For a fixed affine set M, the type of all possible Tucker representations is finite.
We prove this by constructing a `Fintype` instance.
-/
instance finite_tucker_representations
    (M : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) :
    Fintype (TuckerRepresentation M) := by
  sorry

/--
If an affine set is a vector subspace L, then in any Tucker representation
the core affine map `f` is linear (i.e., it maps the zero vector to zero).
-/
theorem tucker_representation_of_subspace_is_linear
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (T : TuckerRepresentation L.toAffineSubspace) :
    T.f 0 = 0 := by
  sorry

/--
A Tucker representation of a vector subspace `L` can be used to construct a Tucker
representation of its orthogonal complement `Lᗮ`.
The new representation swaps the independent/dependent indices, and the core linear map
is the negative adjoint (`-A.adjoint`) of the original map.
-/
theorem tucker_representation_of_orthogonal_complement
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (T : TuckerRepresentation L.toAffineSubspace) :
    -- Use let...in inside the ∀ for readability.
    ∀ (y : EuclideanSpace ℝ (Fin n)),
      let A := (AffineMap.linear T.f :
        ({x // x ∈ T.independent_indices} → ℝ) →ₗ[ℝ] ({x // x ∈ T.dependent_indices} → ℝ)) in
      y ∈ Lᗮ ↔ (fun (i : T.independent_indices) => y i) =
        ((- (LinearMap.adjoint A)).toAffineMap) (fun (i : T.dependent_indices) => y i) := by
  sorry
-/
