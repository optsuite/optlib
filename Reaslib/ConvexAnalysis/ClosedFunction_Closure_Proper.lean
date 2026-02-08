import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Reaslib.ConvexAnalysis.ClosedFunction_Closure

open Filter Set Topology Function Module EReal Inner

/-
Mainly these four theorems:
intrinsicInterior_inclusion
intrinsicInterior_of_epigraph_subset
inter_nonempty
univ_convex_closure_intrinsicInterior

`linear_ri` is in intrinsicInterior (to be merged) under the name `linearMap_intrinsicInterior`.
The relative interior of a product is also included there, named `intrinsicInterior_prod_eq_prod_intrinsicInterior`.
The above theorem `intrinsicInterior_inclusion` is intended to be moved to relative interior too, so we do not reorganize it here.
There are a few errors below, likely due to missing imports; the proofs are a bit messy, but usable :)
-/


section cl_ccp_of_f_proper_convex
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

----------intrinsicInterior_inclusion-----------

lemma affineCoerce_Range [NontriviallyNormedField R] [NormedAddCommGroup α] [NormedSpace R α]
    {M : Set α} (neM : M.Nonempty) :
    range (affSpanCoerce R neM) = affineSpan R M := by
  change range (((↑) : (affineSpan R M) → α) ∘ (affSpanDirEquiv R neM).symm) = (affineSpan R M)
  rw [range_comp, Homeomorph.range_coe (affSpanDirEquiv R neM).symm]
  ext x; simp


lemma inv_image_eq_preimage [Nonempty α] {f : α → β} (s : Set β)
  (hi : Injective f) (hs : s ⊆ range f) : (invFun f) '' s = f ⁻¹' s := by
  ext x
  simp
  constructor
  · rintro ⟨y, hy⟩
    have : f (invFun f y) = y := Function.invFun_eq (hs hy.1)
    rw [← hy.2, this]
    exact hy.1
  intro hx
  have := hs hx
  use (f x)
  have : invFun f (f x) = x := by
    have : ((invFun f) ∘ f) x = x := by
      have := Function.leftInverse_invFun hi
      exact hi (congrArg f (hi (congrArg f (this x))))
    exact hi (congrArg f (hi (congrArg f this)))
  exact ⟨hx, this⟩


lemma intrinsicInterior_inclusion [NontriviallyNormedField R] [NormedAddCommGroup α]
  [NormedSpace R α] (M N : Set α) (ha : affineSpan R M = affineSpan R N) (hc : M ⊆ N)
  (ho : intrinsicInterior R M = M) : M ⊆ intrinsicInterior R N := by
  by_cases neN : ¬N.Nonempty
  · have : N = ∅ := not_nonempty_iff_eq_empty.mp neN
    have : M = ∅ := subset_eq_empty hc this
    rw [this]; simp
  push_neg at neN
  by_cases neM : ¬M.Nonempty
  · have : M = ∅ := not_nonempty_iff_eq_empty.mp neM
    rw [this]; simp
  push_neg at neM
  rw [intrinsicInterior_equiv R neN]
  let phiN := affSpanCoerce R neN
  let phiM := affSpanCoerce R neM
  have phiN_eq : (affSpanCoerce R neN) = phiN := rfl
  have phiM_Range : range phiM = affineSpan R M := affineCoerce_Range neM
  have phiN_Range : range phiN = affineSpan R N := affineCoerce_Range neN
  have subN : M ⊆ Set.range phiN := by
    rw [phiN_Range, ← ha]
    exact subset_affineSpan R M
  have inv_self (s) : (phiN) ⁻¹' ((phiN) '' s) = s := by
    refine Injective.preimage_image ?hf s
    exact AffineIsometry.injective (affSpanCoerce R neN)
  apply (Set.preimage_subset_preimage_iff subN).mp
  rw [phiN_eq, inv_self]
  have inc : (phiN) ⁻¹' M ⊆ ((phiN) ⁻¹' N) := fun ⦃a⦄ a_1 ↦ hc a_1
  have M_open' : IsOpen (phiM ⁻¹' M) := by
    rw [intrinsicInterior_equiv R neM] at ho
    have phiM_eq : (affSpanCoerce R neM) = phiM := rfl
    rw [phiM_eq] at ho
    have : phiM ⁻¹' (phiM '' interior (phiM ⁻¹' M)) = phiM ⁻¹' M := by
      exact congrArg (preimage phiM) ho
    have inv_self' (t) : (phiM) ⁻¹' ((phiM) '' t) = t := by
      exact Injective.preimage_image (AffineIsometry.injective (affSpanCoerce R neM)) t
    rw [inv_self'] at this
    exact interior_eq_iff_isOpen.mp this
  let psiM := (Function.invFun phiN) ∘ phiM
  -- let psiN := (Function.invFun phiM) ∘ phiN
  have M_eq' : phiN ⁻¹' M = psiM '' (phiM ⁻¹' M) := by
    unfold psiM
    rw [Set.image_comp]
    have : (phiM '' (phiM ⁻¹' M)) = M := by
      have : SurjOn phiM univ (affineSpan R M) := by
        rw [← phiM_Range]
        change (range phiM) ⊆ phiM '' univ
        simp
      rw [Set.SurjOn.image_preimage this (by exact subset_affineSpan R M)]
    rw [this, inv_image_eq_preimage]
    · exact AffineIsometry.injective phiN
    · rw [phiN_Range, ← ha]
      exact subset_affineSpan R M
  have psiM_isometry : Isometry (psiM) := by
    refine Isometry.of_dist_eq ?_
    intro x y
    unfold psiM
    simp
    have : dist x y = dist (phiM x) (phiM y) := by
      exact Eq.symm (AffineIsometry.dist_map phiM x y)
    rw [this]
    have (a) (haa : a ∈ affineSpan R N) : phiN (invFun (phiN) a) = a := by
      apply Function.invFun_eq
      apply Set.mem_range.mp
      rw [phiN_Range]
      exact haa
    have (a b) (ha : a ∈ affineSpan R N) (hb: b ∈ affineSpan R N) :
      dist (invFun (phiN) a) (invFun (phiN) b) = dist a b := by
      nth_rw 2 [← this a ha, ← this b hb]
      exact Eq.symm (AffineIsometry.dist_map phiN (invFun (⇑phiN) a) (invFun (⇑phiN) b))
    apply this
    · rw [← AffineSubspace.mem_coe, ← ha, ← phiM_Range]
      exact mem_range_self x
    · rw [← AffineSubspace.mem_coe, ← ha, ← phiM_Range]
      exact mem_range_self y
  have psiM_open : IsOpenEmbedding (psiM) := by
    refine (isOpenEmbedding_iff psiM).mpr ?_
    constructor
    · exact Isometry.isEmbedding psiM_isometry
    unfold psiM
    rw [@range_comp]
    rw [phiM_Range, ha]
    have : invFun phiN '' (affineSpan R N) = univ := by
      rw [inv_image_eq_preimage]
      · apply preimage_eq_univ_iff.mpr
        rw [phiN_Range]
      · exact AffineIsometry.injective phiN
      rw [phiN_Range]
    rw [this]
    simp
  have M_open : IsOpen (phiN ⁻¹' M) := by
    rw [M_eq']
    exact (IsOpenEmbedding.isOpen_iff_image_isOpen psiM_open).mp M_open'
  exact (IsOpen.subset_interior_iff M_open).mpr inc

end cl_ccp_of_f_proper_convex

section closed_convex_affinesup
variable [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → EReal}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]


#check Icc
#check Iio
#check Iic

theorem improper_convex_have_no_finite_point (f : E → EReal) (hp : ¬ ProperFunction univ f)
  (hc : ConvexOn ℝ univ f) :
     ∀ x ∈ intrinsicInterior ℝ (dom univ f), f x = ⊥ := by
    --  unfold ProperFunction at hp
    -- have f_not_top : ∃ x, f x ≠ ⊤ := by
    --   by_contra! h
    by_cases htop : ∀ x, f x = ⊤
    · have : dom univ f = ∅ := by
        simp [dom]
        ext x
        simp
        exact htop x
      rw [this]; simp
    push_neg at htop
    have : ∃ u, f u = ⊥ := by
      by_contra! h
      apply hp
      rw [properFunction_iff]
      constructor
      · exact fun x a ↦ Ne.bot_lt' fun a ↦ h x (id (Eq.symm a))
      right
      rcases htop with ⟨xx, htop⟩
      use xx
      constructor
      trivial
      exact Ne.lt_top' (id (Ne.symm htop))
    have ⟨u, hu⟩ := this
    have dom_nonempty: (dom univ f).Nonempty := by
      use u; simp [dom, hu]
    intro x hx
    have ⟨μ, hμ1, hμ2⟩ : ∃ μ:ℝ , μ > 1 ∧ (1 - μ) • u + μ • x ∈ dom univ f := by
      refine intrinsicInterior_forall_exist_of_intrinsicInterior ?_ hx u ?_
      exact dom_nonempty
      simp [dom, hu]
    let y := (1 - μ) • u + μ • x
    let lam : ℝ := μ⁻¹
    have hlam : lam > 0 ∧ lam < 1 := sorry
    have hxlam : x = (1 - lam) • u + lam • y := sorry
    have hfxleq : f x ≤ (1 - lam) * f u+ lam * f y := by
      rw [hxlam]
      simp [ConvexOn] at hc
      sorry
    by_cases hfy : f y = ⊥
    · rw [hu, hfy, ←EReal.coe_one, ←EReal.coe_sub] at hfxleq
      have : Real.toEReal (1 - lam) * ⊥ + Real.toEReal lam * ⊥ = ⊥ := sorry
      rw [this] at hfxleq
      simp at hfxleq
      exact hfxleq
    sorry

theorem lsc_improper_have_no_finite_point (f : E → EReal) (hp : ¬ ProperFunction univ f)
  (hc : ConvexOn ℝ univ f) (hf : LowerSemicontinuousOn f univ) :
     ∀ x, f x = ⊥ ∨ f x = ⊤ := sorry

theorem clf_improper_have_no_finite_point (f : E → EReal)
  (hp : ¬ ProperFunction univ (f.closure univ)) :
  ∀ x, f.closure univ x = ⊥ ∨ f.closure univ x = ⊤ := by
  intro x
  simp [Function.closure]
  split_ifs
  · sorry
  · left; simp
  right; simp
  -- have : LowerSemicontinuousOn (f.closure univ) univ := by
  --   -- apply?
  --   simp [Function.closure]
  --   split_ifs
  --   exact lowersemicontinuoushull_islowersemicontinuous f
    -- sorry
    -- sorry
    -- refine (LowerSemicontinuousOn_iff_IsClosed_epigraph_of_closed ?_).mpr ?_
    -- simp_rw
    -- refine (LowerSemicontinuousOn_iff_IsClosed_epigraph_of_closed ?_).mpr ?_
    -- exact

theorem inter_nonempty [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (C : Set (WithLp 2 (E × F))) (hc : Convex ℝ C) :
    ∀ y ∈ intrinsicInterior ℝ (D C), {(y, z) | z : F} ∩ intrinsicInterior ℝ C ≠ ∅ := by
  sorry
  -- rw [D_eq_projection,
  -- linear_ri C (ContinuousLinearMap.fst_WithLp2 E F) hc, ← D_eq_projection (ri C)]
  -- rintro y ⟨z, zh⟩
  -- rw [← nonempty_iff_ne_empty]
  -- exact ⟨(y, z), ⟨by simp, zh⟩⟩

--------------  univ_convex_closure_intrinsicInterior  ------------
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma Epi_eq (f : E → EReal) : f.Epi univ = f.Epi (dom univ f) := by
  ext x; unfold Epi; simp
  exact fun h ↦ lt_of_le_of_lt h (EReal.coe_lt_top x.2)

@[simp]
theorem Set.prod_eq_iff_eq' {α : Type u_1} {β : Type u_2} {s : Set α} {t t₁ : Set β}
 (hs : s.Nonempty) :
    s ×ˢ t = s ×ˢ t₁ ↔ t = t₁ := by
  have : s ≠ ∅ := nonempty_iff_ne_empty.mp hs
  by_cases ht: t = ∅
  · rw [ht, eq_comm, eq_comm (b := t₁)]; simp
    exact fun h ↦ by contradiction
  rw [Set.prod_eq_prod_iff]
  simp; intro h _
  have : s = ∅ := h.resolve_right ht
  contradiction

-- This theorem should already be in ClosedFunction_Closure.
lemma affine_set_ri_eq_self [FiniteDimensional ℝ E] (M : Set E)
  (hp : affineSpan ℝ M = M) (he : M.Nonempty) :
    intrinsicInterior ℝ M = M := by sorry

def MM (x : E) : AffineSubspace ℝ (WithLp 2 (E × ℝ)) where
  carrier := Set.prod {x} univ
  smul_vsub_vadd_mem := by
    refine fun c {p₁ p₂ p₃} a a_1 a_2 ↦ ?_
    simp at *
    sorry

#check closure_eq_self'
theorem univ_convex_closure_intrinsicInterior [FiniteDimensional ℝ E]
  (f : E → EReal) [hp : ProperFunction univ f] (hc : ConvexOn ℝ (dom univ f) f) :
    ∀ x ∈ intrinsicInterior ℝ (dom univ f), f.closure univ x = f x  := by
  intro x hx
  have clf_leq_f: (f.closure univ) x ≤ f x := by
    exact closure_le_self univ f x trivial
  by_cases hclf_top : f.closure univ x = ⊤
  · simp [hclf_top] at clf_leq_f
    rwa [clf_leq_f]
  have h13 : Convex ℝ (f.Epi univ):= by
    refine convex_epigraph ?_
    sorry

  have ge_f_iff (x' : E) (y : ℝ) (t: EReal) (ht: t = f x')
  (hx : x' ∈ intrinsicInterior ℝ (dom univ f)) : t ≤ y ↔ (t).toReal ≤ y := by
    have fx_le_top : t < ⊤ := by rw [ht]; exact x_dom_lt_top (intrinsicInterior_subset hx)
    have fx_ge_bot : t > ⊥ := by
      rw [ht];
      apply ProperFunction.uninfinity x' (Set.mem_univ x')
    lift t to ℝ using ⟨LT.lt.ne_top fx_le_top, LT.lt.ne_bot fx_ge_bot⟩
    simp
  have ge_fx_iff (x' : E) (y : ℝ) (hx : x' ∈ intrinsicInterior ℝ (dom univ f)):
   f x' ≤ y ↔ (f x').toReal ≤ y := by
    exact ge_f_iff x' y (f x') rfl hx
  /- Intersection of M and epi f -/
  have hi' : (MM x).carrier ∩ (intrinsicInterior ℝ (f.Epi univ)) ≠ ∅ := by
    sorry
  have ht : (MM x).carrier ∩ (f.Epi univ) = {x} ×ˢ {μ: ℝ | (f x).toReal ≤ μ} := by
    sorry
  have : IsClosed ((MM x).carrier ∩ (f.Epi univ)) := by
    rw [ht]; exact IsClosed.prod isClosed_singleton isClosed_Ici
  have h1 : (MM x).carrier ∩ closure (f.Epi univ) = closure ((MM x).carrier ∩ (f.Epi univ)) := by
    symm; apply closure_affineSubspace_intrinsicInterior_eq h13 hi'

  have h2 : (MM x).carrier ∩ ((f.closure univ).Epi univ) =
    closure ((MM x).carrier ∩ (f.Epi univ)) := by
    have : ((f.closure univ).Epi univ) = closure (f.Epi univ) := by
      sorry
    rwa [← this] at h1
  have h3 : (MM x).carrier ∩ closure (f.Epi univ) =
    (MM x).carrier ∩ ((f.closure univ).Epi univ) := sorry
  have h4 : (MM x).carrier ∩ ((f.closure univ).Epi univ) =
    (MM x).carrier ∩ (f.Epi univ) := sorry
  let α := EReal.toReal ((f.closure univ) x)
  have xα_in: (x, α) ∈ (MM x).carrier ∩ ((f.closure univ).Epi univ) := by
    refine mem_inter ?_ ?_
    · simp [MM, prod]
    simp [Epi]
    exact le_coe_toReal hclf_top
  -- rw [← h3] at xα_in
  have : f x ≤ f.closure univ x := by
    simp [h4] at xα_in
    have hxa : (x, α) ∈ Epi f univ := sorry
    simp [Epi] at hxa
    by_cases hhhh : f.closure univ x = ⊥
    simp [α, hhhh] at hxa
    sorry
    -- rw []
    sorry
  have : f x = f.closure univ x := by
    sorry
  sorry

end closed_convex_affinesup
