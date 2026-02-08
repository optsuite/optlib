import Mathlib.Topology.Defs.Basic
import Reaslib.Basic.EReal
import Reaslib.Basic.ProperFunction
import Reaslib.ConvexAnalysis.ClosedFunction_Closure

open Set
variable {E : Type*}

def M_affine [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
   AffineSubspace ℝ (WithLp 2 (E × ℝ)) where
  carrier := Set.prod univ {α}
  smul_vsub_vadd_mem := by
    refine fun c {p₁ p₂ p₃} a a_1 a_2 ↦ ?_
    simp at *
    rcases a  with ⟨_, h₁⟩
    rcases a_1 with ⟨_, h₂⟩
    rcases a_2 with ⟨_, h₃⟩
    apply Set.mem_prod.mpr
    apply And.intro
    · trivial
    · change (c • (p₁ - p₂) + p₃).snd = α
      calc
          (c • (p₁ - p₂) + p₃).snd = c • (p₁ - p₂).snd + p₃.snd := by simp
          _ = c • (p₁.snd - p₂.snd) + p₃.snd := by simp
          _ = c • (α - α) + α := by rw [h₁, h₂, h₃]
          _ = α := by rw [sub_self, smul_zero, zero_add]

lemma M_inter_epi_eq [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal) (α : ℝ) :
  {x | f x ≤ α} ×ˢ {α} = ((M_affine α).carrier ∩ f.Epi univ) := by
    ext ⟨x, y⟩
    constructor
    · intro h
      rcases h with ⟨hx, hy⟩
      simp [M_affine, Function.Epi]
      apply And.intro
      · trivial
      · simp at *
        rw [hy]
        exact hx
    · intro h
      simp [M_affine, Function.Epi, Set.mem_inter_iff, Set.mem_univ, Set.mem_setOf_eq] at h
      rcases h with ⟨⟨_, hy⟩, hx⟩
      simp [hy]
      simp at hy
      rw [← hy]
      exact hx

lemma M_inter_epicl_eq [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal) (α : ℝ) :
  {x | f.closure univ x ≤ α} ×ˢ {α}= ((M_affine α).carrier ∩ (f.closure univ).Epi univ) := by
    ext ⟨x, y⟩
    constructor
    · intro h
      rcases h with ⟨hx, hy⟩
      simp [M_affine, Function.Epi]
      constructor
      · trivial
      · simp at *
        rw [hy]
        exact hx
    · intro h
      simp [M_affine, Function.Epi, Set.mem_inter_iff, Set.mem_univ, Set.mem_setOf_eq] at h
      rcases h with ⟨⟨_, hy⟩, hx⟩
      simp [hy]
      simp at hy
      rw [← hy]
      exact hx

#check Set.Nonempty
lemma M_inter_intrinsicInterior_nonempty [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (f : E → EReal) [ProperFunction univ f] (hf : ConvexOn ℝ (dom univ f) f)
  (α : ℝ) : ((M_affine α).carrier ∩ intrinsicInterior ℝ (Function.Epi f univ)).Nonempty := by
  simp only [Set.Nonempty]
  have ⟨x,hx⟩: (intrinsicInterior ℝ (dom univ f)).Nonempty := by
    refine (intrinsicInterior_nonempty ?_).mpr ?_
    refine convex_epigraph_dom_convex ?_
    refine EReal.convex_epigraph ?_
    exact convexOn_s_of_convexOn_dom_s_f hf
    exact univ_proper_dom_not_empty f
  sorry

#check interior
#check closure_affineSubspace_intrinsicInterior_eq
theorem closure_of_level_set_le [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → EReal) [ProperFunction univ f] (hf : ConvexOn ℝ (dom univ f) f) (α : ℝ) :
  closure {x | f x ≤ α} = {x | (f.closure univ) x ≤ α} := by
  have : closure {x | f x ≤ α} ×ˢ {α} = {x | (f.closure univ) x ≤ α} ×ˢ {α} := by
    have hc: closure ({x | f x ≤ α} ×ˢ {α}) = closure {x | f x ≤ α} ×ˢ {α}:= by
      simp [closure_prod_eq]
    have cl_epi_eq_epi_cl: closure (f.Epi univ) = (f.closure univ).Epi univ := by
      refine closure_epi_real_eq_epi_real_closure' f (by simp)
    rw [M_inter_epicl_eq, ← hc, M_inter_epi_eq, ← cl_epi_eq_epi_cl]
    apply closure_affineSubspace_intrinsicInterior_eq
    refine EReal.convex_epigraph ?_
    exact convexOn_s_of_convexOn_dom_s_f hf
    -- obtain ⟨x,hx⟩ := M_inter_intrinsicInterior_nonempty f α
    sorry
    -- simp only [Set.Nonempty] at h
    -- exact M_inter_intrinsicInterior_nonempty f α
  simp at this
  exact this

theorem closure_of_level_set_lt [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → EReal) [ProperFunction univ f] (hf : ConvexOn ℝ (dom univ f) f) (α : ℝ) :
  closure {x | f x < α} = {x | (f.closure univ) x ≤ α} := sorry

-- The assumptions on E are a bit strong; adjust later.
theorem intrinsicInterior_of_level_set_le
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal)
  [ProperFunction univ f] (hf : ConvexOn ℝ (dom univ f) f) (α : ℝ) :
  intrinsicInterior ℝ {x | f x ≤ α} = {x ∈ intrinsicInterior ℝ (dom univ f) | f x < α} := sorry


theorem intrinsicInterior_of_level_set_lt
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal)
  [ProperFunction univ f] (hf : ConvexOn ℝ (dom univ f) f) (α : ℝ) :
  intrinsicInterior ℝ {x | f x < α} = {x ∈ intrinsicInterior ℝ (dom univ f) | f x < α} := sorry
