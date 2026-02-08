import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Reaslib.ConvexAnalysis.ClosedFunction_Closure
import Reaslib.ConvexAnalysis.ClosedFunction_Closure_Proper
import Reaslib.ConvexAnalysis.intrinsicInterior_Epigraph
import Reaslib.ConvexAnalysis.ConvexConjugate

open Filter Set Topology Function Module EReal Inner

section Th_7_5

variable {E} [NormedAddCommGroup E] {f : E → EReal} {x : E}

-- (cl f) (y) ≤ liminf_{<1} f ((1-c)x + cy)
lemma closure_le_liminf_affine [InnerProductSpace ℝ E] [ProperFunction univ f] :
    ∀ y, Function.closure f univ y
    ≤ liminf (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ)) := by
  intro y
  -- γ(c) = (1 - c) • x + c • y
  let γ : ℝ → E := fun c => (1 - c) • x + c • y
  have hγ_cont : Continuous γ := by
    have h1 : Continuous fun c : ℝ => (1 - c) := by
      simpa using (continuous_const.sub continuous_id)
    have h1' : Continuous fun c : ℝ => (1 - c) • x := h1.smul continuous_const
    have h2' : Continuous fun c : ℝ => c • y := continuous_id.smul continuous_const
    simpa [γ] using h1'.add h2'
  -- cl f is LSC on univ
  have h_lsc : LowerSemicontinuous (Function.closure f univ) :=
    univ_closure_semicontinuous_of_proper (E:=E) f
  -- composition is LSC
  have hcomp_lsc : LowerSemicontinuous (fun c : ℝ => Function.closure f univ (γ c)) :=
    h_lsc.comp_continuous hγ_cont
  -- γ 1 = y
  have hyγ : γ 1 = y := by simp [γ]
  -- (cl f) y ≤ liminf (cl f ∘ γ) (𝓝 1)
  have h_le_liminf_cl :
      Function.closure f univ y
      ≤ liminf (fun c : ℝ => Function.closure f univ (γ c)) (𝓝 (1 : ℝ)) := by
    simpa [hyγ] using (LowerSemicontinuous.le_liminf hcomp_lsc (1 : ℝ))
  -- cl f ≤ f ⇒ liminf (cl f ∘ γ) (𝓝 1) ≤ liminf (f ∘ γ) (𝓝 1)
  have hmono :
      liminf (fun c : ℝ => Function.closure f univ (γ c)) (𝓝 (1 : ℝ))
      ≤ liminf (fun c : ℝ => f (γ c)) (𝓝 (1 : ℝ)) := by
    apply Filter.liminf_le_liminf
    · refine Eventually.of_forall ?_
      intro c
      have hcl_le : (Function.closure f univ) ≤ f := by
        intro z; exact closure_le_self univ f z trivial
      exact hcl_le (γ c)
    · isBoundedDefault
    · isBoundedDefault
  -- 𝓝[<] 1 ≤ 𝓝 1 ⇒ liminf (·) (𝓝 1) ≤ liminf (·) (𝓝[<] 1)
  have hmono_left :
      liminf (fun c : ℝ => f (γ c)) (𝓝 (1 : ℝ))
      ≤ liminf (fun c : ℝ => f (γ c)) (𝓝[<] (1 : ℝ)) := by
    have hF : (𝓝[<] (1 : ℝ)) ≤ (𝓝 (1 : ℝ)) := nhdsWithin_le_nhds
    exact liminf_le_liminf_of_le hF
  exact le_trans h_le_liminf_cl <| le_trans hmono hmono_left

-- lim_{<1} (1-c)a + cb = b
lemma limsup_affine_at_One {a b : ℝ} :
    limsup (fun c ↦ (1 - c) • a + c • b) (𝓝[<] (1 : ℝ)) = b := by
  -- Continuity (at 1)
  have hcont :
      ContinuousAt (fun c : ℝ => (1 - c) * a + c * b) 1 := by
    simpa using
      (((continuousAt_const.sub continuousAt_id).mul continuousAt_const).add
        (continuousAt_id.mul continuousAt_const))
  -- First get convergence from 𝓝 1
  have ht₀ :
      Tendsto (fun c : ℝ => (1 - c) * a + c * b) (𝓝 (1 : ℝ)) (𝓝 b) := by
    simpa [sub_self (1 : ℝ), zero_mul, one_mul, zero_add] using hcont.tendsto
  -- Then restrict to the left neighborhood 𝓝[<] 1
  have ht :
      Tendsto (fun c : ℝ => (1 - c) * a + c * b) (𝓝[<] (1 : ℝ)) (𝓝 b) :=
    ht₀.mono_left nhdsWithin_le_nhds
  -- If a limit exists, then limsup equals the limit
  simpa using ht.limsup_eq

-- (y,b) ∈ cl (epi f)
lemma mem_closure_epi {b : ℝ} [ProperFunction univ f] (hb : b ≥ Function.closure f univ y) :
    (y, b) ∈ closure (f.Epi univ) := by
  have h : (y, b) ∈ (Function.closure f univ).Epi univ := by
    unfold Epi
    rw [mem_setOf_eq]
    exact ⟨mem_univ (y, b).1, hb⟩
  rw [← closure_epi_real_eq_epi_real_closure' f isClosed_univ] at h
  exact h

#check mem_intrinsicInterior_epi_iff  -- requires [FiniteDimensional ℝ E]
-- sjr
-- (x,a) ∈ ri (epi f)
lemma mem_intrinsicInterior_epi {a : ℝ} [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [ProperFunction univ f] (h : ConvexOn ℝ univ f)
    (hx : x ∈ intrinsicInterior ℝ (dom univ f)) (ha : a > f x) :
    (x, a) ∈ intrinsicInterior ℝ (f.Epi univ) := by
  -- Use Th 7.3
  haveI h : (x, a) ∈ intrinsicInterior ℝ (Epi f (dom univ f)) := by
    rw [mem_intrinsicInterior_epi_iff]
    exact ⟨hx, ha⟩
    apply convexOn_dom_s_f_of_convexOn_s h
  rw [Eq.symm <| Epi_eq f] at h
  exact h

#check openSegment_sub_intrinsicInterior
#check mem_closure_epi
-- (1-c)(x,a) + c(y,b) ∈ ri (epi f)
lemma affine_intrinsicInterior_epi {a b c : ℝ} [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [ProperFunction univ f] (h : ConvexOn ℝ univ f)
    (hx : x ∈ intrinsicInterior ℝ (dom univ f)) (ha : a > f x) (hc : c ∈ Ioo 0 1)
    (hb : b ≥ Function.closure f univ y) :
    (1 - c) • (x, a) + c • (y, b) ∈ intrinsicInterior ℝ (f.Epi univ) := by
  -- Use Th 6.1
  have hmem : (1 - c) • (x, a) + c • (y, b) ∈ openSegment ℝ (x, a) (y, b) := by
    unfold openSegment; simp
    use (1 - c)
    constructor
    · exact sub_pos_of_lt hc.2
    use c
    constructor
    · exact hc.1
    simp
  have hsub : openSegment ℝ (x, a) (y, b) ⊆ intrinsicInterior ℝ (f.Epi univ) := by
    apply openSegment_sub_intrinsicInterior ℝ
    · exact convex_epigraph h  -- requires f convex on univ
    · exact mem_intrinsicInterior_epi h hx ha
    apply mem_closure_epi hb
    simp
    exact subset_closure
  apply hsub hmem

-- /-
-- This instance proves that the closure of a proper convex function is also a proper function.
-- - `uninfinity`: Proved by using `cl(f) = f**` and showing that `f**` is nowhere `⊥`.
-- - `existence_of_finite_value`: Proved by noting that `cl(f) ≤ f`, so if `f` is finite
--   at some point `x`, `cl(f)` cannot be `⊤` everywhere.
-- -/
-- instance univ_convex_closure_proper' (f : E → EReal) [hp : ProperFunction univ f]
--     [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
--     (hc : ConvexOn ℝ (dom univ f) f) :
--     ProperFunction univ (Function.closure f univ) where
--   uninfinity := by
--     intro x _
--     rw [← bi_convex_conjugate_eq_closure hc]
--     have : ProperFunction univ (convex_conjugate univ f) := by
--       exact proper_convex_proper_conjugate f hp hc
--     apply convex_conjugate_ne_bot_s _ (by simp) _ (by trivial)
--   existence_of_finite_value := by
--     right; obtain hp1 := hp.2
--     simp at hp1; rcases hp1 with ⟨x, hx⟩
--     use x; constructor; trivial
--     exact lt_of_le_of_lt (closure_le_self univ f x (by trivial)) hx

lemma limsup_point_le {a b c : ℝ} [InnerProductSpace ℝ E]
    (ha : a > f x) (hc : c ∈ Ioo 0 1) (h : f ((1 - c) • x + c • y) < (1 - c) • a + c • b) :
    limsup (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ))
    ≤ limsup (fun c ↦ (1 - c) • a + c • b) (𝓝[<] (1 : ℝ)) := by
  -- limsup mono
  sorry

#check mem_intrinsicInterior_epi_iff
#check Epi_eq
#check limsup_affine_at_One
#check bot_lowersemicontinuoushull_eq_bot
-- (cl f) (y) ≥ limsup_{<1} f ((1-c)x + cy)
lemma th_7_5' [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (hp : ProperFunction univ f)
    (h : ConvexOn ℝ univ f) (hx : x ∈ intrinsicInterior ℝ (dom univ f)) :
    ∀ y, Function.closure f univ y
    ≥ limsup (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ)) := by
  intro y
  apply le_of_forall_ge
  -- For any b ≥ (cl f) (y), we have b ≥ limsup_{<1} f ((1-c)x + cy).
  -- Hence (cl f) (y) ≥ limsup_{<1} f ((1-c)x + cy).
  intro b hb
  by_cases hbcase : b = ⊤
  · rw [hbcase]
    exact le_top
  have hbnebot : b ≠ ⊥ := by
    intro hbot
    rw [hbot] at hb
    simp at hb
    have : Function.closure f univ y ≠ ⊥ := by
      haveI hcl_proper : ProperFunction univ (Function.closure f univ) := by
        apply univ_convex_closure_proper'
        exact convexOn_dom_s_f_of_convexOn_s h
      exact ne_of_gt (hcl_proper.uninfinity y (mem_univ y))
    exact this hb
  lift b to ℝ using ⟨hbcase, hbnebot⟩
  by_cases h_empty : ∃ a : ℝ, a > f x
  · obtain ⟨a, ha⟩ := h_empty
    have hxa : (x, a) ∈ intrinsicInterior ℝ (f.Epi univ) := mem_intrinsicInterior_epi h hx ha
    have hbound : limsup (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ)) ≤ b := by
      have h : ∀ a : ℝ, a > f x → ∀ c : ℝ, c ∈ Ioo 0 1 →
          limsup (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ)) ≤ b := by
        intro a ha c hc
        have hxa : (x, a) ∈ intrinsicInterior ℝ (f.Epi univ) := mem_intrinsicInterior_epi h hx ha
        have hint : ((1 - c) • x + c • y, (1 - c) • a + c • b)
            ∈ intrinsicInterior ℝ (f.Epi (dom univ f)) := by
          have : (1 - c) • (x, a) + c • (y, b) ∈ intrinsicInterior ℝ (f.Epi univ) :=
            affine_intrinsicInterior_epi h hx ha hc hb
          rw [Epi_eq f] at this
          exact this
        have hf : f ((1 - c) • x + c • y) < (1 - c) • a + c • b := by
          rw [mem_intrinsicInterior_epi_iff f <| convexOn_dom_s_f_of_convexOn_s h] at hint
          exact hint.2
        have : limsup (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ))
            ≤ limsup (fun c ↦ (1 - c) • a + c • b) (𝓝[<] (1 : ℝ)) := by
          apply limsup_point_le ha hc hf
        rw [limsup_affine_at_One] at this
        apply this
      have hnonempty : Nonempty (Ioo (0 : ℝ) 1) := by use 1/2; simp [Ioo]; linarith
      obtain ⟨c₀, hc₀⟩ := hnonempty
      specialize h a ha c₀ hc₀
      exact h
    exact hbound
  · -- If there is no a > f x, then f x = ⊤, contradicting ProperFunction.
    push_neg at h_empty
    have htop : f x = ⊤ := by
      by_contra hnetop
      by_cases hbot : f x = ⊥
      · have h := h_empty 0
        rw [hbot] at h
        simp at h
      · lift f x to ℝ using ⟨hnetop, hbot⟩ with fx
        have h := h_empty (fx + 1)
        simp at h
        have hlt : (fx : EReal) < (fx : EReal) + 1 := by
          have : (fx : EReal) + 1 = ↑(fx + 1) := by simp
          rw [this]
          exact EReal.coe_lt_coe_iff.mpr (lt_add_one fx)
        exact not_le.mpr hlt h
    have hdom : x ∈ dom univ f := intrinsicInterior_subset hx
    have hlttop : f x < ⊤ := x_dom_lt_top hdom
    rw [htop] at hlttop
    -- f x = ⊤ but also f x < ⊤, contradiction.
    exfalso
    exact lt_irrefl ⊤ hlttop

#check closure_le_liminf_affine
#check th_7_5'
#check liminf_le_limsup

-- Theorem 7.5
-- (cl f) (y) = lim_{<1} f ((1-c)x + cy)
theorem closure_eq_limit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [ProperFunction univ f]
    -- dom convex + Proper = univ convex
    (h : ConvexOn ℝ univ f)
    (hx : x ∈ intrinsicInterior ℝ (dom univ f)) :
    ∀ y, Function.closure f univ y
    = lim (𝓝[<] (fun c ↦ f ((1 - c) • x + c • y))) (1 : ℝ) := by
  intro y
  -- closure f = liminf
  have heq1 : liminf (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ))
      = Function.closure f univ y := by
    exact le_antisymm (le_trans liminf_le_limsup <| th_7_5' (by assumption) h hx y) <|
      closure_le_liminf_affine y
  -- closure f = limsup
  have heq2 : limsup (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ))
      = Function.closure f univ y := by
    have : Function.closure f univ y ≤ limsup (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ)) := by
      rw [← heq1]
      exact liminf_le_limsup
    exact le_antisymm (th_7_5' (by assumption) h hx y) this
  -- When liminf = limsup, the limit exists and equals their common value.
  have heq : liminf (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ))
      = limsup (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ)) := by
    rw [heq1, heq2]
  have h : Tendsto (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ))
      (𝓝 (Function.closure f univ y)) := by
    have : Tendsto (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ))
        (𝓝 (limsup (fun c ↦ f ((1 - c) • x + c • y)) (𝓝[<] (1 : ℝ)))) := by
      apply tendsto_of_liminf_eq_limsup heq
      exact rfl
    rw [← heq2]
    exact this
  have : Function.closure f univ y = lim (𝓝[<] (fun c ↦ f ((1 - c) • x + c • y))) (1 : ℝ) := by
    -- refine
    --   Eq.symm
    --     ((fun {x y} hx_top hx_bot hy_top hy_bot ↦
    --     (toReal_eq_toReal hx_top hx_bot hy_top hy_bot).mp)
    --       ?_ ?_ ?_ ?_ ?_)
    -- · sorry
    -- · sorry
    -- · sorry
    -- · sorry
    sorry
  exact this

-- f convex on univ ⇒ c ↦ f ((1-c)x + cy) convex on univ
lemma Convex_mid_point [InnerProductSpace ℝ E] (h : ConvexOn ℝ univ f) :
    ConvexOn ℝ univ fun c => f (((1 : ℝ) - c) • x + c • y) := by
  sorry

-- Corollary 7.5.1
#print Function.IsClosed
theorem th_7_5_1 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (hp : ProperFunction univ f)
    (h : ConvexOn ℝ univ f) (hx : x ∈ dom univ f)
    (hf : f.IsClosed univ) :  -- for proper convex functions, closedness = lower semicontinuity
    ∀ y, f y = lim (𝓝[<] (fun c ↦ f ((1 - c) • x + c • y))) (1 : ℝ) := by
  intro y
  -- γ(c) = (1 - c) • x + c • y
  let γ : ℝ → E := fun c => (1 - c) • x + c • y
  -- φ(c) = f ((1 - c) • x + c • y)
  let φ : ℝ → EReal := fun c => f ((1 - c) • x + c • y)
  have h1 : ConvexOn ℝ univ φ := by exact Convex_mid_point h
  have h2 : ∀ α : EReal, IsClosed {z | f z ≤ α} := by
    -- f is closed, meaning f.IsClosed univ, i.e. its epigraph is closed.
    -- This is equivalent to all sublevel sets being closed.
    intro α
    -- First, f.IsClosed univ implies f is lower semicontinuous on univ.
    have h_lsc : LowerSemicontinuousOn f univ := by
      -- univ is closed
      rw [LowerSemicontinuousOn_iff_IsClosed_epigraph_of_closed isClosed_univ]
      -- f.IsClosed univ means the epigraph is closed in E × ℝ.
      -- Need to show it is also closed in E × EReal.
      rw [EReal_epi_closed_Real_epi_closed]
      exact ⟨isClosed_univ, hf⟩
    -- Sublevel sets of a lower semicontinuous function are closed.
    rw [lowerSemicontinuousOn_iff_isClosed_preimage] at h_lsc
    obtain ⟨u, hu_closed, hu_eq⟩ := h_lsc α
    -- {z | f z ≤ α} = {z | z ∈ univ ∧ f z ≤ α} = f⁻¹' (Iic α) ∩ univ
    have h_eq : {z | f z ≤ α} = f ⁻¹' Iic α ∩ univ := by
      ext z
      simp [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
    rw [h_eq, hu_eq]
    exact hu_closed.inter isClosed_univ
  have h3_sets : ∀ α : EReal, IsClosed {c | φ c ≤ α} := by
    -- Sublevel sets of φ(c) = f(γ(c)) are preimages of sublevel sets of f via the continuous map γ.
    intro α
    have hγ_cont : Continuous γ := by
      simp [γ]
      apply Continuous.add
      · exact Continuous.smul (Continuous.sub continuous_const continuous_id) continuous_const
      · exact Continuous.smul continuous_id continuous_const
    have : {c | φ c ≤ α} = γ ⁻¹' {z | f z ≤ α} := by ext c; simp [φ, γ]
    rw [this]
    exact IsClosed.preimage hγ_cont (h2 α)
  have h3 : LowerSemicontinuous φ := by
    -- Lower semicontinuity follows from closedness of sublevel sets.
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    exact h3_sets
  by_cases hcase : f y = ⊤
  · rw [hcase]
    -- If f y = ⊤, we need to show lim φ (𝓝[<] 1) = ⊤.
    sorry
  have hfy : f y ≠ ⊥ := ne_of_gt (hp.uninfinity y (mem_univ y))
  lift f y to ℝ using ⟨hcase, hfy⟩ with fy
  sorry

end Th_7_5
