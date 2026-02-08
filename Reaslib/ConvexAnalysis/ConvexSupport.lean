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
import Mathlib.Topology.Defs.Induced
import Reaslib.ConvexAnalysis.AffineMinorant
import Reaslib.ConvexAnalysis.ConvexConjugate
import Reaslib.ConvexAnalysis.ConvexIndicator
import Reaslib.ConvexAnalysis.IntrinsicInterior


open Filter BigOperators Set Topology Inner Function Module EReal
open scoped Pointwise

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

section convex_support
/-
  The indicator function of a convex set --Set.convex_indicator
-/
-- @[simp]
-- noncomputable def  Set.convex_indicator (s : Set α) (x : α): EReal :=
--   haveI := Classical.decPred (· ∈ s)
--   if x ∈ s then 0 else ⊤

noncomputable def Set.convex_support [NormedAddCommGroup α] [InnerProductSpace ℝ α]
    (s : Set α) : α →  EReal :=
  convex_conjugate univ s.convex_indicator

section finite

/- 
  Contributor: Shao Siyuan
  Idea: boundedness of a set is equivalent to boundedness of all linear functionals on the set.
  By the Riesz representation theorem, linear functionals can be written as inner products,
  then apply the Banach–Steinhaus theorem to get a uniform bound.
  Note: need to import `Mathlib.Analysis.Normed.Operator.BanachSteinhaus` at the top of the file.
  Also need to declare `[CompleteSpace α]` in variables (completeness).
-/

lemma sup_exist (b : ℝ) (f : α → EReal) :
  (∃ a ∈ univ, f a ≥ b) → (⨆ x ∈ univ, f x ≥ b) := by
  intro ha
  rcases ha with ⟨a, au, fab⟩
  have h : ∀ a ∈ univ, ⨆ x ∈ univ, f x ≥ f a := by
    exact fun a a_1 ↦ EReal.le_biSup a_1
  have ge_trans : ∀ q w: EReal, q ≥ w → w ≥ b → q ≥ b := by
    exact fun q w a a_1 ↦ Preorder.le_trans (↑b) w q a_1 a
  exact ge_trans (⨆ x ∈ univ, f x) (f a) (h a au) fab

--banach_steinhaus requires completeness
variable [NormedAddCommGroup α] [InnerProductSpace ℝ α] [CompleteSpace α]

-- Equivalent characterization of the support function
omit [CompleteSpace α] in
lemma convex_support_eq_sup_of_inner_product (u : α) {s : Set α} :
  s.convex_support u = ⨆ w : s, ⟪w.1, u⟫.toEReal := by
  unfold convex_support convex_conjugate
  let g (x_1 : α) := ⟪x_1, u⟫.toEReal - s.convex_indicator x_1
  simp
  rw [iSup_split g s]
  have : ⨆ x_1, ⨆ (_ : ¬s x_1), ⟪x_1, u⟫.toEReal - s.convex_indicator x_1= ⊥ := by
    refine iSup₂_eq_bot.mpr ?_
    intro x hx
    simp [convex_indicator]
    split_ifs with h₁; simp; exact hx h₁; rfl
  rw [this, sup_bot_eq]
  have : ⨆ x_1, ⨆ (_ : s x_1), ⟪x_1, u⟫.toEReal - s.convex_indicator x_1
      = ⨆ x_1, ⨆ (_ : s x_1), ⟪x_1, u⟫.toEReal := by
    simp [convex_indicator]
    refine Eq.symm (biSup_congr ?_)
    intro i hi
    split_ifs with h₁; simp; exact False.elim (h₁ hi)
  rw [this, iSup_subtype']; rfl

-- Symmetry of the supremum over the inner product
omit [CompleteSpace α] in
lemma sup_of_inner_product_symm {s : Set α} (x : α) :
    ⨆ z : s, (|⟪x, z.1⟫|).toEReal = ⨆ z : s, (|⟪z.1, x⟫|).toEReal := by
  refine iSup_congr fun
    | .mk val property => ?mk
  apply EReal.coe_eq_coe_iff.mpr
  apply congrArg abs
  exact real_inner_comm val x

-- Definition of sup
lemma EReal_sup (a b : EReal) : a ⊔ b = a ∨ a ⊔ b = b := by
  by_cases h1 : a ≤ b
  · right; exact sup_of_le_right h1
  left; refine sup_eq_left.mpr ?_
  exact le_of_not_ge h1

theorem set_bounded_of_convex_support_bounded_aux {s : Set α}
    (hy : ∀ y, ⊥ < s.convex_support y ∧ s.convex_support y < ⊤) :
    ∃ C, ∀ x : s, ‖innerSL ℝ x.1‖ ≤ C := by
  apply banach_steinhaus
  intro x
  let M := ⨆ z : s, (|innerSL ℝ x z.1|).toEReal
  have h₃ : M = s.convex_support x ∨ M = s.convex_support (-x):= by
  -- Show M equals the support function value (absolute value gives two cases)
    simp [convex_support_eq_sup_of_inner_product, M]
    rw [sup_of_inner_product_symm]
    have : ∀ a, (|⟪a, x⟫|).toEReal = (⟪a, x⟫).toEReal ⊔ (-⟪a, x⟫).toEReal := by
      intro; rw [abs_eq_max_neg]; rfl
    simp [this]; rw [iSup_sup_eq]
    let a := ⨆ x_1 : s, ⟪ x_1.1, x⟫.toEReal
    let b := ⨆ x_1 : s, -⟪ x_1.1, x⟫.toEReal
    exact EReal_sup a b
  rcases h₃ with h₃_1 | h₃_2
  · obtain ⟨hy1, hy2⟩ := hy x
    rw [← h₃_1] at hy1
    use M.toReal
    intro y
    apply EReal.coe_le_coe_iff.mp
    rw [coe_toReal (LT.lt.ne_top (lt_of_eq_of_lt h₃_1 hy2)) (LT.lt.ne_bot hy1)]
    simp; rw [real_inner_comm]
    exact le_iSup_iff.mpr fun b a ↦ a y

  · obtain ⟨hy1, hy2⟩ := hy (-x)
    rw [← h₃_2] at hy1
    use M.toReal
    intro y
    apply EReal.coe_le_coe_iff.mp
    rw [coe_toReal (LT.lt.ne_top (lt_of_eq_of_lt h₃_2 hy2)) (LT.lt.ne_bot hy1)]
    simp; rw [real_inner_comm]
    exact le_iSup_iff.mpr fun b a ↦ a y


/-
Mainly prove: if the support function is finite everywhere, then the set is bounded.
-/
theorem set_bounded_of_convex_support_bounded {s : Set α}
    (hy : ∀ y, ⊥ < s.convex_support y ∧ s.convex_support y < ⊤) :
    Bornology.IsBounded s := by
  suffices ∀ y : α, ∃ M ≥ 0, ⨆ x ∈ s, |(innerSL ℝ x) y| ≤ M by
    rcases set_bounded_of_convex_support_bounded_aux hy with ⟨C, ubfC⟩
    have h₄ : ∀ x : s, ‖x.1‖ = ‖innerSL ℝ x.1‖ := by simp
    rw [isBounded_iff_forall_norm_le]
    use C; intro x hx
    specialize ubfC ⟨x, hx⟩
    rwa [← h₄ ⟨x, hx⟩] at ubfC
  exact fun y ↦ exists_ge_of_linear 0 (⨆ x ∈ s, |(innerSL ℝ x) y|)

end finite

section convex_support_property

variable [CompleteSpace E] (s : Set E)

open InnerProductSpace

lemma strict_separation (s : Set E) (hscv : Convex ℝ s)
    (hscl : IsClosed s) (hznin : z ∉ s) :  ∃ (m : E)(n : ℝ), n > ⟪z, m⟫ ∧
  ∀ y ∈ s, ⟪y, m⟫ > n := by --wyj
  obtain ⟨f, u, ⟨hfu1, hfu2⟩⟩ := geometric_hahn_banach_point_closed hscv hscl hznin
  have simple_Riesz_lemma : ∃(m : E), ∀ x : E, ⟪m, x⟫ = f x := by
    use (toDual ℝ E).symm f
    intro x; exact toDual_symm_apply
  rcases simple_Riesz_lemma with ⟨m, hzm⟩
  use m; use u
  constructor
  · rw [real_inner_comm m z]
    exact lt_of_eq_of_lt (hzm z) hfu1
  intro b h
  obtain h''' := hzm b
  rw [real_inner_comm b m] at h'''
  exact lt_of_lt_of_eq (hfu2 b h) (id (Eq.symm h'''))

omit [CompleteSpace E] in
lemma le_of_ge_strict_sepa (q : Set E) (ss : ∃ (m : E) (n : ℝ), n > ⟪z, m⟫ ∧
    ∀ y ∈ q, ⟪y, m⟫ > n) : ∃ (a : E) (b : ℝ), b < ⟪z, a⟫ ∧ ∀ y ∈ q, ⟪y, a⟫ < b := by --wyj
  rcases ss with ⟨m, n, hmn⟩
  use -m
  use -n
  have h1 : ∀ x, ⟪x, -m⟫ = -⟪x, m⟫ := by exact fun x ↦ inner_neg_right x m
  constructor
  · rw [h1]
    exact _root_.neg_lt_neg_iff.mpr hmn.1
  intro y h
  rw [h1]
  exact _root_.neg_lt_neg_iff.mpr (hmn.2 y h)

lemma set_inclusion_convex_support_eq (p q : Set E)
    (hqcv : Convex ℝ q) (hqcl : IsClosed q) (hzp : z ∈ p)
    (hcseq : ∀ (x : E), p.convex_support x = q.convex_support x) : z ∈ q := by --wyj
  by_contra! hz -- proof by contradiction
  have strict_separation1 : ∃ (a : E)(b : ℝ), b < ⟪z, a⟫ ∧ ∀ y ∈ q, ⟪y, a⟫ < b  := by
    apply le_of_ge_strict_sepa; exact strict_separation q hqcv hqcl hz
  rcases strict_separation1 with ⟨a, b, hab⟩
  have h₁ : ¬ ∀  (x : E), p.convex_support x = q.convex_support x := by
    simp [convex_support]
    push_neg
    use a
    have h₂ : convex_conjugate univ p.convex_indicator a >
      convex_conjugate univ q.convex_indicator a := by
      -- It suffices to prove ">" to get "≠".
      apply lt_of_le_of_lt
      have h₃ : convex_conjugate univ q.convex_indicator a ≤ b := by
      -- Use strict separation: ∀y ∈ q, ⟪y, a⟫ < b, to show ⨆y, ⟪y, a⟫ ≤ b.
        simp [convex_conjugate,convex_indicator]
        intro i
        by_cases hi: i ∈ q
        simp [hi]
        exact le_of_lt (hab.2 i hi)
        simp [hi]
      apply h₃ -- use b as the intermediate bound for h₂
      apply lt_of_lt_of_le
      /- Compare b and convex_conjugate univ p.convex_indicator a;
      take the intermediate bound b < ⟪z, a⟫ from strict separation. -/
      apply EReal.coe_lt_coe_iff.mpr hab.1
      -- Now show ⟪z, a⟫ ≤ convex_conjugate univ p.convex_indicator a.
      have h₄ : ⟪z, a⟫ = ⟪z, a⟫ - p.convex_indicator z := by
        simp [convex_indicator]
        simp [hzp]
      rw [h₄]
      simp [convex_conjugate]
      exact le_iSup_iff.mpr fun b a ↦ a z
    exact Ne.symm (ne_of_lt h₂)
  exact h₁ hcseq

theorem convex_support_congr_iff (s t : Set E)
    (hscv : Convex ℝ s) (htcv : Convex ℝ t) (hscl : IsClosed s) (htcl : IsClosed t) :
  s = t ↔ s.convex_support = t.convex_support := by
  -- left to right
  constructor
  · exact fun h => (by rw [h])
  -- right to left
  simp [funext_iff]
  intro h; ext z
  apply iff_iff_implies_and_implies.mpr
  constructor -- use the lemma twice
  · exact fun a ↦ set_inclusion_convex_support_eq s t htcv htcl a h
  exact fun a ↦ set_inclusion_convex_support_eq t s hscv hscl a (fun x => (h x).symm)

-- The support function of a nonempty set is a proper function.
instance convex_support_is_proper_of_nonempty {s : Set E} (hs : s.Nonempty) :
    ProperFunction univ s.convex_support where
  uninfinity := by
    intro x _
    simp [convex_support]
    obtain := ConvexIndicator_is_proper_on_univ hs
    apply convex_conjugate_ge_bot_univ'
  existence_of_finite_value := by -- by wyj
    right
    simp [convex_support]
    -- Need a point x where the support function is finite; x = 0 works.
    have convex_conjugate_at_zero :
      convex_conjugate univ (convex_indicator s) 0 ≤ 0 := by
      refine (conjugate_le_zero_iff s.convex_indicator).mpr ?_
      simp
      intro y
      simp [convex_indicator]
      split_ifs with hy <;> simp
    use 0
    exact lt_of_le_of_lt (convex_conjugate_at_zero) (zero_lt_top)

-- Show convex support function is lower semicontinuous; the original theorem assumes s is closed.
omit [CompleteSpace E] in
theorem convex_support_lowerSemicontinuous_of_closed {s : Set E} :
  LowerSemicontinuous s.convex_support := by --by wyj
  simp [convex_support]
  apply lowerSemicontinuous_iSup
  /- For a two-variable function, if for each fixed first variable it is
  lower semicontinuous in the second variable, then taking supremum over
  the first variable preserves lower semicontinuity in the second. -/
  simp
  intro i
  refine Continuous.lowerSemicontinuous ?h.h
  apply EReal.continuous_inner_sub

omit [NormedAddCommGroup E] in
lemma convex_indicator_empty : ∀ x ∈ univ, (∅ : Set E).convex_indicator x = ⊤ := by
  intro x _
  simp [convex_indicator]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem convex_indicator_empty_iff : s.convex_indicator = ⊤ ↔ s = ∅ := by
  constructor
  · intro h; by_contra! hs
    obtain ⟨x, xs⟩:= Set.nonempty_def.1 hs
    have h1: s.convex_indicator x = 0 := by
      simp [convex_indicator]; exact xs
    have h2 := congrFun h x; simp [h1] at h2
  · intro h; rw [h]; ext x; simp
    exact convex_indicator_empty x trivial

omit [CompleteSpace E] in
theorem convex_support_empty : (∅ : Set E).convex_support = ⊥ := by
  simp [convex_support]
  ext x; simp [convex_conjugate, convex_indicator_empty]

omit [CompleteSpace E] in
theorem convex_support_convex_of_convex {s : Set E} : ConvexOn ℝ univ s.convex_support := by
  by_cases hs : s = ∅
  · rw [hs, convex_support_empty]
    simp [ConvexOn]
    exact convex_univ
  push_neg at hs
  simp [convex_support]
  obtain := ConvexIndicator_is_proper_on_univ hs
  apply convex_conjugate_convex

omit [CompleteSpace E] in
lemma convex_conjugate_eq_bot {f : E → EReal}
  (h : convex_conjugate univ f = ⊥) : f = ⊤ := by
  ext x; have h := congrFun h x
  simp [convex_conjugate] at h; simp
  specialize h x; by_contra hx1
  push_neg at hx1
  by_cases hx2 : f x = ⊥
  · simp [hx2] at h;
  push_neg at hx2
  lift f x to ℝ with fx;
  · exact ⟨hx1, hx2⟩
  rw [← EReal.coe_sub] at h
  apply coe_ne_bot; exact h

omit [CompleteSpace E] in
theorem convex_support_empty_iff : s.convex_support = ⊥ ↔ s = ∅ := by
  constructor
  · intro h
    simp [convex_support] at *
    have := convex_conjugate_eq_bot h
    exact (convex_indicator_empty_iff s).mp this
  · intro hs
    rw [hs]
    exact convex_support_empty

end convex_support_property

end convex_support

theorem ccp_convex_conjugate_bijective {f g : E → EReal} [FiniteDimensional ℝ E]
    (hf : ConvexOn ℝ (dom univ f) f ∧ LowerSemicontinuous f ∧ ProperFunction univ f)
    (hg : ConvexOn ℝ (dom univ g) g ∧ LowerSemicontinuous g ∧ ProperFunction univ g) :
    convex_conjugate univ f =  convex_conjugate univ g ↔ f = g := by
  rcases hf with ⟨hf1, hf2, hf3⟩
  rcases hg with ⟨hg1, hg2, hg3⟩
  constructor
  · intro h
    rw [← bi_convex_conjugate_eq_self hf2 (convexOn_s_of_convexOn_dom_s_f hf1),
      ← bi_convex_conjugate_eq_self hg2 (convexOn_s_of_convexOn_dom_s_f hg1), h]
  intro h; rw [h]


/-
dom s (m • f) = dom s f
-/
-- omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
-- theorem dom_eq_smul (s : Set E) (f : E → EReal) {m : ℝ} (hm : m > 0) :
--     dom s (m • f) = dom s f := by
--   simp
--   ext x
--   simp
--   intro _
--   exact mul_lt_top_iff_lt_top hm
section zero_or_top_iff_positive_homogeneous

section aux


omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma zero_or_inf_iff (s) (f : E → EReal) [hsf : ProperFunction s f] :
    (∀ x ∈ s, f x = 0 ∨ f x = ⊤) ↔ ∀ m > (0 : ℝ), ∀ x ∈ s, f x = m * f x := by
  constructor
  · intro hxs m hm x hx
    rcases hxs x hx with hf | hf
    · rw[hf];simp
    rw[hf];
    exact (coe_mul_top_of_pos hm).symm
  intro hm x hx
  by_contra! hf
  have key := hm 2  (by simp) x hx
  have : f x / f x = (2 : ℝ) * (f x) / f x := by rw [← key]
  have lt_bot := hsf.1 x hx
  rw[EReal.div_self (LT.lt.ne_bot lt_bot) hf.2 hf.1, ← EReal.mul_div, EReal.div_self (
    LT.lt.ne_bot lt_bot) hf.2 hf.1] at this
  simp at this
  norm_cast at this

/- Only for the whole space. -/
lemma conjugate_is_positive_homogeneous_iff (f : E → EReal) :
    (∀ m > (0 : ℝ), ∀ x,  (convex_conjugate univ f) (m • x) = m * (convex_conjugate univ f x)) ↔
    ∀ m > (0 : ℝ), ∀ x, (convex_conjugate univ f) x = m * (convex_conjugate univ f (m⁻¹ • x)) := by
  constructor
  · intro hmx m hm x
    have key := hmx m⁻¹ (inv_pos_of_pos hm) x
    rw[key, ← mul_assoc, ← EReal.coe_mul]
    field_simp; simp
  intro hsfx m hm x
  have key := hsfx m hm (m • x)
  have : m⁻¹ • m • x = x :=
    inv_smul_smul₀ (ne_of_lt hm).symm x
  rw[this] at key
  simpa

theorem conjugate_is_positive_homogeneous (s) (f : E → EReal) :
    ∀ m > (0 : ℝ), ∀ x ∈ s,
    (convex_conjugate s (m • f)) x = m * (convex_conjugate s f (m⁻¹ • x)) := by
  intro m hm x _
  simp [convex_conjugate]
  rw[biSup_mul]
  · apply biSup_congr
    intro i _
    rw [mul_sub_mul_sub_mul, ← EReal.coe_mul, ← real_inner_smul_right]
    rw [smul_smul]
    field_simp; simp
  exact hm

lemma conjugate_is_positive_homogeneous_iff' (f : E → EReal) :
    (∀ m > (0 : ℝ), ∀ x,  (convex_conjugate univ f) (m • x) = m * (convex_conjugate univ f x))
    ↔  ∀ m > (0 : ℝ), (convex_conjugate univ f) = (convex_conjugate univ (m • f)) := by
  rw[conjugate_is_positive_homogeneous_iff]
  rw[forall_congr'];intro m
  rw[imp_congr_right];intro hm
  constructor
  · intro h; ext x
    have := conjugate_is_positive_homogeneous univ f m hm x
    simp at this;rw[this]
    apply h x
  intro h x
  have := conjugate_is_positive_homogeneous univ f m hm x
  simp at this;rw[← this]
  exact congrFun h x

end aux

section zero_or_top_iff_positive_homogeneous
/-
thm-13.2
f is ccp →
(f takes only 0 or ⊤ ↔ its conjugate is positive homogeneous)
-/
theorem ccp_zero_or_inf_iff_conjugate_is_positive_homogeneous
    {f : E → EReal} [FiniteDimensional ℝ E]
    [huf : ProperFunction univ f]
    (hfc : ConvexOn ℝ (dom univ f) f)
    (hf : LowerSemicontinuous f) :
    (∀ x, f x = 0 ∨ f x = ⊤) ↔
    ∀ m > (0 : ℝ), ∀ x,  (convex_conjugate univ f) (m • x) = m • (convex_conjugate univ f x) := by
  have := zero_or_inf_iff univ f
  simp at this;
  simp;rw[this, conjugate_is_positive_homogeneous_iff']
  simp
  rw[forall_congr'];intro m
  rw[imp_congr_right];intro hm
  letI smul_proper:  ProperFunction univ (m • f) := by
    apply instProperFunctionHSMulRealForallERealOfGeOfNat huf
    exact (le_of_lt hm)
  rw [ccp_convex_conjugate_bijective ⟨hfc, hf, huf⟩]
  · exact Iff.symm funext_iff
  letI : ProperFunction (dom univ (m • f)) f := by
    rw[dom_eq_smul _ _ hm]
    exact ProperFunction.proper_of_dom
  constructor
  · apply ProperFunctionConvexOn.smul (le_of_lt hm) ?left.hf
    rwa [dom_eq_smul _ _ hm]
  constructor
  · refine smul_lowerSemicontinuous_of_nonneg (le_of_lt hm) hf
  exact smul_proper

end zero_or_top_iff_positive_homogeneous

section cl_eq_support
/- Corollary 13.2.1 -/
/-
f ≠ ⊤ → f convex → cl f is ccp or ⊥
-/
theorem dom_univ_convex_closure_convex (f : E → EReal)
    (hc : ConvexOn ℝ (dom univ f) f) :
    ConvexOn ℝ (dom univ (f.closure univ)) (f.closure univ) := by
  by_cases hp : ProperFunction univ f
  · apply convex_epigraph_convex
    rw [← closure_epi_real_eq_epi_real_closure' f isClosed_univ]
    refine Convex.closure ?hf.hs
    refine convex_epigraph ?hf.hs.hf
    exact convexOn_s_of_convexOn_dom_s_f hc
  by_cases h : ∀ x ∈ univ, f x ≠ ⊥
  · have ht : ∀ x ∈ univ, Function.closure f univ x = ⊤ := by
      have hn : ¬ ∃ x_1 ∈ univ, f x_1 = ⊥ := by
        push_neg; intro x _; rw [top_of_ne_bot_of_ne_proper hp h]; simp; trivial
      simp [Function.closure, hp]
      intro x
      split_ifs; simp
    apply convexOn_dom_s_f_of_convexOn_s
    exact convex_on_p_top' fun x ↦ ht x trivial
  push_neg at h
  have : (Function.closure f univ) = ⊥ := by
    simp [Function.closure, hp]
    rcases h with ⟨x, _, hx2⟩; use x
  rw [this]
  apply convexOn_dom_s_f_of_convexOn_s
  exact convex_on_n_inf rfl

theorem univ_convex_closure_convex [FiniteDimensional ℝ E] (f : E → EReal)
    (hc : ConvexOn ℝ (dom univ f) f) :
    ConvexOn ℝ univ (f.closure univ) := by
  sorry

theorem closure_ccp_or_bot_of_convex_ne_top {f : E → EReal} (hf : f ≠ ⊤)
    (hfc : ConvexOn ℝ (dom univ f) f) [FiniteDimensional ℝ E] :
  (ConvexOn ℝ (dom univ (f.closure univ)) (f.closure univ) ∧
  LowerSemicontinuous (f.closure univ) ∧ ProperFunction univ (f.closure univ)) ∨
  f.closure univ = ⊥ := by
  by_cases hp : ProperFunction univ f
  · left; constructor
    · exact dom_univ_convex_closure_convex f hfc
    constructor
    · exact univ_convex_closure_semicontinuous_of_proper f
    exact univ_convex_closure_proper' f hfc
  right; simp [Function.closure, hp];
  by_contra hx; push_neg at hx
  apply absurd hp; push_neg
  refine (properFunction_iff univ f).mpr ?_
  constructor
  · intro x _
    exact Ne.bot_lt' fun a ↦ hx x (id (Eq.symm a))
  right; by_contra ht; push_neg at ht
  have : f = ⊤ := by ext x; simp; specialize ht x (by trivial); exact eq_top_iff.mpr ht
  apply absurd this hf

theorem conjugate_proper_of_proper {f : E → EReal} (_ : ConvexOn ℝ (dom univ f) f)
    (hf : ProperFunction univ (convex_conjugate univ f)) :
    ProperFunction univ f := by
  constructor
  · obtain ⟨_, hf2⟩ := hf
    intro x _
    by_contra hxl; simp at hxl
    simp at hf2;
    obtain hs := conjugate_of_bot_exist' ⟨x,  hxl⟩
    apply absurd hf2; push_neg
    simp; intro x; rw [congrFun hs x]; simp
  obtain ⟨hf1, hf2⟩ := hf
  simp at *;
  by_contra ht; push_neg at ht; simp at ht
  obtain hs := conjugate_of_top ((eqOn_univ f ⊤).mp fun ⦃x⦄ _ ↦ ht x)
  rcases hf2 with ⟨x, _⟩; specialize hf1 x
  rw [congrFun hs x] at hf1; exact (lt_self_iff_false ⊥).mp hf1

/-
cl f = ⊥ → ∃ x, f x = ⊥
-/
theorem exist_f_bot_of_cl_bot [FiniteDimensional ℝ E] {f : E → EReal}
    (hc : ConvexOn ℝ (dom univ f) f) (hf : f.closure univ = ⊥) : ∃ x, f x = ⊥ := by
  by_cases h : f = ⊤
  · exfalso; rw [h, top_lowersemicontinuoushull_eq_top] at hf; simp at hf
  by_contra hx; push_neg at hx
  have hp : ProperFunction univ f := by
    constructor; intro x _; exact Ne.bot_lt' fun a ↦ hx x (id (Eq.symm a))
    simp; by_contra hx; apply absurd h; push_neg at *; ext x
    simp at hx; exact hx x
  have hn : (dom univ f).Nonempty := univ_proper_dom_not_empty f
  rw [← intrinsicInterior_nonempty hc.1] at hn
  simp [Function.closure, hp] at hf
  let x := Classical.choose hn
  obtain huc := univ_convex_closure_intrinsicInterior f hc x (by apply Classical.choose_spec)
  specialize hx x
  rw [← huc, Function.closure] at hx
  split_ifs at hx
  exact (not_iff_false_intro (congrFun hf x)).mp hx

/-
f is ccp → f* is ccp
-/
theorem conjugate_ccp_if_ccp [FiniteDimensional ℝ E] (f : E → EReal) :
    ConvexOn ℝ (dom univ f) f ∧ LowerSemicontinuous f ∧ ProperFunction univ f →
    ConvexOn ℝ (dom univ (convex_conjugate univ f)) (convex_conjugate univ f) ∧
    LowerSemicontinuous (convex_conjugate univ f) ∧
    ProperFunction univ (convex_conjugate univ f) := by
  intro h
  constructor
  · obtain hs := convex_conjugate_is_convex f
    exact convexOn_dom_s_f_of_convexOn_s hs
  exact ⟨lowerSemicontinuous_convex_conjugate f, proper_convex_proper_conjugate f h.2.2 h.1⟩

/-
f is positive homogeneous → cl f is positive homogeneous
-/
theorem closure_homogeneous_of_homogeneous [FiniteDimensional ℝ E]
    {f : E → EReal}
    (hmf : ∀ m > (0 : ℝ), ∀ x, f (m • x) = m • (f x)) :
    ∀ m > (0 : ℝ), ∀ x, f.closure univ (m • x) = m • (f.closure univ x) := by
  intro m hm x
  by_cases hf : ProperFunction univ f
  · let g := fun x : E => m • x
    simp [closure_eq_liminf]
    have hfg : f ∘ g = fun x => m * f x := by
      ext x
      simpa [g] using hmf m hm x
    have mgng: map g (𝓝 x) = 𝓝 (g x)  := by
      apply IsOpenEmbedding.map_nhds_eq
      apply Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
      constructor
      · exact continuous_const_smul m
      exact ⟨smul_right_injective E  <| (ne_of_lt hm).symm, isOpenMap_smul₀ (ne_of_lt hm).symm⟩
    rw [← mgng, ← Filter.liminf_comp, hfg]
    refine liminf_negconst_mul ?_ (coe_ne_top m)
    refine EReal.coe_nonneg.mpr (le_of_lt hm)
  simp [Function.closure, hf]
  by_cases hxf : ∃ x ∈ univ, f x = ⊥
  · simp [if_pos hxf, coe_mul_bot_of_pos hm]
  simp [if_neg hxf, coe_mul_top_of_pos hm]

/-
f takes values 0 or ⊤ → f = δ (~ | C), C = {x | f x ≤ 0 }
-/
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem eq_le_zero_convex_support_of_zero_or_top
    {f : E → EReal} (hf : ∀ x, f x = 0 ∨ f x = ⊤) :
    f = {x |f x ≤ 0}.convex_indicator := by
  ext x
  simp [Set.convex_indicator]
  rcases hf x with hf | hf
  <;>simp only [hf, le_refl, top_le_iff, zero_ne_top, ↓reduceIte]

/-
{x |convex_conjugate univ f x ≤ 0} = {x | ∀ y, ⟪x, y⟫ - f y ≤ 0}
-/
lemma conjugate_eq_zero_eq_forall_sub_le (f : E → EReal) :
    {x |convex_conjugate univ f x ≤ 0} = {x | ∀ y, ⟪x, y⟫ ≤ f y} := by
  ext x
  simpa using conjugate_le_zero_iff f

/-
f ≠ ⊤ → f convex and positive homogeneous →
cl f = δ* (·| C)
C = {x | f* (x) ≤ 0}
-/
theorem closure_eq_conjugate_of_positive_homogeneous_of_convex_ne_top [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : f ≠ ⊤)
    (hfc : ConvexOn ℝ (dom univ f) f) (hmf : ∀ m > (0 : ℝ), ∀ x, f (m • x) = m • (f x)) :
  f.closure univ = {x |convex_conjugate univ f x ≤ 0}.convex_support := by
  let g := Function.closure f univ
  by_cases hb : ∃ x, f x = ⊥
  · have : ¬ ProperFunction univ f := by
      by_contra hp
      have ht : ∀ x, f x > ⊥ := by intro x; exact ProperFunction.uninfinity (s := univ) x trivial
      rcases hb with ⟨x, hb⟩
      obtain ht := ht x
      rw [hb] at ht; simp at ht
    simp [Function.closure, hb, this]
    have : convex_conjugate univ f = ⊤ := conjugate_of_bot_exist' hb
    rw [this]; simp
    exact Eq.symm convex_support_empty
  have : ProperFunction univ f := by
    refine { uninfinity := ?uninfinity, existence_of_finite_value := ?existence_of_finite_value }
    · push_neg at hb; intro x _
      obtain hb := hb x
      exact Ne.bot_lt' (id (Ne.symm hb))
    simp; by_contra hx; push_neg at hx
    simp at hx; have : f = ⊤ := by ext x; rw [hx x]; simp
    exact hf this
  have : ProperFunction univ (convex_conjugate univ g) := by
    apply proper_convex_proper_conjugate _ _ (dom_univ_convex_closure_convex f hfc)
    apply univ_convex_closure_proper' f hfc
  change g = _
  rcases closure_ccp_or_bot_of_convex_ne_top hf hfc with _ | hcl
  · have hclg : ∀ m > (0 : ℝ), ∀ x, f.closure univ (m • x) = m • (f.closure univ x) :=
      closure_homogeneous_of_homogeneous hmf
    rw [← bi_convex_conjugate_eq_self (f := g)]
    · have : ∀ x, convex_conjugate univ g x = 0 ∨ convex_conjugate univ g x = ⊤ := by
        rw [ccp_zero_or_inf_iff_conjugate_is_positive_homogeneous]
        rw [bi_convex_conjugate_eq_closure (dom_univ_convex_closure_convex f hfc)]
        intro m hm x
        repeat rw [closure_eq_self' (univ_closure_semicontinuous f)
          (univ_convex_closure_convex f hfc)]
        · exact hclg m hm x
        · refine convexOn_dom_s_f_of_convexOn_s (convex_conjugate_is_convex g)
        exact lowerSemicontinuous_convex_conjugate g
      apply eq_le_zero_convex_support_of_zero_or_top at this
      simp [convex_support]
      · rw [this, convex_conjugate_closure_eq_convex_conjugate]
        exact convexOn_s_of_convexOn_dom_s_f hfc
    · exact univ_convex_closure_semicontinuous_of_proper f
    · exact univ_convex_closure_convex f hfc
  · simp [g, conjugate_eq_zero_eq_forall_sub_le, hcl]
    symm
    rw [convex_support_empty_iff, Set.eq_empty_iff_forall_notMem]
    simp;intro x
    have ⟨y, hy⟩:= exist_f_bot_of_cl_bot hfc hcl
    exact ⟨y, by simp [hy]⟩

end cl_eq_support

end zero_or_top_iff_positive_homogeneous
