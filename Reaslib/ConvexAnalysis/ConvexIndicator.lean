import Reaslib.Basic.EReal
import Reaslib.Basic.ProperFunction


open Filter BigOperators Set Topology Function Module EReal
section convex_indicator_def

/-
  The indicator function of a convex set --Set.convex_indicator
-/

noncomputable def Set.convex_indicator (s : Set α) (x : α) : EReal :=
  haveI := Classical.decPred (· ∈ s)
  if x ∈ s then 0 else ⊤

end convex_indicator_def

section proper

noncomputable instance ConvexIndicator_is_proper (X : Set α) :
    ProperFunction X (X.convex_indicator) where
  uninfinity := by
    intro a _
    dsimp[Set.convex_indicator]
    simp
    by_cases h1 : a ∈ X
    · rw[if_pos h1];exact EReal.bot_lt_zero
    rw[if_neg h1];exact bot_lt_top
  existence_of_finite_value:= by
    by_cases h: X = ∅
    · left; assumption
    right;
    have : ∃ x , x ∈ X :=
      Set.nonempty_def.mp (Set.nonempty_iff_ne_empty.mpr h)
    rcases this with ⟨x, hx⟩
    use x; constructor;
    · exact hx
    dsimp[Set.convex_indicator]
    rw [if_pos hx]
    exact EReal.zero_lt_top

noncomputable instance ConvexIndicator_is_proper_on_univ {s : Set α} (hs : s.Nonempty) :
    ProperFunction univ (s.convex_indicator) where
  uninfinity := by
    intro a _
    dsimp[Set.convex_indicator]
    simp
    by_cases h1 : a ∈ s
    · rw[if_pos h1];exact EReal.bot_lt_zero
    rw[if_neg h1];exact bot_lt_top
  existence_of_finite_value:= by
    right;
    have ⟨x,hx⟩ := hs
    use x
    dsimp[Set.convex_indicator]
    rw [if_pos hx]
    simp

end proper

section convex

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem indicator_is_convex {X : Set E} (hs : Convex ℝ X) :
    ConvexOn ℝ X (Set.convex_indicator X) := by
  have : ConvexOn ℝ X fun _ ↦ (0: EReal) := by
    dsimp [ConvexOn]
    constructor
    exact hs
    intro x _ y _ a b _ _ _
    simp
  have eq : EqOn (fun _ ↦ (0: EReal)) (Set.convex_indicator X) X := by
    dsimp[EqOn]
    intro x hx
    dsimp [Set.convex_indicator]
    rw [if_pos hx]
  apply ConvexOn.congr this eq

theorem indicator_is_convex_on_univ {s : Set E} (hs : Convex ℝ s) :
    ConvexOn ℝ univ s.convex_indicator :=
  let f := (Set.convex_indicator s)
  ⟨convex_univ, fun x _ y _ a b ha hb hab =>
  calc
    f (a • x + b • y)  ≤ a • f x + b • f y := by
      have os {a b : ℝ}(ha : a ≥ 0)(hb : b ≥ 0)(hab : a + b = 1)
        (u v : E)(h : u ∈ s) : f (a • u + b • v)  ≤ a • f u + b • f v := by
        dsimp[f,Set.convex_indicator]
        by_cases hvs : v ∈ s
        · rw[if_pos h, if_pos hvs, if_pos (hs h hvs ha hb hab)];
          simp
        rw[if_pos h, if_neg hvs]
        simp
        by_cases hb1 : b = 0
        · rw[hb1]
          simp
          have hab : a • u + (0 : ℝ) • v ∈ s := by simp;rw[hb1] at hab;simp at hab;rw[hab];simpa;
          rw[if_pos hab]
        rw[EReal.coe_mul_top_of_pos <| lt_of_le_of_ne hb fun a ↦ hb1 (id (Eq.symm a))]
        simp
      by_cases hxs : x ∈ s
      · exact os ha hb hab x y hxs
      by_cases hys : y ∈ s
      · rw[add_comm];
        nth_rw 2 [add_comm]
        have hab' : b + a = 1 := by rwa[add_comm]
        apply os hb ha hab' y x hys
      dsimp[f,Set.convex_indicator]
      rw[if_neg hxs, if_neg hys]
      by_cases hb1 : b = 0
      · rw[hb1]
        simp
        have ha : a * (⊤ : EReal) = ⊤ := by rw[hb1] at hab;simp at hab;rw[hab];simp
        rw[ha];simp
      have hb : b * (⊤ : EReal) = ⊤ := by
        refine EReal.coe_mul_top_of_pos ?h
        exact lt_of_le_of_ne hb fun a ↦ hb1 (id (Eq.symm a))
      simp; rw[hb]
      have : ↑a * (⊤ : EReal) + ⊤ = ⊤ := by
        refine EReal.add_top_iff_ne_bot.mpr ?_
        simp
        apply EReal.smul_top_ne_bot ha
      rw[this]
      exact OrderTop.le_top _
  ⟩

end convex

section lowerSemicontinuous

variable [TopologicalSpace E]

lemma lowerSemicontinuous_convex_indicator_of_closed {C : Set E} (hc : IsClosed C) :
    LowerSemicontinuous C.convex_indicator := by
  unfold LowerSemicontinuous LowerSemicontinuousAt Set.convex_indicator
  intro x y hy
  rw[eventually_nhds_iff]
  by_cases xc : x ∈ C
  · simp [xc] at hy
    use univ
    constructor
    · intro z
      by_cases zc : z ∈ C
      · simp[zc]; exact hy
      simp[zc]
      apply lt_trans;
      · apply hy
      exact zero_lt_top
    exact ⟨isOpen_univ, Set.mem_univ x⟩
  simp [xc] at hy
  use Cᶜ
  constructor
  · intro z hz
    simp[Set.notMem_of_mem_compl hz];
    exact hy
  exact ⟨isOpen_compl_iff.mpr hc, Set.mem_compl xc⟩

end lowerSemicontinuous
