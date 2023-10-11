/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He
-/
import Analysis.Closed_Function
import Mathlib.Order.Bounds.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.SubsetProperties
import Mathlib.Analysis.NormedSpace.Ray
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.ENorm
/-!
  the Weierstrass theorem
-/
open EReal Function Topology Filter Set TopologicalSpace

variable {𝕜 E: Type _}

variable [LinearOrderedRing 𝕜]

variable [AddCommMonoid E]

variable [Module 𝕜 E]

variable (s : Set E) (f : E → EReal)

variable (ksConvex : Convex (E := E) 𝕜 s)

variable [PseudoMetricSpace E] [TopologicalSpace EReal]

variable [OrderTopology EReal]

variable [FirstCountableTopology E] [FirstCountableTopology EReal]

/- 最优化问题解的存在性 -/

open Metric

-- variable [ProperSpace E]
-- variable [T2Space E]

/- 推广的Weierstrass定理 -/

-- 广义实值函数f是适当且闭的
variable (pf : properfun s f) (cf : closedfunc s f)

lemma l1 (r : EReal) (h : (sublevel s f r).Nonempty): sInf {f x | x ∈ sublevel s f r} = sInf {f x | x ∈ s} := by
  have h₀ : {f x | x ∈ s} = {f x | x ∈ sublevel s f r} ∪ {f x | x ∈ s \ sublevel s f r} := by
    ext y
    constructor
    · rintro ⟨x, xs, xeq⟩
      by_cases xsub : x ∈ sublevel s f r
      · left; exact ⟨x, xsub, xeq⟩
      · right; exact ⟨x, mem_diff_of_mem xs xsub, xeq⟩
    · intro h'
      rcases h' with ⟨x, xsub, xeq⟩ | ⟨x, xnsub, xeq⟩
      · exact Exists.intro x { left := xsub.left, right := xeq }
      · exact Exists.intro x { left := xnsub.left, right := xeq }
  have h₁ : sInf {f x | x ∈ sublevel s f r} ≤ sInf {f x | x ∈ s \ sublevel s f r} := by
    apply sInf_le_sInf_of_forall_exists_le
    intro y ynsub
    rcases h with ⟨y', ysub⟩
    use f y'
    constructor
    · exact ⟨y', ysub, rfl⟩
    · apply le_trans ysub.2
      rcases ynsub with ⟨x, xnsub, xeq⟩
      have : f x > r := by
        have : x ∉ sublevel s f r := xnsub.2
        unfold sublevel at this
        rw [mem_setOf] at this
        push_neg at this
        exact this xnsub.1
      exact Eq.trans_ge xeq (le_of_lt this)
  calc
    sInf {f x | x ∈ sublevel s f r} = sInf {f x | x ∈ sublevel s f r} ⊓ sInf {f x | x ∈ s \ sublevel s f r} :=
      Iff.mpr left_eq_inf h₁
    _ = sInf ({f x | x ∈ sublevel s f r} ∪ {f x | x ∈ s \ sublevel s f r}) := Eq.symm sInf_union
    _ = sInf {f x | x ∈ s} := congrArg sInf (id (Eq.symm h₀))


theorem aux2 (h : ∃ r, (sublevel s f r).Nonempty ∧ IsCompact (sublevel s f r)) :
  {x ∈ s | ∀ y ∈ s, f x ≤ f y}.Nonempty ∧ IsCompact {x ∈ s | ∀ y ∈ s, f x ≤ f y} := by
    rcases h with ⟨r, hne, hbd⟩
    have hs : Set.Nonempty {f x | x ∈ sublevel s f r} := by
      rcases hne with ⟨x, xsub⟩
      exact Exists.intro (f x) (Exists.intro x { left := xsub, right := rfl })
    have hs' : BddBelow {f x | x ∈ sublevel s f r} := OrderBot.bddBelow {f x | x ∈ sublevel s f r}
    rcases exists_seq_tendsto_sInf hs hs' with ⟨fx, _, cfx, fxs⟩
    choose x xsub xeq using fxs
    have sInfeq : sInf {f x | x ∈ sublevel s f r} = sInf {f x | x ∈ s} := l1 s f r hne
    have xs : ∀ (n : ℕ), x n ∈ s := fun n => mem_of_mem_inter_left <| xsub n
    rcases IsCompact.tendsto_subseq hbd xsub with ⟨x', xsub', k, mono, cxk⟩
    have cfxk : Tendsto (f ∘ x ∘ k) atTop (𝓝 (sInf {f x | x ∈ sublevel s f r})) := by
      have xkeq : ∀ (n : ℕ), (f ∘ x ∘ k) n = (fx ∘ k) n := fun n => xeq <| k n
      rw [tendsto_congr xkeq]
      exact Tendsto.comp cfx (StrictMono.tendsto_atTop mono)
    have inepi : ∀ (n : ℕ), (x <| k n, f (x <| k n)) ∈ epigraph s f := by
      unfold epigraph
      intro n
      exact mem_setOf.mp ⟨xs (k n), Eq.le rfl⟩
    have inepi' : (x', sInf {f x | x ∈ sublevel s f r}) ∈ epigraph s f :=
      (IsClosed.isSeqClosed cf) inepi (Tendsto.prod_mk_nhds cxk cfxk)
    have feq : f x' = sInf {f x | x ∈ sublevel s f r} := by
      apply le_antisymm
      · exact (mem_setOf.mp inepi').2
      exact sInf_le (Exists.intro x' { left := xsub', right := rfl })
    have h₀ : x' ∈ {x | x ∈ s ∧ ∀ (y : E), y ∈ s → f x ≤ f y} := by
      constructor
      · exact xsub'.1
      intro y ys
      have : sInf {f x | x ∈ sublevel s f r} ≤ f y := by
        have : sInf {f x | x ∈ s} ≤ f y := by
          apply sInf_le
          exact Exists.intro y { left := ys, right := rfl }
        exact le_of_eq_of_le (l1 s f r hne) this
      exact le_of_eq_of_le feq this
    have h₁ : IsCompact {x | x ∈ s ∧ ∀ (y : E), y ∈ s → f x ≤ f y} := by
      have eq : {x | x ∈ s ∧ ∀ (y : E), y ∈ s → f x ≤ f y} = (sublevel s f <|f x') := by
        ext x
        constructor
        · exact fun ⟨xs, fle⟩ => ⟨xs, fle x' xsub'.1⟩
        intro xsub
        constructor
        · exact xsub.1
        intro y ys
        apply le_trans xsub.2
        calc
          f x' = sInf {f x | x ∈ sublevel s f r} := feq
          _ = sInf {f x | x ∈ s} := sInfeq
          _ ≤ f y := sInf_le ⟨y, ys, rfl⟩
      have : IsCompact (sublevel s f <|f x') := by
        have : (sublevel s f <|f x') ⊆ (sublevel s f r) :=
          fun x xsub => ⟨xsub.1, le_trans xsub.2 xsub'.2⟩
        exact isCompact_of_isClosed_subset hbd (aux31' s f cf (f x')) this
      exact Eq.subst (Eq.symm eq) this
    exact ⟨Set.nonempty_of_mem h₀, h₁⟩

/- 强拟凸函数的定义 -/

def strong_quasi : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (((SMul.smul a  x) : E) + (b • y : E)) < max (f x) (f y)

variable ( hf'' : @strong_quasi 𝕜 _ _ _ _ s f )


/- 唯一性定理 -/
variable (hs' : IsCompact s) -- s是非空、紧且凸的

theorem exist_uniqueness : ∃! x', x' ∈ s ∧ ∀ x ∈ s \ {x'}, f x' < f x := by
  have : {x ∈ s | ∀ y ∈ s, f x ≤ f y}.Nonempty ∧ IsCompact {x ∈ s | ∀ y ∈ s, f x ≤ f y} := by
    rcases pf.1 with ⟨x', ⟨xs, _⟩⟩
    apply aux2 s f cf
    use f x'
    constructor
    · exact Set.nonempty_of_mem (mem_sep xs (Eq.le rfl))
    · exact isCompact_of_isClosed_subset hs' (aux31' s f cf (f x')) (sep_subset s _)
  rcases this.1 with ⟨x', xs', hx'⟩
  have uniq : {x ∈ s | ∀ y ∈ s, f x ≤ f y} = {x'} := by
    rw [Set.eq_singleton_iff_nonempty_unique_mem]
    constructor
    · exact this.1
    intro x xs
    by_contra xneq
    push_neg at xneq
    have eq : max (f x) (f x') = f x' := max_eq_right (xs.2 x' xs')
    have h : f ((0 : 𝕜) • x + (1 : 𝕜) • x') < f x' :=
      Eq.trans_gt eq (hf'' xs.1 xs' xneq (Eq.ge rfl) (by simp) (zero_add 1))
    have h' : f ((0 : 𝕜) • x + (1 : 𝕜) • x') = f x' := by
      congr; rw [zero_smul (R := 𝕜) (m := x), zero_add, one_smul (M := 𝕜) (b := x')]
    exact Eq.not_lt h' h
  use x'
  constructor
  · constructor
    · exact xs'
    intro x xns
    have : f x' ≤ f x := hx' x xns.1
    rcases lt_or_eq_of_le this with hlt | heq
    · exact hlt
    exfalso
    exact xns.2 (Eq.subset uniq ⟨xns.1, fun y ys => Eq.trans_le (Eq.symm heq) (hx' y ys)⟩)
  intro x ⟨xs, hx⟩
  by_cases hxs : x ∈ {x | x = x'}
  · exact hxs
  exfalso
  have : x' ∈ s \ {x} := by
    constructor
    · exact xs'
    simp only [mem_singleton_iff]
    simp only [setOf_eq_eq_singleton, mem_singleton_iff] at hxs
    exact Iff.mpr ne_comm hxs
  exact not_lt_of_ge (hx' x xs) (hx x' this)
