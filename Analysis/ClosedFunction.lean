/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.EReal
import Mathlib.Topology.Basic
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Bases
import Mathlib.Topology.Maps
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.NormedSpace.Ray
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.ENorm
/-!
  the defition of the closed function and the lower semicontinuous function
  need to update the equivalence of the different defitions of lower semicontinuous functions
-/

open EReal Function Topology Filter Set TopologicalSpace

variable {𝕜 E ι : Type _}

section LinearOrderedRing

variable [LinearOrderedRing 𝕜]

section AddCommMonoid

variable [AddCommMonoid E]


variable (s : Set E) (f : E → EReal)

/- 恰当函数 -/
def properfun : Prop :=
  (∃ x ∈ s, f x < ⊤) ∧ (∀ x ∈ s, f x > ⊥)

/- 定义域-/
def dom : Set E :=
  {x | f x < ⊤} ∩ s

/- 下水平集 -/
def sublevel (r : EReal) : Set E :=
  { x ∈ s | f x ≤ r }


/- 上方图 -/
def epigraph : Set <| E × EReal :=
  {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}
-- {p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}


variable [TopologicalSpace 𝕜] [PseudoMetricSpace E] [TopologicalSpace EReal]

variable [SequentialSpace E] [SequentialSpace EReal] [SequentialSpace <| E × EReal]

variable [OrderTopology EReal]

variable [FirstCountableTopology E] [FirstCountableTopology EReal]


/- 闭函数 -/

def IsClosedFun : Prop :=
  IsClosed <| epigraph s f


theorem lowerSemiContinuousOn_iff {s : Set E} {f : E → EReal} :
  LowerSemicontinuousOn f s ↔ (∀ x ∈ s, f x ≤ (liminf f <| 𝓝[s] x)) := by
    constructor
    · intro h x xs
      specialize h x xs
      unfold LowerSemicontinuousWithinAt at h
      apply Filter.le_liminf_of_le isCobounded_ge_of_top
      sorry
    · intro h x xs y ylt
      apply Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le ylt (h x xs))



section IsClosed

variable {s f}

/-
闭函数的等价性：
· f(x)的任意下水平集都是闭集
· f(x)是下半连续的
· f(x)是闭函数
证明: 1) => 2), 2) => 3), 3) => 1)
-/

theorem lowerSemicontinuousOn_of_isClosed_sublevel' (hf : ∀ (r : EReal), IsClosed <| sublevel s f r) :
  ∀ x ∈ s, f x ≤ (liminf f <| 𝓝[s] x) := by
    by_contra h; push_neg at h
    obtain ⟨x, ⟨_, hx⟩⟩ := h
    obtain ⟨t, ⟨ltt, tlt⟩⟩ := exists_between hx
    have : x ∈ sublevel s f t := by
      apply isClosed_iff_frequently.mp (hf t) x
      apply frequently_iff.mpr; intro _ hu
      have h : ∃ᶠ (y : E) in 𝓝[s] x, f y ≤ t := by
        apply frequently_iff.mpr; intro _ hu
        obtain ⟨x, xu, fx⟩ := (frequently_iff.mp (frequently_lt_of_liminf_lt (by isBoundedDefault) ltt)) hu
        exact Exists.intro x ⟨xu, LT.lt.le fx⟩
      obtain ⟨x, xu, fx, xs⟩ := (frequently_iff.mp (frequently_nhdsWithin_iff.mp h)) hu
      exact Exists.intro x ⟨xu, ⟨xs, fx⟩⟩
    apply not_le_of_gt tlt this.2

theorem lowerSemicontinuousOn_of_isClosed_sublevel (hf : ∀ (r : EReal), IsClosed <| sublevel s f r) :
  LowerSemicontinuousOn f s :=
    lowerSemiContinuousOn_iff.mpr fun x a => lowerSemicontinuousOn_of_isClosed_sublevel' hf x a

theorem IsClosedFun.isClosed_sublevel (hf : IsClosedFun s f) : ∀ (r : EReal), IsClosed (sublevel s f r) :=
  fun _ => IsSeqClosed.isClosed fun ⦃_⦄ ⦃_⦄ xns cx =>
    IsClosed.isSeqClosed hf (fun n => xns n) (Tendsto.prod_mk_nhds cx tendsto_const_nhds)

theorem LowerSemicontinuousOn.isClosedFun' (hs : IsClosed s) (hf : ∀ x ∈ s, f x ≤ (liminf f <| 𝓝[s] x)) :
  IsClosedFun s f := by
    apply IsSeqClosed.isClosed
    intro f' ⟨x', y'⟩ hxy cxy
    rw [Prod.tendsto_iff] at cxy
    let x : ℕ -> E := fun (n : ℕ) => (f' n).1
    have h1 := isSeqClosed_iff_isClosed.mpr hs (fun n => (hxy n).1) cxy.1
    constructor
    · exact h1
    obtain cx := tendsto_nhdsWithin_iff.mpr ⟨cxy.1, eventually_of_forall (fun n => (hxy n).1)⟩
    obtain xley :=
      fun n => Trans.trans (Trans.trans (Eq.refl ((f ∘ x) n)) (hxy n).2) (Eq.refl (f' n).2)
    calc
        f x' ≤ liminf f (𝓝[s] x') := hf x' h1
        _ = sSup {a | ∀ᶠ (n : E) in 𝓝[s] x', a ≤ f n} := by rw[liminf_eq]
        _ ≤ sSup {a | ∀ᶠ (n : ℕ) in atTop, a ≤ (f ∘ x) n} :=
          sSup_le_sSup
            fun _ fa => (eventually_iff_seq_eventually.mp <| mem_setOf.mp fa) x cx
        _ = liminf (f ∘ x) atTop := by rw[← liminf_eq]
        _ ≤ liminf (fun (n : ℕ) => (f' n).2) atTop := liminf_le_liminf (eventually_of_forall xley)
        _ = y' := (cxy.2).liminf_eq

theorem LowerSemicontinuousOn.isClosedFun (hs : IsClosed s) (hf : LowerSemicontinuousOn f s) :
  IsClosedFun s f :=
    LowerSemicontinuousOn.isClosedFun' hs (lowerSemiContinuousOn_iff.mp hf)

variable (hs : IsClosed s)

/- f(x)的任意下水平集都是闭集 ↔ f(x)是下半连续的 -/

theorem isClosed_sublevel_iff_lowerSemicontinuousOn :
  (∀ (r : EReal), IsClosed <| sublevel s f r) ↔ LowerSemicontinuousOn f s :=
    ⟨fun h => lowerSemicontinuousOn_of_isClosed_sublevel h,
      fun h => IsClosedFun.isClosed_sublevel (LowerSemicontinuousOn.isClosedFun hs h)⟩

/- f(x)是下半连续的 ↔ f(x)是闭函数 -/
theorem lowerSemicontinuousOn_iff_isClosedFun : LowerSemicontinuousOn f s ↔ IsClosedFun s f :=
  ⟨fun h => LowerSemicontinuousOn.isClosedFun hs h,
    fun h => lowerSemicontinuousOn_of_isClosed_sublevel fun r => IsClosedFun.isClosed_sublevel h r⟩

/- f(x)是闭函数 ↔ f(x)的任意下水平集都是闭集 -/
theorem isClosedFun_iff_isClosed_sublevel : IsClosedFun s f ↔ (∀ (r : EReal), IsClosed <| sublevel s f r) :=
  ⟨fun h r => IsClosedFun.isClosed_sublevel h r,
    fun h => LowerSemicontinuousOn.isClosedFun' hs fun x a => lowerSemicontinuousOn_of_isClosed_sublevel' h x a⟩


end IsClosed

theorem ContinuousOn.isClosedFun (hs : IsClosed s) (hf : ContinuousOn f s) :
  IsClosedFun s f := IsClosed.epigraph hs hf

/- 闭函数经过简单运算还是闭函数 -/
-- 加法

theorem IsClosedFun.add [ContinuousAdd EReal] {f g : E → EReal}
  (hs : IsClosed s) (hf : IsClosedFun s f) (hg : IsClosedFun s g) :
    IsClosedFun s (f + g) := by
      rw [← lowerSemicontinuousOn_iff_isClosedFun hs]
      rw [← lowerSemicontinuousOn_iff_isClosedFun hs] at hf
      rw [← lowerSemicontinuousOn_iff_isClosedFun hs] at hg
      apply LowerSemicontinuousOn.add hf hg

theorem isClosedFun_sum [ContinuousAdd EReal] {f : ι → E → EReal} {a : Finset ι}
  (hs : IsClosed s) (ha : ∀ (i : ι), i ∈ a → IsClosedFun s (f i)) :
    IsClosedFun s (fun z => Finset.sum a fun i => f i z) :=
    (lowerSemicontinuousOn_iff_isClosedFun hs).mp
      (lowerSemicontinuousOn_sum fun i ia => (lowerSemicontinuousOn_iff_isClosedFun hs).mpr (ha i ia))


theorem isClosedFun_iSup {f : ι → E → EReal} (hs : IsClosed s) (h : ∀ (i : ι), IsClosedFun s (f i)) :
  IsClosedFun s (fun x' => ⨆ (i : ι), f i x') :=
    (lowerSemicontinuousOn_iff_isClosedFun hs).mp
      (lowerSemicontinuousOn_iSup (fun i => (lowerSemicontinuousOn_iff_isClosedFun hs).mpr (h i)))

theorem isClosedFun_comp_continuous {s : Set E} {f : E → EReal} {g : E → E}
  (hf : IsClosedFun (g '' s) f) (hg : Continuous g) : IsClosedFun s (f ∘ g) := by
    sorry