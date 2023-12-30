/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wanyi He, Zaiwen Wen
-/
import Mathlib.Topology.Sequences
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuous

/-!
## Main results

We introduce some equivalent definitions of LowerSemicontinuous functions.
* `lowerSemicontinuous_iff_le_liminf`:
  a function is lower semi-continuous if and only if `∀ x, f x ≤ (liminf f <| 𝓝 x)`
* `lowerSemicontinuous_iff_IsClosed_epigraph`:
  a function is lower semi-continuous if and only if its epigraph is closed.

## References

* <https://en.wikipedia.org/wiki/Closed_convex_function>
* <https://en.wikipedia.org/wiki/Semi-continuity>

-/


open Topology Filter Set TopologicalSpace

variable {𝕜 E F α β ι : Type*}

variable [AddCommMonoid E]

variable [CompleteLinearOrder F] [DenselyOrdered F]

variable {x : E} {s t : Set E} {f : E → F}

variable [TopologicalSpace E] [TopologicalSpace F]


section

theorem lowerSemicontinuousAt_iff_le_liminf :
    LowerSemicontinuousAt f x ↔ f x ≤ (liminf f <| 𝓝 x) := by
  constructor
  · intro hf; unfold LowerSemicontinuousAt at hf
    contrapose! hf
    obtain ⟨y,lty,ylt⟩ := exists_between hf; use y
    exact ⟨ylt, fun h => not_le_of_lt lty
      (Filter.le_liminf_of_le (by isBoundedDefault)
        (Eventually.mono h (fun _ hx => le_of_lt hx)))⟩
  exact fun hf y ylt => Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le ylt hf)

theorem LowerSemicontinuousAt.le_liminf (hf : LowerSemicontinuousAt f x) :
    f x ≤ (liminf f <| 𝓝 x) :=
  lowerSemicontinuousAt_iff_le_liminf.mp hf

theorem lowerSemicontinuous_iff_le_liminf :
    LowerSemicontinuous f ↔ ∀ x, f x ≤ (liminf f <| 𝓝 x) := by
  simp only [← lowerSemicontinuousAt_iff_le_liminf, LowerSemicontinuous]

theorem LowerSemicontinuous.le_liminf (hf : LowerSemicontinuous f) :
    ∀ x, f x ≤ (liminf f <| 𝓝 x) :=
  lowerSemicontinuous_iff_le_liminf.mp hf

theorem lowerSemicontinuousWithinAt_iff_le_liminf :
    LowerSemicontinuousWithinAt f s x ↔ f x ≤ (liminf f <| 𝓝[s] x) := by
  constructor
  · intro hf; unfold LowerSemicontinuousWithinAt at hf
    contrapose! hf
    obtain ⟨y,lty,ylt⟩ := exists_between hf; use y
    exact ⟨ylt, fun h => not_le_of_lt lty
      (Filter.le_liminf_of_le (by isBoundedDefault)
        (Eventually.mono h (fun _ hx => le_of_lt hx)))⟩
  exact fun hf y ylt => Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le ylt hf)

theorem LowerSemicontinuousWithinAt.le_liminf (hf : LowerSemicontinuousWithinAt f s x) :
    f x ≤ (liminf f <| 𝓝[s] x) :=
  lowerSemicontinuousWithinAt_iff_le_liminf.mp hf

theorem lowerSemicontinuous_on_iff_le_liminf :
    LowerSemicontinuousOn f s ↔ ∀ x ∈ s, f x ≤ (liminf f <| 𝓝[s] x) := by
  simp only [← lowerSemicontinuousWithinAt_iff_le_liminf, LowerSemicontinuousOn]

theorem LowerSemicontinuousOn.le_liminf (hf : LowerSemicontinuousOn f s) :
    ∀ x ∈ s, f x ≤ (liminf f <| 𝓝[s] x) :=
  lowerSemicontinuous_on_iff_le_liminf.mp hf

end

section

variable [FirstCountableTopology E] [FirstCountableTopology F]

variable [OrderTopology F]

theorem lowerSemicontinuous_iff_IsClosed_epigraph :
    LowerSemicontinuous f ↔ IsClosed {p : E × F | f p.1 ≤ p.2} := by
  constructor
  · simp only [lowerSemicontinuous_iff_le_liminf]
    intro hf; apply IsSeqClosed.isClosed
    intro f' ⟨x', y'⟩ hxy cxy
    rw [Prod.tendsto_iff] at cxy
    let x : ℕ -> E := fun (n : ℕ) => (f' n).1
    calc
      f x' ≤ liminf f (𝓝 x') := hf x'
      _ ≤ liminf (f ∘ x) atTop := by
        simp only [liminf_eq, liminf_eq]
        exact sSup_le_sSup (fun _ fa => (eventually_iff_seq_eventually.mp fa) x cxy.1)
      _ ≤ liminf (fun (n : ℕ) => (f' n).2) atTop :=
        liminf_le_liminf (eventually_of_forall (fun n => by convert hxy n))
      _ = y' := (cxy.2).liminf_eq
  simp only [lowerSemicontinuous_iff_isClosed_preimage]
  intro hf y; apply IsSeqClosed.isClosed
  exact fun _ _ xns cx =>
    IsClosed.isSeqClosed hf (fun n => xns n) (Tendsto.prod_mk_nhds cx tendsto_const_nhds)

theorem LowerSemicontinuous.IsClosed_epigraph {f : E → F} (hf : LowerSemicontinuous f) :
    IsClosed {p : E × F | f p.1 ≤ p.2} :=
  lowerSemicontinuous_iff_IsClosed_epigraph.mp hf

end
