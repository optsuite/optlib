/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wanyi He, Chenyi Li, Zichen Wang
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.LinearAlgebra.Dual

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} {x : E} {s : Set E}

open Filter

/-- Subgradient of functions --/
def Banach_HasSubgradientAt (f : E → ℝ) (g : E →L[ℝ] ℝ) (x : E) : Prop :=
  ∀ y, f y ≥ f x + g (y - x)

def Banach_HasSubgradientWithinAt (f : E → ℝ) (g : E →L[ℝ] ℝ) (s : Set E) (x : E) : Prop :=
  ∀ y ∈ s, f y ≥ f x + g (y - x)

/-- Subderiv of functions --/
def Banach_SubderivAt (f : E → ℝ) (x : E) : Set (E →L[ℝ] ℝ) :=
  {g : E →L[ℝ] ℝ| Banach_HasSubgradientAt f g x}

def Banach_SubderivWithinAt (f : E → ℝ) (s : Set E) (x : E) : Set (E →L[ℝ] ℝ) :=
  {g : E →L[ℝ] ℝ| Banach_HasSubgradientWithinAt f g s x}

def Epi (f : E → ℝ) (s : Set E) : Set (E × ℝ) :=
  {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}

lemma EpigraphInterior_existence (hc : ContinuousOn f (interior s)) (hx : x ∈ interior s) :
    ∀ t > f x, (x, t) ∈ interior {p : E × ℝ| p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  intro _ _
  have h : IsOpen {p : E × ℝ| (p.1 ∈ interior s) ∧ f p.1 < p.2} := by
    let t := (fun p : E × ℝ => p.fst) ⁻¹' {p : E | p ∈ interior s}
    have h1 : IsOpen t := IsOpen.preimage continuous_fst isOpen_interior
    have h2: ContinuousOn (fun p : (E × ℝ) => f p.fst) t :=
      ContinuousOn.comp hc continuousOn_fst (fun ⦃x⦄ a => a)
    apply ContinuousOn.isOpen_inter_preimage (h2.prod continuousOn_snd) h1 isOpen_lt_prod
  have h' : {p : E × ℝ| p.1 ∈ interior s ∧ f p.1 < p.2} ⊆ {p | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
    fun p ⟨hp1, hp2⟩ => ⟨interior_subset hp1, le_of_lt hp2⟩
  apply interior_mono h'
  rw [IsOpen.interior_eq h]
  exact ⟨hx, by dsimp; linarith⟩

lemma mem_epi_frontier : ∀ y ∈ interior s, (y, f y) ∈
    frontier {p : E × ℝ| p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  intro y ys
  constructor
  · exact subset_closure ⟨interior_subset ys, Eq.ge rfl⟩
  by_contra h
  simp only [mem_interior] at h
  obtain ⟨t, ⟨st, ⟨opent, ht⟩⟩⟩ := h
  simp only [Metric.isOpen_iff] at opent
  obtain ⟨ε, εpos, ballmem⟩ := opent (y, f y) ht
  have : (y, f y - ε / 2) ∈ t := by
    apply ballmem
    simp only [Metric.mem_ball, dist_eq_norm]
    calc
      ‖(y, f y - ε / 2) - (y, f y)‖ = ‖((0 : E), - (ε / 2))‖ := by
        apply congrArg norm (by simp only [Prod.mk_sub_mk, sub_self]; ring_nf)
      _ = ε / 2 := by simp [norm]; exact LT.lt.le (half_pos εpos)
      _ < ε := half_lt_self εpos
  obtain ⟨_, h2⟩ := st this
  simp at h2; linarith

theorem Banach_SubderivWithinAt.Nonempty (hc : ContinuousOn f (interior s)) (hx : x ∈ interior s) (hf : ConvexOn ℝ s f) :
    Set.Nonempty (Banach_SubderivWithinAt f s x) := by
  have hepi_f₁ : Convex ℝ (interior (Epi f s)) := Convex.interior (ConvexOn.convex_epigraph hf)
  have disj : (x , f x) ∉ interior (Epi f s) := by
    by_contra h
    simp only [mem_interior] at h
    obtain ⟨t, ⟨st, ⟨opent, ht⟩⟩⟩ := h
    simp only [Metric.isOpen_iff] at opent
    obtain ⟨ε, εpos, ballmem⟩ := opent (x, f x) ht
    have : (x, f x - ε / 2) ∈ t := by
      apply ballmem
      simp only [Metric.mem_ball, dist_eq_norm]
      calc
        ‖(x, f x - ε / 2) - (x, f x)‖ = ‖((0 : E), - (ε / 2))‖ := by
          apply congrArg norm (by simp only [Prod.mk_sub_mk, sub_self]; ring_nf)
        _ = ε / 2 := by simp [norm]; exact LT.lt.le (half_pos εpos)
        _ < ε := half_lt_self εpos
    obtain ⟨_, h2⟩ := st this
    simp at h2; linarith
  obtain ⟨φ , hφ⟩ := geometric_hahn_banach_point_open hepi_f₁ isOpen_interior disj
  let g := (LinearEquiv.symm (Module.dualProdDualEquivDual ℝ E ℝ)) φ
  have hg : ∀ a, φ a = g.1 a.1 + g.2 a.2 := by
    intro a
    rw [← Module.dualProdDualEquivDual_apply_apply ℝ E ℝ g a]
    apply LinearMap.congr_fun
      ((LinearEquiv.symm_apply_eq (Module.dualProdDualEquivDual ℝ E ℝ)).1 (by rfl)) a
  have hua : ∃ u, ∀ a, g.2 a = u * a := by
    use g.2 1; intro a; simp [g]
    have : a • ((0 : E), 1) = (0, a) := by
      simp only [Prod.smul_mk, smul_eq_mul, smul_zero, mul_one]
    rw [← this, ContinuousLinearMap.map_smulₛₗ]
    simp only [RingHom.id_apply, smul_eq_mul]; ring_nf
  obtain ⟨u , hu⟩ := hua
  have hgu : ∀ a ∈ interior (Epi f s), g.1 x + u * f x < g.1 a.1 + u * a.2 := by
    intro a ha
    have hgu' : g.1 x + g.2 (f x) < g.1 a.1 + g.2 a.2 := by
      obtain hg1 := hg a; obtain hg2 := hg (x , f x)
      rw[← hg1 , ← hg2]; apply hφ a ha
    simp only [hu, hu] at hgu'; exact hgu'
  have hu0 : u > 0 := by
    specialize hgu (x, f x + 1) (EpigraphInterior_existence hc hx (f x + 1) (lt_add_one (f x)))
    dsimp at hgu; linarith
  let h := - (1 / u) • g.1
  have : ∀ (x : E), ‖h x‖ ≤ ((1 / u) * ‖φ‖) * ‖x‖ := by
    intro x; field_simp [h];  simp only [abs_of_pos hu0]
    apply div_le_div_of_nonneg_right _ (by linarith)
    calc
      |φ (x, 0)| = ‖φ (x, 0)‖ := rfl
      _  ≤ ‖φ‖ * ‖(x , (0 : ℝ))‖ := ContinuousLinearMap.le_opNorm φ (x, 0)
      _  = ‖φ‖ * ‖x‖ := by
        simp only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x)]
  have hh : ∃ (C : ℝ), ∀ (x : E), ‖h x‖ ≤ C * ‖x‖ := by
    use ((1 / u) * ‖φ‖)
  let h' := (LinearMap.mkContinuousOfExistsBound h hh)
  have key1 : ∀ a ∈ interior (Epi f s) , h' (a.1 - x) + f x < a.2 := by
    dsimp [h']; intro a ha
    specialize hgu a ha; dsimp [g] at hgu
    have uneq : u ≠ 0 := by linarith
    rw [← mul_lt_mul_iff_of_pos_left hu0]; field_simp
    have eq1 : u * (-φ (a.1 - x, 0) + f x * u) / u = u * f x - φ (a.1 - x, 0) := by
      field_simp; ring_nf
    have eq2 : φ (x, 0) - φ (a.1, 0) = -φ (a.1 - x, 0) := by
      have : φ (x, 0) - φ (a.1, 0) = φ ((x, 0) - (a.1, 0)) := by
        simp only [φ.map_sub]
      simp only [this, Prod.mk_sub_mk, sub_zero]
      have : (-(1 : ℝ)) • (a.1 - x, (0 : ℝ)) = (x - a.1, 0) := by simp
      rw [← this, ContinuousLinearMap.map_smulₛₗ]; simp
    field_simp [h, g, eq1, eq2, hgu]
    rw [div_lt_iff (by positivity)]; rw [← mul_lt_mul_iff_of_pos_left hu0] at hgu
    linarith

  have key2₀ : ∀ a ∈ (Epi f s), a.1 ∈ interior s → h' (a.1 - x) + f x ≤  a.2 := by
    intro a ha posa
    by_cases hfa : f a.1 < a.2
    · apply le_of_lt (key1 a (EpigraphInterior_existence hc posa a.2 hfa))
    have hfa : f a.1 = a.2 := by linarith [ha.2]
    let an : ℕ → E × ℝ := fun n => (a.1, f a.1 + 1 / (n + 1))
    have can2 : Tendsto (fun n => (an n).2) atTop (nhds (f a.1)) := by
      obtain hh := Tendsto.add
        (tendsto_const_nhds) (tendsto_one_div_add_atTop_nhds_zero_nat)
      simp only [add_zero] at hh; exact hh
    have hxn : ∀ (n : ℕ), h' ((an n).1 - x) + f x ≤ (an n).2 := by
      intro n
      have : (1 : ℝ) / (n + 1) > 0 := one_div_pos.mpr (by linarith)
      obtain han : f a.1 + 1 / (n + 1) > f a.1 := by linarith
      apply le_of_lt (key1 (an n) (EpigraphInterior_existence hc posa (an n).2 han))
    simp only [hfa] at can2
    have cleft :
      Tendsto (fun n => h' ((an n).1 - x) + f x) atTop (nhds (h' (a.1 - x) + f x)) := by
      exact tendsto_const_nhds
    apply le_of_tendsto_of_tendsto' cleft ?_ hxn
    simp only [an, hfa]
    exact can2

  have key2₁ : ∀ a ∈ (Epi f s), a.1 ∉ interior s → h' (a.1 - x) + f x ≤ a.2 := by
    intro a ha _
    let an : ℕ → E × ℝ := fun n => ((n : ℝ) / (n + 1)) • a + ((1 : ℝ) / (n + 1)) • (x, f x)
    have han : ∀ (n : ℕ), h' ((an n).1 - x) + f x ≤ (an n).2 := by
      intro n
      have anin : (an n).1 ∈ interior s := by
        dsimp [an]
        apply Convex.combo_self_interior_mem_interior hf.1 ha.1 hx
        · apply div_nonneg (Nat.cast_nonneg n) (by linarith)
        · apply one_div_pos.mpr (by linarith)
        field_simp
      apply key2₀ (an n) ?_ anin
      constructor
      · apply interior_subset anin
      have ineq : ((n : ℝ) / (n + 1)) * f a.1 ≤ ((n : ℝ) / (n + 1)) * a.2 := by
        apply mul_le_mul_of_nonneg_left ha.2 (div_nonneg (Nat.cast_nonneg n) (by linarith))
      calc
      f (an n).1 = f (((n : ℝ) / (n + 1)) • a.1 + ((1 : ℝ) / (n + 1)) • x) := rfl
      _ ≤ ((n : ℝ) / (n + 1)) * f a.1 + ((1 : ℝ) / (n + 1)) * f x := by
        apply hf.2 ha.1 (interior_subset hx) (div_nonneg (Nat.cast_nonneg n) (by linarith))
          (one_div_nonneg.mpr (by linarith)) (by field_simp)
      _ ≤ ((n : ℝ) / (n + 1)) * a.2 + ((1 : ℝ) / (n + 1)) * f x := by linarith
      _ = (an n).2 := rfl
    have c1 : Tendsto (fun (n : ℕ) => ((n : ℝ) / (n + 1))) atTop (nhds 1) :=
      tendsto_natCast_div_add_atTop 1
    have c2 : Tendsto (fun (n : ℕ) => ((1 : ℝ) / (n + 1))) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have can1 : Tendsto (fun n => (an n).1) atTop (nhds a.1) := by
      have ca1 : Tendsto (fun (n : ℕ) => ((n : ℝ) / (n + 1)) • a.1) atTop (nhds a.1) := by
        have : Tendsto (fun (_ : ℕ) => a.1) atTop (nhds a.1) := tendsto_const_nhds
        obtain cc := Tendsto.smul c1 this
        rw [one_smul] at cc; exact cc
      have cx1 : Tendsto (fun (n : ℕ) => ((1 : ℝ) / (n + 1)) • x) atTop (nhds 0) := by
        have : Tendsto (fun (_ : ℕ) => x) atTop (nhds x) := tendsto_const_nhds
        obtain cc := Tendsto.smul c2 this
        rw [zero_smul] at cc; exact cc
      obtain cc := Tendsto.add ca1 cx1
      rw [add_zero] at cc; exact cc
    have can2 : Tendsto (fun n => (an n).2) atTop (nhds a.2) := by
      have ca1 : Tendsto (fun (n : ℕ) => ((n : ℝ) / (n + 1)) * a.2) atTop (nhds a.2) := by
        have : Tendsto (fun (_ : ℕ) => a.2) atTop (nhds a.2) := tendsto_const_nhds
        obtain cc := Tendsto.smul c1 this
        rw [one_smul] at cc; exact cc
      have cx1 : Tendsto (fun (n : ℕ) => ((1 : ℝ) / (n + 1)) * f x) atTop (nhds 0) := by
        have : Tendsto (fun (_ : ℕ) => f x) atTop (nhds (f x)) := tendsto_const_nhds
        obtain cc := Tendsto.smul c2 this
        rw [zero_smul] at cc; exact cc
      obtain cc := Tendsto.add ca1 cx1
      rw [add_zero] at cc; exact cc
    have cleft :
      Tendsto (fun n => h' ((an n).1 - x) + f x) atTop (nhds (h' (a.1 - x) + f x)) := by
      obtain hh := h'.continuous.tendsto
      apply Filter.Tendsto.add_const
      apply Filter.Tendsto.comp (hh (a.1 - x)) (Tendsto.sub_const can1 x)
    apply le_of_tendsto_of_tendsto' cleft can2 han

  have key2 : ∀ a ∈ (Epi f s), h' (a.1 - x) + f x ≤ a.2 := by
    intro a ha
    by_cases posa : a.1 ∈ interior s
    · exact key2₀ a ha posa
    exact key2₁ a ha posa
  have : h' ∈ (Banach_SubderivWithinAt f s x) :=
    fun a ha => (by linarith [key2 (a, f a) ⟨ha, Eq.le rfl⟩])
  use h'
