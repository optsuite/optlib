import Optlib.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences

noncomputable section

open Set InnerProductSpace Topology Filter LinearMap ContinuousLinearMap InnerProduct Function

variable {X Y:Type*}
[NormedAddCommGroup X] [InnerProductSpace ℝ X]
[NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
(A : X →L[ℝ] Y)(fullrank: Injective A)

lemma KerA_bot (fullrank: Injective A): ker A = ⊥ := ker_eq_bot.2 fullrank

variable [CompleteSpace X] [CompleteSpace Y]

lemma KerA_eq_KerA'A : ker A = ker (A†.comp A) := by
  ext x; constructor
  · intro hx
    simp [ContinuousLinearMap.comp_apply]; simp_all
  · intro hx
    have hx' : (A†) (A x) = 0 := by
      simpa [ContinuousLinearMap.comp_apply] using hx
    have hinner : ⟪A x, A x⟫_ℝ = ⟪x, (A†) (A x)⟫_ℝ := by
      dsimp only
      exact Eq.symm (ContinuousLinearMap.adjoint_inner_right A x (A x))
    have : ⟪A x, A x⟫_ℝ = 0 := by
      simpa [hx', inner_zero_right] using hinner
    exact inner_self_eq_zero.mp this

lemma KerA'A_bot (fullrank: Injective A) : ker (A†.comp A) = ⊥ := by
   rw[← KerA_eq_KerA'A]
   apply KerA_bot A fullrank

-- A injective implies A'A injective
lemma A'A_inj (fullrank: Injective A): Injective (A†.comp  A) := ker_eq_bot.1 (KerA'A_bot A fullrank)

-- A'A injective implies A'A surjective
lemma A'A_Sur [FiniteDimensional ℝ X] (fullrank: Injective A): Surjective (A†.comp A) := by
   have H : Module.finrank ℝ X = Module.finrank ℝ X := rfl
   apply (injective_iff_surjective_of_finrank_eq_finrank H).1 (A'A_inj A fullrank)

-- The inverse of A'A is a bounded linear map (X is finite-dimensional)
lemma inv_bounded₁ [FiniteDimensional ℝ X](fullrank: Injective A):∃ C > 0 , ∀ x : X , ‖x‖ ≤ C * ‖(A†.comp A) x‖ := by
   have := exists_preimage_norm_le (A†.comp A) (A'A_Sur A fullrank)
   rcases this with ⟨C , hc , hx⟩
   use C,hc
   intro x
   rcases hx ((A†.comp A) x) with ⟨x1 , hx1⟩
   have h: x = x1 := (A'A_inj A fullrank) hx1.1.symm
   rw[← h] at hx1
   exact hx1.2

lemma inv_bounded₂' :∃ C > 0 , ∀ x : X , ‖(A†.comp A) x‖ ≤ C * ‖A x‖ :=by
   have := isBoundedLinearMap (A†)
   have h :=IsBoundedLinearMap.bound this
   rcases h with ⟨M , h1⟩
   use M , h1.1
   intro x
   have h2 := h1.2 (A x)
   exact h2

--∃ C > 0 , ∀ x : X , ‖x‖ ≤ C * ‖A x‖
lemma inv_bounded₂ [FiniteDimensional ℝ X] (fullrank: Injective A):∃ C > 0 , ∀ x : X , ‖x‖ ≤ C * ‖A x‖ :=by
   rcases inv_bounded₁ A fullrank with ⟨C₁ , h₁⟩
   rcases inv_bounded₂' A  with ⟨C₂ , h₂⟩
   use (C₁ * C₂), (mul_pos h₁.1 h₂.1)
   intro x
   calc ‖x‖
      _ ≤ C₁ * ‖(A†.comp A) x‖ := h₁.2 x
      _ ≤ C₁ * (C₂ * ‖A x‖) := (mul_le_mul_iff_of_pos_left h₁.1).2 (h₂.2 x)
      _ = (C₁ * C₂) * ‖A x‖ := Mathlib.Tactic.RingNF.mul_assoc_rev C₁ C₂ ‖A x‖
