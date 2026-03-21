/-
Copyright (c) 2024 Chenyi Li, Bowen Yang, Yifan Bai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Bowen Yang, Yifan Bai
-/
import Optlib.Algorithm.BCD.Scheme
import Mathlib.Tactic

/-!
# Block Coordinate Descent

## Main results

This file mainly concentrates on the convergence of the block coordinate descent method.

- We give the formalization of the sufficient descent lemma.
- We prove the upper bound of the subdifferential.
- We prove the properties of the limit points.
- We give the convergence under the assumption of the KL property.

-/

open Set Bornology Filter BigOperators Topology BCD

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def limit_set (z : ℕ → E) :=
  {x | MapClusterPt x atTop z}

end

section block_subdifferential

variable {E : Type*} [NormedAddCommGroup E]

lemma infEdist_bound {s : Set E} : ∀ x ∈ s, ENNReal.ofReal ‖x‖ ≥ Metric.infEDist 0 s := by
  by_cases hs : s = ∅
  simp [hs]
  push_neg at hs
  intro x xs
  have : Metric.infEDist 0 s ≤ edist 0 x := Metric.infEDist_le_edist_of_mem xs
  rw [← dist_zero_left]
  apply (ENNReal.le_ofReal_iff_toReal_le _ _).2
  · exact ENNReal.toReal_le_of_le_ofReal dist_nonneg (edist_dist 0 x ▸ this)
  · exact Metric.infEDist_ne_top hs
  · simp

variable {F: Type*} [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {f : E → ℝ} {g : F → ℝ} {x u : E} {y v : F}

lemma f_subdiff_block (hf : u ∈ f_subdifferential f x) (hg : v ∈ f_subdifferential g y) :
    ((u, v) : WithLp 2 (E × F)) ∈
      f_subdifferential (fun z ↦ f z.fst + g z.snd : WithLp 2 (E × F) → ℝ)
        ((x, y) : WithLp 2 (E × F)) := by
  rw [has_f_subdiff_iff] at *
  intro ε εpos
  have ε2pos : 0 < ε / 2 := by positivity
  have hfx : ∀ᶠ z : WithLp 2 (E × F) in 𝓝 ((x, y) : WithLp 2 (E × F)),
      f z.fst - f x - inner ℝ u (z.fst - x) ≥ -(ε / 2) * ‖z.fst - x‖ :=
    Filter.Tendsto.eventually
      ((WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := F)).tendsto
        ((x, y) : WithLp 2 (E × F))) (hf _ ε2pos)
  have hgy : ∀ᶠ z : WithLp 2 (E × F) in 𝓝 ((x, y) : WithLp 2 (E × F)),
      g z.snd - g y - inner ℝ v (z.snd - y) ≥ -(ε / 2) * ‖z.snd - y‖ :=
    Filter.Tendsto.eventually
      ((WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := F)).tendsto
        ((x, y) : WithLp 2 (E × F))) (hg _ ε2pos)
  filter_upwards [hfx, hgy] with z hfz hyz
  rw [WithLp.prod_inner_apply]
  let z' : WithLp 2 (E × F) := (x, y)
  show f z.fst + g z.snd - (f x + g y) - (⟪u, z.fst - x⟫ + ⟪v, z.snd - y⟫) ≥ -ε * ‖z - z'‖
  have h1 : ‖z.fst - x‖ ≤ ‖z - z'‖ := fst_norm_le_prod_L2 (z - z')
  have h2 : ‖z.snd - y‖ ≤ ‖z - z'‖ := snd_norm_le_prod_L2 (z - z')
  linarith [(mul_le_mul_iff_of_pos_left ε2pos).mpr h1, (mul_le_mul_iff_of_pos_left ε2pos).mpr h2]

end block_subdifferential

section Convergence

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → ℝ} {g : F → ℝ} {H : (WithLp 2 (E × F)) → ℝ} {x0 : E} {y0 : F} {l : NNReal}
variable {alg : BCD f g H l x0 y0}

section descent

/- PALM descent -/
theorem PALM_Descent (h : E → ℝ) {h' : E → E} (Lₕ : NNReal)
    (h₁ : ∀ x₁ : E, HasGradientAt h (h' x₁) x₁) (h₂ : LipschitzWith Lₕ h')
    (σ : E → ℝ) (t : ℝ) (h₅ : 0 < t) :
    ∀ (u : E), ∀ u₁ ∈ prox_set (fun a ↦ t * (σ a)) (u - t • (h' u)),
    h u₁ + σ u₁ ≤ h u + σ u - 1 / 2 * (1 / t - Lₕ) * ‖u₁ - u‖ ^ 2 := by
  intro u u₁ u₁prox
  simp only [prox_set, prox_prop, isMinOn_iff, mem_univ, mem_setOf_eq] at u₁prox
  specialize u₁prox u trivial
  have : u - (u - t • h' u) = t • h' u := by abel
  rw [this] at u₁prox
  have : u₁ - (u - t • h' u) = (u₁ - u) + t • h' u := by abel
  rw [this] at u₁prox
  simp [norm_add_sq_real] at u₁prox
  have ha : t * σ u₁ + ‖u₁ - u‖ ^ 2 / 2 +  ⟪u₁ - u, t • h' u⟫ ≤ t * σ u := by linarith [u₁prox]
  rw [inner_smul_right] at ha
  have : t * (‖u₁ - u‖ ^ 2 / (2 * t)) = ‖u₁ - u‖ ^ 2 / 2 := by
    field_simp [ne_of_gt h₅]
  rw [← this] at ha
  have : t * σ u₁ + t * (‖u₁ - u‖ ^ 2 / (2 * t)) + t * ⟪u₁ - u, h' u⟫
        = t * (σ u₁ + ‖u₁ - u‖ ^ 2 / (2 * t) + ⟪u₁ - u, h' u⟫) := by ring
  rw [this] at ha
  have hne : ⟪u₁ - u, h' u⟫ ≤ σ u - σ u₁ - ‖u₁ - u‖ ^ 2 / (2 * t) := by
    have hmul : σ u₁ + ‖u₁ - u‖ ^ 2 / (2 * t) + ⟪u₁ - u, h' u⟫ ≤ σ u := by
      exact le_of_mul_le_mul_left ha h₅
    linarith [hmul]
  rw [real_inner_comm] at hne
  calc
    _ ≤ h u + σ u - σ u₁ - ‖u₁ - u‖ ^ 2 / (2 * t) + ↑Lₕ / 2 * ‖u₁ - u‖ ^ 2 + σ u₁ := by
      linarith [hne, lipschitz_continuos_upper_bound' h₁ h₂ u u₁]
    _ = h u + σ u - 1 / 2 * (1 / t - ↑Lₕ) * ‖u₁ - u‖ ^ 2 := by
      field_simp [ne_of_gt h₅]; ring

/- sufficient descent -/
theorem Sufficient_Descent1 (γ : ℝ) (hγ : γ > 1)
    (ck : ∀ k, alg.c k = 1 / (γ * l)) (dk : ∀ k, alg.d k = 1 / (γ * l)) :
    ∃ ρ₁ > 0, ρ₁ = (γ - 1) * l ∧ ∀ k, ρ₁ / 2 * ‖alg.z (k+1) - alg.z k‖ ^ 2
      ≤ alg.ψ (alg.z k) -alg.ψ (alg.z (k + 1)) := by
  use (γ - 1) * l
  let ρ₁ := (γ - 1) * l
  constructor; apply mul_pos; linarith; exact alg.lpos;
  constructor; rfl
  obtain ⟨l1, l2⟩ := alg.coordinate_lip
  intro k
  have hHf : H (alg.x (k + 1), alg.y k) + f (alg.x (k + 1)) ≤ H (alg.x k, alg.y k) + f (alg.x k)
      - 1 / 2 * (γ - 1) * l * ‖alg.x (k + 1) - alg.x k‖ ^ 2 := by
    let h  := fun x ↦ H (WithLp.toLp 2 (x, alg.y k))
    let h' := fun x ↦ grad_fst H (alg.y k) x
    have h1 : ∀ x₁ : E, HasGradientAt h (h' x₁) x₁ := by
      intro x
      rw [hasGradientAt_iff_hasFDerivAt]
      have hH' : HasFDerivAt H ((InnerProductSpace.toDual ℝ (WithLp 2 (E × F)))
          (gradient H (WithLp.toLp 2 (x, alg.y k)))) (WithLp.toLp 2 (x, alg.y k)) := by
        exact (DifferentiableAt.hasGradientAt (h := (alg.Hdiff (WithLp.toLp 2 (x, alg.y k))))).hasFDerivAt
      have htoLp : HasFDerivAt (WithLp.toLp 2)
          (IsBoundedLinearMap.toContinuousLinearMap (WithLp.toLp 2) instIsBoundedLinearMapL2equiv)
          ((x, alg.y k) : E × F) := instIsBoundedLinearMapL2equiv.hasFDerivAt
      have hpair : HasFDerivAt (fun x : E => ((x, alg.y k) : E × F)) (ContinuousLinearMap.inl ℝ E F) x := by
        simpa using (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (alg.y k))
      have hcomp : HasFDerivAt (fun x : E => H (WithLp.toLp 2 (x, alg.y k)))
          ((((InnerProductSpace.toDual ℝ (WithLp 2 (E × F))) (gradient H (WithLp.toLp 2 (x, alg.y k)))).comp
            (IsBoundedLinearMap.toContinuousLinearMap (WithLp.toLp 2) instIsBoundedLinearMapL2equiv)).comp
            (ContinuousLinearMap.inl ℝ E F)) x := by
        simpa [Function.comp] using (hH'.comp x (htoLp.comp x hpair))
      refine hcomp.congr_fderiv ?_
      ext u
      have hfst : ((IsBoundedLinearMap.toContinuousLinearMap (WithLp.toLp 2) instIsBoundedLinearMapL2equiv)
          ((u, (0 : F)) : E × F)).fst = u := rfl
      have hsnd : ((IsBoundedLinearMap.toContinuousLinearMap (WithLp.toLp 2) instIsBoundedLinearMapL2equiv)
          ((u, (0 : F)) : E × F)).snd = 0 := rfl
      simp [h', grad_fst, ContinuousLinearMap.comp_apply, hfst, hsnd]
    obtain prop := PALM_Descent h l h1 (l1 _) f (alg.c k) (alg.cpos γ hγ ck k) (alg.x _) (alg.x _)
    apply le_of_le_of_eq (prop (by rw [prox_set]; simp; exact (alg.s₁ k)))
    rw [ck, one_div_one_div]; ring

  have hHg : H (alg.x (k + 1), alg.y (k + 1)) + g (alg.y (k + 1)) ≤ H (alg.x (k + 1), alg.y k)
      + g (alg.y k) - 1 / 2 * (γ - 1) * l * ‖alg.y (k + 1) - alg.y k‖ ^ 2 := by
    let h := fun y ↦ H (WithLp.toLp 2 (alg.x (k + 1), y))
    let h':= fun y ↦ grad_snd H (alg.x (k + 1)) y
    have h1 : ∀ y₁ : F, HasGradientAt h (h' y₁) y₁ := by
      intro y
      rw [hasGradientAt_iff_hasFDerivAt]
      have hH' : HasFDerivAt H ((InnerProductSpace.toDual ℝ (WithLp 2 (E × F)))
          (gradient H (WithLp.toLp 2 (alg.x (k + 1), y)))) (WithLp.toLp 2 (alg.x (k + 1), y)) := by
        exact (DifferentiableAt.hasGradientAt (h := (alg.Hdiff (WithLp.toLp 2 (alg.x (k + 1), y))))).hasFDerivAt
      have htoLp : HasFDerivAt (WithLp.toLp 2)
          (IsBoundedLinearMap.toContinuousLinearMap (WithLp.toLp 2) instIsBoundedLinearMapL2equiv)
          ((alg.x (k + 1), y) : E × F) := instIsBoundedLinearMapL2equiv.hasFDerivAt
      have hpair : HasFDerivAt (fun y : F => ((alg.x (k + 1), y) : E × F)) (ContinuousLinearMap.inr ℝ E F) y := by
        simpa using (hasFDerivAt_prodMk_right (𝕜 := ℝ) (alg.x (k + 1)) y)
      have hcomp : HasFDerivAt (fun y : F => H (WithLp.toLp 2 (alg.x (k + 1), y)))
          ((((InnerProductSpace.toDual ℝ (WithLp 2 (E × F))) (gradient H (WithLp.toLp 2 (alg.x (k + 1), y)))).comp
            (IsBoundedLinearMap.toContinuousLinearMap (WithLp.toLp 2) instIsBoundedLinearMapL2equiv)).comp
            (ContinuousLinearMap.inr ℝ E F)) y := by
        simpa [Function.comp] using (hH'.comp y (htoLp.comp y hpair))
      refine hcomp.congr_fderiv ?_
      ext v
      have hfst : ((IsBoundedLinearMap.toContinuousLinearMap (WithLp.toLp 2) instIsBoundedLinearMapL2equiv)
          (((0 : E), v) : E × F)).fst = 0 := rfl
      have hsnd : ((IsBoundedLinearMap.toContinuousLinearMap (WithLp.toLp 2) instIsBoundedLinearMapL2equiv)
          (((0 : E), v) : E × F)).snd = v := rfl
      simp [h', grad_snd, ContinuousLinearMap.comp_apply, hfst, hsnd]
    obtain prop := PALM_Descent h l h1 (l2 _) g (alg.d k) (alg.dpos γ hγ dk k) (alg.y k) (alg.y _)
    apply le_of_le_of_eq (prop (by rw [prox_set]; simp; exact (alg.s₂ k)))
    rw [dk, one_div_one_div]; ring

  have eq (k : ℕ) : alg.ψ (alg.z k) = H (alg.x k, alg.y k) + f (alg.x k) + g (alg.y k) := by
    rw [BCD.ψ]; nth_rw 2 [add_assoc]; nth_rw 1 [add_comm]
    apply add_right_cancel_iff.2; rfl
  calc
    _ = H (alg.x k, alg.y k) + f (alg.x k) + g (alg.y k) - H (alg.x (k + 1), alg.y (k + 1))
        - f (alg.x (k + 1)) - g (alg.y (k + 1)) := by rw [eq k, eq (k + 1)]; ring
    _ ≥ 1 / 2 * (γ - 1) * l * (‖alg.x (k + 1) - alg.x k‖ ^ 2
        + ‖alg.y (k + 1) - alg.y k‖ ^ 2) := by linarith [hHf,hHg]
    _ = 1 / 2 * ρ₁ * (‖alg.x (k + 1) - alg.x k‖ ^ 2 + ‖alg.y (k + 1) - alg.y k‖ ^ 2) := by
      unfold ρ₁; ring
    _ = _ := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp [BCD.z]
      left
      unfold ρ₁
      ring

/- the value is monotone -/
theorem Sufficient_Descent2 (γ : ℝ) (hγ : γ > 1)
    (ck : ∀ k, alg.c k = 1 / (γ * l)) (dk : ∀ k, alg.d k = 1 / (γ * l)) :
    ∀ (k : ℕ), alg.ψ (alg.z (k + 1)) ≤ alg.ψ (alg.z k) := by
  rcases Sufficient_Descent1 γ hγ ck dk with ⟨ρ₁, ⟨hρ₁, ⟨_, h2⟩⟩⟩
  intro k; specialize h2 k
  have hne : 0 ≤ ρ₁ / 2 * ‖alg.z (k + 1) - alg.z k‖ ^ 2 := by positivity
  linarith

/- The difference series squares are summable-/
theorem Sufficient_Descent3 (γ : ℝ) (hγ : γ > 1) (ck: ∀ k, alg.c k = 1 / (γ * l))
    (dk: ∀ k, alg.d k = 1 / (γ * l)) (lbdψ : BddBelow (alg.ψ '' univ)) :
    ∃ (A : ℝ), Tendsto (fun (n : ℕ) ↦ ∑ k ∈ Finset.range n,
      ‖alg.z (k + 1) - alg.z k‖ ^ 2) atTop (𝓝 A) := by
  rcases Sufficient_Descent1 γ hγ ck dk with ⟨ρ₁, ⟨hρ₁, ⟨_, h2⟩⟩⟩
  have hDescent' : ∀ k, ‖alg.z (k + 1) - alg.z k‖ ^ 2
      ≤ 2 / ρ₁ * (alg.ψ (alg.z k) - alg.ψ (alg.z (k + 1))):= by
    intro k; specialize h2 k
    obtain h1 := mul_le_mul_of_nonneg_left h2 (a := 2 / ρ₁) (by positivity)
    rw [← mul_assoc] at h1; field_simp at h1; field_simp; simpa [mul_comm] using h1
  have hne : ∀ n, ∑ k ∈ Finset.range (n + 1), ‖alg.z (k + 1) - alg.z k‖ ^ 2
      ≤ 2 / ρ₁ * ((alg.ψ (alg.z 0)) - (alg.ψ (alg.z (n + 1)))) := by
    intro n
    induction n with
    | zero =>
        simp; specialize hDescent' 0
        simpa using hDescent'
    | succ d hd =>
        rw [Finset.sum_range_succ _ (d + 1)]
        have : 2 / ρ₁ * (alg.ψ (alg.z 0) - alg.ψ (alg.z (d + 1 + 1)))
            = 2 / ρ₁ * (alg.ψ (alg.z 0) - alg.ψ (alg.z (d + 1)))
            + 2 / ρ₁ * (alg.ψ (alg.z (d + 1)) - alg.ψ (alg.z (d + 1 + 1))) := by ring
        rw [this]
        exact add_le_add hd (hDescent' (d + 1))
  simp [BddBelow,lowerBounds,Set.Nonempty] at lbdψ
  rcases lbdψ with ⟨ψ₀,hψ₀⟩
  obtain hne' := fun n ↦ le_trans (hne n) (mul_le_mul_of_nonneg_left
      (tsub_le_tsub_left (hψ₀ (alg.z (n+1))) (ψ (z 0))) (by positivity))
  set S := fun (n : ℕ) ↦ ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2
  have hne'': ∀ n ≥ 1, S n ≤ 2 / ρ₁ * (alg.ψ (alg.z 0) - ψ₀) := by
    intros n nge1
    specialize hne' (n-1)
    rw [Nat.sub_add_cancel nge1] at hne'; exact hne'
  set M₁ := max (S 0) (2 / ρ₁ * (alg.ψ (alg.z 0) - ψ₀)) with hₘ
  have lbdS: ∀ (n : ℕ) , S n ≤ M₁ := by
    rw [hₘ]; intro n
    by_cases h0 : n = 0
    apply le_max_iff.2; left; rw [h0]
    apply le_max_iff.2; right
    apply Nat.pos_of_ne_zero at h0
    exact hne'' n (by linarith [h0])
  obtain hSum : Summable (fun k ↦ ‖alg.z (k + 1) - alg.z k‖ ^ 2) :=
    summable_of_sum_range_le (fun _ ↦ by positivity) (lbdS)
  simp [Summable] at hSum
  rcases hSum with ⟨a,ha⟩
  obtain hA := HasSum.tendsto_sum_nat ha
  use a

/- the difference squence tends to 0 -/
theorem Sufficient_Descent4 (γ : ℝ) (hγ : γ > 1) (ck: ∀ k, alg.c k = 1 / (γ * l))
    (dk: ∀ k, alg.d k = 1 / (γ * l)) (lbdψ : BddBelow (alg.ψ '' univ)):
    Tendsto (fun k ↦ ‖alg.z (k + 1) - alg.z k‖) atTop (𝓝 0) :=by
  rcases Sufficient_Descent3 γ hγ ck dk lbdψ with ⟨A, hA⟩
  rw [Metric.tendsto_atTop] at hA; simp [dist_eq_norm] at hA
  rw [Metric.tendsto_atTop]; simp [dist_zero_right]
  have SqConver : ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ (n : ℕ), N ≤ n → ‖alg.z (n + 1) - alg.z n‖^2 < ε := by
    intro ε εge0
    specialize hA (ε / 2)
    rcases (hA (by linarith[εge0])) with ⟨N,hNεhalf⟩
    use N; intro n ngeN
    have eq' : ‖alg.z (n + 1) - alg.z n‖ ^ 2 = (∑ k ∈ Finset.range (n + 1), ‖alg.z (k + 1)
        - alg.z k‖ ^ 2 - A) - (∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A) := by
      rw [sub_sub_sub_comm]; simp; rw [Finset.sum_range_succ_sub_sum]
    obtain hNεhalf' := hNεhalf (n + 1) (by linarith [ngeN])
    have hNεhalf1 : ∑ k ∈ Finset.range (n + 1), ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A < ε / 2 := by
      rw [abs_lt] at hNεhalf'; exact hNεhalf'.right
    have hNεhalf2 : ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A > - (ε / 2) := by
      specialize hNεhalf n ngeN
      rw [abs_lt] at hNεhalf; exact hNεhalf.left
    rw [eq']; linarith [hNεhalf1, hNεhalf1]
  intro ε εge0
  set εsq := ε ^ 2 with sqeq
  specialize SqConver εsq (by positivity)
  rw [sqeq] at SqConver
  rcases SqConver with ⟨N,hN⟩
  use N; intro n ngeN
  set a := ‖alg.z (n + 1) - alg.z n‖
  have neq : |a| < |ε| := sq_lt_sq.1 (hN n ngeN)
  rwa [abs_of_pos εge0, abs_of_nonneg (by positivity)] at neq

end descent

section Upperbound_subd

variable {c : ℝ} {f' : E → ℝ} {x u u' : E} {y v : F}

set_option maxHeartbeats 800000 in
theorem Ψ_subdiff_bound (γ : ℝ) (hγ : γ > 1)
    (ck: ∀ k, alg.c k = 1 / (γ * l)) (dk: ∀ k, alg.d k = 1 / (γ * l)) :
    ∃ ρ > 0, ∀ k, ∃ dΨ ∈ f_subdifferential alg.ψ (alg.z (k + 1)),
    ‖dΨ‖ ≤ ρ * ‖alg.z (k + 1) - alg.z k‖ := by
  use l * (2 * γ + 2)
  constructor
  · obtain lpos := alg.lpos; positivity
  intro k; use alg.subdiff k
  constructor
  · apply f_subdiff_add_smooth
    · apply f_subdiff_block
      · have := f_subdiff_smul_prox (alg.s₁ k) (alg.cpos γ hγ ck k)
        rwa [sub_right_comm, smul_sub, inv_smul_smul₀ (ne_of_gt (alg.cpos γ hγ ck k))] at this
      · have := f_subdiff_smul_prox (alg.s₂ k) (alg.dpos γ hγ dk k)
        rwa [sub_right_comm, smul_sub, inv_smul_smul₀ (ne_of_gt (alg.dpos γ hγ dk k))] at this
    exact DifferentiableAt.hasGradientAt (Differentiable.differentiableAt alg.Hdiff)
  apply le_trans (prod_norm_le_block_sum_L2 (alg.subdiff k))
  obtain lip := alg.lip
  rw [lipschitzWith_iff_norm_sub_le] at lip
  have cpos' : (alg.c k)⁻¹ ≥ 0 := by simp; apply le_of_lt (alg.cpos γ hγ ck k)
  have dpos' : (alg.d k)⁻¹ ≥ 0 := by simp; apply le_of_lt (alg.dpos γ hγ dk k)
  have h1 : ‖(alg.subdiff k).fst‖ ≤ l * (γ + 1) * ‖alg.z (k + 1) - alg.z k‖ := by
    let a := (alg.c k)⁻¹ • (alg.x k - alg.x (k + 1))
    calc
      ‖(alg.subdiff k).fst‖
          = ‖a + (gradient H (alg.x (k + 1), alg.y (k + 1))).fst
              - grad_fst H (alg.y k) (alg.x k)‖ := by
            simp [BCD.subdiff, BCD.A_k, BCD.A_kx, BCD.A_ky, a, sub_eq_add_neg, add_left_comm, add_comm]
      _ = ‖a + (gradient H (alg.x (k + 1), alg.y (k + 1))).fst
            - (gradient H (alg.x k, alg.y k)).fst‖ := by
            simp [grad_fst]
      _ ≤ ‖a‖ + ‖(gradient H (alg.x (k + 1), alg.y (k + 1))).fst
            - (gradient H (alg.x k, alg.y k)).fst‖ := by
            simpa [sub_eq_add_neg, add_assoc] using
              (norm_add_le a ((gradient H (alg.x (k + 1), alg.y (k + 1))).fst - (gradient H (alg.x k, alg.y k)).fst))
      _ ≤ ‖a‖ + ‖gradient H (alg.x (k + 1), alg.y (k + 1)) - gradient H (alg.x k, alg.y k)‖ := by
            have hfst :
                ‖(gradient H (alg.x (k + 1), alg.y (k + 1))).fst
                  - (gradient H (alg.x k, alg.y k)).fst‖
                ≤ ‖gradient H (alg.x (k + 1), alg.y (k + 1)) - gradient H (alg.x k, alg.y k)‖ := by
              simpa using (fst_norm_le_prod_L2
                (gradient H (alg.x (k + 1), alg.y (k + 1)) - gradient H (alg.x k, alg.y k)))
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hfst ‖a‖
    have inequ₁ : ‖a‖ ≤ (γ * l) * ‖alg.z (k+1) - alg.z k‖ := by
      calc
        _ = (1 / alg.c k) * ‖alg.x k - alg.x (k + 1)‖ := by
          simp [a]; rw [norm_smul_of_nonneg]; apply cpos'
        _ = (1 / alg.c k) * ‖alg.x (k + 1) - alg.x k‖ := by simp; left; apply norm_sub_rev
        _ = (1 / alg.c k) * ‖(alg.z (k + 1) - alg.z k).fst‖ := by rw [z]; simp; left; rw [z]; simp
        _ ≤ (1 / alg.c k) * ‖alg.z (k + 1) - alg.z k‖ := by
          have : ‖(alg.z (k + 1) - alg.z k).fst‖ ≤ ‖alg.z (k + 1) - alg.z k‖ := fst_norm_le_prod_L2 _
          simp; apply mul_le_mul_of_nonneg_left this cpos'
        _ = (γ * l) * ‖alg.z (k + 1) - alg.z k‖ := by rw [ck k]; simp
    have inequ₂ : ‖gradient H (alg.x (k + 1), alg.y (k + 1)) - gradient H (alg.x k, alg.y k)‖
        ≤ l * ‖alg.z (k+1) - alg.z k‖ := by
      calc
        _ ≤ l * @norm (WithLp 2 (E × F)) (WithLp.instProdNorm 2 E F)
            ((alg.x (k + 1), alg.y (k + 1)) - (alg.x k, alg.y k)) := by
          apply lip
        _ = l * ‖alg.z (k+1) - alg.z k‖ := by repeat rw [z]; simp; left; rfl
    linarith
  have h2 : ‖(alg.subdiff k).snd‖ ≤ l * (γ + 1) * ‖alg.z (k + 1) - alg.z k‖ := by
    let a := (alg.d k)⁻¹ • (alg.y k - alg.y (k + 1))
    calc
      ‖(alg.subdiff k).snd‖
          = ‖a + (gradient H (alg.x (k + 1), alg.y (k + 1))).snd
              - grad_snd H (alg.x (k + 1)) (alg.y k)‖ := by
            simp [BCD.subdiff, BCD.A_k, BCD.A_kx, BCD.A_ky, a, sub_eq_add_neg, add_left_comm, add_comm]
      _ = ‖a + (gradient H (alg.x (k + 1), alg.y (k + 1))).snd
            - (gradient H (alg.x (k + 1), alg.y k)).snd‖ := by
            simp [grad_snd]
      _ ≤ ‖a‖ + ‖(gradient H (alg.x (k + 1), alg.y (k + 1))).snd
            - (gradient H (alg.x (k + 1), alg.y k)).snd‖ := by
            simpa [sub_eq_add_neg, add_assoc] using
              (norm_add_le a ((gradient H (alg.x (k + 1), alg.y (k + 1))).snd - (gradient H (alg.x (k + 1), alg.y k)).snd))
      _ ≤ ‖a‖ + ‖gradient H (alg.x (k + 1), alg.y (k + 1)) - gradient H (alg.x (k + 1), alg.y k)‖ := by
            have hsnd :
                ‖(gradient H (alg.x (k + 1), alg.y (k + 1))).snd
                  - (gradient H (alg.x (k + 1), alg.y k)).snd‖
                ≤ ‖gradient H (alg.x (k + 1), alg.y (k + 1)) - gradient H (alg.x (k + 1), alg.y k)‖ := by
              simpa using (snd_norm_le_prod_L2
                (gradient H (alg.x (k + 1), alg.y (k + 1)) - gradient H (alg.x (k + 1), alg.y k)))
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hsnd ‖a‖
    have inequ₁ : ‖a‖ ≤ (γ * l) * ‖alg.z (k + 1) - alg.z k‖ := by
      calc
        _ = (1 / alg.d k) * ‖alg.y k - alg.y (k + 1)‖ := by
          simp [a]; rw [norm_smul_of_nonneg]; apply dpos'
        _ = (1 / alg.d k) * ‖alg.y (k + 1) - alg.y k‖ := by simp; left; apply norm_sub_rev
        _ = (1 / alg.d k) * ‖(alg.z (k + 1) - alg.z k).snd‖ := by rw [z]; simp; left; rw [z]; simp
        _ ≤ (1 / alg.d k) * ‖alg.z (k + 1) - alg.z k‖ := by
          have : ‖(alg.z (k + 1) - alg.z k).snd‖ ≤ ‖alg.z (k + 1) - alg.z k‖ := by
            apply snd_norm_le_prod_L2
          simp; apply mul_le_mul_of_nonneg_left this dpos'
        _ = (γ * l) * ‖alg.z (k + 1) - alg.z k‖ := by rw [dk k]; simp
    have inequ₂ : ‖gradient H (alg.x (k + 1), alg.y (k + 1)) - gradient H (alg.x (k + 1), alg.y k)‖
                  ≤ l * ‖alg.z (k+1) - alg.z k‖ := by
      calc
        _ ≤ l * @norm (WithLp 2 (E × F)) (WithLp.instProdNorm 2 E F)
            ((alg.x (k + 1), alg.y (k + 1)) - (alg.x (k + 1), alg.y k)) := by
          apply lip
        _ = l * ‖alg.y (k + 1) - alg.y k‖ := by
          simp [WithLp.prod_norm_eq_of_L2]
        _ ≤ l * ‖alg.z (k+1) - alg.z k‖ := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt alg.lpos)
          · simpa [z] using (snd_norm_le_prod_L2 (alg.z (k + 1) - alg.z k))
    linarith
  linarith

end Upperbound_subd

section limit_point

open BCD

variable [ProperSpace E] [ProperSpace F]

private lemma StrictMono_nat (φ : ℕ → ℕ) (hφ : StrictMono φ) : ∀ n, n ≤ (φ n) := fun n ↦ hφ.id_le n

private lemma final (m : ℕ) {α : ℕ → ℕ} (monoa : StrictMono α) : ∃ n : ℕ, m ≤ α n := by
  induction' m with m ih
  · use 1; linarith
  rcases ih with ⟨n, ieqq⟩
  use n + 1
  have : α n + 1 ≤ α (n + 1):= by
    apply Nat.succ_le_iff.mpr
    apply monoa; norm_num
  linarith

lemma fconv (γ : ℝ) (hγ : γ > 1) (ck : ∀ k, alg.c k = 1 / (γ * l)) (dk : ∀ k, alg.d k = 1 / (γ * l))
    (α : ℕ → ℕ) (z_ : WithLp 2 (E×F)) (monoa : StrictMono α)
    (conv : Tendsto (fun n ↦ alg.z (α n)) atTop (𝓝 z_))
    (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)) :
    Tendsto (fun n ↦ f (alg.z (α n)).fst) atTop (𝓝 (f z_.fst)) := by
  obtain lpos := alg.lpos
  apply (nhds_basis_Ioo_pos (f z_.fst)).tendsto_right_iff.mpr
  rintro ε epos
  simp only [Ioo]
  have lef : ∀ᶠ x in atTop, f (alg.z (α x)).fst > f z_.fst - ε :=
    ((WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := F)).tendsto z_ |>.comp conv)
      (by apply alg.hf z_.fst; exact sub_lt_self (f z_.fst) epos)
  have rig : ∀ᶠ x in atTop, f (alg.z (α x)).fst < f z_.fst + ε := by
    have ieq (q) (hq : 1 ≤ α q) : alg.c (α q -1) * f (alg.x (α q)) + ⟪alg.x (α q) - alg.x (α q -1),
        alg.c (α q -1) • grad_fst H (alg.y (α q -1)) (alg.x (α q -1))⟫ ≤
        alg.c (α q -1) * f z_.fst + ‖z_.fst - alg.x (α q -1)‖ ^ 2 / 2 + ⟪z_.fst - alg.x (α q -1),
        alg.c (α q -1) • grad_fst H (alg.y (α q -1)) (alg.x (α q -1))⟫:= by
      rcases isMinOn_iff.mp (alg.s₁ (α q -1)) z_.fst trivial with ieq
      simp at ieq
      rw [← sub_add, norm_add_sq_real, ← sub_add, norm_add_sq_real] at ieq
      repeat rw [add_div] at ieq; repeat rw [← add_assoc] at ieq
      simp [hq] at ieq
      have : 0 ≤ ‖alg.x (α q) - alg.x (α q - 1)‖ ^ 2 / 2 := by positivity
      linarith [ieq,this]
    have Hbd : ∃ C, ∀ q : ℕ, ‖(grad_fst H (alg.y (α q -1)) (alg.x (α q -1)))‖ ≤ C:= by
      rcases isBounded_iff_forall_norm_le.mp bd with ⟨C1,inin⟩
      have con11H : ContinuousOn (fun z : WithLp 2 (E × F) ↦ grad_fst H z.snd z.fst)
          (Metric.closedBall (0:WithLp 2 (E×F)) C1) := by
        apply Continuous.continuousOn
        exact LipschitzWith.continuous (lip_grad_fst_of_lip alg.Hdiff alg.lip)
      rcases @IsCompact.exists_bound_of_continuousOn (WithLp 2 (E×F)) E _ _ _
        (isCompact_closedBall (0 : WithLp 2 (E × F)) C1)
        (fun z : WithLp 2 (E × F) ↦ grad_fst H z.snd z.fst) con11H with ⟨C, sq⟩
      use C; rintro q
      have : ((alg.x (α q -1),alg.y (α q -1)) : WithLp 2 (E × F))
          ∈ Metric.closedBall (0 : WithLp 2 (E × F)) C1 := by
        apply mem_closedBall_iff_norm.mpr; simp
        apply inin ((alg.x (α q -1),alg.y (α q -1)) : WithLp 2 (E × F))
        exact mem_image_of_mem alg.z trivial
      obtain h'' := sq ((alg.x (α q -1),alg.y (α q -1)) : WithLp 2 (E × F)) this
      simp at h''; exact h''
    rcases Hbd with ⟨C,hbd⟩
    have diflte1 : ∀ ε > 0, ∀ᶠ (q : ℕ) in atTop, ‖alg.x (α q) - alg.x (α q - 1)‖ < ε:= by
      intro ε epos
      rcases (nhds_basis_abs_sub_lt (0 : ℝ)).tendsto_right_iff.mp
        (Sufficient_Descent4 γ hγ ck dk lbdψ) ε epos with lte
      simp at lte; rcases lte with ⟨a, ie⟩
      simp; rcases final (a + 1) monoa with ⟨A, iee⟩
      use A
      rintro b Aleb
      have a1leab : a + 1 ≤ α b := by linarith [StrictMono.monotone monoa Aleb, iee]
      calc
        _ ≤ @norm (WithLp 2 (E × F)) (WithLp.instProdNorm 2 E F)
              (alg.x (α b) - alg.x (α b - 1),alg.y (α b) - alg.y (α b - 1)) := by
          rw [WithLp.prod_norm_eq_of_L2]; simp
          exact (Real.le_sqrt (norm_nonneg _) (Left.add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
            (le_add_of_nonneg_right (sq_nonneg _))
        _ < ε := by
          obtain ht := ie (α b - 1) (Nat.le_sub_one_of_lt a1leab)
          have eqq : (α b - 1 + 1) = α b:= by apply Nat.sub_add_cancel; linarith [a1leab]
          rwa [eqq] at ht
    have diflte2 : ∀ ε > 0, ∀ᶠ (q : ℕ) in atTop, ‖z_.fst - alg.x (α q - 1)‖ < ε := by
      rintro ε epos
      have : ∀ᶠ (q : ℕ) in atTop, ‖z_.fst - alg.x (α q )‖ < ε / 2 := by
        rcases (atTop_basis.tendsto_iff (@Metric.nhds_basis_ball _ _ z_)).mp conv (ε / 2)
          (half_pos epos) with ⟨n1,_,ieq1⟩
        simp [dist_eq_norm] at ieq1; simp
        use n1; rintro b n1leb
        calc
          _ ≤ ‖z_ - alg.z (α b)‖ :=by
            rw [WithLp.prod_norm_eq_of_L2]; simp
            exact (Real.le_sqrt (norm_nonneg _) (Left.add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
              (le_add_of_nonneg_right (sq_nonneg _))
          _< ε / 2 := by rw [norm_sub_rev]; exact ieq1 b n1leb
      apply Eventually.mono (Eventually.and this (diflte1 (ε/2) (half_pos epos)))
      rintro x ⟨h1,h2⟩
      rw [← sub_add_sub_cancel]
      calc
        _ ≤ ‖z_.fst - alg.x (α x)‖ + ‖alg.x (α x) - alg.x (α x - 1)‖ := norm_add_le _ _
        _ < ε := by linarith

    have hk (k : ℕ → E) (defle : ∀ ε > 0, ∀ᶠ (q : ℕ) in atTop, ‖k q‖ < ε) : ∀ ε > 0,
        ∀ᶠ (q : ℕ) in atTop,abs ⟪k q, alg.c (α q -1) •
        grad_fst H (alg.y (α q -1)) (alg.x (α q -1))⟫ ≤ ε:= by
      rintro ε epos
      simp at defle; simp
      by_cases Cpos : 0 < C
      · have hdivpos : 0 < ε / (C / (γ * l)) := by
          apply div_pos epos
          apply div_pos Cpos
          nlinarith [hγ, alg.lpos]
        rcases defle (ε / (C / (γ * l))) hdivpos with ⟨nn,ieq⟩
        use nn; rintro b nleb; rw [ck]
        calc
          _ ≤ ‖k b‖ * ‖(1 / (γ * ↑l)) • grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖
              := by apply abs_real_inner_le_norm
          _ ≤ ε / (C / (γ * ↑l))*‖(1 / (γ * ↑l)) • grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖:= by
            apply mul_le_mul (le_of_lt (ieq b nleb)) le_rfl
            repeat apply norm_nonneg
            exact le_of_lt hdivpos
          _ = ε / (C / (γ * ↑l))*(1 / (γ * ↑l)) * ‖grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖:= by
            rw [mul_assoc]; apply mul_eq_mul_left_iff.mpr
            left; exact norm_smul_of_nonneg (by positivity) (grad_fst H _ _)
          _ = ε / C * ‖grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖ := by
            apply mul_eq_mul_right_iff.mpr;left
            rw [← div_mul, mul_assoc, mul_one_div, div_self, mul_one]
            have :0 < γ * ↑l := by apply mul_pos _ alg.lpos;linarith
            linarith
          _ ≤ ε / C * C := by
            apply mul_le_mul;trivial;apply hbd b;apply norm_nonneg
            apply le_of_lt ;apply div_pos epos Cpos
          _ = ε:= div_mul_cancel₀ ε (by linarith [Cpos])
      push_neg at Cpos
      use 0; rintro b _
      rw [ck]
      calc
        _ ≤ ‖k b‖ * ‖(1 / (γ * ↑l)) • grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖ := by
          apply abs_real_inner_le_norm
        _ = ‖k b‖ * (1 / (γ * ↑l)) * ‖grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖ := by
            rw [mul_assoc]; apply mul_eq_mul_left_iff.mpr; left
            exact norm_smul_of_nonneg (by positivity) (grad_fst H _ _)
        _ ≤ ‖k b‖ * (1 / (γ * ↑l)) * C:= by
          apply mul_le_mul
          trivial; apply hbd b; apply norm_nonneg; apply mul_nonneg; apply norm_nonneg
          apply div_nonneg; norm_num; apply mul_nonneg; linarith; linarith [alg.lpos]
        _ ≤ 0:= by
          apply mul_nonpos_iff.mpr
          left; refine ⟨?_,Cpos⟩
          apply mul_nonneg; apply norm_nonneg
          apply div_nonneg; norm_num; apply mul_nonneg; linarith; linarith [alg.lpos]
        _≤ε:= by linarith
    simp only [ck] at ieq
    have h1 := hk (fun q ↦ alg.x (α q) - alg.x (α q - 1)) diflte1 (ε / (γ * l) / 3) (by positivity)
    have h2 := hk (fun q ↦ z_.fst - alg.x (α q - 1)) diflte2 (ε / (γ * l) / 3) (by positivity)
    have h3 : ∀ᶠ (q : ℕ) in atTop, ‖z_.fst - alg.x (α q - 1)‖ ^ 2 / 2 < (ε / (γ * l) / 3):= by
      refine Eventually.mono (diflte2 (√(2*(ε/(γ*l)/3))) ?_) ?_
      apply Real.sqrt_pos_of_pos
      apply mul_pos;norm_num; positivity
      intro x assx
      have :‖z_.fst - alg.x (α x - 1)‖^2<(2*(ε/(γ*l)/3)):= by
        refine (Real.lt_sqrt ?hx).mp ?_
        apply norm_nonneg
        exact assx
      calc
        ‖z_.fst - alg.x (α x - 1)‖ ^ 2 / 2<(2*(ε/(γ*l)/3))/2:= by
          nlinarith [this]
        _=(ε/(γ*l)/3):= by
          apply mul_div_cancel_left₀
          linarith
    simp at h1 h2 h3; simp only [ck] at h1 h2 h3; simp
    rcases h1 with ⟨m1,ie1⟩
    rcases h2 with ⟨m2,ie2⟩
    rcases h3 with ⟨m3,ie3⟩
    use 1 + max (max m1 m2) m3
    intro q mleq
    have m1le : m1 ≤ 1 + max (max m1 m2) m3:= by
      linarith [(le_max_left m1 m2).trans (le_max_left _ m3)]
    have m2le : m2 ≤ 1+max (max m1 m2) m3:= by
      linarith [(le_max_right m1 m2).trans (le_max_left _ m3)]
    have m3le : m3≤1+max (max m1 m2) m3:= by
      linarith [le_max_right (max m1 m2) m3]
    have : 1 ≤ α q := by
      have : α 0 < α q:= by
        apply monoa
        linarith [Nat.le_of_add_right_le mleq]
      linarith
    have key : 1 / (γ * ↑l) * f (alg.x (α q)) <1 / (γ * ↑l) * f z_.fst +ε / (γ * ↑l):= by
      linarith [ieq q this,(abs_le.mp (ie1 q (m1le.trans mleq))).1,(abs_le.mp
        (ie2 q (m2le.trans mleq))).2,ie3 q (m3le.trans mleq), add_thirds (ε / (γ * ↑l))]
    have ltt:0<γ*l:= by
      apply mul_pos;linarith;linarith [alg.lpos]
    calc
      _ = f (alg.x (α q)) := rfl
      _ =(γ * ↑l)*(1 / (γ * ↑l) * f (alg.x (α q))):= by
        rw [←mul_assoc,mul_one_div_cancel (LT.lt.ne ltt).symm,one_mul]
      _ < (γ * ↑l)*(1 / (γ * ↑l) * f z_.fst + ε / (γ * ↑l)) := by
        exact mul_lt_mul_of_pos_left key ltt
      _=f z_.fst + ε:=by
        rw [mul_add, ← mul_assoc, mul_one_div_cancel (LT.lt.ne ltt).symm, one_mul,
          mul_div_cancel₀ _ (LT.lt.ne ltt).symm]
  exact Eventually.and lef rig


lemma gconv (γ : ℝ) (hγ : γ > 1) (ck: ∀ k, alg.c k = 1 / (γ * l)) (dk: ∀ k, alg.d k = 1 / (γ * l))
    (α:ℕ→ℕ)(z_:WithLp 2 (E×F))(monoa:StrictMono α )(conv:Tendsto (fun n ↦ alg.z (α n)) atTop (𝓝 z_))
    (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
    Tendsto (fun n ↦ g (alg.z (α n)).snd) atTop (𝓝 (g z_.snd)):=by
  apply (nhds_basis_Ioo_pos (g z_.snd)).tendsto_right_iff.mpr
  rintro ε epos
  simp only [Ioo]
  have lef:∀ᶠ (x : ℕ) in atTop, g (alg.z (α x)).snd>g z_.snd-ε:= by
    have semi: ∀ᶠ x' in 𝓝 z_.snd, g z_.snd -ε < g x':= by
      apply alg.hg z_.snd
      linarith
    have : Tendsto (fun n ↦ (alg.z (α n)).snd) atTop (𝓝 z_.snd) :=
      ((WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := F)).tendsto z_).comp conv
    exact this semi
  have rig:∀ᶠ (x : ℕ) in atTop, g (alg.z (α x)).snd<g z_.snd+ε:= by
    have ieq (q:ℕ)(hq:1≤α q):alg.d (α q - 1) * g (alg.y (α q)) +
        ⟪alg.y (α q) - alg.y (α q - 1), alg.d (α q - 1) • grad_snd H (alg.x (α q)) (alg.y (α q - 1))⟫≤
        alg.d (α q - 1) * g z_.snd + ‖z_.snd - alg.y (α q - 1)‖ ^ 2 / 2 +
        ⟪z_.snd - alg.y (α q - 1), alg.d (α q - 1) • grad_snd H (alg.x (α q)) (alg.y (α q - 1))⟫:= by
      rcases isMinOn_iff.mp (alg.s₂ (α q -1)) z_.snd trivial with ieq
      simp at ieq
      rw [←sub_add,norm_add_sq_real,←sub_add,norm_add_sq_real] at ieq
      repeat rw [add_div] at ieq
      repeat rw [←add_assoc] at ieq
      simp [hq] at ieq
      have :0≤‖alg.y (α q) - alg.y (α q - 1)‖ ^ 2 / 2 := by
        apply div_nonneg
        norm_num
        norm_num
      linarith [ieq,this]
    have Hbd :∃C,∀q:ℕ ,‖(grad_snd H (alg.x (α q )) (alg.y (α q -1)))‖≤C:= by
      rcases isBounded_iff_forall_norm_le.mp bd with ⟨C1,inin⟩
      have con11H : ContinuousOn (fun z : WithLp 2 (E × F) ↦ grad_snd H z.fst z.snd)
          (Metric.closedBall (0:WithLp 2 (E×F)) (2*C1)) := by
        apply Continuous.continuousOn
        exact LipschitzWith.continuous (lip_grad_snd_of_lip alg.Hdiff alg.lip)
      rcases @IsCompact.exists_bound_of_continuousOn (WithLp 2 (E×F)) F _ _ _
          (isCompact_closedBall (0:WithLp 2 (E×F)) (2*C1))
          (fun z : WithLp 2 (E × F) ↦ grad_snd H z.fst z.snd) con11H with ⟨C,sqsq⟩
      use C
      rintro q
      have : ((alg.x (α q),alg.y (α q -1)) : WithLp 2 (E × F))
          ∈ Metric.closedBall (0:WithLp 2 (E×F)) (2*C1) := by
        apply mem_closedBall_iff_norm.mpr
        simp
        calc
          @norm (WithLp 2 (E × F)) (WithLp.instProdNorm 2 E F)
              ((alg.x (α q),alg.y (α q - 1)) : WithLp 2 (E × F)) ≤
              ‖alg.x (α q)‖+‖alg.y (α q - 1)‖ := by apply prod_norm_le_block_sum_L2
          _≤‖alg.z (α q)‖+‖alg.z (α q -1)‖:=by
            have :‖alg.y (α q -1)‖≤‖alg.z (α q -1)‖:= by
              rw [WithLp.prod_norm_eq_of_L2]
              apply (Real.le_sqrt (norm_nonneg (alg.y (α q -1) ))
              (Left.add_nonneg (sq_nonneg ‖alg.x (α q - 1)‖)
              (sq_nonneg ‖(alg.y (α q -1) )‖ ))).mpr
              apply (le_add_of_nonneg_left (sq_nonneg ‖alg.x (α q - 1)‖))
            have :‖alg.x (α q )‖≤‖alg.z (α q )‖:= by
              rw [WithLp.prod_norm_eq_of_L2]
              apply (Real.le_sqrt (norm_nonneg (alg.x (α q ) ))
              (Left.add_nonneg (sq_nonneg ‖alg.x (α q )‖)
              (sq_nonneg ‖(alg.y (α q ) )‖ ))).mpr
              apply (le_add_of_nonneg_right (sq_nonneg ‖alg.y (α q )‖))
            linarith
          _≤C1+C1:=by
            apply add_le_add
            apply inin ((alg.x (α q), alg.y (α q)) : WithLp 2 (E × F))
            exact mem_image_of_mem alg.z trivial
            apply inin ((alg.x (α q - 1), alg.y (α q - 1)) : WithLp 2 (E × F))
            exact mem_image_of_mem alg.z trivial
          _=2*C1:=Eq.symm (two_mul C1)
      have hhhh := sqsq ((alg.x (α q), alg.y (α q - 1)) : WithLp 2 (E × F)) this
      simp at hhhh
      exact hhhh
    rcases Hbd with ⟨C,hbd⟩
    have diflte1:∀ ε>0, ∀ᶠ (q : ℕ) in atTop,‖alg.y (α q) - alg.y (α q - 1)‖ <ε:= by
      intro ε epos
      rcases (nhds_basis_abs_sub_lt (0:ℝ)).tendsto_right_iff.mp
        (Sufficient_Descent4 γ hγ ck dk lbdψ) ε epos with lte
      simp at lte
      rcases lte with ⟨a,ie⟩
      simp
      rcases final (a+1) monoa with ⟨A,iee⟩
      use A
      rintro b Aleb
      have:Monotone α:= by exact StrictMono.monotone monoa
      have a1leab:a+1≤ α b := by linarith [StrictMono.monotone monoa Aleb,iee]
      have :a≤ α b -1:= by exact Nat.le_sub_one_of_lt a1leab
      calc
        ‖alg.y (α b) - alg.y (α b - 1)‖≤@norm (WithLp 2 (E × F)) (WithLp.instProdNorm 2 E F)
            (alg.x (α b) - alg.x (α b - 1),alg.y (α b) - alg.y (α b - 1)) :=by
          rw [WithLp.prod_norm_eq_of_L2]
          simp
          refine (Real.le_sqrt (norm_nonneg (alg.y (α b) - alg.y (α b - 1)))
            (Left.add_nonneg (sq_nonneg ‖alg.x (α b) - alg.x (α b - 1)‖)
            (sq_nonneg ‖alg.y (α b) - alg.y (α b - 1)‖ ))).mpr
            (le_add_of_nonneg_left (sq_nonneg ‖alg.x (α b) - alg.x (α b - 1)‖))
        _=‖alg.z (α b) - alg.z (α b - 1)‖:= rfl
        _<ε:= by
          have: ‖alg.z (α b - 1 + 1) - alg.z (α b - 1)‖ < ε:=ie (α b - 1) this
          have eqq:(α b - 1 + 1)=α b:= by
            apply Nat.sub_add_cancel
            linarith [a1leab]
          rw [eqq] at this
          assumption
    have diflte2:∀ ε>0, ∀ᶠ (q : ℕ) in atTop,‖z_.snd - alg.y (α q - 1)‖ <ε:= by
      rintro ε epos
      have : ∀ᶠ (q : ℕ) in atTop,‖z_.snd - alg.y (α q )‖ <ε/2:= by
        rcases (atTop_basis.tendsto_iff (@Metric.nhds_basis_ball _ _ z_)).mp conv (ε/2)
          (half_pos epos) with ⟨n1,_,ieq1⟩
        simp [dist_eq_norm] at ieq1;simp
        use n1
        rintro b n1leb
        calc
          ‖z_.snd - alg.y (α b)‖≤‖z_ - alg.z (α b)‖ :=by
            rw [WithLp.prod_norm_eq_of_L2]
            simp
            refine (Real.le_sqrt (norm_nonneg (z_.snd - alg.y (α b)))
              (Left.add_nonneg (sq_nonneg ‖z_.fst - alg.x (α b)‖)
              (sq_nonneg ‖z_.snd - alg.y (α b)‖ ))).mpr
              (le_add_of_nonneg_left (sq_nonneg ‖z_.fst - alg.x (α b)‖))
          _<ε/2:=by
            rw [norm_sub_rev]
            exact ieq1 b n1leb
      have :∀ᶠ (q : ℕ) in atTop,‖z_.snd - alg.y (α q )‖ <ε/2∧‖alg.y (α q) - alg.y (α q - 1)‖ <ε/2
          := Eventually.and this (diflte1 (ε/2) (half_pos epos))
      apply Eventually.mono this
      rintro x ⟨h1,h2⟩
      calc
        ‖z_.snd - alg.y (α x - 1)‖=‖z_.snd - alg.y (α x )+(alg.y (α x) - alg.y (α x -1))‖:= by
          simp
        _≤‖z_.snd - alg.y (α x)‖+‖alg.y (α x) - alg.y (α x - 1)‖:= by
          apply norm_add_le
        _<ε/2+ε/2:= by linarith [h1,h2]
        _=ε := by exact add_halves ε

    have (k:ℕ→F)(defle:∀ ε > 0, ∀ᶠ (q : ℕ) in atTop, ‖k q‖ < ε):∀ ε>0, ∀ᶠ (q : ℕ) in atTop,abs
        ⟪k q, alg.d (α q -1) • grad_snd H (alg.x (α q )) (alg.y (α q -1))⟫≤ε:= by
      rintro ε epos
      simp at defle;simp
      by_cases Cpos:0<C
      · have :0<ε/(C/(γ*l)) := by
          apply div_pos epos;apply div_pos Cpos;apply mul_pos _ alg.lpos;linarith
        rcases defle (ε/(C/(γ*l))) this with ⟨nn,ieq⟩
        use nn
        rintro b nleb
        rw [dk]
        calc
          |⟪k b, (1 / (γ * ↑l)) • grad_snd H (alg.x (α b )) (alg.y (α b - 1))⟫|
            ≤‖k b‖*‖(1 / (γ * ↑l)) • grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖
              := by apply abs_real_inner_le_norm
          _≤ε / (C / (γ * ↑l))*‖(1 / (γ * ↑l)) • grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖:= by
            apply mul_le_mul (le_of_lt (ieq b nleb))
            trivial
            repeat apply norm_nonneg
            apply le_of_lt;apply div_pos;apply epos;apply div_pos Cpos;apply mul_pos _ alg.lpos
            linarith [hγ]
          _=ε / (C / (γ * ↑l))*(1 / (γ * ↑l)) *‖ grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖:= by
            rw [mul_assoc]
            apply mul_eq_mul_left_iff.mpr
            left
            refine
              norm_smul_of_nonneg ?h.ht (grad_snd H (alg.x (α b )) (alg.y (α b - 1)))
            apply div_nonneg
            norm_num;apply mul_nonneg
            linarith [hγ];linarith [alg.lpos]
          _=ε/C*‖ grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖:= by
            apply mul_eq_mul_right_iff.mpr;left
            rw [←div_mul,mul_assoc,mul_one_div,div_self,mul_one]
            have :0<γ * ↑l:=by apply mul_pos _ alg.lpos;linarith
            linarith
          _≤ε/C*C:= by
            apply mul_le_mul;trivial;apply hbd b;apply norm_nonneg
            apply le_of_lt ;apply div_pos epos Cpos
          _=ε:= by
            refine div_mul_cancel₀ ε ?h;linarith [Cpos]
      · push_neg at Cpos
        use 100000
        rintro b _
        rw [dk]
        calc
          |⟪k b,  (1 / (γ * ↑l))• grad_snd H (alg.x (α b )) (alg.y (α b - 1))⟫|
            ≤‖k b‖*‖(1 / (γ * ↑l)) • grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖
              := by apply abs_real_inner_le_norm
          _=‖k b‖*(1 / (γ * ↑l)) *‖grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖
              :=by
              rw [mul_assoc]
              apply mul_eq_mul_left_iff.mpr
              left
              refine
              norm_smul_of_nonneg ?h.ht (grad_snd H (alg.x (α b )) (alg.y (α b - 1)))
          _≤‖k b‖*(1 / (γ * ↑l))*C:= by
            apply mul_le_mul
            trivial;apply hbd b;apply norm_nonneg;apply mul_nonneg;apply norm_nonneg
            apply div_nonneg;norm_num;apply mul_nonneg;linarith;linarith [alg.lpos]
          _≤0:= by
            apply mul_nonpos_iff.mpr
            left
            refine ⟨?_,Cpos⟩
            apply mul_nonneg;apply norm_nonneg
            apply div_nonneg;norm_num;apply mul_nonneg;linarith;linarith [alg.lpos]
          _≤ε:= by linarith
    simp only [dk] at ieq
    have finalpos:0<ε/(γ*l)/3:= by
      apply div_pos;apply div_pos epos;apply mul_pos;linarith;apply alg.lpos;linarith
    have h1:∀ᶠ (q : ℕ) in atTop,|⟪alg.y (α q) - alg.y (α q - 1), alg.d (α q - 1) • grad_snd H
        (alg.x (α q )) (alg.y (α q - 1))⟫| ≤ε / (γ * ↑l) / 3 :=
      this (fun q↦alg.y (α q) - alg.y (α q - 1)) (diflte1) (ε/(γ*l)/3) finalpos
    have h2: ∀ᶠ (q : ℕ) in atTop,|⟪z_.snd - alg.y (α q - 1), alg.d (α q - 1) • grad_snd H (alg.x (α q ))
        (alg.y (α q - 1))⟫| ≤ ε / (γ * ↑l) / 3:=
      this (fun q↦z_.snd - alg.y (α q - 1)) diflte2 (ε/(γ*l)/3) finalpos
    have h3: ∀ᶠ (q : ℕ) in atTop,‖z_.snd - alg.y (α q - 1)‖ ^ 2 / 2<(ε/(γ*l)/3):= by
      refine Eventually.mono (diflte2 (√(2*(ε/(γ*l)/3))) ?_) ?_
      apply Real.sqrt_pos_of_pos
      apply mul_pos;norm_num;apply finalpos
      intro x assx
      have :‖z_.snd - alg.y (α x - 1)‖^2<(2*(ε/(γ*l)/3)):= by
        refine (Real.lt_sqrt ?hy).mp ?_
        apply norm_nonneg
        exact assx
      calc
        ‖z_.snd - alg.y (α x - 1)‖ ^ 2 / 2<(2*(ε/(γ*l)/3))/2:= by
          nlinarith [this]
        _=(ε/(γ*l)/3):= by
          apply mul_div_cancel_left₀
          linarith
    simp at h1 h2 h3
    simp only [dk] at h1 h2 h3
    simp
    rcases h1 with ⟨m1,ie1⟩
    rcases h2 with ⟨m2,ie2⟩
    rcases h3 with ⟨m3,ie3⟩
    use 1+max (max m1 m2) m3
    intro q mleq
    have m1le:m1≤1+max (max m1 m2) m3:=by linarith [(le_max_left m1 m2).trans (le_max_left (max m1 m2) m3)]
    have m2le:m2≤1+max (max m1 m2) m3:= by linarith [(le_max_right m1 m2).trans (le_max_left (max m1 m2) m3)]
    have m3le:m3≤1+max (max m1 m2) m3:= by linarith [le_max_right (max m1 m2) m3]
    have :1≤α q := by
      have :α 0 < α q:= by
        apply monoa
        linarith [Nat.le_of_add_right_le mleq]
      linarith
    have key:1 / (γ * ↑l) * g (alg.y (α q)) <1 / (γ * ↑l) * g z_.snd +ε / (γ * ↑l):= by
      linarith [ieq q this,(abs_le.mp (ie1 q (m1le.trans mleq))).1,(abs_le.mp (ie2 q (m2le.trans mleq))).2,
        ie3 q (m3le.trans mleq),add_thirds (ε / (γ * ↑l))]
    have ltt:0<γ*l:= by
      apply mul_pos;linarith;linarith [alg.lpos]
    calc
      g (alg.z (α q)).snd = g (alg.y (α q)):= rfl
      _=(γ * ↑l)*(1 / (γ * ↑l) * g (alg.y (α q))):= by
        rw [←mul_assoc,mul_one_div_cancel (LT.lt.ne ltt).symm,one_mul]
      _ < (γ * ↑l) * (1 / (γ * ↑l) * g z_.snd + ε / (γ * ↑l)) := by
        exact mul_lt_mul_of_pos_left key ltt
      _=g z_.snd + ε:=by
        rw [mul_add, ← mul_assoc, mul_one_div_cancel (LT.lt.ne ltt).symm,
          one_mul, mul_div_cancel₀ _ (LT.lt.ne ltt).symm]
  exact Eventually.and lef rig

--the convergence of subseq implies the convergence of alg.ψ
theorem psiconv (γ : ℝ) (hγ : γ > 1) (ck: ∀ k, alg.c k = 1 / (γ * l)) (dk: ∀ k, alg.d k = 1 / (γ * l))
    (α:ℕ→ℕ)(z_:WithLp 2 (E×F))(monoa:StrictMono α )(conv:Tendsto (fun n ↦ alg.z (α n)) atTop (𝓝 z_))
    (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
  Tendsto (fun n ↦ alg.ψ (alg.z (α n))) atTop (𝓝 (alg.ψ z_)):=by
      apply Tendsto.add
      · apply Tendsto.add
        · apply fconv γ hγ ck dk α z_ monoa conv bd lbdψ
        · apply gconv γ hγ ck dk α z_ monoa conv bd lbdψ
      exact (continuous_iff_seqContinuous.mp (ContDiff.continuous alg.conf)) conv

lemma limitset_property_1 (γ : ℝ) (hγ : γ > 1)
    (ck: ∀ k, alg.c k = 1 / (γ * l)) (dk: ∀ k, alg.d k = 1 / (γ * l))
    (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
    (limit_set alg.z).Nonempty ∧ ((limit_set alg.z) ⊆ critial_point alg.ψ) := by
  constructor
  --nonempty
  have hz : ∀ (n : ℕ), alg.z n ∈ alg.z '' univ:= by intro n; use n; constructor; exact Set.mem_univ n; rfl
  rcases (tendsto_subseq_of_bounded (bd) (hz)) with ⟨a, _ , φ, ⟨hmφ,haφ⟩⟩
  use a
  simp [limit_set, MapClusterPt]
  apply ClusterPt.mono (ClusterPt.of_le_nhds haφ)
  calc
    _ = map (fun n ↦ alg.z n) (map φ atTop) := by rw [map_map]
    _ ≤ map (fun n ↦ alg.z n) atTop := map_mono (StrictMono.tendsto_atTop hmφ)
  --the folllowing shows that limit_set BCD.z ⊆ critial_point BCD.ψ
  intro z_ ha
  rcases TopologicalSpace.FirstCountableTopology.tendsto_subseq ha with ⟨φ,monoφ,conv⟩
  apply Set.mem_setOf.mpr; rw [subdifferential,Set.mem_setOf]
  use fun n ↦ alg.z (φ (n+1))
  constructor; exact (tendsto_add_atTop_iff_nat 1).mpr conv
  constructor; exact (tendsto_add_atTop_iff_nat 1).mpr (psiconv γ hγ ck dk φ z_ monoφ conv bd lbdψ)
  rcases Ψ_subdiff_bound γ hγ ck dk with ⟨ρ,ρpos,ieq⟩
  let v := fun q ↦ Classical.choose (ieq (φ (q + 1) -1))
  use v; intro n
  have key (q:ℕ) : v q ∈ f_subdifferential alg.ψ (alg.x (φ (q+1) -1 + 1), alg.y (φ (q+1) -1 + 1))
    ∧ ‖v q‖ ≤ ρ * ‖alg.z (φ (q+1) -1 + 1) - alg.z (φ (q+1) - 1)‖:=by
    simp [v]; apply Classical.choose_spec (ieq (φ (q+1) -1))
  have subadd (q : ℕ) : φ (q + 1) - 1 + 1 = φ (q + 1) := Nat.sub_add_cancel
    ((Nat.le_add_left 1 q).trans (StrictMono_nat φ monoφ (q + 1)))
  simp [subadd] at key
  constructor; exact (key n).1
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply (nhds_basis_Ioo_pos 0).tendsto_right_iff.mpr
  rintro ε epos; simp
  rcases (nhds_basis_abs_sub_lt (0:ℝ)).tendsto_right_iff.mp (Sufficient_Descent4 γ hγ ck dk lbdψ)
    (ε/ρ) (div_pos epos ρpos) with lte
  simp at lte; rcases lte with ⟨a, ieq⟩
  use a; rintro b aleb; constructor; linarith [norm_nonneg (v b),epos]
  calc
    _ ≤ ρ * ‖alg.z (φ (b + 1)) - alg.z (φ (b + 1) - 1)‖:= (key b).2
    _ < ρ * (ε / ρ) := by
      have : ‖alg.z (φ (b + 1)-1 + 1) - alg.z (φ (b + 1) - 1)‖ < ε / ρ := by
        apply ieq; apply aleb.trans
        exact Nat.sub_le_sub_right (StrictMono_nat φ monoφ (b+1)) 1
      simp [subadd b] at this
      exact mul_lt_mul_of_pos_left this ρpos
    _ = ε := by rw [mul_comm, div_mul_cancel₀]; linarith [ρpos]

lemma limitset_property_2 (bd : Bornology.IsBounded (alg.z '' univ)) :
    Tendsto (fun n ↦ (Metric.infEDist (alg.z n) (limit_set alg.z)).toReal) atTop (𝓝 0) := by
  apply (nhds_basis_Ioo_pos 0).tendsto_right_iff.mpr
  rintro ε epos; by_contra h; simp at h
  --alg.z∘W is the subseq s.t. the dist is no less than ε
  let W : ℕ → ℕ := fun n ↦ Nat.recOn n (Classical.choose (h 0))
    fun n p ↦ (Classical.choose (h (p+1)))
  obtain monoW : StrictMono W :=
    strictMono_nat_of_lt_succ (fun n ↦ (fun n ↦ (Classical.choose_spec (h (W n +1))).1 ) n)
  have : ∃ z_∈ closure (alg.z ∘ W '' univ), ∃ α : ℕ → ℕ,StrictMono α ∧ Tendsto
      (fun n ↦ (alg.z ∘ W) (α n)) atTop (𝓝 z_) := by
    obtain hcs : IsSeqCompact (closure (alg.z∘W '' univ)) :=
      IsCompact.isSeqCompact (bd.subset (fun k ↦ by simp; exact fun x zk ↦ ⟨W x,zk⟩)).isCompact_closure
    have even n : (alg.z ∘ W) n ∈ closure (alg.z ∘ W '' univ) :=
        subset_closure (mem_image_of_mem (alg.z ∘ W) trivial)
    apply hcs.subseq_of_frequently_in (Filter.Frequently.of_forall even)
  rcases this with ⟨z_, _, α, ⟨monoa, conv⟩⟩
  have z_in : z_ ∈ limit_set alg.z:= by
    simp [limit_set, MapClusterPt]
    apply ClusterPt.mono (ClusterPt.of_le_nhds conv)
    calc
      _ = map (fun n ↦ (alg.z ∘ W) n) (map α atTop) := by rw [map_map]; rfl
      _ ≤ map (fun n ↦ (alg.z ∘ W) n) atTop := map_mono (StrictMono.tendsto_atTop monoa)
      _ ≤ map (fun n ↦ alg.z n) atTop := by
        rw [← map_map]; apply map_mono (StrictMono.tendsto_atTop monoW)
  -- show the contradiction
  have z_ge : (Metric.infEDist z_ (limit_set alg.z)).toReal ≥ ε := by
    apply ge_of_tendsto (continuous_iff_seqContinuous.mp
      (Metric.continuous_infDist_pt (limit_set alg.z)) conv)
    simp; use 1; rintro n len
    rw [← tsub_add_cancel_iff_le.mpr (Nat.one_le_of_lt (monoa len))]
    apply (Classical.choose_spec (h (W (α n -1) +1))).2
    apply lt_of_le_of_lt' (ENNReal.toReal_nonneg) (neg_neg_iff_pos.mpr epos)
  linarith [(ENNReal.toReal_eq_zero_iff _).mpr (by left; exact Metric.infEDist_zero_of_mem z_in)]

lemma limitset_property_3 (γ : ℝ) (hγ : γ > 1)
    (ck : ∀ k, alg.c k = 1 / (γ * l)) (dk : ∀ k, alg.d k = 1 / (γ * l))
    (bd : Bornology.IsBounded (alg.z '' univ))(lbdψ : BddBelow (alg.ψ '' univ)):
    IsCompact (limit_set alg.z) ∧ IsConnected (limit_set alg.z) := by
  constructor
  · apply Metric.isCompact_of_isClosed_isBounded
    apply isClosed_setOf_clusterPt
    apply isBounded_iff_forall_norm_le.mpr
    rcases isBounded_iff_forall_norm_le.mp bd with ⟨C, zin⟩
    use C; rintro z_ z_in
    rcases subseq_tendsto_of_neBot z_in with ⟨φ, ⟨_, conv⟩⟩
    apply le_of_tendsto' (Tendsto.norm conv) (fun n ↦ zin _ (mem_image_of_mem alg.z (mem_univ (φ n))))
  --the following is the proof of connectivity
  constructor; exact (limitset_property_1 γ hγ ck dk bd lbdψ).1
  rw [isPreconnected_closed_iff]
  --construct closed A,B such that A∩B=∅,A∪B=limit_set
  by_contra nonconnect; push_neg at nonconnect
  rcases nonconnect with ⟨a, b, closea, closeb, sub_ab, nez_a, nez_b, nz_ab⟩
  let A := (limit_set alg.z) ∩ a
  let B := (limit_set alg.z) ∩ b
  have eqAB : A ∪ B = limit_set alg.z := by
    simp [A, B]
    rw [← inter_union_distrib_left (limit_set z) a b, left_eq_inter.mpr sub_ab]; simp
  have disjoint_AB : A ∩ B = ∅ := by
    simp [A, B]
    rwa [← inter_inter_distrib_left (limit_set z) a b]
  -- ω is a function that shows the relation between z and A,B
  let ω : WithLp 2 (E × F) -> ℝ := fun z => ((Metric.infEDist z A).toReal) /
    ((Metric.infEDist z A).toReal+(Metric.infEDist z B).toReal)
  have sum_ne_zero : ∀ z, (Metric.infEDist z A).toReal + (Metric.infEDist z B).toReal ≠ 0:= by
    intro z eq0
    have hAclosed : IsClosed A := by
      dsimp [A]
      exact IsClosed.inter isClosed_setOf_clusterPt closea
    have hzA : z ∈ closure A := by
      apply Metric.mem_closure_iff_infEDist_zero.mpr
      have : (Metric.infEDist z A).toReal = 0 := by
        linarith [eq0, @ENNReal.toReal_nonneg (Metric.infEDist z A),
          @ENNReal.toReal_nonneg (Metric.infEDist z B)]
      exact (((fun {x y} hx hy ↦ (ENNReal.toReal_eq_toReal_iff' hx hy).mp)
          ENNReal.top_ne_zero.symm (Metric.infEDist_ne_top nez_a) (id (Eq.symm this)))).symm
    have inA : z ∈ A := by
      simpa [hAclosed.closure_eq] using hzA
    have hBclosed : IsClosed B := by
      dsimp [B]
      exact IsClosed.inter isClosed_setOf_clusterPt closeb
    have hzB : z ∈ closure B := by
      apply Metric.mem_closure_iff_infEDist_zero.mpr
      have : (Metric.infEDist z B).toReal = 0 := by
        linarith [eq0, @ENNReal.toReal_nonneg (Metric.infEDist z A),
          @ENNReal.toReal_nonneg (Metric.infEDist z B)]
      exact (((fun {x y} hx hy ↦ (ENNReal.toReal_eq_toReal_iff' hx hy).mp)
          ENNReal.top_ne_zero.symm (Metric.infEDist_ne_top nez_b) (id (Eq.symm this)))).symm
    have inB : z ∈ B := by
      simpa [hBclosed.closure_eq] using hzB
    obtain hzin : z ∈ A ∩ B := mem_inter inA inB
    rw [disjoint_AB] at hzin; contradiction
  have contω : Continuous ω := by
    apply (Metric.continuous_infDist_pt A).div _ sum_ne_zero
    apply (Metric.continuous_infDist_pt A).add (Metric.continuous_infDist_pt B)
  let U := {z : WithLp 2 (E × F) | (ω z) < (1 / 4)}
  let V := {z : WithLp 2 (E × F) | (3 / 4) < (ω z)}
  have A0 : ∀ z_ ∈ A, ω z_ = 0 := by
    rintro z_ zA; rw [div_eq_zero_iff]; left
    rw [Metric.infEDist_zero_of_mem zA]; rfl
  have B1 : ∀ z_ ∈ B, ω z_ = 1 := by
    rintro z_ zB; simp [ω]; apply (div_eq_one_iff_eq (sum_ne_zero z_)).mpr; simp
    rw [Metric.infEDist_zero_of_mem zB]; rfl
  --eventually alg.z falls in U or V
  have U_V_prop : ∃ k0, ∀ k, (k0 ≤ k) -> (alg.z k ∈ U) ∨ (alg.z k ∈ V) := by
    by_contra h
    push_neg at h
    let W : ℕ → ℕ := fun n ↦ Nat.recOn n (Classical.choose (h 0))
      fun n p ↦ (Classical.choose (h (p + 1)))
    obtain monoW : StrictMono W :=
      strictMono_nat_of_lt_succ (fun n ↦ (fun n ↦ (Classical.choose_spec (h (W n + 1))).1 ) n)
    have bd' : Bornology.IsBounded (alg.z ∘ W '' univ):=by
      apply bd.subset; intro k; simp
      exact fun x zk ↦ ⟨W x, zk⟩
    have : ∃ z_∈ closure (alg.z∘W '' univ), ∃ α : ℕ → ℕ, StrictMono α ∧
        Tendsto (fun n ↦ (alg.z∘W) (α n)) atTop (𝓝 z_) := by
      have even n : (alg.z ∘ W) n ∈ closure (alg.z ∘ W '' univ) :=
          subset_closure (mem_image_of_mem (z ∘ W) trivial)
      apply (IsCompact.isSeqCompact bd'.isCompact_closure).subseq_of_frequently_in
        (Filter.Frequently.of_forall even)
    rcases this with ⟨z_, _, α, ⟨monoa, conv⟩⟩
    have z_in : z_ ∈ limit_set alg.z := by
      simp [limit_set, MapClusterPt]
      apply ClusterPt.mono (ClusterPt.of_le_nhds conv)
      calc
        _ = map (fun n ↦ (alg.z ∘ W) n) (map α atTop) := by rw [map_map]; rfl
        _ ≤ map (fun n↦ (alg.z ∘ W) n) atTop := map_mono (StrictMono.tendsto_atTop monoa)
        _ ≤ map (fun n ↦ alg.z n) atTop := by
          rw [← map_map]; apply map_mono (StrictMono.tendsto_atTop monoW)
    rw [← eqAB] at z_in
    rcases z_in with zA | zB
    · have z_ge : ω z_ ≥ 1 / 4 := by
        apply ge_of_tendsto (continuous_iff_seqContinuous.mp contω conv)
        simp; use 1; rintro n len
        have key : 1 / 4 ≤ ω ((alg.z ∘ W) (α n - 1 + 1)) :=by
          obtain ht := (Classical.choose_spec (h (W (α n - 1) +1))).2.1
          rw [Set.mem_setOf] at ht
          push_neg at ht; exact ht
        rw [← tsub_add_cancel_iff_le.mpr (Nat.one_le_of_lt (monoa len))]
        simp at key; exact key
      linarith [A0 z_ zA]
    · have z_ge : ω z_ ≤ 3 / 4 := by
        apply le_of_tendsto (continuous_iff_seqContinuous.mp (contω) conv)
        simp; use 1; rintro n len
        have key : ω ((alg.z ∘ W) (α n - 1 + 1)) ≤ 3 / 4 :=by
          obtain ht := (Classical.choose_spec (h (W (α n -1) +1))).2.2
          rw [Set.mem_setOf] at ht
          push_neg at ht; exact ht
        rw [← tsub_add_cancel_iff_le.mpr (Nat.one_le_of_lt (monoa len))]
        simp at key; exact key
      linarith [B1 z_ zB]
  rcases U_V_prop with ⟨k0,hk0⟩
  --eventually alg.z falls into the same U or V
  obtain unicont := IsCompact.uniformContinuousOn_of_continuous
    bd.isCompact_closure contω.continuousOn
  have : ∀ ε > 0, ∃ δ > 0, ∀ x1 ∈ (closure (alg.z '' univ)),
      ∀ x2 ∈ (closure (alg.z '' univ)), ‖x1 - x2‖ < δ → ‖ω x1 - ω x2‖ < ε:=by
    obtain h := (((@NormedAddCommGroup.uniformity_basis_dist (WithLp 2 (E × F)) _).inf
      (hasBasis_principal ((closure (alg.z '' univ)) ×ˢ(closure (alg.z '' univ))))).tendsto_iff
      (@NormedAddCommGroup.uniformity_basis_dist ℝ _) ).mp unicont
    simp at h; rw [Eq.symm image_univ] at h
    rintro ε epos; rcases h ε epos with ⟨δ, ⟨dpos, ieq⟩⟩
    exact ⟨δ, ⟨dpos, fun x1 x1s x2 x2s dis ↦ ieq x1 x2 dis x1s x2s⟩⟩
  have : ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖ω (alg.z (n + 1)) - ω (alg.z n)‖ < ε:=by
    rintro ε epos
    rcases this ε epos with ⟨δ,dpos,ieq⟩
    rcases (nhds_basis_abs_sub_lt 0).tendsto_right_iff.mp
      (Sufficient_Descent4 γ hγ ck dk lbdψ) δ dpos with lte
    simp at lte
    rcases lte with ⟨a,ie⟩
    use a; rintro n alen
    apply ieq; apply subset_closure (mem_image_of_mem z (mem_univ (n + 1)))
    apply subset_closure (mem_image_of_mem z (mem_univ n)); apply ie n alen
  rcases this (1 / 2) one_half_pos with ⟨N, key⟩
  have : ∃ M, (∀ n ≥ M, alg.z n ∈ U) ∨ (∀ n ≥ M, alg.z n ∈ V) := by
    let M := max k0 N; use M
    rcases hk0 M (Nat.le_max_left k0 N) with MU | MV
    left
    have (n : ℕ) : alg.z (M + n) ∈ U := by
      induction' n with n ih
      · exact MU
      rcases hk0 (M + n + 1) ((Nat.le_max_left _ _).trans (Nat.le_add_right M (n + 1))) with nU | nV
      exact nU; rw [mem_setOf] at ih nV
      linarith [(abs_lt.mp (key (M + n)
        ((Nat.le_max_right k0 N).trans (Nat.le_add_right M n)))).2, ih, nV]
    rintro n Mlen; rw [← Nat.add_sub_of_le Mlen]; apply this (n - M)
    right
    have (n : ℕ) : alg.z (M + n) ∈ V := by
      induction' n with n ih
      · exact MV
      rcases hk0 (M + n + 1) ((Nat.le_max_left _ _).trans (Nat.le_add_right M (n + 1))) with nU | nV
      rw [mem_setOf] at ih nU
      linarith [(abs_lt.mp (key (M + n)
        ((Nat.le_max_right k0 N).trans (Nat.le_add_right M n)))).1,ih,nU]; exact nV
    rintro n Mlen; rw [← Nat.add_sub_of_le Mlen]; apply this (n - M)
  --show the contradiction
  rcases this with ⟨M, h1 | h2⟩
  · rcases nez_b with ⟨z_, inB⟩
    have : z_ ∈ limit_set alg.z := mem_of_mem_inter_left inB
    rcases subseq_tendsto_of_neBot this with ⟨φ, monoφ, conv⟩
    have : ω z_ ≤ 1 / 4 := by
      apply le_of_tendsto (continuous_iff_seqContinuous.mp (contω) conv)
      simp; use M; rintro b Mleb
      have g := h1 (φ b) (Mleb.trans (StrictMono_nat φ monoφ b))
      rw [mem_setOf] at g; simp at g; apply le_of_lt g
    linarith [this, B1 z_ inB]
  · rcases nez_a with ⟨z_, inA⟩
    have : z_∈limit_set alg.z:= mem_of_mem_inter_left inA
    rcases (subseq_tendsto_of_neBot this) with ⟨φ,monoφ,conv⟩
    have : ω z_ ≥ 3 / 4 := by
      apply ge_of_tendsto (continuous_iff_seqContinuous.mp (contω) conv)
      simp; use M; rintro b Mleb
      have g := h2 (φ b) (Mleb.trans (StrictMono_nat φ monoφ b))
      rw [mem_setOf] at g; apply le_of_lt g
    linarith [this,A0 z_ inA]


lemma limitset_property_4 (γ : ℝ) (hγ : γ > 1)
    (ck: ∀ k, alg.c k = 1 / (γ * l)) (dk: ∀ k, alg.d k = 1 / (γ * l))
    (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
    ∃ (c:ℝ) , ∀ x ∈ (limit_set alg.z) , alg.ψ x = c := by
  -- alg.ψ converges to same ψ_final
  have decent_ψ : ∃ ψ_final, Tendsto (alg.ψ ∘ alg.z) Filter.atTop (nhds ψ_final) := by
    have monopsi : Antitone (alg.ψ ∘ alg.z) :=
      antitone_nat_of_succ_le (Sufficient_Descent2 γ hγ ck dk)
    rcases tendsto_atTop_of_antitone monopsi with h1 | h2
    · rcases lbdψ with ⟨m, hm⟩
      rcases (Filter.tendsto_atTop_atBot.mp h1) (m - 1) with ⟨N, hN⟩
      have hmN : m ≤ (alg.ψ ∘ alg.z) N := hm (by
        refine ⟨alg.z N, ?_, rfl⟩
        exact mem_univ _)
      have hle : (alg.ψ ∘ alg.z) N ≤ m - 1 := hN N le_rfl
      linarith
    · exact h2
  rcases decent_ψ with ⟨ψ_final, hψ⟩
  -- show that ψ_final is what we need
  use ψ_final; intro z_1 hz_1
  rcases (subseq_tendsto_of_neBot hz_1) with ⟨φ, ⟨monoφ, conv⟩⟩
  have tend1 : Tendsto (alg.ψ ∘ alg.z ∘ φ) atTop (𝓝 ψ_final):=by
    apply le_trans _ hψ
    rw [← Filter.map_map]; apply map_mono $ StrictMono.tendsto_atTop monoφ
  apply tendsto_nhds_unique (psiconv γ hγ ck dk φ z_1 monoφ conv bd lbdψ) tend1

end limit_point

section Limited_length

variable [ProperSpace E] [ProperSpace F]

private lemma concave_deriv_bound {φ : ℝ → ℝ} {η x y : ℝ} (h : φ ∈ desingularizing_function η)
    (hx : x ∈ Ioo 0 η) (hy : y ∈ Ioo 0 η) : φ x - φ y ≥ deriv φ x * (x - y) := by
  obtain ⟨h1, _, _, _, h6⟩ := h
  have hdiff := differentiableAt_of_deriv_ne_zero (ne_of_gt (h6 _ hx))
  let hx' := Ioo_subset_Ico_self hx
  let hy' := Ioo_subset_Ico_self hy
  rcases eq_or_ne x y with heq | hne
  · rw [heq]; simp only [sub_self, mul_zero, ge_iff_le, le_refl]
  · rw [← lt_or_lt_iff_ne] at hne
    rcases hne with ygt | xgt
    · obtain h := ConcaveOn.slope_le_deriv h1 hx' hy' ygt hdiff
      rw [slope_def_field, div_le_iff₀] at h
      repeat linarith
    · obtain h := ConcaveOn.deriv_le_slope h1 hy' hx' xgt hdiff
      rw [slope_def_field, le_div_iff₀] at h
      repeat linarith

private lemma sq_le_mul_le_mean {a b c : ℝ} (h : a ^ 2 ≤ b * c) (hpos : 0 ≤ b + c) : 2 * a ≤ b + c := by
  have : 4 * b * c ≤ (b + c) ^ 2 := by
    have : 0 ≤ (b - c) ^ 2 := sq_nonneg _
    rw [add_sq]; linarith
  exact (abs_le_of_sq_le_sq' (by linarith) hpos).2

private lemma ENNReal.mul_pos_real {a : ℝ} {b : ENNReal} (ha : a > 0) (hm : 1 ≤ ENNReal.ofReal a * b)
    (hb : b < ⊤) : a * ENNReal.toReal b ≥ (1 : ℝ) := by
  lift a to NNReal using (by linarith)
  lift b to NNReal using LT.lt.ne_top hb
  simp at hm; simp; rw [← NNReal.coe_mul]
  rw [← ENNReal.coe_mul] at hm
  rwa [ENNReal.one_le_coe_iff] at hm

theorem Limited_length (γ : ℝ) (hγ : γ > 1)
    (ck : ∀ k, alg.c k = 1 / (γ * l)) (dk : ∀ k, alg.d k = 1 / (γ * l))
    (bd : Bornology.IsBounded (alg.z '' univ)) (hψ : KL_function alg.ψ)
    (lbdψ : BddBelow (alg.ψ '' univ)) :
    ∃ M : ℝ, ∀ n, (Finset.range n).sum (fun k ↦ ‖alg.z (k + 1) - alg.z k‖) ≤ M := by
  have :∃ z_∈ closure (alg.z '' univ), ∃ α:ℕ → ℕ,StrictMono α∧Tendsto
      (fun n ↦ alg.z (α n)) atTop (𝓝 z_):= by
    have hcs : IsSeqCompact (closure (alg.z '' univ)) := by
      apply IsCompact.isSeqCompact
      exact bd.isCompact_closure
    have even n : alg.z n ∈ closure (alg.z '' univ) := subset_closure (mem_image_of_mem alg.z trivial)
    exact hcs.subseq_of_frequently_in (Filter.Frequently.of_forall even)
  rcases this with ⟨z_, _, α, ⟨monoa, conv⟩⟩
  rcases Sufficient_Descent1 γ hγ ck dk with ⟨ρ1,ρ1pos,suff_des⟩
  have z_in : z_ ∈ limit_set alg.z:= by
    simp [limit_set, MapClusterPt]
    apply ClusterPt.mono (ClusterPt.of_le_nhds conv)
    calc
      _ = map (fun n ↦ alg.z n) (map α atTop) := by
        rw [map_map]; rfl
      _ ≤ map (fun  n↦ alg.z n) atTop := map_mono (StrictMono.tendsto_atTop monoa)
  have final m : ∃ n : ℕ, m ≤ α n := by
    induction' m with m ih
    · use 1; linarith
    rcases ih with ⟨n, ieqq⟩
    use n + 1
    have : α n + 1 ≤ α (n + 1) := by
      apply Nat.succ_le_iff.mpr; apply monoa; norm_num
    linarith
  obtain psiconv := psiconv γ hγ ck dk α z_ monoa conv bd lbdψ
  have monopsi (m n : ℕ) : alg.ψ (alg.z (m + n)) ≤ alg.ψ (alg.z m):= by
    induction' n with n ih
    · simp
    exact Preorder.le_trans _ _ _ (Sufficient_Descent2 γ hγ ck dk (m + n)) ih
  by_cases h : ∀ n, alg.ψ (alg.z (α n)) > alg.ψ z_
  · have L1 : ∀ η > 0, ∃ l1 : ℕ, ∀ k ≥ l1, alg.ψ z_ < alg.ψ (alg.z k)
        ∧ alg.ψ (alg.z k) <alg.ψ z_ + η := by
      rintro η epos
      rcases (atTop_basis.tendsto_iff (nhds_basis_Ioo_pos (alg.ψ z_))).mp
        psiconv η epos with ⟨l1,_,ieq⟩
      use α l1; rintro k kge
      constructor
      rcases final k with ⟨m,kleam⟩
      calc
        _ < alg.ψ (alg.z (α m)) := h m
        _ = alg.ψ (alg.z (k + (α m - k))) := by
          congr; exact Eq.symm (Nat.add_sub_of_le kleam)
        _ ≤ alg.ψ (alg.z k) := monopsi k (α m - k)
      calc
        _ = alg.ψ (alg.z (α l1 + (k - α l1))):= by
          congr; exact Eq.symm (Nat.add_sub_of_le kge)
        _ ≤ alg.ψ (alg.z (α l1)) := by apply monopsi
        _ < alg.ψ z_ + η := (ieq l1 Set.self_mem_Ici).2
    have L2 : ∀ ε > 0, ∃ l2, ∀k > l2, (Metric.infEDist (alg.z k) (limit_set alg.z)).toReal< ε := by
      rintro ε epos
      rcases limitset_property_2 bd with tendt
      rcases (atTop_basis.tendsto_iff (nhds_basis_abs_sub_lt (0:ℝ))).mp tendt ε epos with ⟨l2,_,ieq⟩
      simp at ieq; exact ⟨l2, fun k kgt ↦ (ieq k (le_of_lt kgt))⟩
    -- have active (n:ℕ) (ngt0 : n>0) : alg.z n ∈ active_domain alg.ψ := by
    --   simp [active_domain]
    --   push_neg
    --   rcases Ψ_subdiff_bound γ hγ ck dk with ⟨_,_,ex⟩
    --   rcases ex (n-1) with ⟨ d,din,_⟩
    --   have : d ∈ subdifferential alg.ψ (alg.z n) := by
    --     apply subdifferential_subset
    --     rw [Nat.sub_add_cancel ngt0] at din; exact din
    --   apply Set.nonempty_of_mem this
    have wklpt : ∀ z0 ∈ (limit_set alg.z), KL_point alg.ψ z0 := by
      rintro z0 z0in; apply hψ
      simp [active_domain]
      intro empt
      have : (0 : WithLp 2 (E × F)) ∈ subdifferential alg.ψ z0 :=
        (limitset_property_1 γ hγ ck dk bd lbdψ).2 z0in
      rw [empt] at this; exact this
    have cons : is_constant_on alg.ψ (limit_set alg.z):= by
      simp [is_constant_on]
      intro x xin y yin
      rcases limitset_property_4 γ hγ  ck dk bd lbdψ with ⟨C,heq⟩
      rw [heq x xin,heq y yin]
    have kl: ∃ ε ∈ Set.Ioi (0 : ℝ), ∃ η ∈  Set.Ioi (0 : ℝ), ∃ φ ∈ desingularizing_function η, ∃ LL, ∀ n > LL,
        (alg.ψ z_ < alg.ψ (alg.z n) ∧ alg.ψ (alg.z n) < alg.ψ z_ + η) ∧ ENNReal.ofReal (deriv φ (alg.ψ (alg.z n)
        - alg.ψ z_)) * Metric.infEDist 0 (subdifferential alg.ψ (alg.z n)) ≥ 1 := by
      rcases uniformized_KL_property (limitset_property_3 γ hγ ck dk bd lbdψ).1 wklpt cons
        with ⟨ε, eppos, η, etpos, φ, hφ, pro⟩
      rcases L1 η etpos with ⟨l1,lem1⟩
      rcases L2 ε eppos with ⟨l2,lem2⟩
      refine' ⟨ε,eppos,η,etpos,φ,hφ,max l1 l2,_⟩
      intro n ngt
      constructor
      · apply lem1 n (le_of_lt (lt_of_le_of_lt (le_max_left l1 l2) ngt))
      apply pro z_ z_in
      simp; constructor
      apply lem2
      apply lt_of_le_of_lt (le_max_right l1 l2) ngt
      constructor
      · exact (lem1 n (le_of_lt (lt_of_le_of_lt (le_max_left l1 l2) ngt))).1
      exact (lem1 n (le_of_lt (lt_of_le_of_lt (le_max_left l1 l2) ngt))).2
    rcases kl with ⟨ε, _, η, _, φ, hφ, LL, ieq⟩
    -- The rest of proof after using KL property
    let a := fun n ↦ φ (alg.ψ (alg.z (n + LL + 1)) - alg.ψ z_)
    let b := fun n ↦ alg.ψ (alg.z (n + LL + 1)) - alg.ψ (alg.z (n + 1 + LL + 1))
    let c := fun n ↦ ‖alg.z (n + LL + 1) - alg.z (n + LL)‖
    let d := fun n ↦ deriv φ (alg.ψ (alg.z (n + LL + 1)) - alg.ψ z_)
    let sum := fun n ↦ ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖
    have hlin n : alg.ψ (alg.z (n + LL + 1)) - alg.ψ z_ ∈ Ioo 0 η := by
      specialize ieq (n + LL + 1) (by linarith)
      obtain ⟨⟨h1, h2⟩, _⟩ := ieq
      constructor <;> linarith
    obtain ⟨ρ, ρpos, hsgub⟩ := Ψ_subdiff_bound γ hγ ck dk
    let C := ρ / (ρ1 / 2)
    have hnnegC : 0 ≤ C := div_nonneg (le_of_lt ρpos) (by linarith)
    have hposa n : 0 < a n := (desingularizing_function_is_nonneg φ η hφ) _ (hlin n)
    have hbd n : 2 * c (n + 1) ≤ c n + C * ((a n) - a (n + 1)) := by
      have hpc : d n * b n ≤ (a n) - a (n + 1) := by
        obtain hderiv := concave_deriv_bound hφ (hlin n) (hlin (n + 1))
        rw [sub_sub] at hderiv
        simp only [add_sub_cancel, ge_iff_le] at hderiv
        assumption
      have hposd : d n > 0 := by
        obtain ⟨_, _, _, _, h6⟩ := hφ
        exact h6 _ (hlin n)
      have hbd2 : 1 ≤ ρ * (c n) * d n := by
        obtain ⟨dpsi, hdp, hub⟩ := hsgub (n + LL)
        have hdp' : dpsi ∈ subdifferential alg.ψ (alg.z (n + LL + 1)) :=
          subdifferential_subset (alg.ψ) (alg.z (n + LL + 1)) hdp
        let S := subdifferential alg.ψ (alg.z (n + LL + 1))
        have h_inf_edist : Metric.infEDist 0 S ≤ edist 0 dpsi := Metric.infEDist_le_edist_of_mem hdp'
        have h_inf : Metric.infEDist 0 S ≤ ENNReal.ofReal ‖dpsi‖ := by
          simpa [edist_dist] using h_inf_edist
        have h_inf_real : (Metric.infEDist 0 S).toReal ≤ ‖dpsi‖ := by
          exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) h_inf
        have h_en : 1 ≤ ENNReal.ofReal (d n) * Metric.infEDist 0 S := by
          simpa [S] using (ieq (n + LL + 1) (by linarith)).2
        have h_real : d n * (Metric.infEDist 0 S).toReal ≥ 1 := by
          exact ENNReal.mul_pos_real hposd h_en (lt_top_iff_ne_top.mpr (Metric.infEDist_ne_top (by
            refine ⟨dpsi, hdp'⟩)))
        have hub' : ‖dpsi‖ ≤ ρ * c n := by
          simpa [c] using hub
        have h_mul1 : d n * (Metric.infEDist 0 S).toReal ≤ d n * ‖dpsi‖ := by
          exact mul_le_mul_of_nonneg_left h_inf_real (le_of_lt hposd)
        have h_mul2 : d n * ‖dpsi‖ ≤ d n * (ρ * c n) := by
          exact mul_le_mul_of_nonneg_left hub' (le_of_lt hposd)
        nlinarith [h_real, h_mul1, h_mul2]
      have hsd : ρ1 / 2 * (c (n + 1)) ^ 2 ≤ b n := by
        obtain h := suff_des.2 (n + LL + 1)
        rw [add_right_comm n LL 1] at h
        nth_rw 3 [add_right_comm n 1 LL] at h; exact h
      have hsd' : (c (n + 1)) ^ 2 ≤ b n / (ρ1 / 2) := by rwa [le_div_iff₀']; linarith
      have hnnegb' : 0 ≤ b n / (ρ1 / 2) := le_trans (sq_nonneg _) hsd'
      have hnnegb : 0 ≤ b n := calc
        0 ≤ b n / (ρ1 / 2) * (ρ1 / 2) := (mul_nonneg_iff_of_pos_right (by linarith)).mpr hnnegb'
        _ = b n := div_mul_cancel₀ _ (by linarith)
      have hnnega' : 0 ≤ (a n - a (n + 1)) :=
          le_trans ((mul_nonneg_iff_of_pos_left hposd).mpr hnnegb) hpc
      have hnnegc' : 0 ≤ C * (c n) := mul_nonneg hnnegC (norm_nonneg _)
      have hbd : (c (n + 1)) ^ 2 ≤ C * (c n) * ((a n) - a (n + 1)) := calc
        c (n + 1) ^ 2 ≤ b n / (ρ1 / 2) := hsd'
        _ ≤ b n / (ρ1 / 2) * (ρ * (c n) * d n) := le_mul_of_one_le_right hnnegb' hbd2
        _ = C * (c n) * (d n * b n) := by ring
        _ ≤ C * (c n) * ((a n) - a (n + 1)) := mul_le_mul_of_nonneg_left hpc hnnegc'
      apply sq_le_mul_le_mean
      rwa [← mul_assoc, mul_comm _ C]
      exact add_nonneg (norm_nonneg _) (mul_nonneg hnnegC hnnega')
    have hbd' n : (Finset.range (n + 1)).sum c ≤ 2 * c 0 + C * a 0 := by
      have hsum n : (Finset.range (n + 1)).sum c ≤ 2 * c 0 - c n + C * (a 0 - a n) := by
        induction' n with i h
        · simp; linarith
        · have : (Finset.range (i + 1 + 1)).sum c = (Finset.range (i + 1)).sum c + c (i + 1) :=
            Finset.sum_range_succ _ (i + 1)
          linarith [hbd i]
      have : 0 ≤ c n := norm_nonneg _
      linarith [mul_nonneg hnnegC (le_of_lt (hposa n)), hsum n]
    have hs n : sum n ≤ sum LL + (Finset.range (n + 1)).sum c := by
      have hs n : sum (n + 1) = sum n + ‖alg.z (n + 1) - alg.z n‖ :=
        Finset.sum_range_succ (fun k ↦ ‖alg.z (k + 1) - alg.z k‖) n
      have hc n : sum (n + LL + 1) = sum (n + LL) + c n := hs (n + LL)
      have : sum LL + (Finset.range (n + 1)).sum c = sum (n + LL + 1) := by
        induction' n with i hn
        · rw [hc 0]; simp
        · rw [Finset.sum_range_succ c (i + 1), hc (i + 1), add_right_comm, ← hn]; ring
      have hspos n k : sum n ≤ sum (n + k) := by
        induction' k with i hk
        · rw [add_zero]
        · rw [← add_assoc, hs (n + i)]
          exact le_add_of_le_of_nonneg hk (norm_nonneg _)
      rw [this, add_assoc]
      exact hspos _ _
    use sum LL + 2 * c 0 + C * a 0
    exact fun n ↦ by linarith [hs n, hbd' n]
  push_neg at h; rcases h with ⟨n,eq⟩
  let N := α n
  have eq0 : ∀ i ≥ N, alg.z (i + 1) = alg.z i := by
    intro i ige
    have : ∀ k ≥ N, alg.ψ (alg.z k) = alg.ψ z_:= by
      intro k kge; apply le_antisymm
      calc
        _ = alg.ψ (alg.z (N + (k - N))) :=by
          congr; exact Eq.symm (Nat.add_sub_of_le kge)
        _ ≤ alg.ψ (alg.z N) := by apply monopsi
        _ ≤ alg.ψ (z_) := eq
      by_contra con; push_neg at con
      rcases final k with ⟨w,kleaw⟩
      have : alg.ψ z_≤ alg.ψ (alg.z k) := by
        apply le_of_tendsto psiconv
        apply atTop_basis.eventually_iff.mpr
        refine' ⟨w, trivial, _⟩
        intro x wlex
        have : α w ≤ α x := by
          by_cases ass : w = x
          · rw [ass]
          exact Nat.le_of_succ_le (monoa (Nat.lt_of_le_of_ne wlex ass))
        calc
          _ = alg.ψ (alg.z (k + (α x - k))) := by
            congr; exact Eq.symm (Nat.add_sub_of_le (by linarith))
          _ ≤ alg.ψ (alg.z k) := by apply monopsi
      linarith
    have : ‖alg.z (i + 1) - alg.z i‖ = 0:= by
      apply sq_eq_zero_iff.mp (le_antisymm (nonpos_of_mul_nonpos_right _
        (half_pos ρ1pos)) (sq_nonneg _))
      calc
        _ ≤ alg.ψ (alg.z i) -alg.ψ (alg.z (i + 1)) := suff_des.2 i
        _ = 0 := by simp [this i ige,this (i+1) (Nat.le_add_right_of_le ige)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  use (∑ k ∈ Finset.range N, ‖alg.z (k + 1) - alg.z k‖)
  intro n
  by_cases nlen : n ≤ N
  · refine Finset.sum_le_sum_of_subset_of_nonneg ((Finset.range_subset_range).2 nlen) ?_
    exact fun a _ _ ↦ norm_nonneg (alg.z (a + 1) - alg.z a)
  · have nlt : N < n := lt_of_not_ge nlen
    have hsub : Finset.range N ⊆ Finset.range n := (Finset.range_subset_range).2 (Nat.le_of_lt nlt)
    have hsum0 : ∑ i ∈ (Finset.range n \ Finset.range N), ‖alg.z (i + 1) - alg.z i‖ = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxN : N ≤ x := by
        have hxnot : x ∉ Finset.range N := (Finset.mem_sdiff.mp hx).2
        have hxlt : ¬ x < N := by simpa [Finset.mem_range] using hxnot
        exact Nat.le_of_not_lt hxlt
      exact norm_sub_eq_zero_iff.mpr (eq0 x hxN)
    have hsplit := Finset.sum_sdiff hsub (f := fun k ↦ ‖alg.z (k + 1) - alg.z k‖)
    have hsumEq : ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖
        = ∑ k ∈ Finset.range N, ‖alg.z (k + 1) - alg.z k‖ := by
      linarith [hsplit, hsum0]
    exact le_of_eq hsumEq

theorem Convergence_to_critpt (γ : ℝ) (hγ : γ > 1)
    (ck : ∀ k, alg.c k = 1 / (γ * l)) (dk : ∀ k, alg.d k = 1 / (γ * l))
    (bd : Bornology.IsBounded (alg.z '' univ)) (hψ : KL_function alg.ψ)
    (lbdψ : BddBelow (alg.ψ '' univ)) : ∃ z_ : (WithLp 2 (E × F)),
    z_ ∈ (critial_point alg.ψ) ∧ Tendsto alg.z atTop (𝓝 z_):= by
  have : ∃ z_, Tendsto alg.z atTop (𝓝 z_) := by
    apply cauchySeq_tendsto_of_complete
    refine cauchySeq_of_summable_dist ?_
    rcases Limited_length γ hγ ck dk bd hψ lbdψ with ⟨M, sumle⟩
    refine summable_of_sum_range_le (c := M) ?_ ?_
    · intro n
      exact dist_nonneg
    · intro n
      calc
        ∑ k ∈ Finset.range n, dist (alg.z k) (alg.z k.succ)
            = ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ := by
              apply Finset.sum_congr rfl
              intro x hx
              simpa using (dist_eq_norm' (alg.z x) (alg.z x.succ))
        _ ≤ M := sumle n
  rcases this with ⟨z_,hzz⟩
  refine' ⟨z_, _, hzz⟩
  have z_in : z_ ∈ limit_set alg.z := by
    simp [limit_set, MapClusterPt]
    exact ClusterPt.of_le_nhds hzz
  apply (limitset_property_1 γ hγ ck dk bd lbdψ).2 z_in

end Limited_length
