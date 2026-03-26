/-
Copyright (c) 2024 Zichen Wang, Yifan Bai, Pengfei Hao, Yuqing Gao, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Zichen Wang, Yifan Bai, Pengfei Hao, Yuqing Gao, Anqing Shen, Zaiwen Wen
-/
import Optlib.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences
import Optlib.Algorithm.ADMM.Lemma
import Optlib.Algorithm.ADMM.Scheme
import Optlib.Convex.ImageSubgradientClosed

noncomputable section

open Set InnerProductSpace Topology Filter Bornology Metric Real

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]

variable(admm : ADMM E₁ E₂ F)

namespace ADMM_Converge_Proof

variable {admm admm_kkt}

local notation "f₁" => admm.f₁
local notation "f₂" => admm.f₂
local notation "A₁" => admm.A₁
local notation "A₂" => admm.A₂
local notation "b" => admm.b
local notation "x₁" => admm.x₁
local notation "x₂" => admm.x₂
local notation "y" => admm.y
local notation "τ" => admm.τ
local notation "ρ" => admm.ρ

local notation "x₁'" => admm_kkt.x₁
local notation "x₂'" => admm_kkt.x₂
local notation "y'" => admm_kkt.y

local notation "A₁†" => ContinuousLinearMap.adjoint A₁
local notation "A₂†" => ContinuousLinearMap.adjoint A₂

section

-- variable [Setting E₁ E₂ F admm admm_kkt]

lemma inSet {X : Type*} ( f : ℕ → X ) : ∀ n : ℕ , f n ∈ range f := by
   intro n;use n

lemma nonneg_prime [Setting E₁ E₂ F admm admm_kkt]: 1 + τ - τ ^ 2 > 0 := by
   rcases admm.htau with ⟨h1, _⟩
   have h0 : 1 + τ - τ ^ 2 = - (τ - 1/2)^ 2 + 5/4 := by ring
   rw [h0];simp only [one_div, gt_iff_lt, lt_neg_add_iff_add_lt, add_zero]
   have h2 : 5/4 = |√5/2|^2:= by
      rw [sq_abs]; field_simp; norm_num
   rw [h2];apply sq_lt_sq.mpr;simp only [abs_abs]
   have h6 : |τ - 2⁻¹| < √5/2 := by
      let θ := τ - 2⁻¹
      have h7 : |θ| < √5/2 := by
         have g1 : (1 + √5) / 2 - 1 / 2 = √5 / 2 := by ring
         have h8 : θ < √5/2 :=
         calc
            _ = τ - 2⁻¹ := by rfl
            _ < (1 + √5) / 2 - 2⁻¹ := by linarith [h2]
            _ = √5/2 := by norm_num [g1]
         have h9 : -(√5/2) < θ := by
            have g2 : 1/2 < √5/2 := by
               apply div_lt_div_of_pos_right _ zero_lt_two
               apply (lt_sqrt _).mpr _
               repeat norm_num
            have h10 : θ > -(√5/2) := by
               calc
                  _ = τ - 2⁻¹ := by rfl
                  _ > 0 - 2⁻¹ := by linarith [h1]
                  _ > -(√5/2) := by norm_num [g2]
            rwa[← gt_iff_lt]
         rw[abs_lt];exact ⟨h9, h8⟩
      exact h7
   apply lt_abs.mpr;left;exact h6

lemma nonneg₁ [Setting E₁ E₂ F admm admm_kkt]: min τ (1 + τ - τ ^ 2) > 0 := by
   rcases admm.htau with ⟨h1, _⟩
   have h2 : 1 + τ - τ ^ 2 > 0 := nonneg_prime
   apply lt_min h1 h2

lemma nonneg₂ [Setting E₁ E₂ F admm admm_kkt]: min 1 (1 + 1 / τ - τ) > 0 := by
   rcases admm.htau with ⟨h1, _⟩
   have h2: 1 + 1/τ - τ > 0 := by
      have hτ : τ ≠ 0 := ne_of_gt h1
      rw [show 1 + 1 / τ - τ = (1 + τ - τ ^ 2) / τ by field_simp [hτ]; ring]
      exact div_pos nonneg_prime h1
   apply lt_min one_pos h2

lemma Φ₁_nonneg [Setting E₁ E₂ F admm admm_kkt]:
∀ n : ℕ+ , 0 ≤ (min τ (1 + τ - τ ^ 2) ) * ρ * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2 := by
   intro n
   have ha: 0 < (min τ (1 + τ - τ ^ 2) ) * ρ := by
      apply mul_pos nonneg₁ ADMM.hrho
   have ha': 0 ≤ (min τ (1 + τ - τ ^ 2) ) * ρ := by apply le_of_lt ha
   have hb: 0 ≤ ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2 := by apply sq_nonneg
   apply mul_nonneg ha' hb

lemma Φ₂_nonneg [Setting E₁ E₂ F admm admm_kkt]:
∀ n : ℕ+ ,  0 ≤ (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2 := by
   intro n
   have ha: 0 < (min 1 (1 + 1 / τ - τ )) * ρ := by
      apply mul_pos nonneg₂ ADMM.hrho
   have ha': 0 ≤ (min 1 (1 + 1 / τ - τ )) * ρ := by apply le_of_lt ha
   have hb: 0 ≤ ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2 := by apply sq_nonneg
   apply mul_nonneg ha' hb

lemma big_is_ge_zero [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
(min τ (1 + τ - τ ^ 2)) * ρ * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2
+ (min 1 (1 + 1 / τ - τ)) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2
≥ 0 := by
   intro n
   have h1 :=Φ₁_nonneg n
   have h2 :=Φ₂_nonneg n
   apply add_nonneg h1 h2

lemma Φ_is_monotone [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+, Φ n ≥ Φ (n+1) := by
   intro n
   let c := (min τ (1 + τ - τ ^ 2)) * ρ * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2
          + (min 1 (1 + 1 / τ - τ)) * ρ * ‖A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))‖ ^ 2
   have h : c ≥ 0 := by apply big_is_ge_zero
   have h' : (Φ n) - (Φ (n + 1)) ≥ 0 := by
      calc
         _ ≥ c := by apply Φ_isdescending
         _ ≥ 0 := by apply h
   linarith [h']

lemma nonneg₃ [Setting E₁ E₂ F admm admm_kkt]: max (1 - τ) (1 - 1 / τ) ≥ 0 := by
   rcases τ_segment with h|h
   case inl
   => have ha : 1 - τ ≥ 1 - 1/τ := by
         apply sub_le_sub_left; rw [le_div_iff₀ (by linarith), ← sq]
         apply pow_le_one₀; repeat linarith
      rw [max_eq_left ha];linarith
   case inr
   => have hb : 1 - 1/τ ≥ 1 - τ := by
         have : 1 / τ ≤ 1 := by
            rw [one_div]
            apply inv_le_one_of_one_le₀; linarith
         linarith
      rw [max_eq_right hb];apply sub_nonneg_of_le
      rw [one_div];apply inv_le_one_of_one_le₀; linarith

lemma Φ_is_nonneg [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ , Φ n ≥ 0 := by
   intro n
   rcases admm.htau with ⟨h1, _⟩
   simp [Φ]
   have h2 : Ψ n ≥ 0 := by
      simp [Ψ];apply add_nonneg;repeat apply mul_nonneg
      apply inv_nonneg_of_nonneg; apply le_of_lt admm.hrho
      apply inv_nonneg_of_nonneg; apply le_of_lt h1
      apply pow_two_nonneg;apply mul_nonneg; apply le_of_lt admm.hrho; apply pow_two_nonneg
   have h3 : ((max (1 - τ) (1 - 1/τ)) * ρ) * ‖A₁ ((e₁) n) + A₂ ((e₂) n)‖ ^2 ≥ 0 := by
      repeat apply mul_nonneg
      apply nonneg₃
      apply le_of_lt admm.hrho
      apply pow_two_nonneg
   rw [← one_div];apply add_nonneg h2 h3

lemma Φ_bd_above [Setting E₁ E₂ F admm admm_kkt]: ∃ C : ℝ, ∀ n : ℕ, Φ n < C := by
   let C := Max.max ((Φ 0) + 1) ((Φ 1) + 1); use C; intro n
   induction n with
   | zero =>
      have : Φ 0 < (Φ 0) + 1 := by linarith
      apply lt_max_iff.2
      left; exact this
   | succ k h =>
      by_cases hh : k = 0
      · rw [hh,zero_add]
        apply lt_max_iff.2
        right; linarith
      · push_neg at hh
        have k_pos : k > 0 := by exact Nat.pos_of_ne_zero hh
        have : (Φ) (k.toPNat k_pos) ≥ (Φ) ((k.toPNat k_pos) + 1) := by
          apply Φ_is_monotone
        have h' : Φ (k.toPNat k_pos) < C := by simpa using h
        show Φ ((k.toPNat k_pos) + 1) < C
        linarith

lemma Φ_isBounded' [Setting E₁ E₂ F admm admm_kkt] : ∃ (r : ℝ), (range Φ) ⊆ ball 0 r := by
   rcases Φ_bd_above with ⟨C,bd⟩
   use C; intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩; rw [← eq, abs_eq_self.2]; exact bd n
   apply Φ_is_nonneg

lemma Φ_isBounded [Setting E₁ E₂ F admm admm_kkt]: IsBounded (range Φ) := (isBounded_iff_subset_ball 0).2  Φ_isBounded'

lemma ey_isBounded' [Setting E₁ E₂ F admm admm_kkt]: ∃ (r : ℝ), (range ey) ⊆ ball 0 r := by
   rcases Φ_bd_above with ⟨r, Φ_isBounded⟩;
   use √(τ * ρ * r); intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n, eq⟩; rw [← eq]
   have hτ : τ > 0 := by rcases admm.htau with ⟨h₁, _⟩; exact h₁
   have hρ : ρ > 0 := by exact admm.hrho
   have τ_mul_ρ' : τ * ρ > 0 := by apply mul_pos hτ hρ
   have τ_mul_ρ : τ * ρ ≥ 0 := by apply le_of_lt (mul_pos hτ hρ)
   have open_Φ (n : ℕ) : τ * ρ * Φ n = ‖ey n‖^2 + τ * ρ * ρ * ‖A₂ (e₂ n)‖ ^ 2 + τ * ρ * ((max (1 - τ) (1 - 1 / τ)) * ρ ) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^2 := by
      simp [Φ, Ψ]; ring_nf; rw [mul_assoc, mul_assoc, mul_assoc]; nth_rw 2 [← mul_assoc] ; rw [mul_inv_cancel₀, one_mul]
      rw [← mul_assoc, mul_inv_cancel₀, one_mul]; ring; apply ne_of_gt hτ; apply ne_of_gt hρ
   have open_Φ' (n : ℕ) :  ‖ey n‖^2 + τ * ρ * ρ * ‖A₂ (e₂ n)‖ ^ 2 + τ * ρ * ((max (1 - τ) (1 - 1 / τ)) * ρ ) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^2
      = ‖ey n‖^2 + (τ * ρ * ρ * ‖A₂ (e₂ n)‖ ^ 2 + τ * ρ * ((max (1 - τ) (1 - 1 / τ)) * ρ ) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^2) := by ring_nf
   have nonneg1 (n : ℕ): τ * ρ * ρ * ‖A₂ (e₂ n)‖ ^ 2 ≥ 0 := by
      have : τ * ρ * ρ > 0 := by apply mul_pos τ_mul_ρ' hρ
      apply mul_nonneg (le_of_lt this)
      apply pow_two_nonneg
   have nonneg2 (n : ℕ): τ * ρ * ((max (1 - τ) (1 - 1 / τ)) * ρ ) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^2 ≥ 0 := by
      have h2 : ((max (1 - τ) (1 - 1 / τ)) * ρ ) ≥ 0 := by
         apply (mul_nonneg_iff_left_nonneg_of_pos hρ).2
         apply nonneg₃
      have h3 : τ * ρ * ((max (1 - τ) (1 - 1 / τ)) * ρ ) ≥ 0 := by apply mul_nonneg τ_mul_ρ h2
      apply mul_nonneg h3
      apply pow_two_nonneg
   have nonneg3 (n : ℕ): τ * ρ * ρ * ‖A₂ (e₂ n)‖ ^ 2 + τ * ρ * ((max (1 - τ) (1 - 1 / τ)) * ρ ) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^2 ≥ 0 := by
      apply add_nonneg (nonneg1 n) (nonneg2 n)
   have ey_norm (n : ℕ): ‖ey n‖ ^ 2 ≤ τ * ρ * Φ n := by
      rw [open_Φ, open_Φ']; linarith [nonneg3 n]
   have ey_norm_pow (n : ℕ) : ‖ey n‖ ^ 2 < τ * ρ * r := by
      have Φ_lt_r :  τ * ρ * Φ n < τ * ρ * r := by apply mul_lt_mul_of_pos_left (Φ_isBounded n) τ_mul_ρ'
      apply lt_of_le_of_lt (ey_norm n) Φ_lt_r
   have ey_norm_above (n : ℕ) : ‖ey n‖ < √(τ * ρ * r) := by
      have h_ey: √(‖ey n‖^2) = ‖ey n‖ := by rw [pow_two]; apply Real.sqrt_mul_self; apply norm_nonneg
      rw [← h_ey]
      have : ‖ey n‖^2 ≥ 0 := by apply pow_two_nonneg
      apply (Real.sqrt_lt_sqrt_iff this).mpr
      exact ey_norm_pow n
   exact ey_norm_above n


lemma ey_isBounded [Setting E₁ E₂ F admm admm_kkt]: IsBounded (range ey ) := (isBounded_iff_subset_ball 0).2  ey_isBounded'

lemma unfold_Φ [Setting E₁ E₂ F admm admm_kkt]: ∀ n, ‖Φ n‖ = ‖1 / (τ * ρ) * ‖ey n‖ ^ 2
+ ρ * ‖A₂ (e₂ n)‖ ^ 2
+ max (1 - τ) (1 - 1 / τ) * ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2‖ := by
   unfold Φ Ψ
   simp

lemma tau_pos : 0 < τ := by apply ADMM.htau.1

lemma rho_pos : 0 < ρ := by exact ADMM.hrho

lemma zero_le_tau_mul_rho : 0 ≤ τ * ρ := by
   have h : 0 < τ * ρ := by exact mul_pos tau_pos rho_pos
   apply le_of_lt h

lemma max_tau_nonneg [Setting E₁ E₂ F admm admm_kkt]: 0 ≤ max (1 - τ) (1 - 1 / τ) := by
   apply nonneg₃

lemma max_tau_mul_nonneg [Setting E₁ E₂ F admm admm_kkt]:∀ n, 0 ≤ max (1 - τ) (1 - 1 / τ) * ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2 :=by
   intro n
   apply mul_nonneg
   · apply mul_nonneg
      max_tau_nonneg; apply le_of_lt rho_pos
   · apply pow_nonneg; simp
lemma ineq1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n, ρ * ‖A₂ (e₂ n)‖ ^ 2 ≤ ‖Φ n‖ := by
   intro n
   let x1 := 1 / (τ*ρ) * ‖ey n‖ ^ 2
   have hx1: 0 ≤ x1 := by
      apply mul_nonneg
      · apply div_nonneg
         zero_le_one; exact zero_le_tau_mul_rho
      · apply pow_nonneg; simp
   let x2 := ρ * ‖A₂ (e₂ n)‖ ^ 2
   have hx2: 0 ≤ x2 := by
      apply mul_nonneg
      · apply le_of_lt rho_pos
      · apply pow_nonneg; simp
   let x3 := max (1 - τ) (1 - 1 / τ) * ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2
   have hx3: 0 ≤ x3 := by apply max_tau_mul_nonneg

   have h: ρ * ‖A₂ (e₂ n)‖ ^ 2 ≤ ‖Φ n‖ ↔ x2 ≤ ‖x1 + x2 + x3‖ := by rw[unfold_Φ]
   have h_norm_pos : 0 ≤ ‖x1 + x2 + x3‖ := by exact norm_nonneg (x1 + x2 + x3)
   have h_norm_eq : ‖x1 + x2 + x3‖ = x1 + x2 + x3 := by rw [Real.norm_of_nonneg];linarith [hx1, hx2, hx3]

   have htrans: x2 ≤ ‖x1 + x2 + x3‖ := by linarith [hx2, h_norm_pos]
   exact (h.mpr htrans)

lemma Φn_isBounded [Setting E₁ E₂ F admm admm_kkt]: ∃ r_Φ , ∀ n, ‖Φ n‖ < r_Φ := by
   have hΦ : ∃ r_Φ, range Φ ⊆ Metric.ball 0 r_Φ := by apply Φ_isBounded'
   rcases hΦ with ⟨r_Φ, hΦ⟩
   use r_Φ
   intro n
   have h0 : Φ n ∈ range Φ := by use n
   have h_in_ball : Φ n ∈ Metric.ball 0 r_Φ := by
      apply hΦ h0
   rw [Metric.mem_ball, dist_zero_right] at h_in_ball
   exact h_in_ball

lemma A₂e₂_isBounded' [Setting E₁ E₂ F admm admm_kkt]: ∃ (r : ℝ), (range (A₂ ∘ e₂) ) ⊆ ball 0 r := by

   rcases Φn_isBounded with ⟨r_Φ, h1⟩

   let r := √ (r_Φ / ρ)
   have hr : r = √ (r_Φ / ρ) := by rfl
   use r
   intros x hx
   rcases hx with ⟨n, rfl⟩

   have h2 : ρ * ‖A₂ (e₂ n)‖ ^ 2 ≤ ‖Φ n‖ := by apply ineq1

   have h3 : ρ * ‖A₂ (e₂ n)‖ ^ 2 < r_Φ := by
      calc
      ρ * ‖A₂ (e₂ n)‖ ^ 2 ≤ ‖Φ n‖ := h2
      _ < r_Φ := h1 n

   have h4 : 0 ≤ ‖A₂ (e₂ n)‖ := by
      apply norm_nonneg

   have h5: ‖A₂ (e₂ n)‖ < √ (r_Φ / ρ) := by
      calc ‖A₂ (e₂ n)‖
         = √ ((‖A₂ (e₂ n)‖) ^ 2) := by conv in ‖A₂ (e₂ n)‖ => rw [← Real.sqrt_sq h4];rfl
         _ < √ (r_Φ / ρ) := by
            rw [← lt_div_iff₀' ADMM.hrho] at h3
            apply Real.sqrt_lt_sqrt at h3
            exact h3; simp

   have h6: dist (A₂ (e₂ n)) 0 < √ (r_Φ / ρ) := by
      simpa [dist_eq_norm] using h5

   rw [← hr] at h6
   rw [← Metric.mem_ball] at h6
   apply h6

lemma A₂e₂_isBounded [Setting E₁ E₂ F admm admm_kkt]: IsBounded (range (A₂ ∘ e₂) ) :=
   (isBounded_iff_subset_ball 0).2 A₂e₂_isBounded'

lemma Φ_sub_nonneg [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , 0 ≤ (Φ n) - (Φ (n + 1)) := by
   intro n
   have h := big_is_ge_zero n
   apply le_trans
   · apply h
   · apply Φ_isdescending

lemma ineq2 [Setting E₁ E₂ F admm admm_kkt]: 0 < min 1 (1 + 1 / τ - τ ) * ρ := by apply mul_pos nonneg₂ ADMM.hrho

lemma A₁e₁_A₂e₂_isBounded'[Setting E₁ E₂ F admm admm_kkt] : ∃ (r : ℝ), (range (A₁ ∘ e₁ + A₂ ∘ e₂) ) ⊆ ball 0 r := by
   -- obtain r_Φ
   have hΦ : ∃ r_Φ, range Φ ⊆ Metric.ball 0 r_Φ := by apply Φ_isBounded'
   rcases hΦ with ⟨r_Φ, hΦ⟩

   -- h1 ~ h5 : n ≥ 1 (n : ℕ +)
   have h1 (k : ℕ+): (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖ ^ 2 ≤
   (min τ (1 + τ - τ ^ 2) )* ρ * ‖A₂ (x₂ k - x₂ (k + 1))‖ ^ 2 +
   (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖ ^ 2 := by
      have h1' : 0 ≤ (min τ (1 + τ - τ ^ 2) ) * ρ * ‖A₂ (x₂ k - x₂ (k + 1))‖ ^ 2 := by
         have ha: 0 < (min τ (1 + τ - τ ^ 2) ) * ρ := by
            apply mul_pos nonneg₁ ADMM.hrho
         have ha': 0 ≤ (min τ (1 + τ - τ ^ 2) ) * ρ := by apply le_of_lt ha
         have hb: 0 ≤ ‖A₂ (x₂ k - x₂ (k + 1))‖ ^ 2 := by apply sq_nonneg
         apply mul_nonneg ha' hb
      linarith

   have h2 (k : ℕ+): (min τ (1 + τ - τ ^ 2) ) * ρ * ‖A₂ (x₂ k - x₂ (k + 1))‖ ^ 2 + (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖ ^ 2 ≤ (Φ k) - (Φ (k + 1)) := by
      apply Φ_isdescending

   have h3 (k : ℕ+): (Φ k) - (Φ (k + 1)) < 2 * r_Φ := by
      have h3a: ‖Φ k‖ < r_Φ := by
         have h3a': Φ k ∈ range Φ := by use k
         have h_in_ball : Φ k ∈ Metric.ball 0 r_Φ := by apply hΦ h3a'
         rw [Metric.mem_ball, dist_zero_right] at h_in_ball
         exact h_in_ball
      have h3b: ‖Φ (k+1)‖ < r_Φ := by
         have h3b': Φ (k+1) ∈ range Φ := by use (k+1)
         have h_in_ball : Φ (k+1) ∈ Metric.ball 0 r_Φ := by apply hΦ h3b'
         rw [Metric.mem_ball, dist_zero_right] at h_in_ball
         exact h_in_ball
      have h3': ‖Φ k‖ + ‖Φ (k+1)‖ < r_Φ + r_Φ := by apply add_lt_add h3a h3b
      have h3'': ‖Φ k‖ + ‖Φ (k+1)‖ < 2 * r_Φ := by linarith [h3']
      have h3aa: ‖(Φ k) - (Φ (k + 1))‖ ≤ ‖Φ k‖ + ‖Φ (k+1)‖ := by apply norm_sub_le
      have h3bb: (Φ k) - (Φ (k + 1)) = ‖(Φ k) - (Φ (k + 1))‖ := by
         refine Eq.symm (Real.norm_of_nonneg ?hr); exact Φ_sub_nonneg k
      rw [h3bb]
      exact lt_of_le_of_lt h3aa h3''

   have h4 (k : ℕ+): ((min 1 (1 + 1 / τ - τ )) * ρ) * ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖ ^ 2 < 2 * r_Φ := by
      calc (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖ ^ 2
         _ ≤ (min τ (1 + τ - τ ^ 2) )* ρ * ‖A₂ (x₂ k - x₂ (k + 1))‖ ^ 2 + (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖ ^ 2 := h1 k
         _ ≤ (Φ k) - (Φ (k + 1)) := h2 k
         _ < 2 * r_Φ := h3 k

   have h5 (k : ℕ+): ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖ < √ (2 * r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ)) := by
      have h4_ins := h4 k
      have h5a: 0 ≤ ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖ := by apply norm_nonneg
      calc ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖
         _ = √ ((‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖) ^ 2) := by conv in ‖A₁ (e₁ (k + 1)) + A₂ (e₂ (k + 1))‖ => rw [← Real.sqrt_sq h5a];rfl
         _ < √ (2 * r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ)) := by
            rw [← lt_div_iff₀' ineq2] at h4_ins
            apply Real.sqrt_lt_sqrt at h4_ins
            exact h4_ins; simp

   have h5' (n : ℕ) (hn : 1 < n): ‖A₁ (e₁ n) + A₂ (e₂ n)‖ < √ (2 * r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ)) := by
      have h_pos : 0 < n - 1 := by exact Nat.zero_lt_sub_of_lt hn
      let k : ℕ+ := (n-1).toPNat h_pos
      have h_k := h5 k
      have k_to_n : k = n - 1 := by rfl
      rw [k_to_n] at h_k
      rw [Nat.sub_add_cancel] at h_k
      exact h_k
      apply le_of_lt hn

   have h_n0 : ‖A₁ (e₁ 0) + A₂ (e₂ 0)‖ < ‖A₁ (e₁ 0) + A₂ (e₂ 0)‖ + 1 := by linarith

   have h_n1 : ‖A₁ (e₁ 1) + A₂ (e₂ 1)‖ < ‖A₁ (e₁ 1) + A₂ (e₂ 1)‖ + 1 := by linarith

   let r := (max (max (√ (2 * r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ))) (‖A₁ (e₁ 0) + A₂ (e₂ 0)‖ + 1 )) (‖A₁ (e₁ 1) + A₂ (e₂ 1)‖ + 1 ))
   have hr' : r = (max (max (√ (2 * r_Φ / ((min 1 (1 + 1 / τ - τ )) * ρ))) (‖A₁ (e₁ 0) + A₂ (e₂ 0)‖ + 1 )) (‖A₁ (e₁ 1) + A₂ (e₂ 1)‖ + 1 )) := by rfl
   use r

   intros x hx
   rcases hx with ⟨n, rfl⟩

   -- combine h5' h_n0 h_n1 together
   have h_n (n : ℕ): ‖A₁ (e₁ n) + A₂ (e₂ n)‖ < r := by

      by_cases hn0 : n = 0
      rw [hn0]
      apply lt_of_lt_of_le h_n0
      rw [hr', max_assoc, max_left_comm]
      apply le_max_left

      by_cases hn1 : n = 1
      rw [hn1]
      apply lt_of_lt_of_le h_n1
      rw [hr']; apply le_max_right
      have hn : 1 < n := by
         exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
      apply lt_of_lt_of_le (h5' n hn)
      rw [hr']
      rw [max_assoc]; apply le_max_left

   have h6: dist (A₁ (e₁ n) + A₂ (e₂ n)) 0 < r := by
      have h_n' := h_n n
      simpa [dist_eq_norm] using h_n'

   rw [← Metric.mem_ball] at h6; simp; simp at h6
   exact h6

lemma A₁e₁_A₂e₂_isBounded [Setting E₁ E₂ F admm admm_kkt]: IsBounded (range (A₁ ∘ e₁ + A₂ ∘ e₂) ) :=
   (isBounded_iff_subset_ball 0).2 A₁e₁_A₂e₂_isBounded'

lemma A₁e₁_isBounded' [Setting E₁ E₂ F admm admm_kkt]: ∃ (r : ℝ), range (A₁ ∘ e₁) ⊆ ball 0 r := by

   have h_A₂e₂ : ∃ r1, range (A₂ ∘ e₂) ⊆ ball 0 r1 := by apply A₂e₂_isBounded'
   rcases h_A₂e₂ with ⟨r1, h_A₂e₂⟩

   have h_A₁e₁_A₂e₂ : ∃ r2, range (A₁ ∘ e₁ + A₂ ∘ e₂) ⊆ ball 0 r2 := by apply A₁e₁_A₂e₂_isBounded'
   rcases h_A₁e₁_A₂e₂ with ⟨r2, h_A₁e₁_A₂e₂⟩

   let r := r1 + r2
   have hr : r = r1 + r2 := by rfl
   use r

   intros x hx
   rcases hx with ⟨n, rfl⟩

   have h : ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ < r1 + r2 := by
      have ha : ‖A₂ (e₂ n)‖ < r1 := by
         have haa : A₂ (e₂ n) ∈ range (A₂ ∘ e₂) := by use n; simp
         have ha_in_ball : A₂ (e₂ n) ∈ Metric.ball 0 r1 := by apply h_A₂e₂ haa
         rw [Metric.mem_ball, dist_zero_right] at ha_in_ball
         exact ha_in_ball
      have hb : ‖A₁ (e₁ n) + A₂ (e₂ n)‖ < r2 := by
         have hbb : A₁ (e₁ n) + A₂ (e₂ n) ∈ range (A₁ ∘ e₁ + A₂ ∘ e₂) := by use n; simp
         have hb_in_ball : A₁ (e₁ n) + A₂ (e₂ n) ∈ Metric.ball 0 r2 := by apply h_A₁e₁_A₂e₂ hbb
         rw [Metric.mem_ball, dist_zero_right] at hb_in_ball
         exact hb_in_ball
      linarith

   have h_ineq : ‖A₁ (e₁ n)‖ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := by apply norm_le_add_norm_add

   have h_norm : ‖A₁ (e₁ n)‖ < r := by
      calc ‖A₁ (e₁ n)‖
         _ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := h_ineq
         _ < r1 + r2 := h
         _ = r := hr

   have h_dist : dist (A₁ (e₁ n)) 0 < r := by
      simpa [dist_eq_norm] using h_norm

   rw [← Metric.mem_ball] at h_dist
   apply h_dist

lemma A₁e₁_isBounded [Setting E₁ E₂ F admm admm_kkt]: IsBounded (range (A₁ ∘ e₁) ) :=
   (isBounded_iff_subset_ball 0).2 A₁e₁_isBounded'

lemma open_mapping_e₁ [Setting E₁ E₂ F admm admm_kkt] (fullrank₁: Function.Injective admm.A₁):
      ∃ C > 0, ∀ n : ℕ, ‖e₁ n‖ ≤ C * ‖A₁ (e₁ n)‖ := by
   rcases inv_bounded₂ A₁ fullrank₁ with ⟨C, ⟨C_pos,hh⟩⟩
   use C; constructor
   ·  exact C_pos
   ·  intro n; exact hh (e₁ n)

lemma open_mapping_e₂ [Setting E₁ E₂ F admm admm_kkt] (fullrank₂: Function.Injective admm.A₂):
      ∃ C > 0, ∀ n : ℕ, ‖e₂ n‖ ≤ C * ‖A₂ (e₂ n)‖ := by
   rcases inv_bounded₂ A₂ fullrank₂ with ⟨C, ⟨C_pos,hh⟩⟩
   use C; constructor
   ·  exact C_pos
   ·  intro n; exact hh (e₂ n)

lemma x₁_isBounded' [Setting E₁ E₂ F admm admm_kkt](fullrank₁: Function.Injective admm.A₁): ∃ (r : ℝ), (range x₁) ⊆ ball 0 r := by
   rcases A₁e₁_isBounded' with ⟨M, h₁⟩
   rcases open_mapping_e₁ fullrank₁ with ⟨C, ⟨C_pos, h₂⟩⟩
   rw [range] at h₁
   use C * M + ‖x₁'‖; intro x hx; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩
   have A₁e₁_bd : ‖A₁ (e₁ n)‖ < M := by
      have : A₁ (e₁ n) ∈ {x | ∃ n, A₁ (e₁ n) = x} := by simp
      have : A₁ (e₁ n) ∈ ball 0 M := by tauto
      simp at this; exact this
   rw [← eq]; simp
   calc
      _ = ‖(x₁ n - x₁') + x₁'‖ := by rw [add_comm, add_sub, add_comm, add_sub_assoc, sub_self, add_zero]
      _ ≤ ‖x₁ n - x₁'‖ + ‖x₁'‖ := by apply norm_add_le
      _ = ‖e₁ n‖ + ‖x₁'‖ := by rw [e₁]
      _ ≤ C * ‖A₁ (e₁ n)‖ + ‖x₁'‖ := by linarith [h₂ n]
      _ < C * M + ‖x₁'‖ := by linarith [mul_lt_mul_of_pos_left A₁e₁_bd C_pos]

lemma x₁_isBounded [Setting E₁ E₂ F admm admm_kkt](fullrank₁: Function.Injective admm.A₁):
      IsBounded (range x₁) :=
   (isBounded_iff_subset_ball 0).2 (x₁_isBounded' fullrank₁)

lemma x₂_isBounded' [Setting E₁ E₂ F admm admm_kkt] (fullrank₂: Function.Injective admm.A₂):
      ∃ (r : ℝ), (range x₂ ) ⊆ ball 0 r := by
   rcases A₂e₂_isBounded' with ⟨M, h₁⟩
   rcases open_mapping_e₂ fullrank₂ with ⟨C, ⟨C_pos, h₂⟩⟩
   rw [range] at h₁
   use C * M + ‖x₂'‖; intro x hx; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩
   have A₂e₂_bd : ‖A₂ (e₂ n)‖ < M := by
      have : A₂ (e₂ n) ∈ {x | ∃ n, A₂ (e₂ n) = x} := by simp
      have : A₂ (e₂ n) ∈ ball 0 M := by tauto
      simp at this; exact this
   rw [← eq]; simp
   calc
      _ = ‖(x₂ n - x₂') + x₂'‖ := by rw [add_comm, add_sub, add_comm, add_sub_assoc, sub_self, add_zero]
      _ ≤ ‖x₂ n - x₂'‖ + ‖x₂'‖ := by apply norm_add_le
      _ = ‖e₂ n‖ + ‖x₂'‖ := by rw [e₂]
      _ ≤ C * ‖A₂ (e₂ n)‖ + ‖x₂'‖ := by linarith [h₂ n]
      _ < C * M + ‖x₂'‖ := by linarith [mul_lt_mul_of_pos_left A₂e₂_bd C_pos]

lemma x₂_isBounded [Setting E₁ E₂ F admm admm_kkt] (fullrank₂: Function.Injective admm.A₂):
      IsBounded (range x₂) :=
   (isBounded_iff_subset_ball 0).2 (x₂_isBounded' fullrank₂)

lemma y_isBounded' [Setting E₁ E₂ F admm admm_kkt] :
      ∃ (r : ℝ), (range y) ⊆ ball 0 r := by
   rcases ey_isBounded' with ⟨M, h⟩
   use M + ‖y'‖; intro x hx; rw [range] at hx h; simp at hx; simp
   rcases hx with ⟨n,eq⟩; rw [← eq]
   have ey_bd : ‖ey n‖ < M := by
      have : ey n ∈ {x | ∃ n, ey n = x} := by simp
      have : ey n ∈ ball 0 M := by tauto
      simp at this; exact this
   calc
      _ = ‖(y n) - y' + y'‖ := by rw [add_comm, add_sub, add_comm, add_sub_assoc, sub_self, add_zero]
      _ ≤ ‖y n - y'‖ + ‖y'‖ := by apply norm_add_le
      _ = ‖ey n‖ + ‖y'‖ := by rw [ey]
      _ < M + ‖y'‖ := by linarith

lemma y_isBounded  [Setting E₁ E₂ F admm admm_kkt]:  IsBounded (range y) :=
   (isBounded_iff_subset_ball 0).2  y_isBounded'


lemma times_eq : (range (fun n => (x₁ n,  x₂ n, y n ) ))
⊆  (range x₁) ×ˢ  (range x₂) ×ˢ (range y) := by
   simp [range]
   intro x hx
   dsimp at hx
   simp only [mem_prod, mem_setOf_eq]
   rcases hx with ⟨n , hn⟩
   have h1 : x₁ n = x.1 := hn.symm ▸ rfl
   have h2 : x₂ n = x.2.1 := hn.symm ▸ rfl
   have h3 : y  n = x.2.2 := hn.symm ▸ rfl
   exact ⟨ ⟨ n , h1 ⟩, ⟨ n , h2 ⟩, ⟨ n , h3 ⟩⟩


lemma xy_isBounded [Setting E₁ E₂ F admm admm_kkt]
      (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂):
      IsBounded (range (fun n => (x₁ n,  x₂ n, y n ) )) := by
   apply IsBounded.subset
   apply IsBounded.prod (x₁_isBounded fullrank₁)
   apply IsBounded.prod (x₂_isBounded fullrank₂) y_isBounded
   apply times_eq

structure Converge_Subseq [Setting E₁ E₂ F admm admm_kkt] where
   x₁'' : E₁
   x₂'' : E₂
   y''  : F
   φ    : ℕ → ℕ
   hphi:StrictMono φ
   hconverge:Tendsto (fun n => (x₁ (φ n),  x₂ (φ n), y (φ n))) atTop (𝓝 (x₁'' , x₂'' , y''))

def Subseq [Setting E₁ E₂ F admm admm_kkt]
      (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂): Converge_Subseq := by
   let x := tendsto_subseq_of_bounded (xy_isBounded fullrank₁ fullrank₂)
      (inSet (fun n => (x₁ n,  x₂ n, y n )) )
   choose x hx using x
   choose φ hphi1 using hx.2
   exact
      {
         x₁'' := x.1
         x₂'' := x.2.1
         y''  := x.2.2
         φ   := φ
         hphi:= hphi1.1
         hconverge:=hphi1.2
      }

variable (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂)
-- Subsequence mapping
local notation "φ" => Converge_Subseq.φ (Subseq fullrank₁ fullrank₂)

-- The limit of the subsequence
local notation "x₁''" => Converge_Subseq.x₁'' (Subseq fullrank₁ fullrank₂)
local notation "x₂''" => Converge_Subseq.x₂'' (Subseq fullrank₁ fullrank₂)
local notation "y''"  => Converge_Subseq.y'' (Subseq fullrank₁ fullrank₂)

-- The subsequence mapping is strictly increasing
lemma hphi_StrictMono [Setting E₁ E₂ F admm admm_kkt] : StrictMono φ := (Subseq fullrank₁ fullrank₂).hphi

--lim_{n → ∞} (uₙ ,vₙ ) = 0 -> lim_{n → ∞} uₙ  = 0
lemma admm_nhds_prod_eq [Setting E₁ E₂ F admm admm_kkt] : 𝓝 (x₁'' , x₂'' , y'') = 𝓝 x₁'' ×ˢ 𝓝 x₂'' ×ˢ 𝓝 y'' := by
   rw[nhds_prod_eq,nhds_prod_eq]

lemma hconverge [Setting E₁ E₂ F admm admm_kkt]  : Tendsto (fun n => (x₁ (φ n),  x₂ (φ n), y (φ n)))
atTop (𝓝 x₁'' ×ˢ 𝓝 x₂'' ×ˢ 𝓝 y''):=by
   have := (Subseq fullrank₁ fullrank₂).hconverge
   rw[admm_nhds_prod_eq] at this
   exact this

lemma x₁_subseq_converge [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => (x₁ (φ n)))  atTop (𝓝 x₁'') :=
   (Filter.tendsto_prod_iff'.1 (hconverge fullrank₁ fullrank₂)).1

lemma x₂_subseq_converge [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => (x₂ (φ n)))  atTop (𝓝 x₂'') :=
   (Filter.tendsto_prod_iff'.1 (Filter.tendsto_prod_iff'.1 (hconverge fullrank₁ fullrank₂)).2).1

lemma y_subseq_converge  [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => (y (φ n)))  atTop (𝓝 y'') :=
   (Filter.tendsto_prod_iff'.1 (Filter.tendsto_prod_iff'.1 (hconverge fullrank₁ fullrank₂)).2).2

def φ₁' [Setting E₁ E₂ F admm admm_kkt] : ℕ → ℕ+ := by
   intro n
   exact (φ (n + 1)).toPNat'

local notation "φ₁" => φ₁' fullrank₁ fullrank₂

lemma φ₁_equ [Setting E₁ E₂ F admm admm_kkt] [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ , φ₁ n = φ (n + 1) := by
   intro n
   have : φ (n + 1) > 0 := by
      calc φ (n + 1)
         _ ≥ n + 1  := StrictMono.id_le (hphi_StrictMono fullrank₁ fullrank₂) (n + 1)
         _ > 0      :=by linarith
   exact Nat.sub_one_add_one_eq_of_pos this

-- lim_{ n → ∞} x_n  = x =>  lim_{ n → ∞} x_{n+1}  = x
lemma x₁_subseq_converge' [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => (x₁ (φ₁ n)))  atTop (𝓝 x₁'') :=by
   have : (fun n => x₁ (φ₁ n)) = (fun n => (x₁ (φ (n+1)))) :=by
      ext n;rw[φ₁_equ fullrank₁ fullrank₂ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ x₁ (φ n)) ) 1]
   apply x₁_subseq_converge

lemma x₂_subseq_converge' [Setting E₁ E₂ F admm admm_kkt]  : Tendsto (fun n => (x₂ (φ₁ n)))  atTop (𝓝 x₂'') :=by
   have : (fun n => x₂ (φ₁ n)) = (fun n => (x₂ (φ (n+1)))) :=by
      ext n;rw[φ₁_equ fullrank₁ fullrank₂ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ x₂ (φ n)) ) 1]
   apply x₂_subseq_converge

lemma Φ_Summable₁' [Setting E₁ E₂ F admm admm_kkt] :
      ∃ (c : ℝ) , ∀ (n : ℕ), ∑ i ∈ Finset.range n, ((Φ i.succ ) - (Φ (i.succ + 1))) ≤ c := by
   rcases Φn_isBounded with ⟨r , hr⟩
   use r + r
   intro n
   let φ₀ := (fun i : ℕ => Φ i.succ)
   have : ∀ i ∈ Finset.range n , (φ₀ i)-(φ₀ (i+1)) = (Φ i.succ ) - (Φ (i.succ + 1)) := by
      intro i hi
      rfl
   have h : Finset.range n =Finset.range n := rfl
   rw[← Finset.sum_congr h this , Finset.sum_range_sub']
   simp only [φ₀]
   calc Φ (Nat.succ 0) - Φ n.succ
      _ ≤ |Φ (Nat.succ 0) - Φ n.succ|:=by apply le_abs_self
      _ ≤ |Φ (Nat.succ 0)| + |Φ n.succ|:= by apply abs_sub
      _ ≤ r + r := by
         apply le_of_lt
         apply add_lt_add (hr (Nat.succ 0)) (hr (Nat.succ n))

lemma Φ_isSummable [Setting E₁ E₂ F admm admm_kkt] : Summable (fun n : ℕ => (Φ (n+1) ) - (Φ (n+1 + 1))) := by
   rcases Φ_Summable₁'  with ⟨c , hn⟩
   apply summable_of_sum_range_le (c:=c)
   intro n
   have :n + 1 > 0 := by linarith
   apply Φ_sub_nonneg (n + 1).toPNat'
   exact hn

theorem summable_of_nonneg_of_le {β : Type*} {f : β → ℝ} {g : β → ℝ}
(hg : ∀ (n : β), 0 ≤ g n) (hgf : ∀ (n : β), g n ≤ f n) (hf : Summable f) :
Summable g:=by
  exact Summable.of_nonneg_of_le hg hgf hf

lemma Φ_inequ₁ [Setting E₁ E₂ F admm admm_kkt] (m : ℕ+):
      (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (m+1)) + A₂ (e₂ (m+1))‖ ^ 2 ≤ Φ m - Φ (m + 1) := by
   calc (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (m+1)) + A₂ (e₂ (m+1))‖ ^ 2
      _≤ (min τ (1 + τ - τ ^ 2) )* ρ * ‖A₂ ((x₂ m )- x₂ (m + 1))‖ ^ 2
       + (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (m + 1)) + A₂ (e₂ (m + 1))‖ ^ 2:=by
         simp only [one_div, le_add_iff_nonneg_left]
         exact Φ₁_nonneg m
      _≤ Φ m - Φ (m + 1) := by apply Φ_isdescending

lemma Summable₁' [Setting E₁ E₂ F admm admm_kkt] :
      ∀ (n : ℕ), (fun n => (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (n+2)) + A₂ (e₂ (n+2))‖^2)  n
      ≤ (fun n : ℕ => (Φ (n+1) ) - (Φ (n+1 + 1))) n :=by
   intro n
   simp only
   let m := (n+1).toPNat'
   show (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (m+1)) + A₂ (e₂ (m+1))‖ ^ 2 ≤ Φ m - Φ (m + 1)
   apply Φ_inequ₁

lemma Summable₁ [Setting E₁ E₂ F admm admm_kkt] : Summable (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖^2) :=by
   let φn := fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2
   let φnsucc := fun n => (φn (n+2))
   show Summable φn
   rw[← summable_nat_add_iff 2]
   show Summable (fun n => φnsucc n)
   have φn_ge_zero': ∀ n , (min 1 (1 + 1 / τ - τ )) * ρ * φnsucc n ≥ 0 :=by
      intro n
      apply Φ₂_nonneg (n+1).toPNat'
   have h : (min 1 (1 + 1 / τ - τ )) * ρ ≠ 0 := by
      linarith [mul_pos nonneg₂ admm.hrho]
   rw[← summable_mul_left_iff h]
   apply summable_of_nonneg_of_le φn_ge_zero' Summable₁'
   apply Φ_isSummable

lemma  Φ_inequ₂ [Setting E₁ E₂ F admm admm_kkt] (m : ℕ+) :
      (min τ (1 + τ - τ ^ 2)) * ρ * ‖A₂ (x₂ (m + 1) - x₂ m)‖^2 ≤ Φ m - Φ (m + 1) := by
   calc (min τ (1 + τ - τ ^ 2)) * ρ * ‖A₂ (x₂ (m + 1) - x₂ m)‖^2
      _≤ (min τ (1 + τ - τ ^ 2) )* ρ * ‖A₂ ((x₂ m )- x₂ (m + 1))‖ ^ 2
       + (min 1 (1 + 1 / τ - τ )) * ρ * ‖A₁ (e₁ (m + 1)) + A₂ (e₂ (m + 1))‖ ^ 2:=by
         rw[norm_comm A₂ (x₂ (m + 1)) (x₂ m)]
         simp only [map_sub, le_add_iff_nonneg_right]
         exact Φ₂_nonneg m
      _≤ Φ m - Φ (m + 1) := by apply Φ_isdescending

lemma Summable₂' [Setting E₁ E₂ F admm admm_kkt] :
      ∀ (n : ℕ), (fun n =>(min τ (1 + τ - τ ^ 2)) * ρ * ‖A₂ (x₂ (n + 1+ 1) - x₂ (n+1))‖^2) n
      ≤ (fun n : ℕ => (Φ (n+1) ) - (Φ (n+1 + 1))) n :=by
   intro n
   simp only
   let m := (n+1).toPNat'
   show (min τ (1 + τ - τ ^ 2)) * ρ * ‖A₂ (x₂ (m + 1) - x₂ m)‖^2 ≤ Φ m - Φ (m + 1)
   apply Φ_inequ₂

-- variable [Setting E₁ E₂ F admm admm_kkt]
lemma Summable₂ [Setting E₁ E₂ F admm admm_kkt]: Summable (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖^2) :=by
   let φn := fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖^2
   let φnsucc := fun n => (φn (n+1))
   show Summable φn
   rw[← summable_nat_add_iff 1]
   show Summable (fun n => φnsucc n)
   have φn_ge_zero : ∀ n ,(min τ (1 + τ - τ ^ 2) )* ρ * φnsucc n ≥ 0 :=by
      intro n
      simp only [φnsucc , φn]
      rw[norm_comm A₂ (x₂ (n + 1 + 1)) (x₂ (n + 1))]
      apply Φ₁_nonneg (n+1).toPNat'
   have h : (min τ (1 + τ - τ ^ 2)) * ρ ≠ 0 := by
      linarith [mul_pos nonneg₁ admm.hrho]
   rw[← summable_mul_left_iff h]
   apply summable_of_nonneg_of_le φn_ge_zero Summable₂'
   apply Φ_isSummable

lemma y_subseq_converge' [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => (y (φ₁ n))) atTop (𝓝 y'') := by
   have : (fun n => y (φ₁ n)) = (fun n => (y (φ (n+1)))) := by
      ext n; rw [φ₁_equ fullrank₁ fullrank₂ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ y (φ n)) ) 1]
   apply y_subseq_converge

lemma square_converge_zero₁ [Setting E₁ E₂ F admm admm_kkt]  (h : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2)  atTop (𝓝 0)) :
   Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₁ (e₁ n) + A₂ (e₂ n)‖)^2))  atTop (𝓝 √0) := by apply Filter.Tendsto.sqrt h
   rw [Real.sqrt_zero] at this; simp at this; exact this

-- ‖A₁ (e₁ n) + A₂ (e₂ n)‖ → 0
lemma converge_zero₁ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2)  atTop (𝓝 0) := by apply Summable.tendsto_atTop_zero Summable₁
   apply square_converge_zero₁ this

-- ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ → 0
lemma converge_zero₂ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖)  atTop (𝓝 0) := by
   have eq : (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖) = (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖) := by
      funext n
      have : A₁ (e₁ n) + A₂ (e₂ n) = A₁ (x₁ n) + A₂ (x₂ n) - b := by
         rw [e₁, e₂]; simp
         calc
            _ = A₁ (x₁ n) + A₂ (x₂ n) - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_sub_comm]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b + b - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_cancel]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b := by rw [Satisfaction_ofthekkt.eq]; simp
      rw [this]
   rw [← eq]
   exact converge_zero₁

-- with the square norm of A₂ (x₂ (n + 1) - x₂ n) → 0, we can infer that the norm of A₂ (x₂ (n + 1) - x₂ n) also → 0
lemma square_converge_zero₃ [Setting E₁ E₂ F admm admm_kkt] (h : Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖ ^ 2)  atTop (𝓝 0)) :
   Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₂ (x₂ (n + 1) - x₂ n)‖)^2))  atTop (𝓝 √0) := by apply Filter.Tendsto.sqrt h
   rw [Real.sqrt_zero] at this; simp [Real.sqrt_sq] at this; simp; exact this

-- the norm of A₂ (x₂ (n + 1) - x₂ n) → 0
lemma converge_zero₃ [Setting E₁ E₂ F admm admm_kkt]  : Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖ ^ 2)  atTop (𝓝 0) := by
      apply Summable.tendsto_atTop_zero Summable₂
   apply square_converge_zero₃ this

-- A₁ (e₁ n) + A₂ (e₂ n) → 0 (Note that this lemma is without the norm)
lemma Seq_converge_zero₁ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => A₁ (e₁ n) + A₂ (e₂ n))  atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2 converge_zero₁

-- A₁ (x₁ n) + A₂ (x₂ n) - b → 0
lemma Seq_converge_zero₂ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => A₁ (x₁ n) + A₂ (x₂ n) - b)  atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2 converge_zero₂

-- A₂ (x₂ (n + 1) - x₂ n) → 0
lemma Seq_converge_zero₃ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => A₂ (x₂ (n + 1) - x₂ n))  atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2 converge_zero₃

-- A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n)) → 0
lemma sub_Seq_converge_zero₁ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n)))
atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 Seq_converge_zero₁
   apply StrictMono.tendsto_atTop
   have : (fun n => (Int.toNat (φ₁ n))) = (fun n => (φ (n+1))) := by
      ext n; rw [φ₁_equ fullrank₁ fullrank₂ n]; simp
   simp at this; rw [this]
   apply StrictMono.comp
   · apply hphi_StrictMono
   · simp [StrictMono]

-- A₁ (x₁ (φ₁ n)) + A₂ (x₂ (φ₁ n)) - b → 0
lemma sub_Seq_converge_zero₂ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => A₁ (x₁ (φ₁ n)) + A₂ (x₂ (φ₁ n)) - b) atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 Seq_converge_zero₂
   apply StrictMono.tendsto_atTop
   have : (fun n => (Int.toNat (φ₁ n))) = (fun n => (φ (n+1))) := by
      ext n; rw [φ₁_equ fullrank₁ fullrank₂ n]; simp
   simp at this; rw [this]
   apply StrictMono.comp
   · apply hphi_StrictMono
   · simp [StrictMono]

-- A₂ (x₂ ((φ₁ n) + 1) - x₂ (φ₁ n)) → 0
lemma sub_Seq_converge_zero₃ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => A₂ (x₂ ((φ₁ n) + 1) - x₂ (φ₁ n))) atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 Seq_converge_zero₃
   apply StrictMono.tendsto_atTop
   have : (fun n => (Int.toNat (φ₁ n))) = (fun n => (φ (n+1))) := by
      ext n; rw [φ₁_equ fullrank₁ fullrank₂ n]; simp
   simp at this; rw [this]
   apply StrictMono.comp
   · apply hphi_StrictMono
   · simp [StrictMono]

-- The difference between this lemma and the one above is the change of sub-script.
-- A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1)) → 0
lemma sub_Seq_converge_zero₃' [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1))) atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 Seq_converge_zero₃
   apply StrictMono.tendsto_atTop
   simp; rw [StrictMono]; intro n₁ n₂ h
   have h₁: φ (n₁ + 1) < φ (n₂ + 1) := by apply hphi_StrictMono; linarith
   have hn₁: φ (n₁ + 1) ≥ 1 := by
      calc
         _ ≥ n₁ + 1 := by apply StrictMono.id_le (hphi_StrictMono fullrank₁ fullrank₂)
         _ ≥ 1 := by linarith
   apply Nat.sub_lt_sub_right hn₁ h₁

-- (( 1 - τ) * ρ ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))) → 0
lemma const_smul_subseq₁ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => (( 1 - τ) * ρ ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n)))) atTop (𝓝 0) := by
   rw [← smul_zero (( 1 - τ) * ρ )]
   apply Filter.Tendsto.const_smul (sub_Seq_converge_zero₁ fullrank₁ fullrank₂) (( 1 - τ) * ρ)

-- ρ • A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n)) → 0
lemma const_smul_subseq₂ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => ρ • A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n))) atTop (𝓝 0) := by
   have : (fun n => ρ • A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n))) = (fun n => (-ρ) • A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1))) := by
      ext n
      calc
         _ = ρ • (-1) • A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1)) := by simp
         _ = (-ρ) • A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1)) := by
            rw [smul_comm, neg_one_smul]; simp
   rw [this, ← smul_zero (-ρ)]
   apply Filter.Tendsto.const_smul (sub_Seq_converge_zero₃' fullrank₁ fullrank₂)

-- u (φ₁ n) converges to (- A₁† y'')
lemma u_subseq_converge [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => u (φ₁ n)) atTop (𝓝 (- A₁† y'')) := by
   have : (fun n => u (φ₁ n)) = (fun n => - A₁† ((y (φ₁ n)) + (( 1 - τ) * ρ ) • (A₁ (e₁ (φ₁ n))
         + A₂ (e₂ (φ₁ n))) + ρ • (A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n))))) := by
      funext n; rw [u]
   rw [this]
   have : Tendsto (fun n => (y (φ₁ n)) + (( 1 - τ) * ρ ) • (A₁ (e₁ (φ₁ n))
         + A₂ (e₂ (φ₁ n)))) atTop (𝓝 y'') := by
      rw [← add_zero y'']
      apply Filter.Tendsto.add (y_subseq_converge' fullrank₁ fullrank₂) (const_smul_subseq₁ fullrank₁ fullrank₂)
   have h: Tendsto (fun n => (y (φ₁ n)) + (( 1 - τ) * ρ ) • (A₁ (e₁ (φ₁ n))
         + A₂ (e₂ (φ₁ n))) + ρ • (A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n)))) atTop (𝓝 y'') := by
      rw [← add_zero y'']
      apply Filter.Tendsto.add (this) (const_smul_subseq₂ fullrank₁ fullrank₂)
   have : Tendsto (- A₁†) (𝓝 y'') (𝓝 (- A₁† y'')) := by apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   apply Filter.tendsto_iff_seq_tendsto.1 this; apply h

-- v (φ₁ n) converges to (- A₂† y'')
lemma v_subseq_converge [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => v (φ₁ n)) atTop (𝓝 (- A₂† y'')) := by
   have : (fun n => v (φ₁ n)) = (fun n => - A₂† (y (φ₁ n) + (( 1 - τ) * ρ ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))))) := by
      funext n; rw [v]
   rw [this]
   have h: Tendsto (fun n => (y (φ₁ n) + (( 1 - τ) * ρ ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))))) atTop (𝓝  y'') := by
      rw [← add_zero y'']
      apply Filter.Tendsto.add (y_subseq_converge' fullrank₁ fullrank₂) (const_smul_subseq₁ fullrank₁ fullrank₂)
   have : Tendsto (- A₂†) (𝓝 y'') (𝓝 (- A₂† y'')) := by apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   apply Filter.tendsto_iff_seq_tendsto.1 this; apply h

-- (nonempty : ∀ (n : ℕ), g n ∈ SubderivAt f (x n)) (lscf : LowerSemicontinuous f)
-- (x_converge : Tendsto x atTop (𝓝 x')) (g_converge : Tendsto g atTop (𝓝 g'))

lemma A₁'y_inthesubgradient [Setting E₁ E₂ F admm admm_kkt] : - A₁† y'' ∈ SubderivAt f₁ x₁'':=
   Image_subgradient_closed (fun n ↦ u_inthesubgradient (φ₁ n)) admm.lscf₁
   (x₁_subseq_converge' fullrank₁ fullrank₂) (u_subseq_converge   fullrank₁ fullrank₂)

lemma A₂'y_inthesubgradient [Setting E₁ E₂ F admm admm_kkt]  : - A₂† y'' ∈ SubderivAt f₂ x₂'':=
   Image_subgradient_closed (fun n => v_inthesubgradient (φ₁ n)) admm.lscf₂
   (x₂_subseq_converge' fullrank₁ fullrank₂) (v_subseq_converge   fullrank₁ fullrank₂)

-- lim ‖ x_n ‖ = ‖ lim x_n ‖
lemma Satisfying_equational_constraint1' [Setting E₁ E₂ F admm admm_kkt] : Tendsto A₁ (𝓝 x₁'') (𝓝 (A₁ x₁'')) := by
   apply Continuous.tendsto
   apply ContinuousLinearMap.continuous

lemma Satisfying_equational_constraint1 [Setting E₁ E₂ F admm admm_kkt] :
Tendsto (fun n => A₁ (x₁ (φ n))) atTop (𝓝 (A₁ x₁'')) := by
   apply tendsto_iff_seq_tendsto.1 (Satisfying_equational_constraint1' fullrank₁ fullrank₂) (x₁ ∘ φ)
   apply tendsto_iff_seq_tendsto.1 (x₁_subseq_converge fullrank₁ fullrank₂)
   apply StrictMono.tendsto_atTop
   apply strictMono_id

lemma Satisfying_equational_constraint2' [Setting E₁ E₂ F admm admm_kkt] : Tendsto A₂ (𝓝 x₂'') (𝓝 (A₂ x₂'')) := by
   apply Continuous.tendsto
   apply ContinuousLinearMap.continuous

lemma Satisfying_equational_constraint2 [Setting E₁ E₂ F admm admm_kkt] :
Tendsto (fun n => A₂ (x₂ (φ n))) atTop (𝓝 (A₂ x₂'')) := by
   apply tendsto_iff_seq_tendsto.1 (Satisfying_equational_constraint2' fullrank₁ fullrank₂) (x₂ ∘ φ)
   apply tendsto_iff_seq_tendsto.1 (x₂_subseq_converge fullrank₁ fullrank₂)
   apply StrictMono.tendsto_atTop
   apply strictMono_id

lemma Satisfying_equational_constraint' [Setting E₁ E₂ F admm admm_kkt] :
Tendsto (fun n => ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖) atTop (𝓝 ‖(A₁ x₁'') + (A₂ x₂'') - admm.b‖)
:= by
   apply Tendsto.norm
   apply Tendsto.sub_const
   apply Tendsto.add
   apply Satisfying_equational_constraint1
   apply Satisfying_equational_constraint2

lemma subconverge_zero₂ [Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n =>  ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖)  atTop (𝓝 0)
:= by
   apply tendsto_iff_seq_tendsto.1 converge_zero₂
   apply StrictMono.tendsto_atTop
   apply hphi_StrictMono

lemma Satisfying_equational_constraint_norm [Setting E₁ E₂ F admm admm_kkt] :
      ‖(A₁ x₁'') + (A₂ x₂'') - admm.b‖ = 0 := by
   apply tendsto_nhds_unique (Satisfying_equational_constraint' fullrank₁ fullrank₂)
   apply subconverge_zero₂

lemma Satisfying_equational_constraint [Setting E₁ E₂ F admm admm_kkt] :
      (A₁ x₁'') + (A₂ x₂'') = admm.b := by
   have h1 := Satisfying_equational_constraint_norm fullrank₁ fullrank₂
   apply norm_eq_zero.1 at h1
   apply eq_of_sub_eq_zero h1

lemma Iskktpair [Setting E₁ E₂ F admm admm_kkt] : Convex_KKT x₁'' x₂'' y'' admm.toOptProblem :=
   {
      subgrad₁ :=A₁'y_inthesubgradient fullrank₁ fullrank₂
      subgrad₂ :=A₂'y_inthesubgradient fullrank₁ fullrank₂
      eq       :=Satisfying_equational_constraint fullrank₁ fullrank₂
   }

end

variable (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂)
-- Subsequence mapping
local notation "φ" => Converge_Subseq.φ (Subseq fullrank₁ fullrank₂)

-- The point of the subsequence convergence
local notation "x₁''" => Converge_Subseq.x₁'' (Subseq fullrank₁ fullrank₂)
local notation "x₂''" => Converge_Subseq.x₂'' (Subseq fullrank₁ fullrank₂)
local notation "y''"  => Converge_Subseq.y'' (Subseq fullrank₁ fullrank₂)

def admm_kkt₁ [_s : Setting E₁ E₂ F admm admm_kkt] :  Existance_of_kkt admm :=
   Existance_of_kkt.mk x₁''  x₂''  y'' (Iskktpair fullrank₁ fullrank₂)

-- e₁ (φ n) → 0
-- x₁ (φ n) → (admm_kkt₁ fullrank₁ fullrank₂).x₁ = x₁''
lemma e₁_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (e₁ ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (x₁ ∘ φ) n - x₁'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply x₁_subseq_converge
   have h₂: (fun n => (x₁ ∘ φ) n - x₁'') = (fun n => e₁ (φ n)) := by
      funext n; rw [e₁]; simp; simp [admm_kkt₁]; rfl
   rw [h₂] at h₁; apply h₁

-- e₂ (φ n) → 0
-- x₂ (φ n) → (admm_kkt₁ fullrank₁ fullrank₂).x₂ = x₂''
lemma e₂_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (e₂ ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (x₂ ∘ φ) n - x₂'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply x₂_subseq_converge
   have h₂: (fun n => (x₂ ∘ φ) n - x₂'') = (fun n => e₂ (φ n)) := by
      funext n; rw [e₂]; simp; simp [admm_kkt₁]; rfl
   rw [h₂] at h₁; apply h₁

-- e₂ (φ n) → 0
-- y (φ n) → (admm_kkt₁ fullrank₁ fullrank₂).y = y''
lemma ey_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (ey ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (y ∘ φ) n - y'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply y_subseq_converge
   have h₂: (fun n => (y ∘ φ) n - y'') = (fun n => ey (φ n)) := by
      funext n; rw [ey]; simp; simp [admm_kkt₁]; rfl
   rw [h₂] at h₁; apply h₁

-- ‖ey (φ n)‖ → 0
lemma nrm_ey_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖ey (φ n)‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply ey_subseq_converge_zero

-- ‖ey (φ n)‖^2 → 0
lemma sqnrm_ey_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖ey (φ n)‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_ey_subseq_converge_zero; linarith

-- (1 / (τ * ρ)) * ‖ey (φ n)‖^2 → 0
lemma const_sqnrm_ey_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => (1 / (τ * ρ)) * ‖ey (φ n)‖^2) atTop (𝓝 0) := by
   rw [← mul_zero]
   apply Filter.Tendsto.const_mul (1 / (τ * ρ)) (sqnrm_ey_subseq_converge_zero fullrank₁ fullrank₂)

-- A₁ (e₁ (φ n)) → 0
lemma A₁e₁_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => A₁ (e₁ (φ n))) atTop (𝓝 0) := by
   have h₁: Tendsto A₁ (𝓝 0) (𝓝 (A₁ 0)) := by
      apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   simp at h₁; apply Filter.tendsto_iff_seq_tendsto.1 h₁; apply e₁_subseq_converge_zero

-- A₂ (e₂ (φ n)) → 0
lemma A₂e₂_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => A₂ (e₂ (φ n))) atTop (𝓝 0) := by
   have h₁: Tendsto A₂ (𝓝 0) (𝓝 (A₂ 0)) := by
      apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   simp at h₁; apply Filter.tendsto_iff_seq_tendsto.1 h₁; apply e₂_subseq_converge_zero

-- ‖A₂ (e₂ (φ n))‖ → 0
lemma nrm_A₂e₂_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₂ (e₂ (φ n))‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply A₂e₂_subseq_converge_zero

-- ‖A₂ (e₂ (φ n))‖^2 → 0
lemma sqnrm_A₂e₂_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_A₂e₂_subseq_converge_zero; linarith

-- ρ * ‖A₂ (e₂ (φ n))‖^2 → 0
lemma const_sqnrm_A₂e₂_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ρ * ‖A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← mul_zero]
   apply Filter.Tendsto.const_mul ρ (sqnrm_A₂e₂_subseq_converge_zero fullrank₁ fullrank₂)

-- A₁ (e₁ (φ n)) + A₂ (e₂ (φ n)) → 0
lemma A₁e₁_A₂e₂_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))) atTop (𝓝 0) := by
   rw [← add_zero 0]
   apply Tendsto.add (A₁e₁_subseq_converge_zero fullrank₁ fullrank₂) (A₂e₂_subseq_converge_zero fullrank₁ fullrank₂)

-- ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖ → 0
lemma nrm_A₁e₁_A₂e₂_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply A₁e₁_A₂e₂_subseq_converge_zero

-- ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2 → 0
lemma sqnrm_A₁e₁_A₂e₂_subseq_converge_zero[Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_A₁e₁_A₂e₂_subseq_converge_zero; linarith

-- ((max (1-τ) (1-(1/τ)))*ρ) * ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2 → 0
lemma const_sqnrm_A₁e₁_A₂e₂_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ((max (1-τ) (1-(1/τ)))*ρ) * ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← mul_zero]
   apply Filter.Tendsto.const_mul ((max (1-τ) (1-(1/τ)))*ρ) (sqnrm_A₁e₁_A₂e₂_subseq_converge_zero fullrank₁ fullrank₂)

-- Φ (φ n) → 0
lemma Φ_subseq_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => Φ (φ n)) atTop (𝓝 0) := by
   have h_add: Tendsto (fun n => (1 / (τ * ρ)) * ‖ey (φ n)‖^2 + ρ * ‖A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
      rw [← zero_add 0]
      apply Tendsto.add (const_sqnrm_ey_subseq_converge_zero fullrank₁ fullrank₂) (const_sqnrm_A₂e₂_subseq_converge_zero fullrank₁ fullrank₂)
   have h_add': Tendsto (fun n => (1 / (τ * ρ)) * ‖ey (φ n)‖^2 + ρ * ‖A₂ (e₂ (φ n))‖^2 + ((max (1-τ) (1-(1/τ)))*ρ) * ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
      rw [← zero_add 0]
      apply Tendsto.add h_add (const_sqnrm_A₁e₁_A₂e₂_subseq_converge_zero fullrank₁ fullrank₂)
   have : (fun n => Φ (φ n)) = (fun n => (1 / (τ * ρ)) * ‖ey (φ n)‖^2 + ρ * ‖A₂ (e₂ (φ n))‖^2 + ((max (1-τ) (1-(1/τ)))*ρ) * ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2) := by
      funext n; rw [Φ, Ψ]
   rw [this]
   apply h_add'

lemma Φ_ge [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      ∀ n , 0 ≤ (fun _ : ℕ ↦ (⨅ i, (fun n ↦ Φ (n + 1)) i)) n := by
   intro n
   simp only
   apply Real.iInf_nonneg (f := (fun n ↦ Φ (n + 1)))
   intro i
   apply Φ_is_nonneg (i+1)

lemma Φ_bddbelow [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      BddBelow (range (fun n ↦ Φ (n + 1))) := by
   simp [BddBelow , lowerBounds]
   use 0
   simp only [mem_setOf_eq]
   intro a
   apply Φ_is_nonneg (a+1)

lemma Φ_le [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:∀ n : ℕ , (⨅ i, (fun n ↦ Φ (n + 1)) i) ≤ Φ (φ n.succ) := by
   intro n
   have := ciInf_le (Φ_bddbelow fullrank₁ fullrank₂) ((φ n.succ)-1)
   have h : φ n.succ > 0:= by
      calc _
         _ ≥ n + 1  := StrictMono.id_le (hphi_StrictMono fullrank₁ fullrank₂) (n + 1)
         _ > 0      :=by linarith
   have h2 : 1 ≤ φ n.succ := by linarith[h]
   have h1 : φ n.succ - 1 + 1 = φ n.succ := by apply Nat.sub_add_cancel h2
   rw[h1] at this
   exact this

lemma Φ_converge_zero''' [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
 Tendsto (fun _ : ℕ ↦ (⨅ i, (fun n ↦ Φ (n + 1)) i)) atTop (𝓝 0) := by
   apply squeeze_zero
   apply Φ_ge
   apply Φ_le
   have :=Φ_subseq_converge_zero fullrank₁ fullrank₂
   rw[← tendsto_add_atTop_iff_nat 1] at this
   exact this

lemma Φ_converge_zero'' [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
 Tendsto (fun _ : ℕ ↦ (⨅ i, (fun n ↦ Φ (n + 1)) i)) atTop (𝓝 (⨅ i, (fun n ↦ Φ (n + 1)) i)) := by
 apply tendsto_const_nhds

lemma Φ_converge_zero' [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      (⨅ i, (fun n ↦ Φ (n + 1)) i) = 0  := by
   apply tendsto_nhds_unique (Φ_converge_zero'' fullrank₁ fullrank₂)
   apply Φ_converge_zero'''

lemma Φ_isMono [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Antitone (fun n ↦ Φ (n + 1)) := by
   apply antitone_nat_of_succ_le
   intro n
   apply Φ_is_monotone (n+1).toPNat'

lemma Φ_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto Φ atTop (𝓝 0) := by
   rw[← tendsto_add_atTop_iff_nat 1]
   have := tendsto_atTop_ciInf (Φ_isMono fullrank₁ fullrank₂) (Φ_bddbelow fullrank₁ fullrank₂)
   rwa[← Φ_converge_zero']

lemma A₂e₂_le_Φ (n : ℕ) [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      ‖A₂ (e₂ n)‖ ^ 2 ≤ (1 / ρ) * Φ n := by
   have hτ : τ > 0 := by rcases admm.htau with ⟨h₁, _⟩; exact h₁
   have hτ' : τ ≥ 0 := by apply le_of_lt hτ
   have h1 (n : ℕ) : (1 / ρ) * Φ n = ρ⁻¹ * Φ n := by simp only [one_div]
   have open_Φ (n : ℕ) : ρ⁻¹ * Φ n = ((ρ⁻¹) ^ 2) * τ⁻¹ * ‖ey n‖^2 + ‖A₂ (e₂ n)‖ ^ 2 + (max (1 - τ) (1 - 1 / τ)) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2 := by
      simp [Φ, Ψ]; ring_nf; rw [mul_inv_cancel₀, one_mul, one_mul]; ring_nf; apply ne_of_gt (admm.hrho)
   have open_Φ' (n : ℕ) : ((ρ⁻¹) ^ 2) * τ⁻¹ * ‖ey n‖^2 + ‖A₂ (e₂ n)‖ ^ 2 + (max (1 - τ) (1 - 1 / τ)) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2 = ‖A₂ (e₂ n)‖ ^ 2 + (((ρ⁻¹) ^ 2) * τ⁻¹ * ‖ey n‖^2 + (max (1 - τ) (1 - 1 / τ)) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2) := by
      ring_nf
   have nonneg1 (n : ℕ) : ((ρ⁻¹) ^ 2) * τ⁻¹ * ‖ey n‖^2 ≥ 0 := by
      have h₁ : (ρ⁻¹) ^ 2 ≥ 0 := by apply pow_two_nonneg
      have h₂ : τ⁻¹ ≥ 0 := by apply inv_nonneg.mpr hτ'
      have h₃ : ‖ey n‖^2 ≥ 0 := by apply pow_two_nonneg
      apply mul_nonneg (mul_nonneg h₁ h₂) h₃
   have nonneg2 (n : ℕ) : (max (1 - τ) (1 - 1 / τ)) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2 ≥ 0:= by
      have h3 : (max (1 - τ) (1 - 1 / τ)) ≥ 0 := by apply nonneg₃
      apply mul_nonneg h3
      apply pow_two_nonneg
   have nonneg3 (n : ℕ) : ((ρ⁻¹) ^ 2) * τ⁻¹ * ‖ey n‖^2 + (max (1 - τ) (1 - 1 / τ)) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2 ≥ 0 := by
      apply add_nonneg (nonneg1 n) (nonneg2 n)
   rw [h1, open_Φ, open_Φ']; linarith [nonneg3 n]

lemma A₂e₂_le_Φ' [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))](n : ℕ) :
      ‖‖A₂ (e₂ n)‖ ^ 2‖ ≤ (1 / ρ) * Φ n := by
   have : ‖‖A₂ (e₂ n)‖ ^ 2‖ = ‖A₂ (e₂ n)‖ ^ 2 := by simp only [norm_pow, norm_norm]
   rw [this]
   apply A₂e₂_le_Φ

lemma A₂e₂_pow_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₂ (e₂ n)‖^2) atTop (𝓝 0) := by
   apply squeeze_zero_norm; apply A₂e₂_le_Φ'
   have h1 : Tendsto (fun n ↦ (1 / ρ) * Φ n) atTop (𝓝 (1 / ρ * 0)) := by
      apply Filter.Tendsto.const_mul (1 / ρ) (Φ_converge_zero fullrank₁ fullrank₂)
   have h2 : Tendsto (fun n ↦ (1 / ρ) * Φ n) atTop (𝓝 0) := by
      have : 1 / ρ * 0 = 0 := by norm_num
      rw [← this]
      exact h1
   assumption

lemma A₂e₂_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₂ (e₂ n)‖)^2))  atTop (𝓝 √0) := by
      apply Tendsto.sqrt (A₂e₂_pow_converge_zero fullrank₁ fullrank₂)
   rw [Real.sqrt_zero] at this; simp [Real.sqrt_sq] at this; exact this

lemma A₁e₁_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by
   have h (n : ℕ) : ‖A₁ (e₁ n)‖ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := by
      let x := A₁ (e₁ n)
      let xx := A₂ (e₂ n)
      have h1 : ‖x‖ = ‖x + xx - xx‖ := by rw [← add_sub, sub_self, add_zero]
      have h2 : ‖x + xx - xx‖ ≤ ‖x + xx‖ + ‖xx‖ := by apply norm_sub_le
      rw [← h1] at h2
      linarith
   have h' (n : ℕ) : ‖‖A₁ (e₁ n)‖‖ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := by
      have : ‖‖A₁ (e₁ n)‖‖ = ‖A₁ (e₁ n)‖ := by simp only [norm_norm]
      rw [this]
      exact h n
   have h'' : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖) atTop (𝓝 (0 + 0)) := by
      apply Tendsto.add (converge_zero₁) (A₂e₂_converge_zero fullrank₁ fullrank₂)
   have h''' : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
      have : (0 : ℝ) = 0 + 0 := by norm_num
      rw [this]
      exact h''
   apply squeeze_zero_norm
   apply h'
   exact h'''

lemma A₁e₁_converge_zero' [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖(A₁ ∘ e₁) n‖) atTop (𝓝 0) := by
   have : (fun n => ‖A₁ (e₁ n)‖) = (fun n => ‖(A₁ ∘ e₁) n‖) := by simp only [Function.comp_apply]
   rw [← this]
   apply A₁e₁_converge_zero

lemma CA₁e₁_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))](C : ℝ) :
      Tendsto (fun n => C * ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by apply A₁e₁_converge_zero
   have h : C * 0 = 0 := by simp only [mul_zero]
   rw[← h]; apply Tendsto.const_mul C this

lemma CA₂e₂_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))](C : ℝ) :
      Tendsto (fun n => C * ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by apply A₂e₂_converge_zero
   have h : C * 0 = 0 := by simp only [mul_zero]
   rw[← h]; apply Tendsto.const_mul C this

lemma e₁_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto e₁ atTop (𝓝 0) := by
   have : ∃ C > 0, ∀ n : ℕ, ‖e₁ n‖ ≤ C * ‖A₁ (e₁ n)‖ := open_mapping_e₁ fullrank₁
   obtain ⟨C, _, hC⟩ := this
   apply squeeze_zero_norm; intro n; exact hC n; apply CA₁e₁_converge_zero

lemma e₂_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto e₂ atTop (𝓝 0) := by
   have : ∃ C > 0, ∀ n : ℕ, ‖e₂ n‖ ≤ C * ‖A₂ (e₂ n)‖ := open_mapping_e₂ fullrank₂
   obtain ⟨C, _, hC⟩ := this
   apply squeeze_zero_norm; intro n; exact hC n; apply CA₂e₂_converge_zero

lemma ey_le_Φ [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))](n : ℕ) :
      (1 / (τ * ρ)) * ‖ey n‖ ^ 2 ≤ Φ n := by
   dsimp [Φ, Ψ]
   have h : ρ * ‖A₂ (e₂ n)‖ ^ 2 ≥ 0 := by
      apply mul_nonneg
      linarith [admm.hrho]
      linarith [pow_two_nonneg (‖A₂ (e₂ n)‖)]
   have h' : max (1 - τ) (1 - 1 / τ) * ρ * ‖A₁ (e₁ n) + A₂ (e₂ n)‖ ^ 2 ≥ 0 := by
      apply mul_nonneg
      apply mul_nonneg
      linarith [nonneg₃, admm.hrho]
      linarith [admm.hrho]
      linarith [pow_two_nonneg (‖A₁ (e₁ n) + A₂ (e₂ n)‖)]
   linarith [h, h']

lemma ey_le_Φ' [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))] (n : ℕ) :
      ‖ey n‖ ^ 2 ≤ (τ * ρ) * Φ n := by
   have : (τ * ρ) * Φ n = Φ n * (τ * ρ) := by ring
   rw [this]
   have : (τ * ρ) > 0 := by apply mul_pos; linarith [admm.htau.1]; linarith [admm.hrho]
   apply (div_le_iff₀ this).mp
   calc
      _= (1 / (τ * ρ)) * ‖ey n‖ ^ 2 := by ring
      _≤ Φ n := by apply ey_le_Φ

lemma const_φ_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => (τ * ρ) * Φ n) atTop (𝓝 0) := by
   rw [← mul_zero (τ * ρ)]
   apply Filter.Tendsto.const_mul (τ * ρ) (Φ_converge_zero fullrank₁ fullrank₂)

lemma ey_sqnrm_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖ey n‖^2)  atTop (𝓝 0) := by
   apply squeeze_zero_norm
   have (n : ℕ) : ‖‖ey n‖ ^ 2‖ ≤ (τ * ρ) * Φ n := by simp [ey_le_Φ']
   apply this; apply const_φ_converge_zero

lemma ey_nrm_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖ey n‖)  atTop (𝓝 0) := by
   rw [← Real.sqrt_zero]
   have : (fun n => ‖ey n‖) = (fun n => √(‖ey n‖^2)) := by funext n; simp [Real.sqrt_sq]
   rw [this]
   apply Filter.Tendsto.sqrt (ey_sqnrm_converge_zero fullrank₁ fullrank₂)

lemma ey_converge_zero [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto ey atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2
   apply ey_nrm_converge_zero

--lim_{ n → ∞} x_n - x = 0 =>  lim_{ n → ∞} x_n  = x
lemma x₁_converge [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto x₁ atTop (𝓝 x₁'') := by
   have : e₁ = (fun n => (x₁ n) - x₁''):= rfl
   have h := e₁_converge_zero fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma x₂_converge [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto x₂ atTop (𝓝 x₂'') := by
   have : e₂ = (fun n => (x₂ n) - x₂''):= rfl
   have h := e₂_converge_zero fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma y_converge [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto y atTop (𝓝 y'') := by
   have : ey = (fun n => (y n) - y''):= rfl
   have h := ey_converge_zero fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

--ADMM收敛定理
theorem ADMM_convergence [Setting E₁ E₂ F admm (admm_kkt₁ fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      ∃ ( _x₁   : E₁) ( _x₂ : E₂) ( _y : F) , Convex_KKT _x₁ _x₂ _y admm.toOptProblem
      ∧ ( Tendsto x₁ atTop (𝓝 _x₁)∧ Tendsto x₂ atTop (𝓝 _x₂)∧ Tendsto y atTop (𝓝 _y)) :=
   ⟨x₁'',x₂'',y'',Iskktpair fullrank₁ fullrank₂ ,
   x₁_converge fullrank₁ fullrank₂ ,x₂_converge fullrank₁ fullrank₂,
   y_converge fullrank₁ fullrank₂⟩

end ADMM_Converge_Proof
