/-
Copyright (c) 2024 Zichen Wang, Yifan Bai, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Zichen Wang, Yifan Bai, Chenyi Li
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Optlib.Function.Proximal
import Optlib.Differential.Subdifferential

open Filter BigOperators Set Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {x : E}

def limsubdifferential_Graph (f : E → ℝ) :=
  {(x, fx, u) : E × ℝ × E| fx = f x ∧ u ∈ f_subdifferential f x}

def subdifferential_Graph (f : E → ℝ) :=
  {(x, u) : E × E| u ∈ subdifferential f x}

lemma subdifferential_Graph' (f : E → ℝ) :
    subdifferential_Graph f =
    {(x, u) : E × E| (x, f x, u) ∈ closure (limsubdifferential_Graph f)} := by
      ext y
      constructor
      · intro hy
        simp [subdifferential_Graph, subdifferential] at hy
        simp [mem_closure_iff_seq_limit, limsubdifferential_Graph]
        rcases hy with ⟨u, ⟨u_conv, ⟨fun_conv, ⟨v, hv⟩⟩⟩⟩
        use fun n => (u n, f (u n), v n)
        constructor
        · intro n; simp; exact (hv n).1
        · exact Filter.Tendsto.prodMk_nhds u_conv
            (Filter.Tendsto.prodMk_nhds fun_conv ((forall_and_right _ _).1 hv).2)
      · intro h
        simp [subdifferential_Graph, subdifferential]
        simp at h
        obtain exist_seq := mem_closure_iff_seq_limit.1 h
        rcases exist_seq with ⟨x, ⟨exist_seq₁, x_converge⟩⟩
        rw [nhds_prod_eq] at x_converge
        obtain ⟨x1_conv, x2_conv⟩ := (Filter.tendsto_prod_iff'.1 x_converge)
        rw [nhds_prod_eq] at x2_conv
        obtain ⟨fx1_conv, x2_conv'⟩ := (Filter.tendsto_prod_iff'.1 x2_conv)
        simp [limsubdifferential_Graph] at exist_seq₁
        use (fun n => (x n).1)
        constructor; exact x1_conv
        constructor
        have : (fun n ↦ (x n).2.1) = (fun n => f (x n).1) := by
          ext n; exact (exist_seq₁ n).1
        rwa [this] at fx1_conv
        use (fun n => (x n).2.2)
        intro n; exact ⟨(exist_seq₁ n).2, x2_conv'⟩

theorem GraphOfSubgradientIsClosed {f : E → ℝ}
    {xn un : ℕ → E} {x u : E} (hx : ∀ n , (xn n, un n) ∈ subdifferential_Graph f)
    (hconv : Tendsto (fun n => (xn n , un n)) atTop (𝓝 (x, u)))
    (hf : Tendsto (fun n => f (xn n)) atTop (𝓝 (f x))) :
    (x, u) ∈ subdifferential_Graph f := by
  rw [subdifferential_Graph',mem_setOf_eq]
  simp only
  rw [← closure_closure,mem_closure_iff_seq_limit]
  use fun n => (xn n , f (xn n), un n)
  constructor
  · intro n
    have := hx n
    rw [subdifferential_Graph',mem_setOf_eq] at this
    exact this
  rw [nhds_prod_eq,Filter.tendsto_prod_iff'] at hconv;
  simp at hconv
  exact Filter.Tendsto.prodMk_nhds hconv.1 (Filter.Tendsto.prodMk_nhds hf hconv.2)

/- Definition of Φ_η, the family of desingularizing function -/
def desingularizing_function (η : ℝ) := {φ : ℝ → ℝ | (ConcaveOn ℝ (Ico 0 η) φ) -- ∧ (∀ x ∈ Ioo 0 η, φ x > 0)
  ∧ (φ 0 = 0) ∧ (ContDiffOn ℝ 1 φ (Ioo 0 η)) ∧ (ContinuousAt φ 0) ∧
  (∀ x ∈ Ioo 0 η, deriv φ x > 0)}

lemma desingularizing_function_is_nonneg (φ : ℝ → ℝ) (η : ℝ) (h : φ ∈ desingularizing_function η) :
  ∀ x ∈ Ioo 0 η, φ x > 0 := by
  simp [desingularizing_function] at h
  intro x ⟨hx₁, hx₂⟩
  rcases h with ⟨_,h₂,h₃,h₄,h₅⟩
  have Cont_φ : ContinuousOn φ (Icc 0 x) := by
    apply continuousOn_of_forall_continuousAt
    intro y hy
    by_cases hy0 : y = 0
    rwa [hy0]
    push_neg at hy0
    -- have hy1: y ∈ Ioc 0 x := ⟨lt_of_le_of_ne hy.1 (id (Ne.symm hy0)), hy.2⟩
    have cont_φ := ContDiffOn.continuousOn h₃
    have isopen : IsOpen (Ioo 0 η) := isOpen_Ioo
    by_cases hyx : y = x
    · simp [hyx]
      apply (IsOpen.continuousOn_iff isopen).1 cont_φ
      exact ⟨hx₁, hx₂⟩
    · push_neg at hyx
      have hy2 : y ∈ Ioo 0 x := ⟨lt_of_le_of_ne hy.1 (id (Ne.symm hy0)), lt_of_le_of_ne hy.2 hyx⟩
      apply (IsOpen.continuousOn_iff isopen).1 cont_φ
      use hy2.1
      rcases hy2 with ⟨_, hy2⟩
      linarith
  have Diff_φ : DifferentiableOn ℝ φ (Ioo 0 x) := by
    have diff_φ := ContDiffOn.differentiableOn h₃ (by simp)
    have subIoo: (Ioo 0 x) ⊆ (Ioo 0 η) := by
      intro x hx; simp at hx; use hx.1; linarith
    exact DifferentiableOn.mono diff_φ subIoo
  have hhh: ∃ y ∈ Ioo 0 x, φ x = φ 0 + (deriv φ y) * (x - 0) := by
    obtain h_lag := exists_deriv_eq_slope φ hx₁ Cont_φ Diff_φ
    rcases h_lag with ⟨c, ⟨hc, hval⟩⟩
    use c, hc
    have hx0 : x - 0 ≠ 0 := by linarith
    have hval' : deriv φ c * (x - 0) = φ x - φ 0 := (eq_div_iff hx0).1 hval
    linarith
  choose y hy₁ hy₂ using hhh
  rcases hy₁ with ⟨hy₁,hy₁'⟩
  have yleq: y < η := by linarith
  have hyderiv : 0 < deriv φ y := h₅ y hy₁ yleq
  nlinarith [hy₂, h₂, hyderiv, hx₁]

-- Definition of KL property with specific desingularizing function
def KL_point_with_reparameter (σ : E → ℝ) (u : E) (φ : ℝ → ℝ) : Prop :=
  ∃ η ∈ Ioi 0, ∃ s ∈ 𝓝 u, (φ ∈ desingularizing_function η) ∧  (∀ x ∈ s ∩
  {y ∈ active_domain σ | σ u < σ y ∧ σ y < σ u + η},
  deriv φ (σ x - σ u) * (Metric.infEDist 0 (subdifferential σ x)).toReal ≥ 1)

-- Definition of the KL property at one point
def KL_point (f : E → ℝ) (u : E) : Prop :=
  ∃ η ∈ Ioi 0, ∃ s ∈ 𝓝 u, ∃ φ ∈ desingularizing_function η, ∀ x ∈ s ∩
  {y | f u < f y ∧ f y < f u + η},
  (ENNReal.ofReal (deriv φ (f x - f u))) * (Metric.infEDist 0 (subdifferential f x)) ≥ ENNReal.ofReal 1

-- Definition of the KL function
def KL_function (f : E → ℝ) : Prop :=
  ∀ u ∈ active_domain f, KL_point f u

-- /- Definition of the desingularizing function -/
-- def desingularizing_function (c θ : ℝ) (_ : θ ∈ Ico 0 1) (_ : 0 < c) : ℝ → ℝ :=
--   fun t ↦  c * t ^ (1 - θ)

/- KL inequality for critical points -/
def KL_property_with_regularization (f : E → ℝ) (u' : E) (φ : ℝ → ℝ) : Prop :=
  ∃ η ∈ Ioi 0, ∃ s ∈ 𝓝 u', (φ ∈ desingularizing_function η) ∧
  (∀ x ∈ s ∩ {y ∈ active_domain f | f u' < f y ∧ f y < f u' + η},
  (Metric.infEDist 0 (subdifferential (λ u => φ (f u - f u')) x)).toReal ≥ 1)

-- deriv of function (fun t => c⁻¹ * t) is c⁻¹
lemma deriv_of_const_mul_func (c : ℝ) (x : ℝ) : deriv (fun (t : ℝ) => c⁻¹ * t) x = c⁻¹ := by
    apply HasDerivAt.deriv
    have : (fun (t : ℝ) => c⁻¹ * t) = (fun t => t * c⁻¹) := by ext t; ring
    rw [this]
    apply hasDerivAt_mul_const c⁻¹

-- Function (fun t => c⁻¹ * t) is a desingularizing function
lemma const_mul_special_concave : ∀ c > 0, (fun t => c⁻¹ * t) ∈ desingularizing_function (c / 2) := by
  intro c cpos; let φ := (fun t => c⁻¹ * t)
  simp [desingularizing_function]
  have fun_smul_eq_mul: (fun t ↦ c⁻¹ * t) = (fun t ↦ c⁻¹ • t) := by
    ext t; rw [smul_eq_mul]
  have h₁: ConcaveOn ℝ (Ico 0 (c / 2)) φ := by
    rw [ConcaveOn]; constructor; apply convex_Ico
    intro x _ y _ a b _ _ _
    show a • (c⁻¹ * x) + b • (c⁻¹ * y) ≤ c⁻¹ *  (a • x + b • y)
    rw [← smul_mul_assoc, ← smul_mul_assoc]; repeat rw [smul_eq_mul]
    linarith
  -- have h₂: ∀ (x : ℝ), 0 < x → x < c / 2 → 0 < φ x := by
  --   intro x xpos _; show c⁻¹ * x > 0; field_simp; exact cpos
  have h₃: ContDiffOn ℝ 1 (fun t ↦ c⁻¹ * t) (Ioo 0 (c / 2)) := by
    rw [fun_smul_eq_mul]; apply ContDiff.contDiffOn; apply contDiff_const_smul
  have h₄: ContinuousAt (fun t ↦ c⁻¹ * t) 0 := by
    simpa using (continuous_const.mul continuous_id).continuousAt
  have h₅: ∀ (x : ℝ), 0 < x → x < c / 2 → 0 < deriv (fun t ↦ c⁻¹ * t) x := by
    intro x _ _
    rw [deriv_of_const_mul_func]
    exact inv_pos.mpr cpos
  exact ⟨h₁, h₃, h₄, h₅⟩


-- Type transformation: ENNReal.ofReal (1 / (↑n + 1)) = (1 / (↑n + 1))
lemma one_div_type_trans: ∀ n : ℕ, ENNReal.ofReal (1 / (↑n + 1)) = (1 / (↑n + 1)) := by
    intro n
    have : ENNReal.ofReal (1 / (↑n + 1)) = ENNReal.ofReal 1 / ENNReal.ofReal (↑n + 1) := by
      apply ENNReal.ofReal_div_of_pos
      exact Nat.cast_add_one_pos n
    rw [this, ENNReal.ofReal_one]
    simp only [one_div, inv_inj]
    rw [← ENNReal.ofReal_one]
    have : ↑n = ENNReal.ofReal (↑n) := Eq.symm (ENNReal.ofReal_natCast n)
    rw [this]
    refine ENNReal.ofReal_add ?hp ?hq
    exact Nat.cast_nonneg' n
    exact zero_le_one' ℝ

lemma const_mul_edist_ge_one {c : ℝ} {ed : ENNReal} (hpos : c > 0)
  (hed : ed ≥ ENNReal.ofReal c) :
  ENNReal.ofReal c⁻¹ * ed ≥ ENNReal.ofReal 1 := by
  by_cases hed' : ed = ⊤
  have : ENNReal.ofReal c⁻¹ * ed = ⊤ := by
    rw [hed']; refine ENNReal.mul_top ?h; simpa
  rw [this]; simp; push_neg at hed'
  calc
    _ ≥ ENNReal.ofReal c⁻¹ * ENNReal.ofReal c := by
      exact mul_le_mul_of_nonneg_left hed (by exact bot_le)
    _ = ENNReal.ofReal 1 := by
      rw [← ENNReal.ofReal_mul]; field_simp; simp; exact le_of_lt hpos

lemma edist_geq_const (h_noncrit : 0 ∉ subdifferential f x) :
  ∃ c > 0, ∀ u, ‖u - x‖ + ‖f u - f x‖ < c →
  Metric.infEDist 0 (subdifferential f u) ≥ ENNReal.ofReal c := by
    by_contra! hc
    have sqh: ∀ n : ℕ, ∃ u, ‖u - x‖ + ‖f u - f x‖ < 1 / (n + 1) ∧
        (Metric.infEDist 0 (subdifferential f u)) < ENNReal.ofReal (1 / (n + 1)) :=
      fun n ↦ hc (1 / (n + 1)) (by simp; linarith)
    choose u hu using sqh
    have inequ_fun : ∀ n, (Metric.infEDist 0 (subdifferential f (u n))).toReal ≤ 1 / (n + 1) := by
      intro n
      apply (ENNReal.toReal_le_of_le_ofReal _ (le_of_lt (hu n).right))
      simp; linarith
    have : Tendsto (fun n ↦ (Metric.infEDist 0 (subdifferential f (u n))).toReal) atTop (𝓝 0) :=
      squeeze_zero (by simp) inequ_fun tendsto_one_div_add_atTop_nhds_zero_nat
    have h_contra : 0 ∈ subdifferential f x := by
      have u_to_x : Tendsto u atTop (𝓝 x) := by
        have : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 0) := by
          apply squeeze_zero (by simp) _ tendsto_one_div_add_atTop_nhds_zero_nat
          intro n
          have inequ₁: ‖u n - x‖ ≤ 1 / (n + 1) := by
              rcases hu n with ⟨hu₁, _⟩
              apply (le_of_add_le_of_nonneg_left (le_of_lt hu₁) (norm_nonneg (f (u n) - f x)))
          exact inequ₁
        apply  tendsto_iff_norm_sub_tendsto_zero.2 this
      have fu_to_fx : Tendsto (fun n ↦ f (u n)) atTop (𝓝 (f x)) := by
        have : Tendsto (fun n => ‖f (u n) - f x‖) atTop (𝓝 0) := by
          apply squeeze_zero (by simp) _ tendsto_one_div_add_atTop_nhds_zero_nat
          intro n
          have inequ₂: ‖f (u n) - f x‖ ≤ 1 / (n + 1) := by
            rcases hu n with ⟨hu₁,_⟩
            apply (le_of_add_le_of_nonneg_right (le_of_lt hu₁) (norm_nonneg (u n - x)))
          exact inequ₂
        apply tendsto_iff_norm_sub_tendsto_zero.2 this
      have exist_v: ∀ n : ℕ, ∃ vn, vn ∈ subdifferential f (u n) ∧ dist 0 vn < 1 / (n + 1) := by
        intro n
        rcases hu n with ⟨_,hu₂⟩
        have : ∃ vn ∈ subdifferential f (u n), edist 0 vn < 1 / (n + 1) := by
          apply Metric.infEDist_lt_iff.1
          rw [← one_div_type_trans n]
          exact hu₂
        choose vn hvn using this
        use vn, hvn.left
        rw [← one_div_type_trans n] at hvn
        apply edist_lt_ofReal.1 hvn.right
      choose v hv using exist_v
      have v_in_subdiff: ∀ n : ℕ, (u n, v n) ∈ subdifferential_Graph f := by
        intro n
        exact (hv n).1
      have v_to_zero: Tendsto v atTop (𝓝 0) := by
        have : Tendsto (fun n => ‖v n‖) atTop (𝓝 0) := by
          apply squeeze_zero (by simp) _ tendsto_one_div_add_atTop_nhds_zero_nat
          intro n
          have hdist : dist 0 (v n) < 1 / (n + 1) := (hv n).right
          exact (le_of_lt (by simpa [dist_eq_norm] using hdist))
        apply tendsto_zero_iff_norm_tendsto_zero.2 this
      show (x, 0) ∈ subdifferential_Graph f
      apply GraphOfSubgradientIsClosed v_in_subdiff
        (Filter.Tendsto.prodMk_nhds u_to_x v_to_zero) fu_to_fx
    contradiction

/-- Non-critical KL property is naturally true -/
theorem KL_property_at_noncritical_point (h_noncrit : 0 ∉ subdifferential f x) : KL_point f x := by
  obtain ⟨c, hc_pos, h⟩ := edist_geq_const h_noncrit
  let φ := (fun (t : ℝ) => c⁻¹ * t)
  rw [KL_point]
  use c/2, (by simpa using hc_pos), Metric.ball x (c / 2)
  constructor
  apply Metric.ball_mem_nhds; simpa using hc_pos
  use φ, const_mul_special_concave c hc_pos
  intro u hu
  rw [deriv_of_const_mul_func _ (f u - f x)]
  have : ‖u - x‖ + ‖f u - f x‖ < c := by
    rw [← add_halves c]
    apply add_lt_add
    · apply mem_ball_iff_norm.1 hu.left
    · simp at *
      rw [abs_eq_self.2] <;> linarith
  exact const_mul_edist_ge_one hc_pos (h u this)
end

section aux_lemma_uniform_KL

lemma real_geq_ennreal_ofreal_geq {a b : ℝ} {c : ENNReal} (hgeq : a ≥ b) (_apos : a > 0):
  (ENNReal.ofReal a) * c ≥ (ENNReal.ofReal b) * c := by
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hgeq) c

end aux_lemma_uniform_KL

variable {E : Type*}
variable {f : E → ℝ} {x : E}

-- Definition of functions constant on a set
def is_constant_on (f : E → ℝ) (Ω : Set E) : Prop :=
  ∀ x ∈ Ω, ∀ y ∈ Ω, f x = f y

-- If f is constant on an empty set, then a constant value can be chosen
lemma exist_constant_value (f : E → ℝ) {Ω : Set E} (h : is_constant_on f Ω)
  (h_nonempty : Ω.Nonempty) :
  ∃ μ : ℝ, ∀ x ∈ Ω, f x = μ := by
  rcases (Set.nonempty_def.1 h_nonempty) with ⟨x, hx⟩
  exact ⟨f x, fun y hy => h y hy x hx⟩

section uniformized_KL
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-  Uniformized KL property -/
theorem uniformized_KL_property {f : E → ℝ} {Ω : Set E} (h_compact : IsCompact Ω)
    (h_Ω1 : ∀ x ∈ Ω, KL_point f x) (h_Ω2: is_constant_on f Ω) :
    ∃ ε ∈ Ioi 0, ∃ η ∈ Ioi 0, ∃ φ ∈ desingularizing_function η, ∀ u ∈ Ω , ∀ x ∈
    {y : E | (Metric.infEDist y Ω).toReal < ε} ∩ {y  | f u < f y ∧ f y < f u + η},
    (ENNReal.ofReal (deriv φ (f x - f u))) * Metric.infEDist 0 (subdifferential f x) ≥ 1 := by
    -- case : Ω = ∅
    by_cases h_empty : Ω = ∅
    ·
      use 1, (by simp), 1, (by simp), (fun t => 2⁻¹ * t)
      constructor
      rw [← div_self]
      exact (const_mul_special_concave 2 (by simp))
      simp
      rw [h_empty]
      tauto
    -- case : Ω ≠ ∅
    have h_nonempty : Ω.Nonempty := Set.nonempty_iff_ne_empty.2 h_empty
    obtain ⟨μ, constant_value⟩ := exist_constant_value f h_Ω2 h_nonempty
    have : ∀ x ∈ Ω, ∃ η ∈ Ioi 0, ∃ (O : Set E) (_: IsOpen O) (_: x ∈ O),  ∃ φ ∈ desingularizing_function η,
      ∀ u ∈ O ∩ {y | f x < f y ∧ f y < f x + η},
      (ENNReal.ofReal (deriv φ (f u - f x))) * Metric.infEDist 0 (subdifferential f u) ≥ 1 := by
        intro x hx; simp [KL_point] at h_Ω1
        rcases h_Ω1 x hx with ⟨η, ⟨hη, ⟨s, ⟨hs, ⟨φ, hφ, h_Ω1⟩⟩⟩⟩⟩
        rcases mem_nhds_iff.1 hs with ⟨O, hO1, hO2, hO3⟩
        use η, hη, O, hO2, hO3, φ, hφ
        intro u hu
        simp at hu
        rcases hu with ⟨hu1, hu2, hu3⟩
        have : u ∈ s := by tauto
        exact h_Ω1 u this hu2 hu3
    choose! η h_exist using this
    choose hη2 h_exist using h_exist
    choose! O h_exist using h_exist
    choose h_Ox h_exist using h_exist
    choose h_Ox' h_exist using h_exist
    choose! φ h_exist using h_exist
    choose hφ h_exist using h_exist
    -- All the neighborhoods of the KL points become an open cover of Ω
    have exist_open_cover: Ω ⊆ ⋃ x ∈ Ω, O x := by
      intro x hx; simp
      exact ⟨x, ⟨hx, h_Ox' x hx⟩⟩
    -- There exists a finite sub-cover of this open cover.
    obtain exist_open_sub_finite_cover :=
      IsCompact.elim_finite_subcover_image h_compact h_Ox exist_open_cover
    rcases exist_open_sub_finite_cover with ⟨t, ht1, ht2, ht3⟩
    have mem_t_in_Ω : ∀ x ∈ ht2.toFinset, x ∈ Ω := by
      intro x hx
      obtain := (Set.Finite.mem_toFinset ht2).1 hx
      tauto
    have t_nonempty : ht2.toFinset.Nonempty := by
      simp; by_contra! h
      have : ⋃ i ∈ t, O i = ∅ := by simp [h]
      have  Ω_subset: Ω ⊆ ∅ := by rwa [this] at ht3
      have contra₁: Ω = ∅ := Set.subset_empty_iff.1 Ω_subset
      have contra₂: Ω ≠ ∅ := Set.Nonempty.ne_empty h_nonempty
      contradiction
    let φ_sum := ∑' x : ht2.toFinset, φ x
    have : ∃ η_min ∈ Ioi 0, ∀ x ∈ t, η x ≥ η_min := by
        have nonempty: (Finset.image η ht2.toFinset).Nonempty := by
          simpa using t_nonempty
        let η_min := (Finset.image η ht2.toFinset).min' nonempty
        use η_min
        constructor
        · simp [η_min]
          intro c hc
          exact hη2 c (mem_t_in_Ω c ((Set.Finite.mem_toFinset ht2).2 hc))
        intro x xt
        have min_le: ∀ s ∈ (Finset.image η ht2.toFinset), η_min ≤ s := by apply Finset.min'_le
        have η_in_image: (η x) ∈ (Finset.image η ht2.toFinset) := by
          rw [Finset.mem_image]
          use x
          constructor
          simp [xt]
          rfl
        exact min_le (η x) η_in_image
    rcases this with ⟨η_min, ηpos, hmin⟩
    simp [desingularizing_function] at hφ
    have hsum_attach : ∀ z : ℝ, ∑ c ∈ ht2.toFinset.attach, φ (↑c) z = ∑ c ∈ ht2.toFinset, φ c z := by
      intro z
      simpa using (Finset.sum_attach (s := ht2.toFinset) (f := fun c => φ c z))
    -- φ_sum is desingularizing_function
    have h_special_concave: φ_sum ∈ desingularizing_function η_min := by
      simp [desingularizing_function]
      have h₁ : ConcaveOn ℝ (Ico 0 η_min) φ_sum := by
        rw [ConcaveOn]
        constructor
        apply convex_Ico
        intro x xpos y ypos a b apos bpos absum
        simp [φ_sum]
        rw [hsum_attach x, hsum_attach y, hsum_attach (a * x + b * y)]
        have : ∀ d : ℝ, ∀ x : ℝ, d * ∑ c ∈ ht2.toFinset,
            φ c x = ∑ c ∈ ht2.toFinset, d * (φ c x) := by
          intro d x
          let f c := φ c x
          show d * ∑ c ∈ ht2.toFinset, f c = ∑ c ∈ ht2.toFinset, d * f c
          rw [← Finset.tsum_subtype', ← Finset.tsum_subtype', ← tsum_mul_left]
        rw [this a x, this b y, ← Finset.sum_add_distrib]
        have : ∀ c ∈ t, (a * φ c x + b * φ c y) ≤ φ c (a * x + b * y) := by
          intro c hc
          simp at xpos ypos
          have xleq : x < η c := by
            obtain := hmin c hc
            linarith
          have yleq : y < η c := by
            obtain := hmin c hc
            linarith
          obtain c_in_finset := (Set.Finite.mem_toFinset ht2).2 hc
          obtain inequ_concave := (hφ c (mem_t_in_Ω c c_in_finset)).1
          simp [ConcaveOn] at inequ_concave
          apply inequ_concave.2 xpos.1 xleq ypos.1 yleq apos bpos absum
        apply Finset.sum_le_sum
        intro c hc
        exact this c ((Set.Finite.mem_toFinset ht2).1 hc)
      -- have h₂ : ∀ (x : ℝ), 0 < x → x < η_min → 0 < φ_sum x := by
      --   intro x hx1 hx2; simp [φ_sum]
      --   apply Finset.sum_pos
      --   intro c hc
      --   have xleq : x < η c := by
      --     obtain := hmin c ((Set.Finite.mem_toFinset ht2).1 hc)
      --     linarith
      --   exact (hφ c (mem_t_in_Ω c hc)).2.1 x hx1 xleq
      --   exact t_nonempty
      have h₃ : φ_sum 0 = 0 := by
        simp [φ_sum, hsum_attach]
        have : ∀ x ∈ ht2.toFinset, φ x 0 = 0 := by
          intro x xt
          exact (hφ x (mem_t_in_Ω x xt)).2.1
        apply Finset.sum_eq_zero this
      have h₄ : ContDiffOn ℝ 1 φ_sum (Ioo 0 η_min) := by
        have : φ_sum = (fun c => ∑ x ∈ ht2.toFinset, φ x c) := by
          ext c
          simpa [φ_sum] using hsum_attach c
        rw [this]
        apply ContDiffOn.sum
        intro c hc
        obtain φ_cont_diff := (hφ c (mem_t_in_Ω c hc)).2.2.1
        apply ContDiffOn.mono φ_cont_diff
        apply Set.Ioo_subset_Ioo_right
        exact hmin c ((Set.Finite.mem_toFinset ht2).1 hc)
      have h₅ : ContinuousAt φ_sum 0 := by
        rw [ContinuousAt]
        have : φ_sum = (fun c => ∑ x ∈ ht2.toFinset, φ x c) := by
          ext c
          simpa [φ_sum] using hsum_attach c
        rw [this]
        apply tendsto_finset_sum
        intro c hc
        obtain cont := (hφ c (mem_t_in_Ω c hc)).2.2.2.1
        rw [ContinuousAt] at cont
        exact cont
      have h₆ : ∀ (x : ℝ), 0 < x → x < η_min → 0 < deriv φ_sum x := by
        intro y ypos yleq
        have : φ_sum = (fun c => ∑ x ∈ ht2.toFinset, φ x c) := by
          ext c
          simpa [φ_sum] using hsum_attach c
        rw [this]
        have : deriv (fun c ↦ ∑ x ∈ ht2.toFinset, φ x c) y = ∑ x ∈ ht2.toFinset, deriv (φ x) y := by
          have hfun : (fun c => ∑ x ∈ ht2.toFinset, φ x c) = (∑ x ∈ ht2.toFinset, φ x) := by
            ext c; exact Eq.symm (Finset.sum_apply c ht2.toFinset φ)
          have hderiv : deriv (∑ x ∈ ht2.toFinset, φ x) y = ∑ x ∈ ht2.toFinset, deriv (φ x) y := by
            apply deriv_sum
            intro c hc
            have η_inequ : y < η c := by
              obtain := hmin c ((Set.Finite.mem_toFinset ht2).1 hc)
              linarith
            specialize hφ c (mem_t_in_Ω c hc)
            obtain contdiff := ContDiffOn.contDiffAt hφ.2.2.1 (Ioo_mem_nhds ypos η_inequ)
            exact ContDiffAt.differentiableAt contdiff (by simp)
          simpa [hfun] using hderiv
        rw [this]
        apply Finset.sum_pos
        · intro c hc
          have : y < η c := by
            obtain := hmin c ((Set.Finite.mem_toFinset ht2).1 hc)
            linarith
          specialize hφ c (mem_t_in_Ω c hc)
          exact hφ.2.2.2.2 y ypos this
        · exact t_nonempty
      exact ⟨h₁,h₃,h₄,h₅,h₆⟩
    have uniform_ball: ∃ ε ∈ Ioi 0, {y| Metric.infEDist y Ω < ENNReal.ofReal ε} ⊆ ⋃ x ∈ t, O x := by
        have union_open : IsOpen (⋃ x ∈ t, O x) := by
          have : ∀ x ∈ t, IsOpen (O x) := by
            intro x hx
            have : x ∈ Ω := by tauto
            apply h_Ox
            apply this
          apply isOpen_biUnion this
        obtain res_thickening := IsCompact.exists_thickening_subset_open h_compact union_open ht3
        rcases res_thickening with ⟨ε, ⟨hε, h2⟩⟩
        use ε, hε
        have : {y| Metric.infEDist y Ω < ENNReal.ofReal ε} = Metric.thickening ε Ω := by
          ext x; exact Metric.mem_thickening_iff_infEDist_lt
        rwa [this]
    choose ε uniform_ball using uniform_ball
    have : {y| Metric.infEDist y Ω < ENNReal.ofReal ε} = {y| (Metric.infEDist y Ω).toReal < ε} := by
      ext x; apply ENNReal.lt_ofReal_iff_toReal_lt (Metric.infEDist_ne_top h_nonempty)
    rw [this] at uniform_ball
    -- There exists one open set in the finite cover
    have exist_one_ball: ∀ u ∈ {y| (Metric.infEDist y Ω).toReal < ε}
        ∩ {y |  μ < f y ∧ f y < μ + η_min},
      ∃ x ∈ t, u ∈ O x := by
      intro u hu
      obtain u_in_union := Set.mem_of_subset_of_mem uniform_ball.2 hu.1
      simpa using u_in_union
    use ε, uniform_ball.1, η_min, ηpos, φ_sum, h_special_concave
    intro baru hbaru
    rw [constant_value baru hbaru]
    intro u hu
    -- u must fall into one ball
    rcases exist_one_ball u hu with ⟨ui, ⟨hui₁, hui₂⟩⟩
    simp at hu
    rcases hu with ⟨_,hu2,hu3⟩
    -- rcases hu with ⟨_, ⟨hu21 , ⟨hu221, hu222⟩⟩⟩
    calc
      _ ≥ (ENNReal.ofReal (deriv (φ ui) (f u - μ))) * Metric.infEDist 0 (subdifferential f u) := by
        have deriv_φ_pos: deriv φ_sum (f u - μ) > 0 := by
          simp [desingularizing_function] at h_special_concave
          obtain h_tmp := h_special_concave.2.2.2.2
          apply h_tmp
          · linarith [hu2]
          · linarith [hu3]
        apply real_geq_ennreal_ofreal_geq
        simp [φ_sum]
        have hfun_attach :
            (∑ b ∈ ht2.toFinset.attach, φ (↑b)) = (fun c => ∑ x ∈ ht2.toFinset, φ x c) := by
          ext c
          simpa [Finset.sum_apply] using hsum_attach c
        rw [hfun_attach]
        have equ₁: deriv (fun c ↦ ∑ x ∈ ht2.toFinset, φ x c) (f u - μ) =
            ∑ x ∈ ht2.toFinset, deriv (φ x) (f u - μ) := by
          have hfun : (fun c => ∑ x ∈ ht2.toFinset, φ x c) = (∑ x ∈ ht2.toFinset, φ x) := by
            ext c; exact Eq.symm (Finset.sum_apply c ht2.toFinset φ)
          have hderiv :
              deriv (∑ x ∈ ht2.toFinset, φ x) (f u - μ) = ∑ x ∈ ht2.toFinset, deriv (φ x) (f u - μ) := by
            apply deriv_sum
            intro c hc
            have σu_pos : f u - μ > 0 := by linarith [hu2]
            have η_inequ : (f u - μ) < η c := by
              obtain inequ_ηmin := hmin c ((Set.Finite.mem_toFinset ht2).1 hc)
              linarith
            specialize hφ c (mem_t_in_Ω c hc)
            obtain contdiff := ContDiffOn.contDiffAt hφ.2.2.1 (Ioo_mem_nhds σu_pos η_inequ)
            exact ContDiffAt.differentiableAt contdiff (by simp)
          simpa [hfun] using hderiv
        rw [equ₁]

        -- have : (∑ x ∈ ht2.toFinset, deriv (φ x) (f u - μ)) ≥ deriv (φ ui) (f u - μ) := by
        let g x := deriv (φ x) (f u - μ)
        show (∑ x ∈ ht2.toFinset, g x) ≥ g ui
        apply Finset.single_le_sum
        intro c hc
        have σu_pos : f u - μ > 0 := by linarith [hu2]
        have η_inequ: (f u - μ) < η c := by
          obtain inequ_ηmin:= hmin c ((Set.Finite.mem_toFinset ht2).1 hc)
          linarith
        simp [g]
        specialize hφ c (mem_t_in_Ω c hc)
        apply le_of_lt (hφ.2.2.2.2 (f u - μ) σu_pos η_inequ)
        apply ((Set.Finite.mem_toFinset ht2).2 hui₁)
        -- apply real_geq_ennreal_ofreal_geq
        -- apply lt_of_lt_of_le _ this
        exact deriv_φ_pos
      _ ≥ 1 := by
        obtain equ_μ := constant_value ui (mem_t_in_Ω ui ((Set.Finite.mem_toFinset ht2).2 hui₁))
        specialize h_exist ui (mem_t_in_Ω ui ((Set.Finite.mem_toFinset ht2).2 hui₁))
        specialize h_exist u ⟨hui₂, _⟩
        simp [equ_μ]
        use hu2
        have : η_min ≤ η ui := hmin ui hui₁
        linarith
        rw [equ_μ] at h_exist
        exact h_exist


-- theorem uniformly_KL_property' {f : E → ℝ} {Ω : Set E} (h_compact : IsCompact Ω)
--     (h_Ω1 : ∀ x ∈ Ω, KL_point f x) (h_Ω2: is_constant_on f Ω) :
--     ∃ ε ∈ Ioi 0, ∃ η ∈ Ioi 0, ∃ φ ∈ desingularizing_function η, ∀ u ∈ Ω , ∀ x ∈
--     {y : E | (Metric.infEDist y Ω).toReal < ε} ∩ {y | f u < f y ∧ f y < f u + η},
--     (Real.toEReal (deriv φ (f x - f u))) * (Metric.infEDist 0 (subdifferential f x))
--       ≥ Real.toEReal 1 := by

--     obtain h := uniformly_KL_property h_compact h_Ω1 h_Ω2
--     rcases h with ⟨ε, hε, η, hη, φ, hφ, h⟩
--     use ε, hε, η, hη, φ, hφ
--     intro u hu x hx
--     by_cases h_empty : Metric.infEDist 0 (subdifferential f x) = ⊤
--     · rw [h_empty]
--       have hderiv: Real.toEReal (deriv φ (f x - f u)) > 0 := by sorry
--       have hh: (Real.toEReal (deriv φ (f x - f u))) * (ENNReal.toEReal ⊤) = ⊤ := by
--         sorry
--       rw [hh]
--       simp
--     · push_neg at h_empty
--       have h_not_bot: Metric.infEDist 0 (subdifferential f x) ≠ ⊥ := by sorry
--       sorry
--     -- by_cases h_empty : Metric.infEDist 0 (subdifferential f x) = ∅
end uniformized_KL
