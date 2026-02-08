import Mathlib.Analysis.Matrix
import Mathlib.Data.Matrix.ColumnRowPartitioned


namespace Matrix

open scoped BigOperators
open Matrix Module

local notation "⟪" x ", " y "⟫_" 𝕜 => inner 𝕜 x y

variable {𝕜 : Type*} [RCLike 𝕜]


section Theorem_2_1_1

/-!
The final goal of this section is to prove
```
Matrix.exists_unitary_completion_matrix_col [RCLike 𝕜]
  [Fintype ι] [Fintype κ₁] [Fintype κ₂]
  [DecidableEq ι] [DecidableEq κ₁] [DecidableEq κ₂]
  (e : ι ≃ κ₁ ⊕ κ₂) (V₁ : Matrix ι κ₁ 𝕜) (h₁ : V₁ᴴ * V₁ = 1) :
  ∃ V₂ V, V = V₁.fromCols V₂ ∧ V.submatrix id ⇑e ∈ unitaryGroup ι 𝕜
```

In order to construct the column/row orthonormal complement of a matrix, we choose to use
the orthonormal complement of its column/row space.

In order to do that, we should view a matrix as a family of vectors in the Euclidean space, where
the orthonormal complement space is defined, which is implemented as `Matrix.colVec` and
`Matrix.rowVec`.

`Matrix.colSubmodule` and `Matrix.rowSubmodule` are respectively the column-space and the row-space
of a matrix.

In addition, it is useful to (noncomputably) construct a matrix as an orthonormal basis of a
subspace in the Euclidean space. So we have `EuclideanSpace.Submodule.rowOrthonormalMatrix` and
`EuclideanSpace.Submodule.colOrthonormalMatrix` to declare the existence of such a matrix.

#### Definitons
Let `A` be a matrix
- `A.colVec` is `A.col` with Euclidean norm.
  The op version is `A.rowVec`.
- `A.colSubmodule` is the submodule spanned by `A.colVec`.
  The op version is `A.rowSubmodule`

#### Theorems
- `inner_eq_mul_conjTranspose` says `⟪A.rowVec i, A.rowVec j⟫_𝕜 = (A * Aᴴ) j i`.
  The oop version is `inner_eq_conjTranspose_mul`
- `rowVec_orthonormal_iff_mul_conjTranspose_eq_one` says `A` is row-orthonormal
  iff `A * Aᴴ = 1`.
  The op version is `colVec_orthonormal_iff_conjTranspose_mul_eq_one`.
- `rowVec_linearIndependent_of_mul_conjTranspose_eq_one` says `A` is row-independent
  if `A * Aᴴ = 1`.
  The op version is `colVec_orthonormal_iff_conjTranspose_mul_eq_one`
- `finrank_rowSubmodule_of_mul_conjTranspose_eq_one` calculates `finrank A` given `A * Aᴴ = 1`.
  The op-version is `finrank_colSubmodule_of_conjTranspose_mul_eq_one`
- `Submodule.orthonormal_iff` reduces the orthonormality of a submodule to that of its parant.
- `EuclideanSpace.Submodule.rowOrthonormalMatrix` gets a matrix for a submodule of an EuclideanSpace
  whose rowVecs orthonormally span it.
  The op-version is `EuclideanSpace.Submodule.colOrthonormalMatrix`

#### Comment Style Note
In Lean, a linear subspace is called a `Submodule` because a linear space is not but a module
over a field. Regardless, we still use the word "subspace" instead of "submodule" in comments.
-/

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
#check InnerProductSpace
/-- For `M : Matrix ι ι' 𝕜`, view `M.col` as `EuclideanSpace 𝕜 ι` -/
def colVec (A : Matrix m n 𝕜) : EuclideanSpace (EuclideanSpace 𝕜 m) n :=
  WithLp.toLp 2 <| fun i => WithLp.toLp 2 <| A.col i

/-- For `M : Matrix ι ι' 𝕜`, view `M.row` as `EuclideanSpace 𝕜 ι'` -/
def rowVec (A : Matrix m n 𝕜) : EuclideanSpace (EuclideanSpace 𝕜 n) m :=
  WithLp.toLp 2 <| fun i => WithLp.toLp 2 <| A.row i

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/--
The inner product of two row vectors can be expressed as an element of
the matrix product of the matrix and its conjTranspose.
-/
lemma inner_eq_mul_conjTranspose {A : Matrix m n 𝕜} {i j} :
    (⟪ A.rowVec i, A.rowVec j ⟫_𝕜) = (A * Aᴴ) j i := by
  simp [conjTranspose, inner, rowVec, Matrix.mul_apply]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The inner product of two column vectors can be expressed as an element of
the matrix product of the conjTranspose of the matrix and itself. -/
lemma inner_eq_conjTranspose_mul {A : Matrix m n 𝕜} {i j} :
    (⟪ A.colVec i, A.colVec j ⟫_𝕜 ) = (Aᴴ * A) i j := by
  simp [conjTranspose, inner, colVec, Matrix.mul_apply, mul_comm]

/--
The rowVecs of a matrix are orthonormal iff the product of the matrix
and its conjTranspose is one.
-/
lemma rowVec_orthonormal_iff_mul_conjTranspose_eq_one {ι ι'}
    [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    {V : Matrix ι ι' 𝕜} :
    Orthonormal 𝕜 (V.rowVec) ↔ (V * Vᴴ = (1 : Matrix ι ι 𝕜))  := by
  simp [←Matrix.ext_iff, ←inner_eq_mul_conjTranspose]
  -- we prove it by proving the identity entrywise, and rewrite the right as the inner product
  -- of vectors
  constructor
  · intro ⟨h₁, h₂⟩ i j
    by_cases ij : i=j
    · rw[ij, inner_self_eq_norm_sq_to_K, h₁]; simp
    · simp [ij]
      exact h₂ (Ne.symm ij)
  · intro hA
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · simp [norm_eq_sqrt_re_inner (𝕜:=𝕜), hA]
    · simp [hA, hij.symm]

omit [Fintype n] [DecidableEq m] in
/--
The colVecs of a matrix are orthonormal iff the product of the
conjTranspose of the matrix and the matrix.
-/
lemma colVec_orthonormal_iff_conjTranspose_mul_eq_one
    {A : Matrix m n 𝕜} :
    Orthonormal 𝕜 (A.colVec) ↔ (Aᴴ * A = 1) := by
  simp [←Matrix.ext_iff, ←inner_eq_conjTranspose_mul]
  constructor
  · intro ⟨h₁, h₂⟩ i j
    by_cases hij : i=j
    · rw [hij, inner_self_eq_norm_sq_to_K, h₁]; simp
    · simp [hij, h₂ hij]
  · intro hA
    refine ⟨fun i => ?_ , fun i j hij => ?_⟩
    · simp [norm_eq_sqrt_re_inner (𝕜:=𝕜), hA]
    · simp [hA, hij] -- branch `i ≠ j`

/-- If `A * Aᴴ = 1`, then `A` is row-independent -/
@[simp] lemma rowVec_linearIndependent_of_mul_conjTranspose_eq_one
    {A : Matrix m n 𝕜} (h : A * Aᴴ = 1) :
    LinearIndependent 𝕜 (A.rowVec) :=
  Orthonormal.linearIndependent <| rowVec_orthonormal_iff_mul_conjTranspose_eq_one.2 h

omit [Fintype n] [DecidableEq m] in
/-- If `Aᴴ * A = 1`, then `A` is col-independent -/
@[simp] lemma colVec_linearIndependent_of_conjTranspose_mul_eq_one
    {A : Matrix m n 𝕜} (h : Aᴴ * A = 1) :
    LinearIndependent 𝕜 (A.colVec) :=
  Orthonormal.linearIndependent <| colVec_orthonormal_iff_conjTranspose_mul_eq_one.2 h

/-- The subspace spanned by the rows of a matrix -/
def rowSubmodule (A : Matrix m n 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  Submodule.span 𝕜 (Set.range A.rowVec)

/-- The subspace spanned by the columns of a matrix -/
def colSubmodule (A : Matrix m n 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 m) :=
  Submodule.span 𝕜 (Set.range A.colVec)

omit [DecidableEq m] in
/--
The finrank of the column space of a matrix equals the number of columns
-/
@[simp] lemma finrank_colSubmodule_of_conjTranspose_mul_eq_one {A : Matrix m n 𝕜} (h : Aᴴ * A = 1) :
    Module.finrank 𝕜 A.colSubmodule = Fintype.card n := by
  unfold colSubmodule
  rw [finrank_span_eq_card]
  simp [h]

/--
The finrank of the row space of a matrix equals the number of rows
-/
@[simp] lemma finrank_rowSubmodule_of_mul_conjTranspose_eq_one {A : Matrix m n 𝕜} (h : A * Aᴴ = 1) :
    Module.finrank 𝕜 A.rowSubmodule = Fintype.card m := by
  unfold rowSubmodule
  rw [finrank_span_eq_card]
  simp [h]

variable {E} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/--
An family of vectors in the subspace is orthonormal, iff it is orthonormal in the total space
-/
def Submodule.orthonormal_iff {ι} (N : Submodule 𝕜 E) (v : ι → N) :
    Orthonormal 𝕜 v ↔ Orthonormal 𝕜 (fun i => (↑(v i) : E)) := by
  unfold Orthonormal norm inner -- lean cannot figure out this is defeq until we unfold the defs
  rfl


/--
For a subspace of a Euclidean space, get a matrix whose rowVecs orthonormally span it.
-/
lemma EuclideanSpace.Submodule.rowOrthonormalMatrix
    (V : Submodule 𝕜 (EuclideanSpace 𝕜 n)) (h : Fintype.card m = finrank 𝕜 V) :
    ∃ A : Matrix m n 𝕜,
      Orthonormal 𝕜 A.rowVec ∧ V = A.rowSubmodule := by
  have ⟨w, ⟨b, _⟩⟩ := exists_orthonormalBasis 𝕜 V -- get an orthonormal bais indexed by `w`
  have e : w ≃ m := by -- prove `w ≃ m` so that we can reindex `b` later
    apply Fintype.equivOfCardEq
    rw [h];
    symm
    exact finrank_eq_card_basis b.toBasis
  let b' := b.reindex e -- `b'` is the index we need
  let A' (i : m) : EuclideanSpace 𝕜 n := (b' i).val -- `A'` is the family of vectors we need
  let A : Matrix m n 𝕜 := A' -- `A` is the matrix of `A'` (as its row vectors)
  use A -- now the goal is `Orthonormal 𝕜 A.rowVec ∧ V = A.rowSubmodule`
  have ONA : Orthonormal 𝕜 A' := b'.orthonormal
  refine ⟨ONA, ?_⟩
  symm -- now the goal is `A.rowSubmodule = V`
  apply Submodule.eq_of_le_of_finrank_eq
  -- the plan is to prove `A` is a subspace of `V` and their dimensions are equal
  case hle =>
    simp [rowSubmodule, Submodule.span_le, Set.range]
    intro
    simp [A, A', rowVec, row]
    intro i h
    rw [← h]
    exact (b' i).property
  case h.hd =>
    rw [← h]
    apply finrank_rowSubmodule_of_mul_conjTranspose_eq_one
    exact rowVec_orthonormal_iff_mul_conjTranspose_eq_one.1 ONA

/--
For a subspace in a Euclidean space, get a matrix whose colVecs orthonormally span it.
-/
lemma EuclideanSpace.Submodule.colOrthonormalMatrix
    (V : Submodule 𝕜 (EuclideanSpace 𝕜 n)) (h : Fintype.card m = finrank 𝕜 V) :
    ∃ A : Matrix n m 𝕜,
      Orthonormal 𝕜 A.colVec ∧ V = A.colSubmodule := by
  have ⟨A, ⟨h1, h2⟩⟩ := rowOrthonormalMatrix V h
  use Aᵀ
  simp [colVec, colSubmodule]
  exact ⟨h1, h2⟩


open Function in
/--
If a submatrix is constructed using equivalences, then the submatrix is in the unitary group
if the original matrix is.
-/
@[simp]
lemma Submatrix.mem_unitaryGroup_of_mem_of_equiv
    (e₁ e₂ : m ≃ n) (A : Matrix n n 𝕜) (h : A ∈ unitaryGroup n 𝕜) :
    A.submatrix e₁ e₂ ∈ unitaryGroup m 𝕜 := by
  simp [mem_unitaryGroup_iff]
  simp [mem_unitaryGroup_iff] at h

  change A.submatrix e₁ e₂ * (A.submatrix e₁ e₂)ᴴ = 1

  change A * Aᴴ = 1 at h

  -- We want to prove the goal `A.submatrix e₁ e₂ * (A.submatrix e₁ e₂)ᴴ = 1` by `h : A * Aᴴ = 1`.
  -- We "submatrix back" the lhs of the goal to make it identical to the lhs of h

  suffices (A.submatrix ⇑e₁ ⇑e₂ * (A.submatrix ⇑e₁ ⇑e₂)ᴴ).submatrix e₁.symm e₁.symm = 1 from by
    have := congrArg (fun x => x.submatrix e₁ e₁) this
    simp at this
    rw [submatrix_mul (e₂ := e₂)] at this
    · exact this
    · exact Equiv.bijective e₂

  simp
  exact h

open Function in
/--
If a submatrix is constructed using equivalences, then the submatrix is in the unitary group
iff the original matrix is.
-/
lemma Submatrix.mem_unitaryGroup_iff_of_equiv (e₁ e₂ : m ≃ n) (A : Matrix n n 𝕜) :
    A.submatrix e₁ e₂ ∈ unitaryGroup m 𝕜 ↔ A ∈ unitaryGroup n 𝕜 where
  mpr := mem_unitaryGroup_of_mem_of_equiv e₁ e₂ A
  mp := by
    have := mem_unitaryGroup_of_mem_of_equiv e₁.symm e₂.symm (A.submatrix e₁ e₂)
    simp at this
    exact this

open Function in
/--
If a submatrix is constructed using bijectives, then the submatrix is in the unitary group
iff the original matrix is.
-/
lemma Submatrix.mem_unitaryGroup_iff_of_bij
    {f g : m → n} (hf : Bijective f) (hg : Bijective g) (A : Matrix n n 𝕜) :
    A.submatrix f g ∈ unitaryGroup m 𝕜 ↔ A ∈ unitaryGroup n 𝕜 :=
  Submatrix.mem_unitaryGroup_iff_of_equiv (Equiv.ofBijective f hf) (Equiv.ofBijective g hg) A

open Fintype in
/--
The version of `exists_unitary_completion_matrix_row` with `ι := κ₁ ⊕ κ₂`,
which is easier to prove than the version generaalized with a more arbitrary `ι`.
-/
private theorem exists_unitary_completion_matrix_row_aux
    {κ₁ κ₂ : Type*}
    [Fintype κ₁] [Fintype κ₂]
    [DecidableEq κ₁] [DecidableEq κ₂]
    (V₁ : Matrix κ₁ (κ₁ ⊕ κ₂) 𝕜)
    (h₁ : V₁ * V₁ᴴ = (1 : Matrix κ₁ κ₁ 𝕜)) :
    ∃ (V₂ : Matrix κ₂ (κ₁ ⊕ κ₂) 𝕜) (V : Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) 𝕜),
      V = V₁.fromRows V₂ ∧
      V ∈ unitaryGroup (κ₁ ⊕ κ₂) 𝕜 := by
  -- Construct the subspace `V₁'` and `V₂' := V₁'ᗮ`, and prove about their finrank
  let V₁' := V₁.rowSubmodule
  let V₂' := V₁'ᗮ
  let on₁ : Orthonormal 𝕜 V₁.rowVec := rowVec_orthonormal_iff_mul_conjTranspose_eq_one.2 h₁
  have : Module.finrank 𝕜 V₁' = card κ₁ := by -- calculate the finrank of V₁'
    simp [V₁',finrank_rowSubmodule_of_mul_conjTranspose_eq_one h₁]
  have fr2 : Module.finrank 𝕜 V₂' = card κ₂:= by -- calculate the finrank of V₂'
    have : card κ₁ + (Module.finrank 𝕜 V₂') = card κ₁ + (card κ₂) := by
      simp [← this , V₂', Submodule.finrank_add_finrank_orthogonal]
    omega
  -- Get the basis-row-matrix of `V₂'` and construct the matrix `V₂` from the basis
  let ⟨V₂, ⟨on₂, V₂'_eq⟩⟩ := EuclideanSpace.Submodule.rowOrthonormalMatrix V₂' fr2.symm
  -- Now we use `V₂` and then prove `Vᴴ * V = 1`
  use V₂; simp
  rw [mem_unitaryGroup_iff]
  change (V₁.fromRows V₂) * (V₁.fromRows V₂)ᴴ = 1
  rw [← rowVec_orthonormal_iff_mul_conjTranspose_eq_one]
  -- Now we changed the goal into the orthonormality of vector families,
  -- which we will prove entrywise for both cases of `orthonormal`,
  -- and thus we have 6 cases in total since we have to case every entry, which is in a sum-type.
  constructor
  · rintro (i | i)
    · exact on₁.1 i
    · exact on₂.1 i
  · rintro (i | i) (j | j) ij
    · simp at ij
      apply on₁.2 ij
    · apply Submodule.inner_right_of_mem_orthogonal (𝕜:=𝕜)
        (u:= V₁.rowVec i) (v := V₂.rowVec j) (K:= V₁')
        (Submodule.mem_span_of_mem (by simp))
      change V₂.rowVec j ∈ V₂'
      rw [V₂'_eq]
      apply Submodule.mem_span_of_mem
      simp
    · apply Submodule.inner_right_of_mem_orthogonal (𝕜:=𝕜)
        (u:= V₂.rowVec i) (v := V₁.rowVec j) (K:= V₂')
      · rw [V₂'_eq]; apply Submodule.mem_span_of_mem; simp
      · simp [V₂']; apply Submodule.mem_span_of_mem; simp
    · simp at ij
      exact on₂.2 ij


/--
**Orthogonal (unitary) completion for matrices over a general RCLike field**:

Let `ι` be a finite index set (rows), and let `κ₁, κ₂` be finite index sets (columns).
Suppose `e : ι ≃ κ₁ ⊕ κ₂` is a decomposition of the row indices.

Let `V₁ : Matrix ι κ₁ 𝕜` be a matrix whose columns are orthonormal:
V₁ᴴ * V₁ = 1

Then there exists a matrix `V₂ : Matrix ι κ₂ 𝕜` such that the concatenation
V = V₁.fromCols V₂

becomes unitary after permuting the rows by `e`:
V.submatrix id e ∈ unitaryGroup ι 𝕜

This is the generalization of the classical Gram–Schmidt completion:
any set of orthonormal vectors can be extended to an orthonormal basis (unitary matrix).

`exists_unitary_completion_matrix_col` or simply `exists_unitary_completion_matrix`
is the default version.

`exists_unitary_completion_matrix_row` is the transposed version,
i.e. there exists `V₁.fromRows V₂` which is unitary, given `V₁ * V₁ᴴ = 1`.
-/

theorem exists_unitary_completion_matrix_row
    {ι κ₁ κ₂ : Type*}
    [Fintype ι] [Fintype κ₁] [Fintype κ₂]
    [DecidableEq ι] [DecidableEq κ₁] [DecidableEq κ₂]
    (e : ι ≃ κ₁ ⊕ κ₂)
    (V₁ : Matrix κ₁ ι 𝕜)
    (h₁ : V₁ * V₁ᴴ = 1) :
    ∃ (V₂ : Matrix κ₂ ι 𝕜) (V : Matrix (κ₁ ⊕ κ₂) ι 𝕜),
      V = V₁.fromRows V₂ ∧
      (V.submatrix e id) ∈ unitaryGroup ι 𝕜 := by
  -- Now that we have already the proof in the case where `ι := κ₁ ⊕ κ₂`, the remaining goal is
  -- to "transpose" the proof through `e`.

  -- first we construct `V₁'` and `V₂'`, which are in the case where `ι := κ₁ ⊕ κ₂`
  let V₁' := V₁.submatrix id e.symm
  have h₁' : V₁' * V₁'ᴴ = 1 := by simp[V₁', h₁]
  let p := exists_unitary_completion_matrix_row_aux V₁' h₁'
  simp at p
  obtain ⟨V₂', h₂'⟩ := p

  let V₂ := V₂'.submatrix id e -- Now we can get `V₂` from `V₂'`

  use V₂; simp -- Now the goal is to prove `V₁.fromRows V₂` is unitary after the permutation

  rw [← Submatrix.mem_unitaryGroup_iff_of_equiv (e₁:=e.symm) (e₂:=e.symm)]
  -- We rewrite the goal with the lemma to cancel the `submatrix`
  simp
  -- Goal: `(V₁.fromRows V₂).submatrix id ⇑e.symm ∈ unitaryGroup (κ₁ ⊕ κ₂) 𝕜`
  -- We have: `h₂' : V₁'.fromRows V₂' ∈ unitaryGroup (κ₁ ⊕ κ₂) 𝕜`
  -- The plan is to show the lhs of `h₂'` is exactly the lhs of the goal
  suffices V₁'.fromRows V₂' = (V₁.fromRows V₂).submatrix id ⇑e.symm from by
    simp [this] at h₂'
    exact h₂'

  apply Matrix.ext
  rintro (i|i) (j|j)
  · rfl
  · rfl
  · simp [V₂]
  · simp [V₂]

@[inherit_doc exists_unitary_completion_matrix_row]
theorem exists_unitary_completion_matrix_col {ι κ₁ κ₂ : Type*}
    [Fintype ι] [Fintype κ₁] [Fintype κ₂]
    [DecidableEq ι] [DecidableEq κ₁] [DecidableEq κ₂]
    (e : ι ≃ κ₁ ⊕ κ₂)
    (V₁ : Matrix ι κ₁ 𝕜)
    (h₁ : V₁ᴴ * V₁ = (1 : Matrix κ₁ κ₁ 𝕜)) :
    ∃ (V₂ : Matrix ι κ₂ 𝕜) (V : Matrix ι (κ₁ ⊕ κ₂) 𝕜),
      V = V₁.fromCols V₂ ∧
      (V.submatrix id e) ∈ unitaryGroup ι 𝕜 := by
  -- This is the transposed version of `exists_unitary_completion_matrix_col`
  -- But we prove it using the conjTranpose instead of the transpose
  -- because it is inconvenient to tackle identities like `Aᵀᴴ = Aᴴᵀ`

  let p := exists_unitary_completion_matrix_row e V₁ᴴ
  simp [h₁] at p
  obtain ⟨V₂', h2⟩ := p

  use V₂'ᴴ
  simp [mem_unitaryGroup_iff']
  simp [mem_unitaryGroup_iff'] at h2
  change ((V₁.fromCols V₂'ᴴ).submatrix id ⇑e)ᴴ * (V₁.fromCols V₂'ᴴ).submatrix id ⇑e = 1
  simp [← conjTranspose_eq_one,
    conjTranspose_fromCols_eq_fromRows_conjTranspose]
  simp [conjTranspose_submatrix]
  rw [mul_eq_one_comm]
  exact h2

@[inherit_doc exists_unitary_completion_matrix_col]
alias exists_unitary_completion_matrix := exists_unitary_completion_matrix_col


end Theorem_2_1_1

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 V]

/-- Define Operator Norm for LinearMap between FiniteDimensional Space -/
@[simp]
noncomputable def opNorm [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) : ℝ :=
  ‖LinearMap.toContinuousLinearMap T‖

-- **Parseval's identity**:
-- If `v : ι → V` is an orthonormal basis of a finite-dimensional inner product
-- space `V` over `𝕜`, then for any vector `u : V`,
-- the squared norm of `u` equals the sum of squares of its Fourier coefficients.
#check OrthonormalBasis.sum_sq_norm_inner_right


/-- Any vector can be uniquely decomposed as a sum of a vector in a subspace and
one in its orthogonal complement. -/
lemma exists_orthogonal_decompose (s : Submodule 𝕜 V) (x : V) :
  ∃ x₁ ∈ s, ∃ x₂ ∈ s.orthogonal, x = x₁ + x₂ :=
by
  use s.starProjection x
  simp [Submodule.starProjection_apply_mem s x]
  use x - s.starProjection x
  simp

omit [FiniteDimensional 𝕜 V] in
/-- The squared norm of a linear combination of an orthonormal family equals the
sum of the squared coefficients. -/
lemma Orthonormal.linearCombo_norm_sq {ι : Type*} [Fintype ι]
  (v : ι → V) (hv : Orthonormal 𝕜 v) (a : ι → 𝕜) :
  ‖∑ i, a i • v i‖ ^ 2 = ∑ i, ‖a i‖^2 :=
by
  rw [norm_sq_eq_re_inner (𝕜:=𝕜), sum_inner]
  simp
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_sq_eq_re_inner (𝕜:=𝕜)]
  congr
  simp [inner_smul_left, Orthonormal.inner_right_fintype, hv]
  ring



/-- If a linear map vanishes on the orthogonal complement of a subspace, the
squared norm of Tx equals that of its component in the subspace. -/
lemma norm_sq_of_orthogonal_complement_zero
  {T : V →ₗ[𝕜] W} {s : Submodule 𝕜 V} (x : V)
  (hker : s.orthogonal ≤ LinearMap.ker T) :
  ∃ x₁ ∈ s, ∃ x₂ ∈ s.orthogonal,
    x = x₁ + x₂ ∧ ‖T x‖^2 = ‖T x₁‖^2 :=
by
  let ⟨x₁, hx₁, x₂, hx₂, hx⟩ := exists_orthogonal_decompose s x
  refine ⟨x₁, hx₁, x₂, hx₂, hx, ?_⟩
  rw [hx, LinearMap.map_add]
  suffices T x₂ = 0 from by
    rw [this, add_zero, norm_sq_eq_re_inner (𝕜:=𝕜)]
  exact LinearMap.mem_ker.mp (hker hx₂)


omit [FiniteDimensional 𝕜 V] in
/--
If an index set of vetors is orthonormal, then any restriction of it is also orthonormal.
-/
@[simp]
lemma Set.restrict_orthonormal_of_orthonormal {ι} {s : Set ι} {v : ι → V}
  (hv : Orthonormal 𝕜 v) : Orthonormal 𝕜 (s.restrict v) := by
  simp [Orthonormal, Pairwise] at *
  aesop

omit [FiniteDimensional 𝕜 V] in
/--
If `v : ι → V` is orthonormal, then there exists an orthonormal basis which equals to `v`
-/
@[simp]
lemma Orthonormal.exists_orthonormalBasis_span_range [Fintype ι] {v : ι → V}
    (hv : Orthonormal 𝕜 v) : ∃ b : OrthonormalBasis ι 𝕜 (Submodule.span 𝕜 (Set.range v)),
    ∀ i, b i = v i := by
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range v)) := by
    apply FiniteDimensional.span_of_finite
    simp [Set.finite_range]

  have : Submodule.HasOrthogonalProjection (Submodule.span 𝕜 (Set.range v)) := by
    apply Submodule.HasOrthogonalProjection.ofCompleteSpace (Submodule.span 𝕜 (Set.range v))


  let b : OrthonormalBasis ι 𝕜 (Submodule.span 𝕜 (Set.range v)) := by
    refine OrthonormalBasis.mkOfOrthogonalEqBot (v := ?v') ?_ ?_
    · intro i
      use v i
      simp [Submodule.mem_span_of_mem]
    · simp [Submodule.orthonormal_iff]
      exact hv
    · simp [Submodule.eq_top_iff']
      intro u h
      simp [Submodule.mem_span_range_iff_exists_fun] at h
      simp [Submodule.mem_span_range_iff_exists_fun, Subtype.eq_iff, h]

  use b

  simp [b]

end Matrix
