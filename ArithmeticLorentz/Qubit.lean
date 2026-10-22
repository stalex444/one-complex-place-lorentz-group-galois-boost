module
public import Mathlib
public import ArithmeticLorentz.Defs
public import ArithmeticLorentz.Counting

@[expose] public section
/-!
# (c) The qubit: `Herm₂(ℂ)` with the explicit place isomorphism

A quartic number field with two real places and one complex place (`r₁ = 2`, `r₂ = 1`; for
`ℚ(Q)`, the real places at `Q` and `q′` and the complex place `σ`) has real Minkowski space
`ℝ × ℝ × ℂ ∋ (x_Q, x_{q′}, x_σ)`. The place isomorphism is

  `X = [[x_Q, conj x_σ], [x_σ, x_{q′}]]`,

a real-linear isomorphism onto `Herm₂(ℂ)`. With the four complex embeddings
`τ ∈ {Q, q′, σ, σ̄}` (values `x_Q, x_{q′}, x_σ, conj x_σ`):

* the Born form `Σ_τ x_τ conj(y_τ)` is the Hilbert–Schmidt form `tr(XY)`;
* the trace form `Σ_τ x_τ y_τ` (which is `Tr_{K/ℚ}(xy)` for the field) is `tr(XYᵀ)`;
* their difference on the diagonal is `4 (Im x_σ)²`, and `X − Xᵀ = 2 Im(x_σ) σ_y`;
* `X ↦ tr(XXᵀ)` on `Herm₂(ℂ)` has type `(3, 1)`: `sigPos = 3`, `sigNeg = 1`;
* `X ↦ tr(XX)` on `Herm₂(ℂ)` is positive definite (`sigPos = 4`, `sigNeg = 0`).

The identification of the place algebra with a physical qubit is not a theorem of this file.
-/

namespace HermitianExclusion

open Matrix ComplexConjugate QuadraticForm QuadraticMap Finset

/-! ### `Herm_n(ℂ)` and its two trace forms (defined in `Defs.lean`) -/

theorem mem_herm {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ herm n ↔ X.IsHermitian := Iff.rfl

theorem transposeBilin_apply {n : ℕ} (X Y : herm n) :
    transposeBilin n X Y = (trace (X.1 * (Y.1)ᵀ)).re := rfl

theorem hsBilin_apply {n : ℕ} (X Y : herm n) : hsBilin n X Y = (trace (X.1 * Y.1)).re := rfl

theorem transposeForm_apply {n : ℕ} (X : herm n) :
    transposeForm n X = (trace (X.1 * (X.1)ᵀ)).re := rfl

theorem hsForm_apply {n : ℕ} (X : herm n) : hsForm n X = (trace (X.1 * X.1)).re := rfl

/-! ### The place matrix (defined in `Defs.lean`) -/

/-- The four complex embeddings `τ ∈ {Q, q′, σ, σ̄}` evaluated on the place vector. -/
def emb (xQ xq : ℝ) (xσ : ℂ) : Fin 4 → ℂ := ![(xQ : ℂ), (xq : ℂ), xσ, conj xσ]

theorem placeMatrix_transpose (xQ xq : ℝ) (xσ : ℂ) :
    (placeMatrix xQ xq xσ)ᵀ = !![(xQ : ℂ), xσ; conj xσ, (xq : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **Born form = Hilbert–Schmidt.** `Σ_τ x_τ conj(y_τ) = tr(XY)`. -/
theorem trace_placeMatrix_mul (xQ xq yQ yq : ℝ) (xσ yσ : ℂ) :
    trace (placeMatrix xQ xq xσ * placeMatrix yQ yq yσ) =
      ∑ τ, emb xQ xq xσ τ * conj (emb yQ yq yσ τ) := by
  simp [placeMatrix, emb, Matrix.trace_fin_two, Fin.sum_univ_four]
  ring

/-- **Trace form = transpose-twisted Hilbert–Schmidt.** `Σ_τ x_τ y_τ = tr(XYᵀ)`. -/
theorem trace_placeMatrix_mul_transpose (xQ xq yQ yq : ℝ) (xσ yσ : ℂ) :
    trace (placeMatrix xQ xq xσ * (placeMatrix yQ yq yσ)ᵀ) =
      ∑ τ, emb xQ xq xσ τ * emb yQ yq yσ τ := by
  rw [placeMatrix_transpose]
  simp [placeMatrix, emb, Matrix.trace_fin_two, Fin.sum_univ_four]
  ring

/-- The Born form in real coordinates: `x_Q y_Q + x_{q′} y_{q′} + 2 Re(x_σ conj y_σ)`. -/
theorem born_real (xQ xq yQ yq : ℝ) (xσ yσ : ℂ) :
    ∑ τ, emb xQ xq xσ τ * conj (emb yQ yq yσ τ) =
      ((xQ * yQ + xq * yq + 2 * (xσ * conj yσ).re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [emb, Fin.sum_univ_succ] <;> ring

/-- The trace form in real coordinates: `x_Q y_Q + x_{q′} y_{q′} + 2 Re(x_σ y_σ)`. -/
theorem trace_real (xQ xq yQ yq : ℝ) (xσ yσ : ℂ) :
    ∑ τ, emb xQ xq xσ τ * emb yQ yq yσ τ =
      ((xQ * yQ + xq * yq + 2 * (xσ * yσ).re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [emb, Fin.sum_univ_succ] <;> ring

/-- **The difference is the imaginary part of the coherence**: `tr(XX) − tr(XXᵀ) = 4 (Im x_σ)²`. -/
theorem trace_sq_sub_trace_mul_transpose (xQ xq : ℝ) (xσ : ℂ) :
    trace (placeMatrix xQ xq xσ * placeMatrix xQ xq xσ) -
        trace (placeMatrix xQ xq xσ * (placeMatrix xQ xq xσ)ᵀ) = 4 * (xσ.im : ℂ) ^ 2 := by
  rw [trace_placeMatrix_mul, trace_placeMatrix_mul_transpose]
  apply Complex.ext <;> simp [emb, Fin.sum_univ_succ, pow_two] <;> ring

/-- The Pauli matrix `σ_y = [[0, −i], [i, 0]]`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- **The single time direction is `σ_y`**: the antisymmetric part of `X` is `2 Im(x_σ) σ_y`. -/
theorem placeMatrix_sub_transpose (xQ xq : ℝ) (xσ : ℂ) :
    placeMatrix xQ xq xσ - (placeMatrix xQ xq xσ)ᵀ = (2 * xσ.im : ℝ) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> simp [placeMatrix, pauliY] <;> ring

/-! ### Multiplication: the Schur (entrywise) product, not the matrix product -/

/-- **Place-wise multiplication is the Schur product of place matrices**:
`X(xy) = X(x) ⊙ X(y)`. -/
theorem placeMatrix_mul_hadamard (xQ xq yQ yq : ℝ) (xσ yσ : ℂ) :
    placeMatrix (xQ * yQ) (xq * yq) (xσ * yσ) =
      hadamard (placeMatrix xQ xq xσ) (placeMatrix yQ yq yσ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [placeMatrix, hadamard_apply]

/-- **The matrix product does not preserve the place image**: `X(1,0,0) · X(0,0,1)` is not
Hermitian, so it is the place matrix of no element. (The place isomorphism is a real-linear
isometry for both forms, not an algebra map for the matrix product.) -/
theorem placeMatrix_mul_not_isHermitian :
    ¬ (placeMatrix 1 0 0 * placeMatrix 0 0 1).IsHermitian := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [placeMatrix, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply] at h01

theorem placeEquiv_apply_coe (p : (Fin 2 → ℝ) × (Fin 1 → ℂ)) :
    (placeEquiv p : Matrix (Fin 2) (Fin 2) ℂ) = placeMatrix (p.1 0) (p.1 1) (p.2 0) := rfl

/-- Under the place isomorphism, `Re tr(XXᵀ)` is the place form `x_Q² + x_{q′}² + 2 Re(x_σ²)`. -/
theorem transposeForm_placeEquiv (p : (Fin 2 → ℝ) × (Fin 1 → ℂ)) :
    transposeForm 2 (placeEquiv p) = placeForm (Fin 2) (Fin 1) p := by
  rcases p with ⟨x, z⟩
  rw [transposeForm_apply, placeEquiv_apply_coe, placeForm_apply,
    trace_placeMatrix_mul_transpose, trace_real]
  simp [Fin.sum_univ_two, pow_two]

/-- `Re tr(XXᵀ)` on `Herm₂(ℂ)` is isometric to the place form of the quartic shape `(2, 1)`. -/
theorem placeForm_equivalent_transposeForm :
    (placeForm (Fin 2) (Fin 1)).Equivalent (transposeForm 2) :=
  ⟨{ placeEquiv with map_app' := transposeForm_placeEquiv }⟩

/-- **(c) The qubit's transpose-twisted trace form is Lorentzian**: on `Herm₂(ℂ)`,
`X ↦ tr(XXᵀ)` has `sigPos = 3` and `sigNeg = 1`. -/
theorem transposeForm_two_signature :
    sigPos (transposeForm 2) = 3 ∧ sigNeg (transposeForm 2) = 1 := by
  have h := placeForm_signature (ι₁ := Fin 2) (ι₂ := Fin 1)
  rw [placeForm_equivalent_transposeForm.sigPos_eq,
    placeForm_equivalent_transposeForm.sigNeg_eq] at h
  simpa using h

theorem sigNeg_transposeForm_two : sigNeg (transposeForm 2) = 1 :=
  transposeForm_two_signature.2

/-- Under the place isomorphism, `Re tr(XX)` is the Born place form
`x_Q² + x_{q′}² + 2 |x_σ|²`. -/
theorem hsForm_placeEquiv (p : (Fin 2 → ℝ) × (Fin 1 → ℂ)) :
    hsForm 2 (placeEquiv p) = bornPlaceForm (Fin 2) (Fin 1) p := by
  rcases p with ⟨x, z⟩
  rw [hsForm_apply, placeEquiv_apply_coe, bornPlaceForm_apply, trace_placeMatrix_mul, born_real]
  simp [Fin.sum_univ_two, pow_two, Complex.normSq_apply, Complex.mul_re]

theorem bornPlaceForm_equivalent_hsForm :
    (bornPlaceForm (Fin 2) (Fin 1)).Equivalent (hsForm 2) :=
  ⟨{ placeEquiv with map_app' := hsForm_placeEquiv }⟩

/-- **The Born (Hilbert–Schmidt) form on `Herm₂(ℂ)` is positive definite**: type `(4, 0)`. -/
theorem hsForm_two_signature : sigPos (hsForm 2) = 4 ∧ sigNeg (hsForm 2) = 0 := by
  have h := bornPlaceForm_signature (ι₁ := Fin 2) (ι₂ := Fin 1)
  rw [bornPlaceForm_equivalent_hsForm.sigPos_eq, bornPlaceForm_equivalent_hsForm.sigNeg_eq] at h
  simpa using h

/-- The two forms on `Herm₂(ℂ)` differ by `4 (Im x_σ)²`, the square of the `σ_y` coordinate. -/
theorem hsForm_sub_transposeForm (p : (Fin 2 → ℝ) × (Fin 1 → ℂ)) :
    hsForm 2 (placeEquiv p) - transposeForm 2 (placeEquiv p) = 4 * (p.2 0).im ^ 2 := by
  rw [hsForm_apply, transposeForm_apply, placeEquiv_apply_coe, ← Complex.sub_re,
    trace_sq_sub_trace_mul_transpose]
  simp [pow_two]

end HermitianExclusion
