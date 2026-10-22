module
public import Mathlib
public import ArithmeticLorentz.Counting
public import ArithmeticLorentz.Arithmetic
public import ArithmeticLorentz.Qubit

@[expose] public section
/-!
# The exclusion theorem on `Herm_n(ℂ)`

`Herm_n(ℂ)` has the place shape `ℝ^n × ℂ^{n(n−1)/2}`: the diagonal is real, and the strict upper
triangle `Upper n = {(i, j) | i < j}` carries one complex coordinate per pair (the lower entry
`X_{ji}`; the upper entry is its conjugate). Under that real-linear isomorphism,

* `X ↦ tr(XXᵀ)` is the place form `Σ x_i² + Σ 2 Re(z_p²)`, so its type is
  `(n(n+1)/2, n(n−1)/2)`;
* `X ↦ tr(XX)` (Hilbert–Schmidt) is `Σ x_i² + Σ 2 |z_p|²`, positive definite.

**The exclusion**: `tr(XXᵀ)` on `Herm_n(ℂ)` has exactly one negative direction iff `n = 2`; then
its type is `(3, 1)` and `dim_ℝ Herm₂(ℂ) = 4`.
-/

namespace HermitianExclusion

open Matrix ComplexConjugate QuadraticForm QuadraticMap Finset

/-- The strict upper triangle `{(i, j) : i < j}` of `Fin n × Fin n`. -/
abbrev Upper (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- `#{(i, j) : i < j} = n(n−1)/2`. -/
theorem card_upper (n : ℕ) : Fintype.card (Upper n) = n * (n - 1) / 2 := by
  classical
  rw [Fintype.card_subtype, card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ j : Fin n, (∑ i : Fin n, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← card_filter, filter_gt_eq_Iio, Fin.card_Iio]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, sum_range_id]

/-- Splitting a double sum over `Fin n × Fin n` into the diagonal and the two triangles. -/
theorem sum_sum_eq_diag_add_upper {n : ℕ} {β : Type*} [AddCommMonoid β] (f : Fin n → Fin n → β) :
    ∑ i, ∑ j, f i j = ∑ i, f i i + ∑ p : Upper n, (f p.1.1 p.1.2 + f p.1.2 p.1.1) := by
  classical
  have h1 : ∀ q : Fin n × Fin n, f q.1 q.2 =
      ((if q.1 < q.2 then f q.1 q.2 else 0) + (if q.2 < q.1 then f q.1 q.2 else 0)) +
        (if q.1 = q.2 then f q.1 q.2 else 0) := by
    rintro ⟨i, j⟩
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have hdiag : ∑ q : Fin n × Fin n, (if q.1 = q.2 then f q.1 q.2 else 0) = ∑ i, f i i := by
    rw [Fintype.sum_prod_type]
    simp
  have hup : ∑ q : Fin n × Fin n, (if q.1 < q.2 then f q.1 q.2 else 0) =
      ∑ p : Upper n, f p.1.1 p.1.2 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (p := fun q : Fin n × Fin n => q.1 < q.2) _ (by simp)
      (fun q : Fin n × Fin n => f q.1 q.2)
  have hlow : ∑ q : Fin n × Fin n, (if q.2 < q.1 then f q.1 q.2 else 0) =
      ∑ p : Upper n, f p.1.2 p.1.1 := by
    rw [Fintype.sum_equiv (Equiv.prodComm _ _)
      (fun q : Fin n × Fin n => if q.2 < q.1 then f q.1 q.2 else 0)
      (fun q => if q.1 < q.2 then f q.2 q.1 else 0) (fun q => rfl), ← Finset.sum_filter]
    exact Finset.sum_subtype (p := fun q : Fin n × Fin n => q.1 < q.2) _ (by simp)
      (fun q : Fin n × Fin n => f q.2 q.1)
  rw [← Fintype.sum_prod_type', Finset.sum_congr rfl (fun q _ => h1 q), sum_add_distrib,
    sum_add_distrib, hdiag, hup, hlow, ← sum_add_distrib, add_comm]

/-- The Hermitian matrix with real diagonal `x` and lower entries `X_{ji} = z(i, j)` (`i < j`). -/
def hermMatrix {n : ℕ} (x : Fin n → ℝ) (z : Upper n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j =>
    if h : i < j then conj (z ⟨(i, j), h⟩) else if h' : j < i then z ⟨(j, i), h'⟩ else (x i : ℂ)

section hermMatrix

variable {n : ℕ} (x : Fin n → ℝ) (z : Upper n → ℂ)

@[simp] theorem hermMatrix_diag (i : Fin n) : hermMatrix x z i i = (x i : ℂ) := by
  simp [hermMatrix]

@[simp] theorem hermMatrix_upper (p : Upper n) : hermMatrix x z p.1.1 p.1.2 = conj (z p) := by
  simp [hermMatrix, p.2]

@[simp] theorem hermMatrix_lower (p : Upper n) : hermMatrix x z p.1.2 p.1.1 = z p := by
  simp [hermMatrix, p.2, not_lt.mpr p.2.le]

theorem hermMatrix_isHermitian : (hermMatrix x z).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, hermMatrix, of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le]
  · simp
  · simp [h, not_lt.mpr h.le]

end hermMatrix

/-- **The place isomorphism of `Herm_n(ℂ)`**: `ℝ^n × ℂ^{Upper n} ≃ Herm_n(ℂ)`, real-linear. -/
def hermEquiv (n : ℕ) : ((Fin n → ℝ) × (Upper n → ℂ)) ≃ₗ[ℝ] herm n where
  toFun p := ⟨hermMatrix p.1 p.2, hermMatrix_isHermitian _ _⟩
  invFun X := (fun i => (X.1 i i).re, fun p => X.1 p.1.2 p.1.1)
  map_add' p q := by
    apply Subtype.ext
    ext i j
    simp only [hermMatrix, of_apply, Submodule.coe_add, Matrix.add_apply, Prod.fst_add,
      Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c p := by
    apply Subtype.ext
    ext i j
    simp only [hermMatrix, of_apply, Submodule.coe_smul, Matrix.smul_apply, Prod.smul_fst,
      Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul]
  left_inv p := by
    rcases p with ⟨x, z⟩
    refine Prod.ext ?_ ?_
    · funext i; simp
    · funext p; simp
  right_inv X := by
    obtain ⟨X, hX⟩ := X
    apply Subtype.ext
    ext i j
    simp only [hermMatrix, of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [h, ↓reduceDIte]
      have := hX.apply i j
      rwa [Complex.star_def] at this
    · simp [diag_re_of_isHermitian hX]
    · simp only [not_lt.mpr h.le, h, ↓reduceDIte]

theorem hermEquiv_apply_coe {n : ℕ} (p : (Fin n → ℝ) × (Upper n → ℂ)) :
    (hermEquiv n p : Matrix (Fin n) (Fin n) ℂ) = hermMatrix p.1 p.2 := rfl

/-- Under the place isomorphism, `Re tr(XXᵀ)` is the place form `Σ x_i² + Σ 2 Re(z_p²)`. -/
theorem transposeForm_hermEquiv {n : ℕ} (p : (Fin n → ℝ) × (Upper n → ℂ)) :
    transposeForm n (hermEquiv n p) = placeForm (Fin n) (Upper n) p := by
  rcases p with ⟨x, z⟩
  rw [transposeForm_apply, hermEquiv_apply_coe, placeForm_apply]
  have htr : trace (hermMatrix x z * (hermMatrix x z)ᵀ) =
      ∑ i, ∑ j, hermMatrix x z i j * hermMatrix x z i j := by
    simp [trace, Matrix.mul_apply]
  rw [htr, sum_sum_eq_diag_add_upper]
  simp only [hermMatrix_diag, hermMatrix_upper, hermMatrix_lower, Complex.add_re,
    Complex.re_sum]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, pow_two]
  · refine sum_congr rfl fun q _ => ?_
    rw [← map_mul, Complex.conj_re, pow_two]
    ring

/-- Under the place isomorphism, `Re tr(XX)` is the Born place form `Σ x_i² + Σ 2 |z_p|²`. -/
theorem hsForm_hermEquiv {n : ℕ} (p : (Fin n → ℝ) × (Upper n → ℂ)) :
    hsForm n (hermEquiv n p) = bornPlaceForm (Fin n) (Upper n) p := by
  rcases p with ⟨x, z⟩
  rw [hsForm_apply, hermEquiv_apply_coe, bornPlaceForm_apply]
  have htr : trace (hermMatrix x z * hermMatrix x z) =
      ∑ i, ∑ j, hermMatrix x z i j * hermMatrix x z j i := by
    simp [trace, Matrix.mul_apply]
  rw [htr, sum_sum_eq_diag_add_upper]
  simp only [hermMatrix_diag, hermMatrix_upper, hermMatrix_lower, Complex.add_re,
    Complex.re_sum]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, pow_two]
  · refine sum_congr rfl fun q _ => ?_
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring

theorem placeForm_equivalent_transposeForm_n (n : ℕ) :
    (placeForm (Fin n) (Upper n)).Equivalent (transposeForm n) :=
  ⟨{ hermEquiv n with map_app' := transposeForm_hermEquiv }⟩

theorem bornPlaceForm_equivalent_hsForm_n (n : ℕ) :
    (bornPlaceForm (Fin n) (Upper n)).Equivalent (hsForm n) :=
  ⟨{ hermEquiv n with map_app' := hsForm_hermEquiv }⟩

/-- **The transpose-twisted trace form on `Herm_n(ℂ)` has type `(n(n+1)/2, n(n−1)/2)`.** -/
theorem transposeForm_signature (n : ℕ) :
    sigPos (transposeForm n) = n * (n + 1) / 2 ∧ sigNeg (transposeForm n) = n * (n - 1) / 2 := by
  have h := placeForm_signature (ι₁ := Fin n) (ι₂ := Upper n)
  rw [(placeForm_equivalent_transposeForm_n n).sigPos_eq,
    (placeForm_equivalent_transposeForm_n n).sigNeg_eq, card_upper, Fintype.card_fin,
    add_choose_two] at h
  exact h

/-- **The Hilbert–Schmidt (Born) form on `Herm_n(ℂ)` is positive definite**: type `(n², 0)`. -/
theorem hsForm_signature (n : ℕ) :
    sigPos (hsForm n) = n * n ∧ sigNeg (hsForm n) = 0 := by
  have h := bornPlaceForm_signature (ι₁ := Fin n) (ι₂ := Upper n)
  rw [(bornPlaceForm_equivalent_hsForm_n n).sigPos_eq,
    (bornPlaceForm_equivalent_hsForm_n n).sigNeg_eq, card_upper, Fintype.card_fin,
    add_two_mul_choose_two] at h
  exact h

/-- `dim_ℝ Herm_n(ℂ) = n²`. -/
theorem finrank_herm (n : ℕ) : Module.finrank ℝ (herm n) = n * n := by
  rw [← (hermEquiv n).finrank_eq, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, sum_const, card_univ, card_upper, smul_eq_mul]
  rw [mul_comm _ 2, add_two_mul_choose_two]

/-- **The exclusion theorem.** Among the Hermitian matrix spaces `Herm_n(ℂ)`, the
transpose-twisted trace form `X ↦ tr(XXᵀ)` has exactly one negative direction iff `n = 2`. -/
theorem sigNeg_transposeForm_eq_one_iff (n : ℕ) : sigNeg (transposeForm n) = 1 ↔ n = 2 := by
  rw [(transposeForm_signature n).2, choose_two_eq_one_iff]

/-- **The exclusion theorem, full form.** One negative direction forces the qubit: `n = 2`,
type `(3, 1)`, real dimension `4`. -/
theorem hermitian_exclusion (n : ℕ) (h : sigNeg (transposeForm n) = 1) :
    n = 2 ∧ sigPos (transposeForm n) = 3 ∧ Module.finrank ℝ (herm n) = 4 := by
  have hn := (sigNeg_transposeForm_eq_one_iff n).mp h
  subst hn
  exact ⟨rfl, transposeForm_two_signature.1, by rw [finrank_herm]⟩

end HermitianExclusion
