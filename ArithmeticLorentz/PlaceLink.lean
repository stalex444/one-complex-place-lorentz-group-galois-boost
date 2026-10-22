module
public import Mathlib
public import ArithmeticLorentz.Counting
public import ArithmeticLorentz.Qubit
public import ArithmeticLorentz.Arithmetic

@[expose] public section
/-!
# The number-field link: the trace form IS the place form; for `(r₁, r₂) = (2, 1)`, `tr(XYᵀ)`

For any number field `K`, through Mathlib's mixed embedding `K → ℝ^{r₁} × ℂ^{r₂}`,

  `Tr_{K/ℚ}(xy) = Σ_{w real} x_w y_w + Σ_{w complex} 2 Re(x_w y_w)`,

so `Tr_{K/ℚ}(x²)` is the place form of the counting statement (a) evaluated at the mixed
embedding of `x`. The sum of the complex embeddings `Σ_φ φ(x) conj φ(y)` (the Born form) is
likewise `Σ_{w real} x_w y_w + Σ_{w complex} 2 Re(x_w conj y_w)`.

For a number field with two real places and one complex place (the shape of `ℚ(Q)`,
`Q⁴ = Q + 1`), the place isomorphism `ℝ² × ℂ ≃ Herm₂(ℂ)` turns these into
`Tr_{K/ℚ}(xy) = Re tr(X Yᵀ)` and `Σ_φ φ(x) conj φ(y) = tr(X Y)`, with `X` the place matrix of `x`.
The two real places and the complex place are labelled by enumerations
`e₁ : {real places} ≃ Fin 2`, `e₂ : {complex places} ≃ Fin 1`, which exist iff `(r₁, r₂) = (2, 1)`
(`Fintype.equivFinOfCardEq`); every statement is proved for every labelling.
-/

namespace HermitianExclusion

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Finset ComplexConjugate
  QuadraticForm Matrix

open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

/-- The embeddings above an infinite place `w` are `embedding w` and its conjugate (one of them
if `w` is real). -/
theorem filter_mk_eq (w : InfinitePlace K) :
    ({φ | mk φ = w} : Finset (K →+* ℂ)) =
      {embedding w, ComplexEmbedding.conjugate (embedding w)} := by
  ext φ
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  conv_lhs => rw [← mk_embedding w]
  rw [mk_eq_iff, ComplexEmbedding.conjugate, star_involutive.eq_iff]

/-- A sum over the embeddings above `w`. -/
theorem sum_filter_mk_eq {M : Type*} [AddCommMonoid M] (w : InfinitePlace K)
    (g : (K →+* ℂ) → M) :
    ∑ φ ∈ ({φ | mk φ = w} : Finset (K →+* ℂ)), g φ =
      if IsReal w then g (embedding w)
      else g (embedding w) + g (ComplexEmbedding.conjugate (embedding w)) := by
  rw [filter_mk_eq]
  split_ifs with hw
  · rw [conjugate_embedding_eq_of_isReal hw, insert_eq_of_mem (mem_singleton_self _),
      sum_singleton]
  · have hne : embedding w ≠ ComplexEmbedding.conjugate (embedding w) := fun h =>
      hw (isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [sum_pair hne]

/-- A sum over all complex embeddings, regrouped by infinite places. -/
theorem sum_embeddings_eq {M : Type*} [AddCommMonoid M] (g : (K →+* ℂ) → M) :
    ∑ φ : K →+* ℂ, g φ =
      ∑ w : {w : InfinitePlace K // IsReal w}, g (embedding w.1) +
        ∑ w : {w : InfinitePlace K // IsComplex w},
          (g (embedding w.1) + g (ComplexEmbedding.conjugate (embedding w.1))) := by
  rw [← Finset.sum_fiberwise univ mk g, sum_eq_sum_add_sum]
  congr 1
  · exact sum_congr rfl fun w _ => by
      rw [sum_filter_mk_eq]
      simp only [w.2, ↓reduceIte]
  · exact sum_congr rfl fun w _ => by
      have hw : ¬IsReal w.1 := not_isReal_iff_isComplex.mpr w.2
      rw [sum_filter_mk_eq]
      simp only [hw, ↓reduceIte]

omit [NumberField K] in
theorem embedding_eq_ofReal {w : InfinitePlace K} (hw : IsReal w) (x : K) :
    embedding w x = ((embedding_of_isReal hw x : ℝ) : ℂ) :=
  (embedding_of_isReal_apply hw x).symm

/-- **The trace as a sum over places**: `Tr(y) = Σ_{w real} y_w + Σ_{w complex} 2 Re(y_w)`. -/
theorem trace_eq_sum_places (y : K) :
    ((Algebra.trace ℚ K y : ℚ) : ℂ) =
      ∑ w : {w : InfinitePlace K // IsReal w}, ((embedding_of_isReal w.2 y : ℝ) : ℂ) +
        ∑ w : {w : InfinitePlace K // IsComplex w}, ((2 * (embedding w.1 y).re : ℝ) : ℂ) := by
  have h := _root_.trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := y)
  rw [eq_ratCast] at h
  rw [h, ← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ y) (fun σ => σ y)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), sum_embeddings_eq]
  congr 1
  · exact sum_congr rfl fun w _ => embedding_eq_ofReal w.2 y
  · refine sum_congr rfl fun w _ => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj, Complex.ofReal_mul,
      Complex.ofReal_ofNat]

/-- **The trace form in place coordinates**:
`Tr_{K/ℚ}(xy) = Σ_{w real} x_w y_w + Σ_{w complex} 2 Re(x_w y_w)`, with `x_w` the coordinates of the
mixed embedding. -/
theorem trace_mul_eq (x y : K) :
    ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) =
      ∑ w, (mixedEmbedding K x).1 w * (mixedEmbedding K y).1 w +
        ∑ w, 2 * ((mixedEmbedding K x).2 w * (mixedEmbedding K y).2 w).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, trace_eq_sum_places]
  push_cast
  simp [mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex, map_mul]

/-- **The Born form in place coordinates**: `Σ_φ φ(x) conj φ(y) =
Σ_{w real} x_w y_w + Σ_{w complex} 2 Re(x_w conj y_w)`. -/
theorem born_eq (x y : K) :
    ∑ φ : K →+* ℂ, φ x * conj (φ y) =
      ((∑ w, (mixedEmbedding K x).1 w * (mixedEmbedding K y).1 w +
        ∑ w, 2 * ((mixedEmbedding K x).2 w * conj ((mixedEmbedding K y).2 w)).re : ℝ) : ℂ) := by
  rw [sum_embeddings_eq]
  push_cast
  congr 1
  · refine sum_congr rfl fun w _ => ?_
    rw [embedding_eq_ofReal w.2 x, embedding_eq_ofReal w.2 y, Complex.conj_ofReal]
    simp [mixedEmbedding_apply_isReal]
  · refine sum_congr rfl fun w _ => ?_
    have key : ∀ a b : ℂ, a * conj b + conj a * conj (conj b) = 2 * ((a * conj b).re : ℂ) := by
      intro a b; apply Complex.ext <;> simp <;> ring
    simp only [ComplexEmbedding.conjugate_coe_eq, mixedEmbedding_apply_isComplex]
    exact key _ _

/-- **Born minus trace is the imaginary part of the complex coordinates**:
`Σ_φ |φ(x)|² − Tr_{K/ℚ}(x²) = Σ_{w complex} 4 (Im x_w)²`. -/
theorem born_sub_trace (x : K) :
    ∑ φ : K →+* ℂ, φ x * conj (φ x) - ((Algebra.trace ℚ K (x * x) : ℚ) : ℂ) =
      ((∑ w, 4 * ((mixedEmbedding K x).2 w).im ^ 2 : ℝ) : ℂ) := by
  rw [born_eq, ← Complex.ofReal_ratCast, trace_mul_eq, ← Complex.ofReal_sub,
    add_sub_add_left_eq_sub, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun w _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **`Tr_{K/ℚ}(x²)` is the place form of the counting statement (a)** at the mixed embedding. -/
theorem trace_sq_eq_placeForm (x : K) :
    ((Algebra.trace ℚ K (x * x) : ℚ) : ℝ) =
      placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w}
        (mixedEmbedding K x) := by
  rw [trace_mul_eq]
  rw [show mixedEmbedding K x = ((mixedEmbedding K x).1, (mixedEmbedding K x).2) from rfl,
    placeForm_apply]
  simp [pow_two]

/-- (a) applied to the Minkowski space of `K`: the place form there has type
`(r₁ + r₂, r₂)` (the trace-form signature over `ℚ` is the registered `traceForm_signature`). -/
theorem placeForm_mixedSpace_signature :
    sigPos (placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w}) =
        nrRealPlaces K + nrComplexPlaces K ∧
      sigNeg (placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w}) =
        nrComplexPlaces K :=
  placeForm_signature

/-! ### The quartic shape `(r₁, r₂) = (2, 1)`: the place isomorphism onto `Herm₂(ℂ)` -/

section Quartic

variable (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
  (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1)

/-- Labellings exist exactly for the shape `(r₁, r₂) = (2, 1)`. -/
theorem nonempty_labelling_iff :
    (Nonempty ({w : InfinitePlace K // IsReal w} ≃ Fin 2) ∧
      Nonempty ({w : InfinitePlace K // IsComplex w} ≃ Fin 1)) ↔
      nrRealPlaces K = 2 ∧ nrComplexPlaces K = 1 := by
  constructor
  · rintro ⟨⟨e₁⟩, ⟨e₂⟩⟩
    exact ⟨by simpa using Fintype.card_congr e₁, by simpa using Fintype.card_congr e₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨Fintype.equivFinOfCardEq h₁⟩, ⟨Fintype.equivFinOfCardEq h₂⟩⟩

/-- The place isomorphism of a number field with two real places and one complex place:
`ℝ^{real places} × ℂ^{complex place} ≃ ℝ² × ℂ ≃ Herm₂(ℂ)`. -/
noncomputable def minkowskiToHerm : mixedSpace K ≃ₗ[ℝ] herm 2 :=
  (LinearEquiv.prodCongr (LinearEquiv.funCongrLeft ℝ ℝ e₁.symm)
    (LinearEquiv.funCongrLeft ℝ ℂ e₂.symm)).trans placeEquiv

omit [NumberField K] in
/-- The place matrix of `x ∈ K`: `X = [[x_{w₁}, conj x_σ], [x_σ, x_{w₂}]]`, `w₁, w₂` the two real
places and `σ` the complex place. -/
theorem minkowskiToHerm_apply (x : K) :
    (minkowskiToHerm e₁ e₂ (mixedEmbedding K x) : Matrix (Fin 2) (Fin 2) ℂ) =
      placeMatrix (embedding_of_isReal (e₁.symm 0).2 x)
        (embedding_of_isReal (e₁.symm 1).2 x)
        (embedding (e₂.symm 0).1 x) := by
  simp [minkowskiToHerm, placeEquiv_apply_coe, LinearEquiv.funCongrLeft_apply,
    mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex]

omit [NumberField K] in
/-- **Field multiplication acts as the Schur product**: `X(xy) = X(x) ⊙ X(y)`. -/
theorem minkowskiToHerm_mul (x y : K) :
    (minkowskiToHerm e₁ e₂ (mixedEmbedding K (x * y)) : Matrix (Fin 2) (Fin 2) ℂ) =
      hadamard (minkowskiToHerm e₁ e₂ (mixedEmbedding K x) : Matrix (Fin 2) (Fin 2) ℂ)
        (minkowskiToHerm e₁ e₂ (mixedEmbedding K y) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [minkowskiToHerm_apply, minkowskiToHerm_apply, minkowskiToHerm_apply, map_mul, map_mul,
    map_mul, ← placeMatrix_mul_hadamard]

theorem sum_real_two (f : {w : InfinitePlace K // IsReal w} → ℝ) :
    ∑ w, f w = f (e₁.symm 0) +
      f (e₁.symm 1) := by
  rw [← Equiv.sum_comp e₁.symm, Fin.sum_univ_two]

theorem sum_complex_one (f : {w : InfinitePlace K // IsComplex w} → ℝ) :
    ∑ w, f w = f (e₂.symm 0) := by
  rw [← Equiv.sum_comp e₂.symm, Fin.sum_univ_one]

/-- **The trace form of the quartic shape is the transpose-twisted Hilbert–Schmidt form**:
`Tr_{K/ℚ}(xy) = Re tr(X Yᵀ)`. -/
theorem trace_mul_eq_trace_transpose (x y : K) :
    ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) =
      (trace ((minkowskiToHerm e₁ e₂ (mixedEmbedding K x) : Matrix (Fin 2) (Fin 2) ℂ) *
        (minkowskiToHerm e₁ e₂ (mixedEmbedding K y) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)).re := by
  rw [minkowskiToHerm_apply, minkowskiToHerm_apply, trace_placeMatrix_mul_transpose, trace_real,
    Complex.ofReal_re, trace_mul_eq, sum_real_two e₁, sum_complex_one e₂]
  simp [mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex]

/-- **The Born form of the quartic shape is the Hilbert–Schmidt form**:
`Σ_φ φ(x) conj φ(y) = tr(X Y)`. -/
theorem born_eq_trace_mul (x y : K) :
    ∑ φ : K →+* ℂ, φ x * conj (φ y) =
      trace ((minkowskiToHerm e₁ e₂ (mixedEmbedding K x) : Matrix (Fin 2) (Fin 2) ℂ) *
        (minkowskiToHerm e₁ e₂ (mixedEmbedding K y) : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [minkowskiToHerm_apply, minkowskiToHerm_apply, trace_placeMatrix_mul, born_real, born_eq,
    sum_real_two e₁, sum_complex_one e₂]
  simp [mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex]

/-- **`Tr_{K/ℚ}(x²) = Re tr(XXᵀ)`, the Lorentzian form of `Herm₂(ℂ)`** (type `(3, 1)` by
`transposeForm_two_signature`). -/
theorem trace_sq_eq_transposeForm (x : K) :
    ((Algebra.trace ℚ K (x * x) : ℚ) : ℝ) =
      transposeForm 2 (minkowskiToHerm e₁ e₂ (mixedEmbedding K x)) := by
  rw [transposeForm_apply, trace_mul_eq_trace_transpose e₁ e₂]

end Quartic

/-- **(b) at the level of number fields.** A number field with exactly one complex place has the
Hermitian place shape `(r₁, r₂) = (n, n(n−1)/2)` for some `n` iff it has degree `4`; then
`n = r₁ = 2`. (By Hermite–Sylvester, `traceForm_signature` of the registered entry, `r₂` is the
number of negative directions of the trace form.) -/
theorem hermitian_shape_iff_degree_four (hc : nrComplexPlaces K = 1) :
    (∃ n, nrRealPlaces K = n ∧ nrComplexPlaces K = n * (n - 1) / 2) ↔
      Module.finrank ℚ K = 4 := by
  have hdeg := card_add_two_mul_card_eq_rank K
  constructor
  · rintro ⟨n, hn₁, hn₂⟩
    have h2 : n = 2 := (choose_two_eq_one_iff n).mp (hn₂ ▸ hc)
    omega
  · intro h4
    exact ⟨2, by omega, by rw [hc]⟩

end HermitianExclusion
