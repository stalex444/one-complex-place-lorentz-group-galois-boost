module
public import Mathlib

@[expose] public section
/-!
# (a) The counting statement

On the real vector space `(ι₁ → ℝ) × (ι₂ → ℂ)` (the shape `ℝ^{r₁} × ℂ^{r₂}` of a number field's
Minkowski space, `r₁ = #ι₁`, `r₂ = #ι₂`), the quadratic form

  `Q(x, z) = Σ_i x_i² + Σ_j 2 Re(z_j²)`

has type `(r₁ + r₂, r₂)`: `sigPos Q = r₁ + r₂` and `sigNeg Q = r₂`. Each complex coordinate
`z = u + iv` contributes `2u² − 2v²`, one positive and one negative square (Sylvester's law of
inertia, Mathlib's `QuadraticForm.sigPos_of_equiv_weightedSumSquares`).
-/

namespace HermitianExclusion

open QuadraticForm QuadraticMap Finset

variable {ι₁ ι₂ : Type*}

/-- The realification `(x, z) ↦ (x_i, Re z_j, Im z_j)`, a real-linear isomorphism
`(ι₁ → ℝ) × (ι₂ → ℂ) ≃ (ι₁ ⊕ (ι₂ ⊕ ι₂) → ℝ)`. -/
def realify : ((ι₁ → ℝ) × (ι₂ → ℂ)) ≃ₗ[ℝ] (ι₁ ⊕ (ι₂ ⊕ ι₂) → ℝ) where
  toFun p := Sum.elim p.1 (Sum.elim (fun j => (p.2 j).re) (fun j => (p.2 j).im))
  invFun v := (fun i => v (Sum.inl i), fun j => ⟨v (Sum.inr (Sum.inl j)), v (Sum.inr (Sum.inr j))⟩)
  map_add' p q := by
    funext k; rcases k with i | j | j <;> simp
  map_smul' c p := by
    funext k; rcases k with i | j | j <;> simp
  left_inv p := by
    rcases p with ⟨x, z⟩
    refine Prod.ext ?_ ?_
    · funext i; simp
    · funext j; apply Complex.ext <;> simp
  right_inv v := by
    funext k; rcases k with i | j | j <;> simp

@[simp] theorem realify_inl (p : (ι₁ → ℝ) × (ι₂ → ℂ)) (i : ι₁) :
    realify p (Sum.inl i) = p.1 i := rfl
@[simp] theorem realify_inr_inl (p : (ι₁ → ℝ) × (ι₂ → ℂ)) (j : ι₂) :
    realify p (Sum.inr (Sum.inl j)) = (p.2 j).re := rfl
@[simp] theorem realify_inr_inr (p : (ι₁ → ℝ) × (ι₂ → ℂ)) (j : ι₂) :
    realify p (Sum.inr (Sum.inr j)) = (p.2 j).im := rfl

variable [Fintype ι₁] [Fintype ι₂]

/-- The weights `(1, …, 1, 2, …, 2, −2, …, −2)`. -/
def placeWeight : ι₁ ⊕ (ι₂ ⊕ ι₂) → ℝ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2) (fun _ => -2))

variable (ι₁ ι₂) in
/-- The place form `Q(x, z) = Σ_i x_i² + Σ_j 2 Re(z_j²)` on `(ι₁ → ℝ) × (ι₂ → ℂ)`. -/
noncomputable def placeForm : QuadraticForm ℝ ((ι₁ → ℝ) × (ι₂ → ℂ)) :=
  (weightedSumSquares ℝ (placeWeight (ι₁ := ι₁) (ι₂ := ι₂))).comp realify.toLinearMap

theorem placeForm_apply (x : ι₁ → ℝ) (z : ι₂ → ℂ) :
    placeForm ι₁ ι₂ (x, z) = ∑ i, x i ^ 2 + ∑ j, 2 * (z j ^ 2).re := by
  simp only [placeForm, QuadraticMap.comp_apply, weightedSumSquares_apply,
    Fintype.sum_sum_type, placeWeight, LinearEquiv.coe_coe, realify_inl, realify_inr_inl,
    realify_inr_inr, Sum.elim_inl, Sum.elim_inr, smul_eq_mul]
  rw [← sum_add_distrib]
  congr 1
  · exact sum_congr rfl fun i _ => by ring
  · refine sum_congr rfl fun j _ => ?_
    rw [_root_.sq, Complex.mul_re]
    ring

/-- `placeForm` is isometric to the weighted sum of squares with weights `placeWeight`. -/
theorem placeForm_equivalent :
    (placeForm ι₁ ι₂).Equivalent (weightedSumSquares ℝ (placeWeight (ι₁ := ι₁) (ι₂ := ι₂))) :=
  ⟨{ realify with map_app' := fun _ => rfl }⟩

theorem ncard_placeWeight_pos :
    {i | 0 < placeWeight (ι₁ := ι₁) (ι₂ := ι₂) i}.ncard =
      Fintype.card ι₁ + Fintype.card ι₂ := by
  classical
  have hset : {i | 0 < placeWeight (ι₁ := ι₁) (ι₂ := ι₂) i} =
      ↑(univ.filter fun i => 0 < placeWeight (ι₁ := ι₁) (ι₂ := ι₂) i) := by
    ext; simp
  rw [hset, Set.ncard_coe_finset, card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  norm_num [placeWeight]

theorem ncard_placeWeight_neg :
    {i | placeWeight (ι₁ := ι₁) (ι₂ := ι₂) i < 0}.ncard = Fintype.card ι₂ := by
  classical
  have hset : {i | placeWeight (ι₁ := ι₁) (ι₂ := ι₂) i < 0} =
      ↑(univ.filter fun i => placeWeight (ι₁ := ι₁) (ι₂ := ι₂) i < 0) := by
    ext; simp
  rw [hset, Set.ncard_coe_finset, card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  norm_num [placeWeight]

/-- **(a) The counting statement**: the place form has type `(r₁ + r₂, r₂)`. -/
theorem placeForm_signature :
    sigPos (placeForm ι₁ ι₂) = Fintype.card ι₁ + Fintype.card ι₂ ∧
      sigNeg (placeForm ι₁ ι₂) = Fintype.card ι₂ :=
  ⟨by rw [sigPos_of_equiv_weightedSumSquares placeForm_equivalent, ncard_placeWeight_pos],
   by rw [sigNeg_of_equiv_weightedSumSquares placeForm_equivalent, ncard_placeWeight_neg]⟩

/-- **(a), hypothesis form**: ANY real quadratic form on `(ι₁ → ℝ) × (ι₂ → ℂ)` that evaluates
to `Σ x_i² + Σ 2 Re(z_j²)` has type `(r₁ + r₂, r₂)`. -/
theorem signature_of_apply_eq (Q : QuadraticForm ℝ ((ι₁ → ℝ) × (ι₂ → ℂ)))
    (hQ : ∀ x z, Q (x, z) = ∑ i, x i ^ 2 + ∑ j, 2 * (z j ^ 2).re) :
    sigPos Q = Fintype.card ι₁ + Fintype.card ι₂ ∧ sigNeg Q = Fintype.card ι₂ := by
  have : Q = placeForm ι₁ ι₂ := QuadraticMap.ext fun p => by
    rcases p with ⟨x, z⟩; rw [hQ, placeForm_apply]
  subst this
  exact placeForm_signature

/-! ### The Born companion: the positive form `Σ x_i² + Σ 2 |z_j|²` -/

/-- The weights `(1, …, 1, 2, …, 2, 2, …, 2)`. -/
def bornWeight : ι₁ ⊕ (ι₂ ⊕ ι₂) → ℝ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2) (fun _ => 2))

variable (ι₁ ι₂) in
/-- The Born place form `B(x, z) = Σ_i x_i² + Σ_j 2 |z_j|²` (the form `Σ_τ x_τ conj x_τ` over
the embeddings). -/
noncomputable def bornPlaceForm : QuadraticForm ℝ ((ι₁ → ℝ) × (ι₂ → ℂ)) :=
  (weightedSumSquares ℝ (bornWeight (ι₁ := ι₁) (ι₂ := ι₂))).comp realify.toLinearMap

theorem bornPlaceForm_apply (x : ι₁ → ℝ) (z : ι₂ → ℂ) :
    bornPlaceForm ι₁ ι₂ (x, z) = ∑ i, x i ^ 2 + ∑ j, 2 * Complex.normSq (z j) := by
  simp only [bornPlaceForm, QuadraticMap.comp_apply, weightedSumSquares_apply,
    Fintype.sum_sum_type, bornWeight, LinearEquiv.coe_coe, realify_inl, realify_inr_inl,
    realify_inr_inr, Sum.elim_inl, Sum.elim_inr, smul_eq_mul]
  rw [← sum_add_distrib]
  congr 1
  · exact sum_congr rfl fun i _ => by ring
  · refine sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_apply]
    ring

theorem bornPlaceForm_equivalent :
    (bornPlaceForm ι₁ ι₂).Equivalent (weightedSumSquares ℝ (bornWeight (ι₁ := ι₁) (ι₂ := ι₂))) :=
  ⟨{ realify with map_app' := fun _ => rfl }⟩

/-- The Born place form is positive definite on the whole Minkowski space: type
`(r₁ + 2 r₂, 0)`. -/
theorem bornPlaceForm_signature :
    sigPos (bornPlaceForm ι₁ ι₂) = Fintype.card ι₁ + 2 * Fintype.card ι₂ ∧
      sigNeg (bornPlaceForm ι₁ ι₂) = 0 := by
  classical
  constructor
  · rw [sigPos_of_equiv_weightedSumSquares bornPlaceForm_equivalent]
    have hset : {i | 0 < bornWeight (ι₁ := ι₁) (ι₂ := ι₂) i} =
        ↑(univ.filter fun i => 0 < bornWeight (ι₁ := ι₁) (ι₂ := ι₂) i) := by
      ext; simp
    rw [hset, Set.ncard_coe_finset, card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
    norm_num [bornWeight]
    ring
  · rw [sigNeg_of_equiv_weightedSumSquares bornPlaceForm_equivalent]
    have hset : {i | bornWeight (ι₁ := ι₁) (ι₂ := ι₂) i < 0} = ∅ := by
      ext i; rcases i with i | j | j <;> norm_num [bornWeight]
    rw [hset, Set.ncard_empty]

end HermitianExclusion
