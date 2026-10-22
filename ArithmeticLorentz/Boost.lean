module
public import Mathlib
public import ArithmeticLorentz.Defs
public import ArithmeticLorentz.Counting
public import ArithmeticLorentz.Qubit

@[expose] public section
/-!
# The arithmetic Lorentz boost on the place space (K7)

The place space of a number field with `r₁` real places and one complex place is
`V = (Fin r₁ → ℝ) × (Fin 1 → ℂ)`; for `r₁ = 2` it is `Herm₂(ℂ)` through `placeEquiv`
(`Qubit.lean`). It carries two real forms (`Counting.lean`, `Qubit.lean`, `PlaceLink.lean`):

* the **trace form** `T(X, Y) = Σ x_i y_i + 2 Re(z w)`, which on `Herm₂(ℂ)` is
  `Re tr(X Yᵀ)` (`transposeBilin 2`), of type `(r₁ + 1, 1)` — for `r₁ = 2`, type `(3, 1)`;
* the **Born form** `B(X, Y) = Σ x_i y_i + 2 Re(z conj w)`, which on `Herm₂(ℂ)` is
  `Re tr(X Y)` (`hsBilin 2`), positive definite.

The Lorentz structure of `Herm₂(ℂ)` used here is the one carried by `tr(XYᵀ)`, whose single
timelike direction is `σ_y` (`placeMatrix_sub_transpose`); it is NOT the determinant form of the
classical identification `Herm₂(ℂ) ≅ ℝ^{3,1}`, `X ↦ det X` (Jordan–von Neumann–Wigner 1934;
Penrose–Rindler, *Spinors and space-time* I, §1.2). Nothing here is claimed beyond "stated in
number-field place coordinates".

**The arithmetic boost.** The real-linear map `iConj : (x, z) ↦ (x, i · conj z)` squares to the
identity and is not multiplication by any element of `V` (K7.1). Its generator on the complex
factor, `boostGen : (x, z) ↦ (0, i · conj z)`, integrates to the one-parameter group

  `boost β (x, z) = (x, cosh β · z + i sinh β · conj z)`

(K7.2: `boost 0 = id`, `boost β ∘ boost γ = boost (β + γ)`, and
`d/dβ boost β = boostGen ∘ boost β`, the flow characterisation of `exp (β · boostGen)`; also the
closed series form `boost β = id + (cosh β − 1) P_ℂ + sinh β · boostGen`).
Sign convention: `boostGen` acts on `(u, v) = (Re z, Im z)` as `[[0, 1], [1, 0]]`, the
opposite generator `[[0, −1], [−1, 0]]` exponentiates to `cosh β z − i sinh β conj z`, which is
`boost (−β)` here (the same group).

* K7.3 `boost β` is an isometry of the trace form (`traceB_boost`, `transposeForm_boost`).
* K7.4 `boost β` is NOT a Born isometry for `β ≠ 0` (`hsForm_boost_ne`).
* K7.5 Galois conjugation `(x, z) ↦ (x, conj z)` is an isometry of both forms and conjugates
  `boost β` to `boost (−β)` (time reversal).
* K7.6 / K7.8 **Classification.** For every `r₁`, a real-linear `L` on `V` that preserves the
  places (block-diagonal for `ℝ ⊕ ⋯ ⊕ ℝ ⊕ ℂ`) and is an infinitesimal isometry of the trace
  form, `T(LX, Y) + T(X, LY) = 0`, is a real multiple of `boostGen`: the place-preserving
  infinitesimal isometries form the line `ℝ · boostGen` (real places admit none), of dimension `1`
  (`placePreserving_infIsometry_eq_span`, `finrank_placePreserving_infIsometry`). The
  place-preserving isometries themselves are `{±1}^{r₁} × O(1, 1)`: on the complex place
  `± boost β` or `± boost β ∘ conj` (`placePreserving_isometry_classification`).
* K7.7 The polar phase `(x, z) ↦ (x, e^{iθ} z)` (`phaseV`; on `Herm₂(ℂ)` it is `Ad diag(1, e^{iθ})`)
  is place-preserving and a Born isometry, and is a trace-form isometry iff `sin θ = 0`
  (`traceB_phaseV_iff`).
-/

namespace HermitianExclusion

open Matrix ComplexConjugate Complex Finset

/-! ### The two forms in place coordinates -/

theorem traceB_self {r₁ : ℕ} (X : PlaceSpace r₁) :
    traceB r₁ X X = placeForm (Fin r₁) (Fin 1) X := by
  rcases X with ⟨x, z⟩
  rw [placeForm_apply]
  simp [traceB, pow_two]

theorem bornB_self {r₁ : ℕ} (X : PlaceSpace r₁) :
    bornB r₁ X X = bornPlaceForm (Fin r₁) (Fin 1) X := by
  rcases X with ⟨x, z⟩
  rw [bornPlaceForm_apply]
  simp [bornB, pow_two, Complex.normSq_apply, Complex.mul_re]

/-- On `Herm₂(ℂ)`, the trace form is `Re tr(X Yᵀ)`. -/
theorem traceB_two (X Y : PlaceSpace 2) :
    traceB 2 X Y = transposeBilin 2 (placeEquiv X) (placeEquiv Y) := by
  rw [transposeBilin_apply, placeEquiv_apply_coe, placeEquiv_apply_coe,
    trace_placeMatrix_mul_transpose, trace_real, Complex.ofReal_re]
  simp [traceB, Fin.sum_univ_two]

/-- On `Herm₂(ℂ)`, the Born form is `Re tr(X Y)`. -/
theorem bornB_two (X Y : PlaceSpace 2) :
    bornB 2 X Y = hsBilin 2 (placeEquiv X) (placeEquiv Y) := by
  rw [hsBilin_apply, placeEquiv_apply_coe, placeEquiv_apply_coe, trace_placeMatrix_mul, born_real,
    Complex.ofReal_re]
  simp [bornB, Fin.sum_univ_two]

/-! ### Galois conjugation, `iConj`, and the boost generator -/

theorem galoisConj_apply {r₁ : ℕ} (p : PlaceSpace r₁) :
    galoisConj r₁ p = (p.1, fun j => conj (p.2 j)) := rfl

theorem iConj_apply {r₁ : ℕ} (p : PlaceSpace r₁) :
    iConj r₁ p = (p.1, fun j => I * conj (p.2 j)) := rfl

theorem boostGen_apply {r₁ : ℕ} (p : PlaceSpace r₁) :
    boostGen r₁ p = (0, fun j => I * conj (p.2 j)) := rfl

/-- **K7.1 (linearity).** `iConj` is `ℝ`-linear (it is a `LinearMap`; this records the two
laws). -/
theorem iConj_linear {r₁ : ℕ} (c : ℝ) (p q : PlaceSpace r₁) :
    iConj r₁ (p + q) = iConj r₁ p + iConj r₁ q ∧ iConj r₁ (c • p) = c • iConj r₁ p :=
  ⟨map_add _ _ _, map_smul _ _ _⟩

/-- **K7.1 (involution).** `iConj ∘ iConj = id` on `V`. -/
theorem iConj_iConj {r₁ : ℕ} (p : PlaceSpace r₁) : iConj r₁ (iConj r₁ p) = p := by
  ext j
  · rfl
  · apply Complex.ext <;> simp [iConj_apply]

/-- **K7.1 (not a multiplication).** There is no `w ∈ ℂ` with `w · z = i · conj z` for all `z`. -/
theorem iConj_not_mul : ¬ ∃ w : ℂ, ∀ z : ℂ, I * conj z = w * z := by
  rintro ⟨w, hw⟩
  have h1 : w = I := by simpa using (hw 1).symm
  have h2 := hw I
  rw [h1, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg] at h2
  norm_num at h2

/-- **K7.1, in `V`.** `iConj` is not multiplication by any element of `V`: the multiplication of
`V` is place-wise, so on the complex place it is multiplication by a complex number `w`, and no
`w` works. -/
theorem iConj_not_placeMul {r₁ : ℕ} :
    ¬ ∃ w : ℂ, ∀ p : PlaceSpace r₁, iConj r₁ p = (p.1, fun j => w * p.2 j) := by
  rintro ⟨w, hw⟩
  refine iConj_not_mul ⟨w, fun z => ?_⟩
  have h := congrArg (fun q : PlaceSpace r₁ => q.2 0) (hw (0, fun _ => z))
  simpa [iConj_apply] using h

/-! ### The boost -/

theorem boost_apply' {r₁ : ℕ} (β : ℝ) (p : PlaceSpace r₁) :
    boost r₁ β p = (p.1, fun j => boostC β (p.2 j)) := rfl

/-- **K7.2 (closed form).** `boost β (x, z) = (x, cosh β · z + i sinh β · conj z)`. -/
theorem boost_apply {r₁ : ℕ} (β : ℝ) (p : PlaceSpace r₁) :
    boost r₁ β p =
      (p.1, fun j => (Real.cosh β : ℂ) * p.2 j + I * (Real.sinh β : ℂ) * conj (p.2 j)) := rfl

theorem boostC_zero (z : ℂ) : boostC 0 z = z := by simp [boostC]

theorem boostC_boostC (β γ : ℝ) (z : ℂ) : boostC β (boostC γ z) = boostC (β + γ) z := by
  apply Complex.ext <;> simp [boostC, Real.cosh_add, Real.sinh_add] <;> ring

/-- **K7.2 (group law).** `boost 0 = id`. -/
theorem boost_zero {r₁ : ℕ} (p : PlaceSpace r₁) : boost r₁ 0 p = p := by
  ext j
  · rfl
  · exact boostC_zero _

/-- **K7.2 (group law).** `boost β ∘ boost γ = boost (β + γ)`. -/
theorem boost_boost {r₁ : ℕ} (β γ : ℝ) (p : PlaceSpace r₁) :
    boost r₁ β (boost r₁ γ p) = boost r₁ (β + γ) p :=
  Prod.ext rfl (funext fun j => boostC_boostC β γ (p.2 j))

theorem boost_neg_boost {r₁ : ℕ} (β : ℝ) (p : PlaceSpace r₁) :
    boost r₁ (-β) (boost r₁ β p) = p := by
  rw [boost_boost, neg_add_cancel, boost_zero]

theorem hasDerivAt_boostC (β : ℝ) (z : ℂ) :
    HasDerivAt (fun β => boostC β z) (I * conj (boostC β z)) β := by
  have hc := (Real.hasDerivAt_cosh β).ofReal_comp.mul_const z
  have hs := ((Real.hasDerivAt_sinh β).ofReal_comp.const_mul I).mul_const (conj z)
  have h := hc.add hs
  refine h.congr_deriv ?_
  apply Complex.ext <;> simp [boostC]
  ring

/-- **K7.2 (the flow).** `β ↦ boost β p` solves `d/dβ boost β p = boostGen (boost β p)` with
`boost 0 p = p`: it is the integral curve of `boostGen`, i.e. `boost β = exp (β · boostGen)`. -/
theorem hasDerivAt_boost {r₁ : ℕ} (β : ℝ) (p : PlaceSpace r₁) :
    HasDerivAt (fun β => boost r₁ β p) (boostGen r₁ (boost r₁ β p)) β := by
  have h1 : HasDerivAt (fun _ : ℝ => p.1) 0 β := hasDerivAt_const β p.1
  have h2 : HasDerivAt (fun β => fun j => boostC β (p.2 j))
      (fun j => I * conj (boostC β (p.2 j))) β :=
    hasDerivAt_pi.mpr fun j => hasDerivAt_boostC β (p.2 j)
  exact h1.prodMk h2

/-- `boostGen² = P_ℂ`, the projection on the complex place. -/
theorem boostGen_boostGen {r₁ : ℕ} (p : PlaceSpace r₁) :
    boostGen r₁ (boostGen r₁ p) = (0, p.2) := by
  ext j
  · rfl
  · apply Complex.ext <;> simp [boostGen_apply]

/-- **K7.2 (series form).** `boost β = id + (cosh β − 1) P_ℂ + sinh β · boostGen`, with `P_ℂ` the
projection on the complex place: the closed form of `Σ βⁿ boostGenⁿ / n!` given
`boostGen² = P_ℂ`. -/
theorem boost_eq_cosh_sinh {r₁ : ℕ} (β : ℝ) (p : PlaceSpace r₁) :
    boost r₁ β p = p + (Real.cosh β - 1) • boostGen r₁ (boostGen r₁ p) +
      Real.sinh β • boostGen r₁ p := by
  ext j
  · simp [boost_apply', boostGen_apply]
  · apply Complex.ext <;> simp [boost_apply', boostC, boostGen_apply] <;> ring

/-! ### K7.3 / K7.4 / K7.5: isometry of the trace form, not of the Born form -/

theorem boostC_mul_re (β : ℝ) (z w : ℂ) : (boostC β z * boostC β w).re = (z * w).re := by
  simp only [boostC, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  linear_combination (z.re * w.re - z.im * w.im) * Real.cosh_sq β

/-- **K7.3.** The boost is an isometry of the trace form. -/
theorem traceB_boost {r₁ : ℕ} (β : ℝ) (X Y : PlaceSpace r₁) :
    traceB r₁ (boost r₁ β X) (boost r₁ β Y) = traceB r₁ X Y := by
  simp only [traceB, boost_apply']
  congr 1
  exact sum_congr rfl fun j _ => by rw [boostC_mul_re]

/-- **K7.3 on `Herm₂(ℂ)`.** `Re tr(boost X (boost Y)ᵀ) = Re tr(X Yᵀ)`. -/
theorem transposeBilin_boost (β : ℝ) (X Y : PlaceSpace 2) :
    transposeBilin 2 (placeEquiv (boost 2 β X)) (placeEquiv (boost 2 β Y)) =
      transposeBilin 2 (placeEquiv X) (placeEquiv Y) := by
  rw [← traceB_two, ← traceB_two, traceB_boost]

/-- **K7.3 on `Herm₂(ℂ)`, quadratic form.** `transposeForm 2 (boost β X) = transposeForm 2 X`. -/
theorem transposeForm_boost (β : ℝ) (X : PlaceSpace 2) :
    transposeForm 2 (placeEquiv (boost 2 β X)) = transposeForm 2 (placeEquiv X) := by
  rw [transposeForm_placeEquiv, transposeForm_placeEquiv, ← traceB_self, ← traceB_self,
    traceB_boost]

/-- The Born mass of the boosted pure coherence `(0, 1)`: `2 cosh² β + 2 sinh² β`. -/
theorem hsForm_boost_coherence (β : ℝ) :
    hsForm 2 (placeEquiv (boost 2 β (0, fun _ => 1))) = 2 + 4 * Real.sinh β ^ 2 := by
  rw [hsForm_placeEquiv, boost_apply, bornPlaceForm_apply]
  simp [Complex.normSq_apply, -Complex.ofReal_sinh, -Complex.ofReal_cosh]
  linear_combination 2 * Real.cosh_sq β

theorem hsForm_coherence : hsForm 2 (placeEquiv ((0 : Fin 2 → ℝ), fun _ => (1 : ℂ))) = 2 := by
  rw [hsForm_placeEquiv, bornPlaceForm_apply]
  simp

/-- **K7.4.** For `β ≠ 0`, the boost is NOT an isometry of the Born form: on the pure coherence
`(0, 0, 1)` it sends `hsForm = 2` to `2 + 4 sinh² β`. -/
theorem hsForm_boost_ne (β : ℝ) (hβ : β ≠ 0) :
    ∃ X : PlaceSpace 2, hsForm 2 (placeEquiv (boost 2 β X)) ≠ hsForm 2 (placeEquiv X) := by
  refine ⟨(0, fun _ => 1), ?_⟩
  rw [hsForm_boost_coherence, hsForm_coherence]
  have hs : Real.sinh β ≠ 0 := fun h => hβ (Real.sinh_eq_zero.mp h)
  have : 0 < Real.sinh β ^ 2 := by positivity
  linarith

/-- **K7.4, the Born deviation in general.** `B(boost X, boost X) − B(X, X) =
Σ_j 4 (sinh β Re z_j + cosh β Im z_j)² − 4 (Im z_j)²`. -/
theorem bornB_boost_self {r₁ : ℕ} (β : ℝ) (X : PlaceSpace r₁) :
    bornB r₁ (boost r₁ β X) (boost r₁ β X) - bornB r₁ X X =
      ∑ j, (4 * (Real.sinh β * (X.2 j).re + Real.cosh β * (X.2 j).im) ^ 2 -
        4 * (X.2 j).im ^ 2) := by
  simp only [bornB, boost_apply', add_sub_add_left_eq_sub, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [boostC, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj,
    Complex.neg_re, Complex.neg_im]
  linear_combination (2 * (X.2 j).re ^ 2 - 2 * (X.2 j).im ^ 2) * Real.cosh_sq β

/-- **K7.5.** Galois conjugation is an isometry of the trace form (time reversal). -/
theorem traceB_galoisConj {r₁ : ℕ} (X Y : PlaceSpace r₁) :
    traceB r₁ (galoisConj r₁ X) (galoisConj r₁ Y) = traceB r₁ X Y := by
  simp only [traceB, galoisConj_apply]
  congr 1
  exact sum_congr rfl fun j _ => by rw [← map_mul, Complex.conj_re]

/-- **K7.5.** Galois conjugation is an isometry of the Born form. -/
theorem bornB_galoisConj {r₁ : ℕ} (X Y : PlaceSpace r₁) :
    bornB r₁ (galoisConj r₁ X) (galoisConj r₁ Y) = bornB r₁ X Y := by
  simp only [bornB, galoisConj_apply, Complex.conj_conj]
  congr 1
  exact sum_congr rfl fun j _ => by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

theorem transposeForm_galoisConj (X : PlaceSpace 2) :
    transposeForm 2 (placeEquiv (galoisConj 2 X)) = transposeForm 2 (placeEquiv X) := by
  rw [transposeForm_placeEquiv, transposeForm_placeEquiv, ← traceB_self, ← traceB_self,
    traceB_galoisConj]

theorem hsForm_galoisConj (X : PlaceSpace 2) :
    hsForm 2 (placeEquiv (galoisConj 2 X)) = hsForm 2 (placeEquiv X) := by
  rw [hsForm_placeEquiv, hsForm_placeEquiv, ← bornB_self, ← bornB_self, bornB_galoisConj]

theorem galoisConj_galoisConj {r₁ : ℕ} (p : PlaceSpace r₁) :
    galoisConj r₁ (galoisConj r₁ p) = p :=
  Prod.ext rfl (funext fun j => Complex.conj_conj (p.2 j))

/-- **K7.5.** `galoisConj ∘ boost β ∘ galoisConj = boost (−β)`: time reversal reverses the
boost. -/
theorem galoisConj_boost_galoisConj {r₁ : ℕ} (β : ℝ) (p : PlaceSpace r₁) :
    galoisConj r₁ (boost r₁ β (galoisConj r₁ p)) = boost r₁ (-β) p := by
  ext j
  · rfl
  · apply Complex.ext <;>
      simp [boost_apply', boostC, galoisConj_apply, Real.cosh_neg, Real.sinh_neg]

/-! ### K7.6 / K7.8: the classification of place-preserving isometries -/

/-- A place-preserving linear map is `(x, z) ↦ (λ_i x_i, Re z · m₁ + Im z · m₂)` for some real
`λ_i` and complex `m₁ = L(1)`, `m₂ = L(i)` on the complex place. -/
theorem PlacePreserving.exists_apply {r₁ : ℕ} {L : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁}
    (hP : PlacePreserving L) :
    ∃ (lam : Fin r₁ → ℝ) (m₁ m₂ : ℂ), ∀ p : PlaceSpace r₁,
      L p = (fun i => lam i * p.1 i, fun j => ((p.2 j).re : ℂ) * m₁ + ((p.2 j).im : ℂ) * m₂) := by
  choose lam hlam using fun i => hP.1 i 1
  refine ⟨lam, (L (0, fun _ => 1)).2 0, (L (0, fun _ => I)).2 0, fun p => ?_⟩
  have hreal : ∀ (i : Fin r₁) (a : ℝ),
      L ((Pi.single i a : Fin r₁ → ℝ), (0 : Fin 1 → ℂ)) =
        ((Pi.single i (lam i * a) : Fin r₁ → ℝ), 0) := by
    intro i a
    have h : (((Pi.single i a : Fin r₁ → ℝ), (0 : Fin 1 → ℂ)) : PlaceSpace r₁) =
        a • (((Pi.single i (1 : ℝ) : Fin r₁ → ℝ), (0 : Fin 1 → ℂ)) : PlaceSpace r₁) := by
      ext k
      · simp [Pi.single_apply]
      · simp
    rw [h, map_smul, hlam i]
    ext k
    · by_cases hk : k = i
      · subst hk; simp [mul_comm]
      · simp [hk]
    · simp
  have hcplx : ∀ z : Fin 1 → ℂ, L (0, z) =
      (0, fun j => ((z j).re : ℂ) * (L (0, fun _ => 1)).2 0 +
        ((z j).im : ℂ) * (L (0, fun _ => I)).2 0) := by
    intro z
    have h : (((0 : Fin r₁ → ℝ), z) : PlaceSpace r₁) =
        (z 0).re • (((0 : Fin r₁ → ℝ), fun _ => (1 : ℂ)) : PlaceSpace r₁) +
          (z 0).im • (((0 : Fin r₁ → ℝ), fun _ => I) : PlaceSpace r₁) := by
      ext j
      · simp
      · have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        apply Complex.ext <;> simp
    rw [h, map_add, map_smul, map_smul]
    refine Prod.ext ?_ (funext fun j => ?_)
    · simp [hP.2]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp [Complex.real_smul]
  have hp : p = ((p.1, 0) : PlaceSpace r₁) + ((0, p.2) : PlaceSpace r₁) := by
    ext j <;> simp
  have h1 : L (p.1, 0) = (fun i => lam i * p.1 i, 0) := by
    have hsum : ((p.1, 0) : PlaceSpace r₁) =
        ∑ i, (((Pi.single i (p.1 i) : Fin r₁ → ℝ), (0 : Fin 1 → ℂ)) : PlaceSpace r₁) := by
      ext k
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [hsum, map_sum]
    simp only [hreal]
    ext k
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  conv_lhs => rw [hp, map_add, h1, hcplx]
  ext k
  · simp
  · simp

/-- **K7.8 (and K7.6 at `r₁ = 2`): the infinitesimal classification.** A place-preserving
infinitesimal isometry of the trace form is a real multiple of `boostGen`: the real places admit
no infinitesimal isometry, and on the complex place the only one is `i · conj`. -/
theorem infIsometry_classification {r₁ : ℕ} (L : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁)
    (hP : PlacePreserving L) (hL : IsInfIsometry L) : ∃ c : ℝ, L = c • boostGen r₁ := by
  obtain ⟨lam, m₁, m₂, hL'⟩ := hP.exists_apply
  refine ⟨m₁.im, ?_⟩
  have hlam : ∀ i, lam i = 0 := by
    intro i
    have h := hL ((Pi.single i (1 : ℝ) : Fin r₁ → ℝ), (0 : Fin 1 → ℂ))
      ((Pi.single i (1 : ℝ) : Fin r₁ → ℝ), (0 : Fin 1 → ℂ))
    simp only [hL', traceB] at h
    simp [Pi.single_apply, mul_ite] at h
    linarith
  have h1 := hL ((0 : Fin r₁ → ℝ), fun _ => (1 : ℂ)) ((0 : Fin r₁ → ℝ), fun _ => (1 : ℂ))
  have h2 := hL ((0 : Fin r₁ → ℝ), fun _ => I) ((0 : Fin r₁ → ℝ), fun _ => I)
  have h3 := hL ((0 : Fin r₁ → ℝ), fun _ => (1 : ℂ)) ((0 : Fin r₁ → ℝ), fun _ => I)
  simp only [hL', traceB] at h1 h2 h3
  simp [Complex.mul_re] at h1 h2 h3
  have hre : m₁.re = 0 := by linarith
  have him : m₂.im = 0 := by linarith
  have hm : m₂.re = m₁.im := by linarith
  refine LinearMap.ext fun p => ?_
  rw [hL', LinearMap.smul_apply, boostGen_apply]
  ext k
  · simp [hlam]
  · apply Complex.ext <;> simp [hre, him, hm] <;> ring

theorem smul_boostGen_placePreserving {r₁ : ℕ} (c : ℝ) : PlacePreserving (c • boostGen r₁) := by
  refine ⟨fun i a => ⟨0, ?_⟩, fun z => ?_⟩
  · rw [Pi.single_zero]
    ext j
    · simp [boostGen_apply]
    · simp [boostGen_apply]
  · simp [boostGen_apply]

theorem smul_boostGen_infIsometry {r₁ : ℕ} (c : ℝ) : IsInfIsometry (c • boostGen r₁) := by
  intro X Y
  simp only [traceB, LinearMap.smul_apply, boostGen_apply, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_zero, Pi.zero_apply, zero_mul, mul_zero, sum_const_zero, zero_add,
    Complex.real_smul]
  rw [← sum_add_distrib]
  refine sum_eq_zero fun j _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **K7.8 / K7.6, the Lie-algebra statement.** The place-preserving infinitesimal isometries of
the trace form are exactly the line `ℝ · boostGen`. -/
theorem placePreserving_infIsometry_eq_span (r₁ : ℕ) :
    {L : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁ | PlacePreserving L ∧ IsInfIsometry L} =
      (Submodule.span ℝ {boostGen r₁} : Set (PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁)) := by
  ext L
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hP, hL⟩
    obtain ⟨c, hc⟩ := infIsometry_classification L hP hL
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨smul_boostGen_placePreserving c, smul_boostGen_infIsometry c⟩

theorem boostGen_ne_zero (r₁ : ℕ) : boostGen r₁ ≠ 0 := by
  intro h
  have h1 : (boostGen r₁ ((0 : Fin r₁ → ℝ), fun _ => (1 : ℂ))).2 0 = I := by
    rw [boostGen_apply]; simp
  rw [h] at h1
  exact Complex.I_ne_zero (by simpa using h1.symm)

/-- **K7.8 / K7.6, the dimension.** The place-preserving isometry algebra is one-dimensional. -/
theorem finrank_placePreserving_infIsometry (r₁ : ℕ) :
    Module.finrank ℝ (Submodule.span ℝ {boostGen r₁}) = 1 :=
  finrank_span_singleton (boostGen_ne_zero r₁)

/-- **K7.6 on `Herm₂(ℂ)`.** A place-preserving `L` with
`Re tr(LX · Yᵀ) + Re tr(X · (LY)ᵀ) = 0` is a real multiple of `boostGen`. -/
theorem infIsometry_classification_herm (L : PlaceSpace 2 →ₗ[ℝ] PlaceSpace 2)
    (hP : PlacePreserving L)
    (hT : ∀ X Y, transposeBilin 2 (placeEquiv (L X)) (placeEquiv Y) +
      transposeBilin 2 (placeEquiv X) (placeEquiv (L Y)) = 0) :
    ∃ c : ℝ, L = c • boostGen 2 :=
  infIsometry_classification L hP fun X Y => by rw [traceB_two, traceB_two]; exact hT X Y

/-- The boosts are place-preserving. -/
theorem boost_placePreserving {r₁ : ℕ} (β : ℝ) : PlacePreserving (boost r₁ β) := by
  refine ⟨fun i a => ⟨a, ?_⟩, fun z => rfl⟩
  exact Prod.ext rfl (funext fun j => by simp [boost_apply', boostC])

/-- The boosts are isometries. -/
theorem boost_isIsometry {r₁ : ℕ} (β : ℝ) : IsIsometry (boost r₁ β) := traceB_boost β

theorem galoisConj_placePreserving {r₁ : ℕ} : PlacePreserving (galoisConj r₁) := by
  refine ⟨fun i a => ⟨a, ?_⟩, fun z => rfl⟩
  exact Prod.ext rfl (funext fun j => by simp [galoisConj_apply])

theorem galoisConj_isIsometry {r₁ : ℕ} : IsIsometry (galoisConj r₁) := traceB_galoisConj

/-- **K7.6, the group statement.** Every place-preserving isometry of the trace form is a sign
`±1` on each real place and, on the complex place, either `ε · boost β` or `ε · boost β ∘ conj`
with `ε = ±1`: the group is `{±1}^{r₁} × O(1, 1)`, with identity component `{boost β}`. -/
theorem placePreserving_isometry_classification {r₁ : ℕ} (g : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁)
    (hP : PlacePreserving g) (hg : IsIsometry g) :
    ∃ (ε : Fin r₁ → ℝ) (ε' β : ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (ε' = 1 ∨ ε' = -1) ∧
      ((∀ p, g p = (fun i => ε i * p.1 i, fun j => ε' * boostC β (p.2 j))) ∨
       (∀ p, g p = (fun i => ε i * p.1 i, fun j => ε' * boostC β (conj (p.2 j))))) := by
  obtain ⟨lam, m₁, m₂, hg'⟩ := hP.exists_apply
  -- the real places: `λ_i² = 1`
  have hlam : ∀ i, lam i = 1 ∨ lam i = -1 := by
    intro i
    have h := hg ((Pi.single i (1 : ℝ) : Fin r₁ → ℝ), (0 : Fin 1 → ℂ))
      ((Pi.single i (1 : ℝ) : Fin r₁ → ℝ), (0 : Fin 1 → ℂ))
    simp only [hg', traceB] at h
    simp [Pi.single_apply, mul_ite] at h
    have h' : lam i * lam i = 1 := h
    have : (lam i - 1) * (lam i + 1) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  -- the complex place: `O(1, 1)`
  have h1 := hg ((0 : Fin r₁ → ℝ), fun _ => (1 : ℂ)) ((0 : Fin r₁ → ℝ), fun _ => (1 : ℂ))
  have h2 := hg ((0 : Fin r₁ → ℝ), fun _ => I) ((0 : Fin r₁ → ℝ), fun _ => I)
  have h3 := hg ((0 : Fin r₁ → ℝ), fun _ => (1 : ℂ)) ((0 : Fin r₁ → ℝ), fun _ => I)
  simp only [hg', traceB] at h1 h2 h3
  simp [Complex.mul_re] at h1 h2 h3
  set p := m₁.re with hp
  set q := m₁.im with hq
  set r := m₂.re with hr
  set s := m₂.im with hs
  have e1 : p ^ 2 - q ^ 2 = 1 := by linarith [h1]
  have e2 : r ^ 2 - s ^ 2 = -1 := by linarith [h2]
  have e3 : p * r - q * s = 0 := by linarith [h3]
  have e4 : (p * r) ^ 2 = (q * s) ^ 2 := by
    have : p * r = q * s := by linarith
    rw [this]
  have hr2 : r ^ 2 = q ^ 2 := by linear_combination e4 - q ^ 2 * e2 - r ^ 2 * e1
  have hs2 : s ^ 2 = p ^ 2 := by linear_combination -e2 - e1 + hr2
  have hp1 : 1 ≤ p ^ 2 := by nlinarith [sq_nonneg q]
  have hp0 : p ≠ 0 := fun h => by rw [h] at hp1; norm_num at hp1
  -- either `(r, s) = (q, p)` or `(r, s) = (−q, −p)`
  have hAB : (r = q ∧ s = p) ∨ (r = -q ∧ s = -p) := by
    have hr' : (r - q) * (r + q) = 0 := by linear_combination hr2
    have hs' : (s - p) * (s + p) = 0 := by linear_combination hs2
    rcases mul_eq_zero.mp hr' with hr' | hr' <;> rcases mul_eq_zero.mp hs' with hs' | hs'
    · left; constructor <;> linarith
    · have hrq : r = q := by linarith
      have hsp : s = -p := by linarith
      have h2pq : 2 * p * q = 0 := by rw [hrq, hsp] at e3; linarith
      have hq0 : q = 0 := by
        rcases mul_eq_zero.mp h2pq with h | h
        · exfalso; exact hp0 (by linarith)
        · exact h
      right; constructor <;> linarith
    · have hrq : r = -q := by linarith
      have hsp : s = p := by linarith
      have h2pq : 2 * p * q = 0 := by rw [hrq, hsp] at e3; linarith
      have hq0 : q = 0 := by
        rcases mul_eq_zero.mp h2pq with h | h
        · exfalso; exact hp0 (by linarith)
        · exact h
      left; constructor <;> linarith
    · right; constructor <;> linarith
  -- the rapidity: `cosh β = ε' p`, `sinh β = ε' q`
  obtain ⟨ε', β, hε', hc, hsh⟩ : ∃ ε' β : ℝ, (ε' = 1 ∨ ε' = -1) ∧
      Real.cosh β = ε' * p ∧ Real.sinh β = ε' * q := by
    rcases le_or_gt 0 p with hp' | hp'
    · refine ⟨1, Real.arsinh q, Or.inl rfl, ?_, by rw [Real.sinh_arsinh, one_mul]⟩
      rw [Real.cosh_arsinh, one_mul, show 1 + q ^ 2 = p ^ 2 by linarith, Real.sqrt_sq hp']
    · refine ⟨-1, Real.arsinh (-q), Or.inr rfl, ?_, by rw [Real.sinh_arsinh, neg_one_mul]⟩
      rw [Real.cosh_arsinh, neg_sq, show 1 + q ^ 2 = p ^ 2 by linarith, Real.sqrt_sq_eq_abs,
        abs_of_neg hp']
      ring
  refine ⟨lam, ε', β, hlam, hε', ?_⟩
  have hε2 : ε' * ε' = 1 := by rcases hε' with h | h <;> rw [h] <;> norm_num
  rcases hAB with ⟨hrq, hsp⟩ | ⟨hrq, hsp⟩
  · left
    intro x
    rw [hg']
    refine Prod.ext rfl (funext fun j => ?_)
    apply Complex.ext
    · simp only [boostC, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
        Complex.conj_im, hc, hsh, ← hp, ← hq, ← hr, ← hs, hrq, hsp]
      linear_combination (-(x.2 j).re * p - (x.2 j).im * q) * hε2
    · simp only [boostC, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
        Complex.conj_im, hc, hsh, ← hp, ← hq, ← hr, ← hs, hrq, hsp]
      linear_combination (-(x.2 j).re * q - (x.2 j).im * p) * hε2
  · right
    intro x
    rw [hg']
    refine Prod.ext rfl (funext fun j => ?_)
    apply Complex.ext
    · simp only [boostC, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
        Complex.conj_im, hc, hsh, ← hp, ← hq, ← hr, ← hs, hrq, hsp]
      linear_combination (-(x.2 j).re * p + (x.2 j).im * q) * hε2
    · simp only [boostC, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
        Complex.conj_im, hc, hsh, ← hp, ← hq, ← hr, ← hs, hrq, hsp]
      linear_combination (-(x.2 j).re * q + (x.2 j).im * p) * hε2


/-! ### K7.7: the polar phase is place-preserving, a Born isometry, and a trace-form isometry
only at `sin θ = 0` -/

theorem phaseV_apply (θ : ℝ) (p : PlaceSpace 2) :
    phaseV θ p = (p.1, fun j => exp (θ * I) * p.2 j) := rfl

theorem exp_mul_conj_exp (θ : ℝ) : exp (θ * I) * conj (exp (θ * I)) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  simp

/-- **K7.7.** The polar phase is place-preserving. -/
theorem phaseV_placePreserving (θ : ℝ) : PlacePreserving (phaseV θ) := by
  refine ⟨fun i a => ⟨a, ?_⟩, fun z => rfl⟩
  exact Prod.ext rfl (funext fun j => by simp [phaseV_apply])

/-- **K7.7.** The polar phase is a Born isometry. -/
theorem bornB_phaseV (θ : ℝ) (X Y : PlaceSpace 2) :
    bornB 2 (phaseV θ X) (phaseV θ Y) = bornB 2 X Y := by
  simp only [bornB, phaseV_apply]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [map_mul, show exp (θ * I) * X.2 j * (conj (exp (θ * I)) * conj (Y.2 j)) =
      (exp (θ * I) * conj (exp (θ * I))) * (X.2 j * conj (Y.2 j)) by ring,
    exp_mul_conj_exp, one_mul]

/-- **K7.7.** The polar phase is an isometry of the trace form iff `sin θ = 0`: on the pure
coherence `(0, 1)` it sends `2 Re(z²) = 2` to `2 cos 2θ`. -/
theorem traceB_phaseV_iff (θ : ℝ) :
    (∀ X : PlaceSpace 2, traceB 2 (phaseV θ X) (phaseV θ X) = traceB 2 X X) ↔
      Real.sin θ = 0 := by
  constructor
  · intro h
    have h1 := h (0, fun _ => 1)
    simp [traceB, phaseV_apply, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im] at h1
    have hs : Real.sin θ ^ 2 = 0 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    exact pow_eq_zero_iff two_ne_zero |>.mp hs
  · intro hs X
    have he : exp (θ * I) = (Real.cos θ : ℂ) := by
      apply Complex.ext
      · rw [Complex.exp_ofReal_mul_I_re, Complex.ofReal_re]
      · rw [Complex.exp_ofReal_mul_I_im, Complex.ofReal_im, hs]
    have hc : Real.cos θ ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    simp only [traceB, phaseV_apply, he]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    have e : (Real.cos θ : ℂ) * X.2 j * ((Real.cos θ : ℂ) * X.2 j) =
        ((Real.cos θ ^ 2 : ℝ) : ℂ) * (X.2 j * X.2 j) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, hc, one_mul]

end HermitianExclusion
