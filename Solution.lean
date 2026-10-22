module
public import Mathlib
public import ArithmeticLorentz.HermN
public import ArithmeticLorentz.Boost
public import ArithmeticLorentz.RegisterBridge

@[expose] public section
/-
Solution: the sixteen statements of `Challenge.lean`, stated identically, each proved by `exact`
of one theorem of the proof modules: `ArithmeticLorentz.HermN` (1, 2), `ArithmeticLorentz.Boost`
(3–8) and `ArithmeticLorentz.RegisterBridge` (9–16), all in namespace `HermitianExclusion`.
-/

open Matrix ComplexConjugate Complex Finset QuadraticForm QuadraticMap

open HermitianExclusion

namespace ArithmeticLorentz

/-- **(1) Lorentzian iff `n = 2`.** Among the Hermitian matrix spaces `Herm_n(ℂ)`, the form
`X ↦ Re tr(X Xᵀ)` has exactly one negative direction iff `n = 2`. -/
theorem sigNeg_transposeForm_eq_one_iff (n : ℕ) : sigNeg (transposeForm n) = 1 ↔ n = 2 := by
  exact HermitianExclusion.sigNeg_transposeForm_eq_one_iff n

/-- **(2) The Hermitian exclusion, full form.** One negative direction forces `n = 2`, type
`(3, 1)`, real dimension `4`. -/
theorem hermitian_exclusion (n : ℕ) (h : sigNeg (transposeForm n) = 1) :
    n = 2 ∧ sigPos (transposeForm n) = 3 ∧ Module.finrank ℝ (herm n) = 4 := by
  exact HermitianExclusion.hermitian_exclusion n h

/-- **(3) The infinitesimal classification**, every `r₁`: a place-preserving infinitesimal
isometry of the trace form is a real multiple of `boostGen`. -/
theorem infIsometry_classification {r₁ : ℕ} (L : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁)
    (hP : PlacePreserving L) (hL : IsInfIsometry L) : ∃ c : ℝ, L = c • boostGen r₁ := by
  exact HermitianExclusion.infIsometry_classification L hP hL

/-- **(4) The group classification**, every `r₁`: a place-preserving isometry of the trace form is
a sign on each real place and `± boost β` or `± boost β ∘ conj` on the complex place:
`{±1}^{r₁} × O(1, 1)`. -/
theorem placePreserving_isometry_classification {r₁ : ℕ} (g : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁)
    (hP : PlacePreserving g) (hg : IsIsometry g) :
    ∃ (ε : Fin r₁ → ℝ) (ε' β : ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (ε' = 1 ∨ ε' = -1) ∧
      ((∀ p, g p = (fun i => ε i * p.1 i, fun j => ε' * boostC β (p.2 j))) ∨
       (∀ p, g p = (fun i => ε i * p.1 i, fun j => ε' * boostC β (conj (p.2 j))))) := by
  exact HermitianExclusion.placePreserving_isometry_classification g hP hg

/-- **(5) The boost is an isometry of the trace form.** -/
theorem traceB_boost {r₁ : ℕ} (β : ℝ) (X Y : PlaceSpace r₁) :
    traceB r₁ (boost r₁ β X) (boost r₁ β Y) = traceB r₁ X Y := by
  exact HermitianExclusion.traceB_boost β X Y

/-- **(6) The boost is not a Born isometry** for `β ≠ 0` (on `Herm₂(ℂ)`, through the place
isomorphism). -/
theorem hsForm_boost_ne (β : ℝ) (hβ : β ≠ 0) :
    ∃ X : PlaceSpace 2, hsForm 2 (placeEquiv (boost 2 β X)) ≠ hsForm 2 (placeEquiv X) := by
  exact HermitianExclusion.hsForm_boost_ne β hβ

/-- **(7) Galois conjugation reverses the boost**: `c ∘ boost β ∘ c = boost (−β)`. -/
theorem galoisConj_boost_galoisConj {r₁ : ℕ} (β : ℝ) (p : PlaceSpace r₁) :
    galoisConj r₁ (boost r₁ β (galoisConj r₁ p)) = boost r₁ (-β) p := by
  exact HermitianExclusion.galoisConj_boost_galoisConj β p

/-- **(8) The polar phase is a trace-form isometry iff `sin θ = 0`.** -/
theorem traceB_phaseV_iff (θ : ℝ) :
    (∀ X : PlaceSpace 2, traceB 2 (phaseV θ X) (phaseV θ X) = traceB 2 X X) ↔
      Real.sin θ = 0 := by
  exact HermitianExclusion.traceB_phaseV_iff θ

/-- **(9) Time-canonical.** A Lorentz map carrying Galois conjugation to the register's time
reflection is `diag(R, s)` with `R ∈ O(3)`, `s = ±1`. -/
theorem time_canonical (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hη : Λᵀ * η4 * Λ = η4)
    (hc : Λ * cArith * Λ⁻¹ = Preg) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ), Rᵀ * R = 1 ∧ (s = 1 ∨ s = -1) ∧ Λ = blockDiag R s := by
  exact HermitianExclusion.time_canonical Λ hη hc

/-- **(10) The rest-frame condition.** For `Λ ∈ O(3, 1)`, `Λ P Λ⁻¹ = P ⟺ Λ Λᵀ = 1`. -/
theorem conj_P_iff_orthogonal (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hη : Λᵀ * η4 * Λ = η4) :
    Λ * Preg * Λ⁻¹ = Preg ↔ Λ * Λᵀ = 1 := by
  exact HermitianExclusion.conj_P_iff_orthogonal Λ hη

/-- **(11) The boost span.** `diag(R, s) · K · diag(Rᵀ, s) = −s (n₀ L03 + n₁ L13 + n₂ L23)`,
`n = R e₂`. -/
theorem boost_span (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    blockDiag R s * Kmat * blockDiag Rᵀ s =
      (-s) • (R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r) := by
  exact HermitianExclusion.boost_span R s

/-- **(12) The phase is excluded from `so(3, 1)`.** -/
theorem phase_not_mem_so31 (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s = 1 ∨ s = -1) : blockDiag R s * Jmat * blockDiag Rᵀ s ∉ so31 := by
  exact HermitianExclusion.phase_not_mem_so31 R s hR hs

/-- **(13) The Hodge exchange.** `H(diag(R, s) · K · diag(Rᵀ, s)) = s (n₀ L12 − n₁ L02 + n₂ L01)`;
at `R = 1`, `s = 1`: `H(K) = L01`. -/
theorem hodge_exchange (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    hodgeOp (blockDiag R s * Kmat * blockDiag Rᵀ s) =
      s • (R 0 2 • L12r - R 1 2 • L02r + R 2 2 • L01r) := by
  exact HermitianExclusion.hodge_exchange R s

/-- **(14) The places are transverse to the divide.**
`D(iConj) = ½(ρ + Q) · iConj − ½ i (ρ − Q) · L01`. -/
theorem divide_iConj (ρ Q : ℝ) :
    (divide ρ Q).mulVec iConjVec =
      (((ρ : ℂ) + Q) / 2) • iConjVec - (Complex.I * ((ρ : ℂ) - Q) / 2) • L01Vec := by
  exact HermitianExclusion.divide_iConj ρ Q

/-- **(15) The divide against its flip.** `D · flip D = ρQ · 1`. -/
theorem divide_mul_flip (ρ Q : ℝ) : divide ρ Q * divideFlip ρ Q = ((ρ * Q : ℝ) : ℂ) • 1 := by
  exact HermitianExclusion.divide_mul_flip ρ Q

/-- **(16) The Holst coefficient of the divide is purely imaginary.** -/
theorem holst_gamma_not_real (ρ Q : ℝ) (hρQ : ρ ≠ Q) (hsum : ρ + Q ≠ 0) (γ : ℂ)
    (h : ∃ lam : ℂ, 1 + γ⁻¹ • HC = lam • divide ρ Q) : γ.re = 0 ∧ γ.im ≠ 0 := by
  exact HermitianExclusion.holst_gamma_not_real ρ Q hρQ hsum γ h

end ArithmeticLorentz
