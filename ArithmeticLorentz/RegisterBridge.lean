module
public import Mathlib
public import ArithmeticLorentz.Defs
public import ArithmeticLorentz.Boost

@[expose] public section
/-!
# The Minkowski bridge between the place space and the gravity register (K8)

The time-canonical, space-isotropic bridge; the Hodge divide as the self-dual split, with the
places transverse to it; and the divide's Holst coefficient, which is imaginary.

## Provenance of the register data (transcribed, not re-derived)

The register is `pdt-hodge-lie-generation @ e2d8dde` (PALOMAR-2026-09-30-000024):
* `Challenge.lean` L35–75: `eta = ![1, 1, 1, -1, 1, -1]`; the fifteen generators
  `L_ab = eta_b E_ab − eta_a E_ba` on the lexicographic pairs of `Fin 6`; the bivector coordinates
  `coord_(a,b)(M) = eta_b M_ab`; the local Hodge `H[out,in] = eta_a eta_b ε₄(a,b,c,d)`.
* `GravityScreening/HodgeBulkScreen.lean` L29–43: `hodgeRotation = !![0,-1; 1,0]`,
  `hodgeChirality = −i · hodgeRotation`, `hodgePlus/Minus = ½(1 ± chirality)`,
  `hodgeDivide ρ q = ρ · hodgePlus + q · hodgeMinus`, `hodgeDivideFlip ρ q`.

The explicit matrices below are the register's generators `L_ab`, their restrictions to the
`0123` plane, and the register's Hodge star evaluated on the ordered local basis
`(L01, L02, L03, L12, L13, L23)`, transcribed as explicit `!![…]` matrices and checked against the
register's Lean source by exact computation. Nothing here is re-derived from `ε₄`; the Hodge
table is the data.

## Sign conventions fixed here

* `η6 = diag(1, 1, 1, −1, 1, −1)`, `η4 = diag(1, 1, 1, −1)` (time = coordinate `3`).
* Arithmetic place coordinates `(a, b, u, v)` with `z = u + i v`: trace form `T = diag(1,1,2,−2)`;
  Galois conjugation `c = diag(1,1,1,−1)`; `iConj = i ∘ c` has generator `K = [[0,1],[1,0]]` on
  `(u, v)` (the K7 convention `boostGen`, `ArithmeticLorentz.lean`); the phase generator
  `J = [[0,−1],[1,0]]` on `(u, v)`. `S = diag(1, 1, √2, √2)` carries `T` to `η4`: `Sᵀ η4 S = T`.
* The register's time reflection `P = diag(1, 1, 1, −1)` on `0123` — the same matrix as `c`.
* Hodge: `H(L01) = L23`, `H(L02) = −L13`, `H(L03) = −L12`, `H(L12) = L03`, `H(L13) = L02`,
  `H(L23) = −L01`; on the ordered pair `(L01, L23)` this is `hodgeRotation = !![0,-1; 1,0]`
  (on `(L02, L13)` and `(L03, L12)` it is `−hodgeRotation`: the pair-basis orientation).
* Chirality `C = −i H`, `P± = ½(1 ± C)`, divide `D = ρ P₊ + Q P₋`, so the ρ side is `H = +i`.

## Statements

* K8.1 `localGen_etaSkew`, `localGen6_etaSkew6`, `localGen_linearIndependent`, `finrank_so31`,
  `mem_so31_iff` (so(3,1) = the η4-skew matrices = the span of the six), `etaSkew_bracket`
  (closure), and the fifteen structure constants `bracket_01_02 … bracket_13_23`.
* K8.2 `time_canonical` (Λ ∈ O(3,1), Λ c Λ⁻¹ = P ⇒ Λ = diag(R, s), RᵀR = 1, s = ±1),
  `time_canonical'` (the same for Λ' = Λ ∘ S : (arith, T) → (0123, η4)), `blockDiag_isometry`
  (converse).
* K8.3 `boost_span`: `diag(R,s) · K · diag(Rᵀ,s) = −s (n₀ L03 + n₁ L13 + n₂ L23)`, `n = R e₂`;
  `boost_span'` with `S`.
* K8.4 `phase_excluded`: `diag(R,s) · J · diag(Rᵀ,s)` is not η4-skew (so not in so(3,1)), and its
  zero extension is not η6-skew (not in so(4,2)); `phase_excluded'` with `S`.
* K8.5 `hodge_exchange`: `H(diag(R,s) K diag(Rᵀ,s)) = s (n₀ L12 − n₁ L02 + n₂ L01)`;
  `hodge_K : H(K) = L01`.
* K8.6 `Pplus_add_Pminus`, `Pplus_mul_Pplus`, `Pminus_mul_Pminus`, `Pplus_mul_Pminus`,
  `Pminus_mul_Pplus`, `HC_mul_Pplus`, `HC_mul_Pminus`, `divide_iConj`, `divide_mul_flip`
  (re-proved in the local basis; nothing imported from the register).
* K8.7 `divide_eq`, `holst_iff`, `holst_gamma_eq`, `holst_gamma_not_real`.
-/

namespace HermitianExclusion

open Matrix

/-! ### The register's data -/

/-- `η6 = diag(1, 1, 1, −1, 1, −1)` (Challenge.lean L35). -/
def η6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
     0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, -1]

/-- The six local generators as `6 × 6` matrices (the register's `L_ab = η_b E_ab − η_a E_ba`). -/
def L01 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def L02 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def L03 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
     -1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def L12 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def L13 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]
def L23 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0;
     0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]

/-- The same six as `6 × 6` matrices. -/
def localGen6 : Fin 6 → Matrix (Fin 6) (Fin 6) ℝ := ![L01, L02, L03, L12, L13, L23]

/-- Zero extension of a `4 × 4` matrix on `0123` to `6 × 6`. -/
def ext4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![M 0 0, M 0 1, M 0 2, M 0 3, 0, 0; M 1 0, M 1 1, M 1 2, M 1 3, 0, 0;
     M 2 0, M 2 1, M 2 2, M 2 3, 0, 0; M 3 0, M 3 1, M 3 2, M 3 3, 0, 0;
     0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]

/-- The `6 × 6` generators are the zero extensions of the `0123` restrictions. -/
theorem localGen6_eq_ext4 (p : Fin 6) : localGen6 p = ext4 (localGen p) := by
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    rfl

/-- `η4`-skewness: `Xᵀ η4 + η4 X = 0`, membership in `so(3,1)`. -/
def IsEtaSkew4 (X : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Xᵀ * η4 + η4 * X = 0

/-- `η6`-skewness: `Xᵀ η6 + η6 X = 0`, membership in `so(4,2)`. -/
def IsEtaSkew6 (X : Matrix (Fin 6) (Fin 6) ℝ) : Prop := Xᵀ * η6 + η6 * X = 0

theorem ext4_transpose (M : Matrix (Fin 4) (Fin 4) ℝ) : (ext4 M)ᵀ = ext4 Mᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem ext4_mul (M N : Matrix (Fin 4) (Fin 4) ℝ) : ext4 M * ext4 N = ext4 (M * N) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ext4, Matrix.mul_apply, Fin.sum_univ_succ]

theorem η6_mul_ext4 (M : Matrix (Fin 4) (Fin 4) ℝ) : η6 * ext4 M = ext4 (η4 * M) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ext4, η6, η4, Matrix.mul_apply, Fin.sum_univ_succ]

theorem ext4_mul_η6 (M : Matrix (Fin 4) (Fin 4) ℝ) : ext4 M * η6 = ext4 (M * η4) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ext4, η6, η4, Matrix.mul_apply, Fin.sum_univ_succ]

theorem ext4_add (M N : Matrix (Fin 4) (Fin 4) ℝ) : ext4 M + ext4 N = ext4 (M + N) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ext4]

theorem ext4_eq_zero_iff (M : Matrix (Fin 4) (Fin 4) ℝ) : ext4 M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h (Fin.castLE (by norm_num) i)) (Fin.castLE (by norm_num) j)
    fin_cases i <;> fin_cases j <;> simpa [ext4] using this
  · rintro rfl; ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Zero extension preserves and reflects `η`-skewness. -/
theorem isEtaSkew6_ext4_iff (M : Matrix (Fin 4) (Fin 4) ℝ) : IsEtaSkew6 (ext4 M) ↔ IsEtaSkew4 M := by
  unfold IsEtaSkew6 IsEtaSkew4
  rw [ext4_transpose, ext4_mul_η6, η6_mul_ext4, ext4_add, ext4_eq_zero_iff]

/-! ### K8.1: the six local generators -/

/-- **K8.1.** Each local generator is `η4`-skew. -/
theorem localGen_etaSkew (p : Fin 6) : IsEtaSkew4 (localGen p) := by
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [localGen, L01r, L02r, L03r, L12r, L13r, L23r, η4, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- **K8.1.** Each local generator, as a `6 × 6` matrix, is `η6`-skew (lies in `so(4,2)`). -/
theorem localGen6_etaSkew6 (p : Fin 6) : IsEtaSkew6 (localGen6 p) := by
  rw [localGen6_eq_ext4, isEtaSkew6_ext4_iff]; exact localGen_etaSkew p

/-- **K8.1.** The six local generators are linearly independent. -/
theorem localGen_linearIndependent : LinearIndependent ℝ localGen := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h01 := congrFun (congrFun hg 0) 1
  have h02 := congrFun (congrFun hg 0) 2
  have h03 := congrFun (congrFun hg 0) 3
  have h12 := congrFun (congrFun hg 1) 2
  have h13 := congrFun (congrFun hg 1) 3
  have h23 := congrFun (congrFun hg 2) 3
  simp [localGen, L01r, L02r, L03r, L12r, L13r, L23r, Fin.sum_univ_succ] at h01 h02 h03 h12 h13 h23
  fin_cases i <;> simp_all

/-- **K8.1.** `so(3,1)` is six-dimensional. -/
theorem finrank_so31 : Module.finrank ℝ so31 = 6 := by
  rw [so31, finrank_span_eq_card localGen_linearIndependent]; simp

/-- The `η4`-skew matrices form a submodule. -/
def etaSkewSubmodule : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := {X | IsEtaSkew4 X}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq, IsEtaSkew4] at *
    rw [transpose_add, add_mul, mul_add, ← add_assoc, add_assoc (Xᵀ * η4), add_comm (Yᵀ * η4),
      ← add_assoc, hX, zero_add, hY]
  zero_mem' := by simp [IsEtaSkew4]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq, IsEtaSkew4] at *
    rw [transpose_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, hX, smul_zero]

/-- Every `η4`-skew matrix is the register's coordinate combination of the six generators,
`X = Σ_(a,b) η_b X_ab · L_ab`. -/
theorem etaSkew_decomp (X : Matrix (Fin 4) (Fin 4) ℝ) (hX : IsEtaSkew4 X) :
    X = X 0 1 • L01r + X 0 2 • L02r + (-(X 0 3)) • L03r + X 1 2 • L12r + (-(X 1 3)) • L13r +
      (-(X 2 3)) • L23r := by
  have h : ∀ i j, (Xᵀ * η4 + η4 * X) i j = 0 := fun i j => by rw [hX]; rfl
  have s00 := h 0 0; have s11 := h 1 1; have s22 := h 2 2; have s33 := h 3 3
  have a01 := h 0 1; have a02 := h 0 2; have a12 := h 1 2
  have b03 := h 0 3; have b13 := h 1 3; have b23 := h 2 3
  simp [η4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at s00 s11 s22 s33 a01 a02 a12 b03 b13 b23
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L01r, L02r, L03r, L12r, L13r, L23r] <;> linarith

/-- **K8.1.** `so(3,1)` = the span of the six local generators = the `η4`-skew matrices. -/
theorem mem_so31_iff (X : Matrix (Fin 4) (Fin 4) ℝ) : X ∈ so31 ↔ IsEtaSkew4 X := by
  constructor
  · intro hX
    have hle : so31 ≤ etaSkewSubmodule := by
      rw [so31, Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact localGen_etaSkew p
    exact hle hX
  · intro hX
    rw [etaSkew_decomp X hX]
    have hm : ∀ p, localGen p ∈ so31 := fun p => Submodule.subset_span ⟨p, rfl⟩
    have h0 : L01r ∈ so31 := hm 0
    have h1 : L02r ∈ so31 := hm 1
    have h2 : L03r ∈ so31 := hm 2
    have h3 : L12r ∈ so31 := hm 3
    have h4 : L13r ∈ so31 := hm 4
    have h5 : L23r ∈ so31 := hm 5
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1))
      (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3)) (Submodule.smul_mem _ _ h4))
      (Submodule.smul_mem _ _ h5)

/-- **K8.1 (closure).** The commutator of two `η`-skew matrices is `η`-skew, for any `η`: the
`η`-skew matrices form a Lie subalgebra. -/
theorem etaSkew_bracket {n : Type*} [Fintype n] [DecidableEq n] (η X Y : Matrix n n ℝ)
    (hX : Xᵀ * η + η * X = 0) (hY : Yᵀ * η + η * Y = 0) :
    (X * Y - Y * X)ᵀ * η + η * (X * Y - Y * X) = 0 := by
  have hX' : Xᵀ * η = -(η * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᵀ * η = -(η * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : (X * Y)ᵀ * η = η * (Y * X) := by
    rw [transpose_mul, Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', neg_mul,
      neg_neg, Matrix.mul_assoc]
  have e2 : (Y * X)ᵀ * η = η * (X * Y) := by
    rw [transpose_mul, Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', neg_mul,
      neg_neg, Matrix.mul_assoc]
  rw [transpose_sub, sub_mul, e1, e2, mul_sub]
  abel

/-- **K8.1 (closure).** `so(3,1)` is closed under the commutator. -/
theorem so31_bracket_mem (X Y : Matrix (Fin 4) (Fin 4) ℝ) (hX : X ∈ so31) (hY : Y ∈ so31) :
    X * Y - Y * X ∈ so31 := by
  rw [mem_so31_iff] at *
  exact etaSkew_bracket η4 X Y hX hY

/-- **K8.1 (closure).** `so(4,2)`-skew matrices are closed under the commutator. -/
theorem etaSkew6_bracket (X Y : Matrix (Fin 6) (Fin 6) ℝ) (hX : IsEtaSkew6 X) (hY : IsEtaSkew6 Y) :
    IsEtaSkew6 (X * Y - Y * X) :=
  etaSkew_bracket η6 X Y hX hY

/-! The fifteen structure constants on `0123`. -/

theorem bracket_01_02 : L01r * L02r - L02r * L01r = -L12r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L01r, L02r, L12r]
theorem bracket_01_03 : L01r * L03r - L03r * L01r = -L13r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L01r, L03r, L13r]
theorem bracket_01_12 : L01r * L12r - L12r * L01r = L02r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L01r, L12r, L02r]
theorem bracket_01_13 : L01r * L13r - L13r * L01r = L03r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L01r, L13r, L03r]
theorem bracket_01_23 : L01r * L23r - L23r * L01r = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L01r, L23r]
theorem bracket_02_03 : L02r * L03r - L03r * L02r = -L23r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L02r, L03r, L23r]
theorem bracket_02_12 : L02r * L12r - L12r * L02r = -L01r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L02r, L12r, L01r]
theorem bracket_02_13 : L02r * L13r - L13r * L02r = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L02r, L13r]
theorem bracket_02_23 : L02r * L23r - L23r * L02r = L03r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L02r, L23r, L03r]
theorem bracket_03_12 : L03r * L12r - L12r * L03r = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L03r, L12r]
theorem bracket_03_13 : L03r * L13r - L13r * L03r = L01r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L03r, L13r, L01r]
theorem bracket_03_23 : L03r * L23r - L23r * L03r = L02r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L03r, L23r, L02r]
theorem bracket_12_13 : L12r * L13r - L13r * L12r = -L23r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L12r, L13r, L23r]
theorem bracket_12_23 : L12r * L23r - L23r * L12r = L13r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L12r, L23r, L13r]
theorem bracket_13_23 : L13r * L23r - L23r * L13r = L12r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L13r, L23r, L12r]

/-! ### The arithmetic side in place coordinates `(a, b, u, v)` and the link to K7 -/

/-- The trace form `tr(X Xᵀ) = a² + b² + 2(u² − v²)` in place coordinates: `T = diag(1,1,2,−2)`. -/
def Tarith : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, -2]
/-- `T⁻¹ = diag(1,1,½,−½)`. -/
noncomputable def Tinv : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1/2, 0; 0, 0, 0, -1/2]
/-- `S = diag(1, 1, √2, √2)`, carrying `T` to `η4`: `Sᵀ η4 S = T`. -/
noncomputable def Smat : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, √2, 0; 0, 0, 0, √2]
/-- `S⁻¹ = diag(1, 1, √2/2, √2/2)`. -/
noncomputable def Sinv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, √2 / 2, 0; 0, 0, 0, √2 / 2]

theorem cArith_eq_Preg : cArith = Preg := rfl
theorem Preg_eq_η4 : Preg = η4 := rfl
theorem Kmat_eq_neg_L23r : Kmat = -L23r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Kmat, L23r]

/-- Place coordinates `(a, b, Re z, Im z)` of a point of the place space `ℝ² × ℂ`. -/
def placeCoords (p : PlaceSpace 2) : Fin 4 → ℝ := ![p.1 0, p.1 1, (p.2 0).re, (p.2 0).im]

/-- K7's `boostGen` (the generator of `iConj`) is `K` in place coordinates. -/
theorem placeCoords_boostGen (p : PlaceSpace 2) :
    placeCoords (boostGen 2 p) = Kmat.mulVec (placeCoords p) := by
  ext i; fin_cases i <;>
    simp [placeCoords, boostGen_apply, Kmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- K7's Galois conjugation is `c` in place coordinates. -/
theorem placeCoords_galoisConj (p : PlaceSpace 2) :
    placeCoords (galoisConj 2 p) = cArith.mulVec (placeCoords p) := by
  ext i; fin_cases i <;>
    simp [placeCoords, galoisConj_apply, cArith, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- K7's trace form is `T = diag(1, 1, 2, −2)` in place coordinates. -/
theorem traceB_eq_placeCoords (X Y : PlaceSpace 2) :
    traceB 2 X Y = placeCoords X ⬝ᵥ Tarith.mulVec (placeCoords Y) := by
  simp [traceB, placeCoords, Tarith, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Complex.mul_re]
  ring

/-- The phase generator on the place space: `(x, z) ↦ (0, i z)` (`d/dθ phaseV θ` at `θ = 0`). -/
def phaseGen : PlaceSpace 2 →ₗ[ℝ] PlaceSpace 2 where
  toFun p := (0, fun j => Complex.I * p.2 j)
  map_add' p q := Prod.ext (zero_add (0 : Fin 2 → ℝ)).symm (funext fun j => by simp [mul_add])
  map_smul' c p := Prod.ext (smul_zero c).symm (funext fun j => by
    simp only [Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Complex.real_smul]; ring)

/-- The phase generator is `J` in place coordinates. -/
theorem placeCoords_phaseGen (p : PlaceSpace 2) :
    placeCoords (phaseGen p) = Jmat.mulVec (placeCoords p) := by
  ext i; fin_cases i <;>
    simp [placeCoords, phaseGen, Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-! ### `S` and the √2 bookkeeping -/

theorem η4_mul_η4 : η4 * η4 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [η4, Matrix.mul_apply, Fin.sum_univ_succ]

theorem Tinv_mul_T : Tinv * Tarith = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Tinv, Tarith, Matrix.mul_apply, Fin.sum_univ_succ]

theorem Smat_mul_Sinv : Smat * Sinv = 1 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Smat, Sinv, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination h2
      | linear_combination (-1 : ℝ) * h2
      | linear_combination (1 / 2 : ℝ) * h2

theorem Sinv_mul_Smat : Sinv * Smat = 1 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Smat, Sinv, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination h2
      | linear_combination (-1 : ℝ) * h2
      | linear_combination (1 / 2 : ℝ) * h2

/-- `Sᵀ η4 S = T`: `S` is an isometry from the arithmetic trace form to the register's `η4`. -/
theorem S_isometry : Smatᵀ * η4 * Smat = Tarith := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Smat, η4, Tarith, Matrix.mul_apply, Fin.sum_univ_succ]

theorem Sinv_T_Sinv : Sinvᵀ * Tarith * Sinv = η4 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Sinv, η4, Tarith, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination h2
      | linear_combination (-1 : ℝ) * h2
      | linear_combination (1 / 2 : ℝ) * h2

/-- `S` is scalar on the complex block, so it fixes `K`, `J`, `c` under conjugation. -/
theorem S_K_Sinv : Smat * Kmat * Sinv = Kmat := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Smat, Sinv, Kmat, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination h2
      | linear_combination (-1 : ℝ) * h2
      | linear_combination (1 / 2 : ℝ) * h2

theorem S_J_Sinv : Smat * Jmat * Sinv = Jmat := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Smat, Sinv, Jmat, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination h2
      | linear_combination (-1 : ℝ) * h2
      | linear_combination (1 / 2 : ℝ) * h2

theorem Sinv_comm_c : Sinv * cArith = cArith * Sinv := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Sinv, cArith, Matrix.mul_apply, Fin.sum_univ_succ]

/-! ### Inverses of isometries -/

/-- If `Λᵀ A Λ = B` and `Binv B = 1`, then `Λ⁻¹ = Binv Λᵀ A`. -/
theorem inv_of_form {n : Type*} [Fintype n] [DecidableEq n] (Λ A B Binv : Matrix n n ℝ)
    (hΛ : Λᵀ * A * Λ = B) (hB : Binv * B = 1) : Λ⁻¹ = Binv * Λᵀ * A := by
  apply Matrix.inv_eq_left_inv
  calc Binv * Λᵀ * A * Λ = Binv * (Λᵀ * A * Λ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hΛ, hB]

/-- For invertible `Λ`, `Λ c Λ⁻¹ = P ↔ Λ c = P Λ`. -/
theorem conj_eq_iff {n : Type*} [Fintype n] [DecidableEq n] (Λ B : Matrix n n ℝ) (hB : B * Λ = 1)
    (c P : Matrix n n ℝ) : Λ * c * Λ⁻¹ = P ↔ Λ * c = P * Λ := by
  have hinv : Λ⁻¹ = B := Matrix.inv_eq_left_inv hB
  have hB' : Λ * B = 1 := mul_eq_one_comm.mp hB
  rw [hinv]
  constructor
  · intro h
    calc Λ * c = Λ * c * (B * Λ) := by rw [hB, Matrix.mul_one]
      _ = (Λ * c * B) * Λ := by simp only [Matrix.mul_assoc]
      _ = P * Λ := by rw [h]
  · intro h
    calc Λ * c * B = P * Λ * B := by rw [h]
      _ = P := by rw [Matrix.mul_assoc, hB', Matrix.mul_one]

/-! ### K8.2: the time-canonical bridge -/

theorem orth_entries (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1) :
    R 0 0 * R 0 0 + R 1 0 * R 1 0 + R 2 0 * R 2 0 = 1 ∧
    R 0 0 * R 0 1 + R 1 0 * R 1 1 + R 2 0 * R 2 1 = 0 ∧
    R 0 0 * R 0 2 + R 1 0 * R 1 2 + R 2 0 * R 2 2 = 0 ∧
    R 0 1 * R 0 1 + R 1 1 * R 1 1 + R 2 1 * R 2 1 = 1 ∧
    R 0 1 * R 0 2 + R 1 1 * R 1 2 + R 2 1 * R 2 2 = 0 ∧
    R 0 2 * R 0 2 + R 1 2 * R 1 2 + R 2 2 * R 2 2 = 1 := by
  have r : ∀ i j, (Rᵀ * R) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j => by rw [hR]
  have r00 := r 0 0; have r01 := r 0 1; have r02 := r 0 2
  have r11 := r 1 1; have r12 := r 1 2; have r22 := r 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at r00 r01 r02 r11 r12 r22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **K8.2 (core).** `Λ ∈ O(3,1)` commuting with `P` is `diag(R, s)` with `R ∈ O(3)`, `s = ±1`. -/
theorem time_canonical_comm (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hη : Λᵀ * η4 * Λ = η4)
    (hcomm : Λ * cArith = Preg * Λ) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ), Rᵀ * R = 1 ∧ (s = 1 ∨ s = -1) ∧ Λ = blockDiag R s := by
  have hc : ∀ i j, (Λ * cArith) i j = (Preg * Λ) i j := fun i j => by rw [hcomm]
  have z03 := hc 0 3; have z13 := hc 1 3; have z23 := hc 2 3
  have z30 := hc 3 0; have z31 := hc 3 1; have z32 := hc 3 2
  simp [cArith, Preg, Matrix.mul_apply, Fin.sum_univ_succ] at z03 z13 z23 z30 z31 z32
  have e03 : Λ 0 3 = 0 := by linarith
  have e13 : Λ 1 3 = 0 := by linarith
  have e23 : Λ 2 3 = 0 := by linarith
  have e30 : Λ 3 0 = 0 := by linarith
  have e31 : Λ 3 1 = 0 := by linarith
  have e32 : Λ 3 2 = 0 := by linarith
  have ho : ∀ i j, (Λᵀ * η4 * Λ) i j = η4 i j := fun i j => by rw [hη]
  have o00 := ho 0 0; have o01 := ho 0 1; have o02 := ho 0 2
  have o11 := ho 1 1; have o12 := ho 1 2; have o22 := ho 2 2; have o33 := ho 3 3
  simp [η4, Matrix.mul_apply, Fin.sum_univ_succ, e03, e13, e23, e30, e31, e32] at o00 o01 o02 o11 o12 o22 o33
  refine ⟨!![Λ 0 0, Λ 0 1, Λ 0 2; Λ 1 0, Λ 1 1, Λ 1 2; Λ 2 0, Λ 2 1, Λ 2 2], Λ 3 3, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
  · have hs : (Λ 3 3 - 1) * (Λ 3 3 + 1) = 0 := by
      linear_combination o33
    rcases mul_eq_zero.mp hs with h | h
    · left; linarith
    · right; linarith
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [blockDiag, e03, e13, e23, e30, e31, e32]

/-- **K8.2 (time-canonical).** For `Λ ∈ O(3,1)` on `0123` with `Λ c Λ⁻¹ = P` (Galois conjugation
carried to the register's time reflection), `Λ = diag(R, s)` with `RᵀR = 1` and `s = ±1`: the
imaginary axis of the complex place IS the time axis up to sign, and the residual freedom is
`O(3) × {±1}` on `(a, b, Re z) × time-sign`. -/
theorem time_canonical (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hη : Λᵀ * η4 * Λ = η4)
    (hc : Λ * cArith * Λ⁻¹ = Preg) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ), Rᵀ * R = 1 ∧ (s = 1 ∨ s = -1) ∧ Λ = blockDiag R s := by
  have hB : (η4 * Λᵀ * η4) * Λ = 1 := by
    calc η4 * Λᵀ * η4 * Λ = η4 * (Λᵀ * η4 * Λ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hη, η4_mul_η4]
  exact time_canonical_comm Λ hη ((conj_eq_iff Λ _ hB cArith Preg).mp hc)

/-- **K8.2 (the clean form).** For `Λ ∈ O(3,1)`, `Λ P Λ⁻¹ = P ⟺ Λ Λᵀ = 1`: the solutions are
`O(3,1) ∩ O(4)`. -/
theorem conj_P_iff_orthogonal (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hη : Λᵀ * η4 * Λ = η4) :
    Λ * Preg * Λ⁻¹ = Preg ↔ Λ * Λᵀ = 1 := by
  have hinv : Λ⁻¹ = η4 * Λᵀ * η4 := inv_of_form Λ η4 η4 η4 hη η4_mul_η4
  have key : Λ * Preg * Λ⁻¹ = Λ * Λᵀ * η4 := by
    rw [hinv, Preg_eq_η4]
    calc Λ * η4 * (η4 * Λᵀ * η4) = Λ * (η4 * η4) * Λᵀ * η4 := by simp only [Matrix.mul_assoc]
      _ = Λ * Λᵀ * η4 := by rw [η4_mul_η4, Matrix.mul_one]
  rw [key]
  constructor
  · intro h
    calc Λ * Λᵀ = Λ * Λᵀ * η4 * η4 := by rw [Matrix.mul_assoc, η4_mul_η4, Matrix.mul_one]
      _ = 1 := by rw [h, Preg_eq_η4, η4_mul_η4]
  · intro h; rw [h, Matrix.one_mul, Preg_eq_η4]

/-- **K8.2 (converse).** Every `diag(R, s)` with `RᵀR = 1`, `s² = 1` is in `O(3,1)` and commutes
with `P`. -/
theorem blockDiag_isometry (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s * s = 1) :
    (blockDiag R s)ᵀ * η4 * blockDiag R s = η4 ∧ blockDiag R s * Preg = Preg * blockDiag R s := by
  obtain ⟨r00, r01, r02, r11, r12, r22⟩ := orth_entries R hR
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockDiag, η4, Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [blockDiag, Preg, Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockDiagT_mul_blockDiag (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s * s = 1) : blockDiag Rᵀ s * blockDiag R s = 1 := by
  obtain ⟨r00, r01, r02, r11, r12, r22⟩ := orth_entries R hR
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith

/-- `diag(R, s)⁻¹ = diag(Rᵀ, s)`. -/
theorem blockDiag_inv (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1) (hs : s * s = 1) :
    (blockDiag R s)⁻¹ = blockDiag Rᵀ s :=
  Matrix.inv_eq_left_inv (blockDiagT_mul_blockDiag R s hR hs)

/-- `(diag(R, s) S)⁻¹ = S⁻¹ diag(Rᵀ, s)`. -/
theorem blockDiag_S_inv (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s * s = 1) : (blockDiag R s * Smat)⁻¹ = Sinv * blockDiag Rᵀ s := by
  apply Matrix.inv_eq_left_inv
  calc Sinv * blockDiag Rᵀ s * (blockDiag R s * Smat)
      = Sinv * (blockDiag Rᵀ s * blockDiag R s) * Smat := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [blockDiagT_mul_blockDiag R s hR hs, Matrix.mul_one, Sinv_mul_Smat]

/-- **K8.2 (for `Λ' = Λ ∘ S`).** An isometry `Λ' : (arith, T) → (0123, η4)`, i.e.
`Λ'ᵀ η4 Λ' = T`, with `Λ' c Λ'⁻¹ = P`, is `diag(R, s) ∘ S` with `RᵀR = 1`, `s = ±1`. (The scaling `S`
carries the arithmetic trace form `T = diag(1, 1, 2, −2)` to `η4`.) -/
theorem time_canonical' (Λ' : Matrix (Fin 4) (Fin 4) ℝ) (hT : Λ'ᵀ * η4 * Λ' = Tarith)
    (hc : Λ' * cArith * Λ'⁻¹ = Preg) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ), Rᵀ * R = 1 ∧ (s = 1 ∨ s = -1) ∧
      Λ' = blockDiag R s * Smat := by
  have hB : (Tinv * Λ'ᵀ * η4) * Λ' = 1 := by
    calc Tinv * Λ'ᵀ * η4 * Λ' = Tinv * (Λ'ᵀ * η4 * Λ') := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT, Tinv_mul_T]
  have hcomm : Λ' * cArith = Preg * Λ' := (conj_eq_iff Λ' _ hB cArith Preg).mp hc
  have hη : (Λ' * Sinv)ᵀ * η4 * (Λ' * Sinv) = η4 := by
    rw [transpose_mul]
    calc Sinvᵀ * Λ'ᵀ * η4 * (Λ' * Sinv) = Sinvᵀ * (Λ'ᵀ * η4 * Λ') * Sinv := by
          simp only [Matrix.mul_assoc]
      _ = η4 := by rw [hT, Sinv_T_Sinv]
  have hcomm2 : (Λ' * Sinv) * cArith = Preg * (Λ' * Sinv) := by
    calc Λ' * Sinv * cArith = Λ' * (Sinv * cArith) := by rw [Matrix.mul_assoc]
      _ = Λ' * (cArith * Sinv) := by rw [Sinv_comm_c]
      _ = (Λ' * cArith) * Sinv := by rw [Matrix.mul_assoc]
      _ = Preg * Λ' * Sinv := by rw [hcomm]
      _ = Preg * (Λ' * Sinv) := by rw [Matrix.mul_assoc]
  obtain ⟨R, s, hR, hs, hΛeq⟩ := time_canonical_comm (Λ' * Sinv) hη hcomm2
  refine ⟨R, s, hR, hs, ?_⟩
  calc Λ' = Λ' * (Sinv * Smat) := by rw [Sinv_mul_Smat, Matrix.mul_one]
    _ = (Λ' * Sinv) * Smat := by rw [Matrix.mul_assoc]
    _ = blockDiag R s * Smat := by rw [hΛeq]

/-! ### K8.3: the boost span -/

/-- **K8.3 (boost span).** `diag(R,s) · K · diag(Rᵀ,s) = −s (n₀ L03 + n₁ L13 + n₂ L23)` with
`n = R e₂` (an exact identity; no orthogonality used). -/
theorem boost_span (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    blockDiag R s * Kmat * blockDiag Rᵀ s =
      (-s) • (R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, Kmat, L03r, L13r, L23r, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Conjugation by `Λ' = diag(R,s) S` agrees with conjugation by `diag(R,s)` on `K`. -/
theorem conjS_K (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    (blockDiag R s * Smat) * Kmat * (Sinv * blockDiag Rᵀ s) =
      blockDiag R s * Kmat * blockDiag Rᵀ s := by
  calc (blockDiag R s * Smat) * Kmat * (Sinv * blockDiag Rᵀ s)
      = blockDiag R s * (Smat * Kmat * Sinv) * blockDiag Rᵀ s := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [S_K_Sinv]

theorem conjS_J (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    (blockDiag R s * Smat) * Jmat * (Sinv * blockDiag Rᵀ s) =
      blockDiag R s * Jmat * blockDiag Rᵀ s := by
  calc (blockDiag R s * Smat) * Jmat * (Sinv * blockDiag Rᵀ s)
      = blockDiag R s * (Smat * Jmat * Sinv) * blockDiag Rᵀ s := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [S_J_Sinv]

/-- **K8.3 (with `S`).** `Λ' K Λ'⁻¹ = −s (n₀ L03 + n₁ L13 + n₂ L23)` for `Λ' = diag(R,s) S`. -/
theorem boost_span' (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1) (hs : s * s = 1) :
    (blockDiag R s * Smat) * Kmat * (blockDiag R s * Smat)⁻¹ =
      (-s) • (R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r) := by
  rw [blockDiag_S_inv R s hR hs, conjS_K, boost_span]

/-- The conjugated `K` lies in `so(3,1)`. -/
theorem boost_span_mem_so31 (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    blockDiag R s * Kmat * blockDiag Rᵀ s ∈ so31 := by
  rw [boost_span]
  have h2 : L03r ∈ so31 := Submodule.subset_span ⟨2, rfl⟩
  have h4 : L13r ∈ so31 := Submodule.subset_span ⟨4, rfl⟩
  have h5 : L23r ∈ so31 := Submodule.subset_span ⟨5, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h4)) (Submodule.smul_mem _ _ h5))

/-! ### K8.4: the phase is excluded -/

/-- `J` itself is not `η4`-skew. -/
theorem Jmat_not_etaSkew : ¬ IsEtaSkew4 Jmat := by
  intro h
  have e := congrFun (congrFun h 2) 3
  simp [Jmat, η4, Matrix.mul_apply, Fin.sum_univ_succ] at e

/-- The skewness defect of the conjugated phase: `2 s (n₀ L03 + n₁ L13 + n₂ L23)`. -/
theorem phase_residual (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    (blockDiag R s * Jmat * blockDiag Rᵀ s)ᵀ * η4 + η4 * (blockDiag R s * Jmat * blockDiag Rᵀ s) =
      (2 * s) • (R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, Jmat, η4, L03r, L13r, L23r, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- **K8.4 (phase excluded).** For every `Λ = diag(R, s)` of K8.2, `Λ J Λ⁻¹` is not `η4`-skew:
the phase generator pulls back to no element of `so(3,1)`. -/
theorem phase_excluded (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s = 1 ∨ s = -1) : ¬ IsEtaSkew4 (blockDiag R s * Jmat * blockDiag Rᵀ s) := by
  intro h
  unfold IsEtaSkew4 at h
  rw [phase_residual] at h
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have e03 := congrFun (congrFun h 0) 3
  have e13 := congrFun (congrFun h 1) 3
  have e23 := congrFun (congrFun h 2) 3
  simp [L03r, L13r, L23r, hs0] at e03 e13 e23
  obtain ⟨-, -, -, -, -, r22⟩ := orth_entries R hR
  simp [e03, e13, e23] at r22

/-- **K8.4.** Hence `Λ J Λ⁻¹ ∉ so(3,1)`. -/
theorem phase_not_mem_so31 (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s = 1 ∨ s = -1) : blockDiag R s * Jmat * blockDiag Rᵀ s ∉ so31 := by
  rw [mem_so31_iff]; exact phase_excluded R s hR hs

/-- **K8.4 (zero-extended).** `Λ J Λ⁻¹`, extended by zero to `ℝ⁶`, is not `η6`-skew: not in
`so(4,2)`. -/
theorem phase_excluded6 (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s = 1 ∨ s = -1) : ¬ IsEtaSkew6 (ext4 (blockDiag R s * Jmat * blockDiag Rᵀ s)) := by
  rw [isEtaSkew6_ext4_iff]; exact phase_excluded R s hR hs

/-- **K8.4 (with `S`).** -/
theorem phase_excluded' (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s = 1 ∨ s = -1) :
    ¬ IsEtaSkew4 ((blockDiag R s * Smat) * Jmat * (blockDiag R s * Smat)⁻¹) := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [blockDiag_S_inv R s hR hs2, conjS_J]; exact phase_excluded R s hR hs

/-! ### K8.5: the Hodge exchange -/

theorem Hmat_mul_Hmat : Hmat * Hmat = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Hmat, Matrix.mul_apply, Fin.sum_univ_succ]

/-- On the ordered pair `(L01, L23)` (indices `0, 5`), `H` is HodgeBulkScreen's
`hodgeRotation = !![0, -1; 1, 0]`. -/
theorem hodge_pair_L01_L23 : Hmat.submatrix ![0, 5] ![0, 5] = !![0, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- On the pairs `(L02, L13)` and `(L03, L12)` it is `−hodgeRotation` (pair-basis orientation). -/
theorem hodge_pair_L02_L13 : Hmat.submatrix ![1, 4] ![1, 4] = -!![0, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Hmat]

theorem hodge_pair_L03_L12 : Hmat.submatrix ![2, 3] ![2, 3] = -!![0, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Hmat]

theorem hodge_L01 : hodgeOp L01r = L23r := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hodgeOp, fromCoords, coords4, Hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      L01r, L02r, L03r, L12r, L13r, L23r]
theorem hodge_L02 : hodgeOp L02r = -L13r := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hodgeOp, fromCoords, coords4, Hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      L01r, L02r, L03r, L12r, L13r, L23r]
theorem hodge_L03 : hodgeOp L03r = -L12r := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hodgeOp, fromCoords, coords4, Hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      L01r, L02r, L03r, L12r, L13r, L23r]
theorem hodge_L12 : hodgeOp L12r = L03r := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hodgeOp, fromCoords, coords4, Hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      L01r, L02r, L03r, L12r, L13r, L23r]
theorem hodge_L13 : hodgeOp L13r = L02r := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hodgeOp, fromCoords, coords4, Hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      L01r, L02r, L03r, L12r, L13r, L23r]
theorem hodge_L23 : hodgeOp L23r = -L01r := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hodgeOp, fromCoords, coords4, Hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      L01r, L02r, L03r, L12r, L13r, L23r]

theorem coords4_fromCoords (c : Fin 6 → ℝ) : coords4 (fromCoords c) = c := by
  ext i; fin_cases i <;> simp [coords4, fromCoords, L01r, L02r, L03r, L12r, L13r, L23r]

/-- An `η4`-skew matrix is reconstructed from its register coordinates. -/
theorem fromCoords_coords4 (X : Matrix (Fin 4) (Fin 4) ℝ) (hX : IsEtaSkew4 X) :
    fromCoords (coords4 X) = X := by
  have h : ∀ i j, (Xᵀ * η4 + η4 * X) i j = 0 := fun i j => by rw [hX]; rfl
  have s00 := h 0 0; have s11 := h 1 1; have s22 := h 2 2; have s33 := h 3 3
  have a01 := h 0 1; have a02 := h 0 2; have a12 := h 1 2
  have b03 := h 0 3; have b13 := h 1 3; have b23 := h 2 3
  simp [η4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at s00 s11 s22 s33 a01 a02 a12 b03 b13 b23
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fromCoords, coords4, L01r, L02r, L03r, L12r, L13r, L23r] <;> linarith

theorem fromCoords_neg (c : Fin 6 → ℝ) : fromCoords (-c) = -fromCoords c := by
  simp only [fromCoords, Pi.neg_apply, neg_smul]; abel

/-- `H² = −1` on `so(3,1)`. -/
theorem hodgeOp_hodgeOp (X : Matrix (Fin 4) (Fin 4) ℝ) (hX : IsEtaSkew4 X) :
    hodgeOp (hodgeOp X) = -X := by
  unfold hodgeOp
  rw [coords4_fromCoords, Matrix.mulVec_mulVec, Hmat_mul_Hmat, Matrix.neg_mulVec,
    Matrix.one_mulVec, fromCoords_neg, fromCoords_coords4 X hX]

/-- **K8.5 (at `R = 1`).** `H(K) = L01`: the Hodge dual of the arithmetic boost is the rotation
of the two real places. -/
theorem hodge_K : hodgeOp Kmat = L01r := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hodgeOp, fromCoords, coords4, Hmat, Kmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      L01r, L02r, L03r, L12r, L13r, L23r]

/-- **K8.5 (Hodge exchange).** `H(diag(R,s) K diag(Rᵀ,s)) = s (n₀ L12 − n₁ L02 + n₂ L01)`,
`n = R e₂`: the Hodge sends the image of the complex-place plane to the rotation in `n⊥`. -/
theorem hodge_exchange (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    hodgeOp (blockDiag R s * Kmat * blockDiag Rᵀ s) =
      s • (R 0 2 • L12r - R 1 2 • L02r + R 2 2 • L01r) := by
  rw [boost_span]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hodgeOp, fromCoords, coords4, Hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      L01r, L02r, L03r, L12r, L13r, L23r]

/-- **K8.5 (with `S`).** -/
theorem hodge_exchange' (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s * s = 1) :
    hodgeOp ((blockDiag R s * Smat) * Kmat * (blockDiag R s * Smat)⁻¹) =
      s • (R 0 2 • L12r - R 1 2 • L02r + R 2 2 • L01r) := by
  rw [blockDiag_S_inv R s hR hs, conjS_K, hodge_exchange]

/-! ### K8.6: the divide is the self-dual split -/

theorem HC_eq_map : HC = Hmat.map ((↑) : ℝ → ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [HC, Hmat]

theorem HC_mul_HC : HC * HC = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [HC, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Close a scalar identity in `ℂ` that holds modulo `I² = −1`. -/
macro "cscalar" : tactic => `(tactic| first
  | ring1
  | (ring_nf; simp only [Complex.I_sq]; done)
  | (ring_nf; simp only [Complex.I_sq]; ring1)
  | (apply Complex.ext <;> simp <;> ring1))

theorem form_mul (a b c d : ℂ) :
    (a • (1 : Matrix (Fin 6) (Fin 6) ℂ) + b • HC) * (c • 1 + d • HC) =
      (a * c - b * d) • 1 + (a * d + b * c) • HC := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, HC_mul_HC]
  module

theorem coeff_eq {a b a' b' : ℂ} (ha : a = a') (hb : b = b') :
    a • (1 : Matrix (Fin 6) (Fin 6) ℂ) + b • HC = a' • 1 + b' • HC := by rw [ha, hb]

theorem Pplus_form : Pplus = (1 / 2 : ℂ) • 1 + (-(Complex.I / 2)) • HC := by
  unfold Pplus chirality; module

theorem Pminus_form : Pminus = (1 / 2 : ℂ) • 1 + (Complex.I / 2) • HC := by
  unfold Pminus chirality; module

theorem chirality_sq : chirality * chirality = 1 := by
  simp only [chirality, smul_mul_assoc, mul_smul_comm, smul_smul, HC_mul_HC]
  simp [Complex.I_mul_I]

/-- **K8.6.** `P₊ + P₋ = 1`. -/
theorem Pplus_add_Pminus : Pplus + Pminus = 1 := by
  rw [Pplus_form, Pminus_form]; module

/-- **K8.6.** `P₊² = P₊`. -/
theorem Pplus_mul_Pplus : Pplus * Pplus = Pplus := by
  rw [Pplus_form, form_mul]
  exact coeff_eq (by cscalar) (by cscalar)

/-- **K8.6.** `P₋² = P₋`. -/
theorem Pminus_mul_Pminus : Pminus * Pminus = Pminus := by
  rw [Pminus_form, form_mul]
  exact coeff_eq (by cscalar) (by cscalar)

/-- **K8.6.** `P₊ P₋ = 0`. -/
theorem Pplus_mul_Pminus : Pplus * Pminus = 0 := by
  rw [Pplus_form, Pminus_form, form_mul,
    show (0 : Matrix (Fin 6) (Fin 6) ℂ) = (0 : ℂ) • 1 + (0 : ℂ) • HC by simp]
  exact coeff_eq (by cscalar) (by cscalar)

/-- **K8.6.** `P₋ P₊ = 0`. -/
theorem Pminus_mul_Pplus : Pminus * Pplus = 0 := by
  rw [Pplus_form, Pminus_form, form_mul,
    show (0 : Matrix (Fin 6) (Fin 6) ℂ) = (0 : ℂ) • 1 + (0 : ℂ) • HC by simp]
  exact coeff_eq (by cscalar) (by cscalar)

/-- **K8.6.** `H P₊ = i P₊`: `P₊` projects on the `H = +i` eigenspace (self-dual). -/
theorem HC_mul_Pplus : HC * Pplus = Complex.I • Pplus := by
  have h1 : HC * Pplus =
      ((0 : ℂ) • 1 + (1 : ℂ) • HC) * ((1 / 2 : ℂ) • 1 + (-(Complex.I / 2)) • HC) := by
    rw [← Pplus_form]; simp
  rw [h1, form_mul, Pplus_form, smul_add, smul_smul, smul_smul]
  exact coeff_eq (by cscalar) (by cscalar)

/-- **K8.6.** `H P₋ = −i P₋`: `P₋` projects on the `H = −i` eigenspace (anti-self-dual). -/
theorem HC_mul_Pminus : HC * Pminus = (-Complex.I) • Pminus := by
  have h1 : HC * Pminus =
      ((0 : ℂ) • 1 + (1 : ℂ) • HC) * ((1 / 2 : ℂ) • 1 + (Complex.I / 2) • HC) := by
    rw [← Pminus_form]; simp
  rw [h1, form_mul, Pminus_form, smul_add, smul_smul, smul_smul]
  exact coeff_eq (by cscalar) (by cscalar)

/-- **K8.7 (the divide in Holst form).** `D = ½(ρ+Q)·1 − ½ i(ρ−Q)·H`. -/
theorem divide_form (ρ Q : ℝ) :
    divide ρ Q = (((ρ : ℂ) + Q) / 2) • 1 + (-(Complex.I * ((ρ : ℂ) - Q) / 2)) • HC := by
  unfold divide; rw [Pplus_form, Pminus_form]; module

theorem divideFlip_form (ρ Q : ℝ) :
    divideFlip ρ Q = (((ρ : ℂ) + Q) / 2) • 1 + (Complex.I * ((ρ : ℂ) - Q) / 2) • HC := by
  unfold divideFlip; rw [Pplus_form, Pminus_form]; module

/-- **K8.6 (`hodgeDivide_mul_flip`, re-proved in the local basis).** `D ∘ flip(D) = ρQ · 1`. -/
theorem divide_mul_flip (ρ Q : ℝ) : divide ρ Q * divideFlip ρ Q = ((ρ * Q : ℝ) : ℂ) • 1 := by
  rw [divide_form, divideFlip_form, form_mul,
    show ((ρ * Q : ℝ) : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) = ((ρ * Q : ℝ) : ℂ) • 1 + (0 : ℂ) • HC
      by simp]
  refine coeff_eq ?_ ?_ <;> push_cast <;> cscalar

theorem coords4_Kmat : coords4 Kmat = ![0, 0, 0, 0, 0, -1] := by
  ext i; fin_cases i <;> simp [coords4, Kmat]

theorem iConjVec_eq : iConjVec = fun i => ((coords4 Kmat i : ℝ) : ℂ) := by
  ext i; fin_cases i <;> simp [iConjVec, coords4, Kmat]

theorem L01Vec_eq : L01Vec = fun i => ((coords4 L01r i : ℝ) : ℂ) := by
  ext i; fin_cases i <;> simp [L01Vec, coords4, L01r]

/-- **K8.6 (the places are transverse to the divide).**
`D(iConj) = ½(ρ+Q)·iConj − ½ i(ρ−Q)·L01`: `iConj` is not an eigenvector of the divide unless
`ρ = Q`; the divide mixes the complex-place boost with the real-pair rotation. -/
theorem divide_iConj (ρ Q : ℝ) :
    (divide ρ Q).mulVec iConjVec =
      (((ρ : ℂ) + Q) / 2) • iConjVec - (Complex.I * ((ρ : ℂ) - Q) / 2) • L01Vec := by
  rw [divide_form]
  ext i
  fin_cases i <;>
    simp [HC, iConjVec, L01Vec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

/-- `D(L01) = ½(ρ+Q)·L01 + ½ i(ρ−Q)·iConj`. -/
theorem divide_L01 (ρ Q : ℝ) :
    (divide ρ Q).mulVec L01Vec =
      (((ρ : ℂ) + Q) / 2) • L01Vec + (Complex.I * ((ρ : ℂ) - Q) / 2) • iConjVec := by
  rw [divide_form]
  ext i
  fin_cases i <;>
    simp [HC, iConjVec, L01Vec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

/-! ### K8.7: the Holst coefficient is imaginary -/

/-- **K8.7 (convention A).** `1 + (1/γ) H ∝ D` iff `1/γ = −i (ρ−Q)/(ρ+Q)`. -/
theorem holst_iff (ρ Q : ℝ) (hsum : ρ + Q ≠ 0) (γ : ℂ) :
    (∃ lam : ℂ, 1 + γ⁻¹ • HC = lam • divide ρ Q) ↔
      γ⁻¹ = -Complex.I * (((ρ : ℂ) - Q) / ((ρ : ℂ) + Q)) := by
  have hsumC : (ρ : ℂ) + Q ≠ 0 := by exact_mod_cast hsum
  constructor
  · rintro ⟨lam, h⟩
    rw [divide_form] at h
    have h00 := congrFun (congrFun h 0) 0
    have h50 := congrFun (congrFun h 5) 0
    simp [HC] at h00 h50
    have hl : lam * ((ρ : ℂ) + Q) = 2 := by
      first
      | linear_combination 2 * h00
      | linear_combination (-2 : ℂ) * h00
    rw [h50]
    apply mul_right_cancel₀ hsumC
    have e : -Complex.I * (((ρ : ℂ) - Q) / ((ρ : ℂ) + Q)) * ((ρ : ℂ) + Q) =
        -Complex.I * ((ρ : ℂ) - Q) := by rw [mul_assoc, div_mul_cancel₀ _ hsumC]
    rw [e]
    linear_combination (-(Complex.I * ((ρ : ℂ) - Q) / 2)) * hl
  · intro hγ
    refine ⟨2 / ((ρ : ℂ) + Q), ?_⟩
    rw [divide_form, hγ, smul_add, smul_smul, smul_smul]
    have e1 : 2 / ((ρ : ℂ) + Q) * (((ρ : ℂ) + Q) / 2) = 1 := by
      field_simp
    have e2 : 2 / ((ρ : ℂ) + Q) * (-(Complex.I * ((ρ : ℂ) - Q) / 2)) =
        -Complex.I * (((ρ : ℂ) - Q) / ((ρ : ℂ) + Q)) := by
      field_simp
    rw [e1, e2, one_smul]

/-- **K8.7 (convention B).** `H + (1/γ)·1 ∝ D` iff `1/γ = i (ρ+Q)/(ρ−Q)`. -/
theorem holst_iff' (ρ Q : ℝ) (hρQ : ρ ≠ Q) (γ : ℂ) :
    (∃ lam : ℂ, HC + γ⁻¹ • 1 = lam • divide ρ Q) ↔
      γ⁻¹ = Complex.I * (((ρ : ℂ) + Q) / ((ρ : ℂ) - Q)) := by
  have hdiff : (ρ : ℂ) - Q ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hρQ
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  constructor
  · rintro ⟨lam, h⟩
    rw [divide_form] at h
    have h00 := congrFun (congrFun h 0) 0
    have h50 := congrFun (congrFun h 5) 0
    simp [HC] at h00 h50
    have hl : lam * (Complex.I * ((ρ : ℂ) - Q)) = -2 := by
      first
      | linear_combination 2 * h50
    have hl' : lam * ((ρ : ℂ) - Q) = 2 * Complex.I := by
      linear_combination (-Complex.I) * hl + (lam * ((ρ : ℂ) - Q)) * hI
    rw [h00]
    apply mul_right_cancel₀ hdiff
    have e : Complex.I * (((ρ : ℂ) + Q) / ((ρ : ℂ) - Q)) * ((ρ : ℂ) - Q) =
        Complex.I * ((ρ : ℂ) + Q) := by rw [mul_assoc, div_mul_cancel₀ _ hdiff]
    rw [e]
    linear_combination (((ρ : ℂ) + Q) / 2) * hl'
  · intro hγ
    refine ⟨2 * Complex.I / ((ρ : ℂ) - Q), ?_⟩
    rw [divide_form, hγ, smul_add, smul_smul, smul_smul]
    have e1 : 2 * Complex.I / ((ρ : ℂ) - Q) * (((ρ : ℂ) + Q) / 2) =
        Complex.I * (((ρ : ℂ) + Q) / ((ρ : ℂ) - Q)) := by
      field_simp
    have e2 : 2 * Complex.I / ((ρ : ℂ) - Q) * (-(Complex.I * ((ρ : ℂ) - Q) / 2)) = 1 := by
      field_simp
      cscalar
    rw [e1, e2, one_smul, add_comm]

/-- **K8.7.** If `1 + (1/γ) H ∝ D` with `ρ ≠ Q`, then `γ = i (ρ+Q)/(ρ−Q)`. -/
theorem holst_gamma_eq (ρ Q : ℝ) (hρQ : ρ ≠ Q) (hsum : ρ + Q ≠ 0) (γ : ℂ)
    (h : ∃ lam : ℂ, 1 + γ⁻¹ • HC = lam • divide ρ Q) :
    γ = Complex.I * (((ρ : ℂ) + Q) / ((ρ : ℂ) - Q)) := by
  have hinv := (holst_iff ρ Q hsum γ).mp h
  have hsumC : (ρ : ℂ) + Q ≠ 0 := by exact_mod_cast hsum
  have hdiff : (ρ : ℂ) - Q ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hρQ
  rw [← inv_inv γ, hinv]
  apply inv_eq_of_mul_eq_one_left
  field_simp
  cscalar

/-- **K8.7 (γ is not real).** For real `ρ ≠ Q` with `ρ + Q ≠ 0`, the Holst coefficient of the
divide is purely imaginary: `Re γ = 0` and `Im γ ≠ 0`. A real Barbero–Immirzi parameter cannot be
read off `D`. -/
theorem holst_gamma_not_real (ρ Q : ℝ) (hρQ : ρ ≠ Q) (hsum : ρ + Q ≠ 0) (γ : ℂ)
    (h : ∃ lam : ℂ, 1 + γ⁻¹ • HC = lam • divide ρ Q) : γ.re = 0 ∧ γ.im ≠ 0 := by
  rw [holst_gamma_eq ρ Q hρQ hsum γ h]
  have hdiff : ρ - Q ≠ 0 := sub_ne_zero.mpr hρQ
  have hcast : (((ρ : ℂ) + Q) / ((ρ : ℂ) - Q)) = (((ρ + Q) / (ρ - Q) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast]
  constructor
  · rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  · rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, zero_add]
    exact div_ne_zero hsum hdiff

end HermitianExclusion
