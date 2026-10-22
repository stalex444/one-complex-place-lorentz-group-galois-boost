module
public import Mathlib

@[expose] public section
/-!
# Shared definitions

The definitions on which the sixteen compared statements rest, with the two supporting theorems
their bodies use (`placeMatrix_isHermitian`, `diag_re_of_isHermitian`, for the place isomorphism;
`boostC_add`, `boostC_smul`, for the boost). The block between the `BEGIN`/`END SHARED
DEFINITIONS` markers is copied byte for byte into `Challenge.lean`, so the Challenge imports
Mathlib only and elaborates the same declarations, under the same names, as the proof modules,
which are all built on this file.
-/

-- BEGIN SHARED DEFINITIONS
-- The definitions of this entry that the compared statements use, with the theorems their bodies
-- depend on. This block is, byte for byte, the body of `ArithmeticLorentz/Defs.lean`, on which the
-- proof modules are built; both files import Mathlib only.
namespace HermitianExclusion

open Matrix ComplexConjugate Complex Finset

/-! #### `Herm_n(ℂ)` as a real vector space, and its two trace forms -/

/-- The Hermitian `n × n` complex matrices, as a real subspace. -/
def herm (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | X.IsHermitian}
  add_mem' hX hY := Matrix.IsHermitian.add hX hY
  zero_mem' := isHermitian_zero
  smul_mem' c _ hX := Matrix.IsHermitian.smul hX (IsSelfAdjoint.all c)

/-- The real bilinear form `(X, Y) ↦ Re tr(X Yᵀ)` on `Herm_n(ℂ)`. -/
noncomputable def transposeBilin (n : ℕ) : LinearMap.BilinForm ℝ (herm n) :=
  LinearMap.mk₂ ℝ (fun X Y => (trace (X.1 * (Y.1)ᵀ)).re)
    (fun X₁ X₂ Y => by simp [Matrix.add_mul, trace_add])
    (fun c X Y => by simp [trace_smul])
    (fun X Y₁ Y₂ => by simp [Matrix.mul_add, trace_add])
    (fun c X Y => by simp [trace_smul])

/-- The real bilinear form `(X, Y) ↦ Re tr(X Y)` on `Herm_n(ℂ)` (Hilbert–Schmidt). -/
noncomputable def hsBilin (n : ℕ) : LinearMap.BilinForm ℝ (herm n) :=
  LinearMap.mk₂ ℝ (fun X Y => (trace (X.1 * Y.1)).re)
    (fun X₁ X₂ Y => by simp [Matrix.add_mul, trace_add])
    (fun c X Y => by simp [trace_smul])
    (fun X Y₁ Y₂ => by simp [Matrix.mul_add, trace_add])
    (fun c X Y => by simp [trace_smul])

/-- The transpose-twisted trace form `X ↦ Re tr(X Xᵀ)` on `Herm_n(ℂ)`. -/
noncomputable def transposeForm (n : ℕ) : QuadraticForm ℝ (herm n) :=
  (transposeBilin n).toQuadraticMap

/-- The Hilbert–Schmidt form `X ↦ Re tr(X X)` on `Herm_n(ℂ)`. -/
noncomputable def hsForm (n : ℕ) : QuadraticForm ℝ (herm n) := (hsBilin n).toQuadraticMap

/-! #### The place matrix and the place isomorphism `ℝ² × ℂ ≃ Herm₂(ℂ)` -/

/-- The place matrix `X = [[x_Q, conj x_σ], [x_σ, x_{q′}]]`. -/
def placeMatrix (xQ xq : ℝ) (xσ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(xQ : ℂ), conj xσ; xσ, (xq : ℂ)]

theorem placeMatrix_isHermitian (xQ xq : ℝ) (xσ : ℂ) : (placeMatrix xQ xq xσ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [placeMatrix, conjTranspose_apply]

/-- The place matrix of a point of the Minkowski space `(Fin 2 → ℝ) × (Fin 1 → ℂ)`. -/
def placeMatrix' (p : (Fin 2 → ℝ) × (Fin 1 → ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  placeMatrix (p.1 0) (p.1 1) (p.2 0)

theorem diag_re_of_isHermitian {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian)
    (i : Fin n) : ((X i i).re : ℂ) = X i i := by
  have h := hX.apply i i
  rw [Complex.star_def] at h
  exact Complex.conj_eq_iff_re.mp h

/-- **The place isomorphism** `ℝ × ℝ × ℂ ≃ Herm₂(ℂ)`, real-linear. -/
def placeEquiv : ((Fin 2 → ℝ) × (Fin 1 → ℂ)) ≃ₗ[ℝ] herm 2 where
  toFun p := ⟨placeMatrix' p, placeMatrix_isHermitian _ _ _⟩
  invFun X := (![(X.1 0 0).re, (X.1 1 1).re], ![X.1 1 0])
  map_add' p q := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [placeMatrix', placeMatrix]
  map_smul' c p := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [placeMatrix', placeMatrix, Complex.real_smul]
  left_inv p := by
    rcases p with ⟨x, z⟩
    refine Prod.ext ?_ ?_
    · funext i; fin_cases i <;> simp [placeMatrix', placeMatrix]
    · funext j; fin_cases j; simp [placeMatrix', placeMatrix]
  right_inv X := by
    obtain ⟨X, hX⟩ := X
    apply Subtype.ext
    have h01 : conj (X 1 0) = X 0 1 := by
      have := hX.apply 0 1; rwa [Complex.star_def] at this
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [placeMatrix', placeMatrix, diag_re_of_isHermitian hX, h01]

/-! #### The place space with `r₁` real places and one complex place, its two forms, Galois
conjugation, `iConj = i ∘ conj`, the boost generator and the boost, the place-preserving and
isometry predicates, and the polar phase -/

/-- The place space with `r₁` real places and one complex place. -/
abbrev PlaceSpace (r₁ : ℕ) := (Fin r₁ → ℝ) × (Fin 1 → ℂ)

/-- The trace form `T(X, Y) = Σ x_i y_i + Σ 2 Re(z_j w_j)`. -/
def traceB (r₁ : ℕ) (X Y : PlaceSpace r₁) : ℝ :=
  ∑ i, X.1 i * Y.1 i + ∑ j, 2 * (X.2 j * Y.2 j).re

/-- The Born form `B(X, Y) = Σ x_i y_i + Σ 2 Re(z_j conj w_j)`. -/
def bornB (r₁ : ℕ) (X Y : PlaceSpace r₁) : ℝ :=
  ∑ i, X.1 i * Y.1 i + ∑ j, 2 * (X.2 j * conj (Y.2 j)).re

/-- Galois conjugation at the complex place: `(x, z) ↦ (x, conj z)`. -/
def galoisConj (r₁ : ℕ) : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁ where
  toFun p := (p.1, fun j => conj (p.2 j))
  map_add' p q := Prod.ext rfl (funext fun j => map_add (starRingEnd ℂ) (p.2 j) (q.2 j))
  map_smul' c p := Prod.ext rfl (funext fun j => by simp [Complex.real_smul])

/-- `iConj : (x, z) ↦ (x, i · conj z)`. -/
def iConj (r₁ : ℕ) : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁ where
  toFun p := (p.1, fun j => I * conj (p.2 j))
  map_add' p q := Prod.ext rfl (funext fun j => by simp [mul_add])
  map_smul' c p := Prod.ext rfl (funext fun j => by
    simp only [Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Complex.real_smul, map_mul,
      Complex.conj_ofReal]
    ring)

/-- The boost generator: `iConj` on the complex place, zero on the real places. -/
def boostGen (r₁ : ℕ) : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁ where
  toFun p := (0, fun j => I * conj (p.2 j))
  map_add' p q := Prod.ext (zero_add (0 : Fin r₁ → ℝ)).symm (funext fun j => by simp [mul_add])
  map_smul' c p := Prod.ext (smul_zero c).symm (funext fun j => by
    simp only [Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Complex.real_smul, map_mul,
      Complex.conj_ofReal]
    ring)

/-- The boost on the complex coordinate: `z ↦ cosh β · z + i sinh β · conj z`. -/
noncomputable def boostC (β : ℝ) (z : ℂ) : ℂ :=
  (Real.cosh β : ℂ) * z + I * (Real.sinh β : ℂ) * conj z

theorem boostC_add (β : ℝ) (z w : ℂ) : boostC β (z + w) = boostC β z + boostC β w := by
  simp only [boostC, map_add]; ring

theorem boostC_smul (β c : ℝ) (z : ℂ) : boostC β (c • z) = c • boostC β z := by
  simp only [boostC, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring

/-- `boost β = exp (β · boostGen)`: identity on the real places, `boostC β` on the complex
place. -/
noncomputable def boost (r₁ : ℕ) (β : ℝ) : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁ where
  toFun p := (p.1, fun j => boostC β (p.2 j))
  map_add' p q := Prod.ext rfl (funext fun j => boostC_add β (p.2 j) (q.2 j))
  map_smul' c p := Prod.ext rfl (funext fun j => boostC_smul β c (p.2 j))

/-- `L` is **place-preserving**: it maps each real-place line into itself and the complex place
into itself (block-diagonal with respect to `ℝ ⊕ ⋯ ⊕ ℝ ⊕ ℂ`). -/
def PlacePreserving {r₁ : ℕ} (L : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁) : Prop :=
  (∀ (i : Fin r₁) (a : ℝ), ∃ a' : ℝ,
    L ((Pi.single i a : Fin r₁ → ℝ), (0 : Fin 1 → ℂ)) = ((Pi.single i a' : Fin r₁ → ℝ), 0)) ∧
  ∀ z : Fin 1 → ℂ, (L (0, z)).1 = 0

/-- `L` is an **infinitesimal isometry** of the trace form: `T(LX, Y) + T(X, LY) = 0`. -/
def IsInfIsometry {r₁ : ℕ} (L : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁) : Prop :=
  ∀ X Y, traceB r₁ (L X) Y + traceB r₁ X (L Y) = 0

/-- `g` is an **isometry** of the trace form. -/
def IsIsometry {r₁ : ℕ} (g : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁) : Prop :=
  ∀ X Y, traceB r₁ (g X) (g Y) = traceB r₁ X Y

/-- The polar phase in place coordinates: `(x, z) ↦ (x, e^{iθ} z)`. -/
noncomputable def phaseV (θ : ℝ) : PlaceSpace 2 →ₗ[ℝ] PlaceSpace 2 where
  toFun p := (p.1, fun j => exp (θ * I) * p.2 j)
  map_add' p q := Prod.ext rfl (funext fun j => by simp [mul_add])
  map_smul' c p := Prod.ext rfl (funext fun j => by
    simp only [Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Complex.real_smul]; ring)

/-! #### The register data: `η4 = diag(1, 1, 1, −1)`, the six local generators `L_ab` on the
`0123` plane, `so(3,1)` as their span, Galois conjugation `c` and the register's time reflection
`P` (the same matrix), the generator `K` of `iConj` and the phase generator `J` on `(Re z, Im z)`,
the block matrices `diag(R, s)`, the local Hodge star on the ordered basis
`(L01, L02, L03, L12, L13, L23)`, and the chirality projectors and the divide `ρ P₊ + Q P₋` -/

/-- `η4 = diag(1, 1, 1, −1)`, the restriction of `η6` to the `0123` plane. -/
def η4 : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- The six local generators restricted to the `0123` plane (the restrictions to `0123` of the register's
`L_ab = η_b E_ab − η_a E_ba`, PALOMAR-2026-09-30-000024, `Challenge.lean`, lines 35–44). -/
def L01r : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def L02r : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 1, 0; 0, 0, 0, 0; -1, 0, 0, 0; 0, 0, 0, 0]
def L03r : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, -1; 0, 0, 0, 0; 0, 0, 0, 0; -1, 0, 0, 0]
def L12r : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 0]
def L13r : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 0, 0; 0, -1, 0, 0]
def L23r : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0]

/-- The ordered local basis `(L01, L02, L03, L12, L13, L23)` on `0123`. -/
def localGen : Fin 6 → Matrix (Fin 4) (Fin 4) ℝ := ![L01r, L02r, L03r, L12r, L13r, L23r]

/-- `so(3,1)` as the span of the six local generators. -/
def so31 : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) := Submodule.span ℝ (Set.range localGen)

/-- Galois conjugation `c : (a, b, u, v) ↦ (a, b, u, −v)`. -/
def cArith : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- The register's time reflection `P = diag(1, 1, 1, −1)` on `0123`. -/
def Preg : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- The generator of `iConj = i ∘ c`: `K = [[0,1],[1,0]]` on `(u, v)`, zero on `(a, b)`. -/
def Kmat : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

/-- The phase generator (multiplication by `i`): `J = [[0,−1],[1,0]]` on `(u, v)`. -/
def Jmat : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

/-- `diag(R, s)`: a `3 × 3` block on `(e₀, e₁, e₂)` and the scalar `s` on the time axis `e₃`. -/
def blockDiag (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![R 0 0, R 0 1, R 0 2, 0; R 1 0, R 1 1, R 1 2, 0; R 2 0, R 2 1, R 2 2, 0; 0, 0, 0, s]

/-- The register's bivector coordinates `coord_(a,b)(X) = η_b X_ab` on the local basis
`(L01, L02, L03, L12, L13, L23)`. -/
def coords4 (X : Matrix (Fin 4) (Fin 4) ℝ) : Fin 6 → ℝ :=
  ![X 0 1, X 0 2, -(X 0 3), X 1 2, -(X 1 3), -(X 2 3)]

/-- The local Hodge star in the ordered basis `(L01, L02, L03, L12, L13, L23)`
(the register's local Hodge
`H[out, in] = η_a η_b ε₄(a, b, c, d)`, read on the local basis): `H(L01) = L23`, `H(L02) = −L13`, `H(L03) = −L12`,
`H(L12) = L03`, `H(L13) = L02`, `H(L23) = −L01`. -/
def Hmat : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0;
     0, 0, -1, 0, 0, 0; 0, -1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0]

/-- Reconstruction of a local element from its coordinates. -/
def fromCoords (c : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  c 0 • L01r + c 1 • L02r + c 2 • L03r + c 3 • L12r + c 4 • L13r + c 5 • L23r

/-- The Hodge operator on `0123` matrices: coordinates, `H`, reconstruct. -/
def hodgeOp (X : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fromCoords (Hmat.mulVec (coords4 X))

/-- The Hodge table over `ℂ` (same entries as `Hmat`). -/
def HC : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0;
     0, 0, -1, 0, 0, 0; 0, -1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0]

/-- The chirality `C = −i H` (HodgeBulkScreen.lean L32). -/
noncomputable def chirality : Matrix (Fin 6) (Fin 6) ℂ := (-Complex.I) • HC

/-- `P₊ = ½(1 + C)` (hodgePlus, L35): the `H = +i` (self-dual) projector. -/
noncomputable def Pplus : Matrix (Fin 6) (Fin 6) ℂ := (1 / 2 : ℂ) • (1 + chirality)

/-- `P₋ = ½(1 − C)` (hodgeMinus, L38): the `H = −i` (anti-self-dual) projector. -/
noncomputable def Pminus : Matrix (Fin 6) (Fin 6) ℂ := (1 / 2 : ℂ) • (1 - chirality)

/-- The divide `D = ρ P₊ + Q P₋` (hodgeDivide, L43). -/
noncomputable def divide (ρ Q : ℝ) : Matrix (Fin 6) (Fin 6) ℂ := (ρ : ℂ) • Pplus + (Q : ℂ) • Pminus

/-- The flipped divide `Q P₊ + ρ P₋` (hodgeDivideFlip, L47). -/
noncomputable def divideFlip (ρ Q : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  (Q : ℂ) • Pplus + (ρ : ℂ) • Pminus

/-- `iConj = −L23` in local coordinates. -/
def iConjVec : Fin 6 → ℂ := ![0, 0, 0, 0, 0, -1]

/-- `L01` in local coordinates. -/
def L01Vec : Fin 6 → ℂ := ![1, 0, 0, 0, 0, 0]

end HermitianExclusion
-- END SHARED DEFINITIONS
