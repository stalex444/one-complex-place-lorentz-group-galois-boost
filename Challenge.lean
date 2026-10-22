module
public import Mathlib

@[expose] public section
/-!
# The arithmetic Lorentz group of a number field with one complex place, and its bridge to the local Hodge register

**The setting.** A number field `K` with `r₁` real places and one complex place embeds, by
Mathlib's mixed embedding, into the place space `V = ℝ^{r₁} × ℂ` (`PlaceSpace r₁`). `V` carries
two real symmetric bilinear forms: the **trace form** `T(X, Y) = Σ_i x_i y_i + 2 Re(z w)`
(`traceB`), which is `Tr_{K/ℚ}(xy)` at the mixed embedding (`ArithmeticLorentz/PlaceLink.lean`,
`trace_mul_eq`), of type `(r₁ + 1, 1)`; and the **Born form**
`B(X, Y) = Σ_i x_i y_i + 2 Re(z · conj w)` (`bornB`), which is `Σ_φ φ(x) · conj φ(y)` over the
complex embeddings, positive definite. For `r₁ = 2` the place isomorphism
`(x₁, x₂, z) ↦ X = [[x₁, conj z], [z, x₂]]` (`placeEquiv`) carries `V` onto the Hermitian matrices
`Herm₂(ℂ)` (`herm 2`), with `T = Re tr(X Yᵀ)` (`transposeForm`), `B = Re tr(X Y)` (`hsForm`),
and the one negative direction of `T` along `σ_y = [[0, −i], [i, 0]]`. A real-linear map of `V`
is **place-preserving** (`PlacePreserving`) if it maps each real-place line into itself and the
complex place into itself; `IsIsometry` and `IsInfIsometry` are isometry and infinitesimal isometry
of `T`. **Galois conjugation** is `c : (x, z) ↦ (x, conj z)` (`galoisConj`); `iConj = i ∘ c`, with
generator `boostGen : (x, z) ↦ (0, i · conj z)`; the **arithmetic boost** is
`boost β : (x, z) ↦ (x, cosh β · z + i sinh β · conj z)` (`boostC` on the complex coordinate),
the flow of `boostGen` (`hasDerivAt_boost` in `ArithmeticLorentz/Boost.lean`); the **polar phase**
is `phaseV θ : (x, z) ↦ (x, e^{iθ} z)`.

**The register.** The second half of the entry is stated on the data of the author's registered
entry PALOMAR-2026-09-30-000024 (`stalex444/pdt-hodge-lie-generation`, commit `e2d8dde`): the
metric `η = diag(1, 1, 1, −1, 1, −1)` on `ℝ⁶`, the generators `L_ab = η_b E_ab − η_a E_ba`, the
bivector coordinates `η_b X_ab`, the local Hodge star on the coordinate four-plane `0123`
(`Challenge.lean`, lines 35–75 of that entry), and, from its `GravityScreening/HodgeBulkScreen.lean`,
the Hodge rotation `[[0, −1], [1, 0]]` on one complexified pair, the chirality `−i ⋆`, the
projectors `P± = ½(1 ± chirality)`, the divide `D = ρ P₊ + Q P₋` and its flip `Q P₊ + ρ P₋`.
Here these are transcribed on the `0123` plane as explicit real `4 × 4` matrices — `η4`, the six
restricted generators `L01r, …, L23r`, their span `so31`, the time reflection `Preg = diag(1,1,1,−1)`
(the same matrix as Galois conjugation `cArith` in the place coordinates `(a, b, Re z, Im z)`), the
generator `Kmat` of `iConj` and the phase generator `Jmat` on `(Re z, Im z)`, the block matrices
`blockDiag R s = diag(R, s)` — and the Hodge star as the `6 × 6` table `Hmat` on the ordered local
basis `(L01, L02, L03, L12, L13, L23)` (`hodgeOp = fromCoords ∘ Hmat ∘ coords4`), with its complex
copy `HC`, `chirality = −i HC`, `Pplus`, `Pminus`, `divide ρ Q`, `divideFlip ρ Q`; `iConjVec` and
`L01Vec` are the local coordinates of `Kmat` (`= −L23r`) and `L01r`. Nothing is imported from the
register: every identity is re-proved on the transcribed matrices (the proof module checks that
the six are `η4`-skew and independent, that `so31` is exactly the `η4`-skew matrices, the fifteen
structure constants, and `H² = −1` on `so31`).

Sixteen compared statements, in namespace `ArithmeticLorentz` (each is one declaration; statements
3–7 hold for every `r₁`):

1. `sigNeg_transposeForm_eq_one_iff` — the form `X ↦ Re tr(X Xᵀ)` on `Herm_n(ℂ)` has exactly one
   negative direction iff `n = 2` (the proof module proves its type `(n(n+1)/2, n(n−1)/2)` for
   every `n`, `transposeForm_signature`, through the place shape `ℝⁿ × ℂ^{n(n−1)/2}` of `Herm_n`).
2. `hermitian_exclusion` — if `sigNeg = 1` then `n = 2`, `sigPos = 3` and `dim_ℝ Herm_n(ℂ) = 4`.
3. `infIsometry_classification` — a place-preserving infinitesimal isometry of `T` is a real
   multiple of `boostGen`: the real places admit none, and on the complex place the only one is
   `i ∘ conj` (so the place-preserving isometry algebra is the line `ℝ · boostGen`, dimension 1).
4. `placePreserving_isometry_classification` — a place-preserving isometry of `T` is a sign `±1`
   on each real place and, on the complex place, `ε' · boost β` or `ε' · boost β ∘ conj` with
   `ε' = ±1`: the group `{±1}^{r₁} × O(1, 1)`.
5. `traceB_boost` — every boost is an isometry of `T`.
6. `hsForm_boost_ne` — for `β ≠ 0` the boost is not an isometry of the Born form (on `Herm₂(ℂ)`;
   on the pure coherence `(0, 0, 1)` the Born mass goes from `2` to `2 + 4 sinh² β`).
7. `galoisConj_boost_galoisConj` — `c ∘ boost β ∘ c = boost (−β)`: Galois conjugation reverses
   the boost.
8. `traceB_phaseV_iff` — the polar phase is an isometry of `T` iff `sin θ = 0`.
9. `time_canonical` — if `Λ ∈ O(3, 1)` (`Λᵀ η4 Λ = η4`) carries `cArith` to `Preg`
   (`Λ cArith Λ⁻¹ = Preg`), then `Λ = diag(R, s)` with `Rᵀ R = 1` and `s = ±1`.
10. `conj_P_iff_orthogonal` — for `Λ ∈ O(3, 1)`, `Λ Preg Λ⁻¹ = Preg ⟺ Λ Λᵀ = 1`: the solutions
    are `O(3, 1) ∩ O(4)`.
11. `boost_span` — `diag(R, s) · Kmat · diag(Rᵀ, s) = −s (n₀ L03r + n₁ L13r + n₂ L23r)` with
    `n = R e₂`, an identity with no hypothesis on `R`, `s`.
12. `phase_not_mem_so31` — for `Rᵀ R = 1`, `s = ±1`: `diag(R, s) · Jmat · diag(Rᵀ, s) ∉ so31`.
13. `hodge_exchange` — `H(diag(R, s) · Kmat · diag(Rᵀ, s)) = s (n₀ L12r − n₁ L02r + n₂ L01r)`; at
    `R = 1`, `s = 1` this is `H(Kmat) = L01r`: the Hodge dual of the arithmetic boost generator is
    the rotation of the two real places.
14. `divide_iConj` — `D(iConj) = ½(ρ + Q) · iConj − ½ i (ρ − Q) · L01` in local coordinates.
15. `divide_mul_flip` — `D · flip D = ρQ · 1` for all real `ρ`, `Q`.
16. `holst_gamma_not_real` — if `1 + γ⁻¹ H` is proportional to `D` with `ρ ≠ Q` and `ρ + Q ≠ 0`,
    then `Re γ = 0` and `Im γ ≠ 0` (the module proves `γ = i (ρ + Q)/(ρ − Q)`, `holst_gamma_eq`).

**What is classical, and is not this structure.** The identification `Herm₂(ℂ) ≅ ℝ^{3,1}`
through the determinant, with the spinor action `X ↦ A X A†` of `SL(2, ℂ)`, is classical
(Jordan–von Neumann–Wigner 1934; Penrose–Rindler, *Spinors and space-time* 1, 1984, §1.2) and is
not what is formalized here: the Lorentz form of this entry is `tr(X Xᵀ)`, whose timelike
direction is `σ_y`, not `det X`; and its boost is `i` composed with Galois conjugation, which is
not a conjugation `X ↦ A X A†` (it is not an `ℂ`-linear map at all, and it is not a Born
isometry, statement 6, whereas unitary conjugations are). That the Hodge dual of a boost generator
of `so(3, 1)` is a rotation generator is textbook (the self-dual/anti-self-dual splitting of
`so(3, 1) ⊗ ℂ`); the content of 13 is which boost and which rotation in a number field's place
coordinates. The count in 1–2 is Sylvester's law of inertia applied to the place shape
`(n, n(n−1)/2)` of `Herm_n(ℂ)`; the type `(r₁ + r₂, r₂)` of the trace form of a number field is
Hermite–Sylvester (in number-field form, O. Taussky 1968) and is formalized in the author's
registered entry PALOMAR-2026-10-21-000012, whose field `ℚ(Q)`, `Q⁴ = Q + 1`, with places `(2, 1)`
and trace-form type `(3, 1)`, is the instance of the shape `r₁ = 2`; the instance is not restated
here. The nearest statement found in the literature to "a number field as a qubit" is Banaszak,
Barańczuk, Lulek, Milewski and Stagraczyński, Acta Phys. Pol. A 121 (2012) 1111 (two Galois-conjugate
real eigenvalues of a rank-2 extension as two levels), which has no complex place, no Hermitian
matrix space and no Lorentz form. No priority is claimed for any ingredient; the contribution is
the kernel-checked classification 3–4 in place coordinates — field multiplication and Galois
conjugation realize a `(1+1)`-dimensional Lorentz group on the complex place and nothing mixing a
real place with time — and the bridge 9–16 to the register's `so(3, 1)`.

**Form of the statements; what is not formalized.** The statements use the definitions of this
entry, stated in this file between `-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`,
byte for byte the block of `ArithmeticLorentz/Defs.lean` on which the proof modules are built;
both files import Mathlib only. `sigPos`, `sigNeg` are Mathlib's inertia indices;
`Module.finrank`, `Submodule.span`, `Matrix` and its `⁻¹`, `ᵀ`, `mulVec` are Mathlib's. The
rapidity in 4 is produced by `Real.arsinh`; "the group `{±1}^{r₁} × O(1, 1)`" is the classification
direction, and the converse (every such map is a place-preserving isometry) is proved in the
module for the boosts and for `c` but is not packaged as a compared statement. In 9 the hypothesis
`Λ cArith Λ⁻¹ = Preg` is a hypothesis; that the register's time reflection is Galois conjugation
is not a theorem of this entry. `O(1, 1)`, `so(3, 1)` are the explicit matrix sets above, not
Mathlib's orthogonal groups. Not formalized: that `(x, z) ↦ (0, iz)` is the derivative of
`phaseV θ` at `θ = 0`; anything about the register's `sl(15)` generation or its other nine
conformal directions; and everything in the application paragraph.

**Application (cited; not a claim of the entry).** In the author's Pisot Dimensional Theory
`ℚ(Q)`, `Q⁴ = Q + 1`, is the arithmetic of four-dimensional spacetime; its place space is
`Herm₂(ℂ)` and its trace form `Tr_{K/ℚ}(x²)` is the Minkowski form of signature `(3, 1)`
(PALOMAR-2026-10-21-000012). Read through the theory, 3–8 say that the only Lorentz symmetry the
arithmetic itself carries is the boost `i ∘ c` of the complex place — generated by Galois
conjugation, with Galois conjugation as time reversal — and that the phase, the symmetry of the
Born form, is not a Lorentz symmetry; 9–10 say that a Lorentz map carrying Galois conjugation to
the register's time reflection fixes the time axis up to sign and is otherwise a rotation of the
three remaining place directions; 11–13 place the arithmetic boost in the register's boost span and
send it, by the Hodge star, to the rotation of the two real places; and 14–16 say that the Hodge
divide `ρ P₊ + Q P₋` of the register mixes that boost with that rotation unless `ρ = Q`, that it
is a unit of weight `ρQ` against its flip, and that its Holst coefficient is purely imaginary, so
no real Barbero–Immirzi parameter can be read off it.
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

open Matrix ComplexConjugate Complex Finset QuadraticForm QuadraticMap

open HermitianExclusion

namespace ArithmeticLorentz

/-- **(1) Lorentzian iff `n = 2`.** Among the Hermitian matrix spaces `Herm_n(ℂ)`, the form
`X ↦ Re tr(X Xᵀ)` has exactly one negative direction iff `n = 2`. -/
theorem sigNeg_transposeForm_eq_one_iff (n : ℕ) : sigNeg (transposeForm n) = 1 ↔ n = 2 := by
  sorry

/-- **(2) The Hermitian exclusion, full form.** One negative direction forces `n = 2`, type
`(3, 1)`, real dimension `4`. -/
theorem hermitian_exclusion (n : ℕ) (h : sigNeg (transposeForm n) = 1) :
    n = 2 ∧ sigPos (transposeForm n) = 3 ∧ Module.finrank ℝ (herm n) = 4 := by
  sorry

/-- **(3) The infinitesimal classification**, every `r₁`: a place-preserving infinitesimal
isometry of the trace form is a real multiple of `boostGen`. -/
theorem infIsometry_classification {r₁ : ℕ} (L : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁)
    (hP : PlacePreserving L) (hL : IsInfIsometry L) : ∃ c : ℝ, L = c • boostGen r₁ := by
  sorry

/-- **(4) The group classification**, every `r₁`: a place-preserving isometry of the trace form is
a sign on each real place and `± boost β` or `± boost β ∘ conj` on the complex place:
`{±1}^{r₁} × O(1, 1)`. -/
theorem placePreserving_isometry_classification {r₁ : ℕ} (g : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁)
    (hP : PlacePreserving g) (hg : IsIsometry g) :
    ∃ (ε : Fin r₁ → ℝ) (ε' β : ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (ε' = 1 ∨ ε' = -1) ∧
      ((∀ p, g p = (fun i => ε i * p.1 i, fun j => ε' * boostC β (p.2 j))) ∨
       (∀ p, g p = (fun i => ε i * p.1 i, fun j => ε' * boostC β (conj (p.2 j))))) := by
  sorry

/-- **(5) The boost is an isometry of the trace form.** -/
theorem traceB_boost {r₁ : ℕ} (β : ℝ) (X Y : PlaceSpace r₁) :
    traceB r₁ (boost r₁ β X) (boost r₁ β Y) = traceB r₁ X Y := by
  sorry

/-- **(6) The boost is not a Born isometry** for `β ≠ 0` (on `Herm₂(ℂ)`, through the place
isomorphism). -/
theorem hsForm_boost_ne (β : ℝ) (hβ : β ≠ 0) :
    ∃ X : PlaceSpace 2, hsForm 2 (placeEquiv (boost 2 β X)) ≠ hsForm 2 (placeEquiv X) := by
  sorry

/-- **(7) Galois conjugation reverses the boost**: `c ∘ boost β ∘ c = boost (−β)`. -/
theorem galoisConj_boost_galoisConj {r₁ : ℕ} (β : ℝ) (p : PlaceSpace r₁) :
    galoisConj r₁ (boost r₁ β (galoisConj r₁ p)) = boost r₁ (-β) p := by
  sorry

/-- **(8) The polar phase is a trace-form isometry iff `sin θ = 0`.** -/
theorem traceB_phaseV_iff (θ : ℝ) :
    (∀ X : PlaceSpace 2, traceB 2 (phaseV θ X) (phaseV θ X) = traceB 2 X X) ↔
      Real.sin θ = 0 := by
  sorry

/-- **(9) Time-canonical.** A Lorentz map carrying Galois conjugation to the register's time
reflection is `diag(R, s)` with `R ∈ O(3)`, `s = ±1`. -/
theorem time_canonical (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hη : Λᵀ * η4 * Λ = η4)
    (hc : Λ * cArith * Λ⁻¹ = Preg) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ), Rᵀ * R = 1 ∧ (s = 1 ∨ s = -1) ∧ Λ = blockDiag R s := by
  sorry

/-- **(10) The rest-frame condition.** For `Λ ∈ O(3, 1)`, `Λ P Λ⁻¹ = P ⟺ Λ Λᵀ = 1`. -/
theorem conj_P_iff_orthogonal (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hη : Λᵀ * η4 * Λ = η4) :
    Λ * Preg * Λ⁻¹ = Preg ↔ Λ * Λᵀ = 1 := by
  sorry

/-- **(11) The boost span.** `diag(R, s) · K · diag(Rᵀ, s) = −s (n₀ L03 + n₁ L13 + n₂ L23)`,
`n = R e₂`. -/
theorem boost_span (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    blockDiag R s * Kmat * blockDiag Rᵀ s =
      (-s) • (R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r) := by
  sorry

/-- **(12) The phase is excluded from `so(3, 1)`.** -/
theorem phase_not_mem_so31 (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (hR : Rᵀ * R = 1)
    (hs : s = 1 ∨ s = -1) : blockDiag R s * Jmat * blockDiag Rᵀ s ∉ so31 := by
  sorry

/-- **(13) The Hodge exchange.** `H(diag(R, s) · K · diag(Rᵀ, s)) = s (n₀ L12 − n₁ L02 + n₂ L01)`;
at `R = 1`, `s = 1`: `H(K) = L01`. -/
theorem hodge_exchange (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    hodgeOp (blockDiag R s * Kmat * blockDiag Rᵀ s) =
      s • (R 0 2 • L12r - R 1 2 • L02r + R 2 2 • L01r) := by
  sorry

/-- **(14) The places are transverse to the divide.**
`D(iConj) = ½(ρ + Q) · iConj − ½ i (ρ − Q) · L01`. -/
theorem divide_iConj (ρ Q : ℝ) :
    (divide ρ Q).mulVec iConjVec =
      (((ρ : ℂ) + Q) / 2) • iConjVec - (Complex.I * ((ρ : ℂ) - Q) / 2) • L01Vec := by
  sorry

/-- **(15) The divide against its flip.** `D · flip D = ρQ · 1`. -/
theorem divide_mul_flip (ρ Q : ℝ) : divide ρ Q * divideFlip ρ Q = ((ρ * Q : ℝ) : ℂ) • 1 := by
  sorry

/-- **(16) The Holst coefficient of the divide is purely imaginary.** -/
theorem holst_gamma_not_real (ρ Q : ℝ) (hρQ : ρ ≠ Q) (hsum : ρ + Q ≠ 0) (γ : ℂ)
    (h : ∃ lam : ℂ, 1 + γ⁻¹ • HC = lam • divide ρ Q) : γ.re = 0 ∧ γ.im ≠ 0 := by
  sorry

end ArithmeticLorentz
