# The arithmetic Lorentz group of a number field with one complex place, and its bridge to the local Hodge register

Kernel-checked, in Lean 4 + Mathlib. A number field with `r₁` real places
and one complex place embeds into the place space `V = ℝ^{r₁} × ℂ`, which
carries the trace form `T = Σ x_i y_i + 2 Re(z w)` (the field's
`Tr_{K/ℚ}(xy)` at the mixed embedding, of type `(r₁ + 1, 1)`) and the
positive-definite Born form `B = Σ x_i y_i + 2 Re(z · conj w)`
(`Σ_φ φ(x) conj φ(y)`). For `r₁ = 2`, `V ≅ Herm₂(ℂ)` with `T = Re tr(XYᵀ)`
and `B = Re tr(XY)`. The entry classifies the Lorentz symmetries of `T`
that respect the places: the place-preserving infinitesimal isometries
are exactly the line spanned by `i ∘ (Galois conjugation)`, and the
place-preserving isometries are `{±1}^{r₁} × O(1, 1)`, with the boosts
`z ↦ cosh β · z + i sinh β · conj z` as identity component; no boost
preserves the Born form, Galois conjugation reverses the boost, and the
polar phase `z ↦ e^{iθ} z` preserves `T` only for `sin θ = 0`. It then
bridges this to the `so(3, 1)` of the author's registered Hodge register
(PALOMAR-2026-09-30-000024): a Lorentz map carrying Galois conjugation
to the register's time reflection is `diag(R, s)` with `R ∈ O(3)`,
`s = ±1` (equivalently `Λ P Λ⁻¹ = P ⟺ Λ Λᵀ = 1`); the arithmetic boost
lands in the register's boost span along `n = R e₂`; the phase lands in
no `so(3, 1)`; the Hodge dual of the arithmetic boost generator is the
rotation of the two real places; and the register's Hodge divide
`ρ P₊ + Q P₋` mixes that boost with that rotation, satisfies
`D · flip D = ρQ`, and has a purely imaginary Holst coefficient.
Sixteen compared theorems; every one on the axioms `propext`,
`Classical.choice`, `Quot.sound` alone.

## The compared statements

Namespace `ArithmeticLorentz` (`Challenge.lean`; proved in
`Solution.lean` by `exact` of the proof modules' theorems, which live in
namespace `HermitianExclusion`). Statements 3–7 hold for every `r₁`.

1. `sigNeg_transposeForm_eq_one_iff` — `X ↦ Re tr(X Xᵀ)` on `Herm_n(ℂ)`
   has exactly one negative direction iff `n = 2`.
2. `hermitian_exclusion` — if it has one negative direction then `n = 2`,
   `sigPos = 3` and `dim_ℝ Herm_n(ℂ) = 4`.
3. `infIsometry_classification` — a place-preserving infinitesimal
   isometry of `T` is a real multiple of `boostGen : (x, z) ↦ (0, i · conj z)`.
4. `placePreserving_isometry_classification` — a place-preserving
   isometry of `T` is a sign on each real place and `± boost β` or
   `± boost β ∘ conj` on the complex place.
5. `traceB_boost` — every boost is an isometry of `T`.
6. `hsForm_boost_ne` — for `β ≠ 0` the boost is not a Born isometry.
7. `galoisConj_boost_galoisConj` — `c ∘ boost β ∘ c = boost (−β)`.
8. `traceB_phaseV_iff` — the polar phase is a `T`-isometry iff `sin θ = 0`.
9. `time_canonical` — `Λ ∈ O(3, 1)` with `Λ c Λ⁻¹ = P` is `diag(R, s)`,
   `Rᵀ R = 1`, `s = ±1`.
10. `conj_P_iff_orthogonal` — for `Λ ∈ O(3, 1)`: `Λ P Λ⁻¹ = P ⟺ Λ Λᵀ = 1`.
11. `boost_span` — `diag(R, s) K diag(Rᵀ, s) = −s (n₀ L03 + n₁ L13 + n₂ L23)`,
    `n = R e₂`.
12. `phase_not_mem_so31` — `diag(R, s) J diag(Rᵀ, s) ∉ so(3, 1)` for
    `Rᵀ R = 1`, `s = ±1`.
13. `hodge_exchange` — `H(diag(R, s) K diag(Rᵀ, s)) = s (n₀ L12 − n₁ L02 + n₂ L01)`;
    at `R = 1`, `s = 1`: `H(K) = L01`.
14. `divide_iConj` — `D(iConj) = ½(ρ + Q) iConj − ½ i (ρ − Q) L01`.
15. `divide_mul_flip` — `D · flip D = ρQ · 1`.
16. `holst_gamma_not_real` — if `1 + γ⁻¹ H ∝ D` with `ρ ≠ Q`, `ρ + Q ≠ 0`,
    then `Re γ = 0` and `Im γ ≠ 0`.

The exact Lean statements, the definitions they use, and the hypotheses
of each are in the opening docstring of `Challenge.lean`, which is the
scope account of the entry.

## What is classical, what is the author's, what is new here

**Classical, and not this structure.** `Herm₂(ℂ) ≅ ℝ^{3,1}` through
the determinant, with the spinor action `X ↦ A X A†` of `SL(2, ℂ)`, is
classical (Jordan, von Neumann and Wigner 1934; Penrose and Rindler 1984,
vol. 1, §1.2; the spin-factor reading in Baez 2002, §3.3). Here the
Lorentz form is `tr(X Xᵀ)`, whose timelike direction is `σ_y`, not
`det X`, and the boost is `i` composed with Galois conjugation, which is
not `ℂ`-linear and is not a Born isometry (6), whereas unitary
conjugations are. That the Hodge dual of a boost generator of `so(3, 1)`
is a rotation generator is textbook (the self-dual/anti-self-dual
splitting of `so(3, 1) ⊗ ℂ`); 13 says which boost and which rotation in
place coordinates. The count in 1–2 is Sylvester's law of inertia on
the place shape `(n, n(n−1)/2)` of `Herm_n(ℂ)`; the type `(r₁ + r₂, r₂)`
of the trace form of a number field is Hermite–Sylvester, in number-field
form O. Taussky (1968). The nearest statement found to "a number field
as a qubit" is Banaszak, Barańczuk, Lulek, Milewski and Stagraczyński
(2012): two Galois-conjugate real eigenvalues of a rank-2 extension as
two levels, with no complex place, no Hermitian matrix space and no
Lorentz form. No priority is claimed for any ingredient.

**The author's registered entries.** The instance of the shape `r₁ = 2`
is the field `ℚ(Q)`, `Q⁴ = Q + 1`, with places `(2, 1)` and trace-form
type `(3, 1)`, of PALOMAR-2026-10-21-000012 (which also formalizes the
general type `(r₁ + r₂, r₂)`); nothing about that field is restated or
compared here — every statement is for the abstract place space, or for
`Herm_n(ℂ)`. The register data of 9–16 are those of
PALOMAR-2026-09-30-000024 (`stalex444/pdt-hodge-lie-generation`, commit
`e2d8dde`: `Challenge.lean` lines 35–75 for `η`, the generators
`L_ab = η_b E_ab − η_a E_ba`, the bivector coordinates and the local
Hodge star; `GravityScreening/HodgeBulkScreen.lean` for the Hodge
rotation, chirality, projectors, divide and flip). They are transcribed
on the `0123` plane as explicit matrices and nothing is imported: the
proof module re-proves that the six restricted generators are
`η4`-skew and independent, that their span is exactly the `η4`-skew
matrices (`mem_so31_iff`), the fifteen structure constants, `H² = −1`,
and the projector identities of the divide.

**New here** is the kernel-checked classification 3–4 (field
multiplication and Galois conjugation realize a `(1+1)`-dimensional
Lorentz group on the complex place and nothing mixing a real place with
time; proved for every `r₁` by solving `T(LX, Y) + T(X, LY) = 0` on a
block-diagonal `L`), the identification of the boost generator with
`i ∘ conj` and the exponential (`hasDerivAt_boost`, flow and closed
series form, in `ArithmeticLorentz/Boost.lean`), and the bridge 9–16 on
the register's own matrices. Not compared but proved in the modules: the
type `(n(n+1)/2, n(n−1)/2)` of `tr(X Xᵀ)` on `Herm_n(ℂ)` for every `n`
(`transposeForm_signature`), the number-field link `Tr_{K/ℚ}(xy) =
Σ_w x_w y_w + Σ_w 2 Re(x_w y_w)` over Mathlib's mixed embedding
(`ArithmeticLorentz/PlaceLink.lean`), the Schur-product law `X(xy) = X(x) ⊙ X(y)`, and
`time_canonical'`, `boost_span'`, `phase_excluded'`, `hodge_exchange'`
with the scaling `S = diag(1, 1, √2, √2)` that carries the arithmetic
trace form `diag(1, 1, 2, −2)` to `η4` made explicit.

## Application (cited; not a claim of the entry)

In the author's Pisot Dimensional Theory `ℚ(Q)`, `Q⁴ = Q + 1`, is the
arithmetic of four-dimensional spacetime; its place space is `Herm₂(ℂ)`
and its trace form `Tr_{K/ℚ}(x²)` is the Minkowski form of signature
`(3, 1)` (PALOMAR-2026-10-21-000012). Read through the theory, 3–8 say
that the only Lorentz symmetry the arithmetic itself carries is the
boost `i ∘ c` of the complex place — generated by Galois conjugation,
with Galois conjugation as time reversal — and that the phase, the
symmetry of the Born form, is not a Lorentz symmetry; 9–10 say that a
Lorentz map carrying Galois conjugation to the register's time
reflection fixes the time axis up to sign and is otherwise a rotation of
the three remaining place directions; 11–13 place the arithmetic boost
in the register's boost span and send it, by the Hodge star, to the
rotation of the two real places; and 14–16 say that the Hodge divide
`ρ P₊ + Q P₋` of the register mixes that boost with that rotation unless
`ρ = Q`, that it is a unit of weight `ρQ` against its flip, and that its
Holst coefficient is purely imaginary, so no real Barbero–Immirzi
parameter can be read off it.

## Layout and build

`Challenge.lean` states the entry's definitions (the shared block) and
the sixteen results with placeholder proofs; `Solution.lean` proves
them by direct transfer from the proof modules; `comparator.json` lists
the sixteen compared declarations, in order; `formalization.yaml`
carries sources, classification and disclosure; `BUILD.txt` is the build
and axiom record (toolchain, Mathlib revision, warnings per file,
`#print axioms` for every compared declaration, the local run of the
registry's pipeline and comparator); `SHA256SUMS.txt` hashes every
shipped file; `READINESS.md` records the pre-submission checks.

The compared statements use definitions of this entry (`herm`,
`transposeForm`, `hsForm`, `placeEquiv`, `PlaceSpace`, `traceB`, `bornB`,
`galoisConj`, `boostGen`, `boostC`, `boost`, `PlacePreserving`,
`IsInfIsometry`, `IsIsometry`, `phaseV`, and the register matrices `η4`,
`L01r … L23r`, `so31`, `cArith`, `Preg`, `Kmat`, `Jmat`, `blockDiag`,
`hodgeOp` with `Hmat`, `coords4`, `fromCoords`, `HC`, `chirality`,
`Pplus`, `Pminus`, `divide`, `divideFlip`, `iConjVec`, `L01Vec`). They are
defined in `ArithmeticLorentz/Defs.lean`, which imports Mathlib only and
on which the proof modules are built. `Challenge.lean` repeats that block
byte for byte between the lines `-- BEGIN SHARED DEFINITIONS` and
`-- END SHARED DEFINITIONS`, so it too imports Mathlib only;
`tools/check_shared_block.py` verifies the identity and
`tools/check_count.py` verifies that the compared set, its count in the
opening docstring, `comparator.json`, `Solution.lean` and
`formalization.yaml` agree (both exit non-zero on any mismatch).

Proof modules (namespace
`HermitianExclusion`, kept from the development they come from, whose
first theorem is statement 2):
- `ArithmeticLorentz/Defs.lean` — the shared definitions.
- `ArithmeticLorentz/Counting.lean` — the place form `Σ x_i² + Σ 2 Re(z_j²)` on
  `ℝ^{r₁} × ℂ^{r₂}` has type `(r₁ + r₂, r₂)`; the Born place form is
  positive definite (Mathlib's `sigPos`, `sigNeg`, Sylvester's law).
- `ArithmeticLorentz/Arithmetic.lean` — `n(n−1)/2 = 1 ↔ n = 2` and the shape arithmetic.
- `ArithmeticLorentz/Qubit.lean` — `Herm₂(ℂ)` through the place matrix: `tr(XY)`,
  `tr(XYᵀ)`, their difference `4 (Im z)²`, `X − Xᵀ = 2 Im(z) σ_y`, the
  types `(3, 1)` and `(4, 0)`, the Schur-product law.
- `ArithmeticLorentz/HermN.lean` — `tr(XXᵀ)` on `Herm_n(ℂ)` has type `(n(n+1)/2, n(n−1)/2)`;
  statements 1, 2.
- `ArithmeticLorentz/PlaceLink.lean` — the trace and Born forms of any number field in
  Mathlib's mixed-embedding coordinates; for `(r₁, r₂) = (2, 1)`,
  `Tr_{K/ℚ}(xy) = Re tr(XYᵀ)` and `Σ_φ φ(x) conj φ(y) = tr(XY)`.
- `ArithmeticLorentz/Boost.lean` — `iConj`, the boost and its flow, the two isometry
  results, time reversal, the classification, the polar phase;
  statements 3–8.
- `ArithmeticLorentz/RegisterBridge.lean` — the register's `so(3, 1)` and the bridge;
  statements 9–16.

```
lake exe cache get
lake build
```

(pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; the default targets are
`ArithmeticLorentz`, `Challenge` and `Solution`; a green build is the
kernel verification). `.github/workflows/palomar-preflight.yml` runs the
registry's mechanical preflight on a chosen commit.

## Context

This repository is a complete, self-contained proof development; nothing
is imported from any other project. Pisot Dimensional Theory is the
author's; its kernel-verified formal spine is the PDT-Lean record
([stalex444/pdt-lean](https://github.com/stalex444/pdt-lean)). The
entry uses, as cited data, the register of PALOMAR-2026-09-30-000024,
and refers to PALOMAR-2026-10-21-000012 for the field instance.

## References

Mathematics and physics
- P. Jordan, J. von Neumann, E. Wigner, "On an algebraic generalization
  of the quantum mechanical formalism", Ann. of Math. 35 (1934), no. 1,
  29–64. doi:10.2307/1968117
- R. Penrose, W. Rindler, *Spinors and space-time*, vol. 1, Cambridge
  University Press, 1984, §1.2. doi:10.1017/CBO9780511564048
- J. C. Baez, "The octonions", Bull. Amer. Math. Soc. 39 (2002), 145–205,
  §3.3. arXiv:math/0105155
- O. Taussky, "The discriminant matrices of an algebraic number field",
  J. London Math. Soc. s1-43 (1968), no. 1, 152–154.
  doi:10.1112/jlms/s1-43.1.152
- G. Banaszak, S. Barańczuk, T. Lulek, J. Milewski, R. Stagraczyński,
  "Galois properties of the eigenproblem of the hexagonal magnetic
  Heisenberg ring", Acta Phys. Pol. A 121 (2012), 1111–1114.
  doi:10.12693/APhysPolA.121.1111
- S. Holst, "Barbero's Hamiltonian derived from a generalized
  Hilbert–Palatini action", Phys. Rev. D 53 (1996), 5966–5969.
  doi:10.1103/PhysRevD.53.5966 (the Holst term, for the terminology
  of statement 16).

Formalizations
- Mathlib, commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`: D.
  Loeffler, `Mathlib/LinearAlgebra/QuadraticForm/Signature.lean`
  (`sigPos`, `sigNeg`, Sylvester's law);
  `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean` and
  `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean`
  (infinite places, the mixed embedding).
- Registered entry PALOMAR-2026-09-30-000024,
  `stalex444/pdt-hodge-lie-generation` @ `e2d8dde` (the register data,
  transcribed, not imported).
- Registered entry PALOMAR-2026-10-21-000012 (the trace-form signature
  `(r₁ + r₂, r₂)` and the field `ℚ(Q)`).

## Licence

MIT (see `LICENSE`).
