module
public import Mathlib
public import ArithmeticLorentz.Defs
public import ArithmeticLorentz.Counting
public import ArithmeticLorentz.Arithmetic
public import ArithmeticLorentz.Qubit
public import ArithmeticLorentz.HermN
public import ArithmeticLorentz.PlaceLink
public import ArithmeticLorentz.Boost
public import ArithmeticLorentz.RegisterBridge

@[expose] public section
/-!
# The arithmetic Lorentz group of a number field with one complex place, and its bridge to the local Hodge register

Proof modules (namespace `HermitianExclusion`, kept from the development they come from; the
compared statements are restated in namespace `ArithmeticLorentz` in `Challenge.lean` and proved
in `Solution.lean` by `exact` of the theorems below):

* `ArithmeticLorentz.Defs` — the definitions the compared statements use (imports Mathlib only;
  repeated byte for byte in `Challenge.lean`).
* `ArithmeticLorentz.Counting` — the place form `Σ x_i² + Σ 2 Re(z_j²)` on `ℝ^{r₁} × ℂ^{r₂}` has
  type `(r₁ + r₂, r₂)`; its Born companion `Σ x_i² + Σ 2|z_j|²` is positive definite.
* `ArithmeticLorentz.Arithmetic` — `n(n−1)/2 = 1 ↔ n = 2`, and the place-shape corollary.
* `ArithmeticLorentz.Qubit` — `Herm₂(ℂ)` with the explicit place isomorphism `ℝ² × ℂ ≃ Herm₂(ℂ)`:
  Born = `tr(XY)`, trace = `tr(XYᵀ)`, difference `4 (Im x_σ)²`, `X − Xᵀ = 2 Im(x_σ) σ_y`, types
  `(3, 1)` and `(4, 0)`; field multiplication is the Schur product of place matrices.
* `ArithmeticLorentz.HermN` — `tr(XXᵀ)` on `Herm_n(ℂ)` has type `(n(n+1)/2, n(n−1)/2)`; one
  negative direction iff `n = 2` (statements 1, 2).
* `ArithmeticLorentz.PlaceLink` — for every number field, `Tr_{K/ℚ}(xy)` and `Σ_φ φ(x) conj φ(y)`
  in Mathlib's mixed-embedding coordinates; for `(r₁, r₂) = (2, 1)`, `Tr = Re tr(XYᵀ)` and
  `Born = tr(XY)` on the place matrices.
* `ArithmeticLorentz.Boost` — the arithmetic boost on the place space `ℝ^{r₁} × ℂ`: `iConj` is an
  involution and not a multiplication; `boost β` is its flow, a trace-form isometry that is not a
  Born isometry; Galois conjugation reverses it; the place-preserving infinitesimal isometries of
  the trace form are exactly `ℝ · boostGen`, the isometries `{±1}^{r₁} × O(1, 1)`; the polar phase
  is a trace-form isometry iff `sin θ = 0` (statements 3–8).
* `ArithmeticLorentz.RegisterBridge` — the bridge to the register's `so(3,1) ⊂ so(4,2)`: the six
  local generators span the `η4`-skew matrices (dimension 6, fifteen structure constants);
  `time_canonical`, `conj_P_iff_orthogonal`, `boost_span`, `phase_not_mem_so31`, `hodge_exchange`,
  the projector identities of the divide, `divide_iConj`, `divide_mul_flip`, and the imaginary
  Holst coefficient (statements 9–16).
-/
