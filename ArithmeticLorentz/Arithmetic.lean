module
public import Mathlib

@[expose] public section
/-!
# (b) The arithmetic core of the exclusion

The Hermitian matrix space `Herm_n(ℂ)` has the place shape `ℝ^{r₁} × ℂ^{r₂}` with `r₁ = n` (the
diagonal) and `r₂ = n(n−1)/2` (the strict upper triangle), so by the counting statement its
transpose-twisted trace form has type `(r₁ + r₂, r₂) = (n(n+1)/2, n(n−1)/2)`. One negative
direction (`r₂ = 1`) happens exactly at `n = 2`, where `r₁ = 2` and the real dimension
`r₁ + 2 r₂ = n²` is `4`.

All divisions are natural-number divisions (`n(n−1)` is always even, so nothing is truncated).
-/

namespace HermitianExclusion

/-- `n(n−1)/2 = 1 ↔ n = 2`. -/
theorem choose_two_eq_one_iff (n : ℕ) : n * (n - 1) / 2 = 1 ↔ n = 2 := by
  constructor
  · intro h
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp_all
    · have h6 : 6 ≤ n * (n - 1) := by
        have : 2 ≤ n - 1 := by omega
        calc 6 = 3 * 2 := by norm_num
          _ ≤ n * (n - 1) := Nat.mul_le_mul hn this
      have : 3 ≤ n * (n - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
      omega
  · rintro rfl; norm_num

/-- `n + n(n−1)/2 = n(n+1)/2` (the positive index of `Herm_n`). -/
theorem add_choose_two (n : ℕ) : n + n * (n - 1) / 2 = n * (n + 1) / 2 := by
  rcases n with _ | m
  · simp
  · have h : (m + 1) * (m + 1 + 1) = (m + 1) * (m + 1 - 1) + 2 * (m + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

/-- `n + 2 · n(n−1)/2 = n²` (the real dimension of `Herm_n`). -/
theorem add_two_mul_choose_two (n : ℕ) : n + 2 * (n * (n - 1) / 2) = n * n := by
  have heven : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (n - 1), by rw [hk]; ring⟩
    · refine ⟨n * k, ?_⟩
      rw [hk]; simp only [Nat.add_sub_cancel]; ring
  rw [Nat.mul_div_cancel' heven]
  rcases n with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]; ring

/-- **(b) The arithmetic core.** If a place shape `(r₁, r₂)` is the Hermitian shape
`(n, n(n−1)/2)` and has exactly one complex coordinate (`r₂ = 1`), then `n = 2`, `r₁ = 2` and
the degree `r₁ + 2 r₂` is `4`. -/
theorem hermitian_shape_one_complex (n r₁ r₂ : ℕ) (h₁ : r₁ = n) (h₂ : r₂ = n * (n - 1) / 2)
    (h : r₂ = 1) : n = 2 ∧ r₁ = 2 ∧ r₁ + 2 * r₂ = 4 := by
  have hn : n = 2 := (choose_two_eq_one_iff n).mp (h₂ ▸ h)
  subst hn
  omega

/-- **(b), the type form.** The Hermitian type `(n(n+1)/2, n(n−1)/2)` has exactly one negative
direction iff `n = 2`, and then it is `(3, 1)`. -/
theorem hermitian_type_one_negative_iff (n : ℕ) :
    n * (n - 1) / 2 = 1 ↔ n = 2 := choose_two_eq_one_iff n

theorem hermitian_type_two : 2 * (2 + 1) / 2 = 3 ∧ 2 * (2 - 1) / 2 = 1 := by norm_num

/-- The converse direction of (b): the shape `(2, 1)` is Hermitian (`n = 2`). -/
theorem hermitian_shape_two : (2 : ℕ) = 2 ∧ (1 : ℕ) = 2 * (2 - 1) / 2 := by norm_num

end HermitianExclusion
