import WPCartierFinite.Basic

open scoped BigOperators

namespace WPCartierFinite

section ScalarAlgebra

variable {V : Type*} [CommRing V] [Algebra ℚ V]

/-- The exact five-term scalar identity follows from the stated mixed-monomial exclusions. -/
theorem scalar_hockey_stick (A B F : V) (L : V →ₗ[ℚ] ℚ)
    (hexcl : ∀ h v : ℕ, h + v ≤ 4 → L (A ^ h * B ^ v * F) = L (B ^ v * F)) :
    (∑ k ∈ Finset.range 5, L ((A - B) ^ k * F)) =
      5 * L F - 10 * L (B * F) + 10 * L (B ^ 2 * F) -
        5 * L (B ^ 3 * F) + L (B ^ 4 * F) := by
  have hpoly : (∑ k ∈ Finset.range 5, (A - B) ^ k * F) =
      F + A * F - B * F + A ^ 2 * F - (2 : ℕ) • (A * B * F) + B ^ 2 * F +
        A ^ 3 * F - (3 : ℕ) • (A ^ 2 * B * F) + (3 : ℕ) • (A * B ^ 2 * F) - B ^ 3 * F +
        A ^ 4 * F - (4 : ℕ) • (A ^ 3 * B * F) + (6 : ℕ) • (A ^ 2 * B ^ 2 * F) -
        (4 : ℕ) • (A * B ^ 3 * F) + B ^ 4 * F := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, nsmul_eq_mul]
    ring
  have h10 := hexcl 1 0 (by omega)
  have h20 := hexcl 2 0 (by omega)
  have h11 := hexcl 1 1 (by omega)
  have h30 := hexcl 3 0 (by omega)
  have h21 := hexcl 2 1 (by omega)
  have h12 := hexcl 1 2 (by omega)
  have h40 := hexcl 4 0 (by omega)
  have h31 := hexcl 3 1 (by omega)
  have h22 := hexcl 2 2 (by omega)
  have h13 := hexcl 1 3 (by omega)
  simp only [pow_zero, pow_one, mul_one, one_mul] at h10 h20 h11 h30 h21 h12 h40 h31 h22 h13
  have hNat (n : ℕ) (x : V) : L ((n : V) * x) = (n : ℚ) * L x := by
    simpa [Algebra.smul_def] using L.map_smul (n : ℚ) x
  rw [← map_sum, hpoly]
  simp only [map_add, map_sub, nsmul_eq_mul, hNat]
  rw [h10, h20, h11, h30, h21, h12, h40, h31, h22, h13]
  ring

/-- Multiplying the actual G-power by p^k cancels the defining denominator uniformly in k. -/
theorem scalar_power_cancellation (p : ℚ) (A B G : V)
    (hG : p • G = A - B) (k : ℕ) : p ^ k • G ^ k = (A - B) ^ k := by
  rw [← hG]
  simp only [Algebra.smul_def, map_pow, mul_pow]

/-- The finite p-weighted scalar has the same exact hockey-stick expression. -/
theorem scalar_weighted_hockey_stick (p : ℚ) (A B F G : V) (L : V →ₗ[ℚ] ℚ)
    (hG : p • G = A - B)
    (hexcl : ∀ h v : ℕ, h + v ≤ 4 → L (A ^ h * B ^ v * F) = L (B ^ v * F)) :
    (∑ k ∈ Finset.range 5, p ^ k * L (G ^ k * F)) =
      5 * L F - 10 * L (B * F) + 10 * L (B ^ 2 * F) -
        5 * L (B ^ 3 * F) + L (B ^ 4 * F) := by
  rw [← scalar_hockey_stick A B F L hexcl]
  apply Finset.sum_congr rfl
  intro k _
  rw [← scalar_power_cancellation p A B G hG k]
  rw [smul_mul_assoc, map_smul]
  rfl

end ScalarAlgebra

end WPCartierFinite
