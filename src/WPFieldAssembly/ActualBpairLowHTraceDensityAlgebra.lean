import WPFieldAssembly.ActualBpairLowHDeltaAlgebra

namespace WPFieldAssembly.ActualBpairContraction

variable {F : Type*} [Field F]

set_option maxHeartbeats 1200000

/-- The original full conic trace source is cleared before its two proper-end poles are divided. -/
theorem lowH_conic_trace_cleared (p N : ℕ) [Fact p.Prime] [CharP F p]
    (hN : 2 * N + 1 = p) (τ w d : F) (h5 : (5 : F) ≠ 0)
    (hc : 5 * τ ^ 2 = w ^ 2 + 1)
    (hsource : (4 - w ^ 2) * (4 * w ^ 2 - 1) * d =
      5 * w * τ ^ (2 * N) * ((w ^ (2 * N))⁻¹ - 1)) :
    (4 - w ^ 2) * (4 * w ^ 2 - 1) * τ ^ p * d * (4 * τ ^ 3 - 3 * τ) =
      (1 / 5 : F) * w * (w ^ (2 * p) + 1) * (4 * w ^ 2 - 11) *
        ((w ^ (2 * N))⁻¹ - 1) := by
  have h5p : (5 : F) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := F) p 5
  have hunit : (5 : F) * (1 / 5) = 1 := mul_one_div_cancel h5
  have ht : τ ^ (2 * p) = (1 / 5 : F) * (w ^ (2 * p) + 1) := by
    have he := congrArg (fun a : F => a ^ p) hc
    rw [mul_pow, h5p, add_pow_char, one_pow] at he
    simp only [← pow_mul] at he
    linear_combination (1 / 5 : F) * he - τ ^ (2 * p) * hunit
  have htc : τ ^ p * τ ^ (2 * N) * (4 * τ ^ 3 - 3 * τ) =
      τ ^ (2 * p) * (4 * τ ^ 2 - 3) := by
    rw [show 4 * τ ^ 3 - 3 * τ = τ * (4 * τ ^ 2 - 3) by ring,
      ← mul_assoc, ← pow_add, ← pow_succ,
      show p + 2 * N + 1 = 2 * p by omega]
  have hscalar : (5 : F) * (1 / 5) * (4 * τ ^ 2 - 3) =
      (1 / 5 : F) * (4 * w ^ 2 - 11) := by
    field_simp [h5]
    linear_combination 4 * hc
  calc
    _ = τ ^ p * ((4 - w ^ 2) * (4 * w ^ 2 - 1) * d) *
        (4 * τ ^ 3 - 3 * τ) := by ring
    _ = 5 * w * (τ ^ p * τ ^ (2 * N) * (4 * τ ^ 3 - 3 * τ)) *
        ((w ^ (2 * N))⁻¹ - 1) := by rw [hsource]; ring
    _ = 5 * w * (τ ^ (2 * p) * (4 * τ ^ 2 - 3)) *
        ((w ^ (2 * N))⁻¹ - 1) := by rw [htc]
    _ = _ := by
      rw [ht]
      linear_combination w * (w ^ (2 * p) + 1) * ((w ^ (2 * N))⁻¹ - 1) * hscalar

/-- The entire trace density retains the original quartic denominator and both reciprocal phases. -/
theorem lowH_conic_trace_density (p N : ℕ) [Fact p.Prime] [CharP F p]
    (hN : 2 * N + 1 = p) (τ w d : F) (h5 : (5 : F) ≠ 0)
    (hc : 5 * τ ^ 2 = w ^ 2 + 1)
    (ha : (4 - w ^ 2) * (4 * w ^ 2 - 1) ≠ 0)
    (hsource : (4 - w ^ 2) * (4 * w ^ 2 - 1) * d =
      5 * w * τ ^ (2 * N) * ((w ^ (2 * N))⁻¹ - 1)) :
    τ ^ p * d * (4 * τ ^ 3 - 3 * τ) =
      ((1 / 5 : F) * w * (w ^ (2 * p) + 1) * (4 * w ^ 2 - 11) *
        ((w ^ (2 * N))⁻¹ - 1)) / ((4 - w ^ 2) * (4 * w ^ 2 - 1)) := by
  apply (eq_div_iff ha).mpr
  have he := lowH_conic_trace_cleared p N hN τ w d h5 hc hsource
  simpa only [mul_assoc, mul_comm, mul_left_comm] using he

end WPFieldAssembly.ActualBpairContraction
