import WPFieldAssembly.ActualBpairLowHEuler

namespace WPFieldAssembly.ActualBpairContraction

variable {F : Type*} [Field F]

set_option maxHeartbeats 1200000

/-- The actual conic relation identifies the whole proper-end quartic. -/
theorem lowH_conic_quartic_identity (τ w : F) (hc : 5 * τ ^ 2 = w ^ 2 + 1) :
    (4 - w ^ 2) * (4 * w ^ 2 - 1) = 25 * ((1 - τ ^ 2) * (4 * τ ^ 2 - 1)) := by
  linear_combination (20 * τ ^ 2 + 4 * w ^ 2 - 21) * hc

/-- No proper-end factor is removed before the original cleared source is used. -/
theorem lowH_conic_quartic_cancel (τ w d R : F) (h5 : (5 : F) ≠ 0)
    (hc : 5 * τ ^ 2 = w ^ 2 + 1)
    (ha : (4 - w ^ 2) * (4 * w ^ 2 - 1) ≠ 0) (hsource :
      (4 - w ^ 2) * (4 * w ^ 2 - 1) * d = R) :
    d * ((1 - τ ^ 2) * (4 * τ ^ 2 - 1)) = R / 25 := by
  have h25 : (25 : F) ≠ 0 := by convert pow_ne_zero 2 h5 using 1; norm_num
  apply mul_left_cancel₀ ha
  rw [← mul_assoc, hsource, lowH_conic_quartic_identity τ w hc]
  field_simp [h25]

/-- The full signed reciprocal phase is retained after the quartic cancellation. -/
theorem lowH_conic_Dsym_delta_cancellation (N : ℕ) (τ w d dτ P : F)
    (h5 : (5 : F) ≠ 0) (hw : w ≠ 0)
    (hc : 5 * τ ^ 2 = w ^ 2 + 1)
    (ha : (4 - w ^ 2) * (4 * w ^ 2 - 1) ≠ 0)
    (hsource : (4 - w ^ 2) * (4 * w ^ 2 - 1) * d =
      5 * w * τ ^ (2 * N) * ((w ^ (2 * N))⁻¹ - 1))
    (hder : 5 * τ * dτ = w) :
    τ ^ (2 * N + 1) * d * ((1 - τ ^ 2) * (4 * τ ^ 2 - 1) * P) =
      (((τ ^ 2 / w) ^ (2 * N + 1) * w - τ ^ (2 * (2 * N + 1))) * P * dτ) := by
  have he := lowH_conic_quartic_cancel τ w d _ h5 hc ha hsource
  have h25 : (25 : F) ≠ 0 := by convert pow_ne_zero 2 h5 using 1; norm_num
  have hpw : w ^ (2 * N) ≠ 0 := pow_ne_zero _ hw
  rw [show τ ^ (2 * N + 1) * d * ((1 - τ ^ 2) * (4 * τ ^ 2 - 1) * P) =
      τ ^ (2 * N + 1) * (d * ((1 - τ ^ 2) * (4 * τ ^ 2 - 1))) * P by ring, he]
  simp only [div_pow, pow_add, pow_one, pow_mul]
  field_simp [hw, hpw, h25]
  linear_combination 5 * τ ^ (2 * N) * τ ^ (2 * N) * τ * P *
    (w ^ (2 * N) - 1) * hder

/-- This prints the two complete Frobenius sources, including the moving denominator. -/
theorem lowH_conic_Dsym_delta_two_sources (p : ℕ) (τ w dτ P : F) :
    (((τ ^ 2 / w) ^ p * w - τ ^ (2 * p)) * P * dτ) =
      (τ / w * τ) ^ p * (P * w * dτ) - (τ ^ 2) ^ p * (P * dτ) := by
  rw [show τ ^ 2 / w = τ / w * τ by simp only [pow_two, div_eq_mul_inv]; ring,
    pow_mul]
  ring

end WPFieldAssembly.ActualBpairContraction
