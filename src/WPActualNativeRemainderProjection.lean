import WPActualNativeRemainderSource

open scoped BigOperators Polynomial LaurentPolynomial Classical
open LaurentPolynomial WPActualNativeCanonicalPart WPActualNativeRemainderSource
  WPActualCanonicalFinitePart WPCartierPoleProjection WPActualPositivePair
  WPActualEtaFieldCutoff

namespace WPActualNativeRemainderProjection

variable (p : ℕ) [Fact p.Prime]

theorem polynomial_negative_value_zero (P : (ZMod p)[X]) (a : ZMod p) :
    negativeValue p (Polynomial.toLaurent P) a = 0 := by
  unfold negativeValue
  apply Finset.sum_eq_zero
  intro j hj
  rw [support_coeff_toLaurent] at hj
  obtain ⟨n, _, rfl⟩ := Finset.mem_map.mp hj
  simp only [Nat.castEmbedding_apply]
  exact if_neg (by omega)

theorem coefficientValue_C_mul (q : ℤ → Prop) (a c : ZMod p)
    (A : (ZMod p)[T;T⁻¹]) :
    coefficientValue p q a (C c * A) = c * coefficientValue p q a A := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

/-- Every negative coefficient of the original Aeta is retained in the bounded B0. -/
theorem actual_native_negative_value (hp : 19 ≤ p) (a : ZMod p) :
    negativeValue p (literalFieldAeta p hp) a = negativeValue p (nativeRemainder p hp) a := by
  rw [negativeValue_linear, actual_native_canonical_decomposition,
    map_add, coefficientValue_C_mul, map_sub, map_sub]
  have hg := polynomial_negative_value_zero p (pullbackPolynomial p (nativeHJet p)) a
  rw [negativeValue_linear] at hg
  have hc (c : ZMod p) : coefficientValue p (fun j => j < 0) a (C c) = 0 := by
    simpa only [T_zero, mul_one, if_neg (by omega : ¬(0 : ℤ) < 0)] using
      coefficientValue_monomial p (fun j => j < 0) a c 0
  rw [hg, hc, coefficientValue_monomial,
    if_neg (by omega : ¬(p : ℤ) < 0), sub_zero, sub_zero, mul_zero, add_zero,
    ← negativeValue_linear]

theorem actual_native_remainder_high_zero (hp : 19 ≤ p) (a : ZMod p) :
    highValue p (nativeRemainder p hp) a = 0 := by
  unfold highValue
  apply Finset.sum_eq_zero
  intro j hj
  have hb := actual_native_remainder_support p hp j (Finsupp.mem_support_iff.mp hj)
  exact if_neg (by omega)

theorem actual_native_remainder_projection (hp : 19 ≤ p) :
    canonicalProjection p (nativeRemainder p hp) =
      (1044 / 625) * valueAt p (nativeRemainder p hp) (1 / 4) -
        (828 / 625) * valueAt p (nativeRemainder p hp) 4 +
        (432 / 625) * (-2 * negativeValue p (nativeRemainder p hp) (1 / 4) -
          negativeValue p (nativeRemainder p hp) 4) := by
  rw [canonicalProjection_formula, actual_native_remainder_high_zero,
    actual_native_remainder_high_zero]
  ring

/-- NC71 period after the actual support bound; the negative source and Cp remain explicit. -/
theorem actual_native_canonicalPeriod_bounded (hp : 19 ≤ p) :
    (WPActualEtaIntegration.canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      (1044 / 625) * valueAt p (nativeRemainder p hp) (1 / 4) -
        (828 / 625) * valueAt p (nativeRemainder p hp) 4 +
        (432 / 625) * (-2 * negativeValue p (nativeRemainder p hp) (1 / 4) -
          negativeValue p (nativeRemainder p hp) 4) -
        (36 / 625) * (pullbackPolynomial p (nativeHJet p)).coeff 0 +
        (1017 / 8750) * (pullbackPolynomial p (nativeHJet p)).coeff p := by
  rw [actual_native_canonicalPeriod, actual_native_remainder_projection]

/-- The normalized original four-part projection, including both invisible native coefficients. -/
theorem actual_native_normalized_period (hp : 19 ≤ p) :
    (625 / 216 : ZMod p) *
      (WPActualEtaIntegration.canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      (29 / 6) * valueAt p (nativeRemainder p hp) (1 / 4) -
        (23 / 6) * valueAt p (nativeRemainder p hp) 4 +
        2 * (-2 * negativeValue p (nativeRemainder p hp) (1 / 4) -
          negativeValue p (nativeRemainder p hp) 4) -
        (pullbackPolynomial p (nativeHJet p)).coeff 0 / 6 +
        (113 / 336) * (pullbackPolynomial p (nativeHJet p)).coeff p := by
  have hu (n : ℕ) (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff n p).mp h
    have hh := Nat.le_of_dvd hn hd
    omega
  have h2 := hu 2 (by norm_num) (by omega)
  have h3 := hu 3 (by norm_num) (by omega)
  have h5 := hu 5 (by norm_num) (by omega)
  have h7 := hu 7 (by norm_num) (by omega)
  rw [actual_native_canonicalPeriod_bounded p hp]
  have h216 : (216 : ZMod p) ≠ 0 := by
    rw [show (216 : ZMod p) = 2 ^ 3 * 3 ^ 3 by ring]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have h625 : (625 : ZMod p) ≠ 0 := by
    rw [show (625 : ZMod p) = 5 ^ 4 by ring]
    exact pow_ne_zero _ h5
  have h8750 : (8750 : ZMod p) ≠ 0 := by
    rw [show (8750 : ZMod p) = 2 * 7 * 5 ^ 4 by ring]
    exact mul_ne_zero (mul_ne_zero h2 h7) (pow_ne_zero _ h5)
  have h6 : (6 : ZMod p) ≠ 0 := by
    rw [show (6 : ZMod p) = 2 * 3 by ring]
    exact mul_ne_zero h2 h3
  have h336 : (336 : ZMod p) ≠ 0 := by
    rw [show (336 : ZMod p) = 2 ^ 4 * 3 * 7 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h3) h7
  field_simp [h216, h625, h8750, h6, h336]
  ring

end WPActualNativeRemainderProjection
