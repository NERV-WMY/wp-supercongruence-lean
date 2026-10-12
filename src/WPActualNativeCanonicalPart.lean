import WPActualCanonicalFinitePart
import WPActualNativeJetODE

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPActualCanonicalFinitePart WPActualPositivePair
  WPActualFieldPrimitive WPActualEtaFieldCutoff WPActualNativeJetODE WPActualNativeParameter

namespace WPActualNativeCanonicalPart

variable (p : ℕ) [Fact p.Prime]

/-- The original H_J of NC70, using every actual parameter-derivative coefficient. -/
noncomputable def nativeHJet : (ZMod p)[X] := eulerPrimitive p (nativeJetField p)

theorem nativeHJet_coeff (n : ℕ) : (nativeHJet p).coeff n =
    (if n < (p - 1) / 2 + 1 then (parameterJet n (-(p : ℚ) / 6) : ZMod p) else 0) /
      (n : ZMod p) := by
  rw [nativeHJet, eulerPrimitive_coeff, nativeJetField_coeff]

theorem nativeHJet_origin : (nativeHJet p).coeff 0 = 0 := by
  rw [nativeHJet_coeff]
  simp

theorem nativeHJet_degree : (nativeHJet p).natDegree ≤ (p - 1) / 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [nativeHJet_coeff, if_neg (by omega), zero_div]

theorem nativeHJet_actual_source (hp : 19 ≤ p) :
    Polynomial.X * (nativeHJet p).derivative = nativeJetField p := by
  apply eulerPrimitive_derivative
  · have h := nativeJetField_degree p
    omega
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using nativeJetField_origin p

/-- Actual source-selected B_0, with the original full Peta and native H_J. -/
noncomputable def nativeRemainder (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  literalRemainder p hp (nativeHJet p)

theorem actual_native_remainder_resonant_zero (hp : 19 ≤ p) (k : ℤ) :
    (nativeRemainder p hp).coeff (k * p) = 0 :=
  literalRemainder_resonant_zero p hp _ k

/-- Actual NC71 decomposition; no native jet or source value is a theorem premise. -/
theorem actual_native_canonical_decomposition (hp : 19 ≤ p) :
    literalFieldAeta p hp = nativeRemainder p hp + C (1 / 6) *
      (Polynomial.toLaurent (pullbackPolynomial p (nativeHJet p)) -
        C ((pullbackPolynomial p (nativeHJet p)).coeff 0) -
        C ((pullbackPolynomial p (nativeHJet p)).coeff p) * T (p : ℤ)) :=
  literal_canonical_decomposition p hp _ (nativeHJet_degree p)

theorem actual_native_remainder_source (hp : 19 ≤ p) :
    fieldDerivative p (nativeRemainder p hp) = literalFieldPeta p hp -
      C (WPActualEtaPrimitive.actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 : ZMod p) *
        T (-1) - C (1 / 6) *
      fieldDerivative p (Polynomial.toLaurent (pullbackPolynomial p (nativeHJet p))) :=
  literalRemainder_source p hp _ (nativeHJet_degree p)

theorem actual_native_pullback_endpoints (hp : 19 ≤ p) :
    (pullbackPolynomial p (nativeHJet p)).eval (1 / 4) = 0 ∧
      (pullbackPolynomial p (nativeHJet p)).eval 4 = 0 :=
  pullback_endpoints p hp _ (nativeHJet_origin p)

theorem actual_native_pullback_high_pair_zero (hp : 19 ≤ p) :
    8 * WPCartierPoleProjection.highValue p (Polynomial.toLaurent
        (pullbackPolynomial p (nativeHJet p))) (1 / 4) +
      WPCartierPoleProjection.highValue p (Polynomial.toLaurent
        (pullbackPolynomial p (nativeHJet p))) 4 / 4 = 0 :=
  actual_high_pair_zero p hp _ (nativeHJet_degree p) (nativeHJet_origin p)

theorem actual_native_pullback_low_pair_zero (hp : 19 ≤ p) :
    8 * WPCartierPoleProjection.valueAt p (lowPart p (Polynomial.toLaurent
        (pullbackPolynomial p (nativeHJet p)))) (1 / 4) +
      WPCartierPoleProjection.valueAt p (lowPart p (Polynomial.toLaurent
        (pullbackPolynomial p (nativeHJet p)))) 4 / 4 = 0 :=
  actual_low_pair_zero p hp _ (nativeHJet_degree p) (nativeHJet_origin p)

/-- The original canonical period with its actual native C0 and Cp both retained. -/
theorem actual_native_canonicalPeriod (hp : 19 ≤ p) :
    (WPActualEtaIntegration.canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      canonicalProjection p (nativeRemainder p hp) -
        (36 / 625) * (pullbackPolynomial p (nativeHJet p)).coeff 0 +
        (1017 / 8750) * (pullbackPolynomial p (nativeHJet p)).coeff p :=
  literal_canonicalPeriod_finite_part p hp _ (nativeHJet_degree p) (nativeHJet_origin p)

end WPActualNativeCanonicalPart
