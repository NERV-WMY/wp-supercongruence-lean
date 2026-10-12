import WPFirstResidue.NativeResidue.NativeDifferential
import WPFirstResidue.LogarithmicHResidue

open scoped Polynomial LaurentPolynomial LaurentSeries RatFunc
open Polynomial LaurentPolynomial WPPIntegralReduction WPActualChiSource
  WPActualEtaPole WPActualEtaPrimitive WPActualEtaIntegrality WPActualPullbackSource
  WPActualCentralResidueSource WPActualPositiveResidueSource WPActualCentralNativeJet
  WPLaurentIntegralResidue WPActualConicInfinitySource WPActualConicInfinityAttachment
  WPHasseIntegralTransport WPFirstResidue.CentralResidue
  WPFirstResidue.CentralResidueAttachment WPFirstResidue.LogarithmicHResidue
  WPMomentPrecision.ConicCoordinates

namespace WPFirstResidue.NativeResidue

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

noncomputable def integralHQPullback (hp : 19 ≤ p) : (integralRationals p)[T;T⁻¹] :=
  invert (Polynomial.toLaurent
    ((nativeHIntegral p (by omega)).comp (integralV p (by omega))))

theorem integralHQPullback_rational (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (integralHQPullback p hp) = Hpull (p / 6) Qx := by
  rw [integralHQPullback, coefficientMap_invert, coefficientMap_toLaurent,
    Polynomial.map_comp, nativeHIntegral_map_rational, integralV_map_rational]
  rw [← substituteOver_toLaurent, substituteOver_invert]
  change substituteOver (Hpolynomial (p / 6)) (invert Vx) = Hpull (p / 6) Qx
  rw [actual_Vx_reciprocal]
  rfl

theorem actual_HQ_integral (hp : 19 ≤ p) : Hpull (p / 6) Qx ∈ integralLaurent p := by
  rw [← integralHQPullback_rational p hp]
  exact coefficientMap_subtype_integral p _

noncomputable def fieldHQPullback : (ZMod p)[T;T⁻¹] :=
  substituteOver (nativeHField p) (nativeQField p)

theorem integralHQPullback_field (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (integralHQPullback p hp) = fieldHQPullback p := by
  rw [integralHQPullback, coefficientMap_invert, coefficientMap_toLaurent,
    Polynomial.map_comp, nativeHIntegral_map_field, integralV_map_field,
    ← substituteOver_toLaurent, substituteOver_invert]
  rfl

noncomputable def integralHQDensity (hp : 19 ≤ p) : (integralRationals p)[T;T⁻¹] :=
  integralLift p ⟨weightedDifference (Hpull (p / 6) Qx),
    weightedDifference_integral p (by omega) _ (actual_HQ_integral p hp)⟩

noncomputable def fieldHQDensity (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  coefficientMap (residueHom p) (integralHQDensity p hp)

theorem fieldHQDensity_coefficient (hp : 19 ≤ p) (j : ℤ) :
    (fieldHQDensity p hp).coeff j =
      ((weightedDifference (Hpull (p / 6) Qx)).coeff j : ZMod p) := by
  rw [fieldHQDensity, coefficientMap_coeff, integralHQDensity, integralLift_coeff]
  rfl

omit [Fact p.Prime] in
theorem actual_HQ_cleared_density :
    (T 1 - LaurentPolynomial.C (1 / 4 : ℚ)) *
      (T 1 - LaurentPolynomial.C (4 : ℚ)) *
        weightedDifference (Hpull (p / 6) Qx) =
      (LaurentPolynomial.C (2 : ℚ) * (T 1 - LaurentPolynomial.C (4 : ℚ)) +
        (T 1 - LaurentPolynomial.C (1 / 4 : ℚ))) *
        Hpull (p / 6) Qx := by
  have ha := dividedDifference_identity (1 / 4) (by norm_num) (Hpull (p / 6) Qx)
  have hb := dividedDifference_identity 4 (by norm_num) (Hpull (p / 6) Qx)
  rw [(Hpull_Q_endpoints (p / 6)).1, map_zero, sub_zero] at ha
  rw [(Hpull_Q_endpoints (p / 6)).2, map_zero, sub_zero] at hb
  rw [weightedDifference_apply]
  linear_combination LaurentPolynomial.C (2 : ℚ) *
    (T 1 - LaurentPolynomial.C (4 : ℚ)) * ha +
    (T 1 - LaurentPolynomial.C (1 / 4 : ℚ)) * hb

theorem actual_integral_HQ_cleared_density (hp : 19 ≤ p) :
    (T 1 - LaurentPolynomial.C (integralQuarter p hp)) *
      (T 1 - (4 : (integralRationals p)[T;T⁻¹])) * integralHQDensity p hp =
      (2 * (T 1 - (4 : (integralRationals p)[T;T⁻¹])) +
        (T 1 - LaurentPolynomial.C (integralQuarter p hp))) * integralHQPullback p hp := by
  apply WPLaurentIntegralResidue.coefficientMap_injective _
    (Subring.subtype_injective (integralRationals p))
  simp only [map_mul, map_add, map_sub, map_ofNat, coefficientMap_T, coefficientMap_C,
    integralHQDensity, integralLift_rational, integralHQPullback_rational,
    integralQuarter_rational]
  simpa only [map_ofNat] using actual_HQ_cleared_density p

theorem actual_field_HQ_cleared_density (hp : 19 ≤ p) :
    (T 1 - LaurentPolynomial.C (1 / 4 : ZMod p)) *
      (T 1 - (4 : (ZMod p)[T;T⁻¹])) * fieldHQDensity p hp =
      (2 * (T 1 - (4 : (ZMod p)[T;T⁻¹])) +
        (T 1 - LaurentPolynomial.C (1 / 4 : ZMod p))) * fieldHQPullback p := by
  have h := congrArg (coefficientMap (residueHom p)) (actual_integral_HQ_cleared_density p hp)
  simpa only [map_mul, map_add, map_sub, map_ofNat, coefficientMap_T, coefficientMap_C,
    integralQuarter_field, integralHQPullback_field, fieldHQDensity] using h

noncomputable def HQLogVRational : RatFunc (ZMod p) :=
  (nativeHField p).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
    (Q (variableRat : RatFunc (ZMod p))) * logV (variableRat : RatFunc (ZMod p))

theorem actual_field_HQ_rational_density (hp : 19 ≤ p) :
    fieldRatify (fieldHQDensity p hp) = HQLogVRational p := by
  have h := congrArg (fieldRatify (K := ZMod p)) (actual_field_HQ_cleared_density p hp)
  simp only [map_mul, map_add, map_sub, map_ofNat, fieldRatify_T, fieldRatify_C,
    zpow_one, map_div₀, map_one] at h
  rw [fieldHQPullback, fieldRatify_substitute, native_Q_field_rational] at h
  have ha : (variableRat : RatFunc (ZMod p)) - 1 / 4 ≠ 0 := by
    simpa only [map_div₀, map_one, map_ofNat] using
      (variableRat_sub_constant_ne_zero (1 / 4 : ZMod p))
  have hb : (variableRat : RatFunc (ZMod p)) - 4 ≠ 0 := by
    simpa only [map_ofNat] using (variableRat_sub_constant_ne_zero (4 : ZMod p))
  unfold HQLogVRational logV
  field_simp [ha, hb]
  linear_combination h

theorem actual_HQ_logV_series (_hp : 19 ≤ p) :
    algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩ (HQLogVRational p) = nativeHQ p * nativeLogV p := by
  simp only [HQLogVRational, map_mul, Polynomial.hom_eval₂, original_rational_coefficients,
    Q, map_div₀, map_pow, map_sub, map_ofNat, map_one, logV, map_add,
    originalX_rational, nativeHQ, nativeQ, nativeLogV]

noncomputable def nativeH0 : ZMod p :=
  (((Hpolynomial (p / 6)).eval (4 / 125 : ℚ) : ℚ) : ZMod p)

theorem native_H0_integral (hp : 19 ≤ p) :
    (Hpolynomial (p / 6)).eval (4 / 125 : ℚ) ∈ integralRationals p := by
  have h := actual_HX_integral p (p / 6) (by omega) (by omega) 0
  rwa [actual_HX_constant] at h

/-- NC58's full logarithmic term is attached to the original field H(Q)
density via the actual integral lift and both endpoint zeros. -/
theorem actual_native_HQ_dlogV_residue (hp : 19 ≤ p) :
    (nativeHQ p * nativeLogV p).coeff (-1) = 3 * nativeH0 p := by
  rw [← actual_HQ_logV_series p hp, ← actual_field_HQ_rational_density p hp]
  have hc := rationalSeries_coefficient (fieldHQDensity p hp) (-1)
  change (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
    (fieldRatify (fieldHQDensity p hp))).coeff (-1) = _ at hc
  rw [hc, fieldHQDensity_coefficient, actual_HQ_dlogV_residue]
  have h0 := native_H0_integral p hp
  rw [Rat.cast_mul_of_ne_zero
    (integral_denominator_cast_ne_zero p 3 (natCast_mem (integralRationals p) 3))
    (integral_denominator_cast_ne_zero p _ h0)]
  simp only [Rat.cast_ofNat, nativeH0]

end WPFirstResidue.NativeResidue
