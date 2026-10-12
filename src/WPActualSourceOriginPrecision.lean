import WPActualFirstConductorPrecision

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1000000

/-- The original complete source differs from the actual conductor by precisely the three retained errors. -/
theorem actual_source_conductor_error_identity (p : ℕ) (hp : 0<p) :
    actualTotalSource p-RatFunc.C (WPReview.nativeEndpoint p)*actualBetaFunctional p =
      RatFunc.C (WPReview.nativeEndpoint p)*actualFirstAngularError p+
        (RatFunc.C (WPReview.nativeEndpoint p)*actualFirstConductorError p+
          RatFunc.C (WPReview.nativeEndpoint p)*actualAngularHighError p) := by
  rw [actual_total_source_endpoint_split p hp, actual_first_endpoint_error_split]
  ring

theorem actual_first_endpoint_error_origin_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℤ) :
    precisionZero p 6 (actualRationalCoefficient
      (RatFunc.C (WPReview.nativeEndpoint p)*actualFirstEndpointError p) k) := by
  rw [actual_first_endpoint_error_split, mul_add, actual_rational_coefficient_add]
  exact precisionZero_add p 6 _ _
    (actual_first_angular_error_origin_precision p hp k)
    (actual_first_conductor_error_origin_precision p hp k)

/-- All actual source error coefficients have precision six, with no unspecified source or regularity premise. -/
theorem actual_source_conductor_error_origin_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℤ) :
    precisionZero p 6 (actualRationalCoefficient
      (actualTotalSource p-RatFunc.C (WPReview.nativeEndpoint p)*actualBetaFunctional p) k) := by
  rw [actual_source_conductor_error_identity p (by omega),
    actual_rational_coefficient_add, actual_rational_coefficient_add]
  exact precisionZero_add p 6 _ _
    (actual_first_angular_error_origin_precision p hp k)
    (precisionZero_add p 6 _ _
      (actual_first_conductor_error_origin_precision p hp k)
      (actual_angular_high_error_origin_precision p hp k))

end

end WPForcedSourceStokes
