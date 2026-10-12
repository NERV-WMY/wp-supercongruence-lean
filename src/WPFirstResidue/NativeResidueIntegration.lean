import WPFirstResidue.NativeResidue.LogarithmicHTransport
import WPFirstResidue.ConicCrossTransport
import WPFirstResidue.NativeCMCoordinate

open scoped Polynomial LaurentPolynomial LaurentSeries PowerSeries RatFunc
open Polynomial WPActualNativeHasse WPActualNativeJetODE WPActualConicInfinitySource
  WPFirstResidue.LaurentDifferential WPFirstResidue.CentralResidueAttachment
  WPFirstResidue.NativeCMCoordinate WPMomentPrecision.ConicCoordinates

namespace WPFirstResidue.NativeResidue

set_option maxHeartbeats 2000000

variable (p : ℕ) [Fact p.Prime]

/-- The full quotient derivative is evaluated at the global rational V(x),
whose denominator was proved nonzero without assuming a nonzero CM value. -/
theorem actual_native_ratio_differential (hp : 19 ≤ p) :
    nativeDerivation (nativeRatio p) =
      ((1 - nativeV p) ^ ((p - 1) / 2) / nativeFV p - 1) * nativeLogV p := by
  have hD : nativeDerivation (nativeRatio p) =
      ((nativeFV p * (nativeJetField p).derivative.eval₂ HahnSeries.C (nativeV p) -
        (nativeField p (p / 6)).derivative.eval₂ HahnSeries.C (nativeV p) * nativeJV p) /
        nativeFV p ^ 2) * nativeDerivation (nativeV p) := by
    have hJV : LaurentSeries.derivative (ZMod p) (nativeJV p) =
        (nativeJetField p).derivative.eval₂ HahnSeries.C (nativeV p) *
          LaurentSeries.derivative (ZMod p) (nativeV p) := by
      simpa only [nativeJV, nativeDerivation_apply] using
        polynomial_derivative_at p (nativeJetField p) (nativeV p)
    have hFV : LaurentSeries.derivative (ZMod p) (nativeFV p) =
        (nativeField p (p / 6)).derivative.eval₂ HahnSeries.C (nativeV p) *
          LaurentSeries.derivative (ZMod p) (nativeV p) := by
      simpa only [nativeFV, nativeDerivation_apply] using
        polynomial_derivative_at p (nativeField p (p / 6)) (nativeV p)
    rw [nativeDerivation_apply, nativeRatio, derivative_quotient, hJV, hFV]
    simp only [nativeDerivation_apply, div_eq_mul_inv]
    ring
  have hi := actual_native_first_ratio_differential_source p hp
    (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩) (nativeV p) (nativeDerivation (nativeV p))
    (nativeV_ne_zero p hp) (nativeFV_ne_zero p hp)
  change ((nativeFV p * (nativeJetField p).derivative.eval₂ HahnSeries.C (nativeV p) -
    (nativeField p (p / 6)).derivative.eval₂ HahnSeries.C (nativeV p) * nativeJV p) /
    nativeFV p ^ 2) * nativeDerivation (nativeV p) = _ at hi
  rw [nativeV_derivative p hp] at hi
  have hlog : nativeV p * nativeLogV p / nativeV p = nativeLogV p := by
    field_simp [nativeV_ne_zero p hp]
  rw [hlog] at hi
  rw [nativeV_derivative p hp] at hD
  exact hD.trans hi

/-- NC58 before extracting any coefficient: its first summand is exactly
the original cross density, including the complete native denominator. -/
theorem actual_native_C_density_source (hp : 19 ≤ p) :
    nativeHQ p * nativeDerivation (nativeRatio p) =
      WPFirstResidue.ConicCross.nativeCrossDensity p
        (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩) (originalX p) -
      nativeHQ p * nativeLogV p := by
  rw [actual_native_ratio_differential p hp]
  have hlog := logV_native_form (originalX p)
    (series_small_unit p hp 4 (by omega) (by omega)) (originalX_pole_units p).1
  unfold WPFirstResidue.ConicCross.nativeCrossDensity
  rw [← hlog]
  change nativeHQ p *
      (((1 - nativeV p) ^ ((p - 1) / 2) / nativeFV p - 1) * nativeLogV p) =
    nativeHQ p * (1 - nativeV p) ^ ((p - 1) / 2) / nativeFV p * nativeLogV p -
      nativeHQ p * nativeLogV p
  simp only [div_eq_mul_inv]
  ring

/-- The original cross residue is zero by the complete conic chart
transport. The logarithmic term retains both original endpoint zeros. -/
theorem actual_native_C_residue (hp : 19 ≤ p) : actualC p = -3 * nativeH0 p := by
  have hcross := WPFirstResidue.ConicCross.actual_native_cross_residue_zero p hp
  change (WPFirstResidue.ConicCross.nativeCrossDensity p
    (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩) (originalX p)).coeff (-1) = 0 at hcross
  have h := congrArg (fun s : (ZMod p)⸨X⸩ => s.coeff (-1))
    (actual_native_C_density_source p hp)
  rw [HahnSeries.coeff_sub, hcross, actual_native_HQ_dlogV_residue p hp] at h
  change actualC p = _ at h
  simpa only [zero_sub, neg_mul] using h

/-- Exact local integration of the actual full negative first lift. -/
theorem actual_Iu_logarithmic_reduction (hp : 19 ≤ p) :
    actualIu p = 3 * nativeH0 p + (nativeRatio p * nativeLogQ p).coeff (-1) := by
  rw [actual_Iu_integration_by_parts p hp, actual_native_C_residue p hp]
  ring

/-- The CM branch series represents the same global native V(x). -/
theorem actual_native_CM_V_attachment :
    ((nativeVSeries : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) = nativeV p := by
  rw [nativeVSeries_original_rational]
  simp only [V, map_div₀, map_mul, map_pow, map_sub, map_ofNat, map_one,
    RatFunc.coe_X, nativeV, originalX]

theorem actual_native_CM_ratio_attachment (hp : 19 ≤ p) :
    actualCMSeries p hp = nativeRatio p := by
  rw [actual_CM_native_ratio p hp, actual_native_CM_V_attachment]
  rfl

/-- The CM finite-part computation uses the original complete dlog Q;
its simple-pole coordinate correction is already contained in that source. -/
theorem actual_native_CM_log_attachment (hp : 19 ≤ p) :
    actualLogQSeries p = nativeLogQ p := by
  have h := nativeLogRegular_actual_laurent (actual_h2 p hp)
  change actualLogQSeries p = _ at h
  rw [nativeLogQ, logQ_native_form (originalX p)
    (series_small_unit p hp 4 (by omega) (by omega)) (originalX_pole_units p).1]
  simpa only [PowerSeries.coe_X, originalX] using h

theorem actual_native_ratio_logarithmic_residue (hp : 19 ≤ p) :
    (nativeRatio p * nativeLogQ p).coeff (-1) =
      6 * WPActualGaussBottom.fieldHarmonic p (p / 6) -
        9 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  rw [← actual_native_CM_ratio_attachment p hp, ← actual_native_CM_log_attachment p hp]
  exact actual_native_CM_logarithmic_residue p hp

theorem actual_Iu_native_value (hp : 19 ≤ p) :
    actualIu p = 3 * nativeH0 p +
      6 * WPActualGaussBottom.fieldHarmonic p (p / 6) -
        9 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  rw [actual_Iu_logarithmic_reduction p hp, actual_native_ratio_logarithmic_residue p hp]
  ring

/-- Original NC44/45/62 r0 attached before any p-division. This field
evaluation does not choose a replacement rational harmonic lift. -/
theorem actual_first_residue_native_value (hp : 19 ≤ p) :
    (WPFirstResidue.LiteralNormalization.actualFirstResidue p : ZMod p) =
      WPActualGaussBottom.fieldHarmonic p (p / 6) -
        (3 / 2 : ZMod p) * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  have h := actual_central_inverted_native_density p hp
  change (WPFirstResidue.LiteralNormalization.actualFirstResidue p : ZMod p) =
    (1 / 6 : ZMod p) * actualIu p - (1 / 2 : ZMod p) * nativeH0 p at h
  rw [actual_Iu_native_value p hp] at h
  have h2 : (2 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  calc
    _ = _ := h
    _ = _ := by field_simp [h2, h6]; ring

/-- The lift on the right is the exact integer-Fermat-quotient rational
R0, fixed before reduction, and not the rational harmonic representative. -/
theorem actual_first_residue_literal_field (hp : 19 ≤ p) :
    (WPFirstResidue.LiteralNormalization.actualFirstResidue p : ZMod p) =
      (WPFirstResidue.LiteralNormalization.literalR0 p : ZMod p) :=
  (actual_first_residue_native_value p hp).trans
    (WPFirstResidue.LiteralNormalization.harmonic_literalR0 p hp)

theorem actual_first_residue_literal_congruence (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 1
      (WPFirstResidue.LiteralNormalization.actualFirstResidue p)
      (WPFirstResidue.LiteralNormalization.literalR0 p) := by
  apply (WPPIntegralReduction.integral_residue_eq_iff p _ _
    (WPFirstResidue.LiteralNormalization.actualFirstResidue_integral p hp)
    (WPFirstResidue.LiteralNormalization.literalR0_integral p hp)).mp
  exact actual_first_residue_literal_field p hp

end WPFirstResidue.NativeResidue
