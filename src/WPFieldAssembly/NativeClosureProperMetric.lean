import WPFieldAssembly.NativeClosureMetricEnds
import WPFieldAssembly.NativeClosureMetricCarrier
import WPFieldAssembly.ActualGreenPrimitive
import WPFieldAssembly.ActualEtaTransport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction
open WPFieldAssembly.ActualGreenPrimitive WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.ConicKernel WPFiniteJHighCoefficient WPFiniteCubicLog WPFiniteWSource

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

/-- The original proper metric numerator, with its complete p-1 power and actual PM. -/
noncomputable def properMetricNumerator (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (X + 1) ^ ((p - 1) / 2) * (4 - 11 * X) ^ (p - 1) *
    (4 * X - 11) * (11 * X ^ 2 + 4 * X + 8) *
    (quadraticInverse (ActualFirstGreen.M p).divX).comp
      (WPHasseIntegralTransport.fieldV p)

/-- This reduction occurs after the original integral metric was defined and divided. -/
theorem properMetricFactor_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (greenOriginMetricFactor p hp) =
      (1 / (250 * 5 ^ ((p - 1) / 2)) : ZMod p) := by
  have h5 : (5 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using
      WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h5p : (5 : ZMod p) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using ZMod.pow_card (5 : ZMod p)
  have h5m : (5 : ZMod p) ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ h5
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p), h5p, one_mul]
  have hn : (p - 1) / 2 + p - 1 = (p - 1) / 2 + (p - 1) := by omega
  simp only [greenOriginMetricFactor, map_mul, map_pow,
    WPActualRankTwoHatLift.smallIntegralInverse_field p 2 (by omega) (by omega),
    WPActualRankTwoHatLift.smallIntegralInverse_field p 5 (by omega) (by omega),
    Nat.cast_ofNat]
  rw [hn, pow_add]
  simp only [inv_pow, h5m, inv_one, mul_one]
  rw [show (250 : ZMod p) = 2 * 5 ^ 3 by norm_num]
  simp only [one_div, mul_inv_rev]
  ring

theorem properMetricNumerator_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (greenOriginMetricNumerator p hp).map (residueHom p) =
      properMetricNumerator p := by
  simp only [greenOriginMetricNumerator, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_ofNat,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_comp,
    greenPMIntegral_field p hp, WPHasseIntegralTransport.integralV_map_field]
  rfl

/-- The original whole metric is a signed literal coefficient, without an assigned value. -/
theorem actual_proper_metric_coefficient (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (greenOriginMetricIntegral p hp) =
      -(1 / (250 * 5 ^ ((p - 1) / 2)) : ZMod p) *
        (properMetricNumerator p).coeff p := by
  rw [greenOriginMetricIntegral_field p hp, properMetricFactor_field p hp,
    properMetricNumerator_field p hp]

noncomputable def properMetricDensity (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (-(1 / (250 * 5 ^ ((p - 1) / 2)) : ZMod p)) *
    T (-((p + 1 : ℕ) : ℤ)) * (properMetricNumerator p).toLaurent

/-- The retained high origin phase gives the original metric residue. -/
theorem actual_proper_metric_origin_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (greenOriginMetricIntegral p hp) =
      (properMetricDensity p).coeff (-1) := by
  rw [actual_proper_metric_coefficient p hp, properMetricDensity]
  have hs := WPFiniteJCarrier.shifted_coeff
    (-(1 / (250 * 5 ^ ((p - 1) / 2)) : ZMod p))
    (-((p + 1 : ℕ) : ℤ)) (-1) (properMetricNumerator p).toLaurent
  rw [show (-1 : ℤ) - -((p + 1 : ℕ) : ℤ) = (p : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat] at hs
  exact hs.symm

/-- The integral proper metric reaches the native field through its same full density. -/
theorem actual_proper_metric_coefficientMap_source {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (g : ZMod p →+* K) :
    g (residueHom p (greenOriginMetricIntegral p hp)) =
      (WPActualChiSource.coefficientMap g (properMetricDensity p)).coeff (-1) := by
  rw [WPActualChiSource.coefficientMap_coeff, actual_proper_metric_origin_source p hp]

end WPFieldAssembly.ActualBpairContraction
