import WPFieldAssembly.NativeClosureProperMetric
import WPFieldAssembly.ActualSimplePoleResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction WPFiniteWSource
open WPFieldAssembly.NativeQuadraticInverse

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

/-- The original added-point phase is the complete p-th power before any cancellation. -/
theorem properMetric_frobenius_phase (p : ℕ) [Fact p.Prime] :
    (4 - 11 * T 1 : (ZMod p)[T;T⁻¹]) ^ p * T (-(p : ℤ)) =
      4 * T (-(p : ℤ)) - 11 := by
  have ht : (T (p : ℤ) * T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have ht1 : (T 1 : (ZMod p)[T;T⁻¹]) ^ p = T (p : ℤ) := by
    rw [T_pow]
    congr 1
    ring
  have heP : (4 - 11 * X : (ZMod p)[X]) ^ p = 4 - 11 * X ^ p := by
    have hc (c : ZMod p) : (Polynomial.C c : (ZMod p)[X]) ^ p =
        Polynomial.C c := by
      rw [← map_pow, ZMod.pow_card]
    change (Polynomial.C (4 : ZMod p) - Polynomial.C (11 : ZMod p) * X) ^ p =
      Polynomial.C (4 : ZMod p) - Polynomial.C (11 : ZMod p) * X ^ p
    rw [sub_pow_char, mul_pow, hc, hc]
  have he : (4 - 11 * T 1 : (ZMod p)[T;T⁻¹]) ^ p = 4 - 11 * T (p : ℤ) := by
    have h := congrArg (fun P : (ZMod p)[X] => P.toLaurent) heP
    simpa only [map_pow, map_sub, map_mul, map_ofNat, Polynomial.toLaurent_X, ht1] using h
  rw [he, sub_mul, mul_assoc, ht, mul_one]

/-- The original full metric and CM source match after clearing the logarithmic denominator.
The density is 2*CM*dlogZvee times its original Frobenius phase. -/
theorem properMetric_CM_cleared_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (T 1 * (T 1 + 1) * (4 - 11 * T 1) : (ZMod p)[T;T⁻¹]) *
        properMetricDensity p =
      -(ActualFirstGreen.CM p).toLaurent * (4 * T (-(p : ℤ)) - 11) *
        (11 * T 1 ^ 2 + 4 * T 1 + 8) := by
  let n := (p - 1) / 2
  let U : (ZMod p)[T;T⁻¹] := T 1 + 1
  let V : (ZMod p)[T;T⁻¹] := 4 - 11 * T 1
  let W : (ZMod p)[T;T⁻¹] := 4 * T 1 - 11
  let B : (ZMod p)[T;T⁻¹] := 11 * T 1 ^ 2 + 4 * T 1 + 8
  let M : (ZMod p)[T;T⁻¹] :=
    ((quadraticInverse (ActualFirstGreen.M p).divX).comp
      (WPHasseIntegralTransport.fieldV p)).toLaurent
  let a : ZMod p := 1 / (250 * 5 ^ n)
  have ha : (1 / 50 : ZMod p) * (5 : ZMod p)⁻¹ ^ (n + 1) = a := by
    dsimp only [a]
    rw [show (250 : ZMod p) = 50 * 5 by norm_num]
    simp only [one_div, mul_inv_rev, inv_pow, pow_succ]
    ring
  have hm : (ActualFirstGreen.CM p).toLaurent =
      LaurentPolynomial.C a * U ^ (n + 1) * W * M := by
    rw [actual_CM_PM_source p hp]
    simp only [squaredCoordinate, map_mul, map_pow, map_add,
      map_sub, map_one, map_ofNat, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
    dsimp only [U, W, M, n]
    rw [mul_pow, ← map_pow]
    calc
      _ = (LaurentPolynomial.C (1 / 50 : ZMod p) *
          LaurentPolynomial.C ((5 : ZMod p)⁻¹ ^ ((p - 1) / 2 + 1))) *
          (T 1 + 1) ^ ((p - 1) / 2 + 1) * (4 * T 1 - 11) *
          ((quadraticInverse (ActualFirstGreen.M p).divX).comp
            (WPHasseIntegralTransport.fieldV p)).toLaurent := by ring
      _ = _ := by rw [← map_mul, ha]
  have hr : properMetricDensity p =
      -LaurentPolynomial.C a * T (-((p + 1 : ℕ) : ℤ)) *
        U ^ n * V ^ (p - 1) * W * B * M := by
    simp only [properMetricDensity, properMetricNumerator, map_mul, map_pow,
      map_add, map_sub, map_one, map_ofNat, Polynomial.toLaurent_X, map_neg]
    dsimp only [a, U, V, W, B, M, n]
    ring
  have ht : (T 1 * T (-((p + 1 : ℕ) : ℤ)) : (ZMod p)[T;T⁻¹]) =
      T (-(p : ℤ)) := by
    rw [← T_add]
    congr 1
    omega
  have hv : V ^ p = V ^ (p - 1) * V := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  rw [hr, hm, ← properMetric_frobenius_phase p]
  change (T 1 * U * V) *
      (-LaurentPolynomial.C a * T (-((p + 1 : ℕ) : ℤ)) *
        U ^ n * V ^ (p - 1) * W * B * M) =
    -(LaurentPolynomial.C a * U ^ (n + 1) * W * M) *
      (V ^ p * T (-(p : ℤ))) * B
  rw [hv, pow_succ]
  linear_combination
    -(LaurentPolynomial.C a * U ^ n * U * V ^ (p - 1) * V * W * B * M) * ht

/-- Clearing the original proper metric commutes with the faithful native transport.
The actual CMK remains half the hand metric; the whole reciprocal phase is retained. -/
theorem properMetric_native_cleared_source {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (T 1 * (T 1 + 1) * (4 - 11 * T 1) : K[T;T⁻¹]) *
        WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
          (properMetricDensity p) =
      -(ActualGreenResidue.CMK (K := K) p).toLaurent *
        (4 * T (-(p : ℤ)) - 11) * (11 * T 1 ^ 2 + 4 * T 1 + 8) := by
  have h := congrArg
    (WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p))
    (properMetric_CM_cleared_source p hp)
  simpa only [map_mul, map_add, map_sub, map_neg, map_pow, map_one, map_ofNat,
    WPActualChiSource.coefficientMap_T, WPActualChiSource.coefficientMap_toLaurent,
    ActualGreenResidue.CMK] using h

/-- The whole proper-pole functional, including every negative phase, is natural in the field. -/
theorem metric_originPole_coefficientMap {R K : Type*} [Field R] [Field K]
    (g : R →+* K) (F : R[T;T⁻¹]) :
    WPFieldAssembly.ActualSimplePoleResidue.originPole
        (WPActualChiSource.coefficientMap g F) =
      g (WPFieldAssembly.ActualSimplePoleResidue.originPole F) := by
  simp only [WPFieldAssembly.ActualSimplePoleResidue.originPole, map_div₀, map_ofNat,
    ← WPActualChiSource.coefficientMap_coeff, map_sub,
    WPFieldAssembly.GreenLaurentOperators.DD_map, map_one]

/-- The actual integral proper metric is the same native proper-pole contribution.
Its coefficient is retained rather than separately assigned a value. -/
theorem actual_proper_metric_native_origin {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFieldAssembly.ActualSimplePoleResidue.originPole
      ((WPFiniteZSource.Abar : K[X]).toLaurent *
        WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
          (properMetricDensity p)) =
      ActualThreePhase.φ (K := K) p
        (WPPIntegralReduction.residueHom p
          (ActualGreenPrimitive.greenOriginMetricIntegral p hp)) := by
  rw [WPFieldAssembly.ActualSimplePoleResidue.originPole_cleared p hp]
  exact (actual_proper_metric_coefficientMap_source p hp
    (ActualThreePhase.φ (K := K) p)).symm

end WPFieldAssembly.ActualBpairContraction
