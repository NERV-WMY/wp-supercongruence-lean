import WPFieldAssembly.NativeJointSuccessorConicSeries
import WPFieldAssembly.NativeClosureLowHCollection
import WPFieldAssembly.NativeClosureLowHSource
import WPFieldAssembly.NativeJointSuccessorWneedCore
import WPFieldAssembly.ActualFiniteA2

open scoped BigOperators Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource WPFiniteLaurentDifferential

namespace WPFieldAssembly.NativeJointSuccessorMixedGreenCore

open ActualBpairContraction ActualGreenResidue ActualBpairLowHLocalPole
  NativeClosureMixedSource NativeJointSuccessorOddSource NativeJointSuccessorJSeries
  NativeJointSuccessorCBMixed NativeJointSuccessorWneedCore NativeClosureLowH

variable {K : Type*} [Field K]
set_option maxHeartbeats 2800000

/-- Quadratic descent of the original last odd coefficient gives the SAME finite quotient. -/
theorem actual_odd_quotient_polynomial (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    NativeQuadraticInverse.quadraticInverse (WPFiniteKSource.OP p : (ZMod p)[X]).divX =
      (oddReciprocalF p).comp (1 - X) := by
  have hOP : (WPFiniteKSource.OP p : (ZMod p)[X]) = X * (oddReciprocalF p).comp (X ^ 2) := by
    classical
    rw [ActualFiniteA2.OP_half_cutoff p hp, Finset.sum_Ico_eq_sum_range,
      oddReciprocalF, sum_comp, Finset.mul_sum]
    simp only [Nat.add_sub_cancel, mul_comp, C_comp, pow_comp, X_comp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show 2 * (1 + i) - 1 = 2 * i + 1 by omega, ← pow_mul, pow_succ]
    ring
  have h0 : (WPFiniteKSource.OP p : (ZMod p)[X]).coeff 0 = 0 := by
    rw [hOP]
    simp
  have hd : (WPFiniteKSource.OP p : (ZMod p)[X]).divX = (oddReciprocalF p).comp (X ^ 2) := by
    apply mul_left_cancel₀ (X_ne_zero : (X : (ZMod p)[X]) ≠ 0)
    rw [← hOP]
    simpa only [h0, map_zero, add_zero] using
      X_mul_divX_add (WPFiniteKSource.OP (K := ZMod p) p)
  rw [NativeQuadraticInverse.quadraticInverse, hd, ← expand_eq_comp_X_pow,
    contract_expand 2 (by norm_num : (2 : ℕ) ≠ 0)]

private theorem originalQ_odd_argument (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (1 - NativeScalarRows.originalQ : K[T;T⁻¹]) = oddReciprocalW := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : K) ≠ 0 := by
    convert pow_ne_zero 3 h5 using 1; norm_num
  have h25 : (25 : K) ≠ 0 := by
    convert pow_ne_zero 2 h5 using 1; norm_num
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent =
      LaurentPolynomial.C (1 / 5 : K) * (T 1 + 1) := by
    simp only [WPFiniteWSource.squaredCoordinate, map_mul, Polynomial.toLaurent_C,
      map_add, Polynomial.toLaurent_X, map_one, one_div]
  have ht : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  have ht3 : (T (-3) : K[T;T⁻¹]) = T (-1) ^ 3 := by rw [T_pow]; norm_num
  have hc : LaurentPolynomial.C ((125 : K)⁻¹) =
      LaurentPolynomial.C (((5 : K) ^ 2)⁻¹) * LaurentPolynomial.C (1 / 5 : K) := by
    rw [← map_mul]
    congr 1
    field_simp [h5, h25, h125]
    ring
  rw [NativeScalarRows.originalQ_factor, oddReciprocalW, hs, ht3, hc]
  have he : (1 - LaurentPolynomial.C ((125 : K)⁻¹) *
      ((4 * T (-1) - 1) ^ 2 * (4 - T (-1)) +
        (T 1 + 1) * T (-1) ^ 3 * (4 - 11 * T 1) ^ 2) : K[T;T⁻¹]) = 0 := by
    have hcinv : LaurentPolynomial.C ((125 : K)⁻¹) * 125 = (1 : K[T;T⁻¹]) := by
      change LaurentPolynomial.C ((125 : K)⁻¹) * LaurentPolynomial.C (125 : K) = 1
      rw [← map_mul, inv_mul_cancel₀ h125, map_one]
    linear_combination -hcinv -
      LaurentPolynomial.C ((125 : K)⁻¹) *
        (-72 * T (-1) ^ 2 + 33 * T (-1) * (T (-1) * T 1 + 1) +
          121 * ((T (-1) * T 1) ^ 2 + T (-1) * T 1 + 1)) * ht
  rw [hc] at he
  linear_combination he

/-- The NC83 odd quotient times the full native Q-log source is a literal Laurent product. -/
theorem actual_odd_quotient_weighted_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    coefficientMap (ActualThreePhase.φ (K := K) p)
        (substituteOver (NativeQuadraticInverse.quadraticInverse
          (WPFiniteKSource.OP p).divX) (NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹])) *
        lowHLinearYQLog (nativeH (K := K) p) =
      3 * (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent *
        T (-(((p - 1) / 2 : ℕ) : ℤ)) * oddReciprocalS p := by
  let f := ActualThreePhase.φ (K := K) p
  have harg := originalQ_odd_argument (K := ZMod p) p hp
  have ho : substituteOver (NativeQuadraticInverse.quadraticInverse
        (WPFiniteKSource.OP p).divX) (NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]) =
      (oddReciprocalF p).eval₂ LaurentPolynomial.C oddReciprocalW := by
    rw [actual_odd_quotient_polynomial p hp]
    change ((oddReciprocalF p).comp (1 - X)).eval₂ LaurentPolynomial.C _ = _
    rw [Polynomial.eval₂_comp]
    simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_X] using
      congrArg ((oddReciprocalF (K := ZMod p) p).eval₂ LaurentPolynomial.C) harg
  have hm := congrArg (coefficientMap f) ho
  have hn : coefficientMap f
      ((oddReciprocalF p : (ZMod p)[X]).eval₂ LaurentPolynomial.C oddReciprocalW) =
      (oddReciprocalF (K := K) p).eval₂ LaurentPolynomial.C oddReciprocalW := by
    classical
    unfold oddReciprocalF
    simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, map_sum, map_mul, map_pow,
      coefficientMap_C, map_inv₀, map_natCast, oddReciprocalW,
      coefficientMap_T, coefficientMap_toLaurent, WPFiniteWSource.squaredCoordinate,
      Polynomial.map_C, Polynomial.map_X, map_add, map_sub, map_one, map_ofNat]
  rw [hn] at hm
  have ht : (T (-(((p - 1) / 2 : ℕ) : ℤ)) *
      T (((p - 1) / 2 - 1 : ℕ) : ℤ) : K[T;T⁻¹]) = T (-1) := by
    rw [← T_add]
    congr 1
    omega
  have htx : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  rw [hm, native_qlog_density _ (nativeH_origin p), oddReciprocalS,
    oddReciprocalKernel_substitution]
  linear_combination
    -3 * (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent *
      (4 - 11 * T 1) * (oddReciprocalF p).eval₂ LaurentPolynomial.C oddReciprocalW * ht +
    33 * (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent *
      (oddReciprocalF p).eval₂ LaurentPolynomial.C oddReciprocalW * htx

/-- The exact original value j retains the full odd numerator and inclusive even bands. -/
theorem actual_J_value_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2) *
        actualJSeries (K := K) p =
      localFiniteSeriesHom (oddReciprocalS p) +
        localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2) *
        localFiniteSeriesHom (frobeniusPhi p) *
          localFiniteSeriesHom (mixedEvenSource p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) := by
  unfold actualJSeries mixedResidual
  simp only [map_add, map_mul, map_pow]
  field_simp [pow_ne_zero ((p - 1) / 2) (conicSeries_squared_ne_zero p hp)]

/-- Differentiation of the complete IR63b correction retains its j and reciprocal even products. -/
theorem actual_delta_series_product_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (D (actualDeltaCarrier p : K[T;T⁻¹])) =
      (2 / 5 : LaurentSeries K) * localFiniteSeriesHom (D (Dsym p)) * actualJSeries (K := K) p +
      (2 / 5 : LaurentSeries K) * localFiniteSeriesHom (Dsym p) *
        LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K) +
      (2 / 3 : LaurentSeries K) * localFiniteSeriesHom (D (Dstar p : K[X]).toLaurent) *
        localFiniteSeriesHom (invert (actualAK p : K[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) +
      (2 / 3 : LaurentSeries K) * localFiniteSeriesHom (Dstar p : K[X]).toLaurent *
        localFiniteSeriesHom (D (invert (actualAK p : K[X]).toLaurent)) := by
  have hd : (actualDeltaSeries (K := K) p : LaurentSeries K) =
      localFiniteSeriesHom (LaurentPolynomial.C (2 / 5 : K) * Dsym p) * actualJSeries (K := K) p +
        localFiniteSeriesHom (LaurentPolynomial.C (2 / 3 : K) * (Dstar p : K[X]).toLaurent) *
          localFiniteSeriesHom (invert (actualAK p : K[X]).toLaurent -
            LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) := by
    simp only [actualDeltaSeries, map_mul, localFiniteSeries_C, map_div₀, map_ofNat]
  have hdReciprocal : localFiniteSeriesHom
      (D (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (invert (actualAK p : K[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) : LaurentSeries K) :=
    lowHFiniteSeries_derivative (invert (actualAK p : K[X]).toLaurent -
      LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))
  rw [← actual_delta_derivative_Laurent p hp, hd, map_add,
    finite_series_derivative_product, finite_series_derivative_product,
    ← hdReciprocal]
  simp only [D_C_mul, map_sub, D_C, sub_zero, map_mul,
    localFiniteSeries_C, map_div₀, map_ofNat]
  ring

end WPFieldAssembly.NativeJointSuccessorMixedGreenCore
