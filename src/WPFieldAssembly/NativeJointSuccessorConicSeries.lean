import WPFieldAssembly.NativeJointSuccessorCMPrimitive
import WPFieldAssembly.NativeClosureJointConic
import WPFieldAssembly.NativeClosureProperMetricGreen
import WPFieldAssembly.NativeJointSuccessorOddSource
import WPFieldAssembly.NativeJointSuccessorJSeries
import WPFieldAssembly.SourceClosureHFBranchFactor

open scoped BigOperators Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource WPFiniteLaurentDifferential

namespace WPFieldAssembly.NativeJointSuccessorMixedGreenCore

open ActualBpairContraction ActualGreenResidue ActualBpairLowHLocalPole
  NativeClosureMixedSource NativeJointSuccessorOddSource NativeJointSuccessorJSeries
  NativeJointSuccessorCBMixed NativeJointSuccessorRroot SourceClosureHFNativeTransport

variable {K : Type*} [Field K]
set_option maxHeartbeats 2800000

/- The half-scale CMK is retained throughout. The reflected Sigma, full j
derivative and original proper metric are collected before a residue. The
three nonunit conic slots are supplied by their actual joint polynomial.
The remaining H and end/branch terms are explicit sources, with no assigned
remaining-collector value and no second conversion of the chi0 origin. -/

noncomputable def actualCgreen (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  LaurentPolynomial.C (2 / 3 : K) * (CMK (K := K) p).toLaurent +
    LaurentPolynomial.C (2 / 5 : K) * (HpullK (K := K) p).toLaurent * Dsym p

noncomputable def actualPC (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  (actualGreenPC p).map (ActualThreePhase.φ p)

noncomputable def actualZlogSeries : LaurentSeries K :=
  localFiniteSeriesHom (nativeZlogNumerator : K[T;T⁻¹]) /
    localFiniteSeriesHom (nativeZlogDenominator : K[T;T⁻¹])

noncomputable def actualBnewSeries (p : ℕ) [Fact p.Prime] [CharP K p] : LaurentSeries K :=
  localFiniteSeriesHom (actualIR63B0 p : K[T;T⁻¹]) + actualDeltaBSeries (K := K) p

/-- The IR66h correction is an entire Laurent density with the original origin term. -/
noncomputable def actualHCorrection (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  LaurentPolynomial.C (2 / 5 : K) * (WPFiniteZSource.Abar : K[X]).toLaurent *
    (HpullK (K := K) p).toLaurent * frobeniusPhi p * Dsym p *
      (LaurentPolynomial.C (1 / 2 : K) * T (-1) +
        LaurentPolynomial.C (1 / 3 : K) * D (actualAK p : K[X]).toLaurent)

theorem conicSeries_finite_injective :
    Function.Injective (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) := by
  intro F G h
  ext j
  exact congrArg (fun Q : LaurentSeries K => Q.coeff j) h

private theorem Abar_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent ≠ 0 := by
  intro hz
  exact WPFiniteZSource.Abar_nonzero p hp
    (conicSeries_finite_injective (hz.trans (map_zero _).symm))

theorem conicSeries_squared_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ≠ 0 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  intro hz
  have hL : (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent = 0 :=
    conicSeries_finite_injective (hz.trans (map_zero _).symm)
  have hP : (WPFiniteWSource.squaredCoordinate : K[X]) = 0 :=
    Polynomial.toLaurent_injective (hL.trans (map_zero _).symm)
  have hc := congrArg (fun P : K[X] => P.coeff 1) hP
  have he : (WPFiniteWSource.squaredCoordinate : K[X]).coeff 1 = (5 : K)⁻¹ := by
    simp [WPFiniteWSource.squaredCoordinate, Polynomial.coeff_one]
  rw [he, Polynomial.coeff_zero] at hc
  exact inv_ne_zero h5 hc

theorem conicSeries_zlog_denominator_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (nativeZlogDenominator : K[T;T⁻¹]) ≠ 0 := by
  intro hz
  exact nativeZlogDenominator_ne_zero p hp
    (conicSeries_finite_injective (hz.trans (map_zero _).symm))

private theorem Dstar_natural {L : Type*} [Field L] (g : K →+* L) (p : ℕ) :
    (Dstar p : K[X]).map g = (Dstar p : L[X]) := by
  simp only [Dstar, WPFiniteWSource.deltaE, WPFiniteWSource.squaredCoordinate,
    Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_C,
    Polynomial.map_comp, Polynomial.map_sum, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_div₀, map_sub, map_one, map_ofNat, map_natCast,
    map_pow, map_mul, map_inv₀]

/-- The whole joint conic coefficient has its actual branch factor and half-scale CM. -/
theorem actual_Cgreen_factor (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    T (((p - 1) / 2 - 1 : ℕ) : ℤ) * (actualCgreen p : K[T;T⁻¹]) =
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
        (actualPC p).toLaurent := by
  have he := congrArg (coefficientMap (ActualThreePhase.φ (K := K) p))
    (actualGreenPC_factor p hp)
  simpa only [actualCgreen, actualPC, map_mul, map_add, map_pow, coefficientMap_C,
    coefficientMap_T, coefficientMap_toLaurent, CMK, HpullK, Dsym,
    coefficientMap_invert, Dstar_natural, WPFiniteWSource.squaredCoordinate,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_one, map_inv₀, map_div₀, map_ofNat, map_one] using he

/-- The full finite odd source produces all four conic phases before multiplication by PC. -/
theorem actual_odd_joint_shift (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    -T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) * (oddDensityCleared p : K[T;T⁻¹]) =
      LaurentPolynomial.C (3 / 10 : K) *
        (4 - 33 * T (-(p : ℤ)) + 72 * T (-2 * (p : ℤ)) -
          16 * T (-3 * (p : ℤ))) * T 2 := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  let Xp : K[T;T⁻¹] := T (-(p : ℤ))
  have hpN : 2 * N + 1 = p := by
    have h := WPFiniteWSource.half_exponent p hp
    dsimp [N]
    omega
  have hs : s ^ p = LaurentPolynomial.C (1 / 5 : K) * (T (p : ℤ) + 1) := by
    have h5 : (5 : K) ^ p = 5 := WPFiniteField.natCast_pow_char p 5
    have hTp : (T 1 : K[T;T⁻¹]) ^ p = T (p : ℤ) := by
      rw [T_pow]
      congr 1
      ring
    have h := show (WPFiniteWSource.squaredCoordinate : K[X]) ^ p =
        Polynomial.C (1 / 5 : K) * (Polynomial.X ^ p + 1) by
      rw [WPFiniteWSource.squaredCoordinate, mul_pow, ← map_pow, inv_pow, h5,
        add_pow_char, one_pow, one_div]
    simpa only [map_pow, map_mul, map_add, map_one, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X, hTp, s] using congrArg (fun P : K[X] => P.toLaurent) h
  have ht : (T (-((N - 1 : ℕ) : ℤ)) * T (-(N : ℤ)) : K[T;T⁻¹]) =
      T 2 * Xp := by
    dsimp only [Xp]
    rw [← T_add, ← T_add]
    congr 1
    omega
  have hu : (T (-((N - 1 : ℕ) : ℤ)) * T ((N + 1 : ℕ) : ℤ) : K[T;T⁻¹]) = T 2 := by
    rw [← T_add]
    congr 1
    omega
  have hx : (Xp * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    dsimp only [Xp]
    rw [← T_add, neg_add_cancel, T_zero]
  have hfirst : (T (-((N - 1 : ℕ) : ℤ)) * T (-(N : ℤ)) * s ^ p : K[T;T⁻¹]) =
      LaurentPolynomial.C (1 / 5 : K) * T 2 * (1 + Xp) := by
    rw [ht, hs]
    linear_combination LaurentPolynomial.C (1 / 5 : K) * T 2 * hx
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have hc : LaurentPolynomial.C (3 / 2 : K) * LaurentPolynomial.C (1 / 5 : K) =
      LaurentPolynomial.C (3 / 10 : K) := by
    rw [← map_mul]
    congr 1
    field_simp [h2, h5, h10]
    ring
  have h75 : LaurentPolynomial.C (75 / 2 : K) =
      LaurentPolynomial.C (3 / 10 : K) * 125 := by
    change LaurentPolynomial.C (75 / 2 : K) =
      LaurentPolynomial.C (3 / 10 : K) * LaurentPolynomial.C (125 : K)
    rw [← map_mul]
    congr 1
    field_simp [h2, h10]
    ring
  have hx2 : (Xp ^ 2 : K[T;T⁻¹]) = T (-2 * (p : ℤ)) := by
    dsimp only [Xp]
    rw [T_pow]
    congr 1
    norm_num
  have hx3 : (Xp ^ 3 : K[T;T⁻¹]) = T (-3 * (p : ℤ)) := by
    dsimp only [Xp]
    rw [T_pow]
    congr 1
    norm_num
  have hpoly : (125 - (1 + Xp) * (4 * Xp - 11) ^ 2 : K[T;T⁻¹]) =
      4 - 33 * Xp + 72 * T (-2 * (p : ℤ)) - 16 * T (-3 * (p : ℤ)) := by
    rw [← hx2, ← hx3]
    ring
  unfold oddDensityCleared
  change -T (-((N - 1 : ℕ) : ℤ)) *
    (LaurentPolynomial.C (3 / 2 : K) * T (-(N : ℤ)) * s ^ (2 * N + 1) *
      (4 * Xp - 11) ^ 2 - LaurentPolynomial.C (75 / 2 : K) * T ((N + 1 : ℕ) : ℤ)) = _
  rw [hpN, h75]
  calc
    _ = -LaurentPolynomial.C (3 / 2 : K) *
        (T (-((N - 1 : ℕ) : ℤ)) * T (-(N : ℤ)) * s ^ p) * (4 * Xp - 11) ^ 2 +
      LaurentPolynomial.C (3 / 10 : K) * 125 *
        (T (-((N - 1 : ℕ) : ℤ)) * T ((N + 1 : ℕ) : ℤ)) := by ring
    _ = LaurentPolynomial.C (3 / 10 : K) *
        (125 - (1 + Xp) * (4 * Xp - 11) ^ 2) * T 2 := by
      rw [hfirst, hu]
      linear_combination -T 2 * (1 + Xp) * (4 * Xp - 11) ^ 2 * hc
    _ = _ := by rw [hpoly]

/-- The combined CM/H odd differential is the actual three-slot conic density. -/
theorem actual_joint_conic_series_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    -localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (actualCgreen p) * actualOddSeries (K := K) p =
      localFiniteSeriesHom (threePhaseConicDensity p (actualPC (K := K) p)) := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  have hf : (actualCgreen p : K[T;T⁻¹]) =
      T (-((N - 1 : ℕ) : ℤ)) * s ^ (N + 1) * (actualPC p).toLaurent := by
    have h := actual_Cgreen_factor (K := K) p hp
    have ht : (T (-((N - 1 : ℕ) : ℤ)) * T ((N - 1 : ℕ) : ℤ) : K[T;T⁻¹]) = 1 := by
      rw [← T_add, neg_add_cancel, T_zero]
    change T ((N - 1 : ℕ) : ℤ) * actualCgreen p = s ^ (N + 1) * (actualPC p).toLaurent at h
    linear_combination T (-((N - 1 : ℕ) : ℤ)) * h - actualCgreen p * ht
  have hc : -(actualCgreen p : K[T;T⁻¹]) * oddDensityCleared p =
      s ^ (N + 1) * threePhaseConicDensity p (actualPC p) := by
    rw [hf]
    have he := actual_odd_joint_shift (K := K) p hp
    change -T (-((N - 1 : ℕ) : ℤ)) * oddDensityCleared p = _ at he
    unfold threePhaseConicDensity
    linear_combination s ^ (N + 1) * (actualPC p).toLaurent * he
  have he := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) hc
  simp only [map_neg, map_mul, map_pow] at he
  unfold actualOddSeries
  field_simp [Abar_series_ne_zero p hp, conicSeries_squared_ne_zero p hp,
    pow_ne_zero (N + 1) (conicSeries_squared_ne_zero p hp)]
  linear_combination he

private theorem series_X_inverse :
    localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) =
      (localFiniteSeriesHom (T 1 : K[T;T⁻¹]))⁻¹ := by
  have ht : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  have hx : localFiniteSeriesHom (T 1 : K[T;T⁻¹]) ≠ 0 := by
    intro hz
    have h := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) ht
    rw [map_mul, hz, mul_zero, map_one] at h
    exact zero_ne_one h
  apply mul_right_cancel₀ hx
  rw [inv_mul_cancel₀ hx]
  simpa only [map_mul, map_one] using congrArg localFiniteSeriesHom ht

/-- The actual inverse logarithm is dlog(Tvee)+dx/(2x), with the origin term retained. -/
theorem actual_Zlog_series (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualZlogSeries (K := K) : LaurentSeries K) = actualLogSeries (K := K) +
      (1 / 2 : LaurentSeries K) * localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) := by
  let x := localFiniteSeriesHom (T 1 : K[T;T⁻¹])
  have hden := conicSeries_zlog_denominator_ne_zero (K := K) p hp
  have hx2 : localFiniteSeriesHom (T 2 : K[T;T⁻¹]) = x ^ 2 := by
    rw [← map_pow, T_pow]
    congr 1
  have hs : localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent =
      (1 / 5 : LaurentSeries K) * (x + 1) := by
    simp only [WPFiniteWSource.squaredCoordinate, map_mul, Polynomial.toLaurent_C,
      map_add, Polynomial.toLaurent_X, map_one, localFiniteSeries_C,
      map_inv₀, map_ofNat, one_div, x]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h2S : (2 : LaurentSeries K) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using
      (algebraMap K (LaurentSeries K)).injective.ne h2
  have h5S : (5 : LaurentSeries K) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using
      (algebraMap K (LaurentSeries K)).injective.ne h5
  have h10S : (10 : LaurentSeries K) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using
      (algebraMap K (LaurentSeries K)).injective.ne h10
  simp only [nativeZlogDenominator, map_mul, map_add, map_sub, map_ofNat, map_one] at hden
  change 2 * x * (x + 1) * (4 - 11 * x) ≠ 0 at hden
  have hw := (mul_ne_zero_iff.mp hden).2
  have hx1 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hden).1).2
  have hx := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hden).1).1).2
  unfold actualZlogSeries actualLogSeries
  simp only [nativeZlogNumerator, nativeZlogDenominator, oddLogCleared,
    map_add, map_sub, map_mul, map_neg, map_ofNat, map_one,
    localFiniteSeries_C, map_div₀, hx2, hs, series_X_inverse]
  change (-11 * x ^ 2 - 4 * x - 8) / (2 * x * (x + 1) * (4 - 11 * x)) =
    ((3 / 10 : LaurentSeries K) * x⁻¹ * (x - 4)) /
      ((1 / 5 : LaurentSeries K) * (x + 1) * (4 - 11 * x)) + (1 / 2) * x⁻¹
  field_simp [h2S, h5S, h10S, hx, hx1, hw]
  ring

/-- The original proper metric is exactly 2*CMK*phi*dlogZvee as a whole source. -/
theorem actual_properMetric_series_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (coefficientMap (ActualThreePhase.φ (K := K) p)
      (properMetricDensity p)) =
      2 * localFiniteSeriesHom (CMK (K := K) p).toLaurent *
        localFiniteSeriesHom (frobeniusPhi p) * actualZlogSeries (K := K) := by
  have hx2 : (T 1 : K[T;T⁻¹]) ^ 2 = T 2 := by rw [T_pow]; norm_num
  have h := properMetric_native_cleared_source (K := K) p hp
  have he : nativeZlogDenominator *
      coefficientMap (ActualThreePhase.φ (K := K) p) (properMetricDensity p) =
      2 * (CMK (K := K) p).toLaurent * frobeniusPhi p * nativeZlogNumerator := by
    unfold nativeZlogDenominator nativeZlogNumerator frobeniusPhi
    rw [← hx2]
    linear_combination 2 * h
  have hs := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) he
  simp only [map_mul, map_ofNat] at hs
  unfold actualZlogSeries
  calc
    _ = (2 * localFiniteSeriesHom (CMK (K := K) p).toLaurent *
        localFiniteSeriesHom (frobeniusPhi p) * localFiniteSeriesHom nativeZlogNumerator) /
          localFiniteSeriesHom nativeZlogDenominator := by
      apply (eq_div_iff (conicSeries_zlog_denominator_ne_zero p hp)).mpr
      linear_combination hs
    _ = _ := by ring


end WPFieldAssembly.NativeJointSuccessorMixedGreenCore
