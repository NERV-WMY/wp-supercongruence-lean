import WPFieldAssembly.NativeClosureLowHReduction

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.ActualBpairContraction WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualBpairLowHLocalPole

namespace WPFieldAssembly.NativeClosureLowH
variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The actual Dstar derivative is kept with the full finite half-Frobenius source. -/
theorem native_dstar_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    (lowHCubicY H).toLaurent * D (Dstar p : K[X]).toLaurent =
      LaurentPolynomial.C (5 / 2 : K) *
        (1 - WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) *
          (lowHBranchYQuotient H).toLaurent := by
  have h := congrArg (fun P : K[X] => P.toLaurent)
    (Dstar_cleared_source (K := K) p hp)
  simp only [map_mul, map_sub, map_pow, map_one, Polynomial.toLaurent_C,
    ← D_toLaurent] at h
  rw [lowHBranchYQuotient_source H h0, map_mul]
  linear_combination (lowHBranchYQuotient H).toLaurent * h

/-- The positive native source keeps its whole branch band after the
logarithmic density is collected. -/
theorem native_u_shifted_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    2 * ((lowHCubicY H).toLaurent * D (actualAK (K := K) p).toLaurent) +
        (lowHqCubicDensity H).toLaurent =
      -3 * (4 * T (p : ℤ) - 11) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (lowHBranchYQuotient H).toLaurent := by
  have hA := actual_AK_cleared_derivative (K := K) p hp
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hhalf : (2 : K[T;T⁻¹]) * LaurentPolynomial.C (3 / 2 : K) = 3 := by
    change LaurentPolynomial.C (2 : K) * LaurentPolynomial.C (3 / 2 : K) =
      LaurentPolynomial.C (3 : K)
    rw [← map_mul]
    congr 1
    field_simp [h2]
  rw [lowHBranchYQuotient_source H h0, map_mul, lowH_linear_ylog_polynomial]
  simp only [map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X]
  linear_combination 2 * (lowHBranchYQuotient H).toLaurent * hA +
    (lowHBranchYQuotient H).toLaurent *
      ((4 * T 1 - 11) -
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (4 * T (p : ℤ) - 11)) * hhalf

/-- The genuine P derivative retains its origin pole and both Frobenius phases. -/
theorem native_P_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (H : K[X]) (h0 : H.coeff 0 = 0) :
    (lowHCubicY H).toLaurent * D (WPFiniteZSource.P p η) =
      LaurentPolynomial.C (1 / 2 : K) *
        (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ))) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (lowHBranchYQuotient H).toLaurent -
      LaurentPolynomial.C (1 / 2 : K) * lowHLinearYOverX H := by
  have hR := WPFiniteZSource.R_cleared (K := K) p hp
  dsimp only [WPFiniteZSource.phase] at hR
  rw [WPFiniteZSource.P_derivative p hp η,
    lowHBranchYQuotient_source H h0, map_mul]
  simp only [lowHLinearYOverX, lowHBranchYQuotient_source H h0, map_mul]
  linear_combination (lowHBranchYQuotient H).toLaurent * hR

/-- Complete inversion transports the actual Dstar source, including the reciprocal band. -/
theorem native_reciprocal_dstar_cleared (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (invert (Dstar p : K[X]).toLaurent) =
      LaurentPolynomial.C (5 / 2 : K) *
        (T (-(((p - 1) / 2 : ℕ) : ℤ)) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) - 1) := by
  have hsource := congrArg (fun P : K[X] => P.toLaurent)
    (Dstar_cleared_source (K := K) p hp)
  simp only [map_mul, map_sub, map_pow, map_one, Polynomial.toLaurent_C,
    ← D_toLaurent] at hsource
  have h := congrArg invert hsource
  simp only [map_mul, map_sub, map_one, invert_C,
    WPFiniteZSource.invert_Abar, WPFiniteZSource.invert_squared_power] at h
  rw [D_invert]
  linear_combination -h

/-- Both reciprocal derivatives are identified from the original positive source. -/
theorem native_v_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    (lowHCubicY H).toLaurent * D (invert (actualAK (K := K) p).toLaurent) =
      LaurentPolynomial.C (3 / 5 : K) * (4 * T (-(p : ℤ)) - 11) *
        ((lowHCubicY H).toLaurent * D (invert (Dstar p : K[X]).toLaurent)) -
      LaurentPolynomial.C (1 / 2 : K) * lowHLinearYQLog H +
      LaurentPolynomial.C (3 / 2 : K) * (4 * T (-(p : ℤ)) - 11) *
        (lowHBranchYQuotient H).toLaurent := by
  have hA := native_v_cleared_derivative (K := K) p hp
  have hD := native_reciprocal_dstar_cleared (K := K) p hp
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc : (3 / 5 : K) * (5 / 2) = 3 / 2 := by field_simp [h5]
  have hcL := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
  simp only [map_mul] at hcL
  have hhalf : LaurentPolynomial.C (1 / 2 : K) * 3 =
      LaurentPolynomial.C (3 / 2 : K) := by
    change LaurentPolynomial.C (1 / 2 : K) * LaurentPolynomial.C (3 : K) = _
    rw [← map_mul]; congr 1; ring
  rw [lowHBranchYQuotient_source H h0, map_mul, native_qlog_density H h0]
  linear_combination (lowHBranchYQuotient H).toLaurent * hA -
    LaurentPolynomial.C (3 / 5 : K) * (4 * T (-(p : ℤ)) - 11) *
      (lowHBranchYQuotient H).toLaurent * hD -
    (4 * T (-(p : ℤ)) - 11) * (lowHBranchYQuotient H).toLaurent *
      (T (-(((p - 1) / 2 : ℕ) : ℤ)) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) - 1) * hcL +
    (4 * T (-1) - 11) * (lowHBranchYQuotient H).toLaurent * hhalf

/-- Differentiation preserves the exact original P-minus-Dstar identity. -/
theorem native_P_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (hη : η ^ 2 = 1 / 5) :
    D (WPFiniteZSource.P p η) - D (Dstar p : K[X]).toLaurent =
      LaurentPolynomial.C (1 / 3 : K) *
        (D (actualAK (K := K) p).toLaurent - D (invert (actualAK (K := K) p).toLaurent)) +
      LaurentPolynomial.C (1 / 5 : K) * (4 * T (-(p : ℤ)) - 11) *
        (D (Dstar p : K[X]).toLaurent + D (invert (Dstar p : K[X]).toLaurent)) := by
  have h := congrArg D (actual_P_minus_Dstar (K := K) p hp η hη)
  have hphase : D (4 * T (-(p : ℤ)) - 11 : K[T;T⁻¹]) = 0 := by
    have ht := D_frobenius_shift p (1 : K[T;T⁻¹]) (-(p : ℤ))
      (dvd_neg.mpr (dvd_refl _))
    have h1 : D (1 : K[T;T⁻¹]) = 0 := by simpa only [map_one] using D_C (1 : K)
    simp only [mul_one, h1, mul_zero] at ht
    change D (LaurentPolynomial.C (4 : K) * T (-(p : ℤ)) -
      LaurentPolynomial.C (11 : K)) = 0
    rw [map_sub, D_C_mul, ht, D_C, mul_zero, sub_self]
  simpa only [map_sub, map_add, D_C_mul, D_mul, D_C, hphase,
    zero_mul, mul_zero, zero_add] using h

/-- P and its true reciprocal retain all source halves and the same native carrier. -/
theorem native_P_reciprocal (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (hη : η ^ 2 = 1 / 5) :
    invert (WPFiniteZSource.P p η) - invert (Dstar p : K[X]).toLaurent =
      LaurentPolynomial.C (1 / 3 : K) *
        (invert (actualAK (K := K) p).toLaurent - (actualAK (K := K) p).toLaurent) +
      LaurentPolynomial.C (1 / 5 : K) * (4 * T (p : ℤ) - 11) *
        ((Dstar p : K[X]).toLaurent + invert (Dstar p : K[X]).toLaurent) := by
  have h := congrArg invert (actual_P_minus_Dstar (K := K) p hp η hη)
  simp only [map_sub, map_mul, map_add, map_ofNat, invert_C, invert_T,
    neg_neg] at h
  rw [involutive_invert, involutive_invert] at h
  convert h using 1; ring

theorem original_Cslot_field {F : Type*} [Field F]
    (h3 : (3 : F) ≠ 0) (h5 : (5 : F) ≠ 0)
    (Xp u v P Ds Dv A B κ q2 : F)
    (hP : P - Ds = (u - v) / 3 + (4 * Xp - 11) * (Ds + Dv) / 5)
    (hV : v = 3 * (4 * Xp - 11) * Dv / 5 +
      2 * Xp * (A - B) / 5 + κ - 4 * q2 * Xp / 5) :
    P - u / 3 = (4 * Xp - 6) * Ds / 5 -
      2 * Xp * (A - B) / 15 + 4 * q2 * Xp / 15 - κ / 3 := by
  have h15 : (15 : F) ≠ 0 := by convert mul_ne_zero h3 h5 using 1; ring
  rw [hV] at hP
  linear_combination (norm := (field_simp [h3, h5, h15]; ring)) hP

/-- The kernel Cslot belongs to the genuine native carrier, including its origin. -/
theorem native_Cslot (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (hη : η ^ 2 = 1 / 5) :
    WPFiniteZSource.P p η - LaurentPolynomial.C (1 / 3 : K) *
      (actualAK (K := K) p).toLaurent =
      lowHWholeCslot p (ActualCubicNativeSource.nativeConstant p) (WPFiniteNC122.q p) := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h3S : (3 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (3 : K) ≠ 0
    exact HahnSeries.C_ne_zero h3
  have h5S : (5 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (5 : K) ≠ 0
    exact HahnSeries.C_ne_zero h5
  have hP := congrArg localFiniteSeriesHom (actual_P_minus_Dstar (K := K) p hp η hη)
  have hV := congrArg localFiniteSeriesHom (native_v_affine (K := K) p hp)
  simp only [map_mul, map_add, map_sub, map_ofNat, localFiniteSeries_C,
    map_div₀, map_one] at hP hV
  have he := original_Cslot_field h3S h5S
    (localFiniteSeriesHom (T (-(p : ℤ))))
    (localFiniteSeriesHom (actualAK (K := K) p).toLaurent)
    (localFiniteSeriesHom (invert (actualAK (K := K) p).toLaurent))
    (localFiniteSeriesHom (WPFiniteZSource.P p η))
    (localFiniteSeriesHom (Dstar p : K[X]).toLaurent)
    (localFiniteSeriesHom (invert (Dstar p : K[X]).toLaurent))
    (localFiniteSeriesHom (lowHLog p 4).toLaurent)
    (localFiniteSeriesHom (lowHLog p (1 / 4)).toLaurent)
    (algebraMap K (LaurentSeries K) (ActualCubicNativeSource.nativeConstant p))
    (algebraMap K (LaurentSeries K) (WPFiniteNC122.q p))
    (by convert hP using 1; ring) (by convert hV using 1; ring)
  apply lowH_whole_finiteSeries_injective
  simp only [lowHWholeCslot, map_mul, map_add, map_sub, map_ofNat,
    localFiniteSeries_C, map_div₀, map_one]
  convert he using 1 <;> ring

/-- The original IR64d source with its IR66h correction, before any lowH reduction. -/
noncomputable def nativeOriginalHSource (p : ℕ) [Fact p.Prime] [CharP K p]
    (η : K) (H : K[X]) (KB DK : K[T;T⁻¹]) (h q2 : K) : K[T;T⁻¹] :=
  let G := T (p : ℤ)
  let Xp := T (-(p : ℤ))
  let Xn := T (((p - 1) / 2 : ℕ) : ℤ)
  let u := (actualAK (K := K) p).toLaurent
  let v := invert u
  let P := WPFiniteZSource.P p η
  let Pv := invert P
  let Ds := (Dstar p : K[X]).toLaurent
  let Dv := invert Ds
  let φ := 4 * Xp - 11
  let y := (lowHCubicY H).toLaurent
  let yl := (lowHqCubicDensity H).toLaurent
  let ylq := lowHLinearYQLog H
  let z := lowHLinearYOverX H
  let Q := (lowHBranchYQuotient H).toLaurent
  (P - LaurentPolynomial.C (1 / 3 : K) * u) * y * DK -
    LaurentPolynomial.C (5 / 6 : K) * KB * yl +
    (LaurentPolynomial.C (5 / 12 : K) * G *
      (v * (y * D u) + (u - (1 + Xn) * v) * (y * D v)) +
      LaurentPolynomial.C (5 / 24 : K) * G * (u * yl - Xn * v * ylq) -
      LaurentPolynomial.C (5 / 4 : K) * G *
        (v * (y * (D P - D Ds)) + (P - Ds) * (y * D v))) -
    LaurentPolynomial.C (5 / 3 : K) * (v - LaurentPolynomial.C (q2 - h)) * Q -
    LaurentPolynomial.C (2 / 3 : K) * (Ds + Pv) * (y * D v) +
    LaurentPolynomial.C (2 / 9 : K) *
      ((v + LaurentPolynomial.C h) - (1 + Xn) * (u + LaurentPolynomial.C h)) * (y * D v) -
    LaurentPolynomial.C (1 / 9 : K) * (u + Xn * (u + LaurentPolynomial.C h)) * ylq -
    LaurentPolynomial.C (1 / 3 : K) * Pv * ylq -
    LaurentPolynomial.C (2 / 5 : K) * φ * (Ds + Dv) *
      (LaurentPolynomial.C (1 / 2 : K) * z + LaurentPolynomial.C (1 / 3 : K) * (y * D u))

/-- The complete original native H source reduces to IR71d without a free native-u premise. -/
theorem native_original_H_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (hη : η ^ 2 = 1 / 5)
    (H : K[X]) (h0 : H.coeff 0 = 0) (KB DK : K[T;T⁻¹]) (h : K) :
    nativeOriginalHSource p η H KB DK h (WPFiniteNC122.q p) =
      lowHWholeOriginalKernelSource p H KB DK
        (ActualCubicNativeSource.nativeConstant p) h (WPFiniteNC122.q p) +
      LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) *
        (actualAK (K := K) p).toLaurent * (lowHqCubicDensity H).toLaurent := by
  let f : K[T;T⁻¹] →+* LaurentSeries K := localFiniteSeriesHom
  let y := (lowHCubicY H).toLaurent
  let u := (actualAK (K := K) p).toLaurent
  let v := invert u
  let P := WPFiniteZSource.P p η
  let Ds := (Dstar p : K[X]).toLaurent
  let Dv := invert Ds
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h2S : (2 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (2 : K) ≠ 0
    exact HahnSeries.C_ne_zero h2
  have h3S : (3 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (3 : K) ≠ 0
    exact HahnSeries.C_ne_zero h3
  have h5S : (5 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (5 : K) ≠ 0
    exact HahnSeries.C_ne_zero h5
  have hGX : f (T (p : ℤ)) * f (T (-(p : ℤ))) = 1 := by
    rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  have hP := congrArg f (actual_P_minus_Dstar (K := K) p hp η hη)
  have hPv := congrArg f (native_P_reciprocal (K := K) p hp η hη)
  have hDP := congrArg (fun R : K[T;T⁻¹] => f (y * R))
    (native_P_derivative (K := K) p hp η hη)
  have hU := congrArg f (native_u_density (K := K) p hp H h0)
  have hV := congrArg f (native_v_density (K := K) p hp H h0)
  have hXV := congrArg f (native_v_shifted_density (K := K) p hp H h0)
  have hD := congrArg f (native_dstar_density (K := K) p hp H h0)
  simp only [f, map_mul, map_add, map_sub, map_ofNat,
    localFiniteSeries_C, map_div₀, map_one] at hP hPv hDP hU hV hXV hD
  have he := original_H_source_reduction h2S h3S h5S
    (f (T (p : ℤ))) (f (T (-(p : ℤ))))
    (f (T (((p - 1) / 2 : ℕ) : ℤ)))
    (f (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)))
    (f u) (f v) (f P) (f (invert P)) (f Ds) (f Dv)
    (f (y * D u)) (f (y * D v)) (f (y * D P))
    (f (y * D Ds)) (f (y * D Dv))
    (f (lowHqCubicDensity H).toLaurent) (f (lowHLinearYQLog H))
    (f (lowHLinearYOverX H)) (f (lowHBranchYQuotient H).toLaurent)
    (f y) (f KB) (f DK)
    (algebraMap K (LaurentSeries K) h)
    (algebraMap K (LaurentSeries K) (WPFiniteNC122.q p)) hGX
    (by convert hP using 1; ring)
    (by convert hPv using 1; ring)
    (by dsimp only [u, v, P, Ds, Dv] at ⊢; simp only [map_mul]; convert hDP using 1 <;> ring)
    (by dsimp only [u, v, P, Ds, Dv, y] at ⊢; simp only [map_mul]; convert hU using 1; ring)
    (by dsimp only [u, v, P, Ds, Dv, y] at ⊢; simp only [map_mul]; convert hV using 1; ring)
    (by dsimp only [u, v, P, Ds, Dv, y] at ⊢; simp only [map_mul]; convert hXV using 1)
    (by dsimp only [u, v, P, Ds, Dv, y] at ⊢; simp only [map_mul]; convert hD using 1; ring)
  apply lowH_whole_finiteSeries_injective
  change f _ = f _
  rw [nativeOriginalHSource, lowHWholeOriginalKernelSource]
  simp only [Dsym]
  dsimp only [u, v, P, Ds, Dv, y] at he
  rw [← native_Cslot p hp η hη]
  simp only [f, map_mul, map_add, map_sub, map_neg, map_ofNat,
    localFiniteSeries_C, map_div₀, map_one] at he ⊢
  have hUA := congrArg f (native_u_affine (K := K) p hp)
  have hVA := congrArg f (native_v_affine (K := K) p hp)
  simp only [f, map_mul, map_add, map_sub, map_ofNat,
    localFiniteSeries_C, map_div₀, map_one] at hUA hVA
  simp only [hUA, hVA] at he ⊢
  convert he using 1 <;> ring

end WPFieldAssembly.NativeClosureLowH
