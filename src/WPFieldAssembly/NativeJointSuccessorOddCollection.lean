import WPFieldAssembly.NativeJointSuccessorOddResidues
import WPFieldAssembly.NativeJointSuccessorProductResidues
import WPFieldAssembly.NativeJointSuccessorActualDeep
import WPFieldAssembly.NativeJointSuccessorAdjointResidues
import WPFieldAssembly.NativeJointSuccessorPrimitiveEnds

open scoped BigOperators Polynomial LaurentPolynomial PowerSeries LaurentSeries
open Polynomial LaurentPolynomial HahnSeries

namespace WPFieldAssembly.NativeJointSuccessorOddCollection

open ActualBpairContraction ActualBpairLowHLocalPole ActualSimplePoleResidue
open NativeClosureMixedSource NativeJointSuccessorMixedPrimitive
open NativeJointSuccessorActualPhase NativeJointSuccessorActualDeep
open NativeJointSuccessorJSeries NativeJointSuccessorOddSource
open NativeJointSuccessorOddResidues NativeJointSuccessorProductResidues
open NativeJointSuccessorAdjointResidues NativeJointSuccessorPrimitiveEnds
open GreenLaurentOperators WPFiniteLaurentDifferential

variable {K : Type*} [Field K]
set_option maxHeartbeats 2800000

/-- The entire finite numerator from the original odd exact primitive. -/
noncomputable def oddPrimitiveNumerator (p : ℕ) : K[T;T⁻¹] :=
  oddReciprocalS p * T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) * (actualCtilde p).toLaurent

noncomputable def oddPrimitiveDerivativeCarrier (p : ℕ) [Fact p.Prime] [CharP K p] :
    K[T;T⁻¹] :=
  calL p * frobeniusPhi p * D (invert (actualAK p : K[X]).toLaurent)

/-- This coefficient is the actual odd value at infinity, before its separate harmonic reduction. -/
noncomputable def originalOddInfinityValue (p : ℕ) : K :=
  (5 : K) ^ ((p - 1) / 2) * (oddReciprocalS p : K[T;T⁻¹]).coeff (((p - 1) / 2 : ℕ) : ℤ)

noncomputable def oddInfinityPolynomial (p : ℕ) : K[X] :=
  LaurentPolynomial.trunc
    (T (((p - 1) / 2 : ℕ) : ℤ) * invert (oddReciprocalS p : K[T;T⁻¹]))

noncomputable def actualOddQuotientInfinitySeries (p : ℕ) : LaurentSeries K :=
  localFiniteSeriesHom (invert (oddReciprocalS p)) /
    localFiniteSeriesHom (invert WPFiniteWSource.squaredCoordinate.toLaurent) ^ ((p - 1) / 2)

noncomputable def actualLambdaInfinitySeries (p : ℕ) : LaurentSeries K :=
  -localFiniteSeriesHom (invert (clearedLambda p)) /
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent

noncomputable def actualKInfinitySeries (p : ℕ) : LaurentSeries K :=
  -localFiniteSeriesHom (invert (actualAdjointNumerator p)) /
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent

noncomputable def actualLogInfinitySeries : LaurentSeries K :=
  -localFiniteSeriesHom (T (-2) * invert (oddLogCleared : K[T;T⁻¹])) /
    (localFiniteSeriesHom (invert WPFiniteWSource.squaredCoordinate.toLaurent) *
      localFiniteSeriesHom (invert (4 - 11 * T 1 : K[T;T⁻¹])))

noncomputable def lambdaInfinityWeight (p : ℕ) : K :=
  2 * kappa p / 15 + WPFiniteNC122.h p / 5

private theorem finite_series_injective :
    Function.Injective (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) := by
  intro F G he
  ext j
  exact congrArg (fun Q : LaurentSeries K => Q.coeff j) he

private theorem Abar_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent ≠ 0 := by
  intro hz
  apply WPFiniteZSource.Abar_nonzero (K := K) p hp
  exact finite_series_injective (hz.trans (map_zero _).symm)

private theorem T_series_ne_zero (j : ℤ) :
    localFiniteSeriesHom (T j : K[T;T⁻¹]) ≠ 0 := by
  rw [localFiniteSeries_T]
  intro hz
  have hc := congrArg (fun Q : LaurentSeries K => Q.coeff j) hz
  simp only [HahnSeries.coeff_single, HahnSeries.coeff_zero] at hc
  exact one_ne_zero hc

private theorem squaredCoordinate_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ≠ 0 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  intro hz
  have hpz : (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent = 0 :=
    finite_series_injective (hz.trans (map_zero _).symm)
  have hp0 : (WPFiniteWSource.squaredCoordinate : K[X]) = 0 :=
    Polynomial.toLaurent_injective (hpz.trans (map_zero _).symm)
  have hc := congrArg (fun P : K[X] => P.coeff 1) hp0
  have he : (WPFiniteWSource.squaredCoordinate : K[X]).coeff 1 = (5 : K)⁻¹ := by
    simp [WPFiniteWSource.squaredCoordinate, Polynomial.coeff_one]
  rw [he, Polynomial.coeff_zero] at hc
  exact inv_ne_zero h5 hc

private theorem inverse_squaredCoordinate_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (invert (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent) ≠ 0 := by
  rw [WPFiniteZSource.invert_squaredCoordinate, map_mul]
  exact mul_ne_zero (T_series_ne_zero (-1)) (squaredCoordinate_series_ne_zero p hp)

private theorem inverse_Abar_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (invert (WPFiniteZSource.Abar : K[X]).toLaurent) ≠ 0 := by
  rw [WPFiniteZSource.invert_Abar, map_mul]
  exact mul_ne_zero (T_series_ne_zero (-2)) (Abar_series_ne_zero p hp)

private theorem inverse_w_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (invert (4 - 11 * T 1 : K[T;T⁻¹])) ≠ 0 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  intro hz
  have hc := congrArg (fun Q : LaurentSeries K => Q.coeff 0) hz
  have he : (4 - 11 * T 1 : K[T;T⁻¹]).coeff 0 = (4 : K) := by
    change (LaurentPolynomial.C (4 : K) - LaurentPolynomial.C (11 : K) * T 1).coeff 0 = 4
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, LaurentPolynomial.C_apply,
      GreenLaurentOperators.C_mul_coeff, LaurentPolynomial.T_apply]
    simp
  rw [localFiniteSeries_coeff, invert_apply, neg_zero, he, HahnSeries.coeff_zero] at hc
  exact h4 hc

private theorem ev_T (a : K) (ha : a ≠ 0) (j : ℤ) :
    ev a ha (T j : K[T;T⁻¹]) = a ^ j := by
  rw [show (T j : K[T;T⁻¹]) = LaurentPolynomial.C (1 : K) * T j by simp]
  simp only [ev, LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply,
    Units.val_zpow_eq_zpow_val, Units.val_mk0, one_mul]

private theorem ev_polynomial (a : K) (ha : a ≠ 0) (P : K[X]) :
    ev a ha P.toLaurent = P.eval a := by
  simp only [ev, LaurentPolynomial.eval₂_toLaurent, eval₂_id, Units.val_mk0]

/-- Both original proper ends retain their actual odd harmonic and branch weights. -/
theorem oddPrimitiveNumerator_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (h4 : (4 : K) ≠ 0) :
    ev (1 / 4) (one_div_ne_zero h4) (oddPrimitiveNumerator p : K[T;T⁻¹]) =
        -20 * WPFiniteNC122.h p * WPFiniteNC122.q p ∧
      ev 4 h4 (oddPrimitiveNumerator p : K[T;T⁻¹]) =
        10 * WPFiniteNC122.h p * WPFiniteNC122.q p := by
  let M := (p - 1) / 2 - 1
  have h4m : (4 : K) ^ M = 1 / 4 := by
    apply mul_right_cancel₀ h4
    rw [← pow_succ, show M + 1 = (p - 1) / 2 by dsimp only [M]; omega,
      WPFiniteWSource.four_half_power p hp, one_div_mul_cancel h4]
  have ham : (1 / 4 : K) ^ M = 4 := by
    rw [one_div, inv_pow, h4m]
    simp only [one_div, inv_inv]
  obtain ⟨hCa, hCb⟩ := actual_Ctilde_endpoints (K := K) p hp
  constructor
  · simp only [oddPrimitiveNumerator, map_mul, oddReciprocalS_eval_quarter p hp h4,
      ev_T, ev_polynomial, hCa, zpow_neg, zpow_natCast, show (p - 1) / 2 - 1 = M from rfl,
      ham]
    field_simp [h4]
    ring
  · simp only [oddPrimitiveNumerator, map_mul, oddReciprocalS_eval_four p hp h4,
      ev_T, ev_polynomial, hCb, zpow_neg, zpow_natCast, show (p - 1) / 2 - 1 = M from rfl,
      h4m, one_div, inv_inv]
    field_simp [h4]

/-- The whole primitive numerator has the two proper-end correction 2hq. -/
theorem oddPrimitiveNumerator_inversion_balance (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole (oddPrimitiveNumerator p : K[T;T⁻¹]) -
      originPole (invert (oddPrimitiveNumerator p)) =
        2 * WPFiniteNC122.h p * WPFiniteNC122.q p := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  let v : Kˣ := Units.mk0 4 h4
  have hv : (v : K) = 4 := rfl
  have hvi : v⁻¹ = Units.mk0 (1 / 4 : K) (one_div_ne_zero h4) := by
    ext
    simp only [v, Units.val_inv_eq_inv_val, Units.val_mk0, one_div]
  obtain ⟨hFa, hFb⟩ := oddPrimitiveNumerator_endpoints p hp h4
  have he := originPole_inversion_balance (oddPrimitiveNumerator p : K[T;T⁻¹]) v hv
  rw [hvi] at he
  change originPole (invert (oddPrimitiveNumerator p)) =
    originPole (oddPrimitiveNumerator p) +
      (ev (1 / 4) (one_div_ne_zero h4) (oddPrimitiveNumerator p) -
        ev 4 h4 (oddPrimitiveNumerator p)) / 15 at he
  rw [hFa, hFb] at he
  linear_combination (norm := (field_simp [h15]; ring)) -he

private theorem polynomial_powerSeries_embedding (P : K[X]) :
    localFiniteSeriesHom P.toLaurent = ((P : PowerSeries K) : LaurentSeries K) := by
  ext j
  rw [localFiniteSeries_coeff, PowerSeries.coeff_coe]
  by_cases hj : j < 0
  · rw [if_pos hj]
    exact WPFiniteJCarrier.toLaurent_coeff_outside P j (Or.inl hj)
  · rw [if_neg hj]
    have hc : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (by omega)
    rw [← hc, WPFiniteJCarrier.toLaurent_coeff_nat]
    simp only [Int.natAbs_natCast]
    exact (Polynomial.coeff_coe P j.toNat).symm

private theorem power_inverse_embedding (Q : PowerSeries K)
    (hc : PowerSeries.constantCoeff Q ≠ 0) (hQ : (Q : LaurentSeries K) ≠ 0) :
    ((Q⁻¹ : PowerSeries K) : LaurentSeries K) = (Q : LaurentSeries K)⁻¹ := by
  apply mul_right_cancel₀ hQ
  rw [inv_mul_cancel₀ hQ, ← PowerSeries.coe_mul,
    PowerSeries.inv_mul_cancel Q hc, PowerSeries.coe_one]

/-- The whole Os upper bound makes its genuine infinity numerator polynomial. -/
theorem oddInfinityPolynomial_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (oddInfinityPolynomial p : K[X]).toLaurent =
      T (((p - 1) / 2 : ℕ) : ℤ) * invert (oddReciprocalS p : K[T;T⁻¹]) := by
  ext j
  by_cases hj : 0 ≤ j
  · have hjn : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj
    rw [← hjn, WPFiniteJCarrier.toLaurent_coeff_nat]
    unfold oddInfinityPolynomial
    rw [WPFiniteJWeightedResidue.trunc_coeff]
  · rw [WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))]
    have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (((p - 1) / 2 : ℕ) : ℤ) j
      (invert (oddReciprocalS p : K[T;T⁻¹]))
    simp only [map_one, one_mul, invert_apply] at hs
    rw [hs]
    apply Eq.symm
    by_contra hc
    have hb := (oddReciprocalS_support (K := K) p hp _ (Finsupp.mem_support_iff.mpr hc)).2
    omega

theorem oddInfinityPolynomial_origin (p : ℕ) :
    (oddInfinityPolynomial p : K[X]).coeff 0 =
      (oddReciprocalS p : K[T;T⁻¹]).coeff (((p - 1) / 2 : ℕ) : ℤ) := by
  unfold oddInfinityPolynomial
  rw [WPFiniteJWeightedResidue.trunc_coeff]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (((p - 1) / 2 : ℕ) : ℤ) 0
    (invert (oddReciprocalS p : K[T;T⁻¹]))
  simp only [map_one, one_mul, invert_apply, zero_sub, neg_neg] at hs
  exact hs

private theorem oddInfinitySeries_polynomial_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientInfinitySeries p : LaurentSeries K) =
      localFiniteSeriesHom (oddInfinityPolynomial p).toLaurent /
        localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) := by
  let N := (p - 1) / 2
  have hi := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (WPFiniteZSource.invert_squared_power (K := K) p)
  simp only [map_pow, map_mul] at hi
  have ht : localFiniteSeriesHom (T (N : ℤ) : K[T;T⁻¹]) *
      localFiniteSeriesHom (T (-(N : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  unfold actualOddQuotientInfinitySeries
  rw [hi, oddInfinityPolynomial_source p hp, map_mul]
  let X : LaurentSeries K := localFiniteSeriesHom (T (N : ℤ) : K[T;T⁻¹])
  let Y : LaurentSeries K := localFiniteSeriesHom (T (-(N : ℤ)) : K[T;T⁻¹])
  let S : LaurentSeries K := localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent
  let O : LaurentSeries K := localFiniteSeriesHom (invert (oddReciprocalS p))
  have hY : Y ≠ 0 := T_series_ne_zero (-(N : ℤ))
  have hS : S ≠ 0 := squaredCoordinate_series_ne_zero p hp
  change X * Y = 1 at ht
  change O / (Y * S ^ N) = X * O / S ^ N
  linear_combination (norm := (field_simp [hY, hS]; ring)) (-O / (Y * S ^ N)) * ht

private theorem oddInfinitySeries_power_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    ∃ Q : PowerSeries K, (actualOddQuotientInfinitySeries p : LaurentSeries K) = Q := by
  let S : PowerSeries K := ((WPFiniteWSource.squaredCoordinate : K[X]) : PowerSeries K) ^ ((p - 1) / 2)
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hs0 : PowerSeries.constantCoeff S = (1 / 5 : K) ^ ((p - 1) / 2) := by
    simp [S, WPFiniteWSource.squaredCoordinate]
  have hs : PowerSeries.constantCoeff S ≠ 0 := by
    rw [hs0]
    exact pow_ne_zero _ (one_div_ne_zero h5)
  have hSN : (S : LaurentSeries K) ≠ 0 := by
    dsimp only [S]
    rw [PowerSeries.coe_pow,
      ← polynomial_powerSeries_embedding (WPFiniteWSource.squaredCoordinate : K[X])]
    exact pow_ne_zero _ (squaredCoordinate_series_ne_zero p hp)
  refine ⟨((oddInfinityPolynomial p : K[X]) : PowerSeries K) * S⁻¹, ?_⟩
  rw [oddInfinitySeries_polynomial_source p hp, polynomial_powerSeries_embedding,
    PowerSeries.coe_mul, power_inverse_embedding S hs hSN]
  dsimp only [S]
  rw [PowerSeries.coe_pow,
    ← polynomial_powerSeries_embedding (WPFiniteWSource.squaredCoordinate : K[X])]
  ring

/-- The original infinity value is its actual leading Os coefficient, with the retained fifth power. -/
theorem actual_odd_infinity_value (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualOddQuotientInfinitySeries p : LaurentSeries K).coeff 0 =
      originalOddInfinityValue p := by
  obtain ⟨Q, hQ⟩ := oddInfinitySeries_power_source (K := K) p hp
  let S : PowerSeries K := ((WPFiniteWSource.squaredCoordinate : K[X]) : PowerSeries K) ^ ((p - 1) / 2)
  have hSQt : ((S * Q : PowerSeries K) : LaurentSeries K) =
      (((oddInfinityPolynomial p : K[X]) : PowerSeries K) : LaurentSeries K) := by
    rw [PowerSeries.coe_mul, ← hQ, oddInfinitySeries_polynomial_source p hp]
    dsimp only [S]
    rw [PowerSeries.coe_pow,
      ← polynomial_powerSeries_embedding (WPFiniteWSource.squaredCoordinate : K[X]),
      ← polynomial_powerSeries_embedding (oddInfinityPolynomial p : K[X])]
    field_simp [squaredCoordinate_series_ne_zero p hp]
  have hSQ : (S * Q : PowerSeries K) = ((oddInfinityPolynomial p : K[X]) : PowerSeries K) := by
    ext n
    have hc := congrArg (fun U : LaurentSeries K => U.coeff (n : ℤ)) hSQt
    simpa only [PowerSeries.coeff_coe, if_neg (by omega : ¬(n : ℤ) < 0),
      Int.natAbs_natCast] using hc
  have hc := congrArg PowerSeries.constantCoeff hSQ
  have hs0 : PowerSeries.constantCoeff S = (1 / 5 : K) ^ ((p - 1) / 2) := by
    simp [S, WPFiniteWSource.squaredCoordinate]
  have hP0 : PowerSeries.constantCoeff (((oddInfinityPolynomial p : K[X]) : PowerSeries K)) =
      (oddInfinityPolynomial p : K[X]).coeff 0 := rfl
  rw [map_mul, hs0, hP0, oddInfinityPolynomial_origin] at hc
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hu : (5 : K) ^ ((p - 1) / 2) * (1 / 5 : K) ^ ((p - 1) / 2) = 1 := by
    rw [← mul_pow, mul_one_div_cancel h5, one_pow]
  rw [hQ, PowerSeries.coeff_coe]
  simp only [lt_self_iff_false, if_false, Int.natAbs_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold originalOddInfinityValue
  linear_combination (norm := ring_nf) (5 : K) ^ ((p - 1) / 2) * hc -
    PowerSeries.constantCoeff Q * hu

/-- The original even endpoints determine the full infinity coefficient of Lambda. -/
theorem lambdaInfinityWeight_value (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    lambdaInfinityWeight (K := K) p =
      -(2 / 5 : K) * (WPFiniteNC122.q p - (originalEven p : K[X]).eval 0) := by
  have hs := originalEven_endpoint_sum (K := K) p hp
  obtain ⟨_, hb⟩ := Dstar_endpoints (K := K) p hp
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have he : (originalEven p : K[X]).eval 4 = 3 * WPFiniteNC122.q p + WPFiniteNC122.h p := by
    simp only [originalEven, eval_neg, eval_mul, eval_C, hb]
    field_simp [h3]
    ring
  unfold lambdaInfinityWeight kappa
  linear_combination (norm := (field_simp [h2, h3, h5, h15]; ring))
    (-2 / 15 : K) * hs + (-2 / 15 : K) * he

/-- Reflection retains the whole original Lambda and isolates its only infinity pole. -/
theorem actual_lambda_infinity_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    -invert (clearedLambda p : K[T;T⁻¹]) =
      LaurentPolynomial.C (lambdaInfinityWeight p) *
          (WPFiniteZSource.Abar : K[X]).toLaurent * T (-1) +
        (Polynomial.C (4 * WPFiniteNC122.h p / 5) * (X + 1) : K[X]).toLaurent := by
  let x : K[T;T⁻¹] := T 1
  let t : K[T;T⁻¹] := T (-1)
  let A : K[T;T⁻¹] := (WPFiniteZSource.Abar : K[X]).toLaurent
  let a : K[T;T⁻¹] := LaurentPolynomial.C (2 * kappa p / 15)
  let c : K[T;T⁻¹] := LaurentPolynomial.C (WPFiniteNC122.h p / 5)
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have ht : x * t = 1 := by dsimp only [x, t]; rw [← T_add]; norm_num
  have hA : A = (4 - x) * (4 * x - 1) := by
    simp only [A, WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat,
      Polynomial.toLaurent_X, map_one, x]
  have hAt : A * t = -4 * x + 17 - 4 * t := by
    rw [hA]
    linear_combination (norm := ring_nf) (-4 * x + 17) * ht
  have hscalar1 : (16 * WPFiniteNC122.h p / 15 : K) - 4 * WPFiniteNC122.h p / 15 =
      4 * (WPFiniteNC122.h p / 5) := by field_simp [h5, h15]; ring
  have hscalar2 : -4 * (16 * WPFiniteNC122.h p / 15 : K) +
        (4 * WPFiniteNC122.h p / 15) * (1 / 4) = -21 * (WPFiniteNC122.h p / 5) := by
    field_simp [h4, h5, h15]
    ring
  have hs1 := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hscalar1
  have hs2 := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hscalar2
  simp only [map_sub, map_add, map_mul, map_neg, map_ofNat] at hs1 hs2
  have ha : LaurentPolynomial.C (-2 * kappa p / 15 : K) = -a := by
    dsimp only [a]
    rw [← map_neg]
    congr 1
    ring
  have hclear : (clearedLambda p : K[T;T⁻¹]) = -a * A * t + 4 * c * x - 21 * c := by
    unfold clearedLambda
    rw [ha]
    change -a * A * t + LaurentPolynomial.C (16 * WPFiniteNC122.h p / 15) * (x - 4) -
      LaurentPolynomial.C (4 * WPFiniteNC122.h p / 15) *
        (x - LaurentPolynomial.C (1 / 4 : K)) = _
    linear_combination (norm := (dsimp only [c]; ring_nf)) x * hs1 + hs2
  have hInvAt : invert (A * t) = A * t := by
    dsimp only [A, t]
    rw [map_mul, WPFiniteZSource.invert_Abar, invert_T]
    simp only [neg_neg]
    have ht2 : (T (-2) * T 1 : K[T;T⁻¹]) = T (-1) := by rw [← T_add]; norm_num
    linear_combination (WPFiniteZSource.Abar : K[X]).toLaurent * ht2
  have hInv : invert (clearedLambda p : K[T;T⁻¹]) = -a * A * t + 4 * c * t - 21 * c := by
    rw [hclear, show -a * A * t = -a * (A * t) by ring]
    rw [map_sub, map_add, map_mul, map_neg, hInvAt]
    simp only [map_mul, map_ofNat, invert_C, a, c, x, t, invert_T]
  have hweight : LaurentPolynomial.C (lambdaInfinityWeight (K := K) p) = a + c := by
    simp only [lambdaInfinityWeight, map_add, a, c]
  have hcoef : LaurentPolynomial.C (4 * WPFiniteNC122.h p / 5 : K) = 4 * c := by
    have he : (4 * WPFiniteNC122.h p / 5 : K) = 4 * (WPFiniteNC122.h p / 5) := by ring
    simpa only [map_mul, map_ofNat, c] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) he
  rw [hInv, hweight]
  simp only [map_mul, Polynomial.toLaurent_C, map_add, Polynomial.toLaurent_X,
    map_one, hcoef]
  change -(-a * A * t + 4 * c * t - 21 * c) = (a + c) * A * t + 4 * c * (x + 1)
  linear_combination (norm := ring_nf) -c * hAt

private theorem Abar_power_inverse (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (((((WPFiniteZSource.Abar : K[X]) : PowerSeries K)⁻¹) : PowerSeries K) : LaurentSeries K) =
      (localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)⁻¹ := by
  let Q : PowerSeries K := (WPFiniteZSource.Abar : K[X])
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hc0 : PowerSeries.constantCoeff Q = -4 := by simp [Q, WPFiniteZSource.Abar]
  have hc : PowerSeries.constantCoeff Q ≠ 0 := by rw [hc0]; exact neg_ne_zero.mpr h4
  have hQ : (Q : LaurentSeries K) ≠ 0 := by
    rw [← polynomial_powerSeries_embedding]
    exact Abar_series_ne_zero p hp
  simpa only [Q, ← polynomial_powerSeries_embedding] using power_inverse_embedding Q hc hQ

private theorem LambdaInfinitySeries_power_remainder (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    ∃ R : PowerSeries K, (actualLambdaInfinitySeries p : LaurentSeries K) =
      HahnSeries.single (-1) (lambdaInfinityWeight p) + (R : LaurentSeries K) := by
  let P : K[X] := Polynomial.C (4 * WPFiniteNC122.h p / 5) * (X + 1)
  let A : PowerSeries K := (WPFiniteZSource.Abar : K[X])
  refine ⟨(P : PowerSeries K) * A⁻¹, ?_⟩
  have hsource : -localFiniteSeriesHom (invert (clearedLambda p : K[T;T⁻¹])) =
      localFiniteSeriesHom (LaurentPolynomial.C (lambdaInfinityWeight p)) *
          localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
          localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) + localFiniteSeriesHom P.toLaurent := by
    simpa only [map_neg, map_add, map_mul, P] using
      congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
        (actual_lambda_infinity_cleared_source (K := K) p hp)
  unfold actualLambdaInfinitySeries
  rw [hsource, PowerSeries.coe_mul, Abar_power_inverse p hp,
    ← polynomial_powerSeries_embedding P]
  have hsing : HahnSeries.single (-1) (lambdaInfinityWeight (K := K) p) =
      localFiniteSeriesHom (LaurentPolynomial.C (lambdaInfinityWeight p)) *
        localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) := by
    rw [localFiniteSeries_C, localFiniteSeries_T, LaurentSeries.algebraMap_apply,
      HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hsing]
  field_simp [Abar_series_ne_zero p hp]

/-- The whole Lambda infinity residue uses the actual original odd value. -/
theorem actual_odd_Lambda_infinity_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientInfinitySeries p * actualLambdaInfinitySeries p : LaurentSeries K).coeff (-1) =
      -(2 / 5 : K) * (WPFiniteNC122.q p - (originalEven p : K[X]).eval 0) *
        originalOddInfinityValue p := by
  obtain ⟨Q, hQ⟩ := oddInfinitySeries_power_source (K := K) p hp
  obtain ⟨R, hR⟩ := LambdaInfinitySeries_power_remainder (K := K) p hp
  rw [hR, mul_add, HahnSeries.coeff_add]
  have hr : (actualOddQuotientInfinitySeries p * (R : LaurentSeries K)).coeff (-1) = 0 := by
    rw [hQ, ← PowerSeries.coe_mul, PowerSeries.coeff_coe, if_pos (by omega : (-1 : ℤ) < 0)]
  rw [hr, add_zero, HahnSeries.coeff_mul_single, sub_self,
    actual_odd_infinity_value p hp, lambdaInfinityWeight_value p hp]
  ring

private theorem finite_quotient_derivative (F Q : K[T;T⁻¹])
    (hQ : localFiniteSeriesHom Q ≠ 0) :
    LaurentSeries.derivative K (localFiniteSeriesHom F / localFiniteSeriesHom Q) =
      (localFiniteSeriesHom (D F) * localFiniteSeriesHom Q -
        localFiniteSeriesHom F * localFiniteSeriesHom (D Q)) /
          localFiniteSeriesHom Q ^ 2 := by
  have hs : localFiniteSeriesHom Q *
      (localFiniteSeriesHom F / localFiniteSeriesHom Q) = localFiniteSeriesHom F := by
    field_simp [hQ]
  have hd := congrArg (LaurentSeries.derivative K) hs
  have hF : LaurentSeries.derivative K (localFiniteSeriesHom F) =
      localFiniteSeriesHom (D F) := (lowHFiniteSeries_derivative F).symm
  rw [finite_series_derivative_product, hF] at hd
  linear_combination (norm := (field_simp [hQ]; ring))
    (1 / localFiniteSeriesHom Q) * hd

private theorem finite_inverse_quotient_derivative (F Q : K[T;T⁻¹])
    (hQ : localFiniteSeriesHom (invert Q) ≠ 0) :
    LaurentSeries.derivative K
        (localFiniteSeriesHom (invert F) / localFiniteSeriesHom (invert Q)) =
      -localFiniteSeriesHom (T (-2) : K[T;T⁻¹]) *
        (localFiniteSeriesHom (invert (D F)) * localFiniteSeriesHom (invert Q) -
          localFiniteSeriesHom (invert F) * localFiniteSeriesHom (invert (D Q))) /
            localFiniteSeriesHom (invert Q) ^ 2 := by
  rw [finite_quotient_derivative _ _ hQ, D_invert, D_invert]
  simp only [map_neg, map_mul]
  ring

/-- The whole original odd derivative is cleared before reciprocal transport. -/
theorem actual_odd_quotient_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * WPFiniteWSource.squaredCoordinate.toLaurent *
        (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * D (oddReciprocalS p) -
          oddReciprocalS p * D (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2))) *
        (4 - 11 * T 1) =
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        (oddDensityCleared p * (4 - 11 * T 1) -
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * frobeniusPhi p *
            oddLogCleared * (WPFiniteZSource.Abar : K[X]).toLaurent -
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) * frobeniusPhi p *
            (WPFiniteZSource.Abar : K[X]).toLaurent *
              D (invert (actualAK p : K[X]).toLaurent) * (4 - 11 * T 1)) := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  let A : K[T;T⁻¹] := (WPFiniteZSource.Abar : K[X]).toLaurent
  let w : K[T;T⁻¹] := 4 - 11 * T 1
  have ho := oddReciprocalS_cleared_source (K := K) p hp
  have hl := actual_odd_log_cleared_source (K := K) p hp
  have he := actual_AQ_cleared_derivative (K := K) p hp
  have hh := mixedHalfPower_homogeneous (K := K) p hp
  have hf : A * (s * D (oddReciprocalS p) + LaurentPolynomial.C (1 / 10 : K) *
        oddReciprocalS p) * w =
      oddDensityCleared p * w - s ^ N * frobeniusPhi p * oddLogCleared * A -
        s ^ (N + 1) * frobeniusPhi p * A * D (invert (actualAK p : K[X]).toLaurent) * w := by
    unfold oddDensityCleared
    rw [show 2 * ((p - 1) / 2) + 1 = (N + 1) + N by dsimp only [N]; omega, pow_add]
    linear_combination (norm := (dsimp only [N, s, A, w, frobeniusPhi]; ring_nf))
      w * ho + s ^ N * hl +
      s ^ (N + 1) * frobeniusPhi p * w * he
  linear_combination (norm := (dsimp only [N, s, A, w]; ring_nf))
    s ^ N * hf - A * oddReciprocalS p * w * hh

/-- The original odd source transports with the reciprocal differential, including its sign. -/
theorem actual_odd_quotient_infinity_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    LaurentSeries.derivative K (actualOddQuotientInfinitySeries p : LaurentSeries K) =
      actualOddInfinitySeries p - localFiniteSeriesHom (invert (frobeniusPhi p)) *
        (actualLogInfinitySeries + localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent)) := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  let A : K[T;T⁻¹] := (WPFiniteZSource.Abar : K[X]).toLaurent
  let w : K[T;T⁻¹] := 4 - 11 * T 1
  let S : LaurentSeries K := localFiniteSeriesHom (invert s)
  let AS : LaurentSeries K := localFiniteSeriesHom (invert A)
  let WS : LaurentSeries K := localFiniteSeriesHom (invert w)
  let t : LaurentSeries K := localFiniteSeriesHom (T (-2) : K[T;T⁻¹])
  let OI : LaurentSeries K := localFiniteSeriesHom (invert (oddReciprocalS p))
  let dO : LaurentSeries K := localFiniteSeriesHom (invert (D (oddReciprocalS p)))
  let dSN : LaurentSeries K := localFiniteSeriesHom (invert (D (s ^ N)))
  let Dn : LaurentSeries K := localFiniteSeriesHom (invert (oddDensityCleared p))
  let P : LaurentSeries K := localFiniteSeriesHom (invert (frobeniusPhi p))
  let L : LaurentSeries K := localFiniteSeriesHom (invert oddLogCleared)
  let dE : LaurentSeries K :=
    localFiniteSeriesHom (invert (D (invert (actualAK p : K[X]).toLaurent)))
  have hS : S ≠ 0 := inverse_squaredCoordinate_series_ne_zero p hp
  have hA : AS ≠ 0 := inverse_Abar_series_ne_zero p hp
  have hW : WS ≠ 0 := inverse_w_series_ne_zero p hp
  have he := congrArg (fun F : K[T;T⁻¹] => LaurentPolynomial.invert F)
    (actual_odd_quotient_cleared_source (K := K) p hp)
  have hm := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) he
  simp only [map_mul, map_sub, map_pow] at hm
  have hm' : AS * S * (S ^ N * dO - OI * dSN) * WS =
      S ^ N * (Dn * WS - S ^ N * P * L * AS - S ^ (N + 1) * P * AS * dE * WS) := by
    simpa only [AS, S, WS, OI, dO, dSN, Dn, P, L, dE, N, s, A, w,
      map_mul, map_sub, map_pow] using hm
  have hd := finite_inverse_quotient_derivative (oddReciprocalS p : K[T;T⁻¹]) (s ^ N)
    (by simpa only [map_pow] using pow_ne_zero N hS)
  simp only [map_pow] at hd
  have hdE := D_invert (invert (actualAK p : K[X]).toLaurent)
  simp only [involutive_invert (actualAK p : K[X]).toLaurent] at hdE
  have hmE := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) hdE
  simp only [map_neg, map_mul] at hmE
  unfold actualOddQuotientInfinitySeries actualOddInfinitySeries actualLogInfinitySeries
  rw [hd, hmE]
  simp only [map_mul]
  change -t * (dO * S ^ N - OI * dSN) / (S ^ N) ^ 2 =
    -(t * Dn) / (S ^ (N + 1) * AS) - P * (-(t * L) / (S * WS) + -(t * dE))
  linear_combination (norm := (field_simp [hS, hA, hW, pow_ne_zero N hS]; ring))
    (-t / (AS * S * (S ^ N) ^ 2 * WS)) * hm'

/-- The whole reciprocal adjoint has the same normalized primitive and original Lambda. -/
theorem actual_adjoint_infinity_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualKInfinitySeries p : LaurentSeries K) =
      LaurentSeries.derivative K (localFiniteSeriesHom (invert (calL (K := K) p))) +
        (actualLambdaInfinitySeries p : LaurentSeries K) := by
  have he := calL_cleared_source (K := K) p hp
  change (WPFiniteZSource.Abar : K[X]).toLaurent * D (calL p) =
    actualAdjointNumerator p - clearedLambda p at he
  have hi := congrArg (fun F : K[T;T⁻¹] => LaurentPolynomial.invert F) he
  simp only [map_mul, map_sub, WPFiniteZSource.invert_Abar] at hi
  have hd : (WPFiniteZSource.Abar : K[X]).toLaurent * D (invert (calL p)) =
      -invert (actualAdjointNumerator p) + invert (clearedLambda p) := by
    rw [D_invert]
    linear_combination (norm := ring_nf) -hi
  have hm := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) hd
  simp only [map_mul, map_add, map_neg] at hm
  unfold actualKInfinitySeries actualLambdaInfinitySeries
  have hdiff : LaurentSeries.derivative K (localFiniteSeriesHom (invert (calL (K := K) p))) =
      localFiniteSeriesHom (D (invert (calL (K := K) p))) :=
    (lowHFiniteSeries_derivative (invert (calL (K := K) p))).symm
  rw [hdiff]
  linear_combination (norm := (field_simp [Abar_series_ne_zero p hp]; ring))
    (-1 / localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent) * hm

private theorem adjoint_full_branch_factor (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualAdjointNumerator p : K[T;T⁻¹]) =
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) * (actualCtilde p).toLaurent := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  have ht : (T (-((N - 1 : ℕ) : ℤ)) * T ((N - 1 : ℕ) : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  unfold actualAdjointNumerator actualCtilde
  rw [lowH_Dsym_full_branch_factor p hp]
  simp only [map_sub, map_mul, map_ofNat, map_pow, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, T_pow]
  change LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) *
      (T (-((N - 1 : ℕ) : ℤ)) * s ^ (N + 1) * (branchPolynomial p).toLaurent) -
    2 * LaurentPolynomial.C (WPFiniteNC122.h p) * s ^ N = _
  rw [show ((N - 1 : ℕ) : ℤ) * 1 = ((N - 1 : ℕ) : ℤ) by ring]
  rw [pow_succ]
  linear_combination (norm := (dsimp only [N, s]; ring_nf))
    2 * LaurentPolynomial.C (WPFiniteNC122.h p) * s ^ N * ht

private theorem actual_odd_K_infinity_carrier (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientInfinitySeries p * actualKInfinitySeries p : LaurentSeries K) =
      -localFiniteSeriesHom (invert (oddPrimitiveNumerator p)) /
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent := by
  have hi := congrArg (fun F : K[T;T⁻¹] => LaurentPolynomial.invert F)
    (adjoint_full_branch_factor (K := K) p hp)
  simp only [map_mul, map_pow] at hi
  unfold actualOddQuotientInfinitySeries actualKInfinitySeries
  rw [hi]
  simp only [oddPrimitiveNumerator, map_mul, map_pow]
  field_simp [inverse_squaredCoordinate_series_ne_zero p hp, Abar_series_ne_zero p hp]

private theorem actual_log_infinity_carrier (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (invert (calL p : K[T;T⁻¹])) *
      localFiniteSeriesHom (invert (frobeniusPhi p)) * actualLogInfinitySeries =
        -localFiniteSeriesHom (T (-2) * invert (oddLogLaurentCarrier p)) := by
  have hi := congrArg (fun F : K[T;T⁻¹] => LaurentPolynomial.invert F)
    (actual_calL_log_Laurent_source (K := K) p hp)
  have hm := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) hi
  simp only [map_mul] at hm
  unfold actualLogInfinitySeries
  simp only [map_mul]
  let S : LaurentSeries K := localFiniteSeriesHom (invert WPFiniteWSource.squaredCoordinate.toLaurent)
  let W : LaurentSeries K := localFiniteSeriesHom (invert (4 - 11 * T 1 : K[T;T⁻¹]))
  let t : LaurentSeries K := localFiniteSeriesHom (T (-2) : K[T;T⁻¹])
  let L : LaurentSeries K := localFiniteSeriesHom (invert oddLogCleared)
  let J : LaurentSeries K := localFiniteSeriesHom (invert (oddLogLaurentCarrier p))
  let C : LaurentSeries K := localFiniteSeriesHom (invert (calL p))
  let P : LaurentSeries K := localFiniteSeriesHom (invert (frobeniusPhi p))
  have hS : S ≠ 0 := inverse_squaredCoordinate_series_ne_zero p hp
  have hW : W ≠ 0 := inverse_w_series_ne_zero p hp
  change S * W * J = C * P * L at hm
  change C * P * (-(t * L) / (S * W)) = -(t * J)
  linear_combination (norm := (field_simp [hS, hW]; ring)) (t / (S * W)) * hm

private theorem actual_derivative_infinity_carrier (p : ℕ) [Fact p.Prime] [CharP K p] :
    localFiniteSeriesHom (invert (calL p : K[T;T⁻¹])) *
        localFiniteSeriesHom (invert (frobeniusPhi p)) *
          localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent) =
      -localFiniteSeriesHom (T (-2) * invert (oddPrimitiveDerivativeCarrier p)) := by
  have hd := D_invert (invert (actualAK p : K[X]).toLaurent)
  simp only [involutive_invert (actualAK p : K[X]).toLaurent] at hd
  rw [hd]
  simp only [oddPrimitiveDerivativeCarrier, map_mul, map_neg]
  ring

private theorem reflected_differential_residue (F : K[T;T⁻¹]) :
    (-localFiniteSeriesHom (T (-2) * invert F)).coeff (-1) = -F.coeff (-1) := by
  rw [HahnSeries.coeff_neg, localFiniteSeries_coeff]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-2) (-1) (invert F)
  simp only [map_one, one_mul, invert_apply] at hs
  rw [hs]
  norm_num

/-- The reciprocal exact primitive attaches the infinity residues to the SAME three finite carriers. -/
theorem actual_odd_reflected_primitive_reduction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientInfinitySeries p * actualLambdaInfinitySeries p -
        localFiniteSeriesHom (invert (calL p)) * actualOddInfinitySeries p : LaurentSeries K).coeff (-1) =
      -originPole (invert (oddPrimitiveNumerator p)) +
        (oddLogLaurentCarrier p : K[T;T⁻¹]).coeff (-1) +
          (oddPrimitiveDerivativeCarrier p : K[T;T⁻¹]).coeff (-1) := by
  have hi := lowH_finite_series_IBP (invert (calL p : K[T;T⁻¹]))
    (actualOddQuotientInfinitySeries p)
  have hdiff : localFiniteSeriesHom (D (invert (calL (K := K) p))) =
      LaurentSeries.derivative K (localFiniteSeriesHom (invert (calL (K := K) p))) :=
    lowHFiniteSeries_derivative (invert (calL (K := K) p))
  change (localFiniteSeriesHom (D (invert (calL (K := K) p))) *
      actualOddQuotientInfinitySeries (K := K) p : LaurentSeries K).coeff (-1) +
    (localFiniteSeriesHom (invert (calL (K := K) p)) *
      LaurentSeries.derivative K (actualOddQuotientInfinitySeries (K := K) p) :
        LaurentSeries K).coeff (-1) = 0 at hi
  rw [hdiff] at hi
  have hi' : (actualOddQuotientInfinitySeries (K := K) p *
      LaurentSeries.derivative K (localFiniteSeriesHom (invert (calL (K := K) p))) +
        localFiniteSeriesHom (invert (calL (K := K) p)) *
          LaurentSeries.derivative K (actualOddQuotientInfinitySeries (K := K) p) :
            LaurentSeries K).coeff (-1) = 0 := by
    rw [HahnSeries.coeff_add]
    simpa only [mul_comm] using hi
  have hreduce : (actualOddQuotientInfinitySeries p * actualLambdaInfinitySeries p -
      localFiniteSeriesHom (invert (calL p)) * actualOddInfinitySeries p : LaurentSeries K).coeff (-1) =
      (actualOddQuotientInfinitySeries p * actualKInfinitySeries p -
        localFiniteSeriesHom (invert (calL p)) * localFiniteSeriesHom (invert (frobeniusPhi p)) *
          (actualLogInfinitySeries + localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent))).coeff (-1) := by
    rw [actual_odd_quotient_infinity_source p hp] at hi'
    rw [actual_adjoint_infinity_source p hp]
    simp only [mul_add, mul_sub, mul_assoc, HahnSeries.coeff_add, HahnSeries.coeff_sub] at *
    linear_combination (norm := ring_nf) -hi'
  rw [hreduce]
  have he : actualOddQuotientInfinitySeries p * actualKInfinitySeries p -
      localFiniteSeriesHom (invert (calL p)) * localFiniteSeriesHom (invert (frobeniusPhi p)) *
        (actualLogInfinitySeries + localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent)) =
      actualOddQuotientInfinitySeries p * actualKInfinitySeries p -
        localFiniteSeriesHom (invert (calL p)) * localFiniteSeriesHom (invert (frobeniusPhi p)) *
          actualLogInfinitySeries -
        localFiniteSeriesHom (invert (calL p)) * localFiniteSeriesHom (invert (frobeniusPhi p)) *
          localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent) := by ring
  rw [he, HahnSeries.coeff_sub, HahnSeries.coeff_sub, actual_odd_K_infinity_carrier p hp,
    actual_log_infinity_carrier p hp, actual_derivative_infinity_carrier]
  rw [show -localFiniteSeriesHom (invert (oddPrimitiveNumerator p)) /
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent =
      -(localFiniteSeriesHom (invert (oddPrimitiveNumerator p)) /
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent) by ring,
    HahnSeries.coeff_neg, local_Abar_quotient_residue p hp,
    reflected_differential_residue, reflected_differential_residue]
  ring

/-- The original two proper ends are collected without a rational global-residue premise. -/
theorem actual_odd_origin_infinity_balance (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientSeries p * actualLambdaSeries p -
        localFiniteSeriesHom (calL p) * NativeJointSuccessorJSeries.actualOddSeries p :
          LaurentSeries K).coeff (-1) +
      (actualOddQuotientInfinitySeries p * actualLambdaInfinitySeries p -
        localFiniteSeriesHom (invert (calL p)) * actualOddInfinitySeries p : LaurentSeries K).coeff (-1) =
        2 * WPFiniteNC122.h p * WPFiniteNC122.q p := by
  rw [actual_odd_branch_residue_reduction p hp, actual_odd_reflected_primitive_reduction p hp]
  change originPole (oddPrimitiveNumerator p) - (oddLogLaurentCarrier p : K[T;T⁻¹]).coeff (-1) -
      (oddPrimitiveDerivativeCarrier p).coeff (-1) +
    (-originPole (invert (oddPrimitiveNumerator p)) + (oddLogLaurentCarrier p).coeff (-1) +
      (oddPrimitiveDerivativeCarrier p).coeff (-1)) = _
  linear_combination (norm := ring_nf) oddPrimitiveNumerator_inversion_balance (K := K) p hp

/-- The actual original odd residue has its proper ends, retained infinity value and full unit term. -/
theorem actual_odd_residue_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientSeries p * actualLambdaSeries p -
        localFiniteSeriesHom (calL p) * NativeJointSuccessorJSeries.actualOddSeries p :
          LaurentSeries K).coeff (-1) =
      2 * WPFiniteNC122.h p * WPFiniteNC122.q p +
        (2 / 5 : K) * (WPFiniteNC122.q p - (originalEven p : K[X]).eval 0) *
          originalOddInfinityValue p +
        6 * originPole (invert (calL p) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) := by
  have he := actual_odd_origin_infinity_balance (K := K) p hp
  simp only [HahnSeries.coeff_sub] at he ⊢
  rw [actual_odd_Lambda_infinity_residue p hp,
    actual_odd_infinity_residue p hp] at he
  linear_combination (norm := ring_nf) he

/-- All four original positive H rows and both even endpoints survive the infinity unit integration. -/
theorem actual_odd_infinity_unit_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    6 * originPole (invert (calL p : K[T;T⁻¹]) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) =
      -(4 / 75 : K) *
          (2 * branchH p (1 / 4) (1 / 4) + branchH p 4 (1 / 4) -
            2 * branchH p (1 / 4) 4 - branchH p 4 4) +
        7 * (WPFiniteNC122.h p) ^ 2 / 125 -
        (4 / 75 : K) * (originalEven p : K[X]).eval (1 / 4) ^ 2 -
        (8 / 75 : K) * (originalEven p).eval 4 ^ 2 -
        (8 / 25 : K) * (originalEven p).eval (1 / 4) * (originalEven p).eval 4 +
        (4 / 25 : K) * (originalEven p).eval 0 ^ 2 -
        (8 * WPFiniteNC122.q p / 25) * (originalEven p).eval 0 := by
  rw [mul_comm (invert (calL p : K[T;T⁻¹]))
      (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)),
    actual_calL_inverse_half_weighted_residue p hp,
    actual_calL_inverse_origin p hp, Tprod_value p hp, Uprod_value p hp]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero 2 h5
  have h40 : (40 : K) ≠ 0 := by
    rw [show (40 : K) = 2 ^ 3 * 5 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h5
  have h50 : (50 : K) ≠ 0 := by
    rw [show (50 : K) = 2 * 25 by ring]
    exact mul_ne_zero h2 h25
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 25 by ring]
    exact mul_ne_zero h3 h25
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero 3 h5
  have h225 : (225 : K) ≠ 0 := by
    rw [show (225 : K) = 15 ^ 2 by ring]
    exact pow_ne_zero 2 h15
  field_simp [h2, h3, h5, h15, h25, h40, h50, h75, h125, h225]
  ring

/-- This uniform original odd scalar is collected from actual sources, with no residue premise. -/
theorem actual_odd_collected_scalar (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientSeries p * actualLambdaSeries p -
        localFiniteSeriesHom (calL p) * NativeJointSuccessorJSeries.actualOddSeries p :
          LaurentSeries K).coeff (-1) =
      2 * WPFiniteNC122.h p * WPFiniteNC122.q p +
        (2 / 5 : K) * (WPFiniteNC122.q p - (originalEven p : K[X]).eval 0) *
          originalOddInfinityValue p -
        (4 / 75 : K) *
          (2 * branchH p (1 / 4) (1 / 4) + branchH p 4 (1 / 4) -
            2 * branchH p (1 / 4) 4 - branchH p 4 4) +
        7 * (WPFiniteNC122.h p) ^ 2 / 125 -
        (4 / 75 : K) * (originalEven p).eval (1 / 4) ^ 2 -
        (8 / 75 : K) * (originalEven p).eval 4 ^ 2 -
        (8 / 25 : K) * (originalEven p).eval (1 / 4) * (originalEven p).eval 4 +
        (4 / 25 : K) * (originalEven p).eval 0 ^ 2 -
        (8 * WPFiniteNC122.q p / 25) * (originalEven p).eval 0 := by
  rw [actual_odd_residue_collection p hp, actual_odd_infinity_unit_collection p hp]
  ring

end WPFieldAssembly.NativeJointSuccessorOddCollection


