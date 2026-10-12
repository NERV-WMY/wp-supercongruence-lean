import WPFieldAssembly.NativeJointSuccessorActualPhase
import WPFieldAssembly.NativeJointSuccessorMixedPrimitive
import WPFieldAssembly.NativeJointSuccessorOddSource
import WPFieldAssembly.ActualBpairLowHLocalPole

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries

namespace WPFieldAssembly.NativeJointSuccessorJSeries

open ActualBpairContraction NativeClosureMixedSource NativeJointSuccessorMixedPrimitive
open NativeJointSuccessorActualPhase
open NativeJointSuccessorOddSource
open ActualBpairLowHLocalPole WPFiniteLaurentDifferential

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The original j is expanded at zero after retaining the entire finite residual R. -/
noncomputable def actualJSeries (p : ℕ) [Fact p.Prime] [CharP K p] : LaurentSeries K :=
  localFiniteSeriesHom (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) /
    localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)

noncomputable def actualAdjointNumerator (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) * Dsym p -
    LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)

noncomputable def actualKSeries (p : ℕ) : LaurentSeries K :=
  localFiniteSeriesHom (actualAdjointNumerator p) /
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent

/-- This is the whole Lambda, including its origin and both proper-end poles. -/
noncomputable def actualLambdaSeries (p : ℕ) : LaurentSeries K :=
  localFiniteSeriesHom (clearedLambda p) /
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent

noncomputable def actualOddSeries (p : ℕ) : LaurentSeries K :=
  localFiniteSeriesHom (oddDensityCleared p) /
    (localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)

noncomputable def actualLogSeries : LaurentSeries K :=
  localFiniteSeriesHom (oddLogCleared : K[T;T⁻¹]) /
    (localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent *
      localFiniteSeriesHom (4 - 11 * T 1))

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
  have hcoef : (WPFiniteWSource.squaredCoordinate : K[X]).coeff 1 = (5 : K)⁻¹ := by
    simp [WPFiniteWSource.squaredCoordinate, Polynomial.coeff_one]
  rw [hcoef, Polynomial.coeff_zero] at hc
  exact inv_ne_zero h5 hc

private theorem oddLinear_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : localFiniteSeriesHom (4 - 11 * T 1 : K[T;T⁻¹]) ≠ 0 := by
  intro hz
  have he : (4 - 11 * T 1 : K[T;T⁻¹]) = 0 :=
    finite_series_injective (hz.trans (map_zero _).symm)
  have hc := congrArg (fun F : K[T;T⁻¹] => F.coeff 0) he
  have hcoef : (4 - 11 * T 1 : K[T;T⁻¹]).coeff 0 = (4 : K) := by
    change (LaurentPolynomial.C (4 : K) - LaurentPolynomial.C (11 : K) * T 1).coeff 0 = 4
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, LaurentPolynomial.C_apply,
      GreenLaurentOperators.C_mul_coeff, LaurentPolynomial.T_apply]
    simp
  rw [hcoef, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  exact h4 hc

/-- The full finite Laurent factor obeys the coefficient product rule against any series. -/
theorem finite_series_derivative_product (F : K[T;T⁻¹]) (Q : LaurentSeries K) :
    LaurentSeries.derivative K (localFiniteSeriesHom F * Q) =
      localFiniteSeriesHom (D F) * Q +
        localFiniteSeriesHom F * LaurentSeries.derivative K Q := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
      simp only [map_add, add_mul, hF, hG]
      ring
  | C_mul_T n a =>
      change LaurentSeries.derivative K (lowHFiniteSeries (LaurentPolynomial.C a * T n) * Q) =
        lowHFiniteSeries (D (LaurentPolynomial.C a * T n)) * Q +
          lowHFiniteSeries (LaurentPolynomial.C a * T n) * LaurentSeries.derivative K Q
      simp only [D_monomial, lowHFiniteSeries_monomial]
      ext j
      rw [lowH_series_derivative_coeff, HahnSeries.coeff_single_mul,
        HahnSeries.coeff_add, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul,
        lowH_series_derivative_coeff]
      rw [show j - n + 1 = j + 1 - n by omega,
        show j - (n - 1) = j + 1 - n by omega]
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one]
      ring

/-- The full j derivative is obtained by the original half-power multiplier, without deleting phases. -/
theorem actual_J_series_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
        LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K) =
      localFiniteSeriesHom
        (WPFiniteWSource.squaredCoordinate.toLaurent *
          D (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) +
            LaurentPolynomial.C (1 / 10 : K) *
              mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  let R : K[T;T⁻¹] := mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)
  let J : LaurentSeries K := actualJSeries p
  have hsN : (localFiniteSeriesHom s : LaurentSeries K) ^ N ≠ 0 :=
    pow_ne_zero N (squaredCoordinate_series_ne_zero (K := K) p hp)
  have hSR : localFiniteSeriesHom (s ^ N) * J = localFiniteSeriesHom R := by
    change localFiniteSeriesHom (s ^ N) *
      (localFiniteSeriesHom R / localFiniteSeriesHom s ^ N) = localFiniteSeriesHom R
    rw [map_pow, mul_comm]
    exact div_mul_cancel₀ (localFiniteSeriesHom (K := K) R) hsN
  have he := congrArg (LaurentSeries.derivative K) hSR
  rw [finite_series_derivative_product] at he
  have hd : LaurentSeries.derivative K (localFiniteSeriesHom R) = localFiniteSeriesHom (D R) :=
    (lowHFiniteSeries_derivative R).symm
  rw [hd] at he
  have hh := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (mixedHalfPower_homogeneous (K := K) p hp)
  simp only [map_add, map_mul, map_pow, map_zero] at hh
  change localFiniteSeriesHom s * localFiniteSeriesHom (D (s ^ N)) +
    localFiniteSeriesHom (LaurentPolynomial.C (1 / 10 : K)) * localFiniteSeriesHom s ^ N = 0 at hh
  change localFiniteSeriesHom s ^ (N + 1) * LaurentSeries.derivative K J =
    localFiniteSeriesHom (s * D R + LaurentPolynomial.C (1 / 10 : K) * R)
  simp only [map_add, map_mul, pow_succ]
  have hSR' : localFiniteSeriesHom s ^ N * J = localFiniteSeriesHom R := by
    simpa only [map_pow] using hSR
  simp only [map_pow] at he
  linear_combination localFiniteSeriesHom s * he - J * hh +
    localFiniteSeriesHom (LaurentPolynomial.C (1 / 10 : K)) * hSR'

/-- The original last odd term and both native even derivatives remain in the full j source. -/
theorem actual_J_original_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        (localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
          LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K)) =
      localFiniteSeriesHom
        (LaurentPolynomial.C (75 / 2 : K) *
          (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
              T (2 - (p : ℤ)) * (4 - 11 * T 1) ^ (p - 1) -
            T ((((p - 1) / 2 + 1 : ℕ) : ℤ))) +
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) * frobeniusPhi p *
            (-LaurentPolynomial.C (3 / 2 : K) *
              ((4 * T (-1) - 11) - T (-(((p - 1) / 2 : ℕ) : ℤ)) *
                WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * frobeniusPhi p) +
              LaurentPolynomial.C (1 / 2 : K) *
                ((4 * T 1 - 11) - WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
                  (4 * T (p : ℤ) - 11)))) := by
  rw [actual_J_series_cleared_derivative p hp, ← map_mul]
  exact congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (actual_R_cleared_source (K := K) p hp)

/-- The actual calL source identifies the entire original adjoint series. -/
theorem actual_adjoint_series_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualKSeries p : LaurentSeries K) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (calL p : K[T;T⁻¹]) : LaurentSeries K) + actualLambdaSeries p := by
  have he := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (calL_cleared_source (K := K) p hp)
  simp only [map_mul, map_sub, map_pow] at he
  have hd : localFiniteSeriesHom (D (calL p : K[T;T⁻¹])) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (calL p : K[T;T⁻¹]) : LaurentSeries K) :=
    lowHFiniteSeries_derivative (calL p)
  rw [hd] at he
  unfold actualKSeries actualLambdaSeries
  apply (div_eq_iff (Abar_series_ne_zero p hp)).mpr
  rw [add_mul, div_mul_cancel₀ _ (Abar_series_ne_zero p hp)]
  unfold actualAdjointNumerator
  simp only [Dsym, map_sub, map_mul, map_pow]
  linear_combination -he

/-- Jraw's full pole detector equals the residue of the same original j times Kj. -/
theorem actual_Jraw_series_detector (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualSimplePoleResidue.originPole
      (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
        (actualJSeries p * actualKSeries p : LaurentSeries K).coeff (-1) := by
  let N := (p - 1) / 2
  let S : LaurentSeries K := localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent
  let A : LaurentSeries K := localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent
  let R : LaurentSeries K := localFiniteSeriesHom
    (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p))
  let J : LaurentSeries K := localFiniteSeriesHom
    (mixedProduct p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p))
  let c : LaurentSeries K := localFiniteSeriesHom (LaurentPolynomial.C (2 / 5 : K))
  let L : LaurentSeries K := localFiniteSeriesHom (33 - 12 * T 1 : K[T;T⁻¹])
  let H : LaurentSeries K := localFiniteSeriesHom (LaurentPolynomial.C (2 * WPFiniteNC122.h p))
  let d : LaurentSeries K := localFiniteSeriesHom (Dsym p : K[T;T⁻¹])
  have hS : S ≠ 0 := squaredCoordinate_series_ne_zero p hp
  have hA : A ≠ 0 := Abar_series_ne_zero p hp
  have hc := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (mixedProduct_consistency (K := K) p hp
      (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p))
  simp only [map_mul, map_pow] at hc
  change S ^ N * J = d * R at hc
  have hAdj : localFiniteSeriesHom (actualAdjointNumerator p : K[T;T⁻¹]) =
      c * L * d - H * S ^ N := by
    dsimp only [c, L, d, H, S, N]
    simp only [actualAdjointNumerator, map_sub, map_mul, map_pow]
  have hNum : localFiniteSeriesHom
      (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      c * L * J - H * R := by
    dsimp only [c, L, H, J, R]
    simp only [mixedJNumerator, map_sub, map_mul]
  have he : (actualJSeries p * actualKSeries p : LaurentSeries K) =
      localFiniteSeriesHom
        (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) / A := by
    change (R / S ^ N) * (localFiniteSeriesHom (actualAdjointNumerator p) / A) =
      localFiniteSeriesHom
        (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) / A
    rw [hAdj, hNum]
    linear_combination (norm := (field_simp [hA, pow_ne_zero N hS]; ring))
      -(c * L / (S ^ N * A)) * hc
  rw [he]
  exact (local_Abar_quotient_residue p hp _).symm

/-- Integration by parts preserves the full odd series and the full simple-pole remainder. -/
theorem actual_Jraw_series_IBP (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualSimplePoleResidue.originPole
      (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      -(localFiniteSeriesHom (calL p : K[T;T⁻¹]) *
          LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K)).coeff (-1) +
        (actualJSeries (K := K) p * actualLambdaSeries p : LaurentSeries K).coeff (-1) := by
  rw [actual_Jraw_series_detector p hp, actual_adjoint_series_source p hp,
    mul_add, HahnSeries.coeff_add]
  have hi := lowH_finite_series_IBP (calL p : K[T;T⁻¹]) (actualJSeries (K := K) p)
  change (localFiniteSeriesHom (D (calL p : K[T;T⁻¹])) * actualJSeries (K := K) p).coeff (-1) +
    (localFiniteSeriesHom (calL p : K[T;T⁻¹]) *
      LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K)).coeff (-1) = 0 at hi
  have hd : localFiniteSeriesHom (D (calL p : K[T;T⁻¹])) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (calL p : K[T;T⁻¹]) : LaurentSeries K) :=
    lowHFiniteSeries_derivative (calL p)
  have hc : (actualJSeries (K := K) p * LaurentSeries.derivative K
      (localFiniteSeriesHom (calL p : K[T;T⁻¹]) : LaurentSeries K)).coeff (-1) =
      -(localFiniteSeriesHom (calL p : K[T;T⁻¹]) *
        LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K)).coeff (-1) := by
    rw [← hd]
    exact eq_neg_of_add_eq_zero_left (by simpa only [mul_comm] using hi)
  rw [hc]

/-- The original odd density, log term and actual native derivative split the full j. -/
theorem actual_J_series_odd_log_split (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K) =
      actualOddSeries p - localFiniteSeriesHom (frobeniusPhi p) * actualLogSeries +
        localFiniteSeriesHom (frobeniusPhi p) *
          localFiniteSeriesHom (LaurentPolynomial.C (1 / 3 : K)) *
            LaurentSeries.derivative K
              (localFiniteSeriesHom (actualAK p : K[X]).toLaurent : LaurentSeries K) := by
  let N := (p - 1) / 2
  let S : LaurentSeries K := localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent
  let A : LaurentSeries K := localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent
  let W : LaurentSeries K := localFiniteSeriesHom (4 - 11 * T 1)
  have hS : S ≠ 0 := squaredCoordinate_series_ne_zero p hp
  have hA : A ≠ 0 := Abar_series_ne_zero p hp
  have hW : W ≠ 0 := oddLinear_series_ne_zero p hp
  have he := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (actual_J_full_odd_log_source (K := K) p hp)
  simp only [map_mul, map_sub, map_add, map_pow] at he
  have hWsource : localFiniteSeriesHom (4 : K[T;T⁻¹]) -
      localFiniteSeriesHom (11 : K[T;T⁻¹]) * localFiniteSeriesHom (T 1) = W := by
    dsimp only [W]
    rw [map_sub, map_mul]
  simp only [hWsource] at he
  have hj := actual_J_series_cleared_derivative (K := K) p hp
  simp only [map_add, map_mul] at hj
  have hdA : localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (actualAK p : K[X]).toLaurent : LaurentSeries K) :=
    lowHFiniteSeries_derivative (actualAK p : K[X]).toLaurent
  rw [← hj, hdA] at he
  unfold actualOddSeries actualLogSeries
  change LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K) =
    localFiniteSeriesHom (oddDensityCleared p) / (S ^ (N + 1) * A) -
      localFiniteSeriesHom (frobeniusPhi p) * (localFiniteSeriesHom oddLogCleared / (S * W)) +
        localFiniteSeriesHom (frobeniusPhi p) * localFiniteSeriesHom (LaurentPolynomial.C (1 / 3 : K)) *
          LaurentSeries.derivative K
            (localFiniteSeriesHom (actualAK p : K[X]).toLaurent : LaurentSeries K)
  change A * (S ^ (N + 1) *
      LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K)) * W =
    localFiniteSeriesHom (oddDensityCleared p) * W -
      S ^ N * localFiniteSeriesHom (frobeniusPhi p) * localFiniteSeriesHom oddLogCleared * A +
        S ^ (N + 1) * localFiniteSeriesHom (frobeniusPhi p) *
          localFiniteSeriesHom (LaurentPolynomial.C (1 / 3 : K)) *
            (A * LaurentSeries.derivative K
              (localFiniteSeriesHom (actualAK p : K[X]).toLaurent : LaurentSeries K)) * W at he
  simp only [pow_succ] at he ⊢
  linear_combination (norm := (field_simp [hA, hS, hW, pow_ne_zero N hS]; ring))
    (1 / (A * (S ^ N * S) * W)) * he

/-- The entire calL*phi*dlog(Tvee) term has its explicit actual Laurent carrier. -/
theorem actual_calL_log_series_carrier (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (calL p : K[T;T⁻¹]) * localFiniteSeriesHom (frobeniusPhi p) *
      actualLogSeries = localFiniteSeriesHom (oddLogLaurentCarrier p) := by
  have he := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (actual_calL_log_Laurent_source (K := K) p hp)
  simp only [map_mul] at he
  unfold actualLogSeries
  have hS := squaredCoordinate_series_ne_zero (K := K) p hp
  have hW := oddLinear_series_ne_zero (K := K) p hp
  have hSW := mul_ne_zero hS hW
  calc
    _ = (localFiniteSeriesHom (calL p) * localFiniteSeriesHom (frobeniusPhi p) *
        localFiniteSeriesHom oddLogCleared) /
          (localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent *
            localFiniteSeriesHom (4 - 11 * T 1)) := by ring
    _ = _ := (div_eq_iff hSW).mpr (by linear_combination -he)

end WPFieldAssembly.NativeJointSuccessorJSeries
