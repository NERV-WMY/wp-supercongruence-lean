import WPFieldAssembly.NativeJointSuccessorOddResidues
import WPFieldAssembly.NativeJointSuccessorAdjointResidues
import WPFieldAssembly.NativeJointSuccessorPrimitiveEnds
import WPFieldAssembly.ScalarFinalSuccessorUniversalEndDensity
import WPFieldAssembly.ActualBpairNativeTail
import WPFieldAssembly.NativeClosureMixedJ

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries

namespace WPFieldAssembly.NativeJointSuccessorEvenResidues

open ActualBpairContraction ActualBpairNativeTail ActualCubicNativeSource
open ActualSimplePoleResidue ActualBpairLowHLocalPole GreenLaurentOperators WPFiniteLaurentDifferential
open NativeClosureMixedSource NativeJointSuccessorOddSource
open NativeJointSuccessorMixedPrimitive NativeJointSuccessorJSeries
open NativeJointSuccessorOddResidues NativeJointSuccessorAdjointResidues
open NativeJointSuccessorPrimitiveEnds NativeJointSuccessorProductResidues

variable {K : Type*} [Field K]
set_option maxHeartbeats 3000000

private theorem finite_series_injective :
    Function.Injective (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) := by
  intro F G he
  ext j
  exact congrArg (fun Q : LaurentSeries K => Q.coeff j) he

private theorem squared_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ≠ 0 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  intro hz
  have hL := finite_series_injective (hz.trans (map_zero _).symm)
  have hP := Polynomial.toLaurent_injective (hL.trans (map_zero _).symm)
  have hc := congrArg (fun P : K[X] => P.coeff 1) hP
  have he : (WPFiniteWSource.squaredCoordinate : K[X]).coeff 1 = (5 : K)⁻¹ := by
    simp [WPFiniteWSource.squaredCoordinate, Polynomial.coeff_one]
  rw [he, Polynomial.coeff_zero] at hc
  exact inv_ne_zero h5 hc

private theorem trunc_of_strict_negative (F : K[T;T⁻¹])
    (hF : ∀ j : ℤ, 0 ≤ j → F.coeff j = 0) : trunc F = 0 := by
  ext j
  rw [WPFiniteJWeightedResidue.trunc_coeff, Polynomial.coeff_zero]
  exact hF _ (by omega)

private theorem trunc_negative_shift (n : ℕ) (F : K[T;T⁻¹])
    (hF : Above F ((n : ℤ) - 1)) : trunc (T (-(n : ℤ)) * F) = 0 := by
  apply trunc_of_strict_negative
  intro j hj
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-(n : ℤ)) j F
  simp only [map_one, one_mul] at hs
  rw [hs]
  exact hF _ (by omega)

private theorem pole_negative_shift (n : ℕ) (F : K[T;T⁻¹])
    (hF : Above F ((n : ℤ) - 1)) (c : K) (hc : c ≠ 0) :
    (DD c c⁻¹ (T (-(n : ℤ)) * F)).coeff (-1) =
      -c ^ (-(n : ℤ)) * ev c hc F := by
  rw [endProduct_pole_evaluation _ c hc, trunc_negative_shift n F hF, eval_zero,
    map_mul]
  have ht : ev c hc (T (-(n : ℤ)) : K[T;T⁻¹]) = c ^ (-(n : ℤ)) := by
    simp [ev]
  rw [ht]
  ring

private theorem origin_nonnegative (F : K[T;T⁻¹])
    (hF : ∀ j : ℤ, j < 0 → F.coeff j = 0) : originPole F = 0 := by
  have ht : trunc (invert F) = Polynomial.C (F.coeff 0) := by
    ext j
    rw [WPFiniteJWeightedResidue.trunc_coeff, invert_apply, coeff_C]
    by_cases hj : j = 0
    · subst j
      simp
    · rw [if_neg hj, hF _ (by omega)]
  rw [originPole_trunc_inverse, ht, eval_C, eval_C, sub_self, zero_div]

private theorem calL_trunc (p : ℕ) :
    trunc (calL p : K[T;T⁻¹]) = calLPositive p - Polynomial.C
      (ev (-1) (neg_ne_zero.mpr one_ne_zero) (calLUnnormalized p)) := by
  have hn : trunc (calLNegative p : K[T;T⁻¹]) = 0 := by
    rw [calLNegative, neg_mul, map_neg, WPFiniteJWeightedResidue.trunc_C_mul]
    have htwo : (2 : K[T;T⁻¹]) = LaurentPolynomial.C (2 : K) := (map_ofNat _ 2).symm
    have hthree : (3 : K[T;T⁻¹]) = LaurentPolynomial.C (3 : K) := (map_ofNat _ 3).symm
    simp only [map_sub, map_add, htwo, hthree, WPFiniteJWeightedResidue.trunc_C_mul,
      WPFiniteJWeightedResidue.trunc_invert, coeff_zero_eq_eval_zero,
      branchHPolynomial_zero, map_zero, mul_zero, add_zero, sub_zero, neg_zero]
  have hC (a : K) : trunc (LaurentPolynomial.C a : K[T;T⁻¹]) = Polynomial.C a := by
    simpa only [Polynomial.toLaurent_C] using trunc_toLaurent (Polynomial.C a)
  simp only [calL, map_sub, calLUnnormalized, map_add, trunc_toLaurent,
    hn, add_zero, hC]

private theorem calL_positive_zero (p : ℕ) : (calLPositive p : K[X]).eval 0 = 0 := by
  simp [calLPositive, branchHPolynomial_zero]

private theorem calL_zero (p : ℕ) : (calL p : K[T;T⁻¹]).coeff 0 =
    -ev (-1) (neg_ne_zero.mpr one_ne_zero) (calLUnnormalized p) := by
  have he := congrArg (fun P : K[X] => P.coeff 0) (calL_trunc (K := K) p)
  rw [WPFiniteJWeightedResidue.trunc_coeff, Nat.cast_zero,
    Polynomial.coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero,
    calL_positive_zero, zero_sub] at he
  exact he

private theorem calL_upper (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    Above (calL p : K[T;T⁻¹]) ((p : ℤ) - 1) := by
  intro j hj
  exact calL_coeff_outside p hp j (Or.inr (by omega))

private theorem calL_phi_pole (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (c : K) (hc : c ≠ 0) :
    (DD c c⁻¹ (calL p * frobeniusPhi p : K[T;T⁻¹])).coeff (-1) =
      -4 * c ^ (-(p : ℤ)) * ev c hc (calL p) +
        11 * (ev c hc (calL p) - (trunc (calL p)).eval c) := by
  have hs : (calL p * frobeniusPhi p : K[T;T⁻¹]) =
      LaurentPolynomial.C (4 : K) * (T (-(p : ℤ)) * calL p) -
        LaurentPolynomial.C (11 : K) * calL p := by
    simp only [frobeniusPhi, map_ofNat]
    ring
  have hm (a : K) (F : K[T;T⁻¹]) :
      DD c c⁻¹ (LaurentPolynomial.C a * F) = LaurentPolynomial.C a * DD c c⁻¹ F := by
    simpa only [LaurentPolynomial.smul_eq_C_mul] using (DD c c⁻¹).map_smul a F
  rw [hs, map_sub, hm, hm, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    C_mul_coeff, C_mul_coeff, pole_negative_shift p _ (calL_upper p hp) c hc,
    endProduct_pole_evaluation _ c hc]
  ring

/-- The full original j retains the reciprocal even log, the native log and its nonzero constant. -/
theorem actual_J_even_series_split (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualJSeries p : LaurentSeries K) = actualOddQuotientSeries p +
      localFiniteSeriesHom (frobeniusPhi p *
        (invert (actualAK p : K[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p) +
            LaurentPolynomial.C (1 / 3 : K) * (actualAK p).toLaurent)) := by
  unfold actualJSeries actualOddQuotientSeries mixedResidual mixedEvenSource
  simp only [map_add, map_mul, map_pow]
  field_simp [squared_series_ne_zero p hp]

/-- The full even part is extracted only after the original odd source is separated. -/
theorem actual_Jraw_even_series_reduction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      (actualOddQuotientSeries p * actualLambdaSeries p -
        localFiniteSeriesHom (calL p) * actualOddSeries p : LaurentSeries K).coeff (-1) +
      (oddLogLaurentCarrier p : K[T;T⁻¹]).coeff (-1) +
      originPole (frobeniusPhi p *
        (invert (actualAK p : K[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) * clearedLambda p) +
      (1 / 3 : K) * originPole
        (frobeniusPhi p * (actualAK p : K[X]).toLaurent * clearedLambda p) -
      (1 / 3 : K) * (calL p * frobeniusPhi p * D (actualAK p : K[X]).toLaurent).coeff (-1) := by
  rw [actual_Jraw_series_IBP p hp, actual_J_series_odd_log_split p hp,
    actual_J_even_series_split p hp]
  have hL : (localFiniteSeriesHom (frobeniusPhi p *
      (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p) +
          LaurentPolynomial.C (1 / 3 : K) * (actualAK p).toLaurent)) *
        actualLambdaSeries p : LaurentSeries K).coeff (-1) =
      originPole (frobeniusPhi p *
        (invert (actualAK p : K[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p) +
            LaurentPolynomial.C (1 / 3 : K) * (actualAK p).toLaurent) * clearedLambda p) := by
    unfold actualLambdaSeries
    rw [← mul_div_assoc, ← map_mul, local_Abar_quotient_residue p hp]
  have hs := actual_calL_log_series_carrier (K := K) p hp
  have hd : localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent) =
      LaurentSeries.derivative K (localFiniteSeriesHom (actualAK p : K[X]).toLaurent) :=
    lowHFiniteSeries_derivative (actualAK p : K[X]).toLaurent
  have hm : localFiniteSeriesHom (calL p) * localFiniteSeriesHom (frobeniusPhi p) *
      localFiniteSeriesHom (LaurentPolynomial.C (1 / 3 : K)) *
        LaurentSeries.derivative K (localFiniteSeriesHom (actualAK p : K[X]).toLaurent) =
      localFiniteSeriesHom (LaurentPolynomial.C (1 / 3 : K) *
        (calL p * frobeniusPhi p * D (actualAK p : K[X]).toLaurent)) := by
    rw [← hd]
    simp only [map_mul]
    ring
  rw [add_mul, HahnSeries.coeff_add, hL]
  rw [mul_add, mul_sub, HahnSeries.coeff_add, HahnSeries.coeff_sub]
  rw [← mul_assoc, hs, localFiniteSeries_coeff]
  rw [← mul_assoc, ← mul_assoc, hm, localFiniteSeries_coeff, C_mul_coeff]
  rw [HahnSeries.coeff_sub]
  have he : frobeniusPhi p *
      (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p) +
          LaurentPolynomial.C (1 / 3 : K) * (actualAK p).toLaurent) * clearedLambda p =
      frobeniusPhi p * (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) * clearedLambda p +
      LaurentPolynomial.C (1 / 3 : K) *
        (frobeniusPhi p * (actualAK p : K[X]).toLaurent * clearedLambda p) := by ring
  rw [he, originPole_add, originPole_C_mul]
  ring

private theorem Lambda_whole (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (F : K[T;T⁻¹]) :
    originPole (F * clearedLambda p) =
      (-2 * kappa p / 15) * F.coeff 0 -
        (4 * WPFiniteNC122.h p / 15) * (DD (1 / 4 : K) 4 F).coeff (-1) +
          (WPFiniteNC122.h p / 15) * (DD (4 : K) (1 / 4) F).coeff (-1) := by
  have hs : F * clearedLambda p =
      LaurentPolynomial.C (-2 * kappa p / 15) *
        ((WPFiniteZSource.Abar : K[X]).toLaurent * (T (-1) * F)) +
      (LaurentPolynomial.C (-21 * WPFiniteNC122.h p / 5) +
        LaurentPolynomial.C (4 * WPFiniteNC122.h p / 5) * T 1) * F := by
    have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
      (Finset.mem_Ico.mpr (by omega))
    have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
      (Finset.mem_Ico.mpr (by omega))
    have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
      (Finset.mem_Ico.mpr (by omega))
    have ha : (16 * WPFiniteNC122.h p / 15 - 4 * WPFiniteNC122.h p / 15 : K) =
        4 * WPFiniteNC122.h p / 5 := by field_simp [h5, h15]; ring
    have hb : ((4 * WPFiniteNC122.h p / 15) * (1 / 4) -
        4 * (16 * WPFiniteNC122.h p / 15) : K) = -21 * WPFiniteNC122.h p / 5 := by
      field_simp [h4, h5, h15]
      ring
    have haC := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) ha
    have hbC := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hb
    simp only [map_sub] at haC
    simp only [map_sub, map_mul, map_ofNat] at hbC
    unfold clearedLambda
    linear_combination F * T 1 * haC + F * hbC
  have hh := WPFiniteJCarrier.shifted_coeff (1 : K) (-1) (-1) F
  simp only [map_one, one_mul, sub_self] at hh
  rw [hs, originPole_add, originPole_C_mul, originPole_cleared p hp, hh,
    endProduct_affine_density p hp]
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h4, h5, h15]
  ring

/-- The reciprocal even phase keeps the genuine nonzero proper ends and its actual infinity value. -/
theorem actual_reciprocal_even_Lambda_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole (frobeniusPhi p *
      (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) * clearedLambda p) =
      -2 * WPFiniteNC122.h p * WPFiniteNC122.q p -
        11 * (-2 * kappa p / 15 - WPFiniteNC122.h p / 5) *
          ((actualAK p : K[X]).eval 0 - WPFiniteNC122.q p + WPFiniteNC122.h p) := by
  let F : K[T;T⁻¹] := frobeniusPhi p *
    (invert (actualAK p : K[X]).toLaurent -
      LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1 / 4 : K) ≠ 0 := one_div_ne_zero h4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by
    have hfour : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
    rw [one_div, inv_pow, hfour]
  have hbp : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hneg : Above F 0 := by
    have hT : Above (T (-(p : ℤ)) : K[T;T⁻¹]) (-(p : ℤ)) := by
      simpa only [map_one, one_mul] using Above_monomial (1 : K) (-(p : ℤ))
    have hphi : Above (frobeniusPhi p : K[T;T⁻¹]) 0 := by
      dsimp only [frobeniusPhi]
      exact Above_mono (Above_sub (Above_C_mul hT 4) (Above_C 11)) (by omega)
    dsimp only [F]
    simpa only [max_self, add_zero] using Above_mul hphi
      (Above_sub (Above_invert_toLaurent _) (Above_C _))
  have ht : trunc F = Polynomial.C (F.coeff 0) := by
    ext j
    rw [WPFiniteJWeightedResidue.trunc_coeff, coeff_C]
    by_cases hj : j = 0
    · subst j
      simp
    · rw [if_neg hj, hneg _ (by omega)]
  have hF0 : F.coeff 0 = -11 *
      ((actualAK p : K[X]).eval 0 - WPFiniteNC122.q p + WPFiniteNC122.h p) := by
    have hshift := WPFiniteJCarrier.shifted_coeff (4 : K) (-(p : ℤ)) 0
      (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))
    have hz : (invert (actualAK p : K[X]).toLaurent -
      LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)).coeff (p : ℤ) = 0 :=
      (Above_sub (Above_invert_toLaurent _) (Above_C _)) _ (by omega)
    simp only [zero_sub, neg_neg, hz, mul_zero] at hshift
    have he : F = LaurentPolynomial.C (4 : K) * (T (-(p : ℤ)) *
        (invert (actualAK p : K[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))) -
        LaurentPolynomial.C (11 : K) * (invert (actualAK p : K[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) := by
      simp only [F, frobeniusPhi, map_ofNat]
      ring
    rw [he, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, ← mul_assoc, hshift]
    have hA0 : ((actualAK p : K[X]).toLaurent).coeff (0 : ℤ) = (actualAK p).eval 0 := by
      simpa only [Nat.cast_zero, coeff_zero_eq_eval_zero] using
        WPFiniteJCarrier.toLaurent_coeff_nat (actualAK p : K[X]) 0
    simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      C_mul_coeff, invert_apply, neg_zero, hA0, LaurentPolynomial.C_apply, if_true]
    ring
  have hev (c : K) (hc : c ≠ 0) : ev c hc F =
      (4 * c ^ (-(p : ℤ)) - 11) *
        ((actualAK p : K[X]).eval c⁻¹ - WPFiniteNC122.q p + WPFiniteNC122.h p) := by
    dsimp only [F, frobeniusPhi]
    simp [ev, map_ofNat, WPFiniteJWeightedResidue.inversion_eval, sub_eq_add_neg]
    left
    ring
  obtain ⟨hAa, hAb⟩ := actual_AK_endpoints (K := K) p hp
  have heva : ev (1 / 4 : K) ha F = -5 * WPFiniteNC122.q p := by
    rw [hev, zpow_neg, zpow_natCast, hap, one_div, inv_inv, hAb]
    ring
  have hevb : ev (4 : K) h4 F = 10 * WPFiniteNC122.q p := by
    rw [hev, zpow_neg, zpow_natCast, hbp, ← one_div (4 : K), hAa]
    field_simp [h4]
    ring
  rw [show frobeniusPhi p * (invert (actualAK p : K[X]).toLaurent -
    LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) = F from rfl,
    Lambda_whole p hp]
  have hrA := endProduct_pole_evaluation F (1 / 4 : K) ha
  have hrB := endProduct_pole_evaluation F (4 : K) h4
  rw [inv_div, div_one] at hrA
  simp only [← one_div (4 : K)] at hrB
  rw [ht, eval_C, heva, hF0] at hrA
  rw [ht, eval_C, hevb, hF0] at hrB
  rw [hrA, hrB, hF0]
  field_simp [h4, h5, h15]
  ring

/-- The original inclusive p band contributes its origin coefficient before any derivative is taken. -/
theorem actual_native_even_Lambda_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    originPole (frobeniusPhi p * (actualAK p : K[X]).toLaurent * clearedLambda p) =
      (-2 * kappa p / 15) *
        (-16 * (WPFifthEntropy.C p u + WPFiniteNC122.q p) / 5 -
          11 * (actualAK p : K[X]).eval 0) -
      21 * WPFiniteNC122.h p ^ 2 / 5 -
        32 * WPFiniteNC122.h p * WPFiniteNC122.q p / 25 +
          24 * WPFiniteNC122.h p * (WPFiniteInversion.integerFermatQuotient p 3 : K) / 25 := by
  let F : K[T;T⁻¹] := frobeniusPhi p * (actualAK p : K[X]).toLaurent
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1 / 4 : K) ≠ 0 := one_div_ne_zero h4
  have hL : Above (nativeL p : K[X]).toLaurent ((p : ℤ) - 1) := by
    exact Above_mono (Above_toLaurent _ _ (nativeL_degree p hp)) (by omega)
  have hsource : F = LaurentPolynomial.C (4 : K) *
      (nativeB p).toLaurent + LaurentPolynomial.C (4 : K) *
        (T (-(p : ℤ)) * (nativeL p).toLaurent) -
          LaurentPolynomial.C (11 : K) * (actualAK p).toLaurent := by
    dsimp only [F, frobeniusPhi]
    rw [actual_AK_phase_source p hp]
    simp only [map_add, map_mul, Polynomial.toLaurent_X_pow, map_ofNat]
    have ht : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
      rw [← T_add, neg_add_cancel, T_zero]
    linear_combination 4 * (nativeB p).toLaurent * ht
  have htrunc : trunc F = Polynomial.C (4 : K) * nativeB p -
      Polynomial.C (11 : K) * actualAK p := by
    rw [hsource]
    simp only [map_add, map_sub, WPFiniteJWeightedResidue.trunc_C_mul,
      trunc_toLaurent, trunc_negative_shift p _ hL, mul_zero, add_zero]
  have hF0 : F.coeff 0 =
      -16 * (WPFifthEntropy.C p u + WPFiniteNC122.q p) / 5 -
        11 * (actualAK p : K[X]).eval 0 := by
    have hh := congrArg (fun P : K[X] => P.coeff 0) htrunc
    rw [WPFiniteJWeightedResidue.trunc_coeff, Nat.cast_zero,
      Polynomial.coeff_sub, coeff_C_mul, coeff_C_mul,
      nativeB_origin_fifth p hp u hu, coeff_zero_eq_eval_zero] at hh
    linear_combination hh
  have hev (c : K) (hc : c ≠ 0) : ev c hc F =
      (4 * c ^ (-(p : ℤ)) - 11) * (actualAK p : K[X]).eval c := by
    simp [F, frobeniusPhi, ev, map_ofNat, LaurentPolynomial.eval₂_toLaurent]
  have hpowa : (1 / 4 : K) ^ p = 1 / 4 := by
    have hfour : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
    rw [one_div, inv_pow, hfour]
  have hpowb : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have rho (c : K) (hc : c ≠ 0) :
      (DD c c⁻¹ F).coeff (-1) =
        -4 * c ^ (-(p : ℤ)) * (nativeL p : K[X]).eval c := by
    have he := congrArg (fun P : K[X] => P.eval c) (actual_AK_phase_source (K := K) p hp)
    simp only [eval_add, eval_mul, eval_pow, eval_X] at he
    rw [endProduct_pole_evaluation F c hc, htrunc, eval_sub]
    simp only [eval_mul, eval_C]
    rw [hev, zpow_neg, zpow_natCast]
    linear_combination (norm := (field_simp [pow_ne_zero p hc]; ring))
      (-4 / c ^ p) * he
  have hrA := rho (1 / 4 : K) ha
  have hrB := rho (4 : K) h4
  rw [inv_div, div_one] at hrA
  simp only [← one_div (4 : K)] at hrB
  rw [zpow_neg, zpow_natCast, hpowa, one_div, inv_inv] at hrA
  rw [zpow_neg, zpow_natCast, hpowb] at hrB
  obtain ⟨hla, hlb⟩ := nativeL_endpoints (K := K) p hp
  simp only [one_div] at hla
  rw [hla] at hrA
  rw [hlb] at hrB
  have hrA' : (DD (1 / 4 : K) 4 F).coeff (-1) =
      -4 * 4 * (-WPFiniteNC122.h p - nativeTau p / 4) := by
    simpa only [one_div] using hrA
  rw [show frobeniusPhi p * (actualAK p : K[X]).toLaurent = F from rfl,
    Lambda_whole p hp, hrA', hrB, hF0]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero 2 h5
  unfold nativeTau WPFiniteNC122.h WPFiniteNC122.q
  field_simp [h2, h4, h5, h15, h25]
  ring

private theorem linear_series_ne_zero (c : K) :
    localFiniteSeriesHom (T 1 - LaurentPolynomial.C c : K[T;T⁻¹]) ≠ 0 := by
  intro hz
  have hc := congrArg (fun Q : LaurentSeries K => Q.coeff 1) hz
  simp only [localFiniteSeries_coeff, HahnSeries.coeff_zero,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    LaurentPolynomial.T_apply, LaurentPolynomial.C_apply,
    if_neg (by omega : (1 : ℤ) ≠ 0), sub_zero] at hc
  exact one_ne_zero hc

private theorem log_series_pole_decomposition (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (actualLogSeries : LaurentSeries K) =
      localFiniteSeriesHom (LaurentPolynomial.C (1 / 2 : K)) /
        localFiniteSeriesHom (T 1 + 1 : K[T;T⁻¹]) +
      1 / localFiniteSeriesHom (T 1 - LaurentPolynomial.C (4 / 11 : K) : K[T;T⁻¹]) -
      localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) *
        localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) := by
  let σ : K →+* LaurentSeries K := algebraMap K (LaurentSeries K)
  let x : LaurentSeries K := localFiniteSeriesHom (T 1 : K[T;T⁻¹])
  let xi : LaurentSeries K := localFiniteSeriesHom (T (-1) : K[T;T⁻¹])
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h11 : (11 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 11
    (Finset.mem_Ico.mpr (by omega))
  have h2S : (2 : LaurentSeries K) ≠ 0 := by simpa only [map_ofNat] using ((_root_.map_ne_zero σ).mpr h2)
  have h5S : (5 : LaurentSeries K) ≠ 0 := by simpa only [map_ofNat] using ((_root_.map_ne_zero σ).mpr h5)
  have h10S : (10 : LaurentSeries K) ≠ 0 := by
    rw [show (10 : LaurentSeries K) = 2 * 5 by ring]
    exact mul_ne_zero h2S h5S
  have h11S : (11 : LaurentSeries K) ≠ 0 := by simpa only [map_ofNat] using ((_root_.map_ne_zero σ).mpr h11)
  have hx : x * xi = 1 := by
    dsimp only [x, xi]
    rw [← map_mul, ← T_add, show (1 : ℤ) + -1 = 0 by omega, T_zero, map_one]
  have hs : x + 1 ≠ 0 := by
    simpa only [map_sub, map_add, map_one, map_neg, localFiniteSeries_C,
      map_one, sub_neg_eq_add, x] using linear_series_ne_zero (K := K) (-1)
  have hv : x - 4 / 11 ≠ 0 := by
    simpa only [map_sub, localFiniteSeries_C, map_div₀, map_ofNat, x]
      using linear_series_ne_zero (K := K) (4 / 11)
  have hw : (4 - 11 * x : LaurentSeries K) ≠ 0 := by
    have he : 4 - 11 * x = -11 * (x - 4 / 11) := by field_simp [h11S]; ring
    rw [he]
    exact mul_ne_zero (neg_ne_zero.mpr h11S) hv
  have hC (a : K) : localFiniteSeriesHom (LaurentPolynomial.C a) = σ a :=
    localFiniteSeries_C a
  unfold actualLogSeries oddLogCleared
  simp only [WPFiniteWSource.squaredCoordinate, map_mul, map_add,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, map_one,
    map_sub, map_ofNat, hC, map_div₀, map_inv₀]
  rw [← one_div (5 : LaurentSeries K)]
  change ((3 / 10 : LaurentSeries K) * xi * (x - 4)) /
    ((1 / 5 : LaurentSeries K) * (x + 1) * (4 - 11 * x)) =
      (1 / 2 : LaurentSeries K) / (x + 1) + 1 / (x - 4 / 11) - (3 / 2) * xi
  have hcore : (3 / 2 : LaurentSeries K) * xi * (x - 4) =
      (1 / 2 : LaurentSeries K) * (4 - 11 * x) - 11 * (x + 1) -
        (3 / 2 : LaurentSeries K) * xi * (x + 1) * (4 - 11 * x) := by
    linear_combination (norm := (field_simp [h2S]; ring))
      -(3 / 2 : LaurentSeries K) * (11 * x + 6) * hx
  calc
    _ = ((3 / 2 : LaurentSeries K) * xi * (x - 4)) /
        ((x + 1) * (4 - 11 * x)) := by
      field_simp [h2S, h5S, h10S, hs, hw]
      ring
    _ = ((1 / 2 : LaurentSeries K) * (4 - 11 * x) - 11 * (x + 1) -
        (3 / 2 : LaurentSeries K) * xi * (x + 1) * (4 - 11 * x)) /
          ((x + 1) * (4 - 11 * x)) := by rw [hcore]
    _ = _ := by
      have hh : (11 * x - 4 : LaurentSeries K) ≠ 0 := by
        simpa only [neg_sub] using neg_ne_zero.mpr hw
      field_simp [h2S, h11S, hs, hv, hw, hh]
      ring

/-- All added, branch and origin poles are extracted together from the actual normalized primitive. -/
theorem actual_calL_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (oddLogLaurentCarrier p : K[T;T⁻¹]).coeff (-1) =
      -11 * (calLPositive p : K[X]).eval (4 / 11) -
        (11 / 2 : K) * (calLPositive p : K[X]).eval (-1) := by
  let F : K[T;T⁻¹] := calL p * frobeniusPhi p
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h11 : (11 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 11
    (Finset.mem_Ico.mpr (by omega))
  have hv : (4 / 11 : K) ≠ 0 := div_ne_zero h4 h11
  have hvp : (4 / 11 : K) ^ p = 4 / 11 := by
    have hf : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
    have he : (11 : K) ^ p = 11 := WPFiniteField.natCast_pow_char p 11
    rw [div_pow, hf, he]
  have hphi0 : F.coeff 0 = -11 * (calL p : K[T;T⁻¹]).coeff 0 := by
    have hp0 := calL_coeff_outside (K := K) p hp (p : ℤ) (Or.inr (by omega))
    have hh := WPFiniteJCarrier.shifted_coeff (4 : K) (-(p : ℤ)) 0 (calL p)
    simp only [zero_sub, neg_neg, hp0, mul_zero] at hh
    have he : F = LaurentPolynomial.C (4 : K) * (T (-(p : ℤ)) * calL p) -
        LaurentPolynomial.C (11 : K) * calL p := by
      simp only [F, frobeniusPhi, map_ofNat]
      ring
    rw [he, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, ← mul_assoc, hh, C_mul_coeff]
    ring
  have hneg := calL_phi_pole (K := K) p hp (-1) (neg_ne_zero.mpr one_ne_zero)
  rw [calL_branch_origin p, mul_zero, zero_add, zero_sub, calL_trunc,
    eval_sub, eval_C] at hneg
  have hadd := calL_phi_pole (K := K) p hp (4 / 11 : K) hv
  rw [zpow_neg, zpow_natCast, hvp, calL_trunc, eval_sub, eval_C] at hadd
  have hadded : (DD (4 / 11 : K) (4 / 11)⁻¹ F).coeff (-1) =
      -11 * ((calLPositive p : K[X]).eval (4 / 11) -
        ev (-1) (neg_ne_zero.mpr one_ne_zero) (calLUnnormalized p)) := by
    dsimp only [F]
    linear_combination (norm := (field_simp [h4, h11]; ring)) hadd
  have he : localFiniteSeriesHom (calL p) * localFiniteSeriesHom (frobeniusPhi p) *
      actualLogSeries = localFiniteSeriesHom (F : K[T;T⁻¹]) * actualLogSeries := by
    simp only [F, map_mul]
  have hc := congrArg (fun Q : LaurentSeries K => Q.coeff (-1))
    (actual_calL_log_series_carrier (K := K) p hp)
  rw [he, log_series_pole_decomposition p hp] at hc
  have hsource : localFiniteSeriesHom F *
      (localFiniteSeriesHom (LaurentPolynomial.C (1 / 2 : K)) /
        localFiniteSeriesHom (T 1 + 1 : K[T;T⁻¹]) +
      1 / localFiniteSeriesHom (T 1 - LaurentPolynomial.C (4 / 11 : K) : K[T;T⁻¹]) -
      localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) *
        localFiniteSeriesHom (T (-1) : K[T;T⁻¹])) =
      localFiniteSeriesHom (LaurentPolynomial.C (1 / 2 : K)) *
        (localFiniteSeriesHom F / localFiniteSeriesHom (T 1 + 1 : K[T;T⁻¹])) +
      localFiniteSeriesHom F /
        localFiniteSeriesHom (T 1 - LaurentPolynomial.C (4 / 11 : K) : K[T;T⁻¹]) -
      localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K) * (T (-1) * F)) := by
    simp only [map_mul]
    ring
  rw [hsource, HahnSeries.coeff_sub, HahnSeries.coeff_add,
    localFiniteSeries_C, LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, sub_zero, localFiniteSeries_coeff, C_mul_coeff] at hc
  have hm := WPFiniteJCarrier.shifted_coeff (1 : K) (-1) (-1) F
  simp only [map_one, one_mul, sub_self] at hm
  have hbranch := local_linear_quotient_residue (-1 : K)
    (neg_ne_zero.mpr one_ne_zero) F
  have hbranch' : (localFiniteSeriesHom F /
      localFiniteSeriesHom (T 1 + 1 : K[T;T⁻¹])).coeff (-1) =
      (DD (-1) (-1) F).coeff (-1) := by
    simpa only [map_add, map_one, localFiniteSeries_T, map_neg,
      sub_neg_eq_add, inv_neg, inv_one] using hbranch
  have hadd' : (localFiniteSeriesHom F /
      localFiniteSeriesHom (T 1 - LaurentPolynomial.C (4 / 11 : K))).coeff (-1) =
      (DD (4 / 11 : K) (4 / 11)⁻¹ F).coeff (-1) := by
    simpa only [map_sub, localFiniteSeries_T, localFiniteSeries_C] using
      local_linear_quotient_residue (4 / 11 : K) hv F
  rw [hbranch', hadd', hm,
    hadded, hphi0, calL_zero, localFiniteSeries_coeff] at hc
  change (1 / 2 : K) * _ + _ - (3 / 2 : K) * _ = _ at hc
  dsimp only [F] at hc
  simp only [inv_neg, inv_one] at hneg
  rw [hneg] at hc
  linear_combination (norm := (field_simp [h2]; ring)) -hc

private theorem calL_half_upper (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : Above (calL p *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) : K[T;T⁻¹])
        ((p : ℤ) - 1) := by
  have hL : Above (calL p : K[T;T⁻¹]) (((p - 1) / 2 - 1 : ℕ) : ℤ) := by
    intro j hj
    exact calL_coeff_outside p hp j (Or.inr hj)
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).natDegree ≤ 1 := by
    change (Polynomial.C (5 : K)⁻¹ * (X + 1)).natDegree ≤ 1
    exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  have hsN : Above (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) : K[T;T⁻¹])
      (((p - 1) / 2 : ℕ) : ℤ) := by
    simpa only [Nat.cast_one, mul_one] using Above_pow (Above_toLaurent _ 1 hs) ((p - 1) / 2)
  exact Above_mono (Above_mul hL hsN) (by omega)

private theorem calL_half_positive_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : originPole (T (p : ℤ) * calL p *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) : K[T;T⁻¹]) = 0 := by
  let F : K[T;T⁻¹] := calL p *
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)
  have hL : Above (invert (calL p : K[T;T⁻¹])) (((p - 1) / 2 - 2 : ℕ) : ℤ) := by
    intro j hj
    rw [invert_apply]
    exact calL_coeff_outside p hp (-j) (Or.inl (by omega))
  have hF : Above (invert F) (((p - 1) / 2 - 2 : ℕ) : ℤ) := by
    dsimp only [F]
    rw [map_mul, ← map_pow]
    exact Above_mul hL (Above_invert_toLaurent _)
  rw [mul_assoc]
  apply origin_nonnegative
  intro j hj
  have hh := WPFiniteJCarrier.shifted_coeff (1 : K) (p : ℤ) j F
  simp only [map_one, one_mul] at hh
  rw [hh]
  have hz := hF ((p : ℤ) - j) (by omega)
  simpa only [invert_apply, neg_sub] using hz

private theorem calL_half_negative_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : originPole (T (-(p : ℤ)) * calL p *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) : K[T;T⁻¹]) =
      (-4 * ev (1 / 4 : K) (one_div_ne_zero
        (WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega)))) (calL p) +
        ev (4 : K) (WPFiniteField.denominator_ne_zero p 4
          (Finset.mem_Ico.mpr (by omega))) (calL p) / 4) / 15 := by
  let F : K[T;T⁻¹] := calL p *
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1 / 4 : K) ≠ 0 := one_div_ne_zero h4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by
    have hfour : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
    rw [one_div, inv_pow, hfour]
  have hbp : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hsA : (WPFiniteWSource.squaredCoordinate : K[X]).eval (1 / 4) = 1 / 4 := by
    simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C, eval_add, eval_X, eval_one]
    field_simp [h4, h5]
    ring
  have hsB : (WPFiniteWSource.squaredCoordinate : K[X]).eval 4 = 1 := by
    simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C, eval_add, eval_X, eval_one]
    norm_num
    exact inv_mul_cancel₀ h5
  have haN : (1 / 4 : K) ^ ((p - 1) / 2) = 1 := by
    rw [one_div, inv_pow, WPFiniteWSource.four_half_power p hp, inv_one]
  have hev (c : K) (hc : c ≠ 0) : ev c hc F = ev c hc (calL p) *
      (WPFiniteWSource.squaredCoordinate : K[X]).eval c ^ ((p - 1) / 2) := by
    simp [F, ev, LaurentPolynomial.eval₂_toLaurent]
  have hA := pole_negative_shift p F (calL_half_upper p hp) (1 / 4 : K) ha
  have hB := pole_negative_shift p F (calL_half_upper p hp) (4 : K) h4
  rw [hev, hsA, haN, mul_one, zpow_neg, zpow_natCast, hap] at hA
  simp only [one_div, inv_inv] at hA
  rw [hev, hsB, one_pow, mul_one, zpow_neg, zpow_natCast, hbp] at hB
  simp only [← one_div (4 : K)] at hB
  rw [mul_assoc]
  change originPole (T (-(p : ℤ)) * F) = _
  have hA' : (DD (1 / 4 : K) 4 (T (-(p : ℤ)) * F)).coeff (-1) =
      -4 * ev (1 / 4 : K) ha (calL p) := by simpa only [one_div] using hA
  simp only [originPole, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hA', hB]
  ring

/-- The entire native derivative keeps all 0,p and reciprocal p phases until the unit-band extraction. -/
theorem actual_calL_native_derivative_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    -(1 / 3 : K) * (calL p * frobeniusPhi p * D (actualAK p : K[X]).toLaurent).coeff (-1) =
      (137 / 2 : K) * originPole (WPFiniteWSource.squaredCoordinate.toLaurent ^
        ((p - 1) / 2) * (calL p : K[T;T⁻¹])) +
      (8 / 15 : K) * ((calLPositive p : K[X]).eval (1 / 4) - (calLPositive p).eval 4) +
      (21 / 5 : K) * ev (1 / 4 : K) (one_div_ne_zero
        (WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))))
          (calLNegative p) +
      (13 / 10 : K) * ev (4 : K) (WPFiniteField.denominator_ne_zero p 4
        (Finset.mem_Ico.mpr (by omega))) (calLNegative p) := by
  let F : K[T;T⁻¹] := calL p *
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)
  let Lphi : K[T;T⁻¹] := calL p * frobeniusPhi p
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by ring]
    exact mul_ne_zero h2 h5
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have ha : (1 / 4 : K) ≠ 0 := one_div_ne_zero h4
  have hpowb : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hpowa : (1 / 4 : K) ^ p = 1 / 4 := by
    rw [one_div, inv_pow, hpowb]
  have ht : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hphase : (frobeniusPhi p * (4 * T (p : ℤ) - 11) : K[T;T⁻¹]) =
      LaurentPolynomial.C (137 : K) - LaurentPolynomial.C (44 : K) * T (p : ℤ) -
        LaurentPolynomial.C (44 : K) * T (-(p : ℤ)) := by
    simp only [frobeniusPhi, map_ofNat]
    linear_combination 16 * ht
  have he : (WPFiniteZSource.Abar : K[X]).toLaurent *
      (LaurentPolynomial.C (-(1 / 3 : K)) *
        (calL p * frobeniusPhi p * D (actualAK p : K[X]).toLaurent)) =
      LaurentPolynomial.C (1 / 6 : K) * ((33 - 12 * T 1) * Lphi) +
        LaurentPolynomial.C (137 / 2 : K) * F -
          LaurentPolynomial.C (22 : K) * (T (p : ℤ) * F) -
            LaurentPolynomial.C (22 : K) * (T (-(p : ℤ)) * F) := by
    have hD := actual_AK_cleared_derivative (K := K) p hp
    have h13 : (-(1 / 3 : K)) * (3 / 2) = -(1 / 2) := by field_simp [h2, h3]
    have h16 : (1 / 6 : K) * (-3) = -(1 / 2) := by
      field_simp [h2, h6]
      ring
    have hc' := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) h16
    simp only [map_mul, map_neg, map_ofNat] at hc'
    have hvector : LaurentPolynomial.C (1 / 6 : K) * (33 - 12 * T 1) =
        LaurentPolynomial.C (-(1 / 2 : K)) * (4 * T 1 - 11) := by
      simp only [map_neg] at hc' ⊢
      linear_combination (4 * T 1 - 11) * hc'
    calc
      _ = LaurentPolynomial.C (-(1 / 3 : K)) * Lphi *
          ((WPFiniteZSource.Abar : K[X]).toLaurent * D (actualAK p : K[X]).toLaurent) := by
        dsimp only [Lphi]
        ring
      _ = LaurentPolynomial.C (-(1 / 3 : K)) * Lphi *
          (LaurentPolynomial.C (3 / 2 : K) *
            ((4 * T 1 - 11) - WPFiniteWSource.squaredCoordinate.toLaurent ^
              ((p - 1) / 2) * (4 * T (p : ℤ) - 11))) := by rw [hD]
      _ = LaurentPolynomial.C (-(1 / 2 : K)) * Lphi *
          ((4 * T 1 - 11) - WPFiniteWSource.squaredCoordinate.toLaurent ^
            ((p - 1) / 2) * (4 * T (p : ℤ) - 11)) := by
        rw [show LaurentPolynomial.C (-(1 / 3 : K)) * Lphi *
          (LaurentPolynomial.C (3 / 2 : K) *
            ((4 * T 1 - 11) - WPFiniteWSource.squaredCoordinate.toLaurent ^
              ((p - 1) / 2) * (4 * T (p : ℤ) - 11))) =
          (LaurentPolynomial.C (-(1 / 3 : K)) * LaurentPolynomial.C (3 / 2 : K)) * Lphi *
            ((4 * T 1 - 11) - WPFiniteWSource.squaredCoordinate.toLaurent ^
              ((p - 1) / 2) * (4 * T (p : ℤ) - 11)) by ring, ← map_mul, h13]
      _ = LaurentPolynomial.C (1 / 6 : K) * ((33 - 12 * T 1) * Lphi) +
          LaurentPolynomial.C (1 / 2 : K) * F *
            (frobeniusPhi p * (4 * T (p : ℤ) - 11)) := by
        rw [show LaurentPolynomial.C (1 / 6 : K) * ((33 - 12 * T 1) * Lphi) =
          (LaurentPolynomial.C (1 / 6 : K) * (33 - 12 * T 1)) * Lphi by ring, hvector]
        dsimp only [F, Lphi]
        simp only [map_neg]
        ring
      _ = _ := by
        rw [hphase]
        have h137 : (1 / 2 : K) * 137 = 137 / 2 := by ring
        have h44 : (1 / 2 : K) * 44 = 22 := by field_simp [h2]; ring
        have h137C := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) h137
        have h44C := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) h44
        simp only [map_mul, map_ofNat] at h137C h44C
        simp only [map_ofNat]
        linear_combination F * h137C - (T (p : ℤ) * F + T (-(p : ℤ)) * F) * h44C
  have hres := congrArg (originPole : K[T;T⁻¹] → K) he
  rw [originPole_cleared p hp, C_mul_coeff, originPole_sub, originPole_sub,
    originPole_add, originPole_C_mul, originPole_C_mul, originPole_C_mul,
    originPole_C_mul] at hres
  have hlog : originPole ((33 - 12 * T 1) * Lphi) =
      2 * (DD (1 / 4 : K) 4 Lphi).coeff (-1) +
        (DD (4 : K) (1 / 4) Lphi).coeff (-1) := by
    simpa only [map_ofNat] using endProduct_dlogV_density (K := K) p hp Lphi
  rw [hlog] at hres
  have hz := calL_half_positive_zero (K := K) p hp
  have hminus := calL_half_negative_ends (K := K) p hp
  rw [mul_assoc] at hz hminus
  change originPole (T (p : ℤ) * F) = 0 at hz
  change originPole (T (-(p : ℤ)) * F) = _ at hminus
  rw [hz, mul_zero, sub_zero, hminus] at hres
  have hra := calL_phi_pole (K := K) p hp (1 / 4 : K) ha
  have hrb := calL_phi_pole (K := K) p hp (4 : K) h4
  have hza : (1 / 4 : K) ^ (-(p : ℤ)) = 4 := by
    rw [zpow_neg, zpow_natCast, hpowa, one_div, inv_inv]
  have hzb : (4 : K) ^ (-(p : ℤ)) = 1 / 4 := by
    rw [zpow_neg, zpow_natCast, hpowb, one_div]
  have hrecA : (1 / 4 : K)⁻¹ = 4 := by rw [one_div, inv_inv]
  have hrecB : (4 : K)⁻¹ = 1 / 4 := (one_div (4 : K)).symm
  simp only [hza, hrecA, calL_trunc, eval_sub, eval_C] at hra
  simp only [hzb, hrecB, calL_trunc, eval_sub, eval_C] at hrb
  rw [hra, hrb] at hres
  have heva (c : K) (hc : c ≠ 0) : ev c hc (calL p) =
      (calLPositive p : K[X]).eval c + ev c hc (calLNegative p) -
        ev (-1) (neg_ne_zero.mpr one_ne_zero) (calLUnnormalized p) := by
    simp [calL, calLUnnormalized, ev, LaurentPolynomial.eval₂_toLaurent]
  rw [heva, heva] at hres
  have hF : originPole F = originPole (WPFiniteWSource.squaredCoordinate.toLaurent ^
      ((p - 1) / 2) * (calL p : K[T;T⁻¹])) := by congr 1; dsimp only [F]; ring
  rw [hF] at hres
  linear_combination (norm := (field_simp [h2, h3, h4, h5, h6, h10, h15]; ring)) hres
private theorem original_even_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (originalEven p : K[X]).eval 0 = WPFifthEntropy.C p u := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  simp only [originalEven, eval_mul, eval_neg, eval_C, ← coeff_zero_eq_eval_zero,
    Dstar_origin_fifth p hp u hu]
  field_simp [h3]
/-- The conic and fifth values come from the same ordered H primitive, including its lower endpoint. -/
theorem actual_calL_log_conic_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (oddLogLaurentCarrier p : K[T;T⁻¹]).coeff (-1) =
      (11 / 15 : K) * ActualKwOrderedEndpoints.originalG p (3 / 11) +
      (44 * WPFiniteNC122.h p / 15) * (originalEven p : K[X]).eval (4 / 11) -
      (11 / 10 : K) * ActualKwOrderedEndpoints.originalG p (1 / 5) -
        22 * WPFiniteNC122.h p * WPFifthEntropy.C p u / 5 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h11 : (11 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 11
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hc := ActualKwOrderedEndpoints.movingH_c_G (K := K) p h4 h5 h11
  have hm := ActualKwOrderedEndpoints.movingH_G_pair (K := K) p (-1) h4 h5
  have hG0 : ActualKwOrderedEndpoints.originalG (K := K) p 0 = 0 := by
    simp [ActualKwOrderedEndpoints.originalG, WPFiniteLoop.D_zero_left]
  simp only [add_neg_cancel, zero_div, hG0, zero_sub] at hm
  have hEbranch : (originalEven p : K[X]).eval (-1) = 0 := by
    simp only [originalEven, eval_neg, eval_mul, eval_C, Dstar_branch_zero p hp,
      mul_zero]
  rw [actual_calL_log_residue p hp]
  simp only [calLPositive, eval_sub, eval_mul, eval_add, eval_neg, eval_C, eval_ofNat,
    branchHPolynomial_eval, branchH_movingH p hp,
    original_even_origin p hp u hu, hEbranch, zero_sub]
  linear_combination (norm := (field_simp [h2, h4, h5, h10, h11, h15]; ring))
    (22 / 15 : K) * hc + (11 / 15 : K) * hm
/-- The original Lambda has its actual origin/infinity balance; no pole coefficient is assigned. -/
theorem actual_Lambda_infinity_balance (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (-2 * kappa p / 15 - WPFiniteNC122.h p / 5 : K) =
      (2 / 5 : K) * (WPFiniteNC122.q p - WPFifthEntropy.C p u) := by
  have hs := originalEven_endpoint_sum (K := K) p hp
  have hb : (originalEven p : K[X]).eval 4 =
      3 * WPFiniteNC122.q p + WPFiniteNC122.h p := by
    have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
      (Finset.mem_Ico.mpr (by omega))
    simp only [originalEven, eval_neg, eval_mul, eval_C,
      (Dstar_endpoints (K := K) p hp).2]
    field_simp [h3]
    ring
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  unfold kappa
  rw [original_even_origin p hp u hu]
  linear_combination (norm := (field_simp [h2, h5, h15]; ring))
    (2 / 15 : K) * hs + (2 / 15 : K) * hb
/-- The primitive and complete positive derivative give six ordered H rows before any fifth dictionary. -/
theorem actual_even_primitive_H_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    -(1 / 3 : K) * (calL p * frobeniusPhi p * D (actualAK p : K[X]).toLaurent).coeff (-1) =
      -(208 / 225 : K) * branchH p (1 / 4) (1 / 4) -
      (368 / 225 : K) * branchH p 4 (1 / 4) +
      (43 / 225 : K) * branchH p (1 / 4) 4 +
      (38 / 225 : K) * branchH p 4 4 +
      (176 / 75 : K) * branchH p 0 (1 / 4) -
      (11 / 75 : K) * branchH p 0 4 -
      (32 * WPFiniteNC122.h p / 225) *
        ((originalEven p : K[X]).eval (1 / 4) - (originalEven p).eval 4) +
      (274 / 225 : K) * Tprod p +
      (137 / 15 : K) * (-2 * kappa p / 15) * WPFifthEntropy.C p u := by
  rw [actual_calL_native_derivative_residue p hp,
    actual_calL_half_weighted_residue p hp, actual_calL_origin p hp,
    original_even_origin p hp u hu]
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1 / 4 : K) ≠ 0 := one_div_ne_zero h4
  have hnA : ev (1 / 4 : K) ha (calLNegative p) =
      -(2 / 15 : K) * (2 * branchH p 4 4 + branchH p (1 / 4) 4 -
        3 * branchH p 0 4) := by
    simp only [calLNegative, map_mul, map_sub, map_add, map_neg, map_ofNat,
      ev, LaurentPolynomial.eval₂_C, RingHom.id_apply,
      WPFiniteJWeightedResidue.inversion_eval, LaurentPolynomial.eval₂_toLaurent,
      eval₂_id, Units.val_inv_eq_inv_val, Units.val_mk0,
      one_div, inv_inv, branchHPolynomial_eval]
  have hnB : ev (4 : K) h4 (calLNegative p) =
      -(2 / 15 : K) * (2 * branchH p 4 (1 / 4) + branchH p (1 / 4) (1 / 4) -
        3 * branchH p 0 (1 / 4)) := by
    simp only [calLNegative, map_mul, map_sub, map_add, map_neg, map_ofNat,
      ev, LaurentPolynomial.eval₂_C, RingHom.id_apply,
      WPFiniteJWeightedResidue.inversion_eval, LaurentPolynomial.eval₂_toLaurent,
      eval₂_id, Units.val_inv_eq_inv_val, Units.val_mk0,
      ← one_div (4 : K), branchHPolynomial_eval]
  rw [hnA, hnB]
  simp only [calLPositive, eval_sub, eval_mul, eval_add, eval_neg, eval_C, eval_ofNat,
    branchHPolynomial_eval]
  change _ = _
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 5 ^ 2 by ring]
    exact mul_ne_zero h3 (pow_ne_zero 2 h5)
  have h225 : (225 : K) ≠ 0 := by
    rw [show (225 : K) = 15 ^ 2 by ring]
    exact pow_ne_zero 2 h15
  dsimp only [Tprod]
  have he : originPole ((33 - 12 * T 1) * (originalEven p : K[X]).toLaurent *
      invert (originalEven p).toLaurent) =
      originPole ((originalEven p : K[X]).toLaurent * invert (originalEven p).toLaurent *
        (33 - 12 * T 1)) := by congr 1; ring
  rw [he]
  field_simp [h2, h3, h4, h5, h10, h15, h75, h225]
  ring
/-- The whole conic-even attachment to Jraw, retaining every inclusive p slot and all ordered H rows. -/
theorem actual_Jraw_conic_even_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      (actualOddQuotientSeries p * actualLambdaSeries p -
        localFiniteSeriesHom (calL p) * actualOddSeries p : LaurentSeries K).coeff (-1) +
      (11 / 15 : K) * ActualKwOrderedEndpoints.originalG p (3 / 11) +
      (44 * WPFiniteNC122.h p / 15) * (originalEven p : K[X]).eval (4 / 11) -
      (11 / 10 : K) * ActualKwOrderedEndpoints.originalG p (1 / 5) -
      (208 / 225 : K) * branchH p (1 / 4) (1 / 4) -
      (368 / 225 : K) * branchH p 4 (1 / 4) +
      (43 / 225 : K) * branchH p (1 / 4) 4 +
      (38 / 225 : K) * branchH p 4 4 +
      (176 / 75 : K) * branchH p 0 (1 / 4) -
      (11 / 75 : K) * branchH p 0 4 -
      2 * WPFiniteNC122.h p * WPFiniteNC122.q p -
      22 * WPFiniteNC122.h p * WPFifthEntropy.C p u / 5 -
      (22 / 5 : K) * (WPFiniteNC122.q p - WPFifthEntropy.C p u) *
        ((actualAK p : K[X]).eval 0 - WPFiniteNC122.q p + WPFiniteNC122.h p) +
      (-2 * kappa p / 45) *
        (-16 * (WPFifthEntropy.C p u + WPFiniteNC122.q p) / 5 -
          11 * (actualAK p : K[X]).eval 0) -
      7 * WPFiniteNC122.h p ^ 2 / 5 -
      32 * WPFiniteNC122.h p * WPFiniteNC122.q p / 75 +
      8 * WPFiniteNC122.h p * (WPFiniteInversion.integerFermatQuotient p 3 : K) / 25 -
      (32 * WPFiniteNC122.h p / 225) *
        ((originalEven p : K[X]).eval (1 / 4) - (originalEven p).eval 4) +
      (274 / 225 : K) * Tprod p +
      (137 / 15 : K) * (-2 * kappa p / 15) * WPFifthEntropy.C p u := by
  rw [actual_Jraw_even_series_reduction p hp, actual_calL_log_conic_residue p hp u hu,
    actual_reciprocal_even_Lambda_residue p hp, actual_Lambda_infinity_balance p hp u hu,
    actual_native_even_Lambda_residue p hp u hu]
  have hd := actual_even_primitive_H_residue (K := K) p hp u hu
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K) ≠ 0 := by rw [show (25 : K) = 5 ^ 2 by ring]; exact pow_ne_zero 2 h5
  have h45 : (45 : K) ≠ 0 := by rw [show (45 : K) = 3 * 15 by ring]; exact mul_ne_zero h3 h15
  have h75 : (75 : K) ≠ 0 := by rw [show (75 : K) = 3 * 25 by ring]; exact mul_ne_zero h3 h25
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h225 : (225 : K) ≠ 0 := by
    rw [show (225 : K) = 15 ^ 2 by ring]
    exact pow_ne_zero 2 h15
  linear_combination (norm := (field_simp [h2, h3, h5, h10, h15, h25, h45, h75, h225]; ring)) hd

/-- The added-point even value is the genuine squared conic substitution for either root. -/
theorem actual_even_conic_coordinate (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (w : K) (hw : w ^ 2 = 3 / 11) :
    (originalEven p : K[X]).eval (4 / 11) = WPFiniteField.E p (2 * w) - WPFiniteField.E p w := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h11 : (11 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 11
    (Finset.mem_Ico.mpr (by omega))
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).eval (4 / 11) = 3 / 11 := by
    simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C,
      eval_add, eval_X, eval_one]
    field_simp [h5, h11]
    ring
  change (-Polynomial.C (3 : K) * Dstar p : K[X]).eval (4 / 11) = _
  rw [Dstar_moving_even_source p hp, eval_comp, hs]
  have he := congrArg (fun P : K[X] => P.eval w) (WPFiniteWSource.deltaE_square (K := K) p hp)
  rw [eval_comp, eval_pow, eval_X, hw, eval_sub, eval_comp, eval_mul,
    eval_ofNat, eval_X] at he
  simp only [WPFiniteKSource.EP, eval_mul, eval_C, eval_add, eval_comp,
    eval_neg, eval_X, WPFiniteAffineLog.LP_eval_eq, WPFiniteField.E,
    div_eq_mul_inv] at he ⊢
  linear_combination he

end WPFieldAssembly.NativeJointSuccessorEvenResidues
