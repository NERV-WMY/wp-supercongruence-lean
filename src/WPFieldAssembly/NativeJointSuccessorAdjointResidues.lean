import WPFieldAssembly.NativeJointSuccessorMixedPrimitive
import WPFieldAssembly.ActualBpairMetricAttachment
import WPFieldAssembly.NativeJointSuccessorProductResidues

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorAdjointResidues

open ActualBpairContraction ActualSimplePoleResidue GreenLaurentOperators
open NativeJointSuccessorMixedPrimitive WPFiniteLaurentDifferential
open NativeJointSuccessorProductResidues

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- In the whole Lambda only its original origin pole contributes against polynomial e. -/
theorem original_even_Lambda_residue (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    originPole ((originalEven p : K[X]).toLaurent * clearedLambda p) =
      (-2 * kappa p / 15) * (originalEven p).eval 0 := by
  have he : (originalEven p : K[X]).toLaurent * clearedLambda p =
      LaurentPolynomial.C (-2 * kappa p / 15) *
        ((WPFiniteZSource.Abar : K[X]).toLaurent *
          (T (-1) * (originalEven p).toLaurent)) +
      (Polynomial.C (16 * WPFiniteNC122.h p / 15 : K) * (X - 4) * originalEven p).toLaurent -
      (Polynomial.C (4 * WPFiniteNC122.h p / 15) *
        (X - Polynomial.C (1 / 4 : K)) * originalEven p).toLaurent := by
    simp only [clearedLambda, map_sub, map_mul, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X, map_ofNat]
    ring
  rw [he, originPole_sub, originPole_add, originPole_C_mul,
    originPole_polynomial, originPole_polynomial, add_zero, sub_zero,
    originPole_cleared p hp]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-1) (-1)
    (originalEven p).toLaurent
  simp only [map_one, one_mul, sub_self] at hs
  have hzero : (originalEven p : K[X]).toLaurent.coeff 0 = (originalEven p).eval 0 := by
    have hc := WPFiniteJCarrier.toLaurent_coeff_nat (originalEven p : K[X]) 0
    simpa only [Nat.cast_zero, coeff_zero_eq_eval_zero] using hc
  rw [hs, hzero]

/-- The full symmetric log product uses the same e and its plain reciprocal. -/
theorem original_even_symmetric_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole ((33 - 12 * T 1) * (originalEven p : K[X]).toLaurent * Dsym p) =
      -(originPole ((33 - 12 * T 1) * (originalEven p : K[X]).toLaurent *
        invert (originalEven p).toLaurent)) / 3 := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hc : (3 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 3 : K) = 1 := by
    change LaurentPolynomial.C (3 : K) * LaurentPolynomial.C (1 / 3 : K) = 1
    rw [← map_mul, mul_one_div_cancel h3, map_one]
  have hv : invert (originalEven p : K[X]).toLaurent = -3 * invert (Dstar p).toLaurent := by
    simp only [originalEven, map_mul, map_neg, map_ofNat]
  have he : (33 - 12 * T 1) * (originalEven p : K[X]).toLaurent * Dsym p =
      ((33 - 12 * X) * originalEven p * Dstar p : K[X]).toLaurent -
        LaurentPolynomial.C (1 / 3 : K) *
          ((33 - 12 * T 1) * (originalEven p).toLaurent * invert (originalEven p).toLaurent) := by
    simp only [Dsym, map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X]
    linear_combination LaurentPolynomial.C (1 / 3 : K) *
      (33 - 12 * T 1) * (originalEven p).toLaurent * hv -
      (33 - 12 * T 1) * (originalEven p).toLaurent * invert (Dstar p).toLaurent * hc
  rw [he, originPole_sub, originPole_polynomial, originPole_C_mul]
  ring

/-- The full adjoint derivative retains the quadratic reciprocal product and Lambda origin. -/
theorem original_even_calL_derivative_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    ((originalEven p : K[X]).toLaurent * D (calL p)).coeff (-1) =
      -(2 / 15 : K) * originPole
        ((33 - 12 * T 1) * (originalEven p : K[X]).toLaurent * invert (originalEven p).toLaurent) -
      (-2 * kappa p / 15) * (originalEven p).eval 0 := by
  have he := congrArg (fun F : K[T;T⁻¹] => originPole ((originalEven p).toLaurent * F))
    (calL_cleared_source (K := K) p hp)
  change originPole ((originalEven p : K[X]).toLaurent *
      ((WPFiniteZSource.Abar : K[X]).toLaurent * D (calL p))) =
    originPole ((originalEven p).toLaurent *
      (LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) * Dsym p -
        LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) - clearedLambda p)) at he
  have hl : originPole ((originalEven p : K[X]).toLaurent *
      ((WPFiniteZSource.Abar : K[X]).toLaurent * D (calL p))) =
      ((originalEven p).toLaurent * D (calL p)).coeff (-1) := by
    rw [show (originalEven p : K[X]).toLaurent *
        ((WPFiniteZSource.Abar : K[X]).toLaurent * D (calL p)) =
      (WPFiniteZSource.Abar : K[X]).toLaurent *
        ((originalEven p).toLaurent * D (calL p)) by ring, originPole_cleared p hp]
  have hz : originPole ((originalEven p : K[X]).toLaurent *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) = 0 := by
    rw [← map_pow, ← map_mul, originPole_polynomial]
  have hL : originPole ((originalEven p : K[X]).toLaurent *
      (LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) * Dsym p)) =
      (2 / 5 : K) * originPole ((33 - 12 * T 1) * (originalEven p).toLaurent * Dsym p) := by
    rw [show (originalEven p : K[X]).toLaurent *
      (LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) * Dsym p) =
      LaurentPolynomial.C (2 / 5 : K) *
        ((33 - 12 * T 1) * (originalEven p).toLaurent * Dsym p) by ring, originPole_C_mul]
  have hh : originPole ((originalEven p : K[X]).toLaurent *
      (LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2))) = 0 := by
    rw [show (originalEven p : K[X]).toLaurent *
      (LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) =
      LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
        ((originalEven p).toLaurent * WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2))
      by ring, originPole_C_mul, hz, mul_zero]
  rw [mul_sub, mul_sub, originPole_sub, originPole_sub, hl, hL, hh, sub_zero,
    original_even_Lambda_residue p hp, original_even_symmetric_log_residue p hp] at he
  rw [he]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h3, h5, h15]
  ring

/-- The first original unit integration keeps its entire adjoint and quadratic product. -/
theorem actual_calL_half_weighted_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      (calL p : K[T;T⁻¹])) = originPole (calL p) +
      (4 / 225 : K) * originPole
        ((33 - 12 * T 1) * (originalEven p : K[X]).toLaurent * invert (originalEven p).toLaurent) +
      (2 / 15 : K) * (-2 * kappa p / 15) * (originalEven p).eval 0 := by
  have hs := actual_D_source_pole_relation (K := K) p hp (calL p)
  have hD3 : D (3 : K[T;T⁻¹]) = 0 := D_C (3 : K)
  have he : D (originalEven p : K[X]).toLaurent = -3 * D (Dstar p).toLaurent := by
    simp only [originalEven, map_mul, map_neg, map_ofNat,
      D_mul, hD3, neg_zero, zero_mul, zero_add]
  have hi : ((calL p : K[T;T⁻¹]) * D (originalEven p).toLaurent).coeff (-1) =
      -((originalEven p).toLaurent * D (calL p)).coeff (-1) := by
    have hz : (D ((calL p : K[T;T⁻¹]) * (originalEven p).toLaurent)).coeff (-1) = 0 := by
      rw [D_coeff]
      norm_num
    rw [D_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hz
    have hz' : ((calL p : K[T;T⁻¹]) * D (originalEven p).toLaurent).coeff (-1) +
        ((originalEven p).toLaurent * D (calL p)).coeff (-1) = 0 := by
      convert hz using 1; ring
    exact eq_neg_of_add_eq_zero_left hz'
  have hcoeff : (3 : K) * ((calL p : K[T;T⁻¹]) * D (Dstar p).toLaurent).coeff (-1) =
      ((originalEven p).toLaurent * D (calL p)).coeff (-1) := by
    rw [he] at hi
    have he' : (calL p : K[T;T⁻¹]) * (-3 * D (Dstar p).toLaurent) =
        LaurentPolynomial.C (-3 : K) * (calL p * D (Dstar p).toLaurent) := by
      simp only [map_neg, map_ofNat]
      ring
    rw [he', C_mul_coeff] at hi
    linear_combination -hi
  rw [original_even_calL_derivative_residue p hp] at hcoeff
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h225 : (225 : K) ≠ 0 := by
    rw [show (225 : K) = 15 ^ 2 by ring]
    exact pow_ne_zero 2 h15
  linear_combination (norm := (field_simp [h3, h5, h15, h225]; ring))
    hs - (2 / 15 : K) * hcoeff

private theorem originPole_inverse_polynomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P : K[X]) :
    originPole (T (-1) * P.toLaurent) = -P.eval 0 / 4 := by
  have hd := congrArg (Polynomial.toLaurent : K[X] → K[T;T⁻¹]) (X_mul_divX_add P)
  simp only [map_add, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C] at hd
  have ht : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← LaurentPolynomial.T_add]; norm_num
  have he : T (-1) * P.toLaurent = P.divX.toLaurent +
      LaurentPolynomial.C (P.coeff 0) * T (-1) := by
    linear_combination -T (-1) * hd + P.divX.toLaurent * ht
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hpole : originPole (T (-1) : K[T;T⁻¹]) = -(1 / 4 : K) := by
    rw [originPole_trunc_inverse, LaurentPolynomial.invert_T, neg_neg]
    have hpoly : (T 1 : K[T;T⁻¹]) = (X : K[X]).toLaurent := Polynomial.toLaurent_X.symm
    rw [hpoly, trunc_toLaurent]
    simp only [eval_X]
    field_simp [h4, h15]
    ring
  rw [he, originPole_add, originPole_polynomial, zero_add, originPole_C_mul, hpole,
    coeff_zero_eq_eval_zero]
  ring

/-- Inverting the entire original Lambda changes only its proper-end linear part. -/
theorem original_clearedLambda_inverse_difference (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    invert (clearedLambda p : K[T;T⁻¹]) = clearedLambda p +
      LaurentPolynomial.C (4 * WPFiniteNC122.h p / 5) * (T (-1) - T 1) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hcoef : (16 * WPFiniteNC122.h p / 15 : K) -
      4 * WPFiniteNC122.h p / 15 = 4 * WPFiniteNC122.h p / 5 := by
    field_simp [h5, h15]
    ring
  have hc := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hcoef
  simp only [map_sub] at hc
  have ht : (T (-2) * T 1 : K[T;T⁻¹]) = T (-1) := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  simp only [clearedLambda, map_add, map_sub, map_mul, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T, WPFiniteZSource.invert_Abar, map_ofNat, neg_neg]
  linear_combination LaurentPolynomial.C (-2 * kappa p / 15) *
    (WPFiniteZSource.Abar : K[X]).toLaurent * ht + (T (-1) - T 1) * hc

/-- The reciprocal Lambda retains the actual original origin coefficient. -/
theorem original_even_inverse_Lambda_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole ((originalEven p : K[X]).toLaurent * invert (clearedLambda p)) =
      (-2 * kappa p / 15 - WPFiniteNC122.h p / 5) * (originalEven p).eval 0 := by
  have he : (originalEven p : K[X]).toLaurent * invert (clearedLambda p) =
      (originalEven p : K[X]).toLaurent * clearedLambda p +
      LaurentPolynomial.C (4 * WPFiniteNC122.h p / 5 : K) *
        (T (-1) * (originalEven p).toLaurent) -
      (Polynomial.C (4 * WPFiniteNC122.h p / 5 : K) * X * originalEven p).toLaurent := by
    rw [original_clearedLambda_inverse_difference p hp]
    simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
    ring
  rw [he, originPole_sub, originPole_add, originPole_C_mul, originPole_polynomial,
    sub_zero, original_even_Lambda_residue p hp, originPole_inverse_polynomial p hp]
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h4, h5, h15]
  ring

/-- The reciprocal numerator has one original simple-pole contribution against e squared. -/
theorem original_even_inverse_square_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole ((33 - 12 * T (-1)) * (originalEven p : K[X]).toLaurent ^ 2) =
      3 * (originalEven p).eval 0 ^ 2 := by
  have he : (33 - 12 * T (-1)) * (originalEven p : K[X]).toLaurent ^ 2 =
      ((33 : K[X]) * originalEven p ^ 2).toLaurent -
      LaurentPolynomial.C (12 : K) * (T (-1) * (originalEven p ^ 2).toLaurent) := by
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [he, originPole_sub, originPole_polynomial, originPole_C_mul,
    originPole_inverse_polynomial p hp]
  simp only [eval_pow]
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h4]
  ring

/-- The reciprocal dlogV numerator sees the whole symmetric product and its endpoint correction. -/
theorem original_even_inverse_product_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole ((33 - 12 * T (-1)) * (originalEven p : K[X]).toLaurent *
      invert (originalEven p).toLaurent) = Tprod (K := K) p +
      3 * (originalEven p).eval (1 / 4) * (originalEven p).eval 4 := by
  let F : K[T;T⁻¹] := (33 - 12 * T 1) * (originalEven p).toLaurent *
    invert (originalEven p).toLaurent
  have hinv : invert F = (33 - 12 * T (-1)) * (originalEven p).toLaurent *
      invert (originalEven p).toLaurent := by
    dsimp only [F]
    simp only [map_sub, map_mul, map_ofNat, LaurentPolynomial.invert_T,
      LaurentPolynomial.involutive_invert (originalEven p : K[X]).toLaurent]
    ring
  have hpole : originPole F = Tprod (K := K) p := by
    dsimp only [F, Tprod]
    congr 1
    ring
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  let v : Kˣ := Units.mk0 4 h4
  have hv : (v : K) = 4 := rfl
  have ha : LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹ F =
      30 * (originalEven p : K[X]).eval (1 / 4) * (originalEven p).eval 4 := by
    dsimp only [F]
    rw [Polynomial.toLaurent_X.symm]
    simp only [map_sub, map_mul, map_ofNat, WPFiniteJWeightedResidue.inversion_eval,
      LaurentPolynomial.eval₂_toLaurent, eval₂_id, eval_X,
      Units.val_inv_eq_inv_val, hv, inv_inv, ← one_div (4 : K)]
    field_simp [h4]
    ring
  have hb : LaurentPolynomial.eval₂ (RingHom.id K) v F =
      -15 * (originalEven p : K[X]).eval (1 / 4) * (originalEven p).eval 4 := by
    dsimp only [F]
    rw [Polynomial.toLaurent_X.symm]
    simp only [map_sub, map_mul, map_ofNat, WPFiniteJWeightedResidue.inversion_eval,
      LaurentPolynomial.eval₂_toLaurent, eval₂_id, eval_X,
      Units.val_inv_eq_inv_val, hv, ← one_div (4 : K)]
    ring
  have hbalance := originPole_inversion_balance F v hv
  rw [hinv, hpole, ha, hb] at hbalance
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  linear_combination (norm := (field_simp [h15]; ring)) hbalance

/-- Inversion of the full adjoint source retains the original squared-coordinate phase. -/
theorem original_calL_inverse_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (invert (calL p)) =
      -LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T (-1)) * Dsym p +
      LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
        T (-(((p - 1) / 2 : ℕ) : ℤ)) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) +
      invert (clearedLambda p) := by
  have hsym : invert (Dsym p : K[T;T⁻¹]) = Dsym p := by
    simp only [Dsym, map_add, LaurentPolynomial.involutive_invert (Dstar p : K[X]).toLaurent]
    ring
  have hi := congrArg invert (calL_cleared_source (K := K) p hp)
  change invert ((WPFiniteZSource.Abar : K[X]).toLaurent * D (calL p)) =
      invert (LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) * Dsym p -
        LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) - clearedLambda p) at hi
  simp only [map_mul, map_sub, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
    map_ofNat, hsym, WPFiniteZSource.invert_Abar,
    WPFiniteZSource.invert_squared_power] at hi
  rw [D_invert]
  simp only [map_mul, map_ofNat]
  linear_combination -hi

private theorem original_even_inverse_symmetric_log_residue (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 19 ≤ p) :
    originPole ((33 - 12 * T (-1)) * (originalEven p : K[X]).toLaurent * Dsym p) =
      -(3 * (originalEven p).eval 0 ^ 2 + Tprod (K := K) p +
        3 * (originalEven p).eval (1 / 4) * (originalEven p).eval 4) / 3 := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hc : (3 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 3 : K) = 1 := by
    change LaurentPolynomial.C (3 : K) * LaurentPolynomial.C (1 / 3 : K) = 1
    rw [← map_mul, mul_one_div_cancel h3, map_one]
  have hE : (originalEven p : K[X]).toLaurent = -3 * (Dstar p).toLaurent := by
    simp only [originalEven, map_mul, map_neg, map_ofNat]
  have hEv : invert (originalEven p : K[X]).toLaurent = -3 * invert (Dstar p).toLaurent := by
    simp only [hE, map_mul, map_neg, map_ofNat]
  have he : (33 - 12 * T (-1)) * (originalEven p : K[X]).toLaurent * Dsym p =
      LaurentPolynomial.C (-(1 / 3 : K)) *
        ((33 - 12 * T (-1)) * (originalEven p).toLaurent ^ 2 +
          (33 - 12 * T (-1)) * (originalEven p).toLaurent *
            invert (originalEven p).toLaurent) := by
    rw [hEv]
    simp only [Dsym, hE, map_neg]
    linear_combination 3 * (33 - 12 * T (-1)) * (Dstar p).toLaurent *
      ((Dstar p).toLaurent + invert (Dstar p).toLaurent) * hc
  rw [he, originPole_C_mul, originPole_add, original_even_inverse_square_log_residue p hp,
    original_even_inverse_product_log_residue p hp]
  ring

/-- The reciprocal adjoint derivative keeps both whole product residues and the Lambda origin. -/
theorem original_even_inverse_calL_derivative_residue (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 19 ≤ p) :
    ((originalEven p : K[X]).toLaurent * D (invert (calL p))).coeff (-1) =
      (2 / 15 : K) * (3 * (originalEven p).eval 0 ^ 2 + Tprod (K := K) p +
        3 * (originalEven p).eval (1 / 4) * (originalEven p).eval 4) +
      2 * WPFiniteNC122.h p * Uprod (K := K) p +
      (-2 * kappa p / 15 - WPFiniteNC122.h p / 5) * (originalEven p).eval 0 := by
  have he := congrArg (fun F : K[T;T⁻¹] => originPole ((originalEven p).toLaurent * F))
    (original_calL_inverse_cleared_source (K := K) p hp)
  have hl : originPole ((originalEven p : K[X]).toLaurent *
      ((WPFiniteZSource.Abar : K[X]).toLaurent * D (invert (calL p)))) =
      ((originalEven p).toLaurent * D (invert (calL p))).coeff (-1) := by
    rw [show (originalEven p : K[X]).toLaurent *
        ((WPFiniteZSource.Abar : K[X]).toLaurent * D (invert (calL p))) =
      (WPFiniteZSource.Abar : K[X]).toLaurent *
        ((originalEven p).toLaurent * D (invert (calL p))) by ring, originPole_cleared p hp]
  have hfirst : originPole ((originalEven p : K[X]).toLaurent *
      (-LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T (-1)) * Dsym p)) =
      -(2 / 5 : K) * originPole ((33 - 12 * T (-1)) * (originalEven p).toLaurent * Dsym p) := by
    have hc : (originalEven p : K[X]).toLaurent *
        (-LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T (-1)) * Dsym p) =
      LaurentPolynomial.C (-(2 / 5 : K)) *
        ((33 - 12 * T (-1)) * (originalEven p).toLaurent * Dsym p) := by
      simp only [map_neg]
      ring
    rw [hc, originPole_C_mul]
  have hsecond : originPole ((originalEven p : K[X]).toLaurent *
      (LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
        T (-(((p - 1) / 2 : ℕ) : ℤ)) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2))) =
      2 * WPFiniteNC122.h p * Uprod (K := K) p := by
    have hc : (originalEven p : K[X]).toLaurent *
        (LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
          T (-(((p - 1) / 2 : ℕ) : ℤ)) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) =
      LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
        ((originalEven p).toLaurent * WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          T (-(((p - 1) / 2 : ℕ) : ℤ))) := by ring
    rw [hc, originPole_C_mul]
    rfl
  simp only [mul_add, originPole_add, hl, hfirst, hsecond,
    original_even_inverse_symmetric_log_residue p hp, original_even_inverse_Lambda_residue p hp] at he
  rw [he]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h3, h5, h15]
  ring

private theorem original_even_unit_integration (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (F : K[T;T⁻¹]) :
    originPole (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * F) =
      originPole F - (2 / 15 : K) * ((originalEven p).toLaurent * D F).coeff (-1) := by
  have hs := actual_D_source_pole_relation (K := K) p hp F
  have hD3 : D (3 : K[T;T⁻¹]) = 0 := D_C (3 : K)
  have he : D (originalEven p : K[X]).toLaurent = -3 * D (Dstar p).toLaurent := by
    simp only [originalEven, map_mul, map_neg, map_ofNat,
      D_mul, hD3, neg_zero, zero_mul, zero_add]
  have hi : (F * D (originalEven p).toLaurent).coeff (-1) =
      -((originalEven p).toLaurent * D F).coeff (-1) := by
    have hz : (D (F * (originalEven p).toLaurent)).coeff (-1) = 0 := by
      rw [D_coeff]
      norm_num
    rw [D_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hz
    have hz' : (F * D (originalEven p).toLaurent).coeff (-1) +
        ((originalEven p).toLaurent * D F).coeff (-1) = 0 := by
      convert hz using 1; ring
    exact eq_neg_of_add_eq_zero_left hz'
  have hcoeff : (3 : K) * (F * D (Dstar p).toLaurent).coeff (-1) =
      ((originalEven p).toLaurent * D F).coeff (-1) := by
    rw [he] at hi
    have he' : F * (-3 * D (Dstar p).toLaurent) =
        LaurentPolynomial.C (-3 : K) * (F * D (Dstar p).toLaurent) := by
      simp only [map_neg, map_ofNat]
      ring
    rw [he', C_mul_coeff] at hi
    linear_combination -hi
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  linear_combination (norm := (field_simp [h3, h5, h15]; ring))
    hs - (2 / 15 : K) * hcoeff

/-- The second unit integration retains the whole reciprocal adjoint and both product residues. -/
theorem actual_calL_inverse_half_weighted_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      invert (calL p : K[T;T⁻¹])) = originPole (invert (calL p)) -
      (4 / 225 : K) * Tprod (K := K) p -
      (4 / 75 : K) * (originalEven p).eval (1 / 4) * (originalEven p).eval 4 -
      (4 * WPFiniteNC122.h p / 15) * Uprod (K := K) p -
      (4 * WPFiniteNC122.q p / 75) * (originalEven p).eval 0 := by
  have hs := original_even_unit_integration (K := K) p hp (invert (calL p))
  rw [original_even_inverse_calL_derivative_residue p hp] at hs
  have hsum := originalEven_endpoint_sum (K := K) p hp
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hb : (originalEven p : K[X]).eval 4 = 3 * WPFiniteNC122.q p + WPFiniteNC122.h p := by
    simp only [originalEven, eval_mul, eval_neg, eval_C, (Dstar_endpoints (K := K) p hp).2]
    field_simp [h3]
    ring
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 5 ^ 2 by ring]
    exact mul_ne_zero h3 (pow_ne_zero 2 h5)
  have h225 : (225 : K) ≠ 0 := by
    rw [show (225 : K) = 15 ^ 2 by ring]
    exact pow_ne_zero 2 h15
  simp only [kappa] at hs
  linear_combination (norm := (field_simp [h2, h3, h5, h15, h75, h225]; ring))
    hs - (4 * (originalEven p).eval 0 / 225) * hsum -
      (4 * (originalEven p).eval 0 / 225) * hb

end WPFieldAssembly.NativeJointSuccessorAdjointResidues
