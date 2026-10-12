import WPFieldAssembly.NativeClosureMixedSource
import WPFieldAssembly.ActualCubicNativeSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.NativeJointSuccessorActualPhase

open ActualBpairContraction ActualCubicNativeSource NativeClosureMixedSource

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The two polynomial bands are taken from the entire original native A. -/
noncomputable def actualU (p : ℕ) : K[X] :=
  Polynomial.C (12 / 5 : K) * Dstar p -
    Polynomial.C (4 * WPFiniteNC122.q p / 5)

noncomputable def actualV (p : ℕ) : K[X] :=
  -Polynomial.C (33 / 5 : K) * Dstar p +
    Polynomial.C (2 / 5 : K) * WPFiniteABSourceTail.logTrace p

theorem actual_A_two_bands (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualAK p : K[X]) = X ^ p * actualU p + actualV p +
      Polynomial.C (nativeConstant p) := by
  rw [actual_AK_two_band p hp]
  unfold actualU actualV
  ring

theorem actual_U_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualU p : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  unfold actualU
  exact (natDegree_sub_le _ _).trans (max_le
    ((natDegree_C_mul_le _ _).trans (Dstar_degree p hp)) (by simp))

theorem actual_V_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualV p : K[X]).natDegree ≤ p - 1 := by
  have hd : (-Polynomial.C (33 / 5 : K) * (Dstar p : K[X])).natDegree ≤ p - 1 := by
    rw [← Polynomial.C_neg]
    exact (natDegree_C_mul_le _ _).trans ((Dstar_degree p hp).trans (by omega))
  unfold actualV
  exact (natDegree_add_le _ _).trans (max_le
    hd
    ((natDegree_C_mul_le _ _).trans (WPFiniteABSourceTail.logTrace_degree p)))

/-- F contains the original c, h and q without an endpoint reassignment. -/
noncomputable def actualF (p : ℕ) : K[T;T⁻¹] :=
  invert (actualV p).toLaurent + LaurentPolynomial.C (1 / 3 : K) *
    (actualV p).toLaurent +
      LaurentPolynomial.C (4 * nativeConstant p / 3 - WPFiniteNC122.q p +
        WPFiniteNC122.h p)

/-- All four multiple-p phases of the actual mixed residual are displayed. -/
theorem actual_R_four_phases (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) =
      oddReciprocalS p + WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        (4 * T (-2 * (p : ℤ)) * invert (actualU p).toLaurent +
          T (-(p : ℤ)) * (4 * actualF p - 11 * invert (actualU p).toLaurent) +
          (LaurentPolynomial.C (4 / 3 : K) * (actualU p).toLaurent - 11 * actualF p) -
          LaurentPolynomial.C (11 / 3 : K) * T (p : ℤ) * (actualU p).toLaurent) := by
  have hA := congrArg (Polynomial.toLaurent : K[X] → K[T;T⁻¹])
    (actual_A_two_bands (K := K) p hp)
  simp only [map_add, map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C] at hA
  have hAv := congrArg invert hA
  simp only [map_add, map_mul, invert_T, invert_C] at hAv
  have ht : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have htt : (T (-(p : ℤ)) * T (-(p : ℤ)) : K[T;T⁻¹]) = T (-2 * (p : ℤ)) := by
    rw [← T_add]
    congr 1
    ring
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hC : LaurentPolynomial.C (4 / 3 : K) = 4 * LaurentPolynomial.C (1 / 3 : K) := by
    simp only [div_eq_mul_inv, map_mul, map_ofNat, one_mul]
  have hC11 : LaurentPolynomial.C (11 / 3 : K) = 11 * LaurentPolynomial.C (1 / 3 : K) := by
    simp only [div_eq_mul_inv, map_mul, map_ofNat, one_mul]
  have hc : LaurentPolynomial.C (4 * nativeConstant (K := K) p / 3 -
      WPFiniteNC122.q p + WPFiniteNC122.h p) =
      LaurentPolynomial.C (nativeConstant p) +
        LaurentPolynomial.C (1 / 3 : K) * LaurentPolynomial.C (nativeConstant p) -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p) := by
    rw [← map_mul, ← map_add, ← map_sub]
    congr 1
    field_simp [h3]
    ring
  unfold mixedResidual mixedEvenSource frobeniusPhi actualF
  rw [hAv, hA, hC, hC11, hc]
  linear_combination
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      (4 * invert (actualU p).toLaurent * htt -
        (-4) * LaurentPolynomial.C (1 / 3 : K) * (actualU p).toLaurent * ht)

/-- This window is only a decomposition; its omitted phases still have a residue. -/
noncomputable def actualRWindow (p : ℕ) : K[T;T⁻¹] :=
  oddReciprocalS p + WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
    (-11 * invert (actualV p).toLaurent +
      LaurentPolynomial.C (1 / 3 : K) * (4 * T (-(p : ℤ)) - 11) * (actualV p).toLaurent +
        LaurentPolynomial.C (4 / 3 : K) * (actualU p).toLaurent -
          LaurentPolynomial.C (11 * (4 * nativeConstant p / 3 - WPFiniteNC122.q p +
            WPFiniteNC122.h p)))

theorem actual_R_window_difference (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) - actualRWindow p =
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        (4 * T (-2 * (p : ℤ)) * invert (actualU p).toLaurent +
          T (-(p : ℤ)) * (4 * invert (actualV p).toLaurent +
            LaurentPolynomial.C (4 * (4 * nativeConstant p / 3 - WPFiniteNC122.q p +
              WPFiniteNC122.h p)) - 11 * invert (actualU p).toLaurent) -
          LaurentPolynomial.C (11 / 3 : K) * T (p : ℤ) * (actualU p).toLaurent) := by
  rw [actual_R_four_phases p hp]
  simp only [actualRWindow, actualF, map_mul, map_ofNat]
  ring

/-- Clearing uses the genuine branch polynomial, with no inverse of Dsym. -/
noncomputable def actualCtilde (p : ℕ) : K[X] :=
  Polynomial.C (2 / 5 : K) * (33 - 12 * X) * WPFiniteWSource.squaredCoordinate *
    branchPolynomial p - Polynomial.C (2 * WPFiniteNC122.h p) * X ^ ((p - 1) / 2 - 1)

theorem actual_Ctilde_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualCtilde p : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  have hl : (33 - 12 * X : K[X]).natDegree ≤ 1 := by compute_degree
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).natDegree ≤ 1 := by
    unfold WPFiniteWSource.squaredCoordinate
    compute_degree
  unfold actualCtilde
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans hl) hs)
      (branchPolynomial_degree p hp)).trans (by omega)
  · exact (natDegree_C_mul_le _ _).trans (by simp)

/-- The full numerator factors through the full residual, including its deep phases. -/
theorem actual_Nj_factor (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) =
      T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) * (actualCtilde p).toLaurent *
        mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  let R := mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)
  let J := mixedProduct p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hsp : (WPFiniteWSource.squaredCoordinate : K[X]) ≠ 0 := by
    have hc : (WPFiniteWSource.squaredCoordinate : K[X]).coeff 1 = (5 : K)⁻¹ := by
      simp [WPFiniteWSource.squaredCoordinate, coeff_one]
    intro hz
    rw [hz, coeff_zero] at hc
    exact inv_ne_zero h5 hc.symm
  have hs : s ≠ 0 := by
    intro hz
    apply hsp
    apply Polynomial.toLaurent_injective
    simpa only [s, map_zero] using hz
  have ht : (T (-((N - 1 : ℕ) : ℤ)) * T ((N - 1 : ℕ) : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hb := congrArg (Polynomial.toLaurent : K[X] → K[T;T⁻¹])
    (branchPolynomial_factor (K := K) p hp)
  rw [branchNumerator_toLaurent p hp] at hb
  simp only [map_mul, map_pow] at hb
  change T ((N - 1 : ℕ) : ℤ) * Dsym p = s ^ (N + 1) * (branchPolynomial p).toLaurent at hb
  have hd : Dsym p = T (-((N - 1 : ℕ) : ℤ)) * s ^ (N + 1) *
      (branchPolynomial p).toLaurent := by
    linear_combination T (-((N - 1 : ℕ) : ℤ)) * hb - Dsym p * ht
  have hj : J = T (-((N - 1 : ℕ) : ℤ)) * s * (branchPolynomial p).toLaurent * R := by
    apply mul_left_cancel₀ (pow_ne_zero N hs)
    have hc := mixedProduct_consistency (K := K) p hp
      (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)
    change s ^ N * J = Dsym p * R at hc
    rw [hc, hd, pow_succ]
    ring
  change LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) * J -
    LaurentPolynomial.C (2 * WPFiniteNC122.h p) * R = _
  rw [hj]
  simp only [actualCtilde, map_sub, map_mul, map_ofNat, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, Polynomial.toLaurent_X_pow]
  change _ = T (-((N - 1 : ℕ) : ℤ)) *
    (LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) * s * (branchPolynomial p).toLaurent -
      2 * LaurentPolynomial.C (WPFiniteNC122.h p) * T ((N - 1 : ℕ) : ℤ)) * R
  linear_combination (2 * LaurentPolynomial.C (WPFiniteNC122.h p)) * R * ht

/-- The full residual derivative consumes the genuine two original A sources. -/
theorem actual_R_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      (WPFiniteWSource.squaredCoordinate.toLaurent *
          D (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) +
        LaurentPolynomial.C (1 / 10 : K) *
          mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      LaurentPolynomial.C (75 / 2 : K) *
        (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
            T (2 - (p : ℤ)) * (4 - 11 * T 1) ^ (p - 1) -
          T ((((p - 1) / 2 + 1 : ℕ) : ℤ))) +
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) * frobeniusPhi p *
        (-LaurentPolynomial.C (3 / 2 : K) *
          ((4 * T (-1) - 11) - T (-(((p - 1) / 2 : ℕ) : ℤ)) *
            WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * frobeniusPhi p) +
          LaurentPolynomial.C (1 / 2 : K) *
            ((4 * T 1 - 11) - WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
              (4 * T (p : ℤ) - 11))) := by
  exact mixedResidual_cleared_source p hp (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)
    (actual_AK_cleared_derivative p hp)
    (by simpa only [frobeniusPhi] using actual_AQ_cleared_derivative (K := K) p hp)

end WPFieldAssembly.NativeJointSuccessorActualPhase
