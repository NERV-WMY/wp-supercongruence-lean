import WPFieldAssembly.NativePrecision
import WPActualResidueVanishing

open scoped Polynomial LaurentPolynomial
open Polynomial WPPIntegralReduction WPFieldAssembly.NativePrecision
  WPActualHasseReciprocal WPActualChiSource WPActualPullbackSource WPActualEtaPole
  WPActualEtaIntegrality WPLaurentIntegralResidue WPActualResidueVanishing WPFiniteJCarrier

namespace WPFieldAssembly.NativeShiftedChi

set_option maxHeartbeats 1000000

noncomputable def nativeHalfPullback (p : ℕ) : ℚ[X] :=
  (WPReview.nativePolynomial ((p - 1) / 2 + 1)).comp Vpolynomial

noncomputable def shiftedChiQ (p : ℕ) : ℚ[X] :=
  C (1 / (p : ℚ)) *
    (X ^ p * nativeHalfPullback p - X * (nativeHalfPullback p).reflect (3 * ((p - 1) / 2)))

theorem nativeHalfPullback_degree (p : ℕ) :
    (nativeHalfPullback p).natDegree ≤ 3 * ((p - 1) / 2) := by
  have hV : Vpolynomial.natDegree ≤ 3 := by unfold Vpolynomial; compute_degree
  rw [nativeHalfPullback, natDegree_comp, rational_native_degree]
  exact (Nat.mul_le_mul_left ((p - 1) / 2) hV).trans_eq (Nat.mul_comm _ _)

theorem shiftedChiQ_toLaurent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (shiftedChiQ p).toLaurent =
      LaurentPolynomial.T (p : ℤ) * chiX p ((p - 1) / 2) ((p - 1) / 2) := by
  let N := (p - 1) / 2
  have hN := WPFiniteWSource.half_exponent p hp
  have hP : (nativeHalfPullback p).toLaurent = Fpull N Vx := by
    unfold nativeHalfPullback
    exact (Fpull_toLaurent N).symm
  have hT : (LaurentPolynomial.T (1 : ℤ) : ℚ[T;T⁻¹]) *
      LaurentPolynomial.T ((3 * N : ℕ) : ℤ) =
        LaurentPolynomial.T (p : ℤ) * LaurentPolynomial.T (N : ℤ) := by
    rw [← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
    congr 1
    dsimp [N]
    omega
  rw [shiftedChiQ]
  simp only [map_mul, map_sub, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
    LaurentPolynomial.T_pow, mul_one]
  rw [toLaurent_reflect _ _ (nativeHalfPullback_degree p)]
  rw [hP]
  change LaurentPolynomial.C (1 / (p : ℚ)) *
      (LaurentPolynomial.T (p : ℤ) * Fpull N Vx -
        LaurentPolynomial.T 1 *
          (LaurentPolynomial.T ((3 * N : ℕ) : ℤ) * LaurentPolynomial.invert (Fpull N Vx))) =
    LaurentPolynomial.T (p : ℤ) * (LaurentPolynomial.C (1 / (p : ℚ)) *
      (Fpull N Vx - LaurentPolynomial.T (N : ℤ) * Fpull N Qx))
  rw [← Fpull_reciprocal]
  calc
    _ = LaurentPolynomial.C (1 / (p : ℚ)) *
      (LaurentPolynomial.T (p : ℤ) * Fpull N Vx -
        (LaurentPolynomial.T 1 * LaurentPolynomial.T ((3 * N : ℕ) : ℤ)) *
          LaurentPolynomial.invert (Fpull N Vx)) := by ring
    _ = _ := by rw [hT]; ring

theorem shiftedChiQ_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (shiftedChiQ p).natDegree ≤ p + 3 * ((p - 1) / 2) := by
  have hP := nativeHalfPullback_degree p
  have href : ((nativeHalfPullback p).reflect (3 * ((p - 1) / 2))).natDegree ≤
      3 * ((p - 1) / 2) := natDegree_reflect_le.trans (max_le (le_refl _) hP)
  have hfirst : (X ^ p * nativeHalfPullback p).natDegree ≤ p + 3 * ((p - 1) / 2) := natDegree_mul_le_of_le
    (show (X ^ p : ℚ[X]).natDegree ≤ p by simp) hP
  have hsecond : (X * (nativeHalfPullback p).reflect (3 * ((p - 1) / 2))).natDegree ≤
      1 + 3 * ((p - 1) / 2) := natDegree_mul_le_of_le (natDegree_X_le (R := ℚ)) href
  have hsub : (X ^ p * nativeHalfPullback p -
      X * (nativeHalfPullback p).reflect (3 * ((p - 1) / 2))).natDegree ≤ p + 3 * ((p - 1) / 2) :=
    (natDegree_sub_le _ _).trans (max_le hfirst (hsecond.trans (by omega)))
  unfold shiftedChiQ
  simpa only [Nat.zero_add] using natDegree_mul_le_of_le
    (show (C (1 / (p : ℚ)) : ℚ[X]).natDegree ≤ 0 by simp) hsub

theorem shiftedChiQ_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℕ) :
    0 ≤ padicValRat p ((shiftedChiQ p).coeff n) := by
  have hc := congrArg (fun P : ℚ[T;T⁻¹] => P.coeff (n : ℤ)) (shiftedChiQ_toLaurent p hp)
  rw [toLaurent_coeff_nat, mul_comm (LaurentPolynomial.T (p : ℤ)), monomial_shift_coefficient] at hc
  rw [hc]
  exact actual_chiX_integral p ((p - 1) / 2) (by omega) (by omega) (by omega) _

theorem exists_integral_polynomial_model (p : ℕ) [Fact p.Prime] (P : ℚ[X])
    (hP : ∀ n, 0 ≤ padicValRat p (P.coeff n)) :
    ∃ Q : (integralRationals p)[X],
      Q.map (integralRationals p).subtype = P ∧ Q.natDegree = P.natDegree := by
  have hL : P ∈ Polynomial.lifts (integralRationals p).subtype := by
    apply (Polynomial.lifts_iff_coeff_lifts (f := (integralRationals p).subtype) P).mpr
    intro n
    exact ⟨⟨P.coeff n, hP n⟩, rfl⟩
  exact Polynomial.exists_natDegree_eq_of_mem_lifts hL

noncomputable def integralPolynomialLift (p : ℕ) [Fact p.Prime] (P : ℚ[X])
    (hP : ∀ n, 0 ≤ padicValRat p (P.coeff n)) : (integralRationals p)[X] :=
  Classical.choose (exists_integral_polynomial_model p P hP)

theorem integralPolynomialLift_rational (p : ℕ) [Fact p.Prime] (P : ℚ[X])
    (hP : ∀ n, 0 ≤ padicValRat p (P.coeff n)) :
    (integralPolynomialLift p P hP).map (integralRationals p).subtype = P :=
  (Classical.choose_spec (exists_integral_polynomial_model p P hP)).1

theorem integralPolynomialLift_degree (p : ℕ) [Fact p.Prime] (P : ℚ[X])
    (hP : ∀ n, 0 ≤ padicValRat p (P.coeff n)) :
    (integralPolynomialLift p P hP).natDegree = P.natDegree :=
  (Classical.choose_spec (exists_integral_polynomial_model p P hP)).2

noncomputable def shiftedChiIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := integralPolynomialLift p (shiftedChiQ p) (shiftedChiQ_integral p hp)

theorem shiftedChiIntegral_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (shiftedChiIntegral p hp).map (integralRationals p).subtype = shiftedChiQ p :=
  integralPolynomialLift_rational _ _ _

noncomputable def shiftedChiField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (shiftedChiIntegral p hp).map (residueHom p)

theorem shiftedChiField_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (shiftedChiField p hp).natDegree ≤ p + 3 * ((p - 1) / 2) := by
  apply natDegree_map_le.trans
  rw [shiftedChiIntegral, integralPolynomialLift_degree]
  exact shiftedChiQ_degree p hp

noncomputable def halfChiIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralLaurent p :=
  ⟨chiX p ((p - 1) / 2) ((p - 1) / 2),
    actual_chiX_integral p _ (by omega) (by omega) (by omega)⟩

theorem shiftedChiField_toLaurent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (shiftedChiField p hp).toLaurent =
      LaurentPolynomial.T (p : ℤ) * residueLaurent p (halfChiIntegral p hp) := by
  have hLift : (shiftedChiIntegral p hp).toLaurent =
      LaurentPolynomial.T (p : ℤ) * integralLift p (halfChiIntegral p hp) := by
    apply WPLaurentIntegralResidue.coefficientMap_injective (integralRationals p).subtype
      (Subring.subtype_injective (integralRationals p))
    rw [coefficientMap_toLaurent, shiftedChiIntegral_rational, map_mul,
      coefficientMap_T, integralLift_rational]
    exact shiftedChiQ_toLaurent p hp
  have hField := congrArg (coefficientMap (residueHom p)) hLift
  simp only [coefficientMap_toLaurent, map_mul, coefficientMap_T] at hField
  exact hField

end WPFieldAssembly.NativeShiftedChi
