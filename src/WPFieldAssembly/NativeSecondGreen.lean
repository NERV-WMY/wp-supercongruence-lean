import WPFieldAssembly.TerminatingSquare
import WPActualRankTwoCarrySource
import WPActualNativeSecondTaylor

open scoped Polynomial
open Polynomial WPActualRankTwoGaussODE WPActualRankTwoParameter
  WPActualRankTwoDividedDifference WPActualRankTwoFirstLift
  WPActualRankTwoHatLift WPActualRankTwoCarrySource WPActualNativeSecondTaylor
  WPFieldAssembly.TerminatingSquare

namespace WPFieldAssembly.NativeSecondGreen

set_option maxHeartbeats 1200000

noncomputable def balancedRank (p : ℕ) : ℚ[X] :=
  rankJacobiNode p 1 + C ((p : ℚ) / 6) * rankDividedJacobi p

theorem balanced_rank_source_aux (r : ℚ) (a R : ℚ[X])
    (ha : rankJacobiClear (-r) a = 0)
    (hR : rankJacobiClear (-r) R =
      36 * (2 * X * (a - C (4 * r) * R).derivative +
        C (1 - 6 * r) * (a - C (4 * r) * R))) :
    rankJacobiClear 0 (a + C r * R) =
      C (r ^ 2) * (-180 * a - 360 * X * R.derivative - 180 * R + C (900 * r) * R) := by
  simp only [rankJacobiClear, derivative_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero] at ha hR ⊢
  norm_num at ha hR ⊢
  linear_combination ha + C r * hR

/-- Both actual terminating nodes determine the entire rational second source. -/
theorem actual_balanced_rank_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rankJacobiClear 0 (balancedRank p) = C ((p : ℚ) ^ 2) *
      (-5 * rankJacobiNode p 1 - 10 * X * (rankDividedJacobi p).derivative -
        5 * rankDividedJacobi p + C (25 * (p : ℚ) / 6) * rankDividedJacobi p) := by
  let a := rankJacobiNode p 1
  let R := rankDividedJacobi p
  let r : ℚ := (p : ℚ) / 6
  have ht : -(p : ℚ) / 6 = -r := by dsimp [r]; ring
  have hfour : 2 * (p : ℚ) / 3 = 4 * r := by dsimp [r]; ring
  have hone : 1 - (p : ℚ) = 1 - 6 * r := by dsimp [r]; ring
  have ha := actual_rankJacobi_ODE p 1 (by omega) (Or.inl rfl)
  norm_num only [Nat.cast_one, neg_one_mul] at ha
  rw [ht] at ha
  change rankJacobiClear (-r) a = 0 at ha
  have hd := actual_two_jacobi_node_difference p (by omega)
  rw [hfour] at hd
  have hb : rankJacobiNode p 5 = a - C (4 * r) * R := by
    change a - rankJacobiNode p 5 = C (4 * r) * R at hd
    linear_combination -hd
  have hR := actual_rankDividedJacobi_ODE p (by omega)
  rw [ht, hb, hone] at hR
  change rankJacobiClear (-r) R =
    36 * (2 * X * (a - C (4 * r) * R).derivative +
      C (1 - 6 * r) * (a - C (4 * r) * R)) at hR
  have h := balanced_rank_source_aux r a R ha hR
  have hp2 : (p : ℚ) ^ 2 = 36 * r ^ 2 := by dsimp [r]; ring
  have h25 : 25 * (p : ℚ) / 6 = 25 * r := by dsimp [r]; ring
  change rankJacobiClear 0 (a + C r * R) = C ((p : ℚ) ^ 2) *
    (-5 * a - 10 * X * R.derivative - 5 * R + C (25 * (p : ℚ) / 6) * R)
  rw [hp2, h25]
  simp only [map_mul, map_ofNat] at h ⊢
  linear_combination h

theorem actual_balanced_square_discriminant_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) * jacobiDiscriminant 0 (balancedRank p ^ 2) =
      C ((p : ℚ) ^ 2) * (1 - X ^ 2) * balancedRank p ^ 3 *
        (-5 * rankJacobiNode p 1 - 10 * X * (rankDividedJacobi p).derivative -
          5 * rankDividedJacobi p + C (25 * (p : ℚ) / 6) * rankDividedJacobi p) := by
  rw [jacobiDiscriminant_square, actual_balanced_rank_source p hp]
  ring

noncomputable def nativeCubicErrorPolynomial (p e : ℕ) : ℚ[X] :=
  coefficientPolynomial e (nativeCubicError p)

/-- The literal cutoff retains all coefficients and the actual cubic error. -/
theorem actual_native_polynomial_secondTaylor (p e : ℕ) [Fact p.Prime] :
    WPReview.nativePolynomial (e + 1) - nativeTermAt p e -
      C ((p : ℚ) / 6) * nativeFirstJetAt p e -
      C ((p : ℚ) ^ 2 / 36) * nativeSecondJetAt p e =
        C ((p : ℚ) ^ 3) * nativeCubicErrorPolynomial p e := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  ext n
  simp only [WPReview.nativePolynomial_coeff, nativeTermAt, nativeFirstJetAt,
    nativeSecondJetAt, nativeCubicErrorPolynomial, coefficientPolynomial_coeff,
    coeff_sub, coeff_C_mul]
  split_ifs
  · unfold nativeCubicError
    field_simp [hpq]
  · ring

theorem nativeCubicErrorPolynomial_integral (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (n : ℕ) :
    0 ≤ padicValRat p ((nativeCubicErrorPolynomial p e).coeff n) := by
  rw [nativeCubicErrorPolynomial, coefficientPolynomial_coeff]
  split_ifs with hn
  · exact actual_nativeCubicError_integral p n hp (by omega)
  · simp

theorem balanced_taylor_algebra (r : ℚ) (F a R J C2 E : ℚ[X])
    (hF : F = a ^ 2 + C r * J + C (r ^ 2) * C2 + C (r ^ 3) * E) :
    F - (a + C r * R) ^ 2 - C (5 * r ^ 2) * (C2 - R ^ 2) =
      C r * (J - 2 * a * R - C (4 * r) * (C2 - R ^ 2)) + C (r ^ 3) * E := by
  rw [hF]
  simp only [map_mul, map_pow, map_ofNat]
  ring

noncomputable def jacobiPolar {K : Type*} [CommRing K] (F G : K[X]) : K[X] :=
  9 * (1 - X ^ 2) * (F * G.derivative.derivative + G * F.derivative.derivative -
    F.derivative * G.derivative) - 18 * X * (F * G.derivative + G * F.derivative) - 5 * F * G

noncomputable def quadraticGreen {K : Type*} [CommRing K] (Y Q : K[X]) : K[X] :=
  (1 - X ^ 2) ^ 2 * Y ^ 2 * Q.derivative.derivative -
    2 * (1 - X ^ 2) * (X * Y ^ 2 + (1 - X ^ 2) * Y * Y.derivative) * Q.derivative +
    (-2 * (1 - X ^ 2) ^ 2 * Y * Y.derivative.derivative +
      2 * (1 - X ^ 2) ^ 2 * Y.derivative ^ 2 +
      4 * X * (1 - X ^ 2) * Y * Y.derivative) * Q

theorem quadraticGreen_polar {K : Type*} [CommRing K] (Y Q : K[X]) :
    (1 - X ^ 2) * jacobiPolar (Y ^ 2) Q =
      9 * quadraticGreen Y Q + (1 - X ^ 2) * Y * Q * rankJacobiClear 0 Y := by
  simp [jacobiPolar, quadraticGreen, rankJacobiClear, derivative_mul, derivative_pow_succ,
    map_ofNat]
  ring

theorem legendre_green_identity {K : Type*} [CommRing K] (d : ℕ) (Y S : K[X]) :
    ((1 - X ^ 2) * (Y * S.derivative - Y.derivative * S)).derivative =
      Y * legendreJacobi d S - S * legendreJacobi d Y := by
  simp [legendreJacobi, derivative_mul, derivative_pow_succ]
  ring

theorem actual_secondCarry_green (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((1 - X ^ 2) * (rationalLegendre (p / 6) * (actualSecondCarryPolynomial p).derivative -
      (rationalLegendre (p / 6)).derivative * actualSecondCarryPolynomial p)).derivative =
        rationalLegendre (p / 6) * carryForcing p := by
  rw [legendre_green_identity, actualSecondCarryPolynomial_ODE p hp,
    rationalLegendre_ODE, mul_zero, sub_zero]

end WPFieldAssembly.NativeSecondGreen
