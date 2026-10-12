import WPActualRankTwoHatLift

open scoped Polynomial BigOperators
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift WPActualRankTwoComparison
  WPActualRankTwoFirstLift WPActualRankTwoGaussODE WPActualRankTwoLowTaylor
  WPActualRankTwoResidueSource WPActualRankTwoDividedDifference WPActualRankTwoParameter
  WPActualNativeHasse WPActualCMGauss

namespace WPActualRankTwoCarrySource

set_option maxHeartbeats 800000

theorem rationalLogPolynomial_derivative (p : ℕ) :
    (rationalLogPolynomial p).derivative = ∑ j ∈ Finset.range (p - 1), (X : ℚ[X]) ^ j := by
  unfold rationalLogPolynomial
  rw [derivative_sum]
  have ht : (∑ j ∈ Finset.Ico 1 p, (C (1 / (j : ℚ)) * X ^ j).derivative) =
      ∑ j ∈ Finset.Ico 1 p, (X : ℚ[X]) ^ (j - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjj := Finset.mem_Ico.mp hj
    rw [derivative_C_mul_X_pow, one_div_mul_cancel (by exact_mod_cast (by omega : j ≠ 0) : (j : ℚ) ≠ 0),
      C_1, one_mul]
  rw [ht, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  omega

theorem rationalLogPolynomial_source (p : ℕ) :
    (1 - X) * (rationalLogPolynomial p).derivative = (1 - X ^ (p - 1) : ℚ[X]) := by
  rw [rationalLogPolynomial_derivative, mul_comm, geom_sum_mul_neg]

theorem rationalEvenLog_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (1 - X ^ 2) * (rationalEvenLog p).derivative = (X - X ^ p : ℚ[X]) := by
  have heven : Even (p - 1) := by
    obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    exact ⟨n, by omega⟩
  have h1 := rationalLogPolynomial_source p
  have h2 := congrArg (fun P : ℚ[X] => P.comp (-X)) h1
  simp only [mul_comp, sub_comp, one_comp, X_comp, pow_comp, sub_neg_eq_add] at h2
  rw [heven.neg_pow] at h2
  have haP : (2 : ℚ[X]) * C (1 / 2 : ℚ) = 1 := by
    have h := congrArg (C : ℚ → ℚ[X]) (by norm_num : (2 : ℚ) * (1 / 2) = 1)
    simpa only [map_mul, map_ofNat, map_one] using h
  have hxp : (X : ℚ[X]) ^ p = X ^ (p - 1) * X := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  rw [rationalEvenLog, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_add, derivative_comp, derivative_neg, derivative_X, hxp]
  linear_combination C (1 / 2 : ℚ) * (1 + X) * h1 -
    C (1 / 2 : ℚ) * (1 - X) * h2 + (X - X ^ (p - 1) * X) * haP

theorem rationalEvenLog_second_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (1 - X ^ 2) * (rationalEvenLog p).derivative.derivative -
      2 * X * (rationalEvenLog p).derivative = 1 - C (p : ℚ) * X ^ (p - 1) := by
  have h := congrArg Polynomial.derivative (rationalEvenLog_source p hp)
  simp only [derivative_mul, derivative_sub, derivative_one, derivative_X_pow, derivative_X] at h
  norm_num [map_ofNat] at h ⊢
  linear_combination h

/-- The exact p-dependent correction of the full rational hat; none is dropped before division. -/
noncomputable def hatCorrection (p : ℕ) : ℚ[X] :=
  -X ^ (p - 1) * rationalLegendre (p / 6) -
    2 * (1 - X ^ 2) * X ^ (p - 1) * (rationalProperJacobi (p / 6)).derivative -
    C ((p : ℚ) - 1) * (1 - X ^ 2) * X ^ (p - 2) * rationalProperJacobi (p / 6) +
    2 * X ^ p * rationalProperJacobi (p / 6)

theorem legendreJacobi_power_product (d p : ℕ) (hp : 2 ≤ p) (n : ℚ[X]) :
    legendreJacobi d (X ^ p * n) = X ^ p * legendreJacobi d n +
      2 * C (p : ℚ) * (1 - X ^ 2) * X ^ (p - 1) * n.derivative +
      C (p : ℚ) * C ((p : ℚ) - 1) * (1 - X ^ 2) * X ^ (p - 2) * n -
      2 * C (p : ℚ) * X ^ p * n := by
  have hpred : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hxp : (X : ℚ[X]) ^ p = X ^ (p - 1) * X := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  simp only [legendreJacobi, derivative_mul, derivative_add, derivative_X_pow, derivative_C,
    zero_mul, zero_add, hpred]
  rw [show p - 1 - 1 = p - 2 by omega]
  rw [hxp]
  ring

theorem rationalRankHat_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreJacobi (p / 6) (rationalRankHat p) =
      2 * X * (rationalLegendre (p / 6)).derivative + rationalLegendre (p / 6) +
      C (p : ℚ) * hatCorrection p := by
  rw [rationalRankHat, legendreJacobi_sub, legendreJacobi_product,
    rationalLegendre_ODE, legendreJacobi_power_product _ _ (by omega), rationalProperJacobi_source]
  simp only [mul_zero, zero_add, derivative_add, derivative_C, add_zero]
  unfold hatCorrection
  linear_combination rationalLegendre (p / 6) * rationalEvenLog_second_source p hp +
    2 * (rationalLegendre (p / 6)).derivative * rationalEvenLog_source p hp

/-- The entire next source, including the integral second-order low-node remainder. -/
noncomputable def carryForcing (p : ℕ) : ℚ[X] :=
  -C (1 / 6 : ℚ) * (2 * X * (fixedJetJacobi (p / 6)).derivative + fixedJetJacobi (p / 6)) -
    rationalLegendre (p / 6) - C (5 / 3 : ℚ) * X * (rankDividedJacobi p).derivative +
    C ((((p / 6 : ℕ) : ℚ) - 2) / 3) * rankDividedJacobi p - hatCorrection p +
    C (p : ℚ) * (2 * X * (fixedErrorJacobi p).derivative + fixedErrorJacobi p +
      C (1 / 6 : ℚ) * fixedJetJacobi (p / 6) + C (2 / 3 : ℚ) * rankDividedJacobi p) -
    C ((p : ℚ) ^ 2) * fixedErrorJacobi p

theorem actual_high_rankJacobi_Taylor (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankJacobiNode p 5 = rationalLegendre (p / 6) -
      C (p : ℚ) * (C (1 / 6 : ℚ) * fixedJetJacobi (p / 6) + C (2 / 3 : ℚ) * rankDividedJacobi p) +
      C ((p : ℚ) ^ 2) * fixedErrorJacobi p := by
  have hlow := actual_low_fixedTaylor_jacobi p hp
  have hdiff := actual_two_jacobi_node_difference p hp
  rw [show C ((p : ℚ) / 6) = C (p : ℚ) * C (1 / 6 : ℚ) by rw [← map_mul]; congr 1; ring] at hlow
  rw [show C (2 * (p : ℚ) / 3) = C (p : ℚ) * C (2 / 3 : ℚ) by rw [← map_mul]; congr 1; ring] at hdiff
  linear_combination hlow - hdiff

theorem actualSecondCarryPolynomial_ODE (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    legendreJacobi (p / 6) (actualSecondCarryPolynomial p) = carryForcing p := by
  have hR := actual_rankDividedJacobi_legendre_source p (by omega : 7 ≤ p)
  have hhigh := actual_high_rankJacobi_Taylor p (by omega : 7 ≤ p)
  have hhighD := congrArg Polynomial.derivative hhigh
  simp only [derivative_add, derivative_sub, derivative_C_mul] at hhighD
  have hS : legendreJacobi (p / 6) (rankDividedJacobi p) -
      legendreJacobi (p / 6) (rationalRankHat p) =
      C (p : ℚ) * legendreJacobi (p / 6) (actualSecondCarryPolynomial p) := by
    have h := congrArg (legendreJacobi (p / 6)) (actualSecondCarryPolynomial_source p hp)
    rw [legendreJacobi_sub, legendreJacobi_C_mul] at h
    exact h
  rw [rationalRankHat_source p (by omega : 7 ≤ p)] at hS
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one] at hR hhigh hhighD hS
  have h23 : (3 : ℚ[X]) * C (2 / 3 : ℚ) = 2 := by
    have h := congrArg (C : ℚ → ℚ[X]) (by norm_num : (3 : ℚ) * (2 / 3) = 2)
    simpa only [map_mul, map_ofNat] using h
  have h53 : (3 : ℚ[X]) * C (5 / 3 : ℚ) = 5 := by
    have h := congrArg (C : ℚ → ℚ[X]) (by norm_num : (3 : ℚ) * (5 / 3) = 5)
    simpa only [map_mul, map_ofNat] using h
  have hd3 : (3 : ℚ[X]) * C ((((p / 6 : ℕ) : ℚ) - 2) / 3) =
      C ((p / 6 : ℕ) : ℚ) - 2 := by
    have h := congrArg (C : ℚ → ℚ[X])
      (show (3 : ℚ) * ((((p / 6 : ℕ) : ℚ) - 2) / 3) = ((p / 6 : ℕ) : ℚ) - 2 by ring)
    simpa only [map_mul, map_sub, map_ofNat] using h
  have hclear : (36 : ℚ[X]) * C (p : ℚ) *
      (legendreJacobi (p / 6) (actualSecondCarryPolynomial p) - carryForcing p) = 0 := by
    unfold carryForcing
    simp only [map_pow]
    linear_combination hR - 36 * hS +
      (72 * X) * hhighD + 36 * (1 - C (p : ℚ)) * hhigh +
      12 * C (p : ℚ) * X * (rankDividedJacobi p).derivative * h53 -
      12 * C (p : ℚ) * rankDividedJacobi p * hd3 -
      12 * C (p : ℚ) * (2 * X * (rankDividedJacobi p).derivative + rankDividedJacobi p) * h23
  exact sub_eq_zero.mp ((mul_eq_zero.mp hclear).resolve_left
    (mul_ne_zero (by norm_num) (Polynomial.C_ne_zero.mpr (by positivity))))

end WPActualRankTwoCarrySource
