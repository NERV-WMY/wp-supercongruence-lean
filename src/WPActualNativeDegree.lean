import WPActualNativeQuadraticSquare

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeQuadraticSquare
  WPActualRankTwoLegendreField WPPIntegralReduction

namespace WPActualNativeDegree

theorem actual_native_coefficient_field_unit (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n ≤ p / 6) : (WPReview.nativeCoefficient n : ZMod p) ≠ 0 := by
  have h6 : 6 * n < p := by
    rcases WPActualNativeParameter.prime_six_classes p hp with he | he <;> omega
  have hval : padicValRat p (WPReview.nativeCoefficient n) = 0 := by
    rw [WPNativeMomentIntegrality.native_coefficient_valuation_below_prime p n hp (by omega),
      Nat.div_eq_of_lt h6, Nat.div_eq_of_lt (by omega : 3 * n < p)]
    norm_num
  have hpos : 0 < WPReview.nativeCoefficient n := by
    unfold WPReview.nativeCoefficient
    positivity
  intro hz
  have hc := (integral_residue_zero_iff p _ (by omega :
    0 ≤ padicValRat p (WPReview.nativeCoefficient n))).mp hz
  simp only [WPReview.RationalCongruent, sub_zero] at hc
  rcases hc with hc | hc
  · exact (ne_of_gt hpos) hc
  · omega

theorem actual_native_field_exact_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (nativeField p (p / 6)).natDegree = p / 6 := by
  apply le_antisymm (actual_native_field_degree p)
  apply le_natDegree_of_ne_zero
  rw [nativeField_coeff, if_pos (by omega)]
  exact actual_native_coefficient_field_unit p (p / 6) hp (by omega)

theorem actualLegendreJacobi_exact_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLegendreJacobi p).natDegree = p / 6 := by
  have he := congrArg Polynomial.natDegree (actual_native_Jacobi_square p hp)
  rw [natDegree_comp, actual_native_field_exact_degree p (by omega), natDegree_pow] at he
  have hg : (1 - X ^ 2 : (ZMod p)[X]).natDegree = 2 := by compute_degree; norm_num
  rw [hg] at he
  omega

end WPActualNativeDegree
