import WPReview.Literal

open scoped BigOperators

namespace WPReview

set_option maxRecDepth 10000

theorem literal_seven :
    RationalCongruent 7 5 (literalSum 7) (9 * (7 : ℚ) ^ 2) := by
  apply (literal_congruence_iff 7 (by norm_num) (by norm_num)).2
  refine ⟨-25673894153385364382356046751667200, ?_⟩
  have hdiff := literal_difference_eq_cleared 7 (by norm_num)
  have hD := (eq_div_iff (clearing_denominator_ne_zero 7)).mp hdiff
  have hrat : (clearedDifference 7 : ℚ) =
      (7 : ℚ) ^ 5 * (-25673894153385364382356046751667200 : ℚ) := by
    rw [← hD]
    norm_num [literalSum, literalTerm, weightNat, clearingDenominatorNat,
      Finset.sum_range_succ, Nat.factorial]
  exact_mod_cast hrat

theorem literal_eleven :
    RationalCongruent 11 5 (literalSum 11) (9 * (11 : ℚ) ^ 2) := by
  apply (literal_congruence_iff 11 (by norm_num) (by norm_num)).2
  refine ⟨-6702852754925649907122189497429545875359720448306050246400, ?_⟩
  have hdiff := literal_difference_eq_cleared 11 (by norm_num)
  have hD := (eq_div_iff (clearing_denominator_ne_zero 11)).mp hdiff
  have hrat : (clearedDifference 11 : ℚ) =
      (11 : ℚ) ^ 5 *
        (-6702852754925649907122189497429545875359720448306050246400 : ℚ) := by
    rw [← hD]
    norm_num [literalSum, literalTerm, weightNat, clearingDenominatorNat,
      Finset.sum_range_succ, Nat.factorial]
  exact_mod_cast hrat

theorem literal_nineteen :
    RationalCongruent 19 5 (literalSum 19) (9 * (19 : ℚ) ^ 2) := by
  apply (literal_congruence_iff 19 (by norm_num) (by norm_num)).2
  refine ⟨-1308308407310665217314467757744748742863578185175823174653009311721241673865327511474808650331462900000000, ?_⟩
  have hdiff := literal_difference_eq_cleared 19 (by norm_num)
  have hD := (eq_div_iff (clearing_denominator_ne_zero 19)).mp hdiff
  have hrat : (clearedDifference 19 : ℚ) =
      (19 : ℚ) ^ 5 *
        (-1308308407310665217314467757744748742863578185175823174653009311721241673865327511474808650331462900000000 : ℚ) := by
    rw [← hD]
    norm_num [literalSum, literalTerm, weightNat, clearingDenominatorNat,
      Finset.sum_range_succ, Nat.factorial]
  exact_mod_cast hrat

end WPReview
