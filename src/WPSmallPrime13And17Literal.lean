import WPReview.Literal

namespace WPReview

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem literal_thirteen :
    RationalCongruent 13 5 (literalSum 13) (9 * (13 : ℚ) ^ 2) := by
  apply (literal_congruence_iff 13 (by norm_num) (by norm_num)).2
  refine ⟨-4070912026441464918395331972876309273211013438393853893417697102720000, ?_⟩
  have hdiff := literal_difference_eq_cleared 13 (by norm_num)
  have hD := (eq_div_iff (clearing_denominator_ne_zero 13)).mp hdiff
  have hrat : (clearedDifference 13 : ℚ) =
      (13 : ℚ) ^ 5 *
        (-4070912026441464918395331972876309273211013438393853893417697102720000 : ℚ) := by
    rw [← hD]
    norm_num [literalSum, literalTerm, weightNat, clearingDenominatorNat,
      Finset.sum_range_succ, Nat.factorial]
  exact_mod_cast hrat

theorem literal_seventeen :
    RationalCongruent 17 5 (literalSum 17) (9 * (17 : ℚ) ^ 2) := by
  apply (literal_congruence_iff 17 (by norm_num) (by norm_num)).2
  refine ⟨-1825184605938154922592300758361178267773894931773239567485481872002877386170036604050757210000, ?_⟩
  have hdiff := literal_difference_eq_cleared 17 (by norm_num)
  have hD := (eq_div_iff (clearing_denominator_ne_zero 17)).mp hdiff
  have hrat : (clearedDifference 17 : ℚ) =
      (17 : ℚ) ^ 5 *
        (-1825184605938154922592300758361178267773894931773239567485481872002877386170036604050757210000 : ℚ) := by
    rw [← hD]
    norm_num [literalSum, literalTerm, weightNat, clearingDenominatorNat,
      Finset.sum_range_succ, Nat.factorial]
  exact_mod_cast hrat

end WPReview
