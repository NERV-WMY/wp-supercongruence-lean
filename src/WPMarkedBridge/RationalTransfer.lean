import WPCompletedCartier.ScalarBridge

namespace WPMarkedBridge

noncomputable section

open WPCompletedCartier.ScalarBridge

/-- The field congruence detects the literal rational valuation, including zero. -/
theorem rationalCongruent_of_qpCongruent (p precision : ℕ) [Fact p.Prime]
    (a b : ℚ) (h : QpCongruent p precision (a : ℚ_[p]) (b : ℚ_[p])) :
    WPReview.RationalCongruent p precision a b := by
  by_cases he : a = b
  · exact Or.inl he
  · apply Or.inr
    have hz : a - b ≠ 0 := sub_ne_zero.mpr he
    have hn := (qpCongruent_iff_norm p precision _ _).mp h
    rw [← Rat.cast_sub, Padic.eq_padicNorm,
      padicNorm.eq_zpow_of_nonzero hz, Rat.cast_zpow, Rat.cast_natCast] at hn
    have hpReal : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Fact.out : p.Prime).one_lt
    have hv := (zpow_le_zpow_iff_right₀ hpReal).mp hn
    exact le_of_neg_le_neg hv

theorem rationalCongruent_iff_qpCongruent (p precision : ℕ) [Fact p.Prime]
    (a b : ℚ) :
    WPReview.RationalCongruent p precision a b ↔
      QpCongruent p precision (a : ℚ_[p]) (b : ℚ_[p]) :=
  ⟨rationalCongruent_cast p precision a b,
    rationalCongruent_of_qpCongruent p precision a b⟩

end
end WPMarkedBridge
