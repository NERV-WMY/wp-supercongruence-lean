import WPActualNativeCMLogValues

open scoped BigOperators
open WPActualGaussBottom WPActualGaussProper WPActualHarmonicCubeFilter
  WPActualPartialHarmonic

namespace WPActualHalfHarmonic

theorem actual_full_harmonic_zero (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    fieldHarmonic p (p - 1) = 0 := by
  have hn : p - 1 + 1 = p := by omega
  rw [← fieldHarmonic_Ico, hn]
  simpa [WPFiniteInversion.ell, one_pow, one_div] using
    WPFiniteInversion.ell_one_eq_zero p (by omega)

theorem ell_minus_one_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    WPFiniteInversion.ell p (-1) =
      -2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have he : WPFiniteInversion.entropyQuotient p (-1) =
      WPFiniteInversion.entropyQuotient p 2 := by
    unfold WPFiniteInversion.entropyQuotient
    norm_num only [show (1 - (-1) : ℤ) = 2 by norm_num,
      show (1 - 2 : ℤ) = -1 by norm_num]
    congr 1
    ring
  have hm := WPFiniteInversion.ell_eq_entropyQuotient p (by omega) (-1)
  have ht := WPFiniteInversion.ell_eq_entropyQuotient p (by omega) 2
  rw [he, ← ht] at hm
  have hm' : WPFiniteInversion.ell p (-1) = WPFiniteInversion.ell p 2 := by simpa using hm
  exact hm'.trans (WPFiniteInversion.ell_two_eq_fermat p (by omega))

/-- The exact harmonic sum through the original half-prime cutoff. -/
theorem actual_harmonic_half (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    fieldHarmonic p ((p - 1) / 2) =
      -2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have hn : p - 1 + 1 = p := by omega
  have hs := alternating_harmonic p (p - 1) hp (by omega)
  rw [hn, actual_full_harmonic_zero p hp, zero_sub] at hs
  have he : WPFiniteInversion.ell p (-1) =
      -(∑ j ∈ Finset.Ico 1 p, (-1 : ZMod p) ^ (j - 1) / (j : ZMod p)) := by
    unfold WPFiniteInversion.ell
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hpow := pow_succ (-1 : ZMod p) (j - 1)
    rw [Nat.sub_add_cancel hj1] at hpow
    rw [hpow]
    ring
  rw [hs, neg_neg] at he
  exact he.symm.trans (ell_minus_one_value p hp)

end WPActualHalfHarmonic
