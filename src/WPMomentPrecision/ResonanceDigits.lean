import WPActualResidueVanishing
import WPFirstResidue.NC59Export

open WPActualEtaPrimitive WPActualEtaIntegrality WPActualResidueVanishing
  WPActualChiSource WPPIntegralReduction

namespace WPMomentPrecision.ResonanceDigits

/-- The literal divided NC62 coefficient at its original complete cutoff. -/
noncomputable def actualResonanceDigit (p : ℕ) (k : ℤ) : ℚ :=
  actualResidue p ((p - 1) / 2) (p - 1 - p / 6) k / (p : ℚ)

theorem actual_resonance_exact_digit (p : ℕ) [Fact p.Prime] (k : ℤ) :
    actualResidue p ((p - 1) / 2) (p - 1 - p / 6) k =
      (p : ℚ) * actualResonanceDigit p k := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  unfold actualResonanceDigit
  field_simp [hp]

theorem actual_residue_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (k : ℤ) :
    0 ≤ padicValRat p (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) k) := by
  have hd := Nat.div_mul_le_self p 6
  exact actual_Peta_integral p (p - 1 - p / 6) (by omega) (by omega) (by omega)
    (k * (p : ℤ) - 1)

/-- Only the three actual noncentral slots are divided using NC45. -/
theorem actual_resonance_digit_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (k : ℤ) (hk : k = -1 ∨ k = 1 ∨ k = 2) :
    0 ≤ padicValRat p (actualResonanceDigit p k) := by
  have hz := literal_three_residues_zero p hp
  have hzero : (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) k : ZMod p) = 0 := by
    rcases hk with rfl | rfl | rfl
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2
  exact divide_prime_integral p _ (actual_residue_integral p hp k) hzero

theorem actual_negative_digit_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualResonanceDigit p (-1)) :=
  actual_resonance_digit_integral p hp (-1) (Or.inl rfl)

theorem actual_first_positive_digit_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualResonanceDigit p 1) :=
  actual_resonance_digit_integral p hp 1 (Or.inr (Or.inl rfl))

theorem actual_second_positive_digit_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualResonanceDigit p 2) :=
  actual_resonance_digit_integral p hp 2 (Or.inr (Or.inr rfl))

end WPMomentPrecision.ResonanceDigits
