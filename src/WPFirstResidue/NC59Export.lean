import WPFirstResidue.NativeResidueIntegration

open WPPIntegralReduction WPActualChiSource

namespace WPFirstResidue

/-- The next central digit uses the literal integer-Fermat-quotient lift
before division, together with the original full-cutoff rational residue. -/
noncomputable def actualRho (p : ℕ) : ℚ :=
  (LiteralNormalization.actualFirstResidue p - LiteralNormalization.literalR0 p) / (p : ℚ)

theorem actual_first_residue_exact_digit (p : ℕ) [Fact p.Prime] :
    LiteralNormalization.actualFirstResidue p = LiteralNormalization.literalR0 p +
      (p : ℚ) * actualRho p := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  unfold actualRho
  field_simp [hp]
  ring

theorem actual_rho_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualRho p) := by
  let a : integralRationals p :=
    ⟨LiteralNormalization.actualFirstResidue p,
      LiteralNormalization.actualFirstResidue_integral p hp⟩
  let b : integralRationals p :=
    ⟨LiteralNormalization.literalR0 p, LiteralNormalization.literalR0_integral p hp⟩
  have hi : 0 ≤ padicValRat p
      (LiteralNormalization.actualFirstResidue p - LiteralNormalization.literalR0 p) :=
    (a - b).property
  have hz : ((LiteralNormalization.actualFirstResidue p -
      LiteralNormalization.literalR0 p : ℚ) : ZMod p) = 0 := by
    change residueHom p (a - b) = 0
    rw [map_sub]
    change (LiteralNormalization.actualFirstResidue p : ZMod p) -
      (LiteralNormalization.literalR0 p : ZMod p) = 0
    exact sub_eq_zero.mpr (NativeResidue.actual_first_residue_literal_field p hp)
  exact divide_prime_integral p _ hi hz

noncomputable def integralActualRho (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p := ⟨actualRho p, actual_rho_integral p hp⟩

theorem integralActualRho_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralActualRho p hp).val =
      (LiteralNormalization.actualFirstResidue p - LiteralNormalization.literalR0 p) /
        (p : ℚ) := rfl

end WPFirstResidue
