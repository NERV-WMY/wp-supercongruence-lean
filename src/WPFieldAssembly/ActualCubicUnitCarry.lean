import WPFieldAssembly.ActualFiniteEntropyCarry
import WPActualPartialHarmonic

open WPPIntegralReduction WPActualRankTwoHatLift
  WPActualHarmonicCubicTrace WPActualGaussProper

namespace WPFieldAssembly.ActualCubicUnitCarry

set_option maxHeartbeats 1000000

/-- The integer cubic trace fixes the actual principal unit in both prime classes. -/
theorem literal_cubic_unit_equation (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteInversion.integerFermatQuotient p 3 =
      2*cubicQuotientSum p (-1)+(p : ℤ)*(cubicQuotientSum p (-1))^2 := by
  let S := cubicQuotientSum p (-1)
  let T := cubicTrace ((1-cubicOmega)^p)
  have ht : T=3+3*(p : ℤ)*S := by
    have h := cubicQuotientSum_minus_source p (by omega)
    change T-3=3*(p : ℤ)*S at h
    linear_combination h
  have hsq := cubicTrace_minus_prime_square p (by omega)
  change T^2=9*(3 : ℤ)^(p-1) at hsq
  rw [ht] at hsq
  have hnum : (3 : ℤ)^(p-1)-1=2*(p : ℤ)*S+(p : ℤ)^2*S^2 := by
    nlinarith [hsq]
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have hq := WPFiniteInversion.integerFermatQuotient_mul p 3 (by simpa using h3)
  rw [hnum] at hq
  apply mul_right_cancel₀
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
  linear_combination hq

/-- This carry is constructed before reduction, from the exact integer cubic trace. -/
noncomputable def cubicUnitCarryIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  -(cubicQuotientSum p (-1) : integralRationals p)^2*smallIntegralInverse p 2

theorem actual_cubic_unit_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (cubicQuotientSum p (-1) : integralRationals p)=
      (WPFiniteInversion.integerFermatQuotient p 3 : integralRationals p)*
        smallIntegralInverse p 2+(p : integralRationals p)*cubicUnitCarryIntegral p := by
  apply Subtype.ext
  have h : (WPFiniteInversion.integerFermatQuotient p 3 : ℚ)=
      2*(cubicQuotientSum p (-1) : ℚ)+(p : ℚ)*(cubicQuotientSum p (-1) : ℚ)^2 := by
    exact_mod_cast literal_cubic_unit_equation p hp
  change (cubicQuotientSum p (-1) : ℚ)=_
  change (cubicQuotientSum p (-1) : ℚ)=
    (WPFiniteInversion.integerFermatQuotient p 3 : ℚ)*
      (smallIntegralInverse p 2).val+(p : ℚ)*
        (-(cubicQuotientSum p (-1) : ℚ)^2*(smallIntegralInverse p 2).val)
  rw [smallIntegralInverse_value p 2 (by omega) (by omega)]
  linear_combination -(1/2 : ℚ)*h

theorem cubicUnitCarryIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (cubicUnitCarryIntegral p).val=
      ((cubicQuotientSum p (-1) : ℚ)-
        (WPFiniteInversion.integerFermatQuotient p 3 : ℚ)/2)/(p : ℚ) := by
  have h := congrArg (integralRationals p).subtype (actual_cubic_unit_firstTaylor p hp)
  simp only [map_add, map_mul, map_natCast, map_intCast, Subring.subtype_apply,
    smallIntegralInverse_value p 2 (by omega) (by omega)] at h
  apply (eq_div_iff
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0)).2
  linear_combination -h

theorem cubicUnitCarryIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (cubicUnitCarryIntegral p)=
      -(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)^2/8 := by
  have hq := WPActualPartialHarmonic.cubicQuotientSum_minus_fermat p (by omega)
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h8 : (8 : ZMod p) ≠ 0 := small_cast_ne_zero p 8 (by omega) (by omega)
  rw [cubicUnitCarryIntegral, map_mul, map_neg, map_pow, map_intCast,
    smallIntegralInverse_field p 2 (by omega) (by omega), hq]
  field_simp [h2, h8]
  ring

end WPFieldAssembly.ActualCubicUnitCarry
