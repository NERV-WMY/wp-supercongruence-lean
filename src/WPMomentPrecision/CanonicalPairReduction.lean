import WPActualNativeRemainderProjection
import WPActualPositiveResidueCarry

open scoped Polynomial LaurentPolynomial
open WPActualNativeCanonicalPart WPActualCanonicalFinitePart
  WPActualNativeRemainderProjection WPCartierPoleProjection

namespace WPMomentPrecision.ResonancePair

variable (p : ℕ) [Fact p.Prime]

/-- Original endpoint/negative-half functional of the source-selected B0. -/
noncomputable def Bpair (hp : 19 ≤ p) : ZMod p :=
  (29 / 6) * valueAt p (nativeRemainder p hp) (1 / 4) -
    (23 / 6) * valueAt p (nativeRemainder p hp) 4 +
    2 * (-2 * negativeValue p (nativeRemainder p hp) (1 / 4) -
      negativeValue p (nativeRemainder p hp) 4)

noncomputable def C0 : ZMod p := (pullbackPolynomial p (nativeHJet p)).coeff 0

noncomputable def Up : ZMod p :=
  (625 / 216) *
    (WPActualEtaIntegration.canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) : ZMod p)

noncomputable def Ubar : ZMod p :=
  Up p - (113 / 28) * (WPActualPositiveResidueCarry.positiveDigit p 1 : ZMod p)

theorem C0_original_endpoint :
    C0 p = (nativeHJet p).eval (4 / 125) := by
  rw [C0, Polynomial.coeff_zero_eq_eval_zero, pullbackPolynomial, Polynomial.eval_comp]
  congr 1
  norm_num [WPHasseIntegralTransport.fieldV, Rat.cast_def]
  ring

/-- The checked NC77a identity is applied to the whole actual H_J. -/
theorem actual_positive_pair_zero (hp : 19 ≤ p) :
    8 * valueAt p (WPActualPositivePair.lowPart p
        (Polynomial.toLaurent (pullbackPolynomial p (nativeHJet p)))) (1 / 4) +
      valueAt p (WPActualPositivePair.lowPart p
        (Polynomial.toLaurent (pullbackPolynomial p (nativeHJet p)))) 4 / 4 = 0 :=
  actual_native_pullback_low_pair_zero p hp

/-- The positive digit cancels only after both actual endpoint/high-half pieces are paired. -/
theorem actual_Up_positive_pair (hp : 19 ≤ p) :
    Up p = (113 / 28) * (WPActualPositiveResidueCarry.positiveDigit p 1 : ZMod p) +
      Bpair p hp - C0 p / 6 := by
  have hsmall (n : ℕ) (hn : 0 < n) (hlt : n < p) : (n : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff n p).mp hz)
    omega
  have h2 : (2 : ZMod p) ≠ 0 := hsmall 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := hsmall 3 (by omega) (by omega)
  have h7 : (7 : ZMod p) ≠ 0 := hsmall 7 (by omega) (by omega)
  have h12 : (12 : ZMod p) ≠ 0 := by
    rw [show (12 : ZMod p) = 2 ^ 2 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero _ h2) h3
  have h28 : (28 : ZMod p) ≠ 0 := by
    rw [show (28 : ZMod p) = 2 ^ 2 * 7 by ring]
    exact mul_ne_zero (pow_ne_zero _ h2) h7
  have h336 : (336 : ZMod p) ≠ 0 := by
    rw [show (336 : ZMod p) = 2 ^ 4 * 3 * 7 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h3) h7
  have hcoef (c : ZMod p) : (113 / 336) * c = (113 / 28) * (c / 12) := by
    field_simp [h12, h28, h336]
    ring
  have h := actual_native_normalized_period p hp
  change Up p = Bpair p hp - C0 p / 6 +
    (113 / 336) * (pullbackPolynomial p (nativeHJet p)).coeff p at h
  rw [h, hcoef, ← WPActualPositiveResidueCarry.actual_first_positive_digit p hp]
  ring

/-- Exact NC77b, retaining the original negative half and the common C0 term. -/
theorem actual_Ubar_pair (hp : 19 ≤ p) :
    Ubar p = Bpair p hp - C0 p / 6 := by
  rw [Ubar, actual_Up_positive_pair p hp]
  ring

end WPMomentPrecision.ResonancePair
