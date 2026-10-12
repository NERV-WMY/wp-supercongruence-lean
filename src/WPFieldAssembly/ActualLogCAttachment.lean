import WPFieldAssembly.ActualLogCCarry
import WPFieldAssembly.ActualConicFiniteLog

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualJointGreen WPFieldAssembly.ActualLogCCarry

namespace WPFieldAssembly.ActualLogCAttachment

set_option maxHeartbeats 1000000

theorem finiteEvenSquaredQ_origin (p : ℕ) [Fact p.Prime] :
    (finiteEvenSquaredQ p).eval 0=0 := by
  have h := congrArg (fun P : ℚ[X] => P.eval 0) (finiteEvenSquaredQ_pullback p)
  simpa only [eval_comp, eval_pow, eval_X, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    finiteEvenLogQ_origin p] using h

/-- The old finite squared logarithm is identified by its source and origin. -/
theorem finiteEvenSquaredQ_eq_moving (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    finiteEvenSquaredQ p=ActualEntropyPolynomial.movingEvenQ p := by
  exact finite_squared_log_unique p _ (finiteEvenSquaredQ_source p hp)
    (finiteEvenSquaredQ_origin p)

theorem finiteConicLogQ_eq_narrow (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    finiteConicLogQ p=conicLogQ p := by
  rw [finiteConicLogQ, finiteEvenSquaredQ_eq_moving p hp]
  rfl

/-- This equality preserves the original integral C coefficient and its rational lift. -/
theorem finiteLogCIntegral_eq_narrow (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    finiteLogCIntegral p hp=logCIntegral p hp := by
  apply Subtype.ext
  rw [finiteLogCIntegral_value p hp, logCIntegral_value p hp,
    finiteConicLogQ_eq_narrow p hp]

theorem actual_finite_C_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    finiteLogCIntegral p hp=-3*smallIntegralInverse p 2+
      (p : integralRationals p)*logCDigitIntegral p := by
  have h := logCDigitIntegral_value p hp
  have he := (eq_div_iff
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0)).mp h
  apply Subtype.ext
  change (finiteLogCIntegral p hp).val=(integralRationals p).subtype
    (-3*smallIntegralInverse p 2+(p : integralRationals p)*logCDigitIntegral p)
  rw [finiteLogCIntegral_eq_narrow p hp, map_add, map_mul, map_mul, map_neg,
    map_ofNat, map_natCast]
  change (logCIntegral p hp).val=-3*(smallIntegralInverse p 2).val+
    (p : ℚ)*(logCDigitIntegral p).val
  rw [smallIntegralInverse_value p 2 (by omega) (by omega)]
  linear_combination -he

theorem actual_finite_C_first_difference (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (logCDigitIntegral p).val=((finiteLogCIntegral p hp).val+3/2)/(p : ℚ) := by
  rw [finiteLogCIntegral_eq_narrow p hp]
  exact logCDigitIntegral_value p hp

end WPFieldAssembly.ActualLogCAttachment
