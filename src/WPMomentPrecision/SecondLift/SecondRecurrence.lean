import WPMomentPrecision.SecondLift.FullNativeTaylor

open scoped Polynomial
open Polynomial WPPIntegralReduction WPNativeParameterTaylor WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeSecondJet WPActualNativeJetRecurrence
  WPMomentPrecision.FullNativeTaylor

namespace WPMomentPrecision.SecondRecurrence

set_option maxHeartbeats 1200000

/-- Exact second differentiation of the original finite quotient recurrence. -/
theorem quotientFullSecondJet_product_recurrence (A D U L : ℚ[X]) (t : ℚ)
    (hD : D.eval t ≠ 0) (hL : L.eval t ≠ 0) :
    L.eval t * quotientFullSecondJet (A * U) (D * L) t +
        2 * L.derivative.eval t * quotientJet (A * U) (D * L) t +
        L.derivative.derivative.eval t * ((A * U).eval t / (D * L).eval t) =
      U.eval t * quotientFullSecondJet A D t +
        2 * U.derivative.eval t * quotientJet A D t +
        U.derivative.derivative.eval t * (A.eval t / D.eval t) := by
  simp only [quotientFullSecondJet, quotientJet, derivative_mul, derivative_add,
    eval_mul, eval_add]
  field_simp [hD, hL]
  ring

/-- The literal full second jet at epsilon=-p/6, before any field reduction. -/
theorem actual_native_full_second_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    (lowerFactor ℚ n).eval (-(p : ℚ) / 6) * nativeFullSecondJetCoefficient p (n + 1) +
        2 * (lowerFactor ℚ n).derivative.eval (-(p : ℚ) / 6) *
          parameterJet (n + 1) (-(p : ℚ) / 6) +
        (lowerFactor ℚ n).derivative.derivative.eval (-(p : ℚ) / 6) *
          parameterCoefficient (n + 1) (-(p : ℚ) / 6) =
      (upperFactor ℚ n).eval (-(p : ℚ) / 6) * nativeFullSecondJetCoefficient p n +
        2 * (upperFactor ℚ n).derivative.eval (-(p : ℚ) / 6) *
          parameterJet n (-(p : ℚ) / 6) +
        (upperFactor ℚ n).derivative.derivative.eval (-(p : ℚ) / 6) *
          parameterCoefficient n (-(p : ℚ) / 6) := by
  have hD : (clearedDenominator ℚ n).eval (-(p : ℚ) / 6) ≠ 0 := by
    have h := (denominator_node_unit p n hp (by omega)).1
    rwa [evaluate_subtype, clearedDenominator_map, integralNode_value] at h
  have hDn : (clearedDenominator ℚ (n + 1)).eval (-(p : ℚ) / 6) ≠ 0 := by
    have h := (denominator_node_unit p (n + 1) hp hn).1
    rwa [evaluate_subtype, clearedDenominator_map, integralNode_value] at h
  rw [actual_parameter_denominator_succ, eval_mul] at hDn
  have hL := (mul_ne_zero_iff.mp hDn).2
  unfold nativeFullSecondJetCoefficient parameterJet parameterCoefficient
  rw [actual_parameter_numerator_succ, actual_parameter_denominator_succ]
  exact quotientFullSecondJet_product_recurrence _ _ _ _ _ hD hL

noncomputable def integralFullSecondCoefficient (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : integralRationals p :=
  2 * integralParameterSecondJet p n hp hn

theorem integralFullSecondCoefficient_value (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (integralFullSecondCoefficient p n hp hn).val = nativeFullSecondJetCoefficient p n := by
  rw [nativeFullSecondJetCoefficient_eq_twice]
  change 2 * (integralParameterSecondJet p n hp hn).val = _
  rw [integralParameterSecondJet_value]

theorem derivative_twice_evaluate_subtype (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) (t : integralRationals p) :
    (P.derivative.derivative.eval t).val =
      (P.map (integralRationals p).subtype).derivative.derivative.eval t.val := by
  rw [evaluate_subtype, Polynomial.derivative_map, Polynomial.derivative_map]

theorem actual_integral_native_full_second_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    (lowerFactor (integralRationals p) n).eval (integralNode p hp) *
        integralFullSecondCoefficient p (n + 1) hp hn +
      2 * (lowerFactor (integralRationals p) n).derivative.eval (integralNode p hp) *
        integralParameterJet p (n + 1) hp hn +
      (lowerFactor (integralRationals p) n).derivative.derivative.eval
          (integralNode p hp) * integralParameterCoefficient p (n + 1) hp hn =
    (upperFactor (integralRationals p) n).eval (integralNode p hp) *
        integralFullSecondCoefficient p n hp (by omega) +
      2 * (upperFactor (integralRationals p) n).derivative.eval (integralNode p hp) *
        integralParameterJet p n hp (by omega) +
      (upperFactor (integralRationals p) n).derivative.derivative.eval
          (integralNode p hp) * integralParameterCoefficient p n hp (by omega) := by
  apply Subtype.ext
  change
    ((lowerFactor (integralRationals p) n).eval (integralNode p hp)).val *
        (integralFullSecondCoefficient p (n + 1) hp hn).val +
      2 * ((lowerFactor (integralRationals p) n).derivative.eval (integralNode p hp)).val *
        (integralParameterJet p (n + 1) hp hn).val +
      ((lowerFactor (integralRationals p) n).derivative.derivative.eval
          (integralNode p hp)).val * (integralParameterCoefficient p (n + 1) hp hn).val =
    ((upperFactor (integralRationals p) n).eval (integralNode p hp)).val *
        (integralFullSecondCoefficient p n hp (by omega)).val +
      2 * ((upperFactor (integralRationals p) n).derivative.eval (integralNode p hp)).val *
        (integralParameterJet p n hp (by omega)).val +
      ((upperFactor (integralRationals p) n).derivative.derivative.eval
          (integralNode p hp)).val * (integralParameterCoefficient p n hp (by omega)).val
  rw [derivative_twice_evaluate_subtype, derivative_twice_evaluate_subtype,
    derivative_evaluate_subtype, derivative_evaluate_subtype]
  simp only [evaluate_subtype, lowerFactor_map, upperFactor_map, integralNode_value,
    integralFullSecondCoefficient_value, integralParameterJet_value,
    integralParameterCoefficient_value]
  exact actual_native_full_second_recurrence p n hp hn

theorem lowerFactor_second_derivative_origin {R : Type*} [CommRing R] (n : ℕ) :
    (lowerFactor R n).derivative.derivative.eval 0 = 288 * ((n : R) + 1) := by
  simp [lowerFactor, derivative_mul, map_mul, map_add, map_ofNat]
  ring

theorem upperFactor_second_derivative_origin {R : Type*} [CommRing R] (n : ℕ) :
    (upperFactor R n).derivative.derivative.eval 0 = 432 * (n : R) + 216 := by
  simp [upperFactor, derivative_mul, map_mul, map_add, map_ofNat]
  ring

theorem second_derivative_lower_node_residue (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p ((lowerFactor (integralRationals p) n).derivative.derivative.eval
      (integralNode p hp)) = 288 * ((n : ZMod p) + 1) := by
  rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map,
    ← Polynomial.derivative_map, lowerFactor_map, integralNode_residue,
    lowerFactor_second_derivative_origin]

theorem second_derivative_upper_node_residue (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p ((upperFactor (integralRationals p) n).derivative.derivative.eval
      (integralNode p hp)) = 432 * (n : ZMod p) + 216 := by
  rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map,
    ← Polynomial.derivative_map, upperFactor_map, integralNode_residue,
    upperFactor_second_derivative_origin]

/-- The actual full second native recurrence, with every first and second source term. -/
theorem actual_native_full_second_field_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    72 * ((n : ZMod p) + 1) ^ 3 * (nativeFullSecondJetCoefficient p (n + 1) : ZMod p) -
      ((2 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 5)) *
        (nativeFullSecondJetCoefficient p n : ZMod p) =
      -432 * ((n : ZMod p) + 1) ^ 2 *
          (parameterJet (n + 1) (-(p : ℚ) / 6) : ZMod p) +
        2 * (216 * (n : ZMod p) ^ 2 + 216 * (n : ZMod p) + 46) *
          (parameterJet n (-(p : ℚ) / 6) : ZMod p) -
        288 * ((n : ZMod p) + 1) * (WPReview.nativeCoefficient (n + 1) : ZMod p) +
        (432 * (n : ZMod p) + 216) * (WPReview.nativeCoefficient n : ZMod p) := by
  have hf := congrArg (residueHom p)
    (actual_integral_native_full_second_recurrence p n hp hn)
  simp only [map_add, map_mul, map_ofNat] at hf
  rw [lowerFactor_node_residue, upperFactor_node_residue,
    lowerFactor_derivative_node_residue, upperFactor_derivative_node_residue,
    second_derivative_lower_node_residue, second_derivative_upper_node_residue,
    actual_parameterCoefficient_residue, actual_parameterCoefficient_residue] at hf
  have hj (m : ℕ) (hm : m < p) : residueHom p (integralParameterJet p m hp hm) =
      (parameterJet m (-(p : ℚ) / 6) : ZMod p) := by
    change ((integralParameterJet p m hp hm).val : ZMod p) = _
    rw [integralParameterJet_value]
  have hk (m : ℕ) (hm : m < p) :
      residueHom p (integralFullSecondCoefficient p m hp hm) =
        (nativeFullSecondJetCoefficient p m : ZMod p) := by
    change ((integralFullSecondCoefficient p m hp hm).val : ZMod p) = _
    rw [integralFullSecondCoefficient_value]
  rw [hj, hj, hk, hk] at hf
  linear_combination hf

end WPMomentPrecision.SecondRecurrence
