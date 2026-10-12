import WPActualCentralNativeJet

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPNativeParameterTaylor WPActualNativeHasse
  WPActualNativeParameter WPActualNativeFirstJet

namespace WPActualNativeJetRecurrence

noncomputable def upperFactor (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  (C (6 * (n : R) + 1) + 6 * X) * (C (2 * (n : R) + 1) + 2 * X) *
    (C (6 * (n : R) + 5) + 6 * X)

noncomputable def lowerFactor (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  C (72 * ((n : R) + 1)) * (C ((n : R) + 1) + X) *
    (C ((n : R) + 1) + 2 * X)

theorem actual_parameter_numerator_succ (R : Type*) [CommRing R] (n : ℕ) :
    clearedNumerator R (n + 1) = clearedNumerator R n * upperFactor R n := by
  simp only [clearedNumerator, Finset.prod_range_succ, upperFactor]

theorem actual_parameter_denominator_succ (R : Type*) [CommRing R] (n : ℕ) :
    clearedDenominator R (n + 1) = clearedDenominator R n * lowerFactor R n := by
  simp only [clearedDenominator, Finset.prod_range_succ, lowerFactor]

/-- Exact quotient differentiation; no analytic or infinite series is used. -/
theorem quotientJet_product_recurrence (A D U L : ℚ[X]) (t : ℚ)
    (hD : D.eval t ≠ 0) (hL : L.eval t ≠ 0) :
    L.eval t * quotientJet (A * U) (D * L) t +
      L.derivative.eval t * ((A * U).eval t / (D * L).eval t) =
    U.eval t * quotientJet A D t + U.derivative.eval t * (A.eval t / D.eval t) := by
  simp only [quotientJet, Polynomial.derivative_mul, Polynomial.eval_mul, Polynomial.eval_add]
  field_simp [hD, hL]
  ring

theorem actual_native_parameter_jet_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    (lowerFactor ℚ n).eval (-(p : ℚ) / 6) * parameterJet (n + 1) (-(p : ℚ) / 6) +
      (lowerFactor ℚ n).derivative.eval (-(p : ℚ) / 6) *
        parameterCoefficient (n + 1) (-(p : ℚ) / 6) =
    (upperFactor ℚ n).eval (-(p : ℚ) / 6) * parameterJet n (-(p : ℚ) / 6) +
      (upperFactor ℚ n).derivative.eval (-(p : ℚ) / 6) *
        parameterCoefficient n (-(p : ℚ) / 6) := by
  have hDn : (clearedDenominator ℚ n).eval (-(p : ℚ) / 6) ≠ 0 := by
    have h := (denominator_node_unit p n hp (by omega)).1
    rw [evaluate_subtype, clearedDenominator_map, integralNode_value] at h
    exact h
  have hDnext : (clearedDenominator ℚ (n + 1)).eval (-(p : ℚ) / 6) ≠ 0 := by
    have h := (denominator_node_unit p (n + 1) hp hn).1
    rw [evaluate_subtype, clearedDenominator_map, integralNode_value] at h
    exact h
  have hL : (lowerFactor ℚ n).eval (-(p : ℚ) / 6) ≠ 0 := by
    rw [actual_parameter_denominator_succ, Polynomial.eval_mul] at hDnext
    exact (mul_ne_zero_iff.mp hDnext).2
  unfold parameterJet parameterCoefficient
  rw [actual_parameter_numerator_succ, actual_parameter_denominator_succ]
  exact quotientJet_product_recurrence _ _ _ _ _ hDn hL

theorem lowerFactor_origin (R : Type*) [CommRing R] (n : ℕ) :
    (lowerFactor R n).eval 0 = 72 * ((n : R) + 1) ^ 3 := by
  simp only [lowerFactor, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, mul_zero, add_zero]
  ring

theorem lowerFactor_derivative_origin (R : Type*) [CommRing R] (n : ℕ) :
    (lowerFactor R n).derivative.eval 0 = 216 * ((n : R) + 1) ^ 2 := by
  simp only [lowerFactor, Polynomial.derivative_mul, Polynomial.derivative_add,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_ofNat,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, mul_zero, zero_mul, add_zero, zero_add, mul_one]
  ring

theorem upperFactor_origin (R : Type*) [CommRing R] (n : ℕ) :
    (upperFactor R n).eval 0 =
      (2 * (n : R) + 1) * (6 * (n : R) + 1) * (6 * (n : R) + 5) := by
  simp only [upperFactor, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, mul_zero, add_zero]
  ring

theorem upperFactor_derivative_origin (R : Type*) [CommRing R] (n : ℕ) :
    (upperFactor R n).derivative.eval 0 = 216 * (n : R) ^ 2 + 216 * (n : R) + 46 := by
  simp only [upperFactor, Polynomial.derivative_mul, Polynomial.derivative_add,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_ofNat,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, mul_zero, zero_mul, add_zero, zero_add, mul_one]
  ring

theorem upperFactor_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) : (upperFactor R n).map f = upperFactor S n := by
  simp only [upperFactor, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_ofNat,
    Polynomial.map_X, Polynomial.map_natCast, Polynomial.map_one,
    map_add, map_mul, map_ofNat, map_natCast, map_one]

theorem lowerFactor_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) : (lowerFactor R n).map f = lowerFactor S n := by
  simp only [lowerFactor, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_ofNat,
    Polynomial.map_X, Polynomial.map_natCast, Polynomial.map_one,
    map_add, map_mul, map_ofNat, map_natCast, map_one]

/-- The actual terminating coefficient with its original denominator inverse. -/
noncomputable def integralParameterCoefficient (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : integralRationals p :=
  (clearedNumerator (integralRationals p) n).eval (integralNode p hp) *
    ⟨((clearedDenominator (integralRationals p) n).eval (integralNode p hp)).val⁻¹,
      (denominator_node_unit p n hp hn).2⟩

theorem integralParameterCoefficient_value (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (integralParameterCoefficient p n hp hn).val =
      parameterCoefficient n (-(p : ℚ) / 6) := by
  change ((clearedNumerator (integralRationals p) n).eval (integralNode p hp)).val *
    ((clearedDenominator (integralRationals p) n).eval (integralNode p hp)).val⁻¹ = _
  rw [evaluate_subtype, evaluate_subtype, clearedNumerator_map, clearedDenominator_map,
    integralNode_value]
  exact (div_eq_mul_inv _ _).symm

theorem actual_parameterCoefficient_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    0 ≤ padicValRat p (parameterCoefficient n (-(p : ℚ) / 6)) := by
  rw [← integralParameterCoefficient_value p n hp hn]
  exact (integralParameterCoefficient p n hp hn).property

theorem actual_parameterCoefficient_residue (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    residueHom p (integralParameterCoefficient p n hp hn) =
      (WPReview.nativeCoefficient n : ZMod p) := by
  obtain ⟨r, hr⟩ := actual_native_first_remainder p n hp hn
  let R := integralRationals p
  let c : R := ⟨WPReview.nativeCoefficient n, actual_native_coefficient_integral p n hp hn⟩
  let j := integralParameterJet p n hp hn
  let t := integralParameterCoefficient p n hp hn
  let s : R := ⟨1 / 6,
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)⟩
  have hR : c - t - (p : R) * s * j = (p : R) ^ 2 * s ^ 2 * r := by
    apply Subtype.ext
    change WPReview.nativeCoefficient n - t.val - (p : ℚ) * (1 / 6 : ℚ) * j.val =
      (p : ℚ) ^ 2 * (1 / 6 : ℚ) ^ 2 * r.val
    rw [integralParameterCoefficient_value, integralParameterJet_value]
    convert hr using 1 <;> ring
  have hf := congrArg (residueHom p) hR
  simp only [map_sub, map_mul, map_pow, map_natCast, ZMod.natCast_self,
    zero_mul, zero_pow (by omega : 2 ≠ 0), sub_zero] at hf
  exact (sub_eq_zero.mp hf).symm

theorem upperFactor_node_residue (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p ((upperFactor (integralRationals p) n).eval (integralNode p hp)) =
      (2 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 5) := by
  rw [← Polynomial.eval_map_apply, upperFactor_map, integralNode_residue, upperFactor_origin]

theorem lowerFactor_node_residue (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p ((lowerFactor (integralRationals p) n).eval (integralNode p hp)) =
      72 * ((n : ZMod p) + 1) ^ 3 := by
  rw [← Polynomial.eval_map_apply, lowerFactor_map, integralNode_residue, lowerFactor_origin]

theorem upperFactor_derivative_node_residue (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p ((upperFactor (integralRationals p) n).derivative.eval (integralNode p hp)) =
      216 * (n : ZMod p) ^ 2 + 216 * (n : ZMod p) + 46 := by
  rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map,
    upperFactor_map, integralNode_residue, upperFactor_derivative_origin]

theorem lowerFactor_derivative_node_residue (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p ((lowerFactor (integralRationals p) n).derivative.eval (integralNode p hp)) =
      216 * ((n : ZMod p) + 1) ^ 2 := by
  rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map,
    lowerFactor_map, integralNode_residue, lowerFactor_derivative_origin]

/-- The differentiated original finite recurrence over the actual integral subring. -/
theorem actual_integral_native_jet_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    (lowerFactor (integralRationals p) n).eval (integralNode p hp) *
        integralParameterJet p (n + 1) hp hn +
      (lowerFactor (integralRationals p) n).derivative.eval (integralNode p hp) *
        integralParameterCoefficient p (n + 1) hp hn =
    (upperFactor (integralRationals p) n).eval (integralNode p hp) *
        integralParameterJet p n hp (by omega) +
      (upperFactor (integralRationals p) n).derivative.eval (integralNode p hp) *
        integralParameterCoefficient p n hp (by omega) := by
  apply Subtype.ext
  change
    ((lowerFactor (integralRationals p) n).eval (integralNode p hp)).val *
        (integralParameterJet p (n + 1) hp hn).val +
      ((lowerFactor (integralRationals p) n).derivative.eval (integralNode p hp)).val *
        (integralParameterCoefficient p (n + 1) hp hn).val =
    ((upperFactor (integralRationals p) n).eval (integralNode p hp)).val *
        (integralParameterJet p n hp (by omega)).val +
      ((upperFactor (integralRationals p) n).derivative.eval (integralNode p hp)).val *
        (integralParameterCoefficient p n hp (by omega)).val
  rw [derivative_evaluate_subtype, derivative_evaluate_subtype]
  simp only [evaluate_subtype, lowerFactor_map, upperFactor_map, integralNode_value,
    integralParameterJet_value, integralParameterCoefficient_value]
  exact actual_native_parameter_jet_recurrence p n hp hn

/-- IR10b, coefficient by coefficient, with the actual native first jet. -/
theorem actual_native_jet_field_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    72 * ((n : ZMod p) + 1) ^ 3 * (parameterJet (n + 1) (-(p : ℚ) / 6) : ZMod p) -
      ((2 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 5)) *
        (parameterJet n (-(p : ℚ) / 6) : ZMod p) =
    -(216 * ((n : ZMod p) + 1) ^ 2 * (WPReview.nativeCoefficient (n + 1) : ZMod p)) +
      (216 * (n : ZMod p) ^ 2 + 216 * (n : ZMod p) + 46) *
        (WPReview.nativeCoefficient n : ZMod p) := by
  have hf := congrArg (residueHom p) (actual_integral_native_jet_recurrence p n hp hn)
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul,
    lowerFactor_node_residue, upperFactor_node_residue,
    lowerFactor_derivative_node_residue, upperFactor_derivative_node_residue,
    actual_parameterCoefficient_residue, actual_parameterCoefficient_residue] at hf
  have hj (m : ℕ) (hm : m < p) : residueHom p (integralParameterJet p m hp hm) =
      (parameterJet m (-(p : ℚ) / 6) : ZMod p) := by
    change ((integralParameterJet p m hp hm).val : ZMod p) = _
    rw [integralParameterJet_value]
  rw [hj, hj] at hf
  linear_combination hf

end WPActualNativeJetRecurrence
