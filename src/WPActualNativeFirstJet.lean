import WPActualNativeParameter

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPNativeParameterTaylor WPActualNativeHasse
  WPActualNativeParameter WPActualCentralResidueSource

namespace WPActualNativeFirstJet

theorem evaluate_subtype (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) (t : integralRationals p) :
    (P.eval t).val = (P.map (integralRationals p).subtype).eval t.val := by
  change (integralRationals p).subtype (P.eval t) =
    (P.map (integralRationals p).subtype).eval ((integralRationals p).subtype t)
  rw [Polynomial.eval_map_apply]

theorem derivative_evaluate_subtype (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) (t : integralRationals p) :
    (P.derivative.eval t).val = (P.map (integralRationals p).subtype).derivative.eval t.val := by
  rw [evaluate_subtype, Polynomial.derivative_map]

theorem denominator_origin_unit (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ((clearedDenominator (integralRationals p) n).eval 0).val ≠ 0 ∧
      (((clearedDenominator (integralRationals p) n).eval 0).val)⁻¹ ∈ integralRationals p := by
  apply integral_inverse_of_residue_ne_zero
  rw [← Polynomial.eval_map_apply, clearedDenominator_map, map_zero]
  exact denominator_origin_residue_ne_zero p n hp hn

/-- The whole exact IR10 coefficient Taylor identity with an integral remainder. -/
theorem actual_native_first_remainder (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ∃ r : integralRationals p,
      WPReview.nativeCoefficient n - parameterCoefficient n (-(p : ℚ) / 6) -
        (p : ℚ) / 6 * parameterJet n (-(p : ℚ) / 6) = (p : ℚ) ^ 2 / 36 * r.val := by
  have hu0 := denominator_origin_unit p n hp hn
  have hut := denominator_node_unit p n hp hn
  obtain ⟨r, hr⟩ := integral_quotient_first_remainder p
    (clearedNumerator (integralRationals p) n)
    (clearedDenominator (integralRationals p) n) (integralNode p hp)
    hu0.1 hut.1 hu0.2 hut.2
  rw [evaluate_subtype, evaluate_subtype, evaluate_subtype, evaluate_subtype,
    derivative_evaluate_subtype, derivative_evaluate_subtype,
    clearedNumerator_map, clearedDenominator_map, Subring.coe_zero,
    integralNode_value] at hr
  refine ⟨r, ?_⟩
  rw [← parameterCoefficient_origin n]
  dsimp [parameterCoefficient, parameterJet, quotientJet]
  linear_combination hr

/-- Literal finite quotient derivative lifted into the actual integral subring. -/
noncomputable def integralParameterJet (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : integralRationals p :=
  let A := clearedNumerator (integralRationals p) n
  let D := clearedDenominator (integralRationals p) n
  let t := integralNode p hp
  let u : integralRationals p := ⟨(D.eval t).val⁻¹, (denominator_node_unit p n hp hn).2⟩
  (A.derivative.eval t * D.eval t - A.eval t * D.derivative.eval t) * u ^ 2

theorem integralParameterJet_value (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (integralParameterJet p n hp hn).val = parameterJet n (-(p : ℚ) / 6) := by
  unfold integralParameterJet
  change
    (((clearedNumerator (integralRationals p) n).derivative.eval (integralNode p hp)).val *
        ((clearedDenominator (integralRationals p) n).eval (integralNode p hp)).val -
      ((clearedNumerator (integralRationals p) n).eval (integralNode p hp)).val *
        ((clearedDenominator (integralRationals p) n).derivative.eval (integralNode p hp)).val) *
      (((clearedDenominator (integralRationals p) n).eval (integralNode p hp)).val⁻¹) ^ 2 = _
  rw [derivative_evaluate_subtype, derivative_evaluate_subtype]
  simp only [evaluate_subtype, clearedNumerator_map, clearedDenominator_map,
    integralNode_value]
  simp only [parameterJet, quotientJet, div_eq_mul_inv, inv_pow]

theorem actual_parameterJet_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    0 ≤ padicValRat p (parameterJet n (-(p : ℚ) / 6)) := by
  rw [← integralParameterJet_value p n hp hn]
  exact (integralParameterJet p n hp hn).property

theorem actual_high_first_jet_coefficient (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (hd : p / 6 < n) :
    ((WPReview.nativeCoefficient n / (p : ℚ) : ℚ) : ZMod p) =
      (1 / 6 : ZMod p) * (parameterJet n (-(p : ℚ) / 6) : ZMod p) := by
  obtain ⟨r, hr⟩ := actual_native_first_remainder p n hp hn
  rw [parameterCoefficient, terminating_numerator_zero p n hp hd, zero_div,
    sub_zero] at hr
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hs : WPReview.nativeCoefficient n / (p : ℚ) -
      parameterJet n (-(p : ℚ) / 6) / 6 = (p : ℚ) * (r.val / 36) := by
    calc
      _ = (WPReview.nativeCoefficient n -
          (p : ℚ) / 6 * parameterJet n (-(p : ℚ) / 6)) / p := by field_simp
      _ = ((p : ℚ) ^ 2 / 36 * r.val) / p := by rw [hr]
      _ = _ := by field_simp
  let R := integralRationals p
  let c : R := ⟨WPReview.nativeCoefficient n / (p : ℚ),
    actual_native_first_high_integral p n hp hn hd⟩
  let j := integralParameterJet p n hp hn
  let s : R := ⟨1 / 6,
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)⟩
  have hR : c - j * s = (p : R) * (r * s ^ 2) := by
    apply Subtype.ext
    change WPReview.nativeCoefficient n / (p : ℚ) - j.val * (1 / 6 : ℚ) =
      (p : ℚ) * (r.val * (1 / 6 : ℚ) ^ 2)
    rw [integralParameterJet_value]
    convert hs using 1 <;> ring
  have hf := congrArg (residueHom p) hR
  rw [map_sub, map_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul] at hf
  have hj : residueHom p j = (parameterJet n (-(p : ℚ) / 6) : ZMod p) := by
    change (j.val : ZMod p) = _
    rw [integralParameterJet_value]
  have hsi : residueHom p s = (1 / 6 : ZMod p) := by
    change ((1 / 6 : ℚ) : ZMod p) = _
    norm_num [Rat.cast_def]
  rw [hj, hsi] at hf
  exact (sub_eq_zero.mp hf).trans (mul_comm _ _)

end WPActualNativeFirstJet
