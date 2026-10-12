import WPMomentPrecision.SecondLift.TwoNodeSquare
import WPMomentPrecision.SecondLift.FullNativeTaylor

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPNativeParameterTaylor WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeSecondJet WPActualNativeSecondTaylor
  WPActualNativeJetRecurrence WPActualRankTwoParameter WPMomentPrecision.FullNativeTaylor
  WPMomentPrecision.TwoNodeSquare

namespace WPMomentPrecision.TwoNodeTaylor

set_option maxHeartbeats 1200000

/-- Taylor between two integral points, with the actual quotient and an integral cubic error. -/
theorem integral_quotient_shifted_second_remainder (p : ℕ) [Fact p.Prime]
    (A D : (integralRationals p)[X]) (t s : integralRationals p)
    (hDs : (D.eval s).val ≠ 0) (hDt : (D.eval t).val ≠ 0)
    (his : (D.eval s).val⁻¹ ∈ integralRationals p)
    (hit : (D.eval t).val⁻¹ ∈ integralRationals p) :
    ∃ r : integralRationals p,
      (A.eval s).val / (D.eval s).val - (A.eval t).val / (D.eval t).val -
        (s.val - t.val) * quotientJet (A.map (integralRationals p).subtype)
          (D.map (integralRationals p).subtype) t.val -
        (s.val - t.val) ^ 2 * quotientSecondJet (A.map (integralRationals p).subtype)
          (D.map (integralRationals p).subtype) t.val =
        (s.val - t.val) ^ 3 * r.val := by
  let u : integralRationals p := ⟨(D.eval t).val⁻¹, hit⟩
  have hu : D.eval t * u = 1 := by
    apply Subtype.ext
    change (D.eval t).val * (D.eval t).val⁻¹ = 1
    exact mul_inv_cancel₀ hDt
  obtain ⟨E, hE⟩ := quotient_taylor_divisible A D t u hu
  let v : integralRationals p := ⟨(D.eval s).val⁻¹, his⟩
  refine ⟨-E.eval (s - t) * v, ?_⟩
  have he := congrArg (fun P : (integralRationals p)[X] =>
    (P.eval (s - t)).val) hE
  simp only [eval_sub, eval_mul, eval_add, eval_C, eval_pow, eval_X,
    taylor_eval, sub_add_cancel] at he
  change (D.eval s).val *
      ((A.eval t).val * u.val + (firstJetOver A D t u).val * (s.val - t.val) ^ 1 +
        (secondJetOver A D t u).val * (s.val - t.val) ^ 2) - (A.eval s).val =
      (s.val - t.val) ^ 3 * (E.eval (s - t)).val at he
  have hj : (firstJetOver A D t u).val =
      quotientJet (A.map (integralRationals p).subtype)
        (D.map (integralRationals p).subtype) t.val := by
    change (A.derivative.eval t).val * (D.eval t).val⁻¹ -
      (A.eval t).val * (D.derivative.eval t).val * ((D.eval t).val⁻¹) ^ 2 = _
    simp only [evaluate_subtype]
    rw [evaluate_subtype] at hDt
    simpa only [firstJetOver, derivative_map] using
      firstJetOver_rational (A.map (integralRationals p).subtype)
        (D.map (integralRationals p).subtype) t.val hDt
  have hs : (secondJetOver A D t u).val =
      quotientSecondJet (A.map (integralRationals p).subtype)
        (D.map (integralRationals p).subtype) t.val := by
    change (integralRationals p).subtype (secondJetOver A D t u) = _
    rw [secondJetOver_map]
    unfold quotientSecondJet
    change secondJetOver (A.map (integralRationals p).subtype)
        (D.map (integralRationals p).subtype) t.val (D.eval t).val⁻¹ =
      secondJetOver (A.map (integralRationals p).subtype)
        (D.map (integralRationals p).subtype) t.val
        ((D.map (integralRationals p).subtype).eval t.val)⁻¹
    rw [evaluate_subtype]
  rw [hj, hs] at he
  dsimp only [u] at he
  change _ = (s.val - t.val) ^ 3 *
    (-(E.eval (s - t)).val * (D.eval s).val⁻¹)
  field_simp [hDs, hDt] at he ⊢
  linear_combination -he

/-- The cubic error is divided over Q at the two literal native terminating parameters. -/
noncomputable def nativeNodeShiftError (p n : ℕ) : ℚ :=
  (parameterCoefficient n (-5 * (p : ℚ) / 6) -
    parameterCoefficient n (-(p : ℚ) / 6) +
    (2 * (p : ℚ) / 3) * parameterJet n (-(p : ℚ) / 6) -
    (2 * (p : ℚ) ^ 2 / 9) * nativeFullSecondJetCoefficient p n) / (p : ℚ) ^ 3

theorem nativeNodeShiftError_integral (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) : nativeNodeShiftError p n ∈ integralRationals p := by
  have ht := native_denominator_node_unit p n 1 (by omega) hn
  have hs := native_denominator_node_unit p n 5 (by omega) hn
  obtain ⟨r, hr⟩ := integral_quotient_shifted_second_remainder p
    (clearedNumerator (integralRationals p) n)
    (clearedDenominator (integralRationals p) n)
    (rankNode p (by omega) 1) (rankNode p (by omega) 5) hs.1 ht.1 hs.2 ht.2
  simp only [evaluate_subtype, clearedNumerator_map, clearedDenominator_map,
    rankNode_value, Nat.cast_one, neg_one_mul, Nat.cast_ofNat] at hr
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : nativeNodeShiftError p n = r.val * (-4 * (1 / 6 : ℚ)) ^ 3 := by
    rw [nativeNodeShiftError, nativeFullSecondJetCoefficient_eq_twice]
    have hnum : parameterCoefficient n (-5 * (p : ℚ) / 6) -
        parameterCoefficient n (-(p : ℚ) / 6) +
        (2 * (p : ℚ) / 3) * parameterJet n (-(p : ℚ) / 6) -
        (2 * (p : ℚ) ^ 2 / 9) * (2 * parameterSecondJet p n) =
        (p : ℚ) ^ 3 * (r.val * (-4 * (1 / 6 : ℚ)) ^ 3) := by
      dsimp only [parameterCoefficient, parameterJet, parameterSecondJet]
      linear_combination hr
    rw [hnum, mul_div_cancel_left₀ _ (pow_ne_zero 3 hpq)]
  rw [he]
  exact (integralRationals p).mul_mem r.property
    ((integralRationals p).pow_mem
      ((integralRationals p).mul_mem (intCast_mem _ (-4))
        (WPActualRankTwoLowTaylor.integralSixth p (by omega)).property) 3)

noncomputable def integralNodeShiftErrorPolynomial (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  coefficientIntegralPolynomial p (p - 1 - p / 6) (nativeNodeShiftError p)
    (fun n hn => nativeNodeShiftError_integral p n hp (by omega))

/-- The full e cutoff is expanded between the two actual nodes before casting. -/
theorem actual_native_two_node_Taylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeNodePolynomial p 5 = nativeNodePolynomial p 1 -
      C (2 * (p : ℚ) / 3) * nativeFirstJetAt p (p - 1 - p / 6) +
      C (2 * (p : ℚ) ^ 2 / 9) * fullSecondJetAt p (p - 1 - p / 6) +
      C ((p : ℚ) ^ 3) *
        (integralNodeShiftErrorPolynomial p hp).map (integralRationals p).subtype := by
  rw [integralNodeShiftErrorPolynomial, coefficientIntegralPolynomial_value]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  ext n
  simp only [nativeNodePolynomial, nativeFirstJetAt, fullSecondJetAt,
    coeff_add, coeff_sub, coeff_C_mul, coefficientPolynomial_coeff,
    Nat.cast_one, neg_one_mul, Nat.cast_ofNat]
  split_ifs
  · unfold nativeNodeShiftError
    field_simp [hpq]
    ring
  · ring

/-- Actual node squares force the whole quadratic second normalization. -/
theorem actual_two_Jacobi_node_Taylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rankJacobiNode p 5 ^ 2 = rankJacobiNode p 1 ^ 2 -
      C (2 * (p : ℚ) / 3) *
        (nativeFirstJetAt p (p - 1 - p / 6)).comp (1 - X ^ 2) +
      C (2 * (p : ℚ) ^ 2 / 9) *
        (fullSecondJetAt p (p - 1 - p / 6)).comp (1 - X ^ 2) +
      C ((p : ℚ) ^ 3) *
        ((integralNodeShiftErrorPolynomial p hp).comp (1 - X ^ 2)).map
          (integralRationals p).subtype := by
  have h := congrArg (fun P : ℚ[X] => P.comp (1 - X ^ 2))
    (actual_native_two_node_Taylor p hp)
  simp only [add_comp, sub_comp, mul_comp, C_comp] at h
  rw [actual_two_node_Jacobi_square p 5 hp (Or.inr rfl),
    actual_two_node_Jacobi_square p 1 hp (Or.inl rfl)] at h
  rw [Polynomial.map_comp]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  exact h

end WPMomentPrecision.TwoNodeTaylor
