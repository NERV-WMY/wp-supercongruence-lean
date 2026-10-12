import WPActualNativeFirstJet
import Mathlib.Algebra.Polynomial.Div

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPNativeParameterTaylor WPActualNativeParameter
  WPActualNativeFirstJet

namespace WPActualNativeSecondJet

/-- Literal second finite quotient coefficient, with its integral Hasse-Taylor coefficient. -/
noncomputable def secondJetOver {R : Type*} [CommRing R]
    (A D : R[X]) (t u : R) : R :=
  (taylor t A).coeff 2 * u - A.derivative.eval t * D.derivative.eval t * u ^ 2 +
    A.eval t * (D.derivative.eval t) ^ 2 * u ^ 3 -
      A.eval t * (taylor t D).coeff 2 * u ^ 2

noncomputable def firstJetOver {R : Type*} [CommRing R]
    (A D : R[X]) (t u : R) : R :=
  A.derivative.eval t * u - A.eval t * D.derivative.eval t * u ^ 2

/-- Exact polynomial division; all three low Taylor coefficients are checked. -/
theorem quotient_taylor_divisible {R : Type*} [CommRing R]
    (A D : R[X]) (t u : R) (hu : D.eval t * u = 1) :
    ∃ E : R[X], taylor t D *
        (C (A.eval t * u) + C (firstJetOver A D t u) * X ^ 1 +
          C (secondJetOver A D t u) * X ^ 2) - taylor t A = X ^ 3 * E := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  interval_cases k
  · norm_num only [coeff_sub, mul_add, coeff_add, ← mul_assoc, coeff_mul_C,
      coeff_mul_X_pow', taylor_coeff_zero, taylor_coeff_one]
    simp only [if_false]
    linear_combination A.eval t * hu
  · norm_num only [coeff_sub, mul_add, coeff_add, ← mul_assoc, coeff_mul_C,
      coeff_mul_X_pow', taylor_coeff_zero, taylor_coeff_one]
    simp only [if_true, if_false]
    dsimp only [firstJetOver, secondJetOver]
    linear_combination (A.derivative.eval t - A.eval t * D.derivative.eval t * u) * hu
  · norm_num only [coeff_sub, mul_add, coeff_add, ← mul_assoc, coeff_mul_C,
      coeff_mul_X_pow', taylor_coeff_zero, taylor_coeff_one]
    simp only [if_true]
    dsimp only [firstJetOver, secondJetOver]
    linear_combination ((taylor t A).coeff 2 - A.derivative.eval t * D.derivative.eval t * u +
      A.eval t * (D.derivative.eval t) ^ 2 * u ^ 2 -
        A.eval t * (taylor t D).coeff 2 * u) * hu

noncomputable def quotientSecondJet (A D : ℚ[X]) (t : ℚ) : ℚ :=
  secondJetOver A D t (D.eval t)⁻¹

theorem firstJetOver_rational (A D : ℚ[X]) (t : ℚ) (hD : D.eval t ≠ 0) :
    firstJetOver A D t (D.eval t)⁻¹ = quotientJet A D t := by
  unfold firstJetOver quotientJet
  field_simp [hD]

theorem secondJetOver_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A D : R[X]) (t u : R) :
    f (secondJetOver A D t u) = secondJetOver (A.map f) (D.map f) (f t) (f u) := by
  have hc (P : R[X]) (n : ℕ) :
      f ((taylor t P).coeff n) = (taylor (f t) (P.map f)).coeff n := by
    rw [← coeff_map, map_taylor]
  unfold secondJetOver
  simp only [map_sub, map_add, map_mul, map_pow, hc,
    ← eval_map_apply, derivative_map]

/-- The exact second quotient remainder lies in the same integral coefficient ring. -/
theorem integral_quotient_second_remainder (p : ℕ) [Fact p.Prime]
    (A D : (integralRationals p)[X]) (t : integralRationals p)
    (hD0 : (D.eval 0).val ≠ 0) (hDt : (D.eval t).val ≠ 0)
    (hi0 : (D.eval 0).val⁻¹ ∈ integralRationals p)
    (hit : (D.eval t).val⁻¹ ∈ integralRationals p) :
    ∃ r : integralRationals p,
      (A.eval 0).val / (D.eval 0).val - (A.eval t).val / (D.eval t).val +
        t.val * quotientJet (A.map (integralRationals p).subtype)
          (D.map (integralRationals p).subtype) t.val -
        t.val ^ 2 * quotientSecondJet (A.map (integralRationals p).subtype)
          (D.map (integralRationals p).subtype) t.val = t.val ^ 3 * r.val := by
  let u : integralRationals p := ⟨(D.eval t).val⁻¹, hit⟩
  have hu : D.eval t * u = 1 := by
    apply Subtype.ext
    change (D.eval t).val * (D.eval t).val⁻¹ = 1
    exact mul_inv_cancel₀ hDt
  obtain ⟨E, hE⟩ := quotient_taylor_divisible A D t u hu
  let v : integralRationals p := ⟨(D.eval 0).val⁻¹, hi0⟩
  refine ⟨E.eval (-t) * v, ?_⟩
  have he := congrArg (fun P : (integralRationals p)[X] => (P.eval (-t)).val) hE
  simp only [eval_sub, eval_mul, eval_add, eval_C, eval_pow, eval_X,
    taylor_eval, neg_add_cancel] at he
  change (D.eval 0).val *
      ((A.eval t).val * u.val + (firstJetOver A D t u).val * (-t.val) ^ 1 +
        (secondJetOver A D t u).val * (-t.val) ^ 2) - (A.eval 0).val =
      (-t.val) ^ 3 * (E.eval (-t)).val at he
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
  change _ = t.val ^ 3 * ((E.eval (-t)).val * (D.eval 0).val⁻¹)
  field_simp [hD0, hDt] at he ⊢
  linear_combination -he

/-- The actual second coefficient of the original cleared native quotient at epsilon=-p/6. -/
noncomputable def parameterSecondJet (p n : ℕ) : ℚ :=
  quotientSecondJet (clearedNumerator ℚ n) (clearedDenominator ℚ n) (-(p : ℚ) / 6)

/-- The actual second coefficient, constructed inside the integral coefficient ring. -/
noncomputable def integralParameterSecondJet (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : integralRationals p :=
  let A := clearedNumerator (integralRationals p) n
  let D := clearedDenominator (integralRationals p) n
  let t := integralNode p hp
  let u : integralRationals p := ⟨(D.eval t).val⁻¹, (denominator_node_unit p n hp hn).2⟩
  secondJetOver A D t u

theorem integralParameterSecondJet_value (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (integralParameterSecondJet p n hp hn).val = parameterSecondJet p n := by
  unfold integralParameterSecondJet
  change (integralRationals p).subtype
    (secondJetOver (clearedNumerator (integralRationals p) n)
      (clearedDenominator (integralRationals p) n) (integralNode p hp)
      ⟨((clearedDenominator (integralRationals p) n).eval (integralNode p hp)).val⁻¹,
        (denominator_node_unit p n hp hn).2⟩) = _
  rw [secondJetOver_map, clearedNumerator_map, clearedDenominator_map]
  unfold parameterSecondJet quotientSecondJet
  change secondJetOver (clearedNumerator ℚ n) (clearedDenominator ℚ n)
      (integralNode p hp).val
      (((clearedDenominator (integralRationals p) n).eval (integralNode p hp)).val⁻¹) = _
  rw [evaluate_subtype, clearedDenominator_map, integralNode_value]

theorem actual_parameterSecondJet_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    0 ≤ padicValRat p (parameterSecondJet p n) := by
  rw [← integralParameterSecondJet_value p n hp hn]
  exact (integralParameterSecondJet p n hp hn).property

theorem parameterSecondJet_origin (p : ℕ) : parameterSecondJet p 0 = 0 := by
  simp [parameterSecondJet, quotientSecondJet, secondJetOver,
    clearedNumerator, clearedDenominator]

theorem actual_native_second_remainder (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ∃ r : integralRationals p,
      WPReview.nativeCoefficient n - parameterCoefficient n (-(p : ℚ) / 6) -
        (p : ℚ) / 6 * parameterJet n (-(p : ℚ) / 6) -
        (p : ℚ) ^ 2 / 36 * parameterSecondJet p n = (p : ℚ) ^ 3 / 216 * r.val := by
  have h0 := denominator_origin_unit p n hp hn
  have ht := denominator_node_unit p n hp hn
  obtain ⟨r, hr⟩ := integral_quotient_second_remainder p
    (clearedNumerator (integralRationals p) n) (clearedDenominator (integralRationals p) n)
    (integralNode p hp) h0.1 ht.1 h0.2 ht.2
  rw [evaluate_subtype, evaluate_subtype, evaluate_subtype, evaluate_subtype,
    clearedNumerator_map, clearedDenominator_map, Subring.coe_zero, integralNode_value] at hr
  refine ⟨-r, ?_⟩
  rw [← parameterCoefficient_origin n]
  dsimp only [parameterCoefficient, parameterJet, parameterSecondJet]
  simp only [Subring.coe_neg]
  linear_combination hr

end WPActualNativeSecondJet
