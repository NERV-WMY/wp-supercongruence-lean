import WPActualNativeSecondTaylor
import WPActualNativeJetODE

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeSecondJet WPActualNativeSecondTaylor
  WPActualNativeJetRecurrence WPActualNativeJetODE WPActualNativeHasse

namespace WPMomentPrecision.FullNativeTaylor

variable (p : ℕ) [Fact p.Prime]

theorem derivative_taylor_rational (t : ℚ) (P : ℚ[X]) :
    (taylor t P).derivative = taylor t P.derivative := by
  simp only [taylor_apply, derivative_comp, derivative_add,
    derivative_X, derivative_C, add_zero, one_mul]

/-- Hasse coefficient two is exactly half the ordinary second derivative. -/
theorem twice_taylor_coeff_two (A : ℚ[X]) (t : ℚ) :
    2 * (taylor t A).coeff 2 = A.derivative.derivative.eval t := by
  have h := congrArg (fun P : ℚ[X] => P.coeff 0)
    (derivative_taylor_rational t A.derivative)
  rw [← derivative_taylor_rational t A] at h
  rw [coeff_derivative, coeff_derivative, taylor_coeff_zero] at h
  norm_num at h
  simpa only [mul_comm] using h

/-- The literal ordinary second quotient derivative, with no selected second jet. -/
noncomputable def quotientFullSecondJet (A D : ℚ[X]) (t : ℚ) : ℚ :=
  A.derivative.derivative.eval t / D.eval t -
    2 * A.derivative.eval t * D.derivative.eval t / (D.eval t) ^ 2 -
    A.eval t * D.derivative.derivative.eval t / (D.eval t) ^ 2 +
    2 * A.eval t * (D.derivative.eval t) ^ 2 / (D.eval t) ^ 3

theorem quotientFullSecondJet_eq_twice (A D : ℚ[X]) (t : ℚ) :
    quotientFullSecondJet A D t = 2 * quotientSecondJet A D t := by
  unfold quotientFullSecondJet quotientSecondJet secondJetOver
  rw [← twice_taylor_coeff_two A t, ← twice_taylor_coeff_two D t]
  simp only [div_eq_mul_inv, inv_pow]
  ring

noncomputable def nativeFullSecondJetCoefficient (n : ℕ) : ℚ :=
  quotientFullSecondJet (clearedNumerator ℚ n) (clearedDenominator ℚ n) (-(p : ℚ) / 6)

omit [Fact p.Prime] in
/-- Explicit transport from the checked Hasse jet to the full K of IR20--IR28. -/
theorem nativeFullSecondJetCoefficient_eq_twice (n : ℕ) :
    nativeFullSecondJetCoefficient p n = 2 * parameterSecondJet p n :=
  quotientFullSecondJet_eq_twice _ _ _

theorem nativeFullSecondJetCoefficient_integral (hp : 7 ≤ p) (n : ℕ) (hn : n < p) :
    nativeFullSecondJetCoefficient p n ∈ integralRationals p := by
  rw [nativeFullSecondJetCoefficient_eq_twice]
  exact (integralRationals p).mul_mem (natCast_mem _ 2)
    (actual_parameterSecondJet_integral p n hp hn)

noncomputable def fullSecondJetAt (e : ℕ) : ℚ[X] :=
  coefficientPolynomial e (nativeFullSecondJetCoefficient p)

omit [Fact p.Prime] in
theorem fullSecondJetAt_eq_twice (e : ℕ) :
    fullSecondJetAt p e = C (2 : ℚ) * nativeSecondJetAt p e := by
  ext n
  rw [fullSecondJetAt, nativeSecondJetAt, coeff_C_mul,
    coefficientPolynomial_coeff, coefficientPolynomial_coeff]
  split_ifs
  · exact nativeFullSecondJetCoefficient_eq_twice p n
  · ring

noncomputable def cubicErrorPolynomial (e : ℕ) : ℚ[X] :=
  coefficientPolynomial e (nativeCubicError p)

/-- A finite integral coefficient model with the actual original coefficients. -/
noncomputable def coefficientIntegralPolynomial (e : ℕ) (a : ℕ → ℚ)
    (ha : ∀ n < e + 1, a n ∈ integralRationals p) : (integralRationals p)[X] :=
  ∑ n : Fin (e + 1), monomial n.val ⟨a n.val, ha n.val n.isLt⟩

theorem coefficientIntegralPolynomial_value (e : ℕ) (a : ℕ → ℚ)
    (ha : ∀ n < e + 1, a n ∈ integralRationals p) :
    (coefficientIntegralPolynomial p e a ha).map (integralRationals p).subtype =
      coefficientPolynomial e a := by
  simp only [coefficientIntegralPolynomial, Polynomial.map_sum, map_monomial,
    Subring.coe_subtype]
  unfold coefficientPolynomial
  exact Fin.sum_univ_eq_sum_range (fun n => monomial n (a n)) (e + 1)

noncomputable def integralCubicErrorPolynomial (e : ℕ) (hp : 7 ≤ p) (he : e < p) :
    (integralRationals p)[X] :=
  coefficientIntegralPolynomial p e (nativeCubicError p)
    (fun n hn => actual_nativeCubicError_integral p n hp (by omega))

theorem integralCubicErrorPolynomial_value (e : ℕ) (hp : 7 ≤ p) (he : e < p) :
    (integralCubicErrorPolynomial p e hp he).map (integralRationals p).subtype =
      cubicErrorPolynomial p e :=
  coefficientIntegralPolynomial_value p e _ _

theorem cubicErrorPolynomial_integral (e : ℕ) (hp : 7 ≤ p) (he : e < p) (n : ℕ) :
    (cubicErrorPolynomial p e).coeff n ∈ integralRationals p := by
  rw [← integralCubicErrorPolynomial_value p e hp he, coeff_map]
  exact ((integralCubicErrorPolynomial p e hp he).coeff n).property

/-- Every coefficient of the first jet above N vanishes after reduction;
the whole second jet is still retained through e. -/
theorem actual_firstJet_field_tail (hp : 19 ≤ p) (n : ℕ)
    (hn : n < p) (hN : (p - 1) / 2 < n) :
    (parameterJet n (-(p : ℚ) / 6) : ZMod p) = 0 := by
  have hh := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hd := Nat.div_mul_le_self p 6
  revert hn hN
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hN
    cases n with
    | zero => omega
    | succ n =>
      have hr := actual_native_jet_field_recurrence p n (by omega) hn
      rw [actual_native_coefficient_field_tail p (n + 1) (by omega) hn (by omega),
        actual_native_coefficient_field_tail p n (by omega) (by omega) (by omega)] at hr
      have hz : ((2 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 1) *
          (6 * (n : ZMod p) + 5)) *
          (parameterJet n (-(p : ℚ) / 6) : ZMod p) = 0 := by
        by_cases he : n = (p - 1) / 2
        · subst n
          rw [WPActualHasseReciprocal.actual_half_field p (by omega)]
          ring
        · rw [ih n (by omega) (by omega) (by omega), mul_zero]
      rw [hz] at hr
      simp only [mul_zero, neg_zero, zero_add, sub_zero] at hr
      have h72 : (72 : ZMod p) ≠ 0 := by
        have hu := denominator_origin_residue_ne_zero p 1 (by omega) (by omega)
        simpa only [denominator_eval_zero, pow_one, Nat.factorial_one,
          Nat.cast_one, one_pow, mul_one] using hu
      have hnext : (n : ZMod p) + 1 ≠ 0 := by
        rw [show (n : ZMod p) + 1 = ((n + 1 : ℕ) : ZMod p) by simp]
        intro he
        have := Nat.le_of_dvd (by omega : 0 < n + 1)
          ((ZMod.natCast_eq_zero_iff (n + 1) p).mp he)
        omega
      exact (mul_eq_zero.mp hr).resolve_left (mul_ne_zero h72 (pow_ne_zero 3 hnext))

noncomputable def integralFirstJetAt (e : ℕ) (hp : 7 ≤ p) (he : e < p) :
    (integralRationals p)[X] :=
  coefficientIntegralPolynomial p e (fun n => parameterJet n (-(p : ℚ) / 6))
    (fun n hn => actual_parameterJet_integral p n hp (by omega))

theorem integralFirstJetAt_value (e : ℕ) (hp : 7 ≤ p) (he : e < p) :
    (integralFirstJetAt p e hp he).map (integralRationals p).subtype =
      nativeFirstJetAt p e :=
  coefficientIntegralPolynomial_value p e _ _

theorem integralFirstJetAt_field (e : ℕ) (hp : 19 ≤ p)
    (he : e < p) (hN : (p - 1) / 2 ≤ e) :
    (integralFirstJetAt p e (by omega) he).map (residueHom p) = nativeJetField p := by
  ext n
  rw [Polynomial.coeff_map]
  have hv := congrArg (fun P : ℚ[X] => P.coeff n)
    (integralFirstJetAt_value p e (by omega) he)
  rw [Polynomial.coeff_map] at hv
  change ((integralFirstJetAt p e (by omega) he).coeff n).val =
    (nativeFirstJetAt p e).coeff n at hv
  change (((integralFirstJetAt p e (by omega) he).coeff n).val : ZMod p) = _
  rw [hv, nativeFirstJetAt, coefficientPolynomial_coeff, nativeJetField_coeff]
  by_cases hn : n < (p - 1) / 2 + 1
  · rw [if_pos hn, if_pos (by omega)]
  · rw [if_neg hn]
    split_ifs with he'
    · exact actual_firstJet_field_tail p hp n (by omega) (by omega)
    · simp only [Rat.cast_zero]

noncomputable def integralFullSecondJetAt (e : ℕ) (hp : 7 ≤ p) (he : e < p) :
    (integralRationals p)[X] :=
  coefficientIntegralPolynomial p e (nativeFullSecondJetCoefficient p)
    (fun n hn => nativeFullSecondJetCoefficient_integral p hp n (by omega))

theorem integralFullSecondJetAt_value (e : ℕ) (hp : 7 ≤ p) (he : e < p) :
    (integralFullSecondJetAt p e hp he).map (integralRationals p).subtype =
      fullSecondJetAt p e :=
  coefficientIntegralPolynomial_value p e _ _

/-- Coefficientwise integral lifting uses the original finite support. -/
noncomputable def integralPolynomialModel (P : ℚ[X])
    (hP : ∀ n, P.coeff n ∈ integralRationals p) : (integralRationals p)[X] :=
  ∑ n ∈ P.support, monomial n ⟨P.coeff n, hP n⟩

theorem integralPolynomialModel_value (P : ℚ[X])
    (hP : ∀ n, P.coeff n ∈ integralRationals p) :
    (integralPolynomialModel p P hP).map (integralRationals p).subtype = P := by
  simp only [integralPolynomialModel, Polynomial.map_sum, Polynomial.map_monomial,
    Subring.coe_subtype]
  exact Polynomial.sum_monomial_eq P

/-- Full coefficient Taylor expansion through the actual upper cutoff, before any projection. -/
theorem actual_full_polynomial_Taylor (e : ℕ) :
    WPReview.nativePolynomial (e + 1) = nativeTermAt p e +
      C ((p : ℚ) / 6) * nativeFirstJetAt p e +
      C ((p : ℚ) ^ 2 / 72) * fullSecondJetAt p e +
      C ((p : ℚ) ^ 3) * cubicErrorPolynomial p e := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  change coefficientPolynomial e WPReview.nativeCoefficient = _
  ext n
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, nativeTermAt,
    nativeFirstJetAt, fullSecondJetAt, cubicErrorPolynomial, coefficientPolynomial_coeff]
  split_ifs with hn
  · rw [nativeFullSecondJetCoefficient_eq_twice]
    unfold nativeCubicError
    field_simp [hpq]
    ring
  · ring

theorem actual_nativeTermAt_eq (e : ℕ) (hp : 7 ≤ p) (he : p / 6 ≤ e) :
    nativeTermAt p e = WPActualNativeChiTaylor.nativeTermPolynomial p := by
  ext n
  rw [nativeTermAt, coefficientPolynomial_coeff,
    WPActualNativeChiTaylor.nativeTermPolynomial_coeff]
  by_cases hn : n ≤ p / 6
  · have hN : p / 6 ≤ (p - 1) / 2 := by
      have hh := WPActualHasseReciprocal.actual_half_exponent p hp
      have hd := Nat.div_mul_le_self p 6
      omega
    rw [if_pos (by omega), if_pos (by omega)]
  · have hz : parameterCoefficient n (-(p : ℚ) / 6) = 0 := by
      rw [parameterCoefficient, terminating_numerator_zero p n hp (by omega), zero_div]
    simp only [hz, ite_self]

theorem actual_full_Taylor_integral_remainder (hp : 19 ≤ p) :
    ∃ E : (integralRationals p)[X],
      WPReview.nativePolynomial (p - p / 6) =
        WPActualNativeChiTaylor.nativeTermPolynomial p +
        C ((p : ℚ) / 6) * nativeFirstJetAt p (p - 1 - p / 6) +
        C ((p : ℚ) ^ 2 / 72) * fullSecondJetAt p (p - 1 - p / 6) +
        C ((p : ℚ) ^ 3) * E.map (integralRationals p).subtype := by
  refine ⟨integralCubicErrorPolynomial p (p - 1 - p / 6) (by omega) (by omega), ?_⟩
  rw [integralCubicErrorPolynomial_value]
  have hd := Nat.div_mul_le_self p 6
  have hcut : p - 1 - p / 6 + 1 = p - p / 6 := by omega
  have h := actual_full_polynomial_Taylor p (p - 1 - p / 6)
  rw [hcut, actual_nativeTermAt_eq p _ (by omega) (by omega)] at h
  exact h

end WPMomentPrecision.FullNativeTaylor
