import WPActualNativeSecondJet
import WPActualNativeChiTaylor

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPPIntegralReduction WPFiniteLaurentIntegral
  WPActualNativeParameter WPActualNativeFirstJet WPActualNativeSecondJet
  WPActualNativeChiTaylor WPActualChiSource WPActualPullbackSource WPActualEtaPole
  WPActualEtaIntegrality WPActualEtaFieldCutoff WPLaurentIntegralResidue

namespace WPActualNativeSecondTaylor

/-- Exact cubic coefficient error, retaining the original finite quotient. -/
noncomputable def nativeCubicError (p n : ℕ) : ℚ :=
  (WPReview.nativeCoefficient n - parameterCoefficient n (-(p : ℚ) / 6) -
    (p : ℚ) / 6 * parameterJet n (-(p : ℚ) / 6) -
    (p : ℚ) ^ 2 / 36 * parameterSecondJet p n) / (p : ℚ) ^ 3

theorem actual_nativeCubicError_remainder (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ∃ r : integralRationals p, nativeCubicError p n = r.val / 216 := by
  obtain ⟨r, hr⟩ := actual_native_second_remainder p n hp hn
  have hpq : (p : ℚ) ≠ 0 := by positivity
  refine ⟨r, ?_⟩
  unfold nativeCubicError
  rw [hr]
  field_simp

theorem actual_nativeCubicError_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    0 ≤ padicValRat p (nativeCubicError p n) := by
  obtain ⟨r, hr⟩ := actual_nativeCubicError_remainder p n hp hn
  have hs : (1 / 6 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)
  have hi := (integralRationals p).mul_mem r.property ((integralRationals p).pow_mem hs 3)
  have he : nativeCubicError p n = r.val * (1 / 6 : ℚ) ^ 3 := by
    rw [hr]
    ring
  rw [he]
  exact hi

noncomputable def coefficientPolynomial (e : ℕ) (a : ℕ → ℚ) : ℚ[X] :=
  ∑ n ∈ Finset.range (e + 1), Polynomial.monomial n (a n)

theorem coefficientPolynomial_coeff (e n : ℕ) (a : ℕ → ℚ) :
    (coefficientPolynomial e a).coeff n = if n < e + 1 then a n else 0 := by
  classical
  simp only [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n < e + 1
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m _ hmn; simp [hmn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by have := Finset.mem_range.mp hm; omega
    simp [hmn]

theorem coefficientPolynomial_origin (e : ℕ) (a : ℕ → ℚ) :
    (coefficientPolynomial e a).eval 0 = a 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coefficientPolynomial_coeff, if_pos (by omega)]

theorem coefficientPolynomial_degree (e : ℕ) (a : ℕ → ℚ) :
    (coefficientPolynomial e a).natDegree ≤ e := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coefficientPolynomial_coeff, if_neg (by omega)]

/-- Both jets retain every index through the given actual upper cutoff. -/
noncomputable def nativeFirstJetAt (p e : ℕ) : ℚ[X] :=
  coefficientPolynomial e (fun n => parameterJet n (-(p : ℚ) / 6))

noncomputable def nativeSecondJetAt (p e : ℕ) : ℚ[X] :=
  coefficientPolynomial e (parameterSecondJet p)

noncomputable def nativeTermAt (p e : ℕ) : ℚ[X] :=
  coefficientPolynomial e (fun n => parameterCoefficient n (-(p : ℚ) / 6))

theorem nativeTermAt_degree (p e : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (nativeTermAt p e).natDegree ≤ p / 6 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [nativeTermAt, coefficientPolynomial_coeff]
  split_ifs
  · rw [parameterCoefficient, terminating_numerator_zero p n hp hn, zero_div]
  · rfl

theorem nativeTermAt_origin (p e : ℕ) : (nativeTermAt p e).eval 0 = 1 := by
  rw [nativeTermAt, coefficientPolynomial_origin]
  simp [parameterCoefficient, clearedNumerator, clearedDenominator]

theorem nativeSecondJetAt_origin (p e : ℕ) : (nativeSecondJetAt p e).eval 0 = 0 := by
  rw [nativeSecondJetAt, coefficientPolynomial_origin, parameterSecondJet_origin]

noncomputable def finiteDifferenceAt (p e : ℕ) (a : ℕ → ℚ) : ℚ[T;T⁻¹] :=
  substitute (coefficientPolynomial e a) Vx -
    T (((p - 1) / 2 : ℕ) : ℤ) * substitute (coefficientPolynomial e a) Qx

noncomputable def deltaTermAt (p e : ℕ) : ℚ[T;T⁻¹] :=
  C (1 / (p : ℚ)) * finiteDifferenceAt p e
    (fun n => parameterCoefficient n (-(p : ℚ) / 6))

noncomputable def firstJetDifferenceAt (p e : ℕ) : ℚ[T;T⁻¹] :=
  finiteDifferenceAt p e (fun n => parameterJet n (-(p : ℚ) / 6))

noncomputable def secondJetDifferenceAt (p e : ℕ) : ℚ[T;T⁻¹] :=
  finiteDifferenceAt p e (parameterSecondJet p)

noncomputable def cubicErrorDifferenceAt (p e : ℕ) : ℚ[T;T⁻¹] :=
  finiteDifferenceAt p e (nativeCubicError p)

theorem finiteDifferenceAt_expansion (p e : ℕ) (a : ℕ → ℚ) :
    finiteDifferenceAt p e a = ∑ n ∈ Finset.range (e + 1),
      C (a n) * (Vx ^ n - T (((p - 1) / 2 : ℕ) : ℤ) * Qx ^ n) := by
  simp only [finiteDifferenceAt, coefficientPolynomial, substitute, map_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change Polynomial.eval₂ C Vx (Polynomial.monomial n (a n)) -
    T (((p - 1) / 2 : ℕ) : ℤ) * Polynomial.eval₂ C Qx (Polynomial.monomial n (a n)) = _
  rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
  ring

/-- Exact full chi expansion, with the integral cubic error still present. -/
theorem actual_native_secondTaylor_identity (p e : ℕ) [Fact p.Prime] :
    chiX p ((p - 1) / 2) e - deltaTermAt p e -
      C (1 / 6) * firstJetDifferenceAt p e -
      C ((p : ℚ) / 36) * secondJetDifferenceAt p e =
        C ((p : ℚ) ^ 2) * cubicErrorDifferenceAt p e := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [WPActualEtaFieldCutoff.actual_chi_expansion]
  unfold deltaTermAt firstJetDifferenceAt secondJetDifferenceAt cubicErrorDifferenceAt
  rw [finiteDifferenceAt_expansion, finiteDifferenceAt_expansion,
    finiteDifferenceAt_expansion, finiteDifferenceAt_expansion,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul,
    ← sub_mul, ← sub_mul, ← sub_mul, ← map_sub, ← map_sub, ← map_sub]
  congr 1
  unfold nativeCubicError
  field_simp

theorem integral_finiteDifferenceAt (p e : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (a : ℕ → ℚ) (ha : ∀ n < e + 1, 0 ≤ padicValRat p (a n)) :
    finiteDifferenceAt p e a ∈ integralLaurent p := by
  rw [finiteDifferenceAt_expansion]
  apply (integralLaurent p).sum_mem
  intro n hn
  exact (integralLaurent p).mul_mem (integral_C p _ (ha n (Finset.mem_range.mp hn)))
    ((integralLaurent p).sub_mem ((integralLaurent p).pow_mem (integral_Vx p hp) n)
      ((integralLaurent p).mul_mem (integral_T p _)
        ((integralLaurent p).pow_mem (integral_Qx p hp) n)))

theorem actual_secondJetDifferenceAt_integral (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) : secondJetDifferenceAt p e ∈ integralLaurent p := by
  apply integral_finiteDifferenceAt p e hp
  intro n hn
  exact actual_parameterSecondJet_integral p n hp (by omega)

theorem actual_cubicErrorDifferenceAt_integral (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) : cubicErrorDifferenceAt p e ∈ integralLaurent p := by
  apply integral_finiteDifferenceAt p e hp
  intro n hn
  exact actual_nativeCubicError_integral p n hp (by omega)

/-- The complete original upper cutoff has a coefficientwise integral p^2 error. -/
theorem actual_full_cutoff_secondTaylor_identity (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    ∃ E ∈ integralLaurent p,
      chiX p ((p - 1) / 2) (p - 1 - p / 6) -
        deltaTermAt p (p - 1 - p / 6) -
        C (1 / 6) * firstJetDifferenceAt p (p - 1 - p / 6) -
        C ((p : ℚ) / 36) * secondJetDifferenceAt p (p - 1 - p / 6) =
          C ((p : ℚ) ^ 2) * E := by
  exact ⟨cubicErrorDifferenceAt p (p - 1 - p / 6),
    actual_cubicErrorDifferenceAt_integral p _ (by omega) (by omega),
    actual_native_secondTaylor_identity p _⟩

end WPActualNativeSecondTaylor
