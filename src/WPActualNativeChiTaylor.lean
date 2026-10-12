import WPActualNativeJetRecurrence

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualEtaPole WPActualEtaIntegrality WPActualEtaFieldCutoff
  WPActualChiSource WPLaurentIntegralResidue WPPIntegralReduction
  WPActualNativeHasse WPActualNativeParameter WPActualNativeFirstJet
  WPActualCentralNativeJet WPActualNativeJetRecurrence

namespace WPActualNativeChiTaylor

noncomputable def nativeTaylorError (p n : ℕ) : ℚ :=
  (WPReview.nativeCoefficient n - parameterCoefficient n (-(p : ℚ) / 6)) / p -
    parameterJet n (-(p : ℚ) / 6) / 6

theorem actual_nativeTaylorError_remainder (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ∃ r : integralRationals p, nativeTaylorError p n = (p : ℚ) * (r.val / 36) := by
  obtain ⟨r, hr⟩ := actual_native_first_remainder p n hp hn
  have hpq : (p : ℚ) ≠ 0 := by positivity
  refine ⟨r, ?_⟩
  unfold nativeTaylorError
  calc
    _ = (WPReview.nativeCoefficient n - parameterCoefficient n (-(p : ℚ) / 6) -
        (p : ℚ) / 6 * parameterJet n (-(p : ℚ) / 6)) / p := by field_simp
    _ = ((p : ℚ) ^ 2 / 36 * r.val) / p := by rw [hr]
    _ = _ := by field_simp

theorem actual_nativeTaylorError_kernel (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : residueZero p (C (nativeTaylorError p n)) := by
  obtain ⟨r, hr⟩ := actual_nativeTaylorError_remainder p n hp hn
  let R := integralRationals p
  let s : R := ⟨1 / 6,
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)⟩
  let z : R := (p : R) * (r * s ^ 2)
  have hz : z.val = nativeTaylorError p n := by
    change (p : ℚ) * (r.val * (1 / 6 : ℚ) ^ 2) = _
    rw [hr]
    ring
  have hfield : residueHom p z = 0 := by
    simp only [z, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  apply residueZero_C p _
  · rw [← hz]
    exact z.property
  · rw [← hz]
    exact hfield

/-- The original terminating polynomial, retaining the complete n<=N indexing. -/
noncomputable def nativeTermPolynomial (p : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range ((p - 1) / 2 + 1),
    Polynomial.monomial n (parameterCoefficient n (-(p : ℚ) / 6))

theorem nativeTermPolynomial_coeff (p n : ℕ) : (nativeTermPolynomial p).coeff n =
    if n < (p - 1) / 2 + 1 then parameterCoefficient n (-(p : ℚ) / 6) else 0 := by
  classical
  simp only [nativeTermPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n < (p - 1) / 2 + 1
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m _ hmn; simp [hmn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by have := Finset.mem_range.mp hm; omega
    simp [hmn]

theorem nativeTermPolynomial_origin (p : ℕ) : (nativeTermPolynomial p).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, nativeTermPolynomial_coeff, if_pos (by omega)]
  simp [parameterCoefficient, clearedNumerator, clearedDenominator]

theorem nativeTermPolynomial_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (nativeTermPolynomial p).natDegree ≤ p / 6 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [nativeTermPolynomial_coeff]
  split_ifs
  · rw [parameterCoefficient, terminating_numerator_zero p n hp hn, zero_div]
  · rfl

noncomputable def termDifference (p : ℕ) : ℚ[T;T⁻¹] :=
  substitute (nativeTermPolynomial p) Vx -
    T (((p - 1) / 2 : ℕ) : ℤ) * substitute (nativeTermPolynomial p) Qx

noncomputable def jetDifference (p : ℕ) : ℚ[T;T⁻¹] :=
  substitute (nativeJetPolynomial p) Vx - nativeJetPullback p

noncomputable def deltaTerm (p : ℕ) : ℚ[T;T⁻¹] := C (1 / (p : ℚ)) * termDifference p

noncomputable def errorDifference (p : ℕ) : ℚ[T;T⁻¹] :=
  ∑ n ∈ Finset.range ((p - 1) / 2 + 1), C (nativeTaylorError p n) *
    (Vx ^ n - T (((p - 1) / 2 : ℕ) : ℤ) * Qx ^ n)

theorem finite_difference_expansion (N : ℕ) (a : ℕ → ℚ) :
    substitute (∑ n ∈ Finset.range (N + 1), Polynomial.monomial n (a n)) Vx -
      T (N : ℤ) * substitute (∑ n ∈ Finset.range (N + 1), Polynomial.monomial n (a n)) Qx =
    ∑ n ∈ Finset.range (N + 1), C (a n) * (Vx ^ n - T (N : ℤ) * Qx ^ n) := by
  simp only [substitute, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change Polynomial.eval₂ C Vx (Polynomial.monomial n (a n)) -
    T (N : ℤ) * Polynomial.eval₂ C Qx (Polynomial.monomial n (a n)) = _
  rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
  ring

theorem actual_chi_nativeTaylor_identity (p : ℕ) :
    chiX p ((p - 1) / 2) ((p - 1) / 2) - deltaTerm p -
      C (1 / 6) * jetDifference p = errorDifference p := by
  rw [actual_chi_expansion]
  unfold deltaTerm termDifference jetDifference nativeJetPullback
    nativeTermPolynomial nativeJetPolynomial errorDifference
  rw [finite_difference_expansion, finite_difference_expansion,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← sub_mul, ← sub_mul,
    ← map_sub, ← map_sub]
  congr 1
  unfold nativeTaylorError
  ring

theorem actual_errorDifference_kernel (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueZero p (errorDifference p) := by
  rw [errorDifference]
  apply residueZero_sum
  intro n hn
  have hr := Finset.mem_range.mp hn
  exact residueZero_mul_integral p (actual_nativeTaylorError_kernel p n hp (by omega))
    ((integralLaurent p).sub_mem ((integralLaurent p).pow_mem (integral_Vx p hp) n)
      ((integralLaurent p).mul_mem (integral_T p _)
        ((integralLaurent p).pow_mem (integral_Qx p hp) n)))

theorem actual_jetDifference_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    jetDifference p ∈ integralLaurent p := by
  unfold jetDifference nativeJetPullback nativeJetPolynomial
  rw [finite_difference_expansion]
  apply (integralLaurent p).sum_mem
  intro n hn
  have hr := Finset.mem_range.mp hn
  exact (integralLaurent p).mul_mem
    (integral_C p _ (actual_parameterJet_integral p n hp (by omega)))
    ((integralLaurent p).sub_mem ((integralLaurent p).pow_mem (integral_Vx p hp) n)
      ((integralLaurent p).mul_mem (integral_T p _)
        ((integralLaurent p).pow_mem (integral_Qx p hp) n)))

theorem actual_deltaTerm_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    deltaTerm p ∈ integralLaurent p := by
  have hs : C (1 / 6 : ℚ) * jetDifference p ∈ integralLaurent p :=
    (integralLaurent p).mul_mem
      (integral_C p _ (WPFiniteConductorPolynomial.small_inverse_integral p 6
        (by norm_num) (by omega))) (actual_jetDifference_integral p hp)
  have hc : chiX p ((p - 1) / 2) ((p - 1) / 2) ∈ integralLaurent p :=
    actual_chiX_integral p _ hp (by omega) (by omega)
  have he := ((residueZero_iff p _).mp (actual_errorDifference_kernel p hp)).1
  have heq : deltaTerm p = chiX p ((p - 1) / 2) ((p - 1) / 2) -
      C (1 / 6) * jetDifference p - errorDifference p := by
    linear_combination -actual_chi_nativeTaylor_identity p
  rw [heq]
  exact (integralLaurent p).sub_mem ((integralLaurent p).sub_mem hc hs) he

theorem actual_nativeTaylor_endpoints (p : ℕ) :
    evaluate (1 / 4) (by norm_num) (deltaTerm p) =
        (1 - (1 / 4 : ℚ) ^ ((p - 1) / 2)) / p ∧
      evaluate 4 (by norm_num) (deltaTerm p) =
        (1 - (4 : ℚ) ^ ((p - 1) / 2)) / p ∧
      evaluate (1 / 4) (by norm_num) (jetDifference p) = 0 ∧
      evaluate 4 (by norm_num) (jetDifference p) = 0 := by
  have hVa : evaluate (1 / 4) (by norm_num) Vx = 0 := by rw [evaluate_Vx]; norm_num
  have hVb : evaluate 4 (by norm_num) Vx = 0 := by rw [evaluate_Vx]; norm_num
  have hQa : evaluate (1 / 4) (by norm_num) Qx = 0 := by rw [evaluate_Qx]; norm_num
  have hQb : evaluate 4 (by norm_num) Qx = 0 := by rw [evaluate_Qx]; norm_num
  have hT (a : ℚ) (ha : a ≠ 0) :
      evaluate a ha (T (((p - 1) / 2 : ℕ) : ℤ)) = a ^ ((p - 1) / 2) := by
    simpa only [map_one, one_mul, zpow_natCast] using
      evaluate_monomial (((p - 1) / 2 : ℕ) : ℤ) 1 a ha
  simp only [deltaTerm, termDifference, jetDifference, nativeJetPullback,
    map_mul, map_sub, evaluate_C, hT, evaluate_substitute, hVa, hVb, hQa, hQb,
    nativeTermPolynomial_origin, nativeJetPolynomial_origin,
    mul_one, mul_zero, sub_self, and_true]
  constructor <;> ring

/-- The full original chi source split, including all Taylor remainders and both pullbacks. -/
theorem literal_chi_nativeTaylor_kernel (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueZero p (chiX p ((p - 1) / 2) (p - 1 - p / 6) - deltaTerm p -
      C (1 / 6) * jetDifference p) := by
  have htail := actual_chi_tail_residue_zero p (p - 1 - p / 6) (by omega)
    (by omega) (by omega)
  have h := residueZero_add p htail (actual_errorDifference_kernel p (by omega))
  convert h using 1
  rw [← actual_chi_nativeTaylor_identity]
  ring

theorem literal_chi_nativeTaylor_coefficient (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (j : ℤ) :
    ((chiX p ((p - 1) / 2) (p - 1 - p / 6)).coeff j : ZMod p) =
      ((deltaTerm p).coeff j : ZMod p) +
        (1 / 6 : ZMod p) * ((jetDifference p).coeff j : ZMod p) := by
  have hd := actual_deltaTerm_integral p (by omega)
  have hj := actual_jetDifference_integral p (by omega)
  have hs : (1 / 6 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)
  have hsj := (integralLaurent p).mul_mem (integral_C p _ hs) hj
  have hker : residueZero p (chiX p ((p - 1) / 2) (p - 1 - p / 6) -
      (deltaTerm p + C (1 / 6) * jetDifference p)) := by
    convert literal_chi_nativeTaylor_kernel p hp using 1
    ring
  have heq := WPActualResidueVanishing.residue_coefficients_equal p
    (chiX p ((p - 1) / 2) (p - 1 - p / 6)) (deltaTerm p + C (1 / 6) * jetDifference p)
    (actual_native_cutoff_chi_integral p hp) ((integralLaurent p).add_mem hd hsj) hker j
  rw [heq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    Rat.cast_add_of_ne_zero (integral_denominator_cast_ne_zero p _ (hd j))
      (integral_denominator_cast_ne_zero p _ (hsj j)),
    WPActualResidueVanishing.constant_mul_coefficient,
    Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ hs)
      (integral_denominator_cast_ne_zero p _ (hj j))]
  have hsfield : ((1 / 6 : ℚ) : ZMod p) = (1 / 6 : ZMod p) := by norm_num [Rat.cast_def]
  rw [hsfield]

end WPActualNativeChiTaylor
