import WPActualNativeFirstJet

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualEtaPole WPActualEtaSupport WPActualEtaPrimitive WPActualEtaIntegrality
  WPActualEtaFieldCutoff WPActualPositiveResidueSource WPActualNativeHasse
  WPActualChiSource WPLaurentIntegralResidue WPPIntegralReduction
  WPActualResidueVanishing WPActualHasseReciprocal WPActualCentralResidueSource
  WPActualNativeParameter WPActualNativeFirstJet

namespace WPActualCentralNativeJet

/-- The entire original finite parameter derivative J_N, formed at epsilon=-p/6. -/
noncomputable def nativeJetPolynomial (p : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range ((p - 1) / 2 + 1),
    Polynomial.monomial n (parameterJet n (-(p : ℚ) / 6))

noncomputable def nativeJetPullback (p : ℕ) : ℚ[T;T⁻¹] :=
  T (((p - 1) / 2 : ℕ) : ℤ) * substitute (nativeJetPolynomial p) Qx

theorem nativeJetPolynomial_coeff (p n : ℕ) : (nativeJetPolynomial p).coeff n =
    if n < (p - 1) / 2 + 1 then parameterJet n (-(p : ℚ) / 6) else 0 := by
  classical
  simp only [nativeJetPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
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

theorem nativeJetPolynomial_origin (p : ℕ) : (nativeJetPolynomial p).eval 0 = 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, nativeJetPolynomial_coeff,
    if_pos (by omega), parameterJet_empty]

theorem actual_nativeJetPullback_endpoints (p : ℕ) :
    evaluate (1 / 4) (by norm_num) (nativeJetPullback p) = 0 ∧
      evaluate 4 (by norm_num) (nativeJetPullback p) = 0 := by
  have ha : evaluate (1 / 4) (by norm_num) Qx = 0 := by rw [evaluate_Qx]; norm_num
  have hb : evaluate 4 (by norm_num) Qx = 0 := by rw [evaluate_Qx]; norm_num
  constructor <;> simp only [nativeJetPullback, map_mul, evaluate_substitute,
    ha, hb, nativeJetPolynomial_origin, mul_zero]

theorem nativeJetPullback_expansion (p : ℕ) : nativeJetPullback p =
    ∑ n ∈ Finset.range ((p - 1) / 2 + 1),
      C (parameterJet n (-(p : ℚ) / 6)) *
        (T (((p - 1) / 2 : ℕ) : ℤ) * Qx ^ n) := by
  simp only [nativeJetPullback, nativeJetPolynomial, substitute, map_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  change T (((p - 1) / 2 : ℕ) : ℤ) *
    Polynomial.eval₂ C Qx (Polynomial.monomial n (parameterJet n (-(p : ℚ) / 6))) = _
  rw [Polynomial.eval₂_monomial]
  ring

theorem actual_nativeJetPullback_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    nativeJetPullback p ∈ integralLaurent p := by
  rw [nativeJetPullback_expansion]
  apply (integralLaurent p).sum_mem
  intro n hn
  have hr := Finset.mem_range.mp hn
  exact (integralLaurent p).mul_mem
    (integral_C p _ (actual_parameterJet_integral p n hp (by omega)))
    ((integralLaurent p).mul_mem (integral_T p _)
      ((integralLaurent p).pow_mem (integral_Qx p hp) n))

noncomputable def highJetSource (p : ℕ) : ℚ[T;T⁻¹] :=
  ∑ n ∈ Finset.Ico (p / 6 + 1) ((p - 1) / 2 + 1),
    C (parameterJet n (-(p : ℚ) / 6) / 6) *
      (T (((p - 1) / 2 : ℕ) : ℤ) * Qx ^ n)

theorem actual_jet_div_six_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    0 ≤ padicValRat p (parameterJet n (-(p : ℚ) / 6) / 6) := by
  have hi : (1 / 6 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)
  change parameterJet n (-(p : ℚ) / 6) / 6 ∈ integralRationals p
  convert (integralRationals p).mul_mem (actual_parameterJet_integral p n hp hn) hi using 1
  ring

theorem actual_highJetSource_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    highJetSource p ∈ integralLaurent p := by
  rw [highJetSource]
  apply (integralLaurent p).sum_mem
  intro n hn
  have hr := Finset.mem_Ico.mp hn
  exact (integralLaurent p).mul_mem
    (integral_C p _ (actual_jet_div_six_integral p n hp (by omega)))
    ((integralLaurent p).mul_mem (integral_T p _)
      ((integralLaurent p).pow_mem (integral_Qx p hp) n))

theorem actual_high_coefficient_jet_kernel (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (hd : p / 6 < n) :
    residueZero p (C (WPReview.nativeCoefficient n / (p : ℚ) -
      parameterJet n (-(p : ℚ) / 6) / 6)) := by
  have hc := actual_native_first_high_integral p n hp hn hd
  have hj := actual_parameterJet_integral p n hp hn
  have hj6 := actual_jet_div_six_integral p n hp hn
  have hs : (1 / 6 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)
  have hsfield : ((1 / 6 : ℚ) : ZMod p) = (1 / 6 : ZMod p) := by norm_num [Rat.cast_def]
  apply residueZero_C p _ ((integralRationals p).sub_mem hc hj6)
  rw [Rat.cast_sub_of_ne_zero (integral_denominator_cast_ne_zero p _ hc)
    (integral_denominator_cast_ne_zero p _ hj6),
    actual_high_first_jet_coefficient p n hp hn hd,
    show parameterJet n (-(p : ℚ) / 6) / 6 =
      parameterJet n (-(p : ℚ) / 6) * (1 / 6 : ℚ) by ring,
    Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ hj)
      (integral_denominator_cast_ne_zero p _ hs), hsfield]
  ring

theorem actual_negativeFirstSource_jet_kernel (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueZero p (negativeFirstSource p ((p - 1) / 2) - highJetSource p) := by
  rw [negativeFirstSource, highJetSource, ← Finset.sum_sub_distrib]
  apply residueZero_sum
  intro n hn
  have hr := Finset.mem_Ico.mp hn
  have h := residueZero_mul_integral p
    (actual_high_coefficient_jet_kernel p n hp (by omega) (by omega))
    ((integralLaurent p).mul_mem (integral_T p (((p - 1) / 2 : ℕ) : ℤ))
      ((integralLaurent p).pow_mem (integral_Qx p hp) n))
  convert h using 1
  rw [map_sub, sub_mul]

theorem weightedDifference_residue_kernel (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : ℚ[T;T⁻¹]) (hP : residueZero p P) : residueZero p (weightedDifference P) := by
  let R := integralRationals p
  have ha : (1 / 4 : ℚ) ∈ R :=
    WPFiniteConductorPolynomial.small_inverse_integral p 4 (by norm_num) (by omega)
  have hb : (4 : ℚ) ∈ R := natCast_mem R 4
  have hai : (1 / 4 : ℚ)⁻¹ ∈ R := by
    simpa only [show (1 / 4 : ℚ)⁻¹ = 4 by norm_num] using hb
  have hbi : (4 : ℚ)⁻¹ ∈ R := by
    simpa only [show (4 : ℚ)⁻¹ = 1 / 4 by norm_num] using ha
  rw [weightedDifference_apply]
  apply residueZero_add
  · rw [mul_comm]
    exact residueZero_mul_integral p (residueZero_dividedDifference p (1 / 4) ha hai P hP)
      (integral_C p 2 (natCast_mem R 2))
  · exact residueZero_dividedDifference p 4 hb hbi P hP

theorem weighted_negative_full_band (N d : ℕ) (hN : 1 ≤ N) (hd : 3 * d ≤ N)
    (a : ℕ → ℚ) :
    (weightedDifference (∑ n ∈ Finset.Ico (d + 1) (N + 1),
      C (a n) * (T (N : ℤ) * Qx ^ n))).coeff (-1) =
    (weightedDifference (∑ n ∈ Finset.range (N + 1),
      C (a n) * (T (N : ℤ) * Qx ^ n))).coeff (-1) := by
  simp only [map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    weightedDifference_C_mul, constant_mul_coefficient]
  rw [Finset.sum_Ico_eq_sub _ (by omega)]
  have hz : (∑ n ∈ Finset.range (d + 1),
      a n * (weightedDifference (T (N : ℤ) * Qx ^ n)).coeff (-1)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hr := Finset.mem_range.mp hn
    rw [actual_negative_low_coefficient N n hN (by omega), mul_zero]
  rw [hz, sub_zero]

theorem actual_highJetSource_full_coefficient (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (weightedDifference (highJetSource p)).coeff (-1) =
      (1 / 6 : ℚ) * (weightedDifference (nativeJetPullback p)).coeff (-1) := by
  rw [highJetSource, weighted_negative_full_band _ _ (by omega) (by
    have hhalf := actual_half_exponent p hp
    have hdiv := Nat.div_mul_le_self p 6
    omega)]
  have h : (∑ n ∈ Finset.range ((p - 1) / 2 + 1),
      C (parameterJet n (-(p : ℚ) / 6) / 6) *
        (T (((p - 1) / 2 : ℕ) : ℤ) * Qx ^ n)) = C (1 / 6) * nativeJetPullback p := by
    rw [nativeJetPullback_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [show parameterJet n (-(p : ℚ) / 6) / 6 =
      (1 / 6 : ℚ) * parameterJet n (-(p : ℚ) / 6) by ring, map_mul]
    ring
  rw [h, weightedDifference_C_mul, constant_mul_coefficient]

/-- The actual original r0 is attached to the full native J_N, with no assigned value. -/
theorem literal_central_native_jet (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 : ZMod p) =
      -(1 / 2 : ZMod p) * (((Hpolynomial (p / 6)).eval (4 / 125 : ℚ) : ℚ) : ZMod p) -
        (1 / 6 : ZMod p) * ((weightedDifference (nativeJetPullback p)).coeff (-1) : ZMod p) := by
  have hcomp := residue_coefficients_equal p
    (weightedDifference (negativeFirstSource p ((p - 1) / 2)))
    (weightedDifference (highJetSource p))
    (weightedDifference_integral p (by omega) _ (actual_negativeFirstSource_integral p (by omega)))
    (weightedDifference_integral p (by omega) _ (actual_highJetSource_integral p (by omega)))
    (by
      rw [← map_sub]
      exact weightedDifference_residue_kernel p (by omega) _
        (actual_negativeFirstSource_jet_kernel p (by omega))) (-1)
  have hj := weightedDifference_integral p (by omega) _ (actual_nativeJetPullback_integral p (by omega)) (-1)
  have hs : (1 / 6 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)
  rw [literal_central_first_source p hp, hcomp, actual_highJetSource_full_coefficient p (by omega),
    Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ hs)
      (integral_denominator_cast_ne_zero p _ hj)]
  have hsfield : ((1 / 6 : ℚ) : ZMod p) = (1 / 6 : ZMod p) := by norm_num [Rat.cast_def]
  rw [hsfield]

end WPActualCentralNativeJet
