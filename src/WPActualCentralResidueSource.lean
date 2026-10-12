import WPActualResidueVanishing

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualEtaPole WPActualEtaSupport WPActualEtaPrimitive WPActualEtaIntegrality
  WPActualEtaFieldCutoff WPActualPositiveResidueSource WPActualNativeHasse
  WPActualChiSource WPLaurentIntegralResidue WPPIntegralReduction
  WPActualResidueVanishing WPActualHasseReciprocal

namespace WPActualCentralResidueSource

/-- The original central coefficient, with both derivative residues literally zero. -/
theorem actual_central_residue_formula (p N e : ℕ) :
    actualResidue p N e 0 = -(1 / 2 : ℚ) * (HX e).coeff 0 -
      (1 / (p : ℚ)) *
        (weightedDifference (T (N : ℤ) * Fpull e Qx)).coeff (-1) := by
  rw [actualResidue, actual_Peta_positive_decomposition]
  simp only [zero_mul, zero_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, constant_mul_coefficient,
    finite_derivative_coeff, monomial_shift_coefficient]
  norm_num

theorem toLaurent_constant_coefficient (P : ℚ[X]) :
    (Polynomial.toLaurent P).coeff 0 = P.eval 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      hP, hQ, Polynomial.eval_add]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T, finite_monomial_coeff]
    cases n with
    | zero => simp
    | succ n =>
      rw [if_neg (by omega)]
      simp

theorem actual_HX_constant (e : ℕ) :
    (HX e).coeff 0 = (Hpolynomial e).eval (4 / 125) := by
  have h : HX e = Polynomial.toLaurent ((Hpolynomial e).comp Vpolynomial) :=
    substituteOver_toLaurent (Hpolynomial e) Vpolynomial
  rw [h, toLaurent_constant_coefficient, Polynomial.eval_comp]
  congr 1
  norm_num [Vpolynomial]

theorem actual_negative_low_coefficient (N n : ℕ) (hN : 1 ≤ N) (hn : 3 * n ≤ N) :
    (weightedDifference (T (N : ℤ) * Qx ^ n)).coeff (-1) = 0 := by
  have hQ : bounded (T (N : ℤ) * Qx ^ n) 0 N :=
    bounded_mono (bounded_mul (bounded_T N) (bounded_pow Qx_bounded n))
      (by
        have h : 3 * (n : ℤ) ≤ N := by exact_mod_cast hn
        nlinarith) (by omega)
  have hD : bounded (weightedDifference (T (N : ℤ) * Qx ^ n)) 0 ((N : ℤ) - 1) := by
    rw [weightedDifference_apply]
    exact bounded_add
      (bounded_mono (bounded_mul (bounded_C 2)
        (dividedDifference_bounded (1 / 4) _ _ _ (le_refl _) (by omega) hQ))
        (by omega) (by omega))
      (dividedDifference_bounded 4 _ _ _ (le_refl _) (by omega) hQ)
  by_contra h
  have := (hD (-1) h).1
  omega

/-- Every literal coefficient c_n/p in the retained first high band is integral. -/
theorem actual_native_first_high_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (hd : p / 6 < n) :
    0 ≤ padicValRat p (WPReview.nativeCoefficient n / (p : ℚ)) :=
  divide_prime_integral p _ (actual_native_coefficient_integral p n hp hn)
    (actual_native_coefficient_field_tail p n hp hn hd)

/-- Actual first high native source; each coefficient is formed over Q before reduction. -/
noncomputable def negativeFirstSource (p N : ℕ) : ℚ[T;T⁻¹] :=
  ∑ n ∈ Finset.Ico (p / 6 + 1) (N + 1),
    C (WPReview.nativeCoefficient n / (p : ℚ)) * (T (N : ℤ) * Qx ^ n)

theorem actual_negative_full_sum (p N e : ℕ) :
    (1 / (p : ℚ)) * (weightedDifference (T (N : ℤ) * Fpull e Qx)).coeff (-1) =
      ∑ n ∈ Finset.range (e + 1), (WPReview.nativeCoefficient n / (p : ℚ)) *
        (weightedDifference (T (N : ℤ) * Qx ^ n)).coeff (-1) := by
  rw [Fpull_expansion, Finset.mul_sum, map_sum, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have h : T (N : ℤ) * (C (WPReview.nativeCoefficient n) * Qx ^ n) =
      C (WPReview.nativeCoefficient n) * (T (N : ℤ) * Qx ^ n) := by ring
  rw [h, weightedDifference_C_mul, constant_mul_coefficient]
  ring

theorem negativeFirstSource_coefficient (p N : ℕ) :
    (weightedDifference (negativeFirstSource p N)).coeff (-1) =
      ∑ n ∈ Finset.Ico (p / 6 + 1) (N + 1),
        (WPReview.nativeCoefficient n / (p : ℚ)) *
          (weightedDifference (T (N : ℤ) * Qx ^ n)).coeff (-1) := by
  simp only [negativeFirstSource, map_sum, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, weightedDifference_C_mul, constant_mul_coefficient]

theorem actual_central_first_band (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    actualResidue p ((p - 1) / 2) ((p - 1) / 2) 0 =
      -(1 / 2 : ℚ) * (HX ((p - 1) / 2)).coeff 0 -
        (weightedDifference (negativeFirstSource p ((p - 1) / 2))).coeff (-1) := by
  rw [actual_central_residue_formula, actual_negative_full_sum,
    negativeFirstSource_coefficient, Finset.sum_Ico_eq_sub _ (by omega)]
  have hz : (∑ n ∈ Finset.range (p / 6 + 1),
      (WPReview.nativeCoefficient n / (p : ℚ)) *
        (weightedDifference (T (((p - 1) / 2 : ℕ) : ℤ) * Qx ^ n)).coeff (-1)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnr := Finset.mem_range.mp hn
    have hhalf := actual_half_exponent p hp
    have hdiv := Nat.div_mul_le_self p 6
    rw [actual_negative_low_coefficient _ n (by omega) (by omega), mul_zero]
  rw [hz, sub_zero]

theorem actual_negativeFirstSource_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    negativeFirstSource p ((p - 1) / 2) ∈ integralLaurent p := by
  rw [negativeFirstSource]
  apply (integralLaurent p).sum_mem
  intro n hn
  have hr := Finset.mem_Ico.mp hn
  exact (integralLaurent p).mul_mem
    (integral_C p _ (actual_native_first_high_integral p n hp (by omega) (by omega)))
    ((integralLaurent p).mul_mem (integral_T p _)
      ((integralLaurent p).pow_mem (integral_Qx p hp) n))

theorem weightedDifference_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) :
    weightedDifference P ∈ integralLaurent p := by
  have hquarter : (1 / 4 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 4 (by norm_num) (by omega)
  have hfour : (4 : ℚ) ∈ integralRationals p := natCast_mem _ 4
  have hqi : (1 / 4 : ℚ)⁻¹ ∈ integralRationals p := by
    simpa only [show (1 / 4 : ℚ)⁻¹ = 4 by norm_num] using hfour
  have hfi : (4 : ℚ)⁻¹ ∈ integralRationals p := by
    simpa only [show (4 : ℚ)⁻¹ = 1 / 4 by norm_num] using hquarter
  rw [weightedDifference_apply]
  exact (integralLaurent p).add_mem
    ((integralLaurent p).mul_mem (integral_C p 2 (natCast_mem (integralRationals p) 2))
      (dividedDifference_integral p (1 / 4) hquarter hqi P hP))
    (dividedDifference_integral p 4 hfour hfi P hP)

/-- The actual central field coefficient reduced to its original integral high source. -/
theorem actual_central_field_source (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) :
    (actualResidue p ((p - 1) / 2) e 0 : ZMod p) =
      -(1 / 2 : ZMod p) * (((Hpolynomial (p / 6)).eval (4 / 125 : ℚ) : ℚ) : ZMod p) -
        ((weightedDifference (negativeFirstSource p ((p - 1) / 2))).coeff (-1) : ZMod p) := by
  rw [actualResidue, actual_Peta_field_cutoff p e hp he hN]
  change (actualResidue p ((p - 1) / 2) ((p - 1) / 2) 0 : ZMod p) = _
  have hH := residue_coefficients_equal p (HX ((p - 1) / 2)) (HX (p / 6))
    (actual_HX_integral p _ hp (by omega)) (actual_HX_integral p _ hp (by omega))
    (actual_HX_low_cutoff p _ hp (by omega) (by omega)) 0
  have hD := weightedDifference_integral p hp _ (actual_negativeFirstSource_integral p hp)
  let R := integralRationals p
  let H : R := ⟨(HX ((p - 1) / 2)).coeff 0, actual_HX_integral p _ hp (by omega) 0⟩
  let D : R := ⟨(weightedDifference (negativeFirstSource p ((p - 1) / 2))).coeff (-1), hD (-1)⟩
  let a : R := ⟨1 / 2,
    WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)⟩
  have hs : actualResidue p ((p - 1) / 2) ((p - 1) / 2) 0 = (-a * H - D).val :=
    actual_central_first_band p hp
  rw [hs]
  change residueHom p (-a * H - D) = _
  rw [map_sub, map_mul, map_neg]
  have ha : residueHom p a = (1 / 2 : ZMod p) := by
    change ((1 / 2 : ℚ) : ZMod p) = _
    norm_num [Rat.cast_def]
  rw [ha, show residueHom p H = ((HX (p / 6)).coeff 0 : ZMod p) from hH,
    actual_HX_constant]
  rfl

theorem literal_central_first_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 : ZMod p) =
      -(1 / 2 : ZMod p) * (((Hpolynomial (p / 6)).eval (4 / 125 : ℚ) : ℚ) : ZMod p) -
        ((weightedDifference (negativeFirstSource p ((p - 1) / 2))).coeff (-1) : ZMod p) :=
  actual_central_field_source p _ (by omega) (by omega) (by omega)

end WPActualCentralResidueSource
