import WPActualPositiveResidueSource

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualEtaPole WPActualEtaSupport WPActualEtaPrimitive WPActualEtaIntegrality
  WPActualEtaFieldCutoff WPActualPositiveResidueSource WPActualNativeHasse
  WPActualChiSource WPLaurentIntegralResidue WPPIntegralReduction

namespace WPActualResidueVanishing

theorem constant_mul_coefficient (c : ℚ) (P : ℚ[T;T⁻¹]) (j : ℤ) :
    (C c * P).coeff j = c * P.coeff j := by
  rw [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]

theorem monomial_shift_coefficient (P : ℚ[T;T⁻¹]) (n j : ℤ) :
    (P * T n).coeff j = P.coeff (j - n) := by
  rw [T, AddMonoidAlgebra.coeff_mul_single_eq_coeff_mul (j - n)]
  · exact mul_one _
  · intro m _
    omega

theorem residue_coefficients_equal (p : ℕ) [Fact p.Prime]
    (P Q : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) (hQ : Q ∈ integralLaurent p)
    (h : residueZero p (P - Q)) (j : ℤ) :
    (P.coeff j : ZMod p) = (Q.coeff j : ZMod p) := by
  have hz := ((residueZero_iff p _).mp h).2 j
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    Rat.cast_sub_of_ne_zero (integral_denominator_cast_ne_zero p _ (hP j))
      (integral_denominator_cast_ne_zero p _ (hQ j))] at hz
  exact sub_eq_zero.mp hz

theorem actual_Peta_field_cutoff (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) (j : ℤ) :
    ((Peta p ((p - 1) / 2) e).coeff j : ZMod p) =
      ((Peta p ((p - 1) / 2) ((p - 1) / 2)).coeff j : ZMod p) := by
  apply residue_coefficients_equal
  · exact actual_Peta_integral p e hp he (by omega)
  · exact actual_Peta_integral p ((p - 1) / 2) hp (by omega) (by omega)
  · exact actual_Peta_tail_residue_zero p e hp he hN

theorem actual_outer_residues_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) :
    (actualResidue p ((p - 1) / 2) e (-1) : ZMod p) = 0 ∧
      (actualResidue p ((p - 1) / 2) e 2 : ZMod p) = 0 := by
  have hb := actual_Peta_full_support p ((p - 1) / 2) ((p - 1) / 2)
    (le_refl _) (by omega)
  have hhalf := WPActualHasseReciprocal.actual_half_exponent p hp
  have hl : (Peta p ((p - 1) / 2) ((p - 1) / 2)).coeff (-(p : ℤ) - 1) = 0 := by
    by_contra hz
    have := hb (-(p : ℤ) - 1) hz
    omega
  have hu : (Peta p ((p - 1) / 2) ((p - 1) / 2)).coeff (2 * (p : ℤ) - 1) = 0 := by
    by_contra hz
    have := hb (2 * (p : ℤ) - 1) hz
    omega
  constructor
  · simp only [actualResidue, neg_one_mul, actual_Peta_field_cutoff p e hp he hN,
      hl, Rat.cast_zero]
  · simp only [actualResidue, actual_Peta_field_cutoff p e hp he hN, hu, Rat.cast_zero]

theorem reciprocal_difference_bounded (N e : ℕ) (hN : 1 ≤ N) :
    bounded (weightedDifference (T (N : ℤ) * Fpull e Qx))
      (-3 * (e : ℤ)) ((N : ℤ) - 1) := by
  have hQ : bounded (T (N : ℤ) * Fpull e Qx) (-3 * (e : ℤ)) N :=
    bounded_mono (bounded_mul (bounded_T N) (actual_FQ_bounded e)) (by omega) (by omega)
  rw [weightedDifference_apply]
  exact bounded_add
    (bounded_mono (bounded_mul (bounded_C 2)
      (dividedDifference_bounded (1 / 4) _ _ _ (by omega) (by omega) hQ))
      (by omega) (by omega))
    (dividedDifference_bounded 4 _ _ _ (by omega) (by omega) hQ)

/-- Exact full-source NC70 coefficient identity, before field reduction. -/
theorem actual_positive_residue_formula (p N e k : ℕ) (hp : 0 < p)
    (hN : 1 ≤ N) (hk : N < k * p) :
    actualResidue p N e (k : ℤ) =
      ((k : ℚ) - 1 / 2) * (HX e).coeff ((k : ℤ) * p) +
        ((k : ℚ) * p) * (GX e).coeff ((k : ℤ) * p) := by
  have hz : (weightedDifference (T (N : ℤ) * Fpull e Qx)).coeff
      ((k : ℤ) * p - 1) = 0 := by
    by_contra h
    have hu := (reciprocal_difference_bounded N e hN _ h).2
    have hkp : (N : ℤ) < (k : ℤ) * p := by exact_mod_cast hk
    omega
  rw [actualResidue, actual_Peta_positive_decomposition]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, constant_mul_coefficient,
    finite_derivative_coeff, monomial_shift_coefficient, hz, mul_zero, sub_zero]
  rw [show (k : ℤ) * p - 1 + 1 = (k : ℤ) * p by omega,
    show (k : ℤ) * p - 1 - -1 = (k : ℤ) * p by omega]
  push_cast
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem actual_HX_low_cutoff (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) :
    residueZero p (HX e - HX (p / 6)) := by
  rw [actual_HX_tail _ e hd]
  apply residueZero_sum
  intro n hn
  have hr := Finset.mem_Ico.mp hn
  have hi : (1 / (n : ℚ)) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p n (by omega) (by omega)
  have hcn := residueZero_C p (WPReview.nativeCoefficient n)
    (actual_native_coefficient_integral p n hp (by omega))
    (actual_native_coefficient_field_tail p n hp (by omega) (by omega))
  have h := residueZero_mul_integral p hcn
    ((integralLaurent p).mul_mem (integral_C p _ hi)
      ((integralLaurent p).pow_mem (integral_Vx p hp) n))
  convert h using 1
  simp only [← mul_assoc, ← map_mul, mul_one_div]

theorem actual_HX_high_coefficient_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) (j : ℤ)
    (hj : 3 * ((p / 6 : ℕ) : ℤ) < j) : ((HX e).coeff j : ZMod p) = 0 := by
  rw [residue_coefficients_equal p (HX e) (HX (p / 6))
    (actual_HX_integral p e hp he) (actual_HX_integral p (p / 6) hp (by omega))
    (actual_HX_low_cutoff p e hp he hd) j]
  have hz : (HX (p / 6)).coeff j = 0 := by
    by_contra h
    have := (actual_HV_bounded (p / 6) j h).2
    omega
  rw [hz, Rat.cast_zero]

theorem actual_GX_integral (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) : GX e ∈ integralLaurent p := by
  rw [GX]
  apply (integralLaurent p).sum_mem
  intro n hn
  have hr := Finset.mem_range.mp hn
  apply (integralLaurent p).mul_mem
  · apply integral_C
    change WPReview.nativeCoefficient n / (n : ℚ) ^ 2 ∈ integralRationals p
    by_cases hz : n = 0
    · subst n; simp
    · have hi : (1 / (n : ℚ)) ∈ integralRationals p :=
        WPFiniteConductorPolynomial.small_inverse_integral p n (by omega) (by omega)
      have h := (integralRationals p).mul_mem
        (native_Hcoefficient_integral p n hp (by omega)) hi
      convert h using 1
      field_simp
  · exact (integralLaurent p).pow_mem (integral_Vx p hp) n

theorem actual_middle_residue_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) :
    (actualResidue p ((p - 1) / 2) e 1 : ZMod p) = 0 := by
  have hH : ((HX e).coeff (p : ℤ) : ZMod p) = 0 := by
    exact actual_HX_high_coefficient_zero p e hp he hd (p : ℤ) (by omega)
  have hG := actual_GX_integral p e hp he (p : ℤ)
  let R := integralRationals p
  have hh : (1 / 2 : ℚ) ∈ R :=
    WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)
  let H : R := ⟨(HX e).coeff (p : ℤ), actual_HX_integral p e hp he (p : ℤ)⟩
  let G : R := ⟨(GX e).coeff (p : ℤ), hG⟩
  let a : R := ⟨1 / 2, hh⟩
  have hsource : actualResidue p ((p - 1) / 2) e 1 = (a * H + p * G).val := by
    have h := actual_positive_residue_formula p ((p - 1) / 2) e 1
      (by omega) (by omega) (by omega)
    simp only [Nat.cast_one, one_mul] at h
    rw [h]
    norm_num [a, H, G]
  rw [hsource]
  change residueHom p (a * H + p * G) = 0
  rw [map_add, map_mul, map_mul, show residueHom p H = 0 from hH,
    map_natCast, ZMod.natCast_self, mul_zero, zero_mul, add_zero]

/-- All three actual noncentral NC62 residues vanish at the original cutoff. -/
theorem literal_three_residues_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) (-1) : ZMod p) = 0 ∧
    (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 1 : ZMod p) = 0 ∧
    (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 2 : ZMod p) = 0 := by
  have hout := actual_outer_residues_zero p (p - 1 - p / 6) (by omega) (by omega) (by omega)
  refine ⟨hout.1, ?_, hout.2⟩
  apply actual_middle_residue_zero p _ (by omega) (by omega)
  have := Nat.div_mul_le_self p 6
  omega

end WPActualResidueVanishing
