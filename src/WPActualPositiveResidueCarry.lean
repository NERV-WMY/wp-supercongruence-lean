import WPActualNativeRemainderSource

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualEtaPole WPActualEtaSupport WPActualEtaPrimitive WPActualEtaIntegrality
  WPActualEtaFieldCutoff WPActualPositiveResidueSource WPActualNativeHasse
  WPActualResidueVanishing WPLaurentIntegralResidue WPPIntegralReduction
  WPActualNativeParameter WPActualNativeFirstJet WPActualCentralResidueSource
  WPActualNativeRemainderSource WPActualNativeCanonicalPart WPActualCanonicalFinitePart
  WPActualCanonicalSource

namespace WPActualPositiveResidueCarry

variable (p : ℕ) [Fact p.Prime]

theorem inverse_nat_integral (n : ℕ) (hn : 0 < n) (hlt : n < p) :
    (n : ℚ)⁻¹ ∈ integralRationals p := by
  change 0 ≤ padicValRat p (n : ℚ)⁻¹
  have hi := WPFiniteConductorPolynomial.small_inverse_integral p n hn hlt
  change 0 ≤ padicValRat p (1 / (n : ℚ)) at hi
  simpa only [one_div] using hi

theorem divide_nat_integral (a : ℚ) (ha : a ∈ integralRationals p)
    (n : ℕ) (hn : 0 < n) (hlt : n < p) : a / n ∈ integralRationals p := by
  exact (integralRationals p).mul_mem ha (inverse_nat_integral p n hn hlt)

theorem divide_nat_residue (a : ℚ) (ha : a ∈ integralRationals p)
    (n : ℕ) (hn : 0 < n) (hlt : n < p) :
    ((a / n : ℚ) : ZMod p) = (a : ZMod p) / (n : ZMod p) := by
  have hu : (n : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff n p).mp hz
    have := Nat.le_of_dvd hn hd
    omega
  have hnum : (((n : ℚ).num : ℤ) : ZMod p) ≠ 0 := by simpa using hu
  rw [Rat.cast_div_of_ne_zero (integral_denominator_cast_ne_zero p a ha) hnum,
    Rat.cast_natCast]

theorem Vpower_high_zero (a : ℚ) (n : ℕ) (j : ℤ) (hj : 3 * (n : ℤ) < j) :
    (C a * Vx ^ n).coeff j = 0 := by
  by_contra h
  have hb := bounded_mul (bounded_C a) (bounded_pow Vx_bounded n)
  have hu := (hb j h).2
  omega

/-- The entire high native band, divided in Q before any residue is taken. -/
noncomputable def dividedH (e : ℕ) : ℚ[T;T⁻¹] :=
  ∑ n ∈ Finset.Ico (p / 6 + 1) (e + 1),
    C ((WPReview.nativeCoefficient n / (p : ℚ)) / (n : ℚ)) * Vx ^ n

theorem dividedH_integral (e : ℕ) (hp : 7 ≤ p) (he : e < p) :
    dividedH p e ∈ integralLaurent p := by
  rw [dividedH]
  apply (integralLaurent p).sum_mem
  intro n hn
  have hr := Finset.mem_Ico.mp hn
  exact (integralLaurent p).mul_mem
    (integral_C p _ (divide_nat_integral p _
      (actual_native_first_high_integral p n hp (by omega) (by omega))
      n (by omega) (by omega)))
    ((integralLaurent p).pow_mem (integral_Vx p hp) n)

omit [Fact p.Prime] in
theorem dividedH_exact_coefficient (e : ℕ) (hd : p / 6 ≤ e)
    (j : ℤ) (hj : 3 * ((p / 6 : ℕ) : ℤ) < j) :
    (dividedH p e).coeff j = (HX e).coeff j / (p : ℚ) := by
  have hs : dividedH p e = C (1 / (p : ℚ)) * (HX e - HX (p / 6)) := by
    rw [actual_HX_tail _ e hd, dividedH, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [← mul_assoc, ← map_mul]
    congr 1
    ring
  have hz : (HX (p / 6)).coeff j = 0 := by
    by_contra h
    have := (actual_HV_bounded (p / 6) j h).2
    omega
  rw [hs, constant_mul_coefficient, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    hz, sub_zero]
  ring

theorem dividedH_term_reduction (n : ℕ) (hp : 7 ≤ p) (hn : n < p)
    (hd : p / 6 < n) :
    reduceLaurent p (C ((WPReview.nativeCoefficient n / (p : ℚ)) / (n : ℚ)) * Vx ^ n) =
      C (1 / 6 : ZMod p) *
        reduceLaurent p (C (parameterJet n (-(p : ℚ) / 6) / (n : ℚ)) * Vx ^ n) := by
  have hc := actual_native_first_high_integral p n hp hn hd
  have hcn := divide_nat_integral p _ hc n (by omega) hn
  have hjn := native_jet_div_integral p n hp hn
  have hV := (integralLaurent p).pow_mem (integral_Vx p hp) n
  rw [reduceLaurent_mul_integral p _ _ (integral_C p _ hcn) hV,
    reduceLaurent_mul_integral p _ _ (integral_C p _ hjn) hV,
    reduceLaurent_C_integral p _ hcn, reduceLaurent_C_integral p _ hjn,
    divide_nat_residue p _ hc n (by omega) hn,
    native_jet_div_residue p n hp hn, actual_high_first_jet_coefficient p n hp hn hd]
  simp only [div_eq_mul_inv, map_mul]
  ring

theorem dividedH_term_high_zero (n : ℕ) (hp : 7 ≤ p) (hn : n < p)
    (hN : (p - 1) / 2 < n) :
    reduceLaurent p (C ((WPReview.nativeCoefficient n / (p : ℚ)) / (n : ℚ)) * Vx ^ n) = 0 := by
  have hc := actual_native_div_prime_above_half p n hp hn hN
  have hcn := divide_nat_integral p _ hc.1 n (by omega) hn
  rw [reduceLaurent_mul_integral p _ _ (integral_C p _ hcn)
    ((integralLaurent p).pow_mem (integral_Vx p hp) n),
    reduceLaurent_C_integral p _ hcn,
    divide_nat_residue p _ hc.1 n (by omega) hn, hc.2, zero_div, map_zero, zero_mul]

theorem dividedH_high_coefficient_reduction (e : ℕ) (hp : 19 ≤ p)
    (he : e < p) (hN : (p - 1) / 2 ≤ e) (j : ℤ)
    (hj : 3 * ((p / 6 : ℕ) : ℤ) < j) :
    ((dividedH p e).coeff j : ZMod p) =
      (1 / 6 : ZMod p) * (Polynomial.toLaurent
        (pullbackPolynomial p (nativeHJet p))).coeff j := by
  have heq : reduceLaurent p (dividedH p e) =
      C (1 / 6 : ZMod p) *
        (∑ n ∈ Finset.Ico (p / 6 + 1) ((p - 1) / 2 + 1),
          reduceLaurent p (C (parameterJet n (-(p : ℚ) / 6) / (n : ℚ)) * Vx ^ n)) := by
    rw [dividedH, reduceLaurent_sum_integral p]
    · have hsub : Finset.Ico (p / 6 + 1) ((p - 1) / 2 + 1) ⊆
          Finset.Ico (p / 6 + 1) (e + 1) := by
        intro n hn
        have := Finset.mem_Ico.mp hn
        exact Finset.mem_Ico.mpr ⟨this.1, by omega⟩
      rw [← Finset.sum_subset hsub]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        have := Finset.mem_Ico.mp hn
        exact dividedH_term_reduction p n (by omega) (by omega) (by omega)
      · intro n hn hout
        have hr := Finset.mem_Ico.mp hn
        have hnN : (p - 1) / 2 < n := by
          by_contra h
          exact hout (Finset.mem_Ico.mpr ⟨hr.1, by omega⟩)
        exact dividedH_term_high_zero p n (by omega) (by omega) hnN
    · intro n hn
      have := Finset.mem_Ico.mp hn
      exact (integralLaurent p).mul_mem (integral_C p _
        (divide_nat_integral p _ (actual_native_first_high_integral p n
          (by omega) (by omega) (by omega)) n (by omega) (by omega)))
        ((integralLaurent p).pow_mem (integral_Vx p (by omega)) n)
  have hfull := actual_rationalNativeHJetPullback_reduction p hp
  rw [rationalNativeHJetPullback, reduceLaurent_sum_integral p] at hfull
  · have hcoeff : (∑ n ∈ Finset.Ico (p / 6 + 1) ((p - 1) / 2 + 1),
          reduceLaurent p (C (parameterJet n (-(p : ℚ) / 6) / (n : ℚ)) * Vx ^ n)).coeff j =
        (∑ n ∈ Finset.range ((p - 1) / 2 + 1),
          reduceLaurent p (C (parameterJet n (-(p : ℚ) / 6) / (n : ℚ)) * Vx ^ n)).coeff j := by
      simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
      · intro n hn hout
        have hnlow : n ≤ p / 6 := by
          by_contra h
          exact hout (Finset.mem_Ico.mpr ⟨by omega, Finset.mem_range.mp hn⟩)
        rw [reduceLaurent_coeff, Vpower_high_zero _ n j (by omega), Rat.cast_zero]
    have hh := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff j) heq
    rw [reduceLaurent_coeff, ← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply,
      smul_eq_mul, hcoeff, hfull] at hh
    exact hh
  · intro n hn
    have := Finset.mem_range.mp hn
    exact (integralLaurent p).mul_mem
      (integral_C p _ (native_jet_div_integral p n (by omega) (by omega)))
      ((integralLaurent p).pow_mem (integral_Vx p (by omega)) n)

theorem GX_high_coefficient_zero (e : ℕ) (hp : 7 ≤ p) (he : e < p)
    (hd : p / 6 ≤ e) (j : ℤ) (hj : 3 * ((p / 6 : ℕ) : ℤ) < j) :
    ((GX e).coeff j : ZMod p) = 0 := by
  have htail : residueZero p (GX e - GX (p / 6)) := by
    have hs : GX e - GX (p / 6) =
        ∑ n ∈ Finset.Ico (p / 6 + 1) (e + 1),
          C (WPReview.nativeCoefficient n / (n : ℚ) ^ 2) * Vx ^ n := by
      rw [GX, GX]
      exact (Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hd)).symm
    rw [hs]
    apply residueZero_sum
    intro n hn
    have hr := Finset.mem_Ico.mp hn
    have hi := inverse_nat_integral p n (by omega) (by omega)
    have hz := residueZero_C p (WPReview.nativeCoefficient n)
      (actual_native_coefficient_integral p n hp (by omega))
      (actual_native_coefficient_field_tail p n hp (by omega) (by omega))
    have h := residueZero_mul_integral p hz
      ((integralLaurent p).mul_mem (integral_C p _ ((integralRationals p).pow_mem hi 2))
        ((integralLaurent p).pow_mem (integral_Vx p hp) n))
    convert h using 1
    simp only [← mul_assoc, ← map_mul]
    congr 1
    field_simp
  rw [residue_coefficients_equal p _ _ (actual_GX_integral p e hp he)
    (actual_GX_integral p (p / 6) hp (by omega)) htail]
  have hz : (GX (p / 6)).coeff j = 0 := by
    rw [GX, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro n hn
    have := Finset.mem_range.mp hn
    exact Vpower_high_zero _ n j (by omega)
  rw [hz, Rat.cast_zero]

/-- The literal original positive residue digit, divided in Q. -/
noncomputable def positiveDigit (k : ℕ) : ℚ :=
  actualResidue p ((p - 1) / 2) (p - 1 - p / 6) (k : ℤ) / (p : ℚ)

omit [Fact p.Prime] in
theorem positiveDigit_exact (hp : 19 ≤ p) (k : ℕ) (hk : 0 < k) :
    positiveDigit p k = ((k : ℚ) - 1 / 2) *
      (dividedH p (p - 1 - p / 6)).coeff ((k : ℤ) * p) +
      (k : ℚ) * (GX (p - 1 - p / 6)).coeff ((k : ℤ) * p) := by
  have hdp := Nat.div_mul_le_self p 6
  have hkp : p ≤ k * p := by nlinarith
  have hthird : 3 * (p / 6) < p := by omega
  have hj : 3 * ((p / 6 : ℕ) : ℤ) < (k : ℤ) * p := by
    have h : 3 * (p / 6) < k * p := hthird.trans_le hkp
    exact_mod_cast h
  rw [positiveDigit, actual_positive_residue_formula p ((p - 1) / 2)
    (p - 1 - p / 6) k (by omega) (by omega) (by omega),
    dividedH_exact_coefficient p _ (by omega) _ hj]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp

theorem positiveDigit_integral (hp : 19 ≤ p) (k : ℕ) (hk : 0 < k) :
    positiveDigit p k ∈ integralRationals p := by
  rw [positiveDigit_exact p hp k hk]
  have hhalf : (1 / 2 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)
  exact (integralRationals p).add_mem
    ((integralRationals p).mul_mem
      ((integralRationals p).sub_mem (natCast_mem _ k) hhalf)
      (dividedH_integral p _ (by omega) (by omega) _))
    ((integralRationals p).mul_mem (natCast_mem _ k)
      (actual_GX_integral p _ (by omega) (by omega) _))

theorem positiveDigit_reduction (hp : 19 ≤ p) (k : ℕ) (hk : 0 < k) :
    (positiveDigit p k : ZMod p) = ((k : ZMod p) - 1 / 2) / 6 *
      (Polynomial.toLaurent (pullbackPolynomial p (nativeHJet p))).coeff ((k : ℤ) * p) := by
  have hdp := Nat.div_mul_le_self p 6
  have hkp : p ≤ k * p := by nlinarith
  have hthird : 3 * (p / 6) < p := by omega
  have hj : 3 * ((p / 6 : ℕ) : ℤ) < (k : ℤ) * p := by
    have h : 3 * (p / 6) < k * p := hthird.trans_le hkp
    exact_mod_cast h
  have hkI : (k : ℚ) ∈ integralRationals p := natCast_mem _ k
  have hhalf : (1 / 2 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)
  have ha : (k : ℚ) - 1 / 2 ∈ integralRationals p :=
    (integralRationals p).sub_mem hkI hhalf
  have hH := dividedH_integral p (p - 1 - p / 6) (by omega) (by omega) ((k : ℤ) * p)
  have hG := actual_GX_integral p (p - 1 - p / 6) (by omega) (by omega) ((k : ℤ) * p)
  rw [positiveDigit_exact p hp k hk,
    Rat.cast_add_of_ne_zero
      (integral_denominator_cast_ne_zero p _ ((integralRationals p).mul_mem ha hH))
      (integral_denominator_cast_ne_zero p _ ((integralRationals p).mul_mem hkI hG)),
    Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ ha)
      (integral_denominator_cast_ne_zero p _ hH),
    Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ hkI)
      (integral_denominator_cast_ne_zero p _ hG),
    Rat.cast_sub_of_ne_zero (integral_denominator_cast_ne_zero p _ hkI)
      (integral_denominator_cast_ne_zero p _ hhalf), Rat.cast_natCast,
    dividedH_high_coefficient_reduction p _ hp (by omega) (by omega) _ hj,
    GX_high_coefficient_zero p _ (by omega) (by omega) (by omega) _ hj, mul_zero, add_zero]
  norm_num [Rat.cast_def]
  ring

/-- Actual NC70 s1=Cp/12, with the native H_J source and full cutoff. -/
theorem actual_first_positive_digit (hp : 19 ≤ p) :
    (positiveDigit p 1 : ZMod p) = (pullbackPolynomial p (nativeHJet p)).coeff p / 12 := by
  rw [positiveDigit_reduction p hp 1 (by norm_num)]
  simp only [Nat.cast_one, one_mul, toLaurent_coeff_nat]
  have hu (n : ℕ) (hn : 0 < n) (hlt : n < p) : (n : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff n p).mp hz)
    omega
  have h2 := hu 2 (by omega) (by omega)
  have h6 := hu 6 (by omega) (by omega)
  have h12 := hu 12 (by omega) (by omega)
  norm_num only [Nat.cast_ofNat] at h2 h6 h12
  generalize hd2 : (2 : ZMod p) = d2
  generalize hd6 : (6 : ZMod p) = d6
  generalize hd12 : (12 : ZMod p) = d12
  have h2u : d2 ≠ 0 := hd2 ▸ h2
  have h6u : d6 ≠ 0 := hd6 ▸ h6
  have h12u : d12 ≠ 0 := hd12 ▸ h12
  field_simp [h2u, h6u, h12u]
  subst d2 d6 d12
  ring

/-- Actual NC70 s2=0; the entire original upper band is retained. -/
theorem actual_second_positive_digit (hp : 19 ≤ p) :
    (positiveDigit p 2 : ZMod p) = 0 := by
  rw [positiveDigit_reduction p hp 2 (by norm_num)]
  have hdeg := pullbackPolynomial_degree p hp (nativeHJet p) (nativeHJet_degree p)
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
  have hcast : (2 : ℤ) * p = ((2 * p : ℕ) : ℤ) := by push_cast; rfl
  simp only [Nat.cast_ofNat]
  rw [hcast, toLaurent_coeff_nat, hz, mul_zero]

/-- An actual integral witness for each original positive residue quotient. -/
noncomputable def integralPositiveDigit (hp : 19 ≤ p) (k : ℕ) (hk : 0 < k) :
    integralRationals p := ⟨positiveDigit p k, positiveDigit_integral p hp k hk⟩

theorem integralPositiveDigit_value (hp : 19 ≤ p) (k : ℕ) (hk : 0 < k) :
    (integralPositiveDigit p hp k hk).val =
      actualResidue p ((p - 1) / 2) (p - 1 - p / 6) (k : ℤ) / (p : ℚ) := rfl

/-- Both literal NC70 next digits with their exact integral witnesses. -/
theorem actual_positive_residue_digits (hp : 19 ≤ p) :
    residueHom p (integralPositiveDigit p hp 1 (by norm_num)) =
        (pullbackPolynomial p (nativeHJet p)).coeff p / 12 ∧
      residueHom p (integralPositiveDigit p hp 2 (by norm_num)) = 0 := by
  exact ⟨actual_first_positive_digit p hp, actual_second_positive_digit p hp⟩

end WPActualPositiveResidueCarry
