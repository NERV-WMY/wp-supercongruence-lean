import WPLaurentIntegralResidue

open scoped BigOperators LaurentPolynomial
open LaurentPolynomial WPActualNativeHasse WPActualChiSource WPActualEtaIntegrality
  WPActualEtaPole WPActualEtaPrimitive WPActualEtaSupport WPActualPullbackSource
  WPLaurentIntegralResidue WPPIntegralReduction WPActualHasseReciprocal

namespace WPActualEtaFieldCutoff

/-- The exact original coefficient valuation above N, uniformly in both prime classes. -/
theorem actual_native_above_half_valuation (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (hN : (p - 1) / 2 < n) :
    2 ≤ padicValRat p (WPReview.nativeCoefficient n) := by
  rw [WPNativeMomentIntegrality.native_coefficient_valuation_below_prime p n hp hn]
  have hp0 : 0 < p := by omega
  have h6 : 3 ≤ 6 * n / p := by
    apply (Nat.le_div_iff_mul_le hp0).mpr
    omega
  have hdouble : 2 * (3 * n / p) ≤ 6 * n / p := by
    apply (Nat.le_div_iff_mul_le hp0).mpr
    have hmul := Nat.div_mul_le_self (3 * n) p
    nlinarith
  by_cases h3 : 3 * n / p ≤ 1 <;> omega

theorem actual_native_div_prime_above_half (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (hN : (p - 1) / 2 < n) :
    0 ≤ padicValRat p (WPReview.nativeCoefficient n / p) ∧
      ((WPReview.nativeCoefficient n / p : ℚ) : ZMod p) = 0 := by
  have hv := actual_native_above_half_valuation p n hp hn hN
  have hc : WPReview.nativeCoefficient n ≠ 0 := by intro hz; rw [hz] at hv; simp at hv
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdiv : 1 ≤ padicValRat p (WPReview.nativeCoefficient n / p) := by
    rw [padicValRat.div hc hp0, padicValRat.self (Fact.out : p.Prime).one_lt]
    omega
  refine ⟨by omega, (integral_residue_zero_iff p _ (by omega)).mpr ?_⟩
  exact Or.inr (by simpa only [WPReview.RationalCongruent, sub_zero, Nat.cast_one] using hdiv)

theorem actual_native_H_above_half (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (hN : (p - 1) / 2 < n) :
    0 ≤ padicValRat p (WPReview.nativeCoefficient n / n) ∧
      ((WPReview.nativeCoefficient n / n : ℚ) : ZMod p) = 0 := by
  have hv := actual_native_above_half_valuation p n hp hn hN
  have hc : WPReview.nativeCoefficient n ≠ 0 := by intro hz; rw [hz] at hv; simp at hv
  have hn0 : 0 < n := by omega
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnd : ¬p ∣ n := by
    intro hd
    have := Nat.le_of_dvd hn0 hd
    omega
  have hnunit : padicValRat p (n : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    rfl
  have hdiv : 1 ≤ padicValRat p (WPReview.nativeCoefficient n / n) := by
    rw [padicValRat.div hc hnq, hnunit]
    omega
  refine ⟨by omega, (integral_residue_zero_iff p _ (by omega)).mpr ?_⟩
  exact Or.inr (by simpa only [WPReview.RationalCongruent, sub_zero, Nat.cast_one] using hdiv)

theorem actual_chi_expansion (p N e : ℕ) : chiX p N e =
    ∑ n ∈ Finset.range (e + 1), C (WPReview.nativeCoefficient n / (p : ℚ)) *
      (Vx ^ n - T (N : ℤ) * Qx ^ n) := by
  rw [chiX, Fpull_expansion, Fpull_expansion]
  simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [div_eq_mul_inv, map_mul, map_one]
  ring

theorem actual_chi_tail (p N e : ℕ) (he : N ≤ e) :
    chiX p N e - chiX p N N =
      ∑ n ∈ Finset.Ico (N + 1) (e + 1), C (WPReview.nativeCoefficient n / (p : ℚ)) *
        (Vx ^ n - T (N : ℤ) * Qx ^ n) := by
  rw [actual_chi_expansion, actual_chi_expansion]
  exact (Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ he)).symm

theorem actual_HX_tail (N e : ℕ) (he : N ≤ e) : HX e - HX N =
    ∑ n ∈ Finset.Ico (N + 1) (e + 1), C (WPReview.nativeCoefficient n / (n : ℚ)) * Vx ^ n := by
  rw [HX, HX, Hpull_expansion, Hpull_expansion]
  exact (Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ he)).symm

theorem integral_Qx (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : Qx ∈ integralLaurent p := by
  rw [← actual_Vx_reciprocal]
  intro j
  rw [invert_apply]
  exact integral_Vx p hp (-j)

theorem actual_chi_tail_residue_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) :
    residueZero p (chiX p ((p - 1) / 2) e - chiX p ((p - 1) / 2) ((p - 1) / 2)) := by
  rw [actual_chi_tail p _ e hN]
  apply residueZero_sum
  intro n hn
  have hrange := Finset.mem_Ico.mp hn
  have hcn := actual_native_div_prime_above_half p n hp (by omega) (by omega)
  apply residueZero_mul_integral p (residueZero_C p _ hcn.1 hcn.2)
  exact (integralLaurent p).sub_mem ((integralLaurent p).pow_mem (integral_Vx p hp) n)
    ((integralLaurent p).mul_mem (integral_T p _) ((integralLaurent p).pow_mem (integral_Qx p hp) n))

theorem actual_HX_tail_residue_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) :
    residueZero p (HX e - HX ((p - 1) / 2)) := by
  rw [actual_HX_tail _ e hN]
  apply residueZero_sum
  intro n hn
  have hrange := Finset.mem_Ico.mp hn
  have hcn := actual_native_H_above_half p n hp (by omega) (by omega)
  exact residueZero_mul_integral p (residueZero_C p _ hcn.1 hcn.2)
    ((integralLaurent p).pow_mem (integral_Vx p hp) n)

theorem actual_AX_tail_residue_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) :
    residueZero p (AX p ((p - 1) / 2) e - AX p ((p - 1) / 2) ((p - 1) / 2)) := by
  have h := residueZero_add p (actual_chi_tail_residue_zero p e hp he hN)
    (actual_HX_tail_residue_zero p e hp he hN)
  convert h using 1
  dsimp [AX]
  ring

theorem actual_Peta_tail (p N e : ℕ) : Peta p N e - Peta p N N =
    C 2 * dividedDifference (1 / 4) (AX p N e - AX p N N) +
      dividedDifference 4 (AX p N e - AX p N N) - C (1 / 2) * (HX e - HX N) * T (-1) := by
  simp only [Peta, map_sub]
  ring

theorem actual_Peta_tail_residue_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) :
    residueZero p (Peta p ((p - 1) / 2) e - Peta p ((p - 1) / 2) ((p - 1) / 2)) := by
  let R := integralRationals p
  have hhalf : (1 / 2 : ℚ) ∈ R :=
    WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)
  have hquarter : (1 / 4 : ℚ) ∈ R := by
    simpa only [show (1 / 2 : ℚ) ^ 2 = 1 / 4 by norm_num] using R.pow_mem hhalf 2
  have h4 : (4 : ℚ) ∈ R := natCast_mem R 4
  have h2 : (2 : ℚ) ∈ R := natCast_mem R 2
  have hinvquarter : (1 / 4 : ℚ)⁻¹ ∈ R := by simpa only [show (1 / 4 : ℚ)⁻¹ = 4 by norm_num] using h4
  have hinv4 : (4 : ℚ)⁻¹ ∈ R := by simpa only [show (4 : ℚ)⁻¹ = 1 / 4 by norm_num] using hquarter
  rw [actual_Peta_tail]
  have hA := actual_AX_tail_residue_zero p e hp he hN
  apply residueZero_sub
  · apply residueZero_add
    · rw [mul_comm]
      exact residueZero_mul_integral p
        (residueZero_dividedDifference p (1 / 4) hquarter hinvquarter _ hA) (integral_C p 2 h2)
    · exact residueZero_dividedDifference p 4 h4 hinv4 _ hA
  · have hH := actual_HX_tail_residue_zero p e hp he hN
    have hscalar := residueZero_mul_integral p hH (integral_C p (1 / 2) hhalf)
    have hprod := residueZero_mul_integral p hscalar (integral_T p (-1))
    convert hprod using 1
    ring

theorem actual_Aeta_tail_residue_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) :
    residueZero p (Aeta p ((p - 1) / 2) e - Aeta p ((p - 1) / 2) ((p - 1) / 2)) := by
  rw [Aeta, Aeta, ← canonicalPrimitive_sub]
  exact residueZero_canonicalPrimitive p _ (actual_Peta_tail_residue_zero p e hp he hN)

/-- Every actual full primitive coefficient has the same residue as the original e=N source. -/
theorem actual_Aeta_field_cutoff (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) (j : ℤ) :
    ((Aeta p ((p - 1) / 2) e).coeff j : ZMod p) =
      ((Aeta p ((p - 1) / 2) ((p - 1) / 2)).coeff j : ZMod p) := by
  have hzero := ((residueZero_iff p _).mp (actual_Aeta_tail_residue_zero p e hp he hN)).2 j
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] at hzero
  have hdN : p / 6 ≤ (p - 1) / 2 := by omega
  have hdE := hdN.trans hN
  rw [Rat.cast_sub_of_ne_zero
    (integral_denominator_cast_ne_zero p _ (actual_Aeta_integral p e hp he hdE j))
    (integral_denominator_cast_ne_zero p _ (actual_Aeta_integral p ((p - 1) / 2) hp (by omega) hdN j))] at hzero
  exact sub_eq_zero.mp hzero

/-- The field source is the actual entire canonical primitive, reduced through integral coefficients. -/
noncomputable def fieldAeta (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) : (ZMod p)[T;T⁻¹] :=
  residueLaurent p ⟨Aeta p ((p - 1) / 2) e, actual_Aeta_integral p e hp he hd⟩

theorem fieldAeta_coeff (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) (j : ℤ) :
    (fieldAeta p e hp he hd).coeff j = ((Aeta p ((p - 1) / 2) e).coeff j : ZMod p) :=
  residueLaurent_coeff p _ j

theorem actual_field_Aeta_support (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) (j : ℤ)
    (hj : (fieldAeta p e hp he (by omega)).coeff j ≠ 0) :
    -(p : ℤ) + 2 ≤ j ∧ j ≤ 3 * (((p - 1) / 2 : ℕ) : ℤ) := by
  rw [fieldAeta_coeff, actual_Aeta_field_cutoff p e hp he hN] at hj
  have hshort : (Aeta p ((p - 1) / 2) ((p - 1) / 2)).coeff j ≠ 0 := by
    intro hz; rw [hz, Rat.cast_zero] at hj; exact hj rfl
  have hb := actual_Aeta_full_support p ((p - 1) / 2) ((p - 1) / 2) (le_refl _) (by omega) j hshort
  have hhalf := actual_half_exponent p hp
  omega

theorem actual_field_Aeta_full_band (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hN : (p - 1) / 2 ≤ e) (j : ℤ)
    (hj : (fieldAeta p e hp he (by omega)).coeff j ≠ 0) :
    -(p : ℤ) < j ∧ j < 2 * (p : ℤ) := by
  have hb := actual_field_Aeta_support p e hp he hN j hj
  omega

theorem actual_field_Aeta_resonant_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) (k : ℤ) :
    (fieldAeta p e hp he hd).coeff (k * p) = 0 := by
  rw [fieldAeta_coeff, actual_Aeta_resonant_zero, Rat.cast_zero]

theorem actual_field_Aeta_two_slots_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) :
    (fieldAeta p e hp he hd).coeff 0 = 0 ∧ (fieldAeta p e hp he hd).coeff (p : ℤ) = 0 := by
  exact ⟨by simpa using actual_field_Aeta_resonant_zero p e hp he hd 0,
    by simpa using actual_field_Aeta_resonant_zero p e hp he hd 1⟩

/-- Literal all-prime source at the original e=p-1-floor(p/6), with no support premise. -/
noncomputable def literalFieldAeta (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  fieldAeta p (p - 1 - p / 6) (by omega) (by omega) (by
    have hdiv := Nat.div_mul_le_self p 6
    omega)

theorem literalFieldAeta_coeff (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℤ) :
    (literalFieldAeta p hp).coeff j =
      ((Aeta p ((p - 1) / 2) (p - 1 - p / 6)).coeff j : ZMod p) := fieldAeta_coeff _ _ _ _ _ _

theorem literal_field_Aeta_NC63 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (∀ j, (literalFieldAeta p hp).coeff j ≠ 0 →
      -(p : ℤ) + 2 ≤ j ∧ j ≤ 3 * (((p - 1) / 2 : ℕ) : ℤ)) ∧
      (literalFieldAeta p hp).coeff 0 = 0 ∧ (literalFieldAeta p hp).coeff (p : ℤ) = 0 := by
  refine ⟨fun j hj => ?_, ?_⟩
  · exact actual_field_Aeta_support p _ (by omega) (by omega) (by omega) j hj
  · exact actual_field_Aeta_two_slots_zero p _ _ _ _

theorem literal_field_Aeta_full_band (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : (literalFieldAeta p hp).coeff j ≠ 0) :
    -(p : ℤ) < j ∧ j < 2 * (p : ℤ) := by
  have h := (literal_field_Aeta_NC63 p hp).1 j hj
  omega

end WPActualEtaFieldCutoff
