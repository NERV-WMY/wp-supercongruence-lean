import WPMomentPrecision.SecondLift.NativeQSource
import WPMomentPrecision.ResonanceDigits

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualEtaPole WPActualEtaSupport WPActualEtaPrimitive WPActualEtaIntegrality
  WPActualChiSource WPActualEtaFieldCutoff WPActualPositiveResidueSource WPActualResidueVanishing
  WPActualCentralResidueSource WPActualNativeRemainderSource WPActualNativeChiTaylor
  WPPIntegralReduction WPActualNativeSecondTaylor
  WPMomentPrecision.NativeSecondLift WPMomentPrecision.FullNativeTaylor
  WPMomentPrecision.NativeQSource

namespace WPMomentPrecision.OriginalNegativeDigit

set_option maxHeartbeats 1800000

/-- The original x-coordinate coefficient of x^(N+jp) G(Q) dlog V.
The subtracted endpoint fractions are regular at x=0, so the finite divided
differences retain exactly this coefficient for j≥0. -/
noncomputable def originalI (p j : ℕ) (G : ℚ[X]) : ℚ :=
  (weightedDifference (T (((p - 1) / 2 : ℕ) : ℤ) * substitute G Qx)).coeff
    (-(j : ℤ) * p - 1)

theorem originalI_add (p j : ℕ) (P Q : ℚ[X]) :
    originalI p j (P + Q) = originalI p j P + originalI p j Q := by
  simp only [originalI, substitute, mul_add, map_add,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem originalI_C_mul (p j : ℕ) (a : ℚ) (P : ℚ[X]) :
    originalI p j (Polynomial.C a * P) = a * originalI p j P := by
  have hs : T (((p - 1) / 2 : ℕ) : ℤ) * substitute (Polynomial.C a * P) Qx =
      LaurentPolynomial.C a * (T (((p - 1) / 2 : ℕ) : ℤ) * substitute P Qx) := by
    simp only [substitute, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    ring
  rw [originalI, hs, weightedDifference_C_mul, constant_mul_coefficient]
  rfl

theorem originalI_low_zero (p j d : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : ℚ[X]) (hP : P.natDegree ≤ d) (hgap : 3 * d ≤ (p - 1) / 2 + j * p) :
    originalI p j P = 0 := by
  let N := (p - 1) / 2
  let lo : ℤ := min 0 ((N : ℤ) - 3 * (d : ℤ))
  have hPbound : bounded (T (N : ℤ) * substitute P Qx) lo N := by
    exact bounded_mono (bounded_mul (bounded_T N) (substitute_Q_bounded P d hP))
      (by dsimp [lo]; omega) (by omega)
  have hD := weightedDifference_bounded _ lo N (by dsimp [lo]; omega)
    (by dsimp [N]; omega) hPbound
  unfold originalI
  by_contra hz
  have hl := (hD _ hz).1
  have hg : 3 * (d : ℤ) ≤ (N : ℤ) + (j : ℤ) * p := by exact_mod_cast hgap
  have hjp : 0 ≤ (j : ℤ) * (p : ℤ) :=
    mul_nonneg (Int.natCast_nonneg j) (Int.natCast_nonneg p)
  dsimp [lo] at hl
  rw [neg_mul] at hl
  omega

theorem substitute_integral_model (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (integralRationals p)[X]) :
    substitute (P.map (integralRationals p).subtype) Qx ∈ integralLaurent p := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.map_add, substitute, map_add] using
      ((integralLaurent p).add_mem hP hQ)
  | monomial n a =>
    simp only [Polynomial.map_monomial, substitute, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_monomial]
    change LaurentPolynomial.C a.val * Qx ^ n ∈ integralLaurent p
    exact (integralLaurent p).mul_mem (integral_C p a.val a.property)
      ((integralLaurent p).pow_mem (integral_Qx p (by omega)) n)

noncomputable def integralOriginalI (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℕ) (P : (integralRationals p)[X]) : integralRationals p :=
  ⟨originalI p j (P.map (integralRationals p).subtype),
    weightedDifference_integral p (by omega) _
      ((integralLaurent p).mul_mem (integral_T p _)
        (substitute_integral_model p hp P)) _⟩

theorem actual_GX_nonnegative (e : ℕ) : bounded (GX e) 0 (3 * (e : ℤ)) := by
  unfold GX
  apply bounded_sum
  intro n hn
  have hn' := Finset.mem_range.mp hn
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_pow Vx_bounded n))
    (by omega) (by omega)

/-- The whole literal negative resonance has no positive H/G contribution.
The original e-cutoff reciprocal source is retained without field truncation. -/
theorem actual_negative_residue_formula (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualResidue p ((p - 1) / 2) (p - 1 - p / 6) (-1) =
      -(1 / (p : ℚ)) * originalI p 1 (WPReview.nativePolynomial (p - p / 6)) := by
  let e := p - 1 - p / 6
  have hH : (HX e).coeff (-(p : ℤ)) = 0 := by
    by_contra hz
    have hl := (actual_HV_bounded e _ hz).1
    omega
  have hG : (GX e).coeff (-(p : ℤ)) = 0 := by
    by_contra hz
    have hl := (actual_GX_nonnegative e _ hz).1
    omega
  rw [actualResidue, actual_Peta_positive_decomposition]
  simp only [neg_one_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, constant_mul_coefficient,
    finite_derivative_coeff, monomial_shift_coefficient]
  rw [show -(p : ℤ) - 1 + 1 = -(p : ℤ) by omega,
    show -(p : ℤ) - 1 - -1 = -(p : ℤ) by omega, hH, hG]
  simp only [mul_zero, zero_add, sub_zero, zero_sub]
  rw [Fpull, show p - 1 - p / 6 + 1 = p - p / 6 by
    have := Nat.div_mul_le_self p 6; omega]
  unfold originalI
  simp only [Nat.cast_one, neg_one_mul]
  ring

variable (p : ℕ) [Fact p.Prime]

noncomputable def actualLowLogQ : ℚ[X] :=
  coefficientPolynomial (p / 6) (fun n => (actualLogQ p).coeff n)

noncomputable def integralActualUpperLogQ (hp : 19 ≤ p) : (integralRationals p)[X] :=
  coefficientIntegralPolynomial p (p - 1 - p / 6)
    (fun n => if p / 6 < n then (actualLogQ p).coeff n / (p : ℚ) else 0)
    (by
      intro n _
      split_ifs with hn
      · exact actual_log_q_upper_divided_integral p hp n hn
      · exact (integralRationals p).zero_mem)

theorem actual_log_q_integral_split (hp : 19 ≤ p) :
    actualLogQ p = actualLowLogQ p +
      Polynomial.C (p : ℚ) * (integralActualUpperLogQ p hp).map (integralRationals p).subtype := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hdegree : (actualLogQ p).natDegree ≤ p - 1 - p / 6 :=
    WPMomentPrecision.RationalNodeParity.rationalQFold_degree _ _
  ext n
  rw [coeff_add, coeff_C_mul, actualLowLogQ, coefficientPolynomial_coeff,
    integralActualUpperLogQ, coefficientIntegralPolynomial_value, coefficientPolynomial_coeff]
  by_cases hn : n < p - 1 - p / 6 + 1
  · rw [if_pos hn]
    by_cases hnd : n < p / 6 + 1
    · rw [if_pos hnd, if_neg (by omega)]
      ring
    · rw [if_neg hnd, if_pos (by omega), zero_add, mul_div_cancel₀ _ hpq]
  · have hnd : ¬ n < p / 6 + 1 := by have := Nat.div_mul_le_self p 6; omega
    rw [if_neg hn, if_neg hnd, mul_zero, add_zero]
    exact coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt (by omega))

theorem actual_log_I1_integral_split (hp : 19 ≤ p) :
    originalI p 1 (actualLogQ p) = (p : ℚ) *
      (integralOriginalI p hp 1 (integralActualUpperLogQ p hp)).val := by
  rw [actual_log_q_integral_split p hp, originalI_add, originalI_C_mul, actualLowLogQ,
    originalI_low_zero p 1 (p / 6) hp _ (coefficientPolynomial_degree _ _)
      (by have := Nat.div_mul_le_self p 6; omega), zero_add]
  rfl

/-- The actual Q-divided negative resonance is attached to the original U²
coefficient. Its remaining p multiple has an explicit integral source. -/
theorem actual_negative_digit_U2_source (hp : 19 ≤ p) :
    ∃ R : integralRationals p,
      WPMomentPrecision.ResonanceDigits.actualResonanceDigit p (-1) =
        -6 * originalI p 1 (actualU2Q p) + (p : ℚ) * R.val := by
  obtain ⟨E, hE⟩ := actual_full_q_expansion p hp
  let IH := integralOriginalI p hp 1 (integralActualUpperLogQ p hp)
  let IE := integralOriginalI p hp 1 E
  let c72 : integralRationals p := 5 * integralSeventyTwoInverse p hp
  let R : integralRationals p := -c72 * IH - IE
  have hc72 : c72.val = (5 / 72 : ℚ) := by
    change 5 * (1 / 72 : ℚ) = 5 / 72
    ring
  have hterm : originalI p 1 (nativeTermPolynomial p) = 0 :=
    originalI_low_zero p 1 (p / 6) hp _ (nativeTermPolynomial_degree p (by omega))
      (by have := Nat.div_mul_le_self p 6; omega)
  have hYU : originalI p 1 (actualYUQ p) = 0 :=
    originalI_low_zero p 1 ((p - 1) / 2) hp _ (actual_YU_q_degree p hp)
      (by have := WPActualHasseReciprocal.actual_half_exponent p (by omega); omega)
  have hF : originalI p 1 (WPReview.nativePolynomial (p - p / 6)) =
      (p : ℚ) ^ 2 * (6 * originalI p 1 (actualU2Q p) +
        (5 / 72 : ℚ) * originalI p 1 (actualLogQ p)) + (p : ℚ) ^ 3 * IE.val := by
    rw [hE, originalI_add, originalI_add, originalI_add, originalI_C_mul,
      originalI_C_mul, originalI_add, originalI_C_mul, originalI_C_mul,
      originalI_C_mul, hterm, hYU]
    simp only [mul_zero, zero_add]
    rfl
  refine ⟨R, ?_⟩
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [WPMomentPrecision.ResonanceDigits.actualResonanceDigit,
    actual_negative_residue_formula p hp, hF, actual_log_I1_integral_split p hp]
  change _ = -6 * originalI p 1 (actualU2Q p) +
    (p : ℚ) * (-c72.val * IH.val - IE.val)
  rw [hc72]
  field_simp [hpq]
  ring

/-- IR29's s_-1=-6 I1(U²) is reduced only after the actual resonance is
divided in Q. It uses the whole low-degree L2 theorem, not a degree premise. -/
theorem actual_negative_digit_U2_field (hp : 19 ≤ p) :
    ((WPMomentPrecision.ResonanceDigits.actualResonanceDigit p (-1) : ℚ) : ZMod p) =
      -6 * ((originalI p 1 (actualU2Q p) : ℚ) : ZMod p) := by
  obtain ⟨R, hR⟩ := actual_negative_digit_U2_source p hp
  let D : integralRationals p :=
    ⟨WPMomentPrecision.ResonanceDigits.actualResonanceDigit p (-1),
      WPMomentPrecision.ResonanceDigits.actual_negative_digit_integral p hp⟩
  let IU := integralOriginalI p hp 1 (integralActualU2Q p hp)
  have hIU : IU.val = originalI p 1 (actualU2Q p) := by
    change originalI p 1 ((integralActualU2Q p hp).map (integralRationals p).subtype) = _
    rw [integralActualU2Q_value]
  have hD : D = -6 * IU + (p : integralRationals p) * R := by
    apply Subtype.ext
    change WPMomentPrecision.ResonanceDigits.actualResonanceDigit p (-1) =
      -6 * IU.val + (p : ℚ) * R.val
    rw [hIU]
    exact hR
  have h := congrArg (residueHom p) hD
  simp only [map_add, map_mul, map_neg, map_ofNat, map_natCast,
    ZMod.natCast_self, zero_mul, add_zero] at h
  change ((WPMomentPrecision.ResonanceDigits.actualResonanceDigit p (-1) : ℚ) : ZMod p) =
    -6 * ((IU.val : ℚ) : ZMod p) at h
  simpa only [hIU] using h

end WPMomentPrecision.OriginalNegativeDigit
