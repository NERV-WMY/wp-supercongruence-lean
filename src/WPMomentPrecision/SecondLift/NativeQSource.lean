import WPMomentPrecision.SecondLift.RationalNodeParity
import WPActualNativeRemainderSource

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPPIntegralReduction WPActualRankTwoParameter
  WPActualRankTwoLowTaylor WPActualNativeFirstJet WPActualNativeChiTaylor WPActualTerminatingSquare
  WPActualRankTwoLegendreField WPActualChiSource
  WPMomentPrecision.NativeSecondLift WPMomentPrecision.FullNativeTaylor
  WPMomentPrecision.RationalNodeParity WPMomentPrecision.LogQuadraticRepresentation

namespace WPMomentPrecision.NativeQSource

set_option maxHeartbeats 1600000

/-- Composition by the original quadratic q is injective in every coefficient
ring. This is expansion by X² followed by the affine involution. -/
theorem quadratic_comp_injective {K : Type*} [CommRing K] :
    Function.Injective (fun P : K[X] => P.comp (1 - X ^ 2)) := by
  intro P Q h
  have he : expand K 2 (P.comp (1 - X)) = expand K 2 (Q.comp (1 - X)) := by
    simpa only [expand_eq_comp_X_pow, comp_assoc, sub_comp, one_comp, X_comp] using h
  have ha := expand_injective (by norm_num : 0 < 2) he
  have hi := congrArg (fun R : K[X] => R.comp (1 - X)) ha
  simpa [comp_assoc] using hi

theorem rationalQFold_add (d : ℕ) (P Q : ℚ[X]) :
    rationalQFold d (P + Q) = rationalQFold d P + rationalQFold d Q := by
  unfold rationalQFold
  rw [← add_comp]
  congr 1
  ext n
  simp only [evenCoefficientFold_coeff, coeff_add]
  split_ifs <;> simp

theorem rationalQFold_C_mul (d : ℕ) (a : ℚ) (P : ℚ[X]) :
    rationalQFold d (C a * P) = C a * rationalQFold d P := by
  have hfold : evenCoefficientFold d (C a * P) = C a * evenCoefficientFold d P := by
    ext n
    simp only [evenCoefficientFold_coeff, coeff_C_mul]
    split_ifs <;> simp
  unfold rationalQFold
  rw [hfold, mul_comp, C_comp]

theorem rationalQFold_of_quadratic (d : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ d) :
    rationalQFold d (P.comp (1 - X ^ 2)) = P := by
  apply quadratic_comp_injective
  apply rationalQFold_source
  · have hq : (1 - X ^ 2 : ℚ[X]).natDegree ≤ 2 := by compute_degree
    exact natDegree_comp_le.trans ((Nat.mul_le_mul hP hq).trans (by omega))
  · rw [comp_assoc]
    congr 1
    simp only [sub_comp, one_comp, pow_comp, X_comp, neg_sq]

theorem rationalQFold_degree_of_bound (d e : ℕ) (P : ℚ[X])
    (hP : P.natDegree ≤ 2 * d) : (rationalQFold e P).natDegree ≤ d := by
  have hfold : (evenCoefficientFold e P).natDegree ≤ d := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [evenCoefficientFold_coeff]
    split_ifs
    · exact coeff_eq_zero_of_natDegree_lt (hP.trans_lt (by omega))
    · rfl
  exact natDegree_comp_le.trans ((Nat.mul_le_mul hfold
    (show (1 - X : ℚ[X]).natDegree ≤ 1 by compute_degree)).trans (by omega))

noncomputable def integralQFold (p d : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) : (integralRationals p)[X] :=
  (evenCoefficientFold d P).comp (1 - X)

theorem evenCoefficientFold_map {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) (d : ℕ) (P : K[X]) :
    (evenCoefficientFold d P).map f = evenCoefficientFold d (P.map f) := by
  ext n
  simp only [coeff_map, evenCoefficientFold_coeff]
  split_ifs <;> simp only [map_zero]

theorem integralQFold_value (p d : ℕ) [Fact p.Prime] (P : (integralRationals p)[X]) :
    (integralQFold p d P).map (integralRationals p).subtype =
      rationalQFold d (P.map (integralRationals p).subtype) := by
  rw [integralQFold, Polynomial.map_comp, evenCoefficientFold_map]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
  rfl

variable (p : ℕ) [Fact p.Prime]

/-- Both sources are literal rational polynomials obtained from the fixed two
terminating nodes before any reduction or divided-residue operation. -/
noncomputable def actualYUQ : ℚ[X] :=
  rationalQFold (p - 1 - p / 6) (rankJacobiNode p 1 * actualU p)

noncomputable def actualU2Q : ℚ[X] :=
  rationalQFold (p - 1 - p / 6) (actualU p ^ 2)

noncomputable def actualLogQ : ℚ[X] :=
  rationalQFold (p - 1 - p / 6) (actualLogSecondNumerator p)

noncomputable def integralActualYUQ (hp : 19 ≤ p) : (integralRationals p)[X] :=
  integralQFold p (p - 1 - p / 6)
    (rankIntegralJacobi p (by omega) 1 * integralU p (by omega))

noncomputable def integralActualU2Q (hp : 19 ≤ p) : (integralRationals p)[X] :=
  integralQFold p (p - 1 - p / 6) (integralU p (by omega) ^ 2)

noncomputable def integralActualLogQ (hp : 19 ≤ p) : (integralRationals p)[X] :=
  integralQFold p (p - 1 - p / 6) (integralLogSecondNumerator p hp)

theorem integralActualYUQ_value (hp : 19 ≤ p) :
    (integralActualYUQ p hp).map (integralRationals p).subtype = actualYUQ p := by
  rw [integralActualYUQ, integralQFold_value, Polynomial.map_mul,
    rankIntegralJacobi_value, integralU_value]
  rfl

theorem integralActualU2Q_value (hp : 19 ≤ p) :
    (integralActualU2Q p hp).map (integralRationals p).subtype = actualU2Q p := by
  rw [integralActualU2Q, integralQFold_value, Polynomial.map_pow, integralU_value]
  rfl

theorem integralActualLogQ_value (hp : 19 ≤ p) :
    (integralActualLogQ p hp).map (integralRationals p).subtype = actualLogQ p := by
  rw [integralActualLogQ, integralQFold_value, integralLogSecondNumerator_value]
  rfl

theorem actual_rational_YU_degree (hp : 19 ≤ p) :
    (rankJacobiNode p 1 * actualU p).natDegree ≤ p - 1 := by
  have hd := Nat.div_mul_le_self p 6
  exact (natDegree_mul_le_of_le (actual_low_rankJacobi_degree p (by omega))
    (actual_U_degree p)).trans (by omega)

theorem actual_YU_q_source (hp : 19 ≤ p) :
    (actualYUQ p).comp (1 - X ^ 2) = rankJacobiNode p 1 * actualU p := by
  apply rationalQFold_source
  · have hd := Nat.div_mul_le_self p 6
    exact (actual_rational_YU_degree p hp).trans (by omega)
  · exact actual_rational_YU_even p hp

theorem actual_U2_q_source (hp : 19 ≤ p) :
    (actualU2Q p).comp (1 - X ^ 2) = actualU p ^ 2 :=
  rationalQFold_source _ _ (natDegree_pow_le_of_le 2 (actual_U_degree p))
    (actual_rational_U_square_even p hp)

theorem actual_YU_q_degree (hp : 19 ≤ p) : (actualYUQ p).natDegree ≤ (p - 1) / 2 := by
  apply rationalQFold_degree_of_bound
  have hh := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  exact (actual_rational_YU_degree p hp).trans (by omega)

omit [Fact p.Prime] in
theorem actual_U2_q_degree : (actualU2Q p).natDegree ≤ p - 1 - p / 6 :=
  rationalQFold_degree _ _

theorem actual_rational_log_even (hp : 19 ≤ p) :
    (actualLogSecondNumerator p).comp (-X) = actualLogSecondNumerator p := by
  have hK : (fullSecondJacobi p).comp (-X) = fullSecondJacobi p := by
    rw [fullSecondJacobi, comp_assoc]
    congr 1
    simp only [sub_comp, one_comp, pow_comp, X_comp, neg_sq]
  simp only [actualLogSecondNumerator, sub_comp, mul_comp, ofNat_comp, pow_comp,
    hK, actual_rational_U_reflection p hp]
  have hs : ((-1 : ℚ) ^ (p / 6)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [mul_pow, ← C_pow, hs, C_1, one_mul]
  simp only [Nat.cast_ofNat]

omit [Fact p.Prime] in
theorem actual_rational_log_degree (_hp : 19 ≤ p) :
    (actualLogSecondNumerator p).natDegree ≤ 2 * (p - 1 - p / 6) := by
  have hK : (fullSecondJacobi p).natDegree ≤ 2 * (p - 1 - p / 6) := by
    exact natDegree_comp_le.trans ((Nat.mul_le_mul
      (WPActualNativeSecondTaylor.coefficientPolynomial_degree _ _)
      (show (1 - X ^ 2 : ℚ[X]).natDegree ≤ 2 by
        compute_degree)).trans (by omega))
  have hU2 : (144 * actualU p ^ 2 : ℚ[X]).natDegree ≤ 2 * (p - 1 - p / 6) :=
    (natDegree_mul_le_of_le (show (144 : ℚ[X]).natDegree ≤ 0 by simp)
      (natDegree_pow_le_of_le 2 (actual_U_degree p))).trans (by omega)
  simpa only [actualLogSecondNumerator, max_self] using natDegree_sub_le_of_le hK hU2

theorem actual_log_q_source (hp : 19 ≤ p) :
    (actualLogQ p).comp (1 - X ^ 2) = actualLogSecondNumerator p :=
  rationalQFold_source _ _ (actual_rational_log_degree p hp) (actual_rational_log_even p hp)

/-- The reduction of the actual rational logarithmic polynomial is the proved
IR28 polynomial, rather than a replacement lift assigned at the residue step. -/
theorem actual_log_q_field (hp : 19 ≤ p) :
    (integralActualLogQ p hp).map (residueHom p) = actualLogSecondQ p hp := by
  apply quadratic_comp_injective
  change ((integralActualLogQ p hp).map (residueHom p)).comp (1 - X ^ 2) =
    (actualLogSecondQ p hp).comp (1 - X ^ 2)
  rw [actual_logarithmic_second_q_representation]
  have hi : (integralActualLogQ p hp).comp (1 - X ^ 2) =
      integralLogSecondNumerator p hp := by
    apply polynomial_subtype_injective p
    change ((integralActualLogQ p hp).comp (1 - X ^ 2)).map (integralRationals p).subtype =
      (integralLogSecondNumerator p hp).map (integralRationals p).subtype
    rw [Polynomial.map_comp, integralActualLogQ_value,
      integralLogSecondNumerator_value]
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
    exact actual_log_q_source p hp
  have hf := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p)) hi
  simpa only [Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X, actualLogSecondNumeratorField] using hf

/-- Every upper coefficient of the literal rational L2 is divisible by p.
This is the precise integral boundary used to omit its negative contribution. -/
theorem actual_log_q_upper_divided_integral (hp : 19 ≤ p) (n : ℕ) (hn : p / 6 < n) :
    (actualLogQ p).coeff n / (p : ℚ) ∈ integralRationals p := by
  have hi : (actualLogQ p).coeff n ∈ integralRationals p := by
    rw [← integralActualLogQ_value p hp, coeff_map]
    exact ((integralActualLogQ p hp).coeff n).property
  have hz : ((actualLogQ p).coeff n : ZMod p) = 0 := by
    rw [← integralActualLogQ_value p hp, coeff_map]
    change residueHom p ((integralActualLogQ p hp).coeff n) = 0
    rw [← coeff_map, actual_log_q_field p hp]
    exact coeff_eq_zero_of_natDegree_lt ((actual_logarithmic_second_q_degree p hp).trans_lt hn)
  exact divide_prime_integral p _ hi hz

/-- The original full cutoff is retained in this rational q expansion. The
quadratic U² source and the literal L2 source are identified before reduction;
the remaining error is a p³ multiple of an integral polynomial. -/
theorem actual_full_q_expansion (hp : 19 ≤ p) :
    ∃ E : (integralRationals p)[X],
      WPReview.nativePolynomial (p - p / 6) = nativeTermPolynomial p +
        C (2 * (p : ℚ)) * actualYUQ p +
        C ((p : ℚ) ^ 2) * (C (6 : ℚ) * actualU2Q p + C (5 / 72 : ℚ) * actualLogQ p) +
        C ((p : ℚ) ^ 3) * E.map (integralRationals p).subtype := by
  obtain ⟨E, hE⟩ := actual_full_integral_second_correction p hp
  let e := p - 1 - p / 6
  let E2 := (WPMomentPrecision.TwoNodeTaylor.integralNodeShiftErrorPolynomial p hp).comp
    (1 - X ^ 2)
  let c4 : integralRationals p := (integralHalf p (by omega)) ^ 2
  let E3 : (integralRationals p)[X] := E + C c4 * E2
  have hc4 : c4.val = (1 / 4 : ℚ) := by
    change (1 / 2 : ℚ) ^ 2 = 1 / 4
    norm_num
  have hmodel : E3.map (integralRationals p).subtype =
      E.map (integralRationals p).subtype + C (1 / 4 : ℚ) * E2.map (integralRationals p).subtype := by
    rw [show E3 = E + C c4 * E2 from rfl, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C]
    change E.map (integralRationals p).subtype +
      C c4.val * E2.map (integralRationals p).subtype = _
    rw [hc4]
  have hsource : (WPReview.nativePolynomial (p - p / 6)).comp (1 - X ^ 2) =
      (nativeTermPolynomial p).comp (1 - X ^ 2) +
        C (2 * (p : ℚ)) * (rankJacobiNode p 1 * actualU p) +
        C ((p : ℚ) ^ 2) * (C (6 : ℚ) * actualU p ^ 2 +
          C (5 / 72 : ℚ) * actualLogSecondNumerator p) +
        C ((p : ℚ) ^ 3) * E3.map (integralRationals p).subtype := by
    rw [hE, integralActualSecondCorrection_value, actual_second_correction_log_source p hp,
      actual_terminating_Jacobi_square p hp, hmodel]
    have hquarter : C ((p : ℚ) / 4) = C (p : ℚ) * C (1 / 4 : ℚ) := by
      rw [← C_mul]
      congr 1
      ring
    rw [hquarter]
    dsimp only [E2]
    simp only [map_mul, map_pow, map_ofNat]
    ring
  refine ⟨integralQFold p e E3, ?_⟩
  have hf := congrArg (rationalQFold e) hsource
  have hFdegree : (WPReview.nativePolynomial (p - p / 6)).natDegree ≤ e := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [WPReview.nativePolynomial_coeff, if_neg (by dsimp [e] at hn; omega)]
  have hTermDegree : (nativeTermPolynomial p).natDegree ≤ e := by
    have hd := Nat.div_mul_le_self p 6
    exact (nativeTermPolynomial_degree p (by omega)).trans (by dsimp [e]; omega)
  rw [rationalQFold_of_quadratic e _ hFdegree, rationalQFold_add,
    rationalQFold_add, rationalQFold_add, rationalQFold_of_quadratic e _ hTermDegree,
    rationalQFold_C_mul, rationalQFold_C_mul, rationalQFold_add,
    rationalQFold_C_mul, rationalQFold_C_mul, rationalQFold_C_mul] at hf
  rw [integralQFold_value]
  exact hf

end WPMomentPrecision.NativeQSource
