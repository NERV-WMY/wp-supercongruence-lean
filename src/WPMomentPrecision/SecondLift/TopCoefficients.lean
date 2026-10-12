import WPMomentPrecision.SecondLift.TopNormalization
import WPMomentPrecision.SecondLift.QuadraticGreen

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualNativeParameter WPActualNativeFirstJet
  WPActualNativeSecondTaylor WPActualRankTwoParameter WPActualRankTwoResidueSource
  WPMomentPrecision.FullNativeTaylor WPMomentPrecision.NativeSecondLift
  WPMomentPrecision.TopNormalization WPMomentPrecision.QuadraticGreen

namespace WPMomentPrecision.TopCoefficients

set_option maxHeartbeats 1200000

/-- The top coefficient is transported through the literal q=1-T², including its sign. -/
theorem quadratic_composition_top {K : Type*} [CommRing K] [Nontrivial K]
    (P : K[X]) (e : ℕ) (hP : P.natDegree ≤ e) :
    (P.comp (1 - X ^ 2)).coeff (2 * e) = (-1 : K) ^ e * P.coeff e := by
  have hqbound : (1 - X ^ 2 : K[X]).natDegree ≤ 2 := by
    exact natDegree_sub_le_of_le
      (show (1 : K[X]).natDegree ≤ 0 by simp) (natDegree_X_pow_le 2)
  have hqcoeff : (1 - X ^ 2 : K[X]).coeff 2 = -1 := by
    rw [coeff_sub, coeff_one, coeff_X_pow_self]
    norm_num
  have hqdegree : (1 - X ^ 2 : K[X]).natDegree = 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero hqbound (by rw [hqcoeff]; exact neg_ne_zero.mpr one_ne_zero)
  have hqlc : (1 - X ^ 2 : K[X]).leadingCoeff = -1 := by
    rw [leadingCoeff, hqdegree, hqcoeff]
  by_cases he : P.natDegree = e
  · have h := coeff_comp_degree_mul_degree (p := P) (q := 1 - X ^ 2)
      (by rw [hqdegree]; omega)
    rw [he, hqdegree, hqlc, leadingCoeff, he] at h
    simpa only [Nat.mul_comm, mul_comm] using h
  · have hPlt : P.natDegree < e := lt_of_le_of_ne hP he
    rw [coeff_eq_zero_of_natDegree_lt hPlt, mul_zero]
    apply coeff_eq_zero_of_natDegree_lt
    have hd := natDegree_comp_le (p := P) (q := 1 - X ^ 2)
    rw [hqdegree] at hd
    omega

/-- The original first carry has no degree-2e contribution from the terminating YU term. -/
theorem actual_first_carry_top_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualFirstCarry p).coeff (2 * (p - 1 - p / 6)) =
      (-1 : ℚ) ^ (p - 1 - p / 6) *
        (parameterJet (p - 1 - p / 6) (-(p : ℚ) / 6) / (p : ℚ)) := by
  let e := p - 1 - p / 6
  have hd := Nat.div_mul_le_self p 6
  have hprod : (rankJacobiNode p 1 * actualU p).natDegree < 2 * e := by
    have h := natDegree_mul_le_of_le (actual_low_rankJacobi_degree p (by omega))
      (actual_U_degree p)
    dsimp only [e]
    omega
  have htop := quadratic_composition_top
    (nativeFirstJetAt p e) e (coefficientPolynomial_degree e _)
  rw [nativeFirstJetAt, coefficientPolynomial_coeff, if_pos (by omega)] at htop
  change (actualFirstCarry p).coeff (2 * e) = _
  rw [actualFirstCarry, mul_assoc, coeff_C_mul, coeff_sub, coeff_ofNat_mul,
    coeff_eq_zero_of_natDegree_lt hprod, mul_zero, sub_zero]
  change (1 / (p : ℚ)) * ((nativeFirstJetAt p e).comp (1 - X ^ 2)).coeff (2 * e) = _
  rw [nativeFirstJetAt, htop]
  ring

theorem integral_full_second_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralFullSecondJetAt p (p - 1 - p / 6) (by omega) (by omega)).natDegree ≤
      p - 1 - p / 6 := by
  rw [← natDegree_map_eq_of_injective
    (show Function.Injective (integralRationals p).subtype from Subtype.val_injective),
    integralFullSecondJetAt_value]
  exact coefficientPolynomial_degree _ _

theorem actual_full_second_top_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralFullSecondJacobi p hp).coeff (2 * (p - 1 - p / 6)) =
      (-1 : integralRationals p) ^ (p - 1 - p / 6) *
        (integralFullSecondJetAt p (p - 1 - p / 6) (by omega) (by omega)).coeff
          (p - 1 - p / 6) := by
  exact quadratic_composition_top _ _ (integral_full_second_degree p hp)

/-- The rational top quotient is reduced only after its integral lift is proved. -/
theorem actual_first_carry_top_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((integralActualFirstCarry p hp).map (residueHom p)).coeff
        (2 * (p - 1 - p / 6)) =
      ((integralFullSecondJacobi p hp).map (residueHom p)).coeff
        (2 * (p - 1 - p / 6)) / 6 := by
  let e := p - 1 - p / 6
  let j : integralRationals p := ⟨parameterJet e (-(p : ℚ) / 6) / (p : ℚ),
    actual_top_first_divided_integral p hp⟩
  have hc : (integralActualFirstCarry p hp).coeff (2 * e) = (-1 : integralRationals p) ^ e * j := by
    apply Subtype.ext
    have hv := congrArg (fun P : ℚ[X] => P.coeff (2 * e))
      (integralActualFirstCarry_value p hp)
    rw [coeff_map] at hv
    change ((integralActualFirstCarry p hp).coeff (2 * e)).val = _ at hv
    rw [hv, actual_first_carry_top_rational p hp]
    rfl
  have hk := congrArg (fun P : ℚ[X] => P.coeff e)
    (integralFullSecondJetAt_value p e (by omega) (by dsimp [e]; omega))
  rw [coeff_map, fullSecondJetAt, coefficientPolynomial_coeff,
    if_pos (by omega)] at hk
  change ((integralFullSecondJetAt p e (by omega) (by dsimp [e]; omega)).coeff e).val = _ at hk
  have hj : residueHom p j = (nativeFullSecondJetCoefficient p e : ZMod p) / 6 :=
    actual_top_first_second_residue p hp
  rw [coeff_map, hc, map_mul, map_pow, map_neg, map_one, hj,
    coeff_map, actual_full_second_top_integral p hp, map_mul, map_pow, map_neg, map_one]
  change (-1 : ZMod p) ^ e * ((nativeFullSecondJetCoefficient p e : ZMod p) / 6) =
    ((-1 : ZMod p) ^ e *
      (((integralFullSecondJetAt p e (by omega) (by dsimp [e]; omega)).coeff e).val : ZMod p)) / 6
  rw [hk]
  ring

/-- The actual two-node carry and centered factors fix the complete K top row. -/
theorem actual_full_second_top_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((integralFullSecondJacobi p hp).map (residueHom p)).coeff
        (2 * (p - 1 - p / 6)) =
      4 * ((actualRankDividedField p (by omega)).coeff (p - 1 - p / 6)) ^ 2 := by
  let e := p - 1 - p / 6
  have hr := congrArg (fun P : (ZMod p)[X] => P.coeff (2 * e))
    (actual_first_carry_field p hp)
  rw [coeff_C_mul, coeff_sub, coeff_ofNat_mul] at hr
  have hRsq : (actualRankDividedField p (by omega) ^ 2).coeff (2 * e) =
      ((actualRankDividedField p (by omega)).coeff e) ^ 2 := by
    rw [pow_two, show 2 * e = e + e by omega,
      coeff_mul_add_eq_of_natDegree_le (actualRankDividedField_degree p (by omega))
        (actualRankDividedField_degree p (by omega)), pow_two]
  rw [actual_first_carry_top_field p hp, hRsq] at hr
  have h6 : (6 : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd (by norm_num : 0 < 6)
      ((ZMod.natCast_eq_zero_iff 6 p).mp hz)
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd (by norm_num : 0 < 3)
      ((ZMod.natCast_eq_zero_iff 3 p).mp hz)
    omega
  have hscale : (3 : ZMod p)⁻¹ = 2 * (6 : ZMod p)⁻¹ := by
    field_simp [h6, h3]
    norm_num
  simp only [div_eq_mul_inv, one_mul] at hr
  rw [hscale] at hr
  apply mul_left_cancel₀ (inv_ne_zero h6)
  linear_combination -hr

theorem actual_quadratic_jet_top_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualQuadraticJet p hp).coeff (2 * (p - 1 - p / 6)) =
      2 * ((actualRankDividedField p (by omega)).coeff (p - 1 - p / 6)) ^ 2 := by
  rw [actualQuadraticJet, coeff_sub, coeff_ofNat_mul,
    actual_full_second_top_square p hp,
    show actualRankDividedField p (by omega) ^ 2 =
        actualRankDividedField p (by omega) * actualRankDividedField p (by omega) from pow_two _,
    show 2 * (p - 1 - p / 6) = (p - 1 - p / 6) + (p - 1 - p / 6) by omega,
    coeff_mul_add_eq_of_natDegree_le (actualRankDividedField_degree p (by omega))
      (actualRankDividedField_degree p (by omega))]
  ring

/- The terminal scalar now has an actual coefficient source. The next step uses
   the full R Wronskian to compute its product with the leading coefficient of Y,
   and the Green leading coefficient at degree 2p. No value of K is postulated. -/

end WPMomentPrecision.TopCoefficients
