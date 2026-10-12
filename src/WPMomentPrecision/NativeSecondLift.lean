import WPMomentPrecision.SecondLift.TerminatingSquare
import WPMomentPrecision.SecondLift.FullNativeTaylor
import WPMomentPrecision.SecondLift.TwoNodeTaylor
import WPActualRankTwoResidueSource
import WPActualNativeJacobiJet
import WPActualPositiveResidueCarry
import WPMomentPrecision.ResonanceDigits

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPPIntegralReduction WPActualRankTwoParameter
  WPActualRankTwoDividedDifference WPActualRankTwoGaussODE
  WPActualRankTwoLegendreField WPActualRankTwoResidueSource
  WPActualRankTwoLowTaylor WPActualNativeJacobiJet
  WPActualEtaPrimitive WPActualEtaIntegrality WPActualResidueVanishing
  WPActualChiSource

namespace WPMomentPrecision.NativeSecondLift

set_option maxHeartbeats 1200000

variable (p : ℕ) [Fact p.Prime]

/-- NC76's actual rational lift U, fixed by the two original terminating nodes. -/
noncomputable def actualU : ℚ[X] := C (1 / 6 : ℚ) * rankDividedJacobi p

theorem actual_U_normalization (hp : 7 ≤ p) :
    C (4 * (p : ℚ)) * actualU p = rankJacobiNode p 1 - rankJacobiNode p 5 := by
  rw [actual_two_jacobi_node_difference p hp, actualU, ← mul_assoc, ← C_mul]
  rw [show 4 * (p : ℚ) * (1 / 6) = 2 * (p : ℚ) / 3 by ring]

theorem actual_U_divided_nodes (hp : 7 ≤ p) :
    actualU p = C (1 / (4 * (p : ℚ))) * (rankJacobiNode p 1 - rankJacobiNode p 5) := by
  rw [← actual_U_normalization p hp, ← mul_assoc, ← C_mul]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  rw [one_div_mul_cancel (mul_ne_zero (by norm_num) hpq), C_1, one_mul]

/-- The parity-preserving native representative of IR27 uses both exact nodes. -/
noncomputable def actualZ : ℚ[X] :=
  C (1 / 4 : ℚ) * (5 * rankJacobiNode p 1 - rankJacobiNode p 5)

theorem actual_Z_source (hp : 7 ≤ p) :
    actualZ p = rankJacobiNode p 1 + C (p : ℚ) * actualU p := by
  have h := actual_U_normalization p hp
  simp only [map_mul, map_ofNat] at h
  have hs : C (1 / 4 : ℚ) * (4 : ℚ[X]) = 1 := by
    change C (1 / 4 : ℚ) * C (4 : ℚ) = 1
    rw [← C_mul]
    norm_num
  unfold actualZ
  linear_combination -C (1 / 4 : ℚ) * h +
    rankJacobiNode p 1 * hs + C (p : ℚ) * actualU p * hs

noncomputable def integralU (hp : 7 ≤ p) : (integralRationals p)[X] :=
  C (integralSixth p hp) * rankDividedIntegralJacobi p hp

theorem integralU_value (hp : 7 ≤ p) :
    (integralU p hp).map (integralRationals p).subtype = actualU p := by
  rw [integralU, Polynomial.map_mul, Polynomial.map_C, rankDividedIntegralJacobi_value]
  rfl

theorem actual_U_integral (hp : 7 ≤ p) (n : ℕ) :
    (actualU p).coeff n ∈ integralRationals p := by
  rw [← integralU_value p hp, Polynomial.coeff_map]
  exact ((integralU p hp).coeff n).property

noncomputable def actualUField (hp : 7 ≤ p) : (ZMod p)[X] :=
  (integralU p hp).map (residueHom p)

theorem actual_U_field (hp : 7 ≤ p) :
    actualUField p hp = C (1 / 6 : ZMod p) * actualRankDividedField p hp := by
  rw [actualUField, integralU, Polynomial.map_mul, Polynomial.map_C, integralSixth_field]
  rfl

theorem actual_U_field_coefficient (hp : 7 ≤ p) (n : ℕ) :
    ((actualU p).coeff n : ZMod p) = (actualUField p hp).coeff n := by
  rw [← integralU_value p hp, actualUField, Polynomial.coeff_map, Polynomial.coeff_map]
  rfl

omit [Fact p.Prime] in
theorem actual_U_endpoint_one : (actualU p).eval 1 = 0 := by
  rw [actualU, eval_mul, eval_C, rankDividedJacobi_endpoint_one, mul_zero]

omit [Fact p.Prime] in
theorem actual_U_degree : (actualU p).natDegree ≤ p - 1 - p / 6 := by
  exact (natDegree_mul_le_of_le (show (C (1 / 6 : ℚ)).natDegree ≤ 0 by simp)
    (rankDividedJacobi_degree p)).trans (by simp)

/-- Complete NC53 first-jet normalization after the actual U lift is attached. -/
theorem actual_native_jet_twelve_YU (hp : 19 ≤ p) :
    nativeJacobiJet p = 12 * actualLegendreJacobi p * actualUField p (by omega) := by
  have h6 : (6 : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd (by norm_num : 0 < 6)
      ((ZMod.natCast_eq_zero_iff 6 p).mp hz)
    omega
  have hscale : (12 : (ZMod p)[X]) * C (1 / 6 : ZMod p) = 2 := by
    rw [show (12 : (ZMod p)[X]) = C (12 : ZMod p) by rfl, ← C_mul]
    change C ((12 : ZMod p) * (1 / 6)) = C (2 : ZMod p)
    congr 1
    field_simp [h6]
    ring
  rw [actual_native_Jacobi_jet p hp, actual_U_field]
  linear_combination -actualLegendreJacobi p * actualRankDividedField p (by omega) * hscale

/-- Entire actual NC76 Wronskian over Q; its quotient by q is polynomial. -/
noncomputable def actualW : ℚ[X] :=
  (1 - X ^ 2) * (rankJacobiNode p 1 * (actualU p).derivative -
    (rankJacobiNode p 1).derivative * actualU p)

theorem polynomial_wronskian_source_identity (a : ℚ) (Y U : ℚ[X]) :
    36 * (((1 - X ^ 2) * (Y * U.derivative - Y.derivative * U)).derivative +
      C a * X * (Y * U.derivative - Y.derivative * U) -
      ((C (1 / 6 : ℚ) * X * Y ^ 2 - C (2 * a / 3) * X * Y * U).derivative -
        C (a / 6) * Y ^ 2 + C (2 * a ^ 2 / 3) * Y * U)) =
      Y * rankJacobiClear (-a / 6) U - U * rankJacobiClear (-a / 6) Y -
        6 * Y * (2 * X * (Y - C (4 * a) * U).derivative +
          C (1 - a) * (Y - C (4 * a) * U)) := by
  have hthird : C ((3 : ℚ)⁻¹) = 2 * C ((6 : ℚ)⁻¹) := by
    have hq : (3 : ℚ)⁻¹ = 2 * (6 : ℚ)⁻¹ := by norm_num
    simpa only [map_mul, map_ofNat] using congrArg (C : ℚ → ℚ[X]) hq
  have hsix : (6 : ℚ[X]) * C ((6 : ℚ)⁻¹) = 1 := by
    change C (6 : ℚ) * C ((6 : ℚ)⁻¹) = 1
    rw [← C_mul]
    norm_num
  simp only [rankJacobiClear, derivative_mul, derivative_C,
    derivative_X, derivative_pow_succ, derivative_one, derivative_ofNat,
    zero_mul, zero_add, mul_zero, div_eq_mul_inv, map_mul, map_add,
    map_sub, map_neg, map_pow, map_ofNat, C_1, hthird]
  simp only [Nat.cast_one, C_1]
  linear_combination
    (-12 * X * Y * Y.derivative + 12 * X * Y * U.derivative * C a +
      36 * X * Y.derivative * U * C a + 24 * Y * U * C a -
      24 * Y * U * C a ^ 2 - 6 * Y ^ 2 + 6 * Y ^ 2 * C a) * hsix

theorem actual_U_full_ODE (hp : 7 ≤ p) :
    rankJacobiClear (-(p : ℚ) / 6) (actualU p) =
      6 * (2 * X * (rankJacobiNode p 5).derivative +
        C (1 - (p : ℚ)) * rankJacobiNode p 5) := by
  rw [actualU, rankJacobiClear_C_mul, actual_rankDividedJacobi_ODE p hp]
  have hscale : C (1 / 6 : ℚ) * (36 : ℚ[X]) = 6 := by
    change C (1 / 6 : ℚ) * C (36 : ℚ) = C (6 : ℚ)
    rw [← C_mul]
    congr 1
    norm_num
  rw [← mul_assoc, hscale]

/-- The exact terminating-pair source of NC76, retaining both p and p^2 corrections. -/
theorem actual_W_full_source (hp : 7 ≤ p) :
    (actualW p).derivative + C (p : ℚ) * X *
        (rankJacobiNode p 1 * (actualU p).derivative -
          (rankJacobiNode p 1).derivative * actualU p) =
      (C (1 / 6 : ℚ) * X * rankJacobiNode p 1 ^ 2 -
        C (2 * (p : ℚ) / 3) * X * rankJacobiNode p 1 * actualU p).derivative -
      C ((p : ℚ) / 6) * rankJacobiNode p 1 ^ 2 +
      C (2 * (p : ℚ) ^ 2 / 3) * rankJacobiNode p 1 * actualU p := by
  have hY := actual_rankJacobi_ODE p 1 hp (Or.inl rfl)
  norm_num only [Nat.cast_one, neg_one_mul] at hY
  have hnode : rankJacobiNode p 1 - C (4 * (p : ℚ)) * actualU p =
      rankJacobiNode p 5 := by
    linear_combination -actual_U_normalization p hp
  have hz : (36 : ℚ[X]) *
      (((actualW p).derivative + C (p : ℚ) * X *
        (rankJacobiNode p 1 * (actualU p).derivative -
          (rankJacobiNode p 1).derivative * actualU p)) -
        ((C (1 / 6 : ℚ) * X * rankJacobiNode p 1 ^ 2 -
          C (2 * (p : ℚ) / 3) * X * rankJacobiNode p 1 * actualU p).derivative -
          C ((p : ℚ) / 6) * rankJacobiNode p 1 ^ 2 +
          C (2 * (p : ℚ) ^ 2 / 3) * rankJacobiNode p 1 * actualU p)) = 0 := by
    rw [actualW, polynomial_wronskian_source_identity, hY, actual_U_full_ODE p hp, hnode]
    ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by norm_num : (36 : ℚ[X]) ≠ 0))

/-- Genuine rational square and integral cubic error, with the full first and second cutoffs. -/
theorem actual_full_native_node_Taylor (hp : 19 ≤ p) :
    ∃ E : (integralRationals p)[X],
      (WPReview.nativePolynomial (p - p / 6)).comp (1 - X ^ 2) =
        rankJacobiNode p 1 ^ 2 +
        C ((p : ℚ) / 6) *
          (WPActualNativeSecondTaylor.nativeFirstJetAt p (p - 1 - p / 6)).comp (1 - X ^ 2) +
        C ((p : ℚ) ^ 2 / 72) *
          (WPMomentPrecision.FullNativeTaylor.fullSecondJetAt p (p - 1 - p / 6)).comp
            (1 - X ^ 2) +
        C ((p : ℚ) ^ 3) * E.map (integralRationals p).subtype := by
  obtain ⟨E, hE⟩ := WPMomentPrecision.FullNativeTaylor.actual_full_Taylor_integral_remainder p hp
  refine ⟨E.comp (1 - X ^ 2), ?_⟩
  have h := congrArg (fun P : ℚ[X] => P.comp (1 - X ^ 2)) hE
  simp only [add_comp, mul_comp, C_comp] at h
  rw [WPActualTerminatingSquare.actual_terminating_Jacobi_square p hp] at h
  rw [Polynomial.map_comp]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  exact h

noncomputable def fullFirstJacobi : ℚ[X] :=
  (WPActualNativeSecondTaylor.nativeFirstJetAt p (p - 1 - p / 6)).comp (1 - X ^ 2)

noncomputable def fullSecondJacobi : ℚ[X] :=
  (WPMomentPrecision.FullNativeTaylor.fullSecondJetAt p (p - 1 - p / 6)).comp (1 - X ^ 2)

noncomputable def integralFullFirstJacobi (hp : 19 ≤ p) : (integralRationals p)[X] :=
  (WPMomentPrecision.FullNativeTaylor.integralFirstJetAt p (p - 1 - p / 6)
    (by omega) (by omega)).comp (1 - X ^ 2)

noncomputable def integralFullSecondJacobi (hp : 19 ≤ p) : (integralRationals p)[X] :=
  (WPMomentPrecision.FullNativeTaylor.integralFullSecondJetAt p (p - 1 - p / 6)
    (by omega) (by omega)).comp (1 - X ^ 2)

theorem integralFullFirstJacobi_value (hp : 19 ≤ p) :
    (integralFullFirstJacobi p hp).map (integralRationals p).subtype = fullFirstJacobi p := by
  rw [integralFullFirstJacobi, Polynomial.map_comp,
    WPMomentPrecision.FullNativeTaylor.integralFirstJetAt_value]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  rfl

theorem integralFullSecondJacobi_value (hp : 19 ≤ p) :
    (integralFullSecondJacobi p hp).map (integralRationals p).subtype = fullSecondJacobi p := by
  rw [integralFullSecondJacobi, Polynomial.map_comp,
    WPMomentPrecision.FullNativeTaylor.integralFullSecondJetAt_value]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  rfl

theorem full_second_jacobi_integral (hp : 19 ≤ p) (n : ℕ) :
    (fullSecondJacobi p).coeff n ∈ integralRationals p := by
  rw [← integralFullSecondJacobi_value p hp, Polynomial.coeff_map]
  exact ((integralFullSecondJacobi p hp).coeff n).property

omit [Fact p.Prime] in
theorem full_second_jacobi_endpoint_one : (fullSecondJacobi p).eval 1 = 0 := by
  rw [fullSecondJacobi, Polynomial.eval_comp]
  simp only [eval_sub, eval_one, eval_pow, eval_X, one_pow, sub_self]
  rw [WPMomentPrecision.FullNativeTaylor.fullSecondJetAt_eq_twice,
    eval_mul, eval_C, WPActualNativeSecondTaylor.nativeSecondJetAt_origin, mul_zero]

theorem integralFullFirstJacobi_field (hp : 19 ≤ p) :
    (integralFullFirstJacobi p hp).map (residueHom p) = nativeJacobiJet p := by
  have hd := Nat.div_mul_le_self p 6
  have hh := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  rw [integralFullFirstJacobi, Polynomial.map_comp,
    WPMomentPrecision.FullNativeTaylor.integralFirstJetAt_field p _ hp (by omega) (by omega)]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  rfl

/-- The actual next first-jet carry is divided over Q only after its whole
original coefficient polynomial has been attached to the checked first jet. -/
noncomputable def actualFirstCarry : ℚ[X] :=
  C (1 / (p : ℚ)) * (fullFirstJacobi p - 12 * rankJacobiNode p 1 * actualU p)

theorem actual_first_carry_integral (hp : 19 ≤ p) (n : ℕ) :
    (actualFirstCarry p).coeff n ∈ integralRationals p := by
  let D : (integralRationals p)[X] := integralFullFirstJacobi p hp -
    12 * rankIntegralJacobi p (by omega) 1 * integralU p (by omega)
  have hD : D.map (integralRationals p).subtype =
      fullFirstJacobi p - 12 * rankJacobiNode p 1 * actualU p := by
    simp only [D, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
      integralFullFirstJacobi_value, rankIntegralJacobi_value, integralU_value]
  have hF : D.map (residueHom p) = 0 := by
    simp only [D, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
      integralFullFirstJacobi_field, rankIntegralJacobi_field]
    change nativeJacobiJet p -
      12 * actualLegendreJacobi p * actualUField p (by omega) = 0
    exact sub_eq_zero.mpr (actual_native_jet_twelve_YU p hp)
  have hq := congrArg (fun P : ℚ[X] => P.coeff n) hD
  rw [Polynomial.coeff_map] at hq
  have hf := congrArg (fun P : (ZMod p)[X] => P.coeff n) hF
  rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hf
  rw [actualFirstCarry, coeff_C_mul]
  rw [← hq]
  change (1 / (p : ℚ)) * (D.coeff n).val ∈ integralRationals p
  rw [show (1 / (p : ℚ)) * (D.coeff n).val = (D.coeff n).val / p by ring]
  exact divide_prime_integral p _ (D.coeff n).property hf

noncomputable def integralActualFirstCarry (hp : 19 ≤ p) : (integralRationals p)[X] :=
  WPMomentPrecision.FullNativeTaylor.integralPolynomialModel p (actualFirstCarry p)
    (actual_first_carry_integral p hp)

theorem integralActualFirstCarry_value (hp : 19 ≤ p) :
    (integralActualFirstCarry p hp).map (integralRationals p).subtype = actualFirstCarry p :=
  WPMomentPrecision.FullNativeTaylor.integralPolynomialModel_value p _ _

theorem actual_first_carry_source :
    fullFirstJacobi p = 12 * rankJacobiNode p 1 * actualU p +
      C (p : ℚ) * actualFirstCarry p := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [actualFirstCarry, ← mul_assoc, ← C_mul, mul_one_div_cancel hpq, C_1, one_mul]
  ring

/-- The actual first carry is normalized by the exact second terminating node.
The error is integral and multiplied by p after division over Q. -/
theorem actual_first_carry_two_node_source (hp : 19 ≤ p) :
    actualFirstCarry p = C (1 / 3 : ℚ) * fullSecondJacobi p -
      24 * actualU p ^ 2 + C (3 * (p : ℚ) / 2) *
        ((WPMomentPrecision.TwoNodeTaylor.integralNodeShiftErrorPolynomial p hp).comp
          (1 - X ^ 2)).map (integralRationals p).subtype := by
  have h := WPMomentPrecision.TwoNodeTaylor.actual_two_Jacobi_node_Taylor p hp
  have hb : rankJacobiNode p 5 = rankJacobiNode p 1 - C (4 * (p : ℚ)) * actualU p := by
    have hu := actual_U_normalization p (by omega)
    linear_combination hu
  rw [hb] at h
  have hsquare : (rankJacobiNode p 1 - C (4 * (p : ℚ)) * actualU p) ^ 2 =
      rankJacobiNode p 1 ^ 2 - C (8 * (p : ℚ)) * (rankJacobiNode p 1 * actualU p) +
        C (16 * (p : ℚ) ^ 2) * actualU p ^ 2 := by
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [hsquare] at h
  change rankJacobiNode p 1 ^ 2 - C (8 * (p : ℚ)) *
      (rankJacobiNode p 1 * actualU p) + C (16 * (p : ℚ) ^ 2) * actualU p ^ 2 =
      rankJacobiNode p 1 ^ 2 - C (2 * (p : ℚ) / 3) * fullFirstJacobi p +
      C (2 * (p : ℚ) ^ 2 / 9) * fullSecondJacobi p + C ((p : ℚ) ^ 3) *
        ((WPMomentPrecision.TwoNodeTaylor.integralNodeShiftErrorPolynomial p hp).comp
          (1 - X ^ 2)).map (integralRationals p).subtype at h
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  ext n
  have hn := congrArg (fun P : ℚ[X] => P.coeff n) h
  simp only [coeff_add, coeff_sub, coeff_C_mul] at hn
  have hc : (fullFirstJacobi p).coeff n - 12 * (rankJacobiNode p 1 * actualU p).coeff n =
      (p : ℚ) / 3 * (fullSecondJacobi p).coeff n -
        24 * (p : ℚ) * (actualU p ^ 2).coeff n + 3 * (p : ℚ) ^ 2 / 2 *
          (((WPMomentPrecision.TwoNodeTaylor.integralNodeShiftErrorPolynomial p hp).comp
            (1 - X ^ 2)).map (integralRationals p).subtype).coeff n := by
    have hscale : 2 * (p : ℚ) / 3 ≠ 0 :=
      div_ne_zero (mul_ne_zero (by norm_num) hpq) (by norm_num)
    apply mul_left_cancel₀ hscale
    linear_combination hn
  simp only [actualFirstCarry, mul_assoc, coeff_C_mul, coeff_sub, coeff_ofNat_mul,
    coeff_add]
  rw [hc]
  field_simp [hpq]

/-- Reduction of the actual Q-divided first carry is the whole (K(q)-2R^2)/3. -/
theorem actual_first_carry_field (hp : 19 ≤ p) :
    (integralActualFirstCarry p hp).map (residueHom p) =
      C (1 / 3 : ZMod p) * ((integralFullSecondJacobi p hp).map (residueHom p) -
        2 * actualRankDividedField p (by omega) ^ 2) := by
  let s : integralRationals p := 2 * integralSixth p (by omega)
  let t : integralRationals p := 3 * integralHalf p (by omega)
  let E := (WPMomentPrecision.TwoNodeTaylor.integralNodeShiftErrorPolynomial p hp).comp
    (1 - X ^ 2)
  have hs : s.val = (1 / 3 : ℚ) := by
    change 2 * (1 / 6 : ℚ) = 1 / 3
    norm_num
  have ht : (t * (p : integralRationals p)).val = 3 * (p : ℚ) / 2 := by
    change (3 * (1 / 2 : ℚ)) * (p : ℚ) = 3 * (p : ℚ) / 2
    ring
  have hmodel : integralActualFirstCarry p hp =
      C s * integralFullSecondJacobi p hp - 24 * integralU p (by omega) ^ 2 +
        C (t * (p : integralRationals p)) * E := by
    apply polynomial_subtype_injective p
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_ofNat, Polynomial.map_pow,
      integralActualFirstCarry_value, integralFullSecondJacobi_value, integralU_value]
    change actualFirstCarry p = C s.val * fullSecondJacobi p -
      24 * actualU p ^ 2 + C (t * (p : integralRationals p)).val *
        E.map (integralRationals p).subtype
    rw [hs, ht, actual_first_carry_two_node_source p hp]
  have hpn : residueHom p (p : integralRationals p) = 0 := by simp
  have htF : residueHom p (t * (p : integralRationals p)) = 0 := by
    rw [map_mul, hpn, mul_zero]
  rw [hmodel]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_ofNat, Polynomial.map_pow,
    htF, C_0, zero_mul, add_zero]
  have hsF : residueHom p s = (1 / 3 : ZMod p) := by
    rw [show s = 2 * integralSixth p (by omega) by rfl, map_mul,
      map_ofNat, integralSixth_field]
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
    field_simp [h6, h3]
    norm_num
  change C (residueHom p s) * _ - 24 * actualUField p (by omega) ^ 2 = _
  rw [hsF, actual_U_field]
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
  have hscale : (24 : (ZMod p)[X]) * C (1 / 6 : ZMod p) ^ 2 =
      C (1 / 3 : ZMod p) * 2 := by
    rw [← C_pow, show (24 : (ZMod p)[X]) = C (24 : ZMod p) by rfl,
      show (2 : (ZMod p)[X]) = C (2 : ZMod p) by rfl, ← C_mul, ← C_mul]
    congr 1
    field_simp [h6, h3]
    norm_num
  linear_combination -actualRankDividedField p (by omega) ^ 2 * hscale

/-- The full actual second correction, before the unproved high-band contraction. -/
noncomputable def actualSecondCorrection : ℚ[X] :=
  C (1 / 6 : ℚ) * actualFirstCarry p + C (1 / 72 : ℚ) * fullSecondJacobi p

noncomputable def integralSeventyTwoInverse (hp : 19 ≤ p) : integralRationals p :=
  ⟨1 / 72, by
    have h := (integralRationals p).mul_mem
      ((integralRationals p).pow_mem (integralSixth p (by omega)).property 2)
      (integralHalf p (by omega)).property
    change (1 / 6 : ℚ) ^ 2 * (1 / 2 : ℚ) ∈ integralRationals p at h
    convert h using 1
    norm_num⟩

noncomputable def integralActualSecondCorrection (hp : 19 ≤ p) : (integralRationals p)[X] :=
  C (integralSixth p (by omega)) * integralActualFirstCarry p hp +
    C (integralSeventyTwoInverse p hp) * integralFullSecondJacobi p hp

theorem integralActualSecondCorrection_value (hp : 19 ≤ p) :
    (integralActualSecondCorrection p hp).map (integralRationals p).subtype =
      actualSecondCorrection p := by
  simp only [integralActualSecondCorrection, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, integralActualFirstCarry_value, integralFullSecondJacobi_value]
  rfl

/-- An actual integral p^3 identity with the original e-cutoff second correction.
Replacing this correction by the low L2 expression still requires IR26--28. -/
theorem actual_full_integral_second_correction (hp : 19 ≤ p) :
    ∃ E : (integralRationals p)[X],
      (WPReview.nativePolynomial (p - p / 6)).comp (1 - X ^ 2) =
        rankJacobiNode p 1 ^ 2 +
        C (2 * (p : ℚ)) * rankJacobiNode p 1 * actualU p +
        C ((p : ℚ) ^ 2) *
          (integralActualSecondCorrection p hp).map (integralRationals p).subtype +
        C ((p : ℚ) ^ 3) * E.map (integralRationals p).subtype := by
  obtain ⟨E, hE⟩ := actual_full_native_node_Taylor p hp
  refine ⟨E, ?_⟩
  change (WPReview.nativePolynomial (p - p / 6)).comp (1 - X ^ 2) =
    rankJacobiNode p 1 ^ 2 + C ((p : ℚ) / 6) * fullFirstJacobi p +
      C ((p : ℚ) ^ 2 / 72) * fullSecondJacobi p +
      C ((p : ℚ) ^ 3) * E.map (integralRationals p).subtype at hE
  rw [hE, integralActualSecondCorrection_value, actualSecondCorrection,
    actual_first_carry_source]
  have hscale : (12 : ℚ[X]) * C ((6 : ℚ)⁻¹) = 2 := by
    have hq : (12 : ℚ) * (6 : ℚ)⁻¹ = 2 := by norm_num
    simpa only [map_mul, map_ofNat] using congrArg (C : ℚ → ℚ[X]) hq
  simp only [div_eq_mul_inv, map_mul, map_pow, map_ofNat, C_1]
  linear_combination rankJacobiNode p 1 * C (p : ℚ) * actualU p * hscale

/-- The actual logarithmic second numerator, retaining every upper coefficient.
Its reduction is K(q)-4R^2; no low-degree property is asserted by definition. -/
noncomputable def actualLogSecondNumerator : ℚ[X] :=
  fullSecondJacobi p - 144 * actualU p ^ 2

noncomputable def integralLogSecondNumerator (hp : 19 ≤ p) : (integralRationals p)[X] :=
  integralFullSecondJacobi p hp - 144 * integralU p (by omega) ^ 2

theorem integralLogSecondNumerator_value (hp : 19 ≤ p) :
    (integralLogSecondNumerator p hp).map (integralRationals p).subtype =
      actualLogSecondNumerator p := by
  simp only [integralLogSecondNumerator, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_ofNat, Polynomial.map_pow, integralFullSecondJacobi_value, integralU_value]
  rfl

omit [Fact p.Prime] in
theorem actual_log_second_numerator_endpoint_one :
    (actualLogSecondNumerator p).eval 1 = 0 := by
  simp only [actualLogSecondNumerator, eval_sub, eval_mul, eval_ofNat, eval_pow,
    full_second_jacobi_endpoint_one, actual_U_endpoint_one, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, sub_zero]

noncomputable def actualLogSecondNumeratorField (hp : 19 ≤ p) : (ZMod p)[X] :=
  (integralLogSecondNumerator p hp).map (residueHom p)

theorem actual_log_second_numerator_field (hp : 19 ≤ p) :
    actualLogSecondNumeratorField p hp =
      (integralFullSecondJacobi p hp).map (residueHom p) -
        4 * actualRankDividedField p (by omega) ^ 2 := by
  simp only [actualLogSecondNumeratorField, integralLogSecondNumerator,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_pow]
  change _ - 144 * actualUField p (by omega) ^ 2 = _
  rw [actual_U_field]
  have h6 : (6 : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd (by norm_num : 0 < 6)
      ((ZMod.natCast_eq_zero_iff 6 p).mp hz)
    omega
  have hscale : (144 : (ZMod p)[X]) * C (1 / 6 : ZMod p) ^ 2 = 4 := by
    rw [← C_pow, show (144 : (ZMod p)[X]) = C (144 : ZMod p) by rfl, ← C_mul]
    change C ((144 : ZMod p) * (1 / 6) ^ 2) = C (4 : ZMod p)
    congr 1
    field_simp [h6]
    ring
  linear_combination -actualRankDividedField p (by omega) ^ 2 * hscale

/-- The full actual second correction has the IR28 logarithmic normalization,
with its integral cubic error still displayed before any residue extraction. -/
theorem actual_second_correction_log_source (hp : 19 ≤ p) :
    actualSecondCorrection p = 6 * actualU p ^ 2 +
      C (5 / 72 : ℚ) * actualLogSecondNumerator p + C ((p : ℚ) / 4) *
        ((WPMomentPrecision.TwoNodeTaylor.integralNodeShiftErrorPolynomial p hp).comp
          (1 - X ^ 2)).map (integralRationals p).subtype := by
  rw [actualSecondCorrection, actual_first_carry_two_node_source p hp]
  ext n
  simp only [actualLogSecondNumerator, coeff_add, coeff_sub, coeff_C_mul,
    coeff_ofNat_mul]
  ring

/-- The negative resonance is divided in Q before reduction, at the whole actual cutoff. -/
noncomputable def actualNegativeDigit : ℚ :=
  WPMomentPrecision.ResonanceDigits.actualResonanceDigit p (-1)

theorem actual_negative_digit_integral (hp : 19 ≤ p) :
    actualNegativeDigit p ∈ integralRationals p := by
  exact WPMomentPrecision.ResonanceDigits.actual_negative_digit_integral p hp

noncomputable def integralNegativeDigit (hp : 19 ≤ p) : integralRationals p :=
  ⟨actualNegativeDigit p, actual_negative_digit_integral p hp⟩

theorem integralNegativeDigit_value (hp : 19 ≤ p) :
    (integralNegativeDigit p hp).val =
      actualResidue p ((p - 1) / 2) (p - 1 - p / 6) (-1) / (p : ℚ) := rfl

/- The complete source bodies downstream are GreenComplete.lean for the
full finite IR27 identity with its +4 Frobenius term, and
LogQuadraticRepresentation.lean for the IR28 bound natDegree(L2) ≤ 2d and
the actual q representation. Their checked status is determined only by
the root's compilation of the affected cone. OriginalNegativeDigit.lean
and OriginalCentralDigit.lean carry the literal rational lifts through
the original-coordinate residue before dividing by p; actualNegativeDigit
above is an alias of the root's canonical actualResonanceDigit at -1.
The original NC75 y2/P2 source attachment remains open, as specified in
HJetYUAttachment.lean. No z_T^p P2 term or logarithmic cross residue has
been deleted. The full-native IR29 route supplies the subsequent NC77
source without assuming that missing NC75 attachment. -/

end WPMomentPrecision.NativeSecondLift
