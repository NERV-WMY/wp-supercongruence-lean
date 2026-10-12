import WPFieldAssembly.ActualBpairLowHGreen
import WPFieldAssembly.GreenLaurentOperators

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

theorem lowHLogBands_regular (p : ℕ) (R : K[X]) (c : K) :
    ((lowHLog p c).toLaurent * R.toLaurent).coeff (-1) = 0 := by
  rw [← map_mul]
  exact WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))

/-- The complete negative Frobenius phase uses the checked p-1 coefficient, including R(0). -/
theorem lowHLogBands_first (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (c : K) (hc : c ≠ 0) :
    (T (-(p : ℤ)) * (lowHLog p c).toLaurent * R.toLaurent).coeff (-1) =
      -(c⁻¹ ^ p) * (lowHIntegralP p R).eval c := by
  rw [mul_assoc, ← map_mul]
  have he := WPFiniteJCarrier.shifted_coeff (1 : K) (-(p : ℤ)) (-1)
    (lowHLog p c * R).toLaurent
  simp only [map_one, one_mul] at he
  rw [he, show (-1 : ℤ) - -(p : ℤ) = ((p - 1 : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat, lowH_log_green_coefficient p hp R hR c hc]

/-- Both original origin-simple-pole log sources vanish by their literal indices 0 and p. -/
theorem lowHLogBands_origin_two_sources (p : ℕ) (hp : 1 ≤ p) (c : K) :
    (T (-1) * (lowHLog p c).toLaurent).coeff (-1) = 0 ∧
      (T (-(p : ℤ)) * T (-1) * (lowHLog p c).toLaurent).coeff (-1) = 0 := by
  have h0 := WPFiniteJCarrier.shifted_coeff (1 : K) (-1) (-1) (lowHLog p c).toLaurent
  have h1 := WPFiniteJCarrier.shifted_coeff (1 : K) (-(p : ℤ) - 1) (-1) (lowHLog p c).toLaurent
  simp only [map_one, one_mul] at h0 h1
  constructor
  · rw [h0, show (-1 : ℤ) - -1 = 0 by omega]
    simpa only [Nat.cast_zero, lowHLog_zero] using
      (WPFiniteJCarrier.toLaurent_coeff_nat (lowHLog p c) 0)
  · rw [← T_add, show -(p : ℤ) + -1 = -(p : ℤ) - 1 by omega, h1,
      show (-1 : ℤ) - (-(p : ℤ) - 1) = (p : ℤ) by omega,
      WPFiniteJCarrier.toLaurent_coeff_nat]
    exact coeff_eq_zero_of_natDegree_lt ((lowHLog_degree p c).trans_lt (by omega))

/-- The literal two-end log difference retains its complete origin-simple-pole subtraction. -/
theorem lowHLogBands_difference_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (α β r0 : K) :
    ((LaurentPolynomial.C α + LaurentPolynomial.C β * T (-(p : ℤ))) *
      ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
      (R.toLaurent - LaurentPolynomial.C r0 * T (-1))).coeff (-1) =
      β * (-(1 / 4 : K) * (lowHIntegralP p R).eval 4 +
        4 * (lowHIntegralP p R).eval (1 / 4)) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have ha := lowHLogBands_first p hp R hR (4 : K) h4
  have hb := lowHLogBands_first p hp R hR (1 / 4) (one_div_ne_zero h4)
  rw [inv_pow, h4p] at ha
  rw [one_div, inv_inv, h4p] at hb
  have hzA := lowHLogBands_origin_two_sources (K := K) p (by omega) (4 : K)
  have hzB := lowHLogBands_origin_two_sources (K := K) p (by omega) (1 / 4 : K)
  simp only [one_div] at hzB
  rw [show (LaurentPolynomial.C α + LaurentPolynomial.C β * T (-(p : ℤ))) *
      ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
      (R.toLaurent - LaurentPolynomial.C r0 * T (-1)) =
      LaurentPolynomial.C α *
        (((lowHLog p 4).toLaurent * R.toLaurent) -
          ((lowHLog p (1 / 4)).toLaurent * R.toLaurent)) +
      LaurentPolynomial.C β *
        ((T (-(p : ℤ)) * (lowHLog p 4).toLaurent * R.toLaurent) -
          (T (-(p : ℤ)) * (lowHLog p (1 / 4)).toLaurent * R.toLaurent)) -
      LaurentPolynomial.C (α * r0) *
        (T (-1) * (lowHLog p 4).toLaurent - T (-1) * (lowHLog p (1 / 4)).toLaurent) -
      LaurentPolynomial.C (β * r0) *
        (T (-(p : ℤ)) * T (-1) * (lowHLog p 4).toLaurent -
          T (-(p : ℤ)) * T (-1) * (lowHLog p (1 / 4)).toLaurent) by rw [map_mul, map_mul]; ring]
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply, C_mul_coeff,
    lowHLogBands_regular, ha, hb, hzA.1, hzA.2, hzB.1, hzB.2,
    sub_self, mul_zero, zero_add, one_div]
  ring

/-- The whole phi-weighted two-end source contracts to its genuine endpoint difference. -/
theorem lowHLogBands_phi_pair (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) :
    ((4 * T (-(p : ℤ)) - 11) *
      (4 * (lowHLog p 4).toLaurent - LaurentPolynomial.C (1 / 4 : K) *
        (lowHLog p (1 / 4)).toLaurent) * R.toLaurent).coeff (-1) =
      -4 * ((lowHIntegralP p R).eval 4 - (lowHIntegralP p R).eval (1 / 4)) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have ha := lowHLogBands_first p hp R hR (4 : K) h4
  have hb := lowHLogBands_first p hp R hR (1 / 4) (one_div_ne_zero h4)
  rw [inv_pow, h4p] at ha
  rw [one_div, inv_inv, h4p] at hb
  rw [show (4 * T (-(p : ℤ)) - 11) *
      (4 * (lowHLog p 4).toLaurent - LaurentPolynomial.C (1 / 4 : K) *
        (lowHLog p (1 / 4)).toLaurent) * R.toLaurent =
      LaurentPolynomial.C (4 : K) *
        (LaurentPolynomial.C (4 : K) *
            (T (-(p : ℤ)) * (lowHLog p 4).toLaurent * R.toLaurent) -
          LaurentPolynomial.C (1 / 4 : K) *
            (T (-(p : ℤ)) * (lowHLog p (1 / 4)).toLaurent * R.toLaurent)) -
      LaurentPolynomial.C (11 : K) *
        (LaurentPolynomial.C (4 : K) * ((lowHLog p 4).toLaurent * R.toLaurent) -
          LaurentPolynomial.C (1 / 4 : K) * ((lowHLog p (1 / 4)).toLaurent * R.toLaurent)) by
    simp only [map_ofNat]
    ring]
  simp only [one_div, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, C_mul_coeff,
    lowHLogBands_regular, ha, hb, mul_zero, sub_self, sub_zero]
  field_simp [h4]
  ring

end WPFieldAssembly.ActualBpairContraction
