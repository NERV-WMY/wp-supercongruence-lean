import WPFieldAssembly.ActualBpairFiniteKernel
import WPFieldAssembly.ActualBpairLowHIntegralRelations
import WPFieldAssembly.ActualBpairLowHLogBands

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteProductTail WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

theorem lowH_kernelLog_literal (p : ℕ) (c : K) :
    kernelLog p c = (lowHLog p c⁻¹).toLaurent := by
  rw [kernelLog, lowHLog, inv_inv]

private theorem lowH_log_linear_regular (p : ℕ) (R : K[X]) (c : K) :
    ((lowHLog p c).toLaurent * R.toLaurent).coeff (-1) = 0 := by
  exact lowHLogBands_regular p R c

private theorem lowH_log_linear_first (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (c : K) (hc : c ≠ 0) :
    (T (-(p : ℤ)) * (lowHLog p c).toLaurent * R.toLaurent).coeff (-1) =
      -(c⁻¹ ^ p) * (lowHIntegralP p R).eval c := by
  exact lowHLogBands_first p hp R hR c hc

private theorem lowH_log_linear_second (p : ℕ) (hp : 19 ≤ p)
    (R : K[X]) (hR : R.natDegree < p - 1) (c : K) :
    (T (-2 * (p : ℤ)) * (lowHLog p c).toLaurent * R.toLaurent).coeff (-1) = 0 := by
  rw [mul_assoc, ← map_mul]
  have he := WPFiniteJCarrier.shifted_coeff (1 : K) (-2 * (p : ℤ)) (-1)
    (lowHLog p c * R).toLaurent
  simp only [map_one, one_mul] at he
  rw [he, show (-1 : ℤ) - -2 * (p : ℤ) = ((2 * p - 1 : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat]
  exact lowH_log_product_upper_zero p hp R hR c _ (by omega)

/-- All three bands of the original literal kernel are paired before the two endpoint integrals. -/
theorem lowH_literalKB_density_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) :
    (literalKB (K := K) p * R.toLaurent).coeff (-1) =
      -(23 / 6 : K) * (lowHIntegralP p R).eval 4 +
        (29 / 6 : K) * (lowHIntegralP p R).eval (1 / 4) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have ha : kernelLog p (1 / 4 : K) = (lowHLog p 4).toLaurent := by
    rw [lowH_kernelLog_literal, one_div, inv_inv]
  have hb : kernelLog p (4 : K) = (lowHLog p (1 / 4)).toLaurent := by
    rw [lowH_kernelLog_literal, one_div]
  rw [show literalKB (K := K) p * R.toLaurent =
      LaurentPolynomial.C (1 / 6 : K) *
        (LaurentPolynomial.C (35 : K) * ((lowHLog p 4).toLaurent * R.toLaurent) +
          LaurentPolynomial.C (23 * 4 : K) *
            (T (-(p : ℤ)) * (lowHLog p 4).toLaurent * R.toLaurent) +
          LaurentPolynomial.C (23 * 4 ^ 2 : K) *
            (T (-2 * (p : ℤ)) * (lowHLog p 4).toLaurent * R.toLaurent) -
          LaurentPolynomial.C (5 : K) * ((lowHLog p (1 / 4)).toLaurent * R.toLaurent) -
          LaurentPolynomial.C (29 * (1 / 4) : K) *
            (T (-(p : ℤ)) * (lowHLog p (1 / 4)).toLaurent * R.toLaurent) -
          LaurentPolynomial.C (29 * (1 / 4) ^ 2 : K) *
            (T (-2 * (p : ℤ)) * (lowHLog p (1 / 4)).toLaurent * R.toLaurent)) by
    rw [literalKB, ha, hb]
    ring]
  simp only [C_mul_coeff, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply,
    lowH_log_linear_regular, lowH_log_linear_second p hp R hR,
    lowH_log_linear_first p hp R hR 4 h4,
    lowH_log_linear_first p hp R hR (4 : K)⁻¹ (inv_ne_zero h4),
    inv_pow, one_div, inv_inv, h4p, mul_zero, zero_add, add_zero, sub_zero]
  field_simp [h2, h3, h4]
  ring

/-- The entire original K_B*y*l term is the same unevaluated origin correction at both ends. -/
theorem lowH_literalKB_cubic_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p)
    (H : K[X]) (hH : H.natDegree ≤ d) (h0 : H.coeff 0 = 0) :
    (literalKB (K := K) p * (lowHqCubicDensity H).toLaurent).coeff (-1) =
      -(lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval 0) := by
  have hR : (lowHqCubicDensity H).natDegree < p - 1 := by
    have he := lowHqCubicDensity_degree d hd H hH
    omega
  have he := lowHqCubicDensity_both_end_integrals p hp d hd hband H hH h0
  rw [lowH_literalKB_density_residue p hp _ hR, he.1, he.2]
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h6]
  ring

theorem lowH_literalKB_scaled_cubic_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p)
    (H : K[X]) (hH : H.natDegree ≤ d) (h0 : H.coeff 0 = 0) :
    (LaurentPolynomial.C (-5 / 6 : K) *
      (literalKB (K := K) p * (lowHqCubicDensity H).toLaurent)).coeff (-1) =
      (5 / 6 : K) * (lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval 0) := by
  rw [C_mul_coeff, lowH_literalKB_cubic_log_residue p hp d hd hband H hH h0]
  ring

end WPFieldAssembly.ActualBpairContraction
