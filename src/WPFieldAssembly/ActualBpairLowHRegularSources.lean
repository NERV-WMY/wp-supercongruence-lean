import WPFieldAssembly.ActualBpairLowHBranchTail
import WPFieldAssembly.ActualBpairLowHQuadratic

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/- STATEMENT_FIDELITY: These are the full regular u_c/v_c/c/h groups of IR71d
after its stated affine sources, for p >= 19 and degree H <= floor(p/6).
The original kappa, q2 and h stay independent literal parameters until the
root-owned actual-u attachment. Both Frobenius directions and G*X=1 remain.
There is no generated data, CM scalar premise, kernel replacement or G2 claim. -/

theorem lowH_regular_D_density_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    (lowHCubicY H * (Dstar p).derivative).natDegree < p - 1 := by
  have hY := lowHCubicY_degree (p / 6) H hH
  have hD := Dstar_degree (K := K) p hp
  have hN : 2 * ((p - 1) / 2) + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> omega
  have hs := lowH_prime_six_band p hp
  have hd := natDegree_derivative_le (Dstar p : K[X])
  have hm := natDegree_mul_le (p := lowHCubicY H) (q := (Dstar p : K[X]).derivative)
  omega

theorem lowH_regular_branch_density_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    (lowHBranchYQuotient H).natDegree < p - 1 := by
  have hs := lowH_prime_six_band p hp
  have hQ := lowHBranchYQuotient_degree (p / 6) (by omega) H hH
  omega

/-- All four bilinear phases are retained; the origin phase G*X is cancelled only as a whole. -/
theorem lowH_regular_phase_pair_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (α β γ δ : K) :
    ((LaurentPolynomial.C α + LaurentPolynomial.C β * T (p : ℤ)) *
      (LaurentPolynomial.C γ + LaurentPolynomial.C δ * T (-(p : ℤ))) * R.toLaurent).coeff (-1) = 0 := by
  have hG := lowH_subp_frobenius_phase_zero p hp R hR (1 : ℤ)
  have hX := lowH_subp_frobenius_phase_zero p hp R hR (-1 : ℤ)
  have h0 := lowH_subp_frobenius_phase_zero p hp R hR (0 : ℤ)
  simp only [one_mul, neg_mul, zero_mul, T_zero] at hG hX h0
  have hGX : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  rw [show (LaurentPolynomial.C α + LaurentPolynomial.C β * T (p : ℤ)) *
      (LaurentPolynomial.C γ + LaurentPolynomial.C δ * T (-(p : ℤ))) * R.toLaurent =
      LaurentPolynomial.C (α * γ + β * δ) * R.toLaurent +
      LaurentPolynomial.C (β * γ) * (T (p : ℤ) * R.toLaurent) +
      LaurentPolynomial.C (α * δ) * (T (-(p : ℤ)) * R.toLaurent) by
    simp only [map_add, map_mul]
    linear_combination LaurentPolynomial.C β * LaurentPolynomial.C δ * R.toLaurent * hGX]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, C_mul_coeff,
    h0, hG, hX, mul_zero, zero_add]

/-- The full constant portion of (2phi/15)(u+h-3Bp*w/5)dD has zero residue. -/
theorem lowH_original_constant_D_source_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (κ h q2 : K) :
    (LaurentPolynomial.C (2 / 15 : K) *
      (LaurentPolynomial.C (4 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (11 : K)) *
      (LaurentPolynomial.C (κ + h) - LaurentPolynomial.C (4 * q2 / 5) * T (p : ℤ)) *
      (lowHCubicY H * (Dstar p).derivative).toLaurent).coeff (-1) = 0 := by
  have he := lowH_regular_phase_pair_zero p hp _ (lowH_regular_D_density_degree p hp H hH)
    (κ + h) (-(4 * q2 / 5)) (-11) 4
  have hr : LaurentPolynomial.C (2 / 15 : K) *
      (LaurentPolynomial.C (4 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (11 : K)) *
      (LaurentPolynomial.C (κ + h) - LaurentPolynomial.C (4 * q2 / 5) * T (p : ℤ)) *
      (lowHCubicY H * (Dstar p).derivative).toLaurent =
      LaurentPolynomial.C (2 / 15 : K) *
        ((LaurentPolynomial.C (κ + h) + LaurentPolynomial.C (-(4 * q2 / 5)) * T (p : ℤ)) *
          (LaurentPolynomial.C (-11 : K) + LaurentPolynomial.C (4 : K) * T (-(p : ℤ))) *
          (lowHCubicY H * (Dstar p).derivative).toLaurent) := by
    simp only [map_neg, map_ofNat]
    ring
  rw [hr, C_mul_coeff, he, mul_zero]

/-- The entire original c/h regular source keeps u_c and v_c and both reciprocal phases. -/
theorem lowH_original_constant_regular_source_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (κ h q2 : K) :
    ((-LaurentPolynomial.C (5 / 3 : K) *
        (LaurentPolynomial.C (κ - q2 + h) - LaurentPolynomial.C (4 * q2 / 5) * T (-(p : ℤ))) -
      LaurentPolynomial.C (1 / 3 : K) *
        (LaurentPolynomial.C (4 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (11 : K)) *
        (LaurentPolynomial.C (κ + h) - LaurentPolynomial.C (4 * q2 / 5) * T (p : ℤ))) *
      (lowHBranchYQuotient H).toLaurent).coeff (-1) = 0 := by
  have hQ := lowH_regular_branch_density_degree p hp H hH
  have ha := lowH_regular_phase_pair_zero p hp (lowHBranchYQuotient H) hQ
    (1 : K) 0 (κ - q2 + h) (-(4 * q2 / 5))
  simp only [map_one, map_zero, zero_mul, add_zero, one_mul, map_neg] at ha
  rw [neg_mul, ← sub_eq_add_neg] at ha
  have hb := lowH_regular_phase_pair_zero p hp (lowHBranchYQuotient H) hQ
    (κ + h) (-(4 * q2 / 5)) (-11) 4
  have hr : (-LaurentPolynomial.C (5 / 3 : K) *
        (LaurentPolynomial.C (κ - q2 + h) - LaurentPolynomial.C (4 * q2 / 5) * T (-(p : ℤ))) -
      LaurentPolynomial.C (1 / 3 : K) *
        (LaurentPolynomial.C (4 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (11 : K)) *
        (LaurentPolynomial.C (κ + h) - LaurentPolynomial.C (4 * q2 / 5) * T (p : ℤ))) *
      (lowHBranchYQuotient H).toLaurent =
      LaurentPolynomial.C (-(5 / 3 : K)) *
        ((LaurentPolynomial.C (κ - q2 + h) - LaurentPolynomial.C (4 * q2 / 5) * T (-(p : ℤ))) *
          (lowHBranchYQuotient H).toLaurent) -
      LaurentPolynomial.C (1 / 3 : K) *
        ((LaurentPolynomial.C (κ + h) + LaurentPolynomial.C (-(4 * q2 / 5)) * T (p : ℤ)) *
          (LaurentPolynomial.C (-11 : K) + LaurentPolynomial.C (4 : K) * T (-(p : ℤ))) *
          (lowHBranchYQuotient H).toLaurent) := by
    simp only [map_neg, map_ofNat]
    ring
  rw [hr]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, C_mul_coeff,
    ha, hb, mul_zero, sub_self]

/-- The original own-variable term is polynomial before its positive G phase is selected. -/
theorem lowH_original_own_variable_source_zero (p : ℕ) (H U : K[X]) :
    (LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) *
      (U.comp WPFiniteNC122Residue.VP).toLaurent * (lowHqCubicDensity H).toLaurent).coeff (-1) = 0 := by
  rw [show LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) *
      (U.comp WPFiniteNC122Residue.VP).toLaurent * (lowHqCubicDensity H).toLaurent =
      LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) *
        ((U.comp WPFiniteNC122Residue.VP) * lowHqCubicDensity H).toLaurent by rw [map_mul]; ring]
  have he := WPFiniteJCarrier.shifted_coeff (5 / 24 : K) (p : ℤ) (-1)
    ((U.comp WPFiniteNC122Residue.VP) * lowHqCubicDensity H).toLaurent
  rw [he, WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega)), mul_zero]

end WPFieldAssembly.ActualBpairContraction
