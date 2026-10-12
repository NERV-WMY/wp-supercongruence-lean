import WPFieldAssembly.ActualBpairLowHWholeAlgebra
import WPFieldAssembly.ActualBpairLowHLogCollection
import WPFieldAssembly.ActualBpairLowHConicJs

open scoped Polynomial LaurentPolynomial LaurentSeries PowerSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/- STATEMENT_FIDELITY: This collects the entire literal IR71d source after
the displayed IR70 affine u/v identities, for every p >= 19, degree H <= p/6
and H(0)=0. KB is the original literalKB and DK its actual derivative. Both
proper ends, all Frobenius bands, both auxiliary integrals and all origin
terms are kept until their proved cancellation. The conic form uses either
actual inverse germ and 5*eta^2=1; the own-variable term is an arbitrary
polynomial U(V). Root owns the original native-u/IR71c attachment and the
actual Gauss value J_H(1)=-h^2, neither of which is asserted here. -/

/-- The actual cubic kernel keeps its D-origin, scalar-origin and complete log portions. -/
theorem lowH_whole_cubic_kernel_parts (p : ℕ) (H : K[X]) (κ q2 : K) :
    lowHWholeCubicKernelSource p H (literalKB (K := K) p)
        (D (literalKB (K := K) p)) κ q2 =
      (lowHCubicY H).toLaurent *
        (LaurentPolynomial.C (4 / 5 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (6 / 5 : K)) *
        (Dstar p).toLaurent * D (literalKB (K := K) p) +
      (lowHCubicY H).toLaurent *
        (LaurentPolynomial.C (4 * q2 / 15 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (κ / 3)) *
        D (literalKB (K := K) p) +
      LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
        (lowHCubicY H).toLaurent * D (literalKB (K := K) p) +
      LaurentPolynomial.C (-5 / 6 : K) *
        (literalKB (K := K) p * (lowHqCubicDensity H).toLaurent) := by
  simp only [lowHWholeCubicKernelSource, lowHWholeCslot, div_eq_mul_inv,
    map_mul, map_ofNat, map_one, map_neg]
  ring

/-- Both auxiliary primitives cancel in the full cubic and remaining log source. -/
theorem lowH_whole_cubic_and_remaining_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) (κ q2 : K) :
    (lowHWholeCubicKernelSource p H (literalKB (K := K) p)
        (D (literalKB (K := K) p)) κ q2 +
      lowHRemainingLogDensity p (lowHCubicY H * (Dstar p).derivative)
        (lowHJQDensity H) (lowHBranchYQuotient H) ((lowHCubicY H).coeff 0)).coeff (-1) =
      (3 / 10 : K) * (lowHCubicY H).coeff 0 * (Dstar p : K[X]).coeff 0 +
      (q2 / 2 - κ / 3) * (lowHCubicY H).coeff 0 +
      (8 / 75 : K) * (lowHEulerJ p H).eval 1 := by
  rw [lowH_whole_cubic_kernel_parts]
  rw [show
      (lowHCubicY H).toLaurent *
          (LaurentPolynomial.C (4 / 5 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (6 / 5 : K)) *
          (Dstar p).toLaurent * D (literalKB (K := K) p) +
        (lowHCubicY H).toLaurent *
          (LaurentPolynomial.C (4 * q2 / 15 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (κ / 3)) *
          D (literalKB (K := K) p) +
        LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
          ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
          (lowHCubicY H).toLaurent * D (literalKB (K := K) p) +
        LaurentPolynomial.C (-5 / 6 : K) *
          (literalKB (K := K) p * (lowHqCubicDensity H).toLaurent) +
        lowHRemainingLogDensity p (lowHCubicY H * (Dstar p).derivative)
          (lowHJQDensity H) (lowHBranchYQuotient H) ((lowHCubicY H).coeff 0) =
      (lowHCubicY H).toLaurent *
          (LaurentPolynomial.C (4 / 5 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (6 / 5 : K)) *
          (Dstar p).toLaurent * D (literalKB (K := K) p) +
        (lowHCubicY H).toLaurent *
          (LaurentPolynomial.C (4 * q2 / 15 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (κ / 3)) *
          D (literalKB (K := K) p) +
        (LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
          ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
          (lowHCubicY H).toLaurent * D (literalKB (K := K) p) +
        LaurentPolynomial.C (-5 / 6 : K) *
          (literalKB (K := K) p * (lowHqCubicDensity H).toLaurent) +
        lowHRemainingLogDensity p (lowHCubicY H * (Dstar p).derivative)
          (lowHJQDensity H) (lowHBranchYQuotient H) ((lowHCubicY H).coeff 0)) by ring]
  have hl := lowH_original_whole_log_residue p hp H hH h0
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hl ⊢
  rw [lowH_original_D_KB_residue p hp H hH h0,
    lowH_original_constant_KB_residue p hp H hH h0,
    hl]

/-- The complete original kernel cancels both origin slots and the whole J0 functional. -/
theorem lowH_whole_original_kernel_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0)
    (κ h q2 : K) :
    (lowHWholeOriginalKernelSource p H (literalKB (K := K) p)
      (D (literalKB (K := K) p)) κ h q2).coeff (-1) =
      (8 / 75 : K) * (lowHEulerJ p H).eval 1 + (137 / 5 : K) * lowHBranchJs p H := by
  rw [lowH_whole_original_kernel_decomposition p hp H h0]
  have hc := lowH_whole_cubic_and_remaining_log_residue p hp H hH h0 κ q2
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hc ⊢
  rw [lowH_original_D_linear_residue p hp H hH]
  change _ + _ + _ + (lowHWholeQuadraticSource p H).coeff (-1) +
      (lowHWholeRegularDSource p H κ h q2).coeff (-1) +
      (lowHWholeRegularRSource p H κ h q2).coeff (-1) +
      (lowHOriginalQLogConstantSource p H κ q2).coeff (-1) = _
  have hD : (lowHWholeRegularDSource p H κ h q2).coeff (-1) = 0 := by
    simpa only [lowHWholeRegularDSource, map_ofNat] using
      lowH_original_constant_D_source_zero p hp H hH κ h q2
  have hR : (lowHWholeRegularRSource p H κ h q2).coeff (-1) = 0 := by
    simpa only [lowHWholeRegularRSource, map_ofNat] using
      lowH_original_constant_regular_source_zero p hp H hH κ h q2
  rw [lowHWholeQuadraticSource, lowH_original_quadratic_residue p hp H hH h0, hD, hR,
    lowH_original_qlog_constant_residue p hp H hH]
  linear_combination hc

/-- The whole conic contraction derives its coefficient from both genuine finite sources. -/
theorem lowH_whole_conic_kernel_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1)
    (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) (κ h q2 : K) :
    (lowHWholeOriginalKernelSource p H (literalKB (K := K) p)
      (D (literalKB (K := K) p)) κ h q2).coeff (-1) =
      -(97 / 375 : K) * (lowHEulerJ p H).eval 1 := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h75 : (75 : K) ≠ 0 := by
    convert mul_ne_zero h3 (pow_ne_zero 2 h5) using 1; norm_num
  have h375 : (375 : K) ≠ 0 := by
    convert mul_ne_zero h3 (pow_ne_zero 3 h5) using 1; norm_num
  rw [lowH_whole_original_kernel_residue p hp H hH h0,
    lowHBranchJs_conic_contraction p hp ε hε hu η hη H hH]
  field_simp [h3, h5, h75, h375]
  ring

/-- The original own-variable term is retained and proved regular before the final contraction. -/
theorem lowH_whole_conic_new_kernel_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1)
    (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) (κ h q2 : K) (U : K[X]) :
    (lowHWholeOriginalKernelSource p H (literalKB (K := K) p)
        (D (literalKB (K := K) p)) κ h q2 +
      LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) *
        (U.comp WPFiniteNC122Residue.VP).toLaurent * (lowHqCubicDensity H).toLaurent).coeff (-1) =
      -(97 / 375 : K) * (lowHEulerJ p H).eval 1 := by
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  rw [lowH_whole_conic_kernel_contraction p hp ε hε hu η hη H hH h0,
    lowH_original_own_variable_source_zero, add_zero]

end WPFieldAssembly.ActualBpairContraction
