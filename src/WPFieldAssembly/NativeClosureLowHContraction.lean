import WPFieldAssembly.NativeClosureLowHSource
import WPFieldAssembly.ActualBpairLowHWholeContraction
import WPFieldAssembly.ActualLowHGaussEndpoint

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.ActualBpairContraction WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.NativeClosureLowH
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

theorem native_cubic_coordinate_map (p : ℕ) [Fact p.Prime] [CharP K p] :
    (WPHasseIntegralTransport.fieldV p).map (ActualThreePhase.φ (K := K) p) =
      (WPFiniteNC122Residue.VP : K[X]) := by
  rw [← ActualLowEuler.Qrev_eq_fieldV p, WPFiniteNC122Residue.Qrev_factored]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat,
    map_inv₀, map_ofNat]
  rw [WPFiniteNC122Residue.VP]
  ring

/-- The own-variable carrier is exactly the native actualLogMinusH polynomial. -/
theorem native_u_actual_variable (p : ℕ) [Fact p.Prime] [CharP K p] :
    actualAK (K := K) p =
      ((ActualNormCrossAttachment.actualLogMinusH p).map (ActualThreePhase.φ p)).comp
        WPFiniteNC122Residue.VP := by
  rw [actualAK, Polynomial.map_comp, native_cubic_coordinate_map]

/-- The whole original native H source contracts with no free native-u hypothesis. -/
theorem native_original_H_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (hη : (5 : K) * η ^ 2 = 1) (h : K) :
    (nativeOriginalHSource p η (nativeH (K := K) p) (literalKB (K := K) p)
      (D (literalKB (K := K) p)) h (WPFiniteNC122.q p)).coeff (-1) =
        (97 / 375 : K) * (WPFiniteNC122.h p : K) ^ 2 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hη' : η ^ 2 = 1 / 5 := by
    apply (eq_div_iff h5).mpr
    simpa only [mul_comm] using hη
  rw [native_original_H_source p hp η hη' _ (nativeH_origin p)]
  rw [native_u_actual_variable]
  rw [lowH_whole_conic_new_kernel_contraction p hp (1 : Kˣ) (Or.inl rfl)
    (lowHConicGermW_first_unit p hp 1 (Or.inl rfl)) η hη
    (nativeH (K := K) p) (nativeH_degree p hp) (nativeH_origin p)]
  have hJ := ActualGaussHarmonic.actual_lowHEulerJ_endpoint_K (K := K) p hp
  change (lowHEulerJ p (nativeH (K := K) p)).eval 1 =
    -(ActualThreePhase.φ p (WPActualGaussBottom.fieldHarmonic p (p / 6))) ^ 2 at hJ
  rw [ActualCubicNativeSource.actual_harmonic_map p hp] at hJ
  rw [hJ]
  ring

/-- The chi0 term uses the pulled-back H origin. -/
theorem native_H_chi0_kernel_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (h : K) :
    (LaurentPolynomial.C (h / 3) * (lowHCubicY (nativeH (K := K) p)).toLaurent *
      D (literalKB (K := K) p)).coeff (-1) =
        (h / 3) * (lowHCubicY (nativeH (K := K) p)).coeff 0 := by
  have he := lowH_original_constant_KB_residue p hp (nativeH (K := K) p)
    (nativeH_degree p hp) (nativeH_origin p) 0 (-h)
  simp only [mul_zero, zero_div, map_zero, zero_mul, zero_sub,
    neg_div, map_neg, neg_neg] at he
  rw [show LaurentPolynomial.C (h / 3) *
      (lowHCubicY (nativeH (K := K) p)).toLaurent * D (literalKB (K := K) p) =
      (lowHCubicY (nativeH (K := K) p)).toLaurent *
        LaurentPolynomial.C (h / 3) * D (literalKB (K := K) p) by ring]
  exact he

/-- Replacing P-u/3 by the actual chi0 P-(u+h)/3 retains its whole origin correction. -/
theorem native_original_chi0_H_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (hη : (5 : K) * η ^ 2 = 1) (h : K) :
    (nativeOriginalHSource p η (nativeH (K := K) p) (literalKB (K := K) p)
      (D (literalKB (K := K) p)) h (WPFiniteNC122.q p) -
      LaurentPolynomial.C (h / 3) * (lowHCubicY (nativeH (K := K) p)).toLaurent *
        D (literalKB (K := K) p)).coeff (-1) =
      (97 / 375 : K) * (WPFiniteNC122.h p : K) ^ 2 -
        (h / 3) * (lowHCubicY (nativeH (K := K) p)).coeff 0 := by
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    native_original_H_contraction p hp η hη h,
    native_H_chi0_kernel_origin p hp h]

end WPFieldAssembly.NativeClosureLowH
