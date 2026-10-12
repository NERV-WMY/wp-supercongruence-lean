import WPFieldAssembly.NativeEulerPrimitive
import WPActualEtaIntegrality

open scoped BigOperators Polynomial
open Polynomial WPActualNativeHasse WPActualEtaIntegrality WPActualPullbackSource
  WPPIntegralReduction

namespace WPFieldAssembly.NativeEulerPrimitive

theorem nativeHField_literal_coefficient (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (hn : n ≤ p / 6) :
    (nativeHField p).coeff n = (WPReview.nativeCoefficient n / (n : ℚ) : ℚ) := by
  rw [nativeHField_coeff, if_pos hn]
  by_cases hn0 : n = 0
  · subst n; simp
  have hden := integral_denominator_cast_ne_zero p _
    (actual_native_coefficient_integral p n hp (by omega))
  have hnu : (n : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p n (by omega) (by omega)
  have hnum : (((n : ℚ).num : ℤ) : ZMod p) ≠ 0 := by simpa using hnu
  rw [Rat.cast_div_of_ne_zero hden hnum]
  simp

/-- The retained rational Euler primitive, lifted before reduction. -/
noncomputable def nativeHIntegral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  ∑ n : Fin (p / 6 + 1), monomial n.val
    ⟨WPReview.nativeCoefficient n.val / (n.val : ℚ),
      native_Hcoefficient_integral p n.val hp (by have hn := n.isLt; omega)⟩

theorem nativeHIntegral_map_rational (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (nativeHIntegral p hp).map (integralRationals p).subtype = Hpolynomial (p / 6) := by
  simp only [nativeHIntegral, Polynomial.map_sum, map_monomial, Subring.coe_subtype]
  exact Fin.sum_univ_eq_sum_range
    (fun n => monomial n (WPReview.nativeCoefficient n / (n : ℚ))) (p / 6 + 1)

theorem nativeHIntegral_map_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (nativeHIntegral p hp).map (residueHom p) = nativeHField p := by
  ext n
  rw [coeff_map]
  change (((nativeHIntegral p hp).coeff n).val : ZMod p) = _
  have he := congrArg (fun P : ℚ[X] => P.coeff n) (nativeHIntegral_map_rational p hp)
  rw [coeff_map] at he
  change ((nativeHIntegral p hp).coeff n).val = (Hpolynomial (p / 6)).coeff n at he
  rw [he, Hpolynomial_coeff]
  by_cases hn : n < p / 6 + 1
  · rw [if_pos hn]
    exact (nativeHField_literal_coefficient p n hp (by omega)).symm
  · rw [if_neg hn, nativeHField_coeff, if_neg (by omega)]
    simp

end WPFieldAssembly.NativeEulerPrimitive
