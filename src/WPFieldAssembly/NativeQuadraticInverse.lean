import WPFieldAssembly.NativePrecisionTwo
import Mathlib.Algebra.Polynomial.Expand

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualNativeFirstIntegral
  WPFieldAssembly.TerminatingSquare WPFieldAssembly.NativeDiscriminant
  WPFieldAssembly.NativePrecision WPFieldAssembly.NativePrecisionTwo

namespace WPFieldAssembly.NativeQuadraticInverse

set_option maxHeartbeats 800000

/-- The inverse on the whole quadratic pullback uses no division of coefficients. -/
noncomputable def quadraticInverse {R : Type*} [CommRing R] (P : R[X]) : R[X] :=
  (contract 2 P).comp (1 - X)

theorem contract_quadratic {R : Type*} [CommRing R] (H : R[X]) :
    contract 2 (H.comp (1 - X ^ 2)) = H.comp (1 - X) := by
  have he : H.comp (1 - X ^ 2) = expand R 2 (H.comp (1 - X)) := by
    rw [expand_eq_comp_X_pow, comp_assoc]
    simp only [sub_comp, one_comp, X_comp]
  rw [he, contract_expand 2 (by norm_num : (2 : ℕ) ≠ 0)]

theorem quadraticInverse_quadratic {R : Type*} [CommRing R] (H : R[X]) :
    quadraticInverse (H.comp (1 - X ^ 2)) = H := by
  rw [quadraticInverse, contract_quadratic, comp_assoc]
  simp only [sub_comp, one_comp, X_comp, sub_sub_cancel, comp_X]

theorem quadraticInverse_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : R[X]) :
    (quadraticInverse P).map f = quadraticInverse (P.map f) := by
  rw [quadraticInverse, Polynomial.map_comp, map_contract (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, quadraticInverse]

noncomputable def nativeH (p : ℕ) : ℚ[X] :=
  C (1 / 2 : ℚ) * X * nativeDiscriminant (WPReview.nativePolynomial ((p - 1) / 2 + 1))

theorem weightedNativeDiscriminant_eq_nativeH_quadratic (p : ℕ) :
    weightedNativeDiscriminant p = (nativeH p).comp (1 - X ^ 2) := by
  have he := (native_discriminant_quadratic
    (WPReview.nativePolynomial ((p - 1) / 2 + 1))).symm
  change (1 - X ^ 2) * jacobiDiscriminant 0 (halfNativeJacobi p) = _
  simp only [nativeH, mul_comp, C_comp, X_comp]
  change _ = C (1 / 2 : ℚ) * (1 - X ^ 2) *
    (nativeDiscriminant (WPReview.nativePolynomial ((p - 1) / 2 + 1))).comp (1 - X ^ 2)
  change (nativeDiscriminant (WPReview.nativePolynomial ((p - 1) / 2 + 1))).comp
      (1 - X ^ 2) = 2 * jacobiDiscriminant 0 (halfNativeJacobi p) at he
  rw [he]
  have hhalf : (2 : ℚ[X]) * C (1 / 2 : ℚ) = 1 := by
    change C (2 : ℚ) * C (1 / 2 : ℚ) = C (1 : ℚ)
    rw [← C_mul]
    norm_num
  linear_combination -(1 - X ^ 2) * jacobiDiscriminant 0 (halfNativeJacobi p) * hhalf

/-- All native coefficients retain p² precision under the integral quadratic inverse. -/
theorem actual_nativeH_divided_two_witness (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ∃ Q : (integralRationals p)[X],
      Q.map (integralRationals p).subtype = C (1 / (p : ℚ) ^ 2) * nativeH p := by
  obtain ⟨Q, hQ⟩ := actual_native_discriminant_divided_two_witness p hp
  have hs : C (1 / (p : ℚ) ^ 2) * weightedNativeDiscriminant p =
      (C (1 / (p : ℚ) ^ 2) * nativeH p).comp (1 - X ^ 2) := by
    rw [weightedNativeDiscriminant_eq_nativeH_quadratic, mul_comp, C_comp]
  refine ⟨quadraticInverse Q, ?_⟩
  rw [quadraticInverse_map, hQ, hs, quadraticInverse_quadratic]

theorem actual_nativeH_divided_two_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℕ) :
    0 ≤ padicValRat p ((C (1 / (p : ℚ) ^ 2) * nativeH p).coeff n) := by
  obtain ⟨Q, hQ⟩ := actual_nativeH_divided_two_witness p hp
  rw [← hQ, coeff_map]
  exact (Q.coeff n).property

end WPFieldAssembly.NativeQuadraticInverse
