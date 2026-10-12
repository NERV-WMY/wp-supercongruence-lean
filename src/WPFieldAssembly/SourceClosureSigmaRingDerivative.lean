import WPFiniteLaurentDifferential
import WPActualChiSource

open scoped LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.SourceClosureSigmaActualVS

set_option maxHeartbeats 1500000

/-- The same finite derivative is defined over the actual integral coefficient ring. -/
noncomputable def ringD {R : Type*} [CommRing R] : R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] :=
  (Finsupp.linearCombination R (fun n : ℤ => LaurentPolynomial.C (n : R) * T (n - 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem ringD_monomial {R : Type*} [CommRing R] (a : R) (n : ℤ) :
    ringD (LaurentPolynomial.C a * T n) = LaurentPolynomial.C (a * (n : R)) * T (n - 1) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination R _ (Finsupp.single n a) = _
  rw [Finsupp.linearCombination_single, smul_eq_C_mul, ← mul_assoc, ← _root_.map_mul]

theorem ringD_coefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : R[T;T⁻¹]) :
    WPActualChiSource.coefficientMap f (ringD F) =
      ringD (WPActualChiSource.coefficientMap f F) := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG => simp only [_root_.map_add, hF, hG]
  | C_mul_T n a =>
    rw [ringD_monomial, WPActualChiSource.coefficientMap_monomial,
      WPActualChiSource.coefficientMap_monomial, ringD_monomial,
      _root_.map_mul, _root_.map_intCast]

theorem ringD_field {K : Type*} [Field K] (F : K[T;T⁻¹]) : ringD F = D F := rfl

theorem D_coefficientMap {R S : Type*} [Field R] [Field S]
    (f : R →+* S) (F : R[T;T⁻¹]) :
    WPActualChiSource.coefficientMap f (D F) = D (WPActualChiSource.coefficientMap f F) := by
  ext j
  rw [WPActualChiSource.coefficientMap_coeff, D_coeff, D_coeff,
    WPActualChiSource.coefficientMap_coeff, _root_.map_mul, _root_.map_intCast]

theorem invert_coefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : R[T;T⁻¹]) :
    WPActualChiSource.coefficientMap f (invert F) = invert (WPActualChiSource.coefficientMap f F) :=
  WPActualChiSource.coefficientMap_invert f F

end WPFieldAssembly.SourceClosureSigmaActualVS
