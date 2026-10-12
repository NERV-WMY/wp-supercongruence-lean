import WPActualFirstAngularEndpoint
import WPActualFirstConductorRows
import WPFiniteFirstConductorKernel

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

def firstConductorDivisor : RatFunc ℚ :=
  symbol^4*(25-9*symbol)*(99*symbol-50)^2

theorem actual_first_conductor_divisor : RatFunc.C firstConductorDivisor=bivSourceDivisor := by
  norm_num [firstConductorDivisor, bivSourceDivisor, bivCollision, bivEscape, bivX,
    map_mul, map_sub, map_pow, _root_.map_ofNat]

theorem actual_first_conductor_quadratic :
    algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
      (finiteQuadraticPolynomial firstConductorMean lambda)=bivConductor := by
  norm_num [finiteQuadraticPolynomial, firstConductorMean, bivConductor,
    bivMean, bivLam, lambda, bivX, bivS, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, map_mul, map_pow, map_sub, map_add, map_div₀,
    _root_.map_ofNat]

theorem actual_first_source_divisor_ne_zero : bivSourceDivisor≠0 := by
  have hM : bivCollision≠0 := by
    rw [bivCollision, show 25-9*bivX=-(9*bivX-25) by ring]
    exact neg_ne_zero.mpr biv_collision_ne_zero
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ bivX_ne_zero) hM)
    (pow_ne_zero _ biv_escape_ne_zero)

def actualFirstConductorKernel (p n : ℕ) : RatFunc ℚ :=
  (2/firstConductorDivisor)*firstQuadraticKernel p n firstConductorMean
    firstConductorNumeratorZero firstConductorNumeratorOne

/-- The actual complete BU contribution is a finite sum over the literal native coefficients. -/
theorem actual_first_conductor_error_finite (p : ℕ) :
    actualFirstConductorError p =
      ∑ n ∈ Finset.range p, RatFunc.C (WPReview.nativeCoefficient n)*actualFirstConductorKernel p n := by
  have hrow : (∑ j : Fin 3, bivConductorBU 2 j*finiteNativeJet p bivB j) =
      (1-bivS)*bivBU 0 2*(2*bivB^2*(1-bivB)*finiteNativeJet p bivB 0) := by
    simp only [actual_first_conductor_transformed_row]
    norm_num [Fin.sum_univ_succ, bivJCG, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    all_goals ring
  have hF : finiteNativeJet p bivB 0 =
      ∑ n ∈ Finset.range p, RatFunc.C (RatFunc.C (WPReview.nativeCoefficient n))*bivB^n := by
    simpa only [Fin.val_zero, pow_zero, one_mul, outer_native_scalar] using
      finite_native_jet_sum p bivB 0
  have h1 : 1-bivS≠0 := by
    have h := bivS_sub_coefficient_ne_zero (1 : RatFunc ℚ)
    rw [map_one] at h
    rw [show 1-bivS=-(bivS-1) by ring]
    exact neg_ne_zero.mpr h
  rw [actualFirstConductorError, hrow, actual_first_conductor_affine_numerator, hF]
  simp only [Finset.mul_sum, rationalResidue_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  have ht : bivS^(p-1)/(1-bivS)*
        ((1-bivS)*
          ((RatFunc.C firstConductorNumeratorZero+RatFunc.C firstConductorNumeratorOne*bivS)/
            (bivSourceDivisor*bivConductor))*
          (2*bivB^2*(1-bivB)*(RatFunc.C (RatFunc.C (WPReview.nativeCoefficient n))*bivB^n))) =
      RatFunc.C (RatFunc.C (WPReview.nativeCoefficient n))*RatFunc.C (2/firstConductorDivisor)*
        (bivS^(p-1)*(RatFunc.C firstConductorNumeratorZero+RatFunc.C firstConductorNumeratorOne*bivS)/
          algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
            (finiteQuadraticPolynomial firstConductorMean lambda)*bivB^(n+2)*(1-bivB)) := by
    rw [actual_first_conductor_quadratic]
    simp only [map_div₀, _root_.map_ofNat, actual_first_conductor_divisor, pow_add, pow_two]
    field_simp [h1, actual_first_source_divisor_ne_zero, bivConductor_ne_zero]
  rw [ht, mul_assoc, rationalResidue_coefficient_mul, rationalResidue_coefficient_mul]
  rfl

theorem actual_first_conductor_kernel_low_zero (p n : ℕ) (hn : n+4≤p) :
    actualFirstConductorKernel p n=0 := by
  rw [actualFirstConductorKernel, first_quadratic_kernel_low_zero p n _ _ _ hn, mul_zero]

end

end WPForcedSourceStokes
