import WPFiniteNativeJet

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

/-- Every coefficient of the literal finite native Euler polynomial. -/
theorem theta_native_polynomial_sum (p k : ℕ) :
    thetaPower k (WPReview.nativePolynomial p) =
      ∑ n ∈ Finset.range p, monomial n ((n : ℚ)^k*WPReview.nativeCoefficient n) := by
  classical
  ext n
  rw [thetaPower_coeff, WPReview.nativePolynomial_coeff]
  simp only [finsetSum_coeff, coeff_monomial]
  by_cases hn : n<p
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [hbn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b≠n := by
      have hb' := Finset.mem_range.mp hb
      omega
    simp [hbn]

section Field

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem finite_native_jet_sum (p : ℕ) (q : K) (i : Fin 3) :
    finiteNativeJet p q i =
      ∑ n ∈ Finset.range p,
        algebraMap ℚ K ((n : ℚ)^i.val*WPReview.nativeCoefficient n)*q^n := by
  rw [finiteNativeJet, theta_native_polynomial_sum]
  simp only [map_sum, aeval_monomial]

theorem finite_native_weighted_sum (p : ℕ) (q : K) :
    (5/72)*finiteNativeJet p q 0 + (23/36)*finiteNativeJet p q 1 +
      (3/2)*finiteNativeJet p q 2 =
      ∑ n ∈ Finset.range p,
        algebraMap ℚ K (nativeBoundaryWeight n*WPReview.nativeCoefficient n)*q^n := by
  simp only [finite_native_jet_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  norm_num [nativeBoundaryWeight, map_add, map_mul, map_pow, native_algebraMap_rat]
  ring

end Field

end

end WPForcedSourceStokes
