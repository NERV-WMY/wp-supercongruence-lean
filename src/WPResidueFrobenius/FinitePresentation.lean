import WPResidueFrobenius.Numerical

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)

theorem rawPullbackTerm_coe (r k : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    ((rawPullbackTerm p hp r k hr P hP : FClosed (1/10 : ℚ_[p])) : NumericalRing p) =
      (p : NumericalRing p)^5*((r-1).factorial : NumericalRing p)*numericalPhi p P*
        inverseF (1/10 : ℚ_[p])^(p*r)*
        algebraMap ℚ (NumericalRing p) (binomialWeight r k)*numericalQ p hp^k := by
  unfold rawPullbackTerm integralToField rawIntegralGenerator integralPolynomialGenerator
  simp only [Submodule.coe_smul, IntegralTransport.closedMap_coe, Algebra.smul_def]
  change algebraMap ℚ_[p] (NumericalRing p) (pullbackScalar p r k : ℚ_[p]) *
    IntegralTransport.actualMap (IntegralTransport.padicCoefficientMap p)
      (Parameter.integralTenth p hp) (1/10 : ℚ_[p]) _
      (algebraMap (WPResidueQuotient.LaurentPolynomial ℤ_[p])
        (ActualRing (Parameter.integralTenth p hp)) (pullbackNumerator p hp P k)*
        factorialPole (Parameter.integralTenth p hp) (p*(r+k)-1)) = _
  rw [map_mul, IntegralTransport.actualMap_laurent, IntegralTransport.actualMap_factorialPole]
  change algebraMap ℚ_[p] (NumericalRing p) (pullbackScalar p r k : ℚ_[p]) *
    (fieldLaurent p (pullbackNumerator p hp P k)*factorialPole (1/10 : ℚ_[p]) (p*(r+k)-1)) = _
  rw [pullbackNumerator, map_mul, map_pow]
  change algebraMap ℚ_[p] (NumericalRing p) (pullbackScalar p r k : ℚ_[p]) *
    (numericalPhi p P*numericalG p hp^k*factorialPole (1/10 : ℚ_[p]) (p*(r+k)-1)) = _
  have he : p*(r+k)-1+1 = p*(r+k) := by
    have := Nat.mul_pos (Fact.out : p.Prime).pos (by omega : 0 < r+k)
    omega
  rw [factorialPole, he]
  have hs := congrArg (algebraMap ℚ (NumericalRing p)) (pullbackScalar_binomial p r k hr)
  simp only [map_mul, map_pow, map_natCast] at hs
  rw [IsScalarTower.algebraMap_apply ℚ ℚ_[p] (NumericalRing p) (pullbackScalar p r k)] at hs
  have hc : algebraMap ℚ ℚ_[p] (pullbackScalar p r k) = (pullbackScalar p r k : ℚ_[p]) :=
    map_ratCast (algebraMap ℚ ℚ_[p]) (pullbackScalar p r k)
  rw [hc] at hs
  have hpow : inverseF (1/10 : ℚ_[p])^(p*(r+k)) =
      inverseF (1/10 : ℚ_[p])^(p*r)*(inverseF (1/10 : ℚ_[p])^p)^k := by
    simp only [Nat.mul_add, pow_add, pow_mul]
  calc
    _ = (algebraMap ℚ_[p] (NumericalRing p) (pullbackScalar p r k : ℚ_[p])*
      ((p*(r+k)-1).factorial : NumericalRing p))*numericalPhi p P*numericalG p hp^k*
      inverseF (1/10 : ℚ_[p])^(p*(r+k)) := by ring
    _ = _ := by
      rw [hs, hpow, pow_add, numericalQ, mul_pow, mul_pow]
      ring

def finiteRawPullback (r N : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) : FClosed (1/10 : ℚ_[p]) :=
  ∑ k ∈ Finset.range N, rawPullbackTerm p hp r k hr P hP

theorem finiteRawPullback_coe (r N : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    ((finiteRawPullback p hp r N hr P hP : FClosed (1/10 : ℚ_[p])) : NumericalRing p) =
      (p : NumericalRing p)^5*((r-1).factorial : NumericalRing p)*
        finiteNumericalPullback p hp P r N := by
  simp only [finiteRawPullback, Submodule.coe_sum, rawPullbackTerm_coe,
    finiteNumericalPullback, binomialPartial]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end WPResidueFrobenius
