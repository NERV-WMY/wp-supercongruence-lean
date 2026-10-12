import WPResidueFrobenius.IntegralOperator

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators Topology
open WPResidueQuotient Filter

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem monomial_supported (a : Fin 6 → ℕ) (m : ℕ) (ha : (∑ i, a i) ≤ m) :
    laurentMonomial (R := ℤ_[p]) (fun i => (a i : ℤ)) ∈ numeratorFiltration ℤ_[p] m := by
  apply single_mem_numeratorFiltration
  exact (latticeQ_nonnegative_degree_le a).trans ha

include hp7 hp19 in
theorem presentedPullback_factorialNumerator (n : ℕ)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] (n+1)) :
    presentedPullback p hp (integralPolynomialGenerator p hp n P hP) =
      rawPullbackCoordinates p hp (n+1) (by omega) P hP := by
  have hsm := (numeratorFiltration ℤ_[p] (n+1)).smul_mem (n.factorial : ℤ_[p]) hP
  have he : ((integralPolynomialGenerator p hp n P hP : FClosed _) : ActualRing _) =
      poleLinearMap (Parameter.integralTenth p hp) (n+1) ((n.factorial : ℤ_[p]) • P) := by
    simp only [integralPolynomialGenerator, factorialNumeratorMap_apply,
      poleLinearMap_apply, factorialPole, Algebra.smul_def, map_mul, map_natCast]
    ring
  rw [presentedPullback_eq p hp hp7 hp19 _ (n+1) (by omega) _ hsm he,
    plainPullbackCoordinates_smul p hp (n+1) (by omega) (n.factorial : ℤ_[p]) P hP,
    plainPullbackCoordinates, map_natCast, Nat.add_sub_cancel, smul_smul]
  have hn : (n.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [mul_comm, inv_mul_cancel₀ hn, one_smul]

theorem integralGenerator_as_polynomial (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n+1) :
    integralGenerator p hp a n ha = integralPolynomialGenerator p hp n
      (laurentMonomial (fun i => (a i : ℤ)))
      (monomial_supported p a (n+1) ha) := by
  apply Subtype.ext
  rfl

include hp7 hp19 in
theorem presentedPullback_generator (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n+1) :
    presentedPullback p hp (integralGenerator p hp a n ha) =
      rawPullbackCoordinates p hp (n+1) (by omega)
        (laurentMonomial (fun i => (a i : ℤ)))
        (monomial_supported p a (n+1) ha) := by
  rw [integralGenerator_as_polynomial]
  exact presentedPullback_factorialNumerator p hp hp7 hp19 n _ _

/-- Each actual primitive has the ordered four-volume pullback p^4. -/
def finitePrimitivePullback (r K : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) : FClosed (1/10 : ℚ_[p]) :=
  (p : ℚ_[p])⁻¹ • finiteRawPullback p hp r K hr P hP

theorem finitePrimitivePullback_coe (r K : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    ((finitePrimitivePullback p hp r K hr P hP : FClosed _) : NumericalRing p) =
      (p : NumericalRing p)^4*((r-1).factorial : NumericalRing p)*
        finiteNumericalPullback p hp P r K := by
  rw [finitePrimitivePullback, Submodule.coe_smul, finiteRawPullback_coe, Algebra.smul_def]
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hi : algebraMap ℚ_[p] (NumericalRing p) (p : ℚ_[p])⁻¹ * (p : NumericalRing p) = 1 := by
    calc
      _ = algebraMap ℚ_[p] (NumericalRing p) ((p : ℚ_[p])⁻¹ * (p : ℚ_[p])) := by
        rw [map_mul, map_natCast]
      _ = 1 := by rw [inv_mul_cancel₀ hpne, map_one]
  calc
    _ = (algebraMap ℚ_[p] (NumericalRing p) (p : ℚ_[p])⁻¹*(p : NumericalRing p))*
      ((p : NumericalRing p)^4*((r-1).factorial : NumericalRing p)*
        finiteNumericalPullback p hp P r K) := by ring
    _ = _ := by rw [hi, one_mul]

theorem finitePrimitivePullback_derivative (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r k : ℕ) (hr : 1 ≤ r) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    DClosed (1/10 : ℚ_[p]) i (finitePrimitivePullback p hp r (k+1) hr P hP) =
      finiteDerivativePullback p hp P i r (k+1) hr hP + primitiveUpperTail p hp P i r k hP -
        primitiveLowerTail p hp P i r (k+1) hP := by
  rw [finitePrimitivePullback, map_smul, finiteDerivativePullback_identity, smul_smul]
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [inv_mul_cancel₀ hpne, one_smul]

include hp7 hp19 in
theorem finitePrimitivePullback_coordinates_tendsto
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (r : ℕ) (hr : 1 ≤ r)
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    Tendsto (fun K => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (finitePrimitivePullback p hp r K hr P hP)) atTop
        (𝓝 ((p : ℚ_[p])⁻¹ • rawPullbackCoordinates p hp r hr P hP)) := by
  simpa only [finitePrimitivePullback, map_smul] using
    (finiteRawPullback_coordinates_tendsto p hp hp7 hp19 P r hr hP).const_smul (p : ℚ_[p])⁻¹

end WPResidueFrobenius
