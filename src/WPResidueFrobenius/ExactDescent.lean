import WPResidueFrobenius.PrimitiveTails

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators Topology
open WPResidueQuotient Filter

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

def derivativeNumerator (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5) :=
  logarithmicDerivation (coordinateWeight i) P

theorem derivativeNumerator_supported (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    derivativeNumerator p P i ∈ numeratorFiltration ℤ_[p] r :=
  logarithmicDerivation_preserves_numeratorFiltration (coordinateWeight i) r hP

def derivativePoleNumerator (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5) :=
  P*logarithmicDerivation (coordinateWeight i) (torusPolynomial (Parameter.integralTenth p hp))

theorem derivativePoleNumerator_supported (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    derivativePoleNumerator p hp P i ∈ numeratorFiltration ℤ_[p] (r+1) :=
  numeratorFiltration_mul hP
    (logarithmicDerivation_preserves_numeratorFiltration (coordinateWeight i) 1
      (torusPolynomial_mem_numeratorFiltration _))

def finiteDerivativePullback (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5)
    (r K : ℕ) (hr : 1 ≤ r) (hP : P ∈ numeratorFiltration ℤ_[p] r) : FClosed (1/10 : ℚ_[p]) :=
  finiteRawPullback p hp r K hr (derivativeNumerator p P i) (derivativeNumerator_supported p P i r hP) -
    finiteRawPullback p hp (r+1) K (by omega) (derivativePoleNumerator p hp P i)
      (derivativePoleNumerator_supported p hp P i r hP)

def primitiveUpperTail (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5)
    (r k : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] r) : FClosed (1/10 : ℚ_[p]) :=
  rawPullbackTerm p hp (r+1) k (by omega) (derivativePoleNumerator p hp P i)
    (derivativePoleNumerator_supported p hp P i r hP)

theorem finiteDerivativePullback_identity (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r k : ℕ) (hr : 1 ≤ r) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    DClosed (1/10 : ℚ_[p]) i (finiteRawPullback p hp r (k+1) hr P hP) = (p : ℚ_[p]) •
      (finiteDerivativePullback p hp P i r (k+1) hr hP + primitiveUpperTail p hp P i r k hP -
        primitiveLowerTail p hp P i r (k+1) hP) := by
  apply Subtype.ext
  change numericalD p i ((finiteRawPullback p hp r (k+1) hr P hP : FClosed (1/10 : ℚ_[p])) :
      NumericalRing p) = _
  simp only [finiteDerivativePullback, primitiveUpperTail, Submodule.coe_smul,
    Submodule.coe_sub, Submodule.coe_add, Algebra.smul_def]
  rw [finiteRawPullback_coe, finiteRawPullback_coe, finiteRawPullback_coe,
    rawPullbackTerm_coe, primitiveLowerTail_coe p hp P i r k hr hP]
  rw [Derivation.leibniz]
  simp only [Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_natCast,
    smul_zero, add_zero, mul_zero, Algebra.smul_def,
    Algebra.algebraMap_self_apply, map_natCast]
  have he : r-1+1 = r := by omega
  have hf := Nat.factorial_succ (r-1)
  rw [he] at hf
  have hfR : (r.factorial : NumericalRing p) = (r : NumericalRing p)*((r-1).factorial : NumericalRing p) :=
    by rw [hf, Nat.cast_mul]
  have hpow : inverseF (1/10 : ℚ_[p])^(p*(r+1)) =
      inverseF (1/10 : ℚ_[p])^(p*r)*inverseF (1/10 : ℚ_[p])^p := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
  have hn := finiteNumericalPullback_derivative p hp P i r k hr
  have hg := numericalG_inverse_identity p hp i
  unfold derivativeNumerator derivativePoleNumerator at *
  simp only [numericalPhi, map_mul, hpow, Nat.add_sub_cancel, hfR] at *
  linear_combination
    (p : NumericalRing p)^5*((r-1).factorial : NumericalRing p)*hn +
      -(p : NumericalRing p)^6*((r-1).factorial : NumericalRing p)*(r : NumericalRing p)*
        fieldLaurent p (laurentPhi ℤ_[p] p P)*inverseF (1/10 : ℚ_[p])^(p*r)*
        algebraMap ℚ (NumericalRing p) (binomialWeight (r+1) k)*numericalQ p hp^k*hg

theorem closedCoordinate_derivative_zero (g : FClosed (1/10 : ℚ_[p])) (i : Fin 5) :
    ActualSpecialization.tenthClosedCoordinates ℚ_[p] (DClosed (1/10 : ℚ_[p]) i g) = 0 := by
  change (ActualSpecialization.tenthQuotientEquiv ℚ_[p]).symm
    (Submodule.Quotient.mk (DClosed (1/10 : ℚ_[p]) i g)) = 0
  rw [(Submodule.Quotient.mk_eq_zero (exactSubmodule (1/10 : ℚ_[p]))).mpr
    (DClosed_mem_exact (1/10 : ℚ_[p]) i g), map_zero]

theorem finiteDerivativePullback_coordinates (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r k : ℕ) (hr : 1 ≤ r) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    ActualSpecialization.tenthClosedCoordinates ℚ_[p] (finiteDerivativePullback p hp P i r (k+1) hr hP) =
      ActualSpecialization.tenthClosedCoordinates ℚ_[p] (primitiveLowerTail p hp P i r (k+1) hP) -
      ActualSpecialization.tenthClosedCoordinates ℚ_[p] (primitiveUpperTail p hp P i r k hP) := by
  have h := congrArg (ActualSpecialization.tenthClosedCoordinates ℚ_[p])
    (finiteDerivativePullback_identity p hp P i r k hr hP)
  rw [closedCoordinate_derivative_zero, map_smul, map_sub, map_add] at h
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hz := (smul_eq_zero.mp h.symm).resolve_left hpne
  linear_combination hz

include hp7 hp19 in
theorem finiteRawPullback_coordinates_tendsto (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (r : ℕ) (hr : 1 ≤ r) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    Tendsto (fun K => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (finiteRawPullback p hp r K hr P hP)) atTop (𝓝 (rawPullbackCoordinates p hp r hr P hP)) := by
  simpa only [finiteRawPullback, map_sum] using
    (rawPullbackCoordinates_hasSum p hp hp7 hp19 r hr P hP).tendsto_sum_nat

include hp7 hp19 in
theorem raw_coordinates_annihilate_presented_derivative
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5) (r : ℕ) (hr : 1 ≤ r)
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    rawPullbackCoordinates p hp r hr (derivativeNumerator p P i)
      (derivativeNumerator_supported p P i r hP) -
      rawPullbackCoordinates p hp (r+1) (by omega) (derivativePoleNumerator p hp P i)
        (derivativePoleNumerator_supported p hp P i r hP) = 0 := by
  have hL : Tendsto (fun K => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (primitiveLowerTail p hp P i r K hP)) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact primitiveLowerTail_coordinate_tendsto_zero p hp hp7 hp19 P i r hr hP j
  have hU : Tendsto (fun k => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (primitiveUpperTail p hp P i r k hP)) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact rawPullbackTerm_coordinate_tendsto_zero p hp hp7 hp19 (r+1) (by omega)
      (derivativePoleNumerator p hp P i) (derivativePoleNumerator_supported p hp P i r hP) j
  have hz := ((hL.comp (tendsto_add_atTop_nat 1)).sub hU).congr'
    (Filter.Eventually.of_forall fun k => (finiteDerivativePullback_coordinates p hp P i r k hr hP).symm)
  have hD := ((finiteRawPullback_coordinates_tendsto p hp hp7 hp19
      (derivativeNumerator p P i) r hr (derivativeNumerator_supported p P i r hP)).sub
    (finiteRawPullback_coordinates_tendsto p hp hp7 hp19 (derivativePoleNumerator p hp P i)
      (r+1) (by omega) (derivativePoleNumerator_supported p hp P i r hP))).comp
        (tendsto_add_atTop_nat 1)
  have hD' : Tendsto (fun k => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (finiteDerivativePullback p hp P i r (k+1) hr hP)) atTop (𝓝
      (rawPullbackCoordinates p hp r hr (derivativeNumerator p P i)
        (derivativeNumerator_supported p P i r hP) -
      rawPullbackCoordinates p hp (r+1) (by omega) (derivativePoleNumerator p hp P i)
        (derivativePoleNumerator_supported p hp P i r hP))) := by
    simpa only [finiteDerivativePullback, map_sub, Function.comp_def] using hD
  simpa only [sub_zero] using tendsto_nhds_unique hD' hz

end WPResidueFrobenius
