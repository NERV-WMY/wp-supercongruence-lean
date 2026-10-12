import WPResidueFrobenius.FinitePresentation

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators Topology
open WPResidueQuotient Filter

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

def primitiveLowerNumerator (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5) (k : ℕ) :=
  pullbackNumerator p hp P k * logarithmicDerivation (coordinateWeight i)
    (torusPolynomial (Parameter.integralTenth p hp))

theorem primitiveLowerNumerator_supported (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r k : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    primitiveLowerNumerator p hp P i k ∈ numeratorFiltration ℤ_[p] (p*(r+k)+1) :=
  numeratorFiltration_mul (pullbackNumerator_supported p hp P r k hP)
    (logarithmicDerivation_preserves_numeratorFiltration (coordinateWeight i) 1
      (torusPolynomial_mem_numeratorFiltration _))

def primitiveLowerIntegral (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5)
    (r k : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] r) : FClosed (Parameter.integralTenth p hp) :=
  integralPolynomialGenerator p hp (p*(r+k)) (primitiveLowerNumerator p hp P i k)
    (primitiveLowerNumerator_supported p hp P i r k hP)

theorem primitiveLowerIntegral_coordinates_bound (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r k : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    ∃ w : Fin 11 → ℤ_[p], ActualSpecialization.integralConstantCoordinates p hp hp7 hp19
      (primitiveLowerIntegral p hp P i r k hP) = (p : ℤ)^(pullbackGain (r+1) k) • w := by
  obtain ⟨w, hw⟩ := integralPolynomialGenerator_coordinates_bound p hp hp7 hp19
    (p*(r+k)) (primitiveLowerNumerator p hp P i k) _
  refine ⟨w, ?_⟩
  have he : pullbackGain (r+1) k = (r+k-5)/5 := by
    unfold pullbackGain
    congr 1
    omega
  rw [he]
  simpa [primitiveLowerIntegral, (Fact.out : p.Prime).ne_zero] using hw

def primitiveLowerTail (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5)
    (r K : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] r) : FClosed (1/10 : ℚ_[p]) :=
  (primitiveTailScalar p r K : ℚ_[p]) • integralToField p hp
    (primitiveLowerIntegral p hp P i r (K-1) hP)

include hp7 hp19 in
theorem primitiveLowerTail_coordinates_factor (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r K : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    ∃ w : Fin 11 → ℤ_[p], ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (primitiveLowerTail p hp P i r K hP) = fun j => (primitiveTailScalar p r K : ℚ_[p])*
        (p : ℚ_[p])^(pullbackGain (r+1) (K-1))*IntegralTransport.padicCoefficientMap p (w j) := by
  obtain ⟨w, hw⟩ := primitiveLowerIntegral_coordinates_bound p hp hp7 hp19 P i r (K-1) hP
  refine ⟨w, ?_⟩
  rw [primitiveLowerTail, map_smul, integralToField_coordinates p hp hp7 hp19, hw]
  funext j
  simp [Algebra.smul_def, mul_assoc]

include hp7 hp19 in
theorem primitiveLowerTail_coordinate_norm (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r K : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] r) (j : Fin 11) :
    ‖ActualSpecialization.tenthClosedCoordinates ℚ_[p] (primitiveLowerTail p hp P i r K hP) j‖ ≤
      (p : ℝ)^(-(padicValRat p (primitiveTailScalar p r K)+pullbackGain (r+1) (K-1))) := by
  obtain ⟨w, hw⟩ := primitiveLowerTail_coordinates_factor p hp hp7 hp19 P i r K hP
  rw [hw]
  exact integral_factor_norm p _ (primitiveTailScalar_ne_zero p r K (Fact.out : p.Prime)) _ _

include hp7 hp19 in
theorem primitiveLowerTail_coordinate_tendsto_zero (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r : ℕ) (hr : 1 ≤ r) (hP : P ∈ numeratorFiltration ℤ_[p] r) (j : Fin 11) :
    Tendsto (fun K => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (primitiveLowerTail p hp P i r K hP) j) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hb : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨precision, hm⟩ := exists_pow_lt_of_lt_one hε hb
  obtain ⟨cutoff, hc⟩ := primitive_tail_gain_eventual p r precision (Fact.out : p.Prime) hp hr
  refine ⟨cutoff, ?_⟩
  intro K hK
  rw [dist_zero_right]
  apply lt_of_le_of_lt (primitiveLowerTail_coordinate_norm p hp hp7 hp19 P i r K hP j)
  apply lt_of_le_of_lt _ (show (p : ℝ)^(-(precision : ℤ)) < ε by
    simpa [zpow_neg, zpow_natCast, inv_pow] using hm)
  apply zpow_le_zpow_right₀
  · exact_mod_cast (Fact.out : p.Prime).one_lt.le
  · have he := hc K hK; omega

theorem primitiveLowerTail_coe (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r k : ℕ) (hr : 1 ≤ r) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    ((primitiveLowerTail p hp P i r (k+1) hP : FClosed (1/10 : ℚ_[p])) : NumericalRing p) =
      (p : NumericalRing p)^5*((r-1).factorial : NumericalRing p)*(r : NumericalRing p)*
        numericalPhi p P*inverseF (1/10 : ℚ_[p])^(p*r)*
        algebraMap ℚ (NumericalRing p) (binomialWeight (r+1) k)*numericalQ p hp^k*
        numericalD p i (numericalF p hp)*inverseF (1/10 : ℚ_[p]) := by
  unfold primitiveLowerTail integralToField primitiveLowerIntegral integralPolynomialGenerator
  simp only [Submodule.coe_smul, IntegralTransport.closedMap_coe, Algebra.smul_def,
    Nat.add_sub_cancel]
  change algebraMap ℚ_[p] (NumericalRing p) (primitiveTailScalar p r (k+1) : ℚ_[p]) *
    IntegralTransport.actualMap (IntegralTransport.padicCoefficientMap p)
      (Parameter.integralTenth p hp) (1/10 : ℚ_[p]) _
      (algebraMap (WPResidueQuotient.LaurentPolynomial ℤ_[p])
        (ActualRing (Parameter.integralTenth p hp)) (primitiveLowerNumerator p hp P i k)*
        factorialPole (Parameter.integralTenth p hp) (p*(r+k))) = _
  rw [map_mul, IntegralTransport.actualMap_laurent, IntegralTransport.actualMap_factorialPole]
  change algebraMap ℚ_[p] (NumericalRing p) (primitiveTailScalar p r (k+1) : ℚ_[p]) *
    (fieldLaurent p (primitiveLowerNumerator p hp P i k)*factorialPole (1/10 : ℚ_[p]) (p*(r+k))) = _
  rw [primitiveLowerNumerator, pullbackNumerator, map_mul, map_mul, map_pow, factorialPole]
  change algebraMap ℚ_[p] (NumericalRing p) (primitiveTailScalar p r (k+1) : ℚ_[p]) *
    (numericalPhi p P*numericalG p hp^k*
      fieldLaurent p (logarithmicDerivation (coordinateWeight i)
        (torusPolynomial (Parameter.integralTenth p hp))) *
      (((p*(r+k)).factorial : NumericalRing p)*inverseF (1/10 : ℚ_[p])^(p*(r+k)+1))) = _
  have hs := congrArg (algebraMap ℚ (NumericalRing p))
    (primitiveTailScalar_binomial p r k (Fact.out : p.Prime) hr)
  simp only [map_mul, map_pow, map_natCast] at hs
  rw [IsScalarTower.algebraMap_apply ℚ ℚ_[p] (NumericalRing p) (primitiveTailScalar p r (k+1))] at hs
  have hc : algebraMap ℚ ℚ_[p] (primitiveTailScalar p r (k+1)) =
      (primitiveTailScalar p r (k+1) : ℚ_[p]) := map_ratCast _ _
  rw [hc] at hs
  have hd : fieldLaurent p (logarithmicDerivation (coordinateWeight i)
      (torusPolynomial (Parameter.integralTenth p hp))) = numericalD p i (numericalF p hp) := by
    exact (fieldLaurent_D p i _).symm
  have hpow : inverseF (1/10 : ℚ_[p])^(p*(r+k)+1) =
      inverseF (1/10 : ℚ_[p])^(p*r)*(inverseF (1/10 : ℚ_[p])^p)^k*
        inverseF (1/10 : ℚ_[p]) := by
    simp only [Nat.mul_add, pow_add, pow_mul, pow_one]
  calc
    _ = (algebraMap ℚ_[p] (NumericalRing p) (primitiveTailScalar p r (k+1) : ℚ_[p])*
      ((p*(r+k)).factorial : NumericalRing p))*numericalPhi p P*numericalG p hp^k*
      numericalD p i (numericalF p hp)*inverseF (1/10 : ℚ_[p])^(p*(r+k)+1) := by rw [hd]; ring
    _ = _ := by
      rw [hs, hpow, pow_add, numericalQ, mul_pow, mul_pow]
      ring

end WPResidueFrobenius
