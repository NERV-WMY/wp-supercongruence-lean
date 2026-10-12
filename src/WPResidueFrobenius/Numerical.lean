import WPResidueFrobenius.FiniteDerivative

noncomputable section

namespace WPResidueFrobenius

open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)

abbrev NumericalRing := ActualRing (1/10 : ℚ_[p])

def fieldLaurent : WPResidueQuotient.LaurentPolynomial ℤ_[p] →+* NumericalRing p :=
  (algebraMap (WPResidueQuotient.LaurentPolynomial ℚ_[p]) (NumericalRing p)).comp
    (IntegralTransport.laurentMap (IntegralTransport.padicCoefficientMap p))

def numericalD (i : Fin 5) : Derivation ℚ (NumericalRing p) (NumericalRing p) :=
  (actualD (1/10 : ℚ_[p]) i).restrictScalars ℚ

def numericalF : NumericalRing p := fieldLaurent p (torusPolynomial (Parameter.integralTenth p hp))
def numericalG : NumericalRing p := fieldLaurent p (G p hp)
def numericalPhi (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) : NumericalRing p :=
  fieldLaurent p (laurentPhi ℤ_[p] p P)
def numericalQ : NumericalRing p := (p : NumericalRing p)*numericalG p hp*
  inverseF (1/10 : ℚ_[p])^p

theorem fieldLaurent_D (i : Fin 5) (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) :
    numericalD p i (fieldLaurent p P) =
      fieldLaurent p (logarithmicDerivation (coordinateWeight i) P) := by
  change actualD (1/10 : ℚ_[p]) i
    (algebraMap (WPResidueQuotient.LaurentPolynomial ℚ_[p]) (NumericalRing p)
      (IntegralTransport.laurentMap _ P)) = _
  rw [actualD_algebraMap_numerator, ← IntegralTransport.laurentMap_logarithmic]
  rfl

theorem numericalPhi_D (i : Fin 5) (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) :
    numericalD p i (numericalPhi p P) =
      (p : NumericalRing p)*numericalPhi p (logarithmicDerivation (coordinateWeight i) P) := by
  rw [numericalPhi, fieldLaurent_D, laurentPhi_logarithmic]
  simp [Algebra.smul_def, numericalPhi]

theorem numericalF_eq : numericalF p hp =
    algebraMap (WPResidueQuotient.LaurentPolynomial ℚ_[p]) (NumericalRing p)
      (torusPolynomial (1/10 : ℚ_[p])) := by
  unfold numericalF fieldLaurent
  simp only [RingHom.comp_apply]
  rw [IntegralTransport.laurentMap_torusPolynomial _ _ _
    (ParameterSpecialization.integralTenth_in_field p hp)]

theorem numericalF_mul_inverse : numericalF p hp*inverseF (1/10 : ℚ_[p]) = 1 := by
  rw [numericalF_eq]
  exact imageF_mul_inverseF _

theorem numericalPhi_f : numericalPhi p (torusPolynomial (Parameter.integralTenth p hp)) =
    numericalF p hp^p + (p : NumericalRing p)*numericalG p hp := by
  rw [numericalPhi, laurentPhi_f]
  simp [numericalF, numericalG, Algebra.smul_def]

theorem numericalPhi_f_inverse :
    numericalPhi p (torusPolynomial (Parameter.integralTenth p hp))*
      inverseF (1/10 : ℚ_[p])^p = 1+numericalQ p hp := by
  have he : numericalF p hp^p*inverseF (1/10 : ℚ_[p])^p = 1 := by
    rw [← mul_pow, numericalF_mul_inverse, one_pow]
  rw [numericalPhi_f, add_mul, he, numericalQ]

theorem numericalG_D (i : Fin 5) :
    numericalD p i (numericalG p hp) =
      numericalPhi p (logarithmicDerivation (coordinateWeight i)
        (torusPolynomial (Parameter.integralTenth p hp))) -
      numericalF p hp^(p-1)*numericalD p i (numericalF p hp) := by
  rw [numericalG, fieldLaurent_D, G_logarithmic]
  simp only [map_sub, map_mul, map_pow, numericalPhi, numericalF, fieldLaurent_D]

theorem numericalInverse_D (i : Fin 5) :
    numericalD p i (inverseF (1/10 : ℚ_[p])) =
      -(inverseF (1/10 : ℚ_[p]))^2 * numericalD p i (numericalF p hp) := by
  rw [numericalF_eq]
  exact derivation_invSelf (torusPolynomial (1/10 : ℚ_[p])) (numericalD p i)

theorem numericalInversePow_D (i : Fin 5) (n : ℕ) (hn : 1 ≤ n) :
    numericalD p i (inverseF (1/10 : ℚ_[p])^n) =
      -(n : NumericalRing p)*inverseF (1/10 : ℚ_[p])^n*
        inverseF (1/10 : ℚ_[p])*numericalD p i (numericalF p hp) := by
  rw [Derivation.leibniz_pow, numericalInverse_D p hp i]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  have he : n-1+2 = n+1 := by omega
  calc
    _ = -(n : NumericalRing p)*(inverseF (1/10 : ℚ_[p])^(n-1)*
      inverseF (1/10 : ℚ_[p])^2)*numericalD p i (numericalF p hp) := by ring
    _ = _ := by rw [← pow_add, he, pow_succ]; ring

theorem numericalG_inverse_identity (i : Fin 5) :
    numericalPhi p (logarithmicDerivation (coordinateWeight i)
      (torusPolynomial (Parameter.integralTenth p hp)))*inverseF (1/10 : ℚ_[p])^p -
      numericalD p i (numericalF p hp)*inverseF (1/10 : ℚ_[p]) =
      inverseF (1/10 : ℚ_[p])^p*numericalD p i (numericalG p hp) := by
  have he : p-1+1 = p := by omega
  have hc : numericalF p hp^(p-1)*inverseF (1/10 : ℚ_[p])^p =
      inverseF (1/10 : ℚ_[p]) := by
    have hep : inverseF (1/10 : ℚ_[p])^p =
        inverseF (1/10 : ℚ_[p])^(p-1)*inverseF (1/10 : ℚ_[p]) := by
      simpa only [he] using pow_succ (inverseF (1/10 : ℚ_[p])) (p-1)
    rw [hep]
    calc
      _ = (numericalF p hp*inverseF (1/10 : ℚ_[p]))^(p-1)*inverseF (1/10 : ℚ_[p]) := by
        rw [mul_pow]; ring
      _ = _ := by rw [numericalF_mul_inverse, one_pow, one_mul]
  rw [numericalG_D]
  linear_combination numericalD p i (numericalF p hp)*hc

theorem numericalQ_D (i : Fin 5) :
    numericalD p i (numericalQ p hp) =
      (p : NumericalRing p)*numericalPhi p (logarithmicDerivation (coordinateWeight i)
        (torusPolynomial (Parameter.integralTenth p hp)))*inverseF (1/10 : ℚ_[p])^p -
      (p : NumericalRing p)*numericalD p i (numericalF p hp)*
        inverseF (1/10 : ℚ_[p])*(1+numericalQ p hp) := by
  rw [numericalQ, Derivation.leibniz, Derivation.leibniz,
    numericalInversePow_D p hp i p (by omega)]
  simp only [Derivation.map_natCast, Algebra.smul_def, Algebra.algebraMap_self_apply,
    mul_zero, add_zero]
  linear_combination -(p : NumericalRing p)*numericalG_inverse_identity p hp i

def finiteNumericalPullback (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (r N : ℕ) :
    NumericalRing p := numericalPhi p P * inverseF (1/10 : ℚ_[p])^(p*r) *
      binomialPartial r N (numericalQ p hp)

theorem finiteNumericalPullback_raise (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (r N : ℕ) : finiteNumericalPullback p hp
      (P*torusPolynomial (Parameter.integralTenth p hp)) (r+1) (N+1) -
      finiteNumericalPullback p hp P r (N+1) =
      numericalPhi p P*inverseF (1/10 : ℚ_[p])^(p*r)*
        algebraMap ℚ (NumericalRing p) (binomialWeight (r+1) N)*numericalQ p hp^(N+1) := by
  have he : inverseF (1/10 : ℚ_[p])^(p*(r+1)) =
      inverseF (1/10 : ℚ_[p])^(p*r)*inverseF (1/10 : ℚ_[p])^p := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
  have hf := numericalPhi_f_inverse p hp
  have hs := binomialPartial_raise r N (numericalQ p hp)
  unfold finiteNumericalPullback numericalPhi
  rw [map_mul, map_mul, he]
  change numericalPhi p P*
      numericalPhi p (torusPolynomial (Parameter.integralTenth p hp))*
      (inverseF (1/10 : ℚ_[p])^(p*r)*inverseF (1/10 : ℚ_[p])^p)*
      binomialPartial (r+1) (N+1) (numericalQ p hp) -
      numericalPhi p P*inverseF (1/10 : ℚ_[p])^(p*r)*binomialPartial r (N+1) (numericalQ p hp) =
      numericalPhi p P*inverseF (1/10 : ℚ_[p])^(p*r)*
        algebraMap ℚ (NumericalRing p) (binomialWeight (r+1) N)*numericalQ p hp^(N+1)
  linear_combination
    numericalPhi p P*inverseF (1/10 : ℚ_[p])^(p*r)*hs +
      numericalPhi p P*inverseF (1/10 : ℚ_[p])^(p*r)*
        binomialPartial (r+1) (N+1) (numericalQ p hp)*hf

theorem finiteNumericalPullback_derivative (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (i : Fin 5) (r N : ℕ) (hr : 1 ≤ r) :
    numericalD p i (finiteNumericalPullback p hp P r (N+1)) - (p : NumericalRing p)*
      (finiteNumericalPullback p hp (logarithmicDerivation (coordinateWeight i) P) r (N+1) -
        (r : NumericalRing p)*finiteNumericalPullback p hp
          (P*logarithmicDerivation (coordinateWeight i)
            (torusPolynomial (Parameter.integralTenth p hp))) (r+1) (N+1)) =
      (p : NumericalRing p)*(r : NumericalRing p)*numericalPhi p P*
        inverseF (1/10 : ℚ_[p])^(p*r)*inverseF (1/10 : ℚ_[p])^p*
        algebraMap ℚ (NumericalRing p) (binomialWeight (r+1) N)*
        numericalQ p hp^N*numericalD p i (numericalG p hp) := by
  have h := finite_binomial_derivative (numericalD p i) p r N hr
    (numericalPhi p P) (numericalPhi p (logarithmicDerivation (coordinateWeight i) P))
    (inverseF (1/10 : ℚ_[p])^(p*r)) (inverseF (1/10 : ℚ_[p])) (numericalQ p hp)
    (numericalD p i (numericalF p hp))
    (numericalPhi p (logarithmicDerivation (coordinateWeight i)
      (torusPolynomial (Parameter.integralTenth p hp)))) (numericalD p i (numericalG p hp))
    (numericalPhi_D p i P)
    (by
      rw [numericalInversePow_D p hp i (p*r)
        (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))]
      simp [Nat.cast_mul, mul_assoc])
    (numericalQ_D p hp i) (numericalG_inverse_identity p hp i)
  have he : inverseF (1/10 : ℚ_[p])^(p*(r+1)) =
      inverseF (1/10 : ℚ_[p])^(p*r)*inverseF (1/10 : ℚ_[p])^p := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
  simpa only [finiteNumericalPullback, numericalPhi, map_mul, he, mul_assoc] using h

end WPResidueFrobenius
