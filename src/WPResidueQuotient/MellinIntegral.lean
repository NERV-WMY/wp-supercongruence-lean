import WPResidueQuotient.MellinFunctional

/-!
Integral independence uses the actual coefficient inclusion into a
characteristic-zero field and then a literal localization lift into Laurent
series. This gives a functional on the integral actual residue quotient
itself; no residue-quotient base-change assertion is assumed.
-/

noncomputable section

namespace WPResidueQuotient.MellinFactors

open scoped LaurentSeries

variable {A : Type*} [CommRing A]
variable (K : Type*) [Field K] [CharZero K] (τ : A →+* K)

def coefficientPolynomialSeriesMap : Polynomial A →+* LSK K :=
  (algebraMap (Polynomial K) (LSK K)).comp (Polynomial.mapRingHom τ)

omit [CharZero K] in
@[simp] theorem coefficientPolynomialSeriesMap_apply (P : Polynomial A) :
    coefficientPolynomialSeriesMap K τ P =
      algebraMap (Polynomial K) (LSK K) (P.map τ) := rfl

omit [CharZero K] in
theorem coefficientPolynomialSeriesMap_injective (hτ : Function.Injective τ) :
    Function.Injective (coefficientPolynomialSeriesMap K τ) :=
  (Polynomial.algebraMap_hahnSeries_injective ℤ).comp (Polynomial.map_injective τ hτ)

omit [CharZero K] in
theorem map_parameter_denominator :
    (Parameter.denominatorPolynomial A).map τ = Parameter.denominatorPolynomial K := by
  simp [Parameter.denominatorPolynomial, Parameter.discriminantPolynomial]

/-- Coefficient inclusion followed by actual localization at the displayed
parameter denominator. -/
def parameterCoefficientSeriesMap : Parameter.ParameterRing A →+* LSK K :=
  IsLocalization.Away.lift (Parameter.denominatorPolynomial A)
    (g := coefficientPolynomialSeriesMap K τ) (by
      rw [coefficientPolynomialSeriesMap_apply, map_parameter_denominator]
      apply isUnit_iff_ne_zero.mpr
      exact fun h => Parameter.denominatorPolynomial_ne_zero
        (Polynomial.algebraMap_hahnSeries_injective ℤ (h.trans (map_zero _).symm)))

omit [CharZero K] in
@[simp] theorem parameterCoefficientSeriesMap_polynomial (P : Polynomial A) :
    parameterCoefficientSeriesMap K τ
      (algebraMap (Polynomial A) (Parameter.ParameterRing A) P) =
        coefficientPolynomialSeriesMap K τ P := by
  simp [parameterCoefficientSeriesMap]

omit [CharZero K] in
@[simp] theorem parameterCoefficientSeriesMap_u :
    parameterCoefficientSeriesMap K τ (Parameter.u : Parameter.ParameterRing A) =
      uSeries K := by
  rw [Parameter.u, parameterCoefficientSeriesMap_polynomial,
    coefficientPolynomialSeriesMap_apply, Polynomial.map_X]
  change (((Polynomial.X : Polynomial K) : PowerSeries K) : LSK K) = uSeries K
  simp only [Polynomial.coe_X, PowerSeries.coe_X, uSeries]

omit [CharZero K] in
theorem parameterCoefficientSeriesMap_injective [IsDomain A] (hτ : Function.Injective τ) :
    Function.Injective (parameterCoefficientSeriesMap K τ) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Parameter.denominatorPolynomial A))
    (parameterCoefficientSeriesMap K τ)).2
  intro P Q
  rw [parameterCoefficientSeriesMap_polynomial, parameterCoefficientSeriesMap_polynomial]
  constructor
  · intro h
    exact congrArg (coefficientPolynomialSeriesMap K τ)
      (Parameter.polynomial_embedding_injective h)
  · intro h
    exact congrArg (algebraMap (Polynomial A) (Parameter.ParameterRing A))
      (coefficientPolynomialSeriesMap_injective K τ hτ h)

def coefficientMellinFunctional [IsDomain A] (r : Fin 5) :
    FClosed (Parameter.u : Parameter.ParameterRing A)
      →ₛₗ[parameterCoefficientSeriesMap K τ] LSK K :=
  mellinFunctional K (parameterCoefficientSeriesMap K τ) Parameter.u
    (parameterCoefficientSeriesMap_u K τ) r

def coefficientMellinQuotientFunctional [IsDomain A] (r : Fin 5) :
    ClosedResidueQuotient (Parameter.u : Parameter.ParameterRing A)
      →ₛₗ[parameterCoefficientSeriesMap K τ] LSK K :=
  mellinQuotientFunctional K (parameterCoefficientSeriesMap K τ) Parameter.u
    (parameterCoefficientSeriesMap_u K τ) r

theorem coefficientGammaQuotientFamily_independent [IsDomain A]
    (hτ : Function.Injective τ) :
    LinearIndependent (Parameter.ParameterRing A)
      (gammaQuotientFamily (Parameter.u : Parameter.ParameterRing A)) :=
  gammaQuotientFamily_independent K (parameterCoefficientSeriesMap K τ) Parameter.u
    (parameterCoefficientSeriesMap_u K τ) (parameterCoefficientSeriesMap_injective K τ hτ)

section Padic

variable (p : ℕ) [Fact p.Prime]

def integralParameterSeriesMap : Parameter.ParameterRing ℤ_[p] →+* LaurentSeries ℚ_[p] :=
  parameterCoefficientSeriesMap ℚ_[p] PadicInt.Coe.ringHom

theorem integralParameterSeriesMap_injective : Function.Injective (integralParameterSeriesMap p) :=
  parameterCoefficientSeriesMap_injective ℚ_[p] PadicInt.Coe.ringHom Subtype.val_injective

@[simp] theorem integralParameterSeriesMap_u :
    integralParameterSeriesMap p (Parameter.u : Parameter.ParameterRing ℤ_[p]) =
      uSeries ℚ_[p] := parameterCoefficientSeriesMap_u ℚ_[p] PadicInt.Coe.ringHom

def integralMellinFunctional (r : Fin 5) :
    FClosed (Parameter.u : Parameter.ParameterRing ℤ_[p])
      →ₛₗ[integralParameterSeriesMap p] LaurentSeries ℚ_[p] :=
  mellinFunctional ℚ_[p] (integralParameterSeriesMap p) Parameter.u
    (integralParameterSeriesMap_u p) r

def integralMellinQuotientFunctional (r : Fin 5) :
    ClosedResidueQuotient (Parameter.u : Parameter.ParameterRing ℤ_[p])
      →ₛₗ[integralParameterSeriesMap p] LaurentSeries ℚ_[p] :=
  mellinQuotientFunctional ℚ_[p] (integralParameterSeriesMap p) Parameter.u
    (integralParameterSeriesMap_u p) r

/-- All primes are allowed for this independence statement. Good-prime
hypotheses needed by integral spanning are separate from this argument. -/
theorem integralGammaQuotientFamily_independent :
    LinearIndependent (Parameter.ParameterRing ℤ_[p])
      (gammaQuotientFamily (Parameter.u : Parameter.ParameterRing ℤ_[p])) :=
  gammaQuotientFamily_independent ℚ_[p] (integralParameterSeriesMap p) Parameter.u
    (integralParameterSeriesMap_u p) (integralParameterSeriesMap_injective p)

end Padic

end WPResidueQuotient.MellinFactors
