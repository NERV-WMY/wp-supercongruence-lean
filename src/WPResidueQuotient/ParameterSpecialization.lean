import WPResidueQuotient.IntegralTransport

/-!
The coefficient-ring specialization squares commute as actual ring
homomorphisms.  Over the integral ring the denominator is invertible for
`p ≥ 7`, `p ≠ 7, 19`; the field specialization exists for every prime.
The value of the integral parameter in the field is exactly `1/10`.
Actual localized module maps are supplied separately by SpecializationCore.
-/

namespace WPResidueQuotient.ParameterSpecialization

noncomputable section

variable (p : ℕ) [Fact p.Prime]

def fieldSpecialization : Parameter.ParameterRing ℚ_[p] →+* ℚ_[p] :=
  IsLocalization.Away.lift (Parameter.denominatorPolynomial ℚ_[p])
    (g := Polynomial.evalRingHom (1 / 10 : ℚ_[p])) (by
      apply isUnit_iff_ne_zero.mpr
      norm_num [Parameter.denominatorPolynomial, Parameter.discriminantPolynomial,
        Polynomial.evalRingHom])

@[simp] theorem fieldSpecialization_polynomial (P : Polynomial ℚ_[p]) :
    fieldSpecialization p
      (algebraMap (Polynomial ℚ_[p]) (Parameter.ParameterRing ℚ_[p]) P) =
        Polynomial.eval (1 / 10 : ℚ_[p]) P := by
  simp [fieldSpecialization]

@[simp] theorem fieldSpecialization_u :
    fieldSpecialization p (Parameter.u : Parameter.ParameterRing ℚ_[p]) = 1 / 10 := by
  simp [Parameter.u]

@[simp] theorem fieldSpecialization_scalar (r : ℚ_[p]) :
    fieldSpecialization p (algebraMap ℚ_[p] (Parameter.ParameterRing ℚ_[p]) r) = r := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (Polynomial ℚ_[p])
    (Parameter.ParameterRing ℚ_[p])]
  change fieldSpecialization p
    (algebraMap (Polynomial ℚ_[p]) (Parameter.ParameterRing ℚ_[p]) (Polynomial.C r)) = r
  rw [fieldSpecialization_polynomial, Polynomial.eval_C]

def fieldSpecializationAlg : Parameter.ParameterRing ℚ_[p] →ₐ[ℚ_[p]] ℚ_[p] where
  __ := fieldSpecialization p
  commutes' := fieldSpecialization_scalar p

theorem fieldSpecialization_discriminant :
    fieldSpecialization p (Parameter.discriminant : Parameter.ParameterRing ℚ_[p]) =
      14896 / 15625 := by
  norm_num [Parameter.discriminant, map_sub, map_pow, map_mul, map_ofNat]

theorem integralTenth_in_field (hp : 7 ≤ p) :
    IntegralTransport.padicCoefficientMap p (Parameter.integralTenth p hp) =
      (1 / 10 : ℚ_[p]) := by
  have h := congrArg (IntegralTransport.padicCoefficientMap p)
    (Parameter.ten_mul_integralTenth p hp)
  simp only [map_mul, map_ofNat, map_one] at h
  apply (eq_div_iff (by norm_num : (10 : ℚ_[p]) ≠ 0)).mpr
  simpa only [mul_comm] using h

theorem evaluation_naturality {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (t : K) (P : Polynomial K) :
    Polynomial.eval (φ t) (IntegralTransport.polynomialMap φ P) =
      φ (Polynomial.eval t P) := by
  change (P.map φ).eval (φ t) = φ (P.eval t)
  rw [Polynomial.eval_map, Polynomial.eval₂_hom]

/-- The integral and field specializations agree on every element of the
actual parameter localization.  There is no extra exception at `p = 11`. -/
theorem integral_field_square (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    (IntegralTransport.padicCoefficientMap p).comp
        (Parameter.integralSpecialization p hp hp7 hp19) =
      (fieldSpecialization p).comp (IntegralTransport.padicParameterMap p) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Parameter.denominatorPolynomial ℤ_[p]))
  apply RingHom.ext
  intro P
  simp only [RingHom.comp_apply, Parameter.integralSpecialization_polynomial]
  change IntegralTransport.padicCoefficientMap p
      (Polynomial.eval (Parameter.integralTenth p hp) P) =
    fieldSpecialization p
      (IntegralTransport.parameterMap (IntegralTransport.padicCoefficientMap p)
        (algebraMap (Polynomial ℤ_[p]) (Parameter.ParameterRing ℤ_[p]) P))
  rw [IntegralTransport.parameterMap_polynomial, fieldSpecialization_polynomial,
    ← integralTenth_in_field p hp, evaluation_naturality]

theorem integral_field_square_apply (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)
    (r : Parameter.ParameterRing ℤ_[p]) :
    IntegralTransport.padicCoefficientMap p (Parameter.integralSpecialization p hp hp7 hp19 r) =
      fieldSpecialization p (IntegralTransport.padicParameterMap p r) :=
  DFunLike.congr_fun (integral_field_square p hp hp7 hp19) r

def rationalCoefficientMap : ℚ →+* ℚ_[p] := algebraMap ℚ ℚ_[p]

def rationalParameterMap : Parameter.ParameterRing ℚ →+* Parameter.ParameterRing ℚ_[p] :=
  IntegralTransport.parameterMap (rationalCoefficientMap p)

theorem rational_field_square :
    (rationalCoefficientMap p).comp Parameter.rationalSpecialization =
      (fieldSpecialization p).comp (rationalParameterMap p) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Parameter.denominatorPolynomial ℚ))
  apply RingHom.ext
  intro P
  simp only [RingHom.comp_apply, Parameter.rationalSpecialization_polynomial]
  change rationalCoefficientMap p (Polynomial.eval (1 / 10 : ℚ) P) =
    fieldSpecialization p
      (IntegralTransport.parameterMap (rationalCoefficientMap p)
        (algebraMap (Polynomial ℚ) (Parameter.ParameterRing ℚ) P))
  rw [IntegralTransport.parameterMap_polynomial, fieldSpecialization_polynomial]
  have ht : rationalCoefficientMap p (1 / 10 : ℚ) = (1 / 10 : ℚ_[p]) := by
    norm_num [rationalCoefficientMap, map_div₀]
  rw [← ht, evaluation_naturality]

theorem rational_field_square_apply (r : Parameter.ParameterRing ℚ) :
    rationalCoefficientMap p (Parameter.rationalSpecialization r) =
      fieldSpecialization p (rationalParameterMap p r) :=
  DFunLike.congr_fun (rational_field_square p) r

end
end WPResidueQuotient.ParameterSpecialization
